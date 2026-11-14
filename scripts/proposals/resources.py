"""Bound proof memory by machine capacity, leaving room for the host services.

Capacity is deliberately stable rather than free RAM; the reserve cannot protect
against unrelated workloads that already consume a large part of the machine.
"""
from pathlib import Path, PurePosixPath
import platform
import re
import subprocess

MIB = 1024 * 1024


def memory_budget(requested_mb, capacity_mb):
    """Return a bounded MiB allocation; never silently permit an invalid budget."""
    if any(type(value) is not int or value <= 0 for value in (requested_mb, capacity_mb)):
        raise ValueError('Memory request and capacity must be positive integer MiB values')
    effective = min(requested_mb, capacity_mb - max(2048, capacity_mb // 8))
    if effective < 1024:
        raise ValueError('Insufficient memory: proof budget after host reserve is below 1024 MiB')
    return effective


def _positive_integer(value):
    if not re.fullmatch(r'[0-9]+', value) or int(value) <= 0:
        raise ValueError(f'Invalid memory capacity: {value!r}')
    return int(value)


def _unescape(value):
    return re.sub(r'\\([0-7]{3})', lambda match: chr(int(match[1], 8)), value)


def _cgroup_limits():
    """Read the current cgroup and its visible ancestors in each memory mount."""
    try:
        memberships = Path('/proc/self/cgroup').read_text().splitlines()
        mounts = Path('/proc/self/mountinfo').read_text().splitlines()
    except FileNotFoundError:
        return []
    limits = []
    for mount in mounts:
        before, separator, after = mount.partition(' - ')
        fields, filesystem = before.split(), after.split()
        if not separator or len(fields) < 5 or len(filesystem) < 3:
            continue
        unified = filesystem[0] == 'cgroup2'
        if not unified and not (filesystem[0] == 'cgroup' and 'memory' in filesystem[2].split(',')):
            continue
        root, location = PurePosixPath(_unescape(fields[3])), Path(_unescape(fields[4]))
        for membership in memberships:
            parts = membership.split(':', 2)
            if len(parts) != 3:
                raise ValueError('Malformed cgroup membership')
            if not (parts[1] == '' if unified else 'memory' in parts[1].split(',')):
                continue
            member = PurePosixPath(parts[2])
            try:
                relative = member.relative_to(root)
            except ValueError:
                if member != PurePosixPath('/'):
                    continue  # This mount exposes a different subtree.
                relative = PurePosixPath('.')  # A cgroup namespace's root.
            current = location.joinpath(*relative.parts)
            for directory in (current, *current.parents):
                try:
                    value = (directory / ('memory.max' if unified else 'memory.limit_in_bytes')).read_text().strip()
                except FileNotFoundError:
                    pass  # The memory controller may be disabled at this level.
                else:
                    if not (unified and value == 'max'):
                        limits.append(_positive_integer(value))
                if directory == location:
                    break
    return limits


def host_memory_capacity_mb():
    """Return physical RAM capped by visible enforced cgroup limits, in MiB."""
    system = platform.system()
    try:
        if system == 'Linux':
            match = re.search(r'^MemTotal:\s*(\d+)\s+kB\s*$', Path('/proc/meminfo').read_text(), re.M)
            if not match:
                raise ValueError('Cannot read physical RAM from /proc/meminfo')
            capacity = min([_positive_integer(match[1]) * 1024, *_cgroup_limits()])
        elif system == 'Darwin':
            capacity = _positive_integer(subprocess.check_output(
                ['sysctl', '-n', 'hw.memsize'], text=True, timeout=10).strip())
        else:
            raise ValueError(f'Unsupported memory-capacity host: {system}')
    except (OSError, subprocess.SubprocessError) as error:
        raise ValueError(f'Cannot determine physical memory capacity: {error}') from error
    if capacity < MIB:
        raise ValueError('Physical memory capacity is below 1 MiB')
    return capacity // MIB
