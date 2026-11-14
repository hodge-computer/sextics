#!/usr/bin/env python3
"""Synthetic checks for proof budgets without requiring privileged containers."""
from contextlib import redirect_stdout
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent / 'proposals'))
from resources import MIB, host_memory_capacity_mb, memory_budget
from sandbox import verify


class MemoryResources(unittest.TestCase):
    def capacity(self, files):
        def read(path):
            try:
                return files[str(path)]
            except KeyError:
                raise FileNotFoundError(str(path)) from None
        with patch('resources.platform.system', return_value='Linux'), patch.object(Path, 'read_text', read):
            return host_memory_capacity_mb()

    def test_budgets_and_reserve(self):
        for requested, capacity, expected in ((28672, 16384, 14336), (28672, 32768, 28672),
                                               (6144, 32768, 6144), (28672, 10240, 8192)):
            with self.subTest(capacity=capacity, requested=requested):
                self.assertEqual(memory_budget(requested, capacity), expected)

    def test_invalid_or_small_budget_fails(self):
        for requested, capacity in ((0, 16384), (28672, -1), (True, 16384), ('28672', 16384),
                                    (28672, 2048), (512, 16384)):
            with self.subTest(requested=requested, capacity=capacity), self.assertRaises(ValueError):
                memory_budget(requested, capacity)

    def test_physical_memory_required(self):
        self.assertEqual(self.capacity({'/proc/meminfo': 'MemTotal: 16777216 kB\n'}), 16384)
        for value in ('MemAvailable: 100 kB\n', 'MemTotal: 0 kB\n', 'MemTotal: invalid kB\n'):
            with self.subTest(value=value), self.assertRaises(ValueError):
                self.capacity({'/proc/meminfo': value})

    def cgroup_files(self, unified=True):
        return {'/proc/meminfo': 'MemTotal: 33554432 kB\n',
                '/proc/self/cgroup': '0::/tenant/job\n' if unified else '5:memory:/tenant/job\n',
                '/proc/self/mountinfo': '20 1 0:1 /tenant /cg rw - ' +
                    ('cgroup2 cgroup rw\n' if unified else 'cgroup cgroup rw,memory\n')}

    def test_v2_parent_limit_and_mount_root(self):
        files = self.cgroup_files()
        files.update({'/cg/job/memory.max': 'max', '/cg/memory.max': str(12288 * MIB)})
        self.assertEqual(self.capacity(files), 12288)
        self.assertEqual(memory_budget(28672, self.capacity(files)), 10240)
        files['/cg/job/memory.max'] = str(8192 * MIB)
        self.assertEqual(self.capacity(files), 8192)

    def test_unlimited_cgroups_preserve_physical_bound(self):
        files = self.cgroup_files()
        files.update({'/cg/job/memory.max': 'max', '/cg/memory.max': 'max'})
        self.assertEqual(self.capacity(files), 32768)
        files = self.cgroup_files(False)
        files.update({'/cg/job/memory.limit_in_bytes': str(2**63 - 4096),
                      '/cg/memory.limit_in_bytes': str(12288 * MIB)})
        self.assertEqual(self.capacity(files), 12288)

    def test_namespace_root_and_invalid_limit(self):
        files = self.cgroup_files()
        files['/proc/self/cgroup'] = '0::/\n'
        files['/cg/memory.max'] = str(8192 * MIB)
        self.assertEqual(self.capacity(files), 8192)
        files['/cg/memory.max'] = 'invalid'
        with self.assertRaises(ValueError):
            self.capacity(files)

    def test_darwin(self):
        with patch('resources.platform.system', return_value='Darwin'), \
                patch('resources.subprocess.check_output', return_value=str(32768 * MIB)):
            self.assertEqual(host_memory_capacity_mb(), 32768)

    def test_sandbox_enforces_daemon_capacity_through_compile_replay_and_audit(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            lean_root, prefix, output = root / 'formal/lean', root / 'toolchain', root / 'logs'
            for path in (lean_root, prefix / 'bin', output):
                path.mkdir(parents=True)
            (prefix / 'bin/leanchecker').touch()
            (lean_root / 'lean-toolchain').write_text('leanprover/lean4:v4.33.1\n')
            for daemon_mb, expected_mb in ((16384, 14336), (32768, 28672)):
                with self.subTest(daemon_mb=daemon_mb):
                    containers = []

                    def command(args, **kwargs):
                        if args == ['/usr/bin/lake', 'env', 'printenv', 'LEAN_PATH']:
                            return b'/trusted/dependencies\n'
                        if args == ['/usr/bin/lake', 'env', 'lean', '--print-prefix']:
                            return str(prefix).encode()
                        if args == [str(prefix / 'bin/lean'), '--version']:
                            return b'Lean (version 4.33.1, test)\n'
                        if args[:2] == ['docker', 'pull']:
                            return b''
                        if args == ['docker', 'info', '--format', '{{.MemTotal}}']:
                            return str(daemon_mb * MIB).encode()
                        if args[:2] == ['docker', 'run']:
                            containers.append(args)
                            if '--run' in args:
                                kwargs['stdout'].write(json.dumps({'theorem': 'HodgeSubmission.checked',
                                    'witnessChecked': False, 'axioms': []}).encode())
                            return b''
                        self.fail(f'Unexpected sandbox command: {args}')

                    with patch('sandbox.platform.system', return_value='Linux'), \
                            patch('sandbox.host_memory_capacity_mb', return_value=32768), \
                            patch('sandbox.os.getuid', return_value=1000), \
                            patch('sandbox.shutil.which', side_effect=lambda name: '/usr/bin/' + name), \
                            patch('sandbox.target_source', return_value=''), \
                            patch('sandbox.command', side_effect=command), \
                            patch('sandbox.subprocess.run'), redirect_stdout(io.StringIO()):
                        report = verify(root, {'Solution.lean': b''}, {}, {'theorem': 'Submission.certificate'},
                            ['Solution.lean'], [], {'memoryMb': 28672, 'timeoutSeconds': 3600}, output,
                            prepared=True)
                    self.assertEqual(len(containers), 7)  # Three compiles, three replays, and the audit.
                    for args in containers:
                        self.assertEqual(args[args.index('--memory') + 1], f'{expected_mb}m')
                        if str(prefix / 'bin/lean') in args:
                            self.assertEqual(args[args.index('-M') + 1], str(expected_mb))
                    self.assertEqual(report['requestedMemoryMb'], 28672)
                    self.assertEqual(report['effectiveMemoryMb'], expected_mb)
                    self.assertEqual(report['hostMemoryMb'], daemon_mb)


if __name__ == '__main__':
    unittest.main()
