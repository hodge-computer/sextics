#!/usr/bin/env python3
"""Distinguish solve submissions from owner-reviewed source maintenance."""
import argparse
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
SOLUTION = re.compile(r'data/([^/]+)/(proof\.json|solution\.md|witness\.json|[A-Z][A-Za-z0-9_]*\.lean)')


def is_solve_change(kind, path, accepted_instance=False):
    match = SOLUTION.fullmatch(path)
    if not match:
        return False
    # Existing solves are maintained through Repository build, which reverifies
    # changed proof sources. Only the trusted base can establish this status;
    # adding an acceptance file in a proposal cannot bypass the solve checker.
    return not accepted_instance


def classify(base, head):
    if not all(re.fullmatch(r'[0-9a-f]{40}', sha) for sha in (base, head)):
        raise ValueError('Use immutable full commit SHAs')
    raw = subprocess.check_output(['git', 'diff', '--name-status', '--no-renames',
                                   '-z', base+'...'+head], cwd=ROOT).decode()
    fields = raw.split('\0')[:-1]
    for kind, path in zip(fields[::2], fields[1::2]):
        accepted = False
        match = SOLUTION.fullmatch(path)
        if match:
            result = subprocess.run(['git', 'show',
                f'{base}:data/{match[1]}/acceptance.json'], cwd=ROOT,
                capture_output=True)
            accepted = result.returncode == 0
        if is_solve_change(kind, path, accepted):
            return 'solve'
    return 'maintenance'


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', required=True)
    parser.add_argument('--head', required=True)
    args = parser.parse_args()
    print(classify(args.base, args.head))
