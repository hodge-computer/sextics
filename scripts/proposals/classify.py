#!/usr/bin/env python3
"""Distinguish solve submissions from owner-reviewed source maintenance."""
import argparse
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
SOLUTION = re.compile(r'data/([^/]+)/(proof\.json|solution\.md|witness\.json|[A-Z][A-Za-z0-9_]*\.lean)')


def is_solve_change(kind, path, accepted_explanation=False):
    match = SOLUTION.fullmatch(path)
    if not match:
        return False
    # Only ordinary edits to prose with acceptance on the trusted base are editorial.
    # Additions, deletions, type changes, and every proof/witness change still
    # enter the strict solve checker. A receipt added by the PR grants nothing.
    return not (kind == 'M' and match[2] == 'solution.md' and accepted_explanation)


def classify(base, head):
    if not all(re.fullmatch(r'[0-9a-f]{40}', sha) for sha in (base, head)):
        raise ValueError('Use immutable full commit SHAs')
    raw = subprocess.check_output(['git', 'diff', '--name-status', '--no-renames',
                                   '-z', base+'...'+head], cwd=ROOT).decode()
    fields = raw.split('\0')[:-1]
    for kind, path in zip(fields[::2], fields[1::2]):
        accepted = False
        match = SOLUTION.fullmatch(path)
        if kind == 'M' and match and match[2] == 'solution.md':
            result = subprocess.run(['git', 'show',
                f'{base}:data/{match[1]}/acceptance.json'], cwd=ROOT,
                capture_output=True)
            if result.returncode == 0:
                receipt = json.loads(result.stdout)
                accepted = (receipt.get('formalAcceptance') is True and
                            receipt.get('instanceId') == match[1])
        if is_solve_change(kind, path, accepted):
            return 'solve'
    return 'maintenance'


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', required=True)
    parser.add_argument('--head', required=True)
    args = parser.parse_args()
    print(classify(args.base, args.head))
