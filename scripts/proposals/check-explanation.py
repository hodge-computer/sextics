#!/usr/bin/env python3
"""Render a proposal's explanation using trusted code, before preparing Lean."""
import argparse
import json
from pathlib import Path
import subprocess
import sys

from check import ROOT, git, read_proposal, require
from acceptance import accepted_sources
sys.path.insert(0, str(ROOT / 'scripts'))
from content import render


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--base')
    mode.add_argument('--instance', help='Check the explanation in a local instance folder')
    parser.add_argument('--head')
    parser.add_argument('--author')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.instance:
        rid = args.instance
        require(rid in json.loads((ROOT / 'data/catalogue.json').read_text())['instanceIds'],
                'Choose an existing instance ID')
        local = ROOT / 'data' / rid
        files = {name: (local / name).read_bytes() for name in accepted_sources(local)}
        require('solution.md' in files, 'Missing solution.md')
    else:
        require(args.head and args.author, 'Provide --head and --author with --base')
        require(git('rev-parse', 'HEAD').decode().strip() == args.base,
                'Run the checker from the trusted base checkout')
        policy = json.loads((ROOT / '.github/solve-policy.json').read_text())
        rid, _, files, _ = read_proposal(args.base, args.head, args.author, policy)
    subprocess.run([sys.executable, str(ROOT / 'scripts/build-content.py')], cwd=ROOT, check=True)
    folder = Path('data') / rid
    rendered = render(files['solution.md'].decode(), root=ROOT,
                      source_path=folder / 'solution.md',
                      extra_files=[folder / name for name in files])
    args.output.mkdir(parents=True, exist_ok=True)
    path = args.output / 'solution.html'
    path.write_text(rendered)
    subprocess.run([sys.executable, str(ROOT / 'scripts/check-content.py'),
                    '--explanation', str(path)], cwd=ROOT, check=True)
    print(f'{folder}/solution.md: explanation links and displayed mathematics passed.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, UnicodeError) as error:
        raise SystemExit(str(error)) from None
