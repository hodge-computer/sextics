#!/usr/bin/env python3
"""Record credit for merged solves. Verification belongs to pre-merge CI.

This script does not run proofs, inspect CI artifacts, or merge pull requests.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
REPOSITORY = 'hodge-computer/sextics'


def publish(number):
    pr = json.loads(subprocess.check_output(
        ['gh', 'api', f'repos/{REPOSITORY}/pulls/{number}'], timeout=120))
    if not (pr['merged'] and pr['base']['ref'] == 'main'
            and pr['base']['repo']['full_name'] == REPOSITORY):
        raise ValueError('Expected a merged pull request against main')
    merge = pr['merge_commit_sha']
    subprocess.run(['git', 'merge-base', '--is-ancestor', merge, 'HEAD'], cwd=ROOT, check=True)
    pages = json.loads(subprocess.check_output(
        ['gh', 'api', f'repos/{REPOSITORY}/pulls/{number}/files?per_page=100',
         '--paginate', '--slurp'], timeout=120))
    added = [item['filename'] for page in pages for item in page if item['status'] == 'added']
    instances = [m[1] for name in added
                 if (m := re.fullmatch(r'data/([A-Za-z0-9]+(?:-[A-Za-z0-9]+)*)/proof\.json', name))]
    for rid in instances:
        path = ROOT/'data'/rid/'acceptance.json'
        record = {'schemaVersion': 2, 'githubLogin': pr['user']['login'],
                  'acceptedAt': pr['merged_at'],
                  'pullRequest': {'number': number, 'url': pr['html_url']}}
        if path.exists():
            # Retrying publication never overwrites existing attribution.
            if json.loads(path.read_text())['pullRequest']['number'] != number:
                raise ValueError(f'{rid} already has credit for another pull request')
        else:
            path.write_text(json.dumps(record, indent=2)+'\n')
        print(f'Recorded {rid}: {pr["user"]["login"]}, PR #{number}.')
    if not instances:
        print('No new solve in this merge.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pr', type=int, required=True)
    publish(parser.parse_args().pr)
