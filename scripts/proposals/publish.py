#!/usr/bin/env python3
"""Publish one merged solve after authenticating its successful protected workflow.

This script never merges a PR, changes repository visibility, or runs proposal code.
The caller must hold trusted repository credentials; solve PRs cannot edit this code.
"""
import argparse
from datetime import datetime, timezone
import io
import json
from pathlib import Path
import subprocess
import zipfile

import yaml

from acceptance import REPOSITORY, read_acceptance, require, sha256, statement_hash, accepted_sources

ROOT = Path(__file__).resolve().parents[2]


def api(path, *, binary=False, paginate=False):
    result = subprocess.run(['gh','api',path,*(['--paginate','--slurp'] if paginate else [])],
                            check=True,stdout=subprocess.PIPE,timeout=120)
    if binary: return result.stdout
    data=json.loads(result.stdout)
    return [item for page in data for item in page] if paginate else data


def git(*args):
    return subprocess.check_output(['git',*args],cwd=ROOT)


def validate_report(report, pr, run, merge):
    require(report.get('schemaVersion') in (1,2), 'Unsupported protected report version')
    require(pr['merged'] and pr['base']['ref']=='main' and
            pr['base']['repo']['full_name']==REPOSITORY, 'Expected a merged main-branch PR')
    require(len(merge['parents'])==2 and merge['parents'][1]['sha']==pr['head']['sha'],
            'Use a merge commit preserving the checked proposal head')
    require(report['baseCommit']==merge['parents'][0]['sha'] and report['headCommit']==pr['head']['sha'],
            'PR was not merged against its checked base and head; recheck before merging')
    require(report['pullRequest']==pr['number'] and report['githubLogin']==pr['user']['login'], 'PR attribution mismatch')
    require(report['mode']=='live' and report['kernelReplay'] is True and
            report['result']=='lean-checked-awaiting-owner', 'A live protected proof check is required')
    # The Actions REST API associates a pull_request_target run with the PR
    # head, even though GITHUB_SHA and the executed workflow are from main.
    # A manual dispatch is associated with main itself.
    run_head=pr['head']['sha'] if run['event']=='pull_request_target' else report['baseCommit']
    require(run['conclusion']=='success' and run['path']=='.github/workflows/solve-proposal.yml' and
            run['event'] in ('pull_request_target','workflow_dispatch') and
            run['head_sha']==run_head, 'Receipt does not come from the protected base workflow')
    for path,expected in report['verifierSha256'].items():
        require(sha256(git('show',report['baseCommit']+':'+path))==expected, 'Verifier evidence differs from the checked base')
    require('.github/workflows/solve-proposal.yml' in report['verifierSha256'], 'Missing workflow source binding')


def publish(number):
    policy=json.loads((ROOT/'.github/solve-policy.json').read_text())
    require(policy['mode']=='live', 'Invalid publication mode')
    pr=api(f'repos/{REPOSITORY}/pulls/{number}')
    require(pr.get('merged') is True, 'PR is not merged')
    merge=api(f'repos/{REPOSITORY}/commits/{pr["merge_commit_sha"]}')
    require(subprocess.run(['git','merge-base','--is-ancestor',pr['merge_commit_sha'],'HEAD'],cwd=ROOT).returncode==0,
            'Publish from main containing the merge')
    added = git('diff','--name-only','--diff-filter=A',pr['merge_commit_sha']+'^1',pr['merge_commit_sha']).decode().splitlines()
    if not any(name.startswith('data/') and name.endswith('/proof.json') for name in added):
        print('No new solve in this merge; no publication needed.')
        return
    statuses=api(f'repos/{REPOSITORY}/commits/{pr["head"]["sha"]}/statuses?per_page=100')
    status=next((s for s in statuses if s['context']=='solve/lean'),None)
    require(status and status['state']=='success' and status['creator']['login']=='github-actions[bot]',
            'Missing successful protected solve status')
    prefix=f'https://github.com/{REPOSITORY}/actions/runs/'
    require(status['target_url'].startswith(prefix) and status['target_url'][len(prefix):].isdigit(), 'Invalid workflow link')
    run_id=int(status['target_url'][len(prefix):])
    run=api(f'repos/{REPOSITORY}/actions/runs/{run_id}')
    artifacts=api(f'repos/{REPOSITORY}/actions/runs/{run_id}/artifacts?per_page=100')['artifacts']
    name=f'solve-{number}-{pr["head"]["sha"]}'
    candidates=[a for a in artifacts if a['name']==name and not a['expired']]
    require(len(candidates)==1 and candidates[0]['size_in_bytes']<32*1024*1024, 'Missing or oversized verification artifact')
    archive=api(f'repos/{REPOSITORY}/actions/artifacts/{candidates[0]["id"]}/zip',binary=True)
    with zipfile.ZipFile(io.BytesIO(archive)) as bundle:
        reports=[entry for entry in bundle.infolist() if entry.filename=='report.json']
        require(len(reports)==1 and reports[0].file_size<4*1024*1024, 'Invalid receipt artifact')
        report=json.loads(bundle.read(reports[0]))
    validate_report(report,pr,run,merge)
    rid=report['instanceId']
    require(rid in json.loads((ROOT/'data/catalogue.json').read_text())['instanceIds'], 'Unknown instance')
    instance=yaml.safe_load((ROOT/'data'/rid/'instance.rec').read_text())
    require(statement_hash(instance)==report['statementSha256'], 'Target changed after checking')
    folder=ROOT/'data'/rid
    receipt={'schemaVersion':1,'formalAcceptance':True,'repository':REPOSITORY,'instanceId':rid,
             'githubLogin':pr['user']['login'],'submittedAt':pr['created_at'],'acceptedAt':pr['merged_at'],
             'publishedAt':datetime.now(timezone.utc).isoformat(),
             'pullRequest':{'number':number,'url':pr['html_url'],'headCommit':pr['head']['sha'],
                            'baseCommit':report['baseCommit'],'mergeCommit':pr['merge_commit_sha']},
             'run':{'id':run_id,'url':status['target_url'],'workflowPath':run['path'],'conclusion':'success'},
             'verification':report}
    path=ROOT/'data'/rid/'acceptance.json'
    if path.exists():
        previous=read_acceptance(ROOT,rid)
        require(previous['pullRequest']==receipt['pullRequest'], 'Instance already accepted through another PR')
        # A previous build may have stopped after writing the receipt. Regenerate
        # and validate the complete output before declaring a retry successful.
        receipt=previous
    else:
        # First acceptance must match the entire reviewed submission. Later
        # editorial changes are allowed by read_acceptance, including on retry.
        require(accepted_sources(folder)==report['sourceHashes'],
                'Merged proposal differs from the checked sources')
    path.parent.mkdir(exist_ok=True)
    path.write_text(json.dumps(receipt,indent=2)+'\n')
    read_acceptance(ROOT,rid)
    subprocess.run(['python3','scripts/build-content.py'],cwd=ROOT,check=True)
    subprocess.run(['python3','scripts/validate-records.py'],cwd=ROOT,check=True)
    subprocess.run(['python3','scripts/check-content.py'],cwd=ROOT,check=True)
    print(f'Published checked solve {rid} from PR #{number}; contributor {pr["user"]["login"]}.')


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pr',type=int,required=True)
    publish(parser.parse_args().pr)
