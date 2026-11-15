#!/usr/bin/env python3
"""Announce atlas entries, accepted solves, and new discussion comments in Discord."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request

STATE_KEY = 'notifications/discord-state.json'
SITE = 'https://hodge.computer'
REPO = 'https://github.com/hodge-computer/sextics'


def snapshot(index):
    records = index['records']
    return {'schemaVersion': 1,
            'instances': sorted(r['id'] for r in records),
            'solves': sorted(r['id'] for r in records
                             if r['formalStatus'] == 'proved')}


def validate_state(state):
    if state.get('schemaVersion') != 1:
        raise ValueError('Unsupported Discord notification state')
    for key in ('instances', 'solves'):
        if not isinstance(state.get(key), list) or not all(
                isinstance(x, str) and re.fullmatch(r'[A-Za-z0-9-]+', x) for x in state[key]):
            raise ValueError('Invalid Discord notification state')
    if not set(state['solves']) <= set(state['instances']):
        raise ValueError('Notification state contains an unknown solve')
    return state


def pending_events(index, state):
    """Retain past IDs across reorders, edits, rollbacks, and repeated deployments."""
    current = snapshot(index)
    added = set(current['instances']) - set(state['instances'])
    solved = set(current['solves']) - set(state['solves'])
    events = []
    for number, record in enumerate(index['records'], 1):
        rid = record['id']
        # An entry introduced already solved gets one solve announcement.
        if rid in solved:
            events.append(('solve', number, record))
        elif rid in added:
            events.append(('instance', number, record))
    return events


def payload(kind, number, record, site):
    rid = record['id']
    title = record['title']
    embed = {'title': f'{"New solve" if kind == "solve" else "New atlas instance"} · {number:02d}',
             'description': title, 'url': f'{SITE}/#case/{rid}',
             'color': 0x6ECCA8 if kind == 'solve' else 0x9CBCE4}
    if kind == 'solve':
        full = json.loads((site / record['path']).read_text())
        login = full['credit']['githubLogin']
        if not re.fullmatch(r'[A-Za-z0-9-]+', login):
            raise ValueError('Invalid solve attribution')
        embed['fields'] = [
            {'name': 'Contributor', 'value': f'[`{login}`](https://github.com/{login})', 'inline': True}]
    else:
        embed['fields'] = [{'name': 'Open target', 'value': f'[Explore and discuss]({SITE}/#case/{rid}/discussion)'}]
    return {'embeds': [embed], 'allowed_mentions': {'parse': []}}


def s3_read(bucket, key, *, optional=False):
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / 'object.json'
        result = subprocess.run(['aws', 's3api', 'get-object', '--bucket', bucket,
                                 '--key', key, str(path)], capture_output=True, text=True)
        if result.returncode:
            if optional and '(NoSuchKey)' in result.stderr:
                return None
            raise RuntimeError(f'Could not read notification input s3://{bucket}/{key}')
        return json.loads(path.read_text())


def s3_write(bucket, state, *, key=STATE_KEY):
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / 'state.json'
        path.write_text(json.dumps(state, indent=2) + '\n')
        subprocess.run(['aws', 's3api', 'put-object', '--bucket', bucket, '--key', key,
                        '--body', str(path), '--server-side-encryption', 'AES256',
                        '--content-type', 'application/json', '--cache-control', 'no-store'],
                       check=True, stdout=subprocess.DEVNULL)


def send(webhook, message):
    url = urllib.parse.urlsplit(webhook)
    if (url.scheme != 'https' or url.netloc != 'discord.com' or
            not re.fullmatch(r'/api(?:/v\d+)?/webhooks/\d+/[A-Za-z0-9._-]+', url.path)):
        raise ValueError('Expected a Discord incoming webhook URL')
    # wait=true confirms Discord saved the message; never print the secret URL.
    endpoint = urllib.parse.urlunsplit((url.scheme, url.netloc, url.path, 'wait=true', ''))
    request = urllib.request.Request(endpoint, json.dumps(message).encode(),
                                     {'Content-Type': 'application/json',
                                      'User-Agent': 'hodge.computer solve announcements'})
    for attempt in range(4):
        try:
            with urllib.request.urlopen(request, timeout=30) as response:
                result = json.load(response)
            message_id = result.get('id')
            if not isinstance(message_id, str) or not re.fullmatch(r'[0-9]+', message_id):
                raise RuntimeError('Discord did not confirm a saved message')
            return message_id
        except urllib.error.HTTPError as error:
            if error.code == 429 and attempt < 3:
                delay = min(60, max(1, float(json.loads(error.read()).get('retry_after', 5))))
                time.sleep(delay)
                continue
            raise RuntimeError(f'Discord rejected the announcement (HTTP {error.code})') from None
        except (urllib.error.URLError, TimeoutError):
            # Delivery may already have occurred. Do not blindly duplicate it.
            raise RuntimeError('Discord delivery could not be confirmed; inspect the channel before retrying') from None


def wait_for_site(site):
    expected = json.loads((site / 'assets/atlas/index.json').read_text())
    for attempt in range(40):
        try:
            with urllib.request.urlopen(f'{SITE}/assets/atlas/index.json?announcement={time.time_ns()}',
                                        timeout=10) as response:
                if json.load(response) == expected:
                    return
        except (OSError, ValueError):
            pass
        time.sleep(3)
    raise RuntimeError('The deployed atlas is not visible yet; retry deployment to send pending alerts')


def announce(index, state, site, deliver, save):
    for kind, number, record in pending_events(index, state):
        deliver(payload(kind, number, record, site))
        rid = record['id']
        state['instances'] = sorted(set(state['instances']) | {rid})
        if kind == 'solve':
            state['solves'] = sorted(set(state['solves']) | {rid})
        save(state)
        print(f'Announced {kind}: {rid}', flush=True)


def discussion_payload(event, site):
    """Use the event only as data; never evaluate or relay the comment body."""
    if event.get('action') != 'created':
        return None
    if event.get('repository', {}).get('full_name') != 'hodge-computer/sextics':
        raise ValueError('Unexpected discussion repository')
    comment, discussion = event['comment'], event['discussion']
    comment_id, number = comment['id'], discussion['number']
    if any(type(value) is not int or value <= 0 for value in (comment_id, number)):
        raise ValueError('Invalid discussion or comment ID')
    url = f'{REPO}/discussions/{number}#discussioncomment-{comment_id}'
    if comment.get('html_url') != url:
        raise ValueError('Unexpected discussion comment URL')
    login = comment['user']['login']
    if not isinstance(login, str) or not re.fullmatch(r'[A-Za-z0-9-]+(?:\[bot\])?', login):
        raise ValueError('Invalid discussion author')
    mapping = json.loads((site / 'discussions/index.json').read_text())
    if mapping['repository'] != 'hodge-computer/sextics':
        raise ValueError('Unexpected discussion mapping repository')
    matches = [rid for rid, thread in mapping['instances'].items() if thread['number'] == number]
    if len(matches) > 1:
        raise ValueError('Ambiguous discussion mapping')
    heading = 'New discussion comment'
    title = discussion['title']
    if matches:
        rid = matches[0]
        catalogue = json.loads((site / 'data/catalogue.json').read_text())['instanceIds']
        if rid not in catalogue:
            raise ValueError('Discussion instance is absent from the atlas')
        atlas_number = catalogue.index(rid) + 1
        heading += f' · {atlas_number:02d}'
        url = f'{SITE}/#case/{rid}/discussion/{comment_id}'
    # Titles of non-atlas discussions are user content. Render them as text.
    title = re.sub(r'([\\`*_~|\[\]()<>])', r'\\\1', ' '.join(title.split())[:512])
    return comment_id, {
        'embeds': [{'title': heading, 'description': title, 'url': url,
                    'color': 0xB6A0D6,
                    'fields': [{'name': 'Commenter', 'value': f'`{login}`', 'inline': True},
                               {'name': 'Discussion', 'value': f'[Read comment]({url})', 'inline': True}]}],
        'allowed_mentions': {'parse': []},
    }


def announce_discussion(event, site, deliver, read, save):
    item = discussion_payload(event, site)
    if item is None:
        print('No new discussion comment to announce.')
        return
    comment_id, message = item
    # Separate keys let unrelated comments arrive concurrently without losing state.
    key = f'notifications/discussion-comments/{comment_id}.json'
    prior = read(key)
    if prior is not None:
        if (prior.get('schemaVersion') != 1 or prior.get('commentId') != comment_id or
                not re.fullmatch(r'[0-9]+', str(prior.get('discordMessageId', '')))):
            raise ValueError('Invalid discussion notification state')
        print(f'Discussion comment already announced: {comment_id}')
        return
    message_id = deliver(message)
    save(key, {'schemaVersion': 1, 'commentId': comment_id, 'discordMessageId': message_id})
    print(f'Announced discussion comment: {comment_id}', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('phase', choices=('prepare', 'send', 'discussion'))
    parser.add_argument('--bucket', required=True)
    parser.add_argument('--site', type=Path, required=True)
    args = parser.parse_args()
    webhook = os.environ.get('DISCORD_SOLVE_WEBHOOK_URL', '')
    if not webhook:
        print('Discord notifications are disabled: repository secret is not configured.')
        return
    if args.phase == 'discussion':
        if os.environ.get('GITHUB_EVENT_NAME') != 'discussion_comment':
            raise ValueError('Expected a GitHub discussion_comment event')
        event = json.loads(Path(os.environ['GITHUB_EVENT_PATH']).read_text())
        announce_discussion(event, args.site, lambda message: send(webhook, message),
                            lambda key: s3_read(args.bucket, key, optional=True),
                            lambda key, value: s3_write(args.bucket, value, key=key))
        return
    state = s3_read(args.bucket, STATE_KEY, optional=True)
    if args.phase == 'prepare':
        if state is None:
            # First activation starts from what is already live, before upload.
            # Persist it now so a failed first send can be retried safely.
            state = snapshot(s3_read(args.bucket, 'assets/atlas/index.json'))
            s3_write(args.bucket, validate_state(state))
            print('Initialized notifications from the existing published atlas.')
        else:
            validate_state(state)
        return
    if state is None:
        raise RuntimeError('Notification baseline was not prepared before deployment')
    validate_state(state)
    index = json.loads((args.site / 'assets/atlas/index.json').read_text())
    if pending_events(index, state):
        wait_for_site(args.site)
        announce(index, state, args.site, lambda message: send(webhook, message),
                 lambda value: s3_write(args.bucket, value))
    else:
        print('No new atlas entries or accepted solves to announce.')


if __name__ == '__main__':
    main()
