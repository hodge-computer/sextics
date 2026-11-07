#!/usr/bin/env python3
"""Compile and replay the partial Lean development against the pinned sextics repo.

This verifies only the stated partial results. It does not look for, or claim,
a Submission.certificate. The independent polynomial/matrix audit is separate.
"""

import argparse
import hashlib
import fcntl
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parent
COMMIT = 'ca173aad142bd5f6bf5dd156b6798223a45df54f'
MATHLIB = '0df444a360eaa60ab8c11dca51a86af692955474'
MODULES = json.loads((ROOT / 'modules.json').read_text())


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', required=True, type=Path)
    parser.add_argument('--replay-only', action='store_true',
                        help='Replay already compiled .olean files; do not recompile')
    parser.add_argument('--modules', nargs='+', choices=MODULES, default=MODULES)
    parser.add_argument('--memory-mb', type=int, default=4096)
    parser.add_argument('--lock-file', type=Path, help='Optional shared lock to serialize Lean processes')
    args = parser.parse_args()
    repo = args.repo.resolve()
    cwd = repo / 'formal' / 'lean'
    logs = ROOT / 'verification_logs'
    logs.mkdir(exist_ok=True)
    env = os.environ.copy()

    def capture(command, *, directory=cwd):
        return subprocess.check_output(command, cwd=directory, env=env, text=True).strip()

    head = capture(['git', 'rev-parse', 'HEAD'], directory=repo)
    if head != COMMIT:
        raise SystemExit(f'Expected sextics {COMMIT}; got {head}')
    manifest = json.loads((cwd / 'lake-manifest.json').read_text())
    ml = next(p for p in manifest['packages'] if p['name'] == 'mathlib')
    if ml['rev'] != MATHLIB:
        raise SystemExit('Unexpected mathlib revision')
    env['LEAN_PATH'] = str(ROOT) + os.pathsep + capture(['lake', 'env', 'printenv', 'LEAN_PATH'])
    env['PATH'] = capture(['lake', 'env', 'printenv', 'PATH'])
    version = capture(['lean', '--version'])
    if 'version 4.33.1 ' not in version and 'version 4.33.1,' not in version:
        raise SystemExit(f'Unexpected Lean version: {version}')

    receipt = {
        'status': 'RUNNING',
        'started_utc': datetime.now(timezone.utc).isoformat(),
        'mode': 'replay_existing_objects' if args.replay_only else 'compile_then_replay',
        'sextics_commit': head, 'mathlib_revision': MATHLIB, 'lean_version': version,
        'full_certificate_proved': False,
        'kernel_replay_scope': 'Each new module replayed into its imported environment; standard imports are not replayed from an empty environment.',
        'polynomial_matrix_semantics': 'Actual rational quotient-product coefficient matrices and exhaustive orbit representative coverage are Lean theorems; geometric Hodge identification remains unproved.',
        'protected_target_sha256': sha256(repo / 'data/symmetric-sextic-residual/instance.rec'),
        'modules': [],
    }

    def save():
        (ROOT / 'lean_verification_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')

    save()
    for module in args.modules:
        source = ROOT / f'{module}.lean'
        # Deliberately strict for these sources, which need none of these tokens.
        if re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|unsafe)\b', source.read_text(), re.M):
            raise SystemExit(f'Forbidden proof placeholder or declaration in {source.name}')
        entry = {'module': module, 'source_sha256': sha256(source)}
        receipt['modules'].append(entry)
        commands = []
        if not args.replay_only:
            commands.append(('compile', ['lean', '-j1', f'-M{args.memory_mb}', '-R', str(ROOT),
                '-o', str(ROOT / f'{module}.olean'), str(source)]))
        if args.replay_only and not (ROOT / f'{module}.olean').is_file():
            raise SystemExit(f'Missing compiled module: {module}')
        commands.append(('kernel_replay', ['leanchecker', '--verbose', module]))
        for phase, command in commands:
            log = logs / f'{module}.{phase}.log'
            print(f'{phase}: {module}', flush=True)
            started = time.monotonic()
            lock = args.lock_file.open('a') if args.lock_file else None
            try:
                if lock is not None:
                    fcntl.flock(lock, fcntl.LOCK_EX)
                with log.open('w') as stream:
                    result = subprocess.run(command, cwd=cwd, env=env,
                                            stdout=stream, stderr=subprocess.STDOUT)
            finally:
                if lock is not None:
                    fcntl.flock(lock, fcntl.LOCK_UN)
                    lock.close()
            entry[phase] = {'exit_code': result.returncode,
                            'seconds': round(time.monotonic() - started, 3),
                            'log': str(log.relative_to(ROOT))}
            save()
            if result.returncode != 0:
                receipt['status'] = 'FAIL'
                save()
                print(log.read_text(), file=sys.stderr)
                return 1
        entry['object_sha256'] = sha256(ROOT / f'{module}.olean')
        save()
    receipt['status'] = 'PASS'
    receipt['completed_utc'] = datetime.now(timezone.utc).isoformat()
    save()
    print(f"PASS: {len(args.modules)} modules; full certificate remains unproved.", flush=True)
    return 0


if __name__ == '__main__':
    sys.exit(main())
