#!/usr/bin/env python3
"""Audit the public theorems and replay selected paper-formalization modules.

Run with --repo /path/to/sextics. In the combined delivery all Lean objects
are beside this script; --prior-dir is needed only in the development layout.
The audit does not assert the unproved regular-current existential.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent
MODULES = ["TwoReflectionSectors", "SignedSourceCharacters", "MonodromyImageSpanning",
           "PolynomialSupportedProjector", "SymmetricPrime", "AutomaticLegalClearing",
           "RegularEulerClearing", "CanonicalFractionCoordinates",
           "CertificateRegularCurrent", "SymmetricRegularCurrent"]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strip_comments(source):
    output = []; depth = 0; i = 0
    while i < len(source):
        pair = source[i:i+2]
        if pair == '/-':
            depth += 1; output.append('  '); i += 2
        elif depth and pair == '-/':
            depth -= 1; output.append('  '); i += 2
        elif not depth and pair == '--':
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
        else:
            output.append('\n' if source[i] == '\n' else ' ' if depth else source[i]); i += 1
    if depth:
        raise ValueError('Unterminated Lean block comment')
    return ''.join(output)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, required=True)
    ap.add_argument('--prior-dir', type=Path, action='append', default=[])
    ap.add_argument('--lock-file', type=Path)
    ap.add_argument('--kernel-modules', nargs='*', choices=MODULES, default=MODULES)
    args = ap.parse_args()
    cwd = args.repo.resolve() / 'formal/lean'
    env = os.environ.copy()
    lake = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=cwd,
                                   env=env, text=True).strip()
    env['LEAN_PATH'] = os.pathsep.join([str(HERE)] + [str(p.resolve()) for p in args.prior_dir] + [lake])
    names = []; sources = []
    for module in MODULES:
        source = HERE / (module + '.lean')
        clean = strip_comments(source.read_text())
        if re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|unsafe)\b', clean, re.M):
            raise ValueError('Unacceptable declaration in ' + module)
        scopes = []
        for line in clean.splitlines():
            line = line.strip()
            ns = re.match(r'^namespace (\S+)$', line)
            end = re.match(r'^end (\S+)$', line)
            theorem = re.match(r'^(?:@\[[^]]*\]\s*)*(?:theorem|lemma) ([^\s:(]+)', line)
            if ns:
                scopes.append(ns[1])
            elif end and scopes and scopes[-1] == end[1]:
                scopes.pop()
            elif theorem:
                names.append('.'.join(scopes + [theorem[1]]))
        sources.append({'module': module, 'source_sha256': digest(source),
                        'object_sha256': digest(HERE / (module + '.olean'))})
    assert len(names) == len(set(names))
    logs = HERE / 'paper_verification_logs'; logs.mkdir(exist_ok=True)
    program = '\n'.join('import ' + m for m in MODULES) + '\n'
    program += '\n'.join('#print axioms ' + n for n in names) + '\n'
    (logs / 'public_axioms_input.lean').write_text(program)
    prefix = ['flock', str(args.lock_file.resolve())] if args.lock_file else []
    audit = subprocess.run(prefix + ['lean', '-j1', '-M4096', '--stdin'], cwd=cwd, env=env,
                           input=program, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (logs / 'public_axioms.log').write_text(audit.stdout)
    parsed = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", audit.stdout)
    dependencies = {name: [x.strip() for x in axioms.split(',') if x.strip()] for name, axioms in parsed}
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    if audit.returncode or set(dependencies) != set(names) or any(set(v) - allowed for v in dependencies.values()):
        print(audit.stdout); raise SystemExit('Axiom audit failed')
    print(f'Axiom audit PASS: {len(names)} public theorems', flush=True)
    replay = []
    for module in args.kernel_modules:
        logfile = logs / (module + '.leanchecker.log')
        start = time.monotonic()
        with logfile.open('w') as stream:
            result = subprocess.run(prefix + ['leanchecker', '--verbose', module], cwd=cwd,
                                    env=env, stdout=stream, stderr=subprocess.STDOUT)
        replay.append({'module': module, 'exit_code': result.returncode,
                       'seconds': round(time.monotonic()-start, 3), 'log_sha256': digest(logfile)})
        if result.returncode:
            print(logfile.read_text()); raise SystemExit(result.returncode)
        print('Kernel replay PASS: ' + module, flush=True)
    receipt = {'status': 'PASS', 'public_theorems_audited': len(names),
               'allowed_axioms': sorted(allowed), 'theorem_axioms': dependencies,
               'modules': sources, 'kernel_replay': replay,
               'kernel_scope': 'Selected modules replayed against their imported environments; imports are not replayed from an empty environment.',
               'full_certificate_proved': False,
               'remaining_goal': 'SymmetricRegularCurrent.RegularGameExists'}
    (HERE / 'paper_steps_axiom_audit.json').write_text(json.dumps(receipt, indent=2)+'\n')


if __name__ == '__main__':
    main()
