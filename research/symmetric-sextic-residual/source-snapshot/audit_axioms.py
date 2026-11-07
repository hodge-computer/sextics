#!/usr/bin/env python3
"""Ask Lean to print every new theorem's axioms and enforce the allowed set."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
from verify_partial import ROOT, MODULES, COMMIT


def strip_comments(source):
    """Remove nested Lean comments while retaining line boundaries and strings."""
    result = []
    depth = 0
    string = False
    escaped = False
    i = 0
    while i < len(source):
        char = source[i]
        pair = source[i:i+2]
        if depth:
            if pair == '/-':
                depth += 1; i += 2; continue
            if pair == '-/':
                depth -= 1; i += 2; continue
            result.append('\n' if char == '\n' else ' ')
        elif string:
            result.append(char)
            if escaped:
                escaped = False
            elif char == '\\':
                escaped = True
            elif char == '"':
                string = False
        elif pair == '/-':
            depth = 1; result.append('  '); i += 2; continue
        elif pair == '--':
            end = source.find('\n', i)
            if end == -1:
                break
            result.append('\n'); i = end + 1; continue
        else:
            result.append(char)
            if char == '"':
                string = True
        i += 1
    if depth:
        raise ValueError('Unterminated Lean block comment')
    return ''.join(result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    args = parser.parse_args()
    repo = args.repo.resolve()
    cwd = repo / 'formal/lean'
    env = os.environ.copy()
    def capture(command, directory=cwd):
        return subprocess.check_output(command, cwd=directory, env=env, text=True).strip()
    assert capture(['git', 'rev-parse', 'HEAD'], repo) == COMMIT
    env['LEAN_PATH'] = str(ROOT) + os.pathsep + capture(['lake', 'env', 'printenv', 'LEAN_PATH'])
    env['PATH'] = capture(['lake', 'env', 'printenv', 'PATH'])

    names = []
    for module in MODULES:
        scopes = []
        for line in strip_comments((ROOT / f'{module}.lean').read_text()).splitlines():
            line = line.strip()
            ns = re.match(r'^namespace ([A-Za-z0-9_.]+)$', line)
            ending = re.match(r'^end ([A-Za-z0-9_.]+)$', line)
            thm = re.match(r'^(?:@\[[^]]*\]\s*)*(?:theorem|lemma) ([^\s:(]+)', line)
            if ns:
                scopes.append(ns.group(1))
            elif ending and scopes and scopes[-1] == ending.group(1):
                scopes.pop()
            elif thm:
                names.append('.'.join(scopes + [thm.group(1)]))
    assert len(names) == len(set(names))
    program = '\n'.join('import ' + m for m in MODULES) + '\n'
    program += '\n'.join('#print axioms ' + n for n in names) + '\n'
    logs = ROOT / 'verification_logs'
    logs.mkdir(exist_ok=True)
    (logs / 'axiom_audit_input.lean').write_text(program)
    result = subprocess.run(['lean', '-j1', '-M4096', '--stdin'], cwd=cwd,
                            env=env, input=program, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (logs / 'axiom_audit.log').write_text(result.stdout)
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    actual = {}
    for name, text in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", result.stdout):
        actual[name] = [a.strip() for a in text.split(',') if a.strip()]
    for name in re.findall(r"'([^']+)' does not depend on any axioms", result.stdout):
        actual[name] = []
    success = (result.returncode == 0 and set(actual) == set(names)
               and all(set(a) <= allowed for a in actual.values()))
    receipt = {'status': 'PASS' if success else 'FAIL',
               'lean_exit_code': result.returncode, 'theorems_requested': len(names),
               'theorems_reported': len(actual), 'allowed_axioms': sorted(allowed),
               'theorem_axioms': actual,
               'log': 'verification_logs/axiom_audit.log',
               'full_certificate_proved': False}
    (ROOT / 'axiom_audit_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(receipt['status'], len(actual), 'theorem axiom reports')
    if not success:
        print(result.stdout)
    return 0 if success else 1


if __name__ == '__main__':
    raise SystemExit(main())
