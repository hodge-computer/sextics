#!/usr/bin/env python3
"""Build missing unchanged dependencies sequentially with the shared Lean lock."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
REPO = ROOT / 'sextics/formal/lean'
MATHLIB = REPO / '.lake/packages/mathlib'


def main():
    visited = set()
    needed = []

    def visit(module):
        if module in visited:
            return
        visited.add(module)
        package = MATHLIB if module.startswith('Mathlib.') else REPO
        relative = module.replace('.', '/')
        source = package / (relative + '.lean')
        target = package / '.lake/build/lib/lean' / (relative + '.olean')
        if not source.exists():
            return
        # Existing cached objects can themselves have missing dependencies.
        for line in source.read_text().splitlines():
            words = line.split()
            if words and words[0] == 'import':
                for dependency in words[1:]:
                    visit(dependency)
            elif len(words) > 1 and words[:2] == ['public', 'import']:
                for dependency in words[2:]:
                    visit(dependency)
        if not target.exists():
            needed.append((module, package, source, target))

    for module in ['HodgeComputer.Constructions.HoldoutCover.HomogeneousCertificate',
                   'Mathlib.Algebra.MvPolynomial.NoZeroDivisors',
                   'Mathlib.RingTheory.MvPolynomial.EulerIdentity',
                   'Mathlib.RingTheory.Localization.Integer']:
        visit(module)
    print('Missing unchanged dependencies:', [item[0] for item in needed], flush=True)
    environment = os.environ.copy()
    environment['PATH'] = str(ROOT / 'toolchains/lean-4.33.1-linux/bin') + os.pathsep + environment['PATH']
    environment['LD_PRELOAD'] = str(ROOT / 'runtime_compat/own_exe_path.so')
    environment['LEAN_PATH'] = subprocess.check_output(
        ['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=REPO, env=environment, text=True).strip()
    logs = HERE / 'compilation_logs'
    logs.mkdir(exist_ok=True)
    receipt = HERE / 'automatic_clearing_dependencies_receipt.json'
    records = json.loads(receipt.read_text()) if receipt.exists() else []
    for module, package, source, target in needed:
        target.parent.mkdir(parents=True, exist_ok=True)
        log = logs / ('dependency_' + module + '.log')
        start = time.monotonic()
        command = ['flock', str(ROOT / 'lean_compile.lock'), 'lean', '-j1', '-M4096',
                   '-R', str(package), '-o', str(target), str(source)]
        with log.open('w') as output:
            result = subprocess.run(command, cwd=REPO, env=environment,
                                    stdout=output, stderr=subprocess.STDOUT)
        row = {'module': module, 'exit_code': result.returncode,
               'seconds': time.monotonic() - start,
               'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
               'log': str(log.relative_to(HERE)), 'source_modified': False}
        records = [old for old in records if old['module'] != module] + [row]
        receipt.write_text(json.dumps(records, indent=2) + '\n')
        print(json.dumps(row), flush=True)
        if result.returncode:
            print(log.read_text(), flush=True)
            raise SystemExit(result.returncode)


if __name__ == '__main__':
    main()
