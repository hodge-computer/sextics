#!/usr/bin/env python3
"""Replay the certificate-to-current proof and bind its exact build artifacts."""
from hashlib import sha256
from pathlib import Path
import json
import os
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
REPO = ROOT / 'sextics/formal/lean'


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    started = time.monotonic()
    module = 'CertificateRegularCurrent'
    source = HERE / (module + '.lean')
    obj = HERE / (module + '.olean')
    compilation = HERE / (module + '_compile_receipt.json')
    log = HERE / 'compilation_logs' / (module + '.log')
    record = json.loads(compilation.read_text())
    assert record['status'] == 'PASS' and record['exit_code'] == 0
    assert record['source_sha256'] == digest(source)
    assert record['object_sha256'] == digest(obj)
    assert not re.search(r'\b(sorry|admit|native_decide|unsafe)\b', source.read_text())
    assert not re.search(r'^\s*axiom\s', source.read_text(), re.M)
    axioms = {
        name: [item.strip() for item in items.split(',') if item.strip()]
        for name, items in re.findall(
            r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", log.read_text(), re.S)
    }
    expected = {
        module + '.' + endpoint for endpoint in (
            'euler_action_homogeneous', 'homogeneous_quotient_euler_weight_one',
            'certificateCurrent_euler_weight_one', 'certificateCurrent_game',
            'exists_regular_homogeneous_game_of_verify',
            'exists_regular_homogeneous_game_of_hasCertificate')
    }
    assert set(axioms) == expected
    assert all(set(items) <= {'propext', 'Classical.choice', 'Quot.sound'}
               for items in axioms.values())
    bindir = ROOT / 'toolchains/lean-4.33.1-linux/bin'
    env = os.environ.copy()
    env['PATH'] = str(bindir) + os.pathsep + env['PATH']
    env['LD_PRELOAD'] = str(ROOT / 'runtime_compat/own_exe_path.so')
    lake = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'],
                                   cwd=REPO, env=env, text=True).strip()
    prior = [ROOT / ('proof_attempt' + str(i)) for i in range(5, 1, -1)]
    prior += [ROOT / 'proof_attempt']
    env['LEAN_PATH'] = os.pathsep.join([str(HERE)] + list(map(str, prior)) + [lake])
    command = ['flock', str(ROOT / 'lean_compile.lock'), 'leanchecker', '-v', module]
    replay = subprocess.run(command, cwd=REPO, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    checker_log = HERE / 'compilation_logs' / (module + '_leanchecker.log')
    checker_log.write_text(replay.stdout)
    assert replay.returncode == 0, replay.stdout
    assert 'replaying ' + module in replay.stdout
    receipt = {
        'status': 'PASS', 'module': module,
        'source_sha256': digest(source), 'object_sha256': digest(obj),
        'compile_receipt_sha256': digest(compilation),
        'compiler_log_sha256': digest(log), 'endpoint_axioms': axioms,
        'audit_script_sha256': digest(Path(__file__)),
        'compiler_binary_sha256': digest(bindir / 'lean'),
        'checker_binary_sha256': digest(bindir / 'leanchecker'),
        'checker_command': command, 'checker_exit_code': replay.returncode,
        'checker_log_sha256': digest(checker_log),
        'import_bindings': {
            name: {'source_sha256': digest(HERE / (name + '.lean')),
                   'object_sha256': digest(HERE / (name + '.olean'))}
            for name in ('RegularEulerClearing', 'AutomaticLegalClearing')
        },
        'scope': ('An actual Verify or HasCertificate yields the regular current N_i/D, '
                  'the remainder Q/D^2, the raw game, and Euler weight one. '
                  'No existence of a certificate or current is asserted.'),
        'checker_scope': ('Same-kernel leanchecker replay of the new module against imported '
                          'objects; dependencies were not replayed with --fresh.'),
        'no_sorry_or_new_axioms': True, 'full_certificate_proved': False,
        'seconds': time.monotonic() - started,
    }
    (HERE / (module + '_kernel_receipt.json')).write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'status': 'PASS', 'module': module,
                      'seconds': receipt['seconds'], 'full_certificate_proved': False}), flush=True)


if __name__ == '__main__':
    main()
