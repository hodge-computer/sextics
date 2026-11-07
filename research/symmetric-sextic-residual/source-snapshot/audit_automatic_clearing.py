#!/usr/bin/env python3
"""Bind the three current-clearing modules to their successful kernel replays."""
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
    bindir = ROOT / 'toolchains/lean-4.33.1-linux/bin'
    environment = os.environ.copy()
    environment['PATH'] = str(bindir) + os.pathsep + environment['PATH']
    environment['LD_PRELOAD'] = str(ROOT / 'runtime_compat/own_exe_path.so')
    lake = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'],
                                   cwd=REPO, env=environment, text=True).strip()
    prior = [ROOT / ('proof_attempt' + str(i)) for i in range(5, 1, -1)] + [ROOT / 'proof_attempt']
    environment['LEAN_PATH'] = os.pathsep.join([str(HERE)] + list(map(str, prior)) + [lake])
    expected = {
        'AutomaticLegalClearing': {
            'AutomaticLegalClearing.common_legal_representatives',
            'AutomaticLegalClearing.normalized_data_of_regular_current',
            'AutomaticLegalClearing.exists_normal_chart',
            'AutomaticLegalClearing.hasCertificate_of_regular_current',
            'AutomaticLegalClearing.hasCertificate_of_regular_strict_current',
        },
        'RegularEulerClearing': {
            'RegularEulerClearing.divergence_is_regular',
            'RegularEulerClearing.correction_degree_zero',
            'RegularEulerClearing.hasCertificate_of_regular_homogeneous_game',
            'RegularEulerClearing.hasCertificate_of_exists_regular_homogeneous_game',
        },
        'CanonicalFractionCoordinates': {
            'CanonicalFractionCoordinates.coordinateDerivative_polynomial',
            'CanonicalFractionCoordinates.polynomial_partials_commute',
            'CanonicalFractionCoordinates.coordinate_derivatives_commute',
        },
    }
    records = []
    for module, endpoints in expected.items():
        source = HERE / (module + '.lean')
        obj = HERE / (module + '.olean')
        compile_receipt = HERE / (module + '_compile_receipt.json')
        compiled = json.loads(compile_receipt.read_text())
        assert compiled['status'] == 'PASS' and compiled['exit_code'] == 0
        assert compiled['source_sha256'] == digest(source)
        assert compiled['object_sha256'] == digest(obj)
        source_text = source.read_text()
        assert not re.search(r'\b(sorry|admit|native_decide|unsafe)\b', source_text)
        assert not re.search(r'^\s*axiom\s', source_text, re.M)
        log = HERE / 'compilation_logs' / (module + '.log')
        axioms = {name: [item.strip() for item in values.split(',') if item.strip()]
                  for name, values in re.findall(
                      r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", log.read_text(), re.S)}
        assert set(axioms) == endpoints
        assert all(set(values) <= {'propext', 'Classical.choice', 'Quot.sound'}
                   for values in axioms.values())
        command = ['flock', str(ROOT / 'lean_compile.lock'), 'leanchecker', '-v', module]
        result = subprocess.run(command, cwd=REPO, env=environment, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        checker_log = HERE / 'compilation_logs' / (module + '_leanchecker.log')
        checker_log.write_text(result.stdout)
        assert result.returncode == 0, result.stdout
        assert 'replaying ' + module in result.stdout
        records.append({
            'module': module, 'status': 'PASS', 'source_sha256': digest(source),
            'object_sha256': digest(obj), 'compile_receipt_sha256': digest(compile_receipt),
            'compiler_log_sha256': digest(log), 'endpoint_axioms': axioms,
            'checker_exit_code': result.returncode,
            'checker_log_sha256': digest(checker_log), 'checker_command': command,
            'no_sorry_or_new_axioms': True,
        })
        print(module + ': source binding, axioms, and kernel replay PASS', flush=True)
    imports = {}
    for name, source, obj in [
        ('CurrentVerifierBridge', ROOT / 'proof_attempt4/CurrentVerifierBridge.lean',
         ROOT / 'proof_attempt4/CurrentVerifierBridge.olean'),
        ('HodgeComputer.Verify', REPO / 'HodgeComputer/Verify.lean',
         REPO / '.lake/build/lib/lean/HodgeComputer/Verify.olean'),
        ('HodgeComputer.Constructions.HoldoutCover.HomogeneousCertificate',
         REPO / 'HodgeComputer/Constructions/HoldoutCover/HomogeneousCertificate.lean',
         REPO / '.lake/build/lib/lean/HodgeComputer/Constructions/HoldoutCover/HomogeneousCertificate.olean'),
        ('HodgeComputer.Constructions.FiniteAlgebra.FractionDerivation',
         REPO / 'HodgeComputer/Constructions/FiniteAlgebra/FractionDerivation.lean',
         REPO / '.lake/build/lib/lean/HodgeComputer/Constructions/FiniteAlgebra/FractionDerivation.olean'),
    ]:
        imports[name] = {'source_sha256': digest(source), 'object_sha256': digest(obj)}
    receipt = {
        'status': 'PASS',
        'toolchain': subprocess.check_output(['lean', '--version'], cwd=REPO,
                                            env=environment, text=True).strip(),
        'compiler_binary_sha256': digest(bindir / 'lean'),
        'checker_binary_sha256': digest(bindir / 'leanchecker'),
        'audit_script_sha256': digest(Path(__file__)), 'modules': records,
        'import_bindings': imports, 'serialized_with': 'lean_compile.lock',
        'checker_scope': 'leanchecker replayed each new module against its imported environment using the same Lean kernel. Imported dependencies were not replayed with --fresh; this is not an external proof checker.',
        'mathematical_scope': 'Automatic legal common-denominator clearing, Euler normalization of a regular weight-one ordinary game, homogeneous certificate existence, and canonical commuting fraction-field coordinates. The substantive regular-current existence statement remains unproved for the protected target.',
        'polynomial_witness_inputs_removed': True,
        'normal_chart_input_removed': True,
        'ordinary_remainder_retained': True,
        'geometric_support_proved': False, 'full_certificate_proved': False,
        'seconds': time.monotonic() - started,
    }
    (HERE / 'automatic_clearing_kernel_audit.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'status': 'PASS', 'modules': len(records),
                      'endpoint_axiom_lists': sum(len(row['endpoint_axioms']) for row in records),
                      'seconds': receipt['seconds'], 'full_certificate_proved': False}), flush=True)


if __name__ == '__main__':
    main()
