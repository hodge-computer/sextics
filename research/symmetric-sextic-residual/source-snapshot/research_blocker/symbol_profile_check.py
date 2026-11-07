#!/usr/bin/env python3
"""Small byte-for-byte baseline and checkpoint checks; never runs the target."""
from pathlib import Path
import hashlib
import json
import os
import re
import resource
import struct
import subprocess
import time

HERE = Path(__file__).resolve().parent
ENV = {**os.environ, 'MALLOC_ARENA_MAX': '2', 'OMP_WAIT_POLICY': 'PASSIVE',
       'OMP_STACKSIZE': '4M', 'OPENBLAS_NUM_THREADS': '1'}
PROFILE = re.compile(r'^\[symbol_profile\] (.*)$', re.M)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def memory_limit():
    resource.setrlimit(resource.RLIMIT_AS, (1024**3,) * 2)


def main():
    started = time.monotonic()
    build = json.loads((HERE / 'symbol_profile_build_receipt.json').read_text())
    binary = Path(build['binary'])
    base = Path(build['base_build_directory'])
    folder = Path(build['build_directory']) / 'checks'
    folder.mkdir(exist_ok=True)
    assert sha(binary) == build['binary_sha256']
    assert sha(base / 'resumable_f4_openmp') == build['base_binary_sha256']

    def run(name, inp, checkpoint=None, state=None, budget=None):
        output = folder / (name + '.hcf')
        command = [str(binary), '--input', str(inp), '--output', str(output),
                   '--pairs', '1', '--info', '2', '--threads', '8']
        if checkpoint:
            command += ['--checkpoint', str(checkpoint)]
        if state:
            command += ['--resume-state', str(state)]
        if budget:
            command += ['--round-budget', str(budget)]
        result = subprocess.run(command, capture_output=True, text=True, timeout=30,
                                env=ENV, preexec_fn=memory_limit)
        (folder / (name + '.log')).write_text(result.stderr + result.stdout)
        assert result.returncode in (0, 75), (name, result.returncode, result.stderr)
        entries = PROFILE.findall(result.stderr)
        assert len(entries) == 1, (name, entries)
        profile = dict(part.split('=', 1) for part in entries[0].split())
        counts = {key: int(profile[key]) for key in
                  ['lookup_calls', 'lookup_hits', 'lookup_misses', 'leading_positions',
                   'full_divisibility_tests', 'materialized_rows', 'materialized_terms',
                   'lookup_ns', 'materialization_ns']}
        assert counts['lookup_calls'] == counts['lookup_hits'] + counts['lookup_misses']
        assert counts['materialized_rows'] == counts['lookup_hits']
        assert counts['materialized_terms'] >= counts['materialized_rows']
        assert counts['full_divisibility_tests'] <= counts['leading_positions']
        assert counts['lookup_ns'] > 0
        assert counts['materialization_ns'] > 0
        assert profile['phase'] == ('complete' if result.returncode == 0 else 'checkpoint')
        assert '[parallel] requested_threads=8 actual_threads=8 dynamic=0' in result.stderr
        return result, output, counts

    complete = []
    for name in ['cyclic4', 'mixed16', 'block2', 'degree_fall']:
        result, output, counts = run(name, base / 'checks' / (name + '.hcf'))
        assert result.returncode == 0
        reference = base / 'checks' / (name + '_omp8.hcf')
        assert output.read_bytes() == reference.read_bytes(), name
        complete.append({'case': name, 'threads': 8,
                         'complete_output_byte_identical_to_frozen_OpenMP': True,
                         'output_sha256': sha(output), 'profile': counts})

    cp = folder / 'cyclic4_checkpoint.hcf'
    first, _, first_counts = run('cyclic4_checkpoint_unused', base / 'checks/cyclic4.hcf',
                                 checkpoint=cp, budget=2)
    assert first.returncode == 75
    assert first.stderr.index('[symbol_profile]') < first.stderr.index('[state] saved')
    state = Path(str(cp) + '.state')
    assert state.read_bytes()[:8] == b'HCF4ST01'
    second, output, second_counts = run('cyclic4_resumed', cp, state=state)
    assert second.returncode == 0
    assert 'initial pair generation skipped' in second.stderr
    assert output.read_bytes() == (base / 'checks/cyclic4_omp8.hcf').read_bytes()
    abi = struct.unpack_from('<12I', state.read_bytes(), 8)[1]
    frozen_abi = json.loads((HERE / 'resumable_openmp_validation_receipt.json').read_text())['native_metadata_ABI_bytes']
    assert abi == frozen_abi

    # One frozen-produced state is consumed directly to check incoming compatibility.
    frozen_cp = base / 'checks/cyclic4_from8_to4.hcf'
    third, output, incoming_counts = run('cyclic4_frozen_state', frozen_cp,
                                         state=Path(str(frozen_cp) + '.state'))
    assert third.returncode == 0
    assert 'initial pair generation skipped' in third.stderr
    assert output.read_bytes() == (base / 'checks/cyclic4_omp8.hcf').read_bytes()
    receipt = {
        'status': 'PASS', 'binary': str(binary), 'binary_sha256': build['binary_sha256'],
        'frozen_OpenMP_binary_sha256': build['base_binary_sha256'],
        'complete_checks': complete,
        'checkpoint_profile_emitted_before_serialization': True,
        'profile_checkpoint_resume_byte_identical_to_frozen_complete_output': True,
        'frozen_OpenMP_sidecar_consumed_successfully': True,
        'native_metadata_ABI_bytes': abi,
        'checkpoint_profile': first_counts, 'resumed_profile': second_counts,
        'incoming_frozen_state_profile': incoming_counts,
        'profile_counters_process_local_not_serialized': True,
        'target_run_performed': False, 'frozen_build_modified': False,
        'scope': 'Profile-only instrumentation; small exact byte comparisons and native-state compatibility. No target quotient or trace result.',
        'seconds': time.monotonic() - started,
    }
    (HERE / 'symbol_profile_validation_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'status': 'PASS', 'complete_checks': len(complete),
                      'native_metadata_ABI_bytes': abi, 'seconds': receipt['seconds'],
                      'binary': str(binary)}, indent=2), flush=True)


if __name__ == '__main__':
    main()
