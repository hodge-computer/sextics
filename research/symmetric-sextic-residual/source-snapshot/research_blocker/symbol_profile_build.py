#!/usr/bin/env python3
"""Profile-only immutable copy of the frozen OpenMP native F4 build."""
from pathlib import Path
import difflib
import hashlib
import json
import shutil
import subprocess
import time

HERE = Path(__file__).resolve().parent
BASE = HERE / 'vendor/openmp_88974186e92805c0'
BASE_BINARY_SHA = '3a74bff5469683817a3596eb7f13cc10247a503081e5fd519ec125b7bf1cd069'
BASE_DRIVER_SHA = '8e9d491f376e6ea2230816c017a1320b59999f1b9c8d603d63761f42656e4782'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def once(text, old, new):
    assert text.count(old) == 1, ('unique instrumentation anchor', old)
    return text.replace(old, new, 1)


def instrument_symbol(text):
    start = text.index('static inline void find_multiplied_reducer(')
    end = text.index('\nstatic void symbolic_preprocessing(', start)
    function = text[start:end]
    function = once(function, '    len_t i, k;',
                    '    const uint64_t symbol_profile_started = symbol_profile_now();\n'
                    '    ++symbol_profile_lookup_calls;\n'
                    '    len_t i, k;')
    function = once(function, '    if (i < lml) {',
                    '    if (i < lml) {\n'
                    '        ++symbol_profile_full_tests;')
    function = once(function,
                    '        const hi_t h  = hdm.val - hdb[b[OFFSET]].val;\n'
                    '        rows[rr]  = multiplied_poly_to_matrix_row(sht, bht, h, etmp, b);',
                    '        symbol_profile_lookup_ns += symbol_profile_now() - symbol_profile_started;\n'
                    '        ++symbol_profile_lookup_hits;\n'
                    '        symbol_profile_leading_positions += (uint64_t)i + 1;\n'
                    '        const hi_t h  = hdm.val - hdb[b[OFFSET]].val;\n'
                    '        const uint64_t symbol_profile_row_started = symbol_profile_now();\n'
                    '        rows[rr]  = multiplied_poly_to_matrix_row(sht, bht, h, etmp, b);\n'
                    '        symbol_profile_materialization_ns += symbol_profile_now() - symbol_profile_row_started;\n'
                    '        ++symbol_profile_rows;\n'
                    '        symbol_profile_terms += b[LENGTH];')
    function = once(function, '        *nr             = rr + 1;\n    }\n}',
                    '        *nr             = rr + 1;\n'
                    '    } else {\n'
                    '        symbol_profile_lookup_ns += symbol_profile_now() - symbol_profile_started;\n'
                    '        ++symbol_profile_lookup_misses;\n'
                    '        symbol_profile_leading_positions += (uint64_t)lml;\n'
                    '    }\n}')
    return text[:start] + function + text[end:]


def main():
    assert sha(BASE / 'resumable_f4_openmp') == BASE_BINARY_SHA
    assert sha(BASE / 'driver.c') == BASE_DRIVER_SHA
    baseline = json.loads((BASE / 'receipt.json').read_text())
    old_symbol = (BASE / 'source/src/neogb/symbol.c').read_text()
    new_symbol = instrument_symbol(old_symbol)
    old_driver = (BASE / 'driver.c').read_text()
    new_driver = once(old_driver, '#include "gb.c"',
                      '#include "symbol_profile_support.h"\n#include "gb.c"')
    new_driver = once(new_driver,
                      '        hc_stream_basis(hc_checkpoint_path,bs,md,0);',
                      '        symbol_profile_emit("checkpoint");\n'
                      '        hc_stream_basis(hc_checkpoint_path,bs,md,0);')
    new_driver = once(new_driver, '    hc_stream_basis(output,bs,md,1);',
                      '    symbol_profile_emit("complete");\n'
                      '    hc_stream_basis(output,bs,md,1);')
    inputs = {name: sha(HERE / name) for name in
              ['symbol_profile_support.h', 'symbol_profile_build.py']}
    source_hashes = {str(path.relative_to(BASE)): sha(path)
                     for path in sorted((BASE / 'source').rglob('*')) if path.is_file()}
    key = hashlib.sha256(json.dumps([inputs, source_hashes, BASE_DRIVER_SHA],
                                   sort_keys=True).encode()).hexdigest()[:16]
    build = HERE / ('vendor/symbol_profile_' + key)
    if build.exists():
        raise RuntimeError('Immutable build already exists: ' + str(build))
    shutil.copytree(BASE / 'source', build / 'source')
    (build / 'source/src/neogb/symbol.c').write_text(new_symbol)
    (build / 'driver.c').write_text(new_driver)
    shutil.copy2(HERE / 'symbol_profile_support.h', build / 'symbol_profile_support.h')
    changes = ''.join(difflib.unified_diff(old_symbol.splitlines(True), new_symbol.splitlines(True),
                     fromfile='frozen/src/neogb/symbol.c', tofile='profile/src/neogb/symbol.c'))
    changes += ''.join(difflib.unified_diff(old_driver.splitlines(True), new_driver.splitlines(True),
                      fromfile='frozen/driver.c', tofile='profile/driver.c'))
    (HERE / 'symbol_profile_changes.patch').write_text(changes)
    (build / 'changes.patch').write_text(changes)
    binary = build / 'resumable_f4_symbol_profile'
    command = [arg.replace(str(BASE), str(build)) for arg in baseline['compile_command']]
    command[command.index('-o') + 1] = str(binary)
    started = time.monotonic()
    with (build / 'build.log').open('w') as output:
        subprocess.run(command, stdout=output, stderr=subprocess.STDOUT, check=True)
    # Confirm that only the one instrumented source file differs from the copy.
    changed = [name for name, digest in source_hashes.items() if sha(build / name) != digest]
    assert changed == ['source/src/neogb/symbol.c'], changed
    assert sha(BASE / 'driver.c') == BASE_DRIVER_SHA
    assert sha(BASE / 'resumable_f4_openmp') == BASE_BINARY_SHA
    receipt = {
        'status': 'BUILT_VALIDATION_PENDING',
        'build_directory': str(build), 'binary': str(binary), 'binary_sha256': sha(binary),
        'base_build_directory': str(BASE), 'base_binary_sha256': BASE_BINARY_SHA,
        'base_driver_sha256': BASE_DRIVER_SHA, 'input_sha256': inputs,
        'base_source_sha256': source_hashes,
        'instrumented_symbol_sha256': sha(build / 'source/src/neogb/symbol.c'),
        'instrumented_driver_sha256': sha(build / 'driver.c'),
        'changes_patch_sha256': sha(HERE / 'symbol_profile_changes.patch'),
        'changed_upstream_source_files': changed, 'compile_command': command,
        'monotonic_clock': 'CLOCK_MONOTONIC',
        'profile_counters_outside_native_metadata': True,
        'checkpoint_format_unchanged': True,
        'reducer_choice_or_algorithm_changed': False,
        'frozen_build_modified': False, 'target_run_performed': False,
        'seconds': time.monotonic() - started,
    }
    (build / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    (HERE / 'symbol_profile_build_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({key: receipt[key] for key in
                     ['status', 'binary', 'binary_sha256', 'seconds']}, indent=2), flush=True)


if __name__ == '__main__':
    main()
