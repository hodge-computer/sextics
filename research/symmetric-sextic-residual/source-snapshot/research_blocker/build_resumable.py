#!/usr/bin/env python3
"""Isolated SIMD driver build; never rewrites an existing mapped library."""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import time

HERE=Path(__file__).resolve().parent
VENDOR=HERE/'vendor'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--audit',action='store_true')
    parser.add_argument('--dictionary-import',action='store_true',help='Build the direct packed dictionary importer in a separate immutable directory.')
    parser.add_argument('--native-state',action='store_true',help='Build the dictionary importer with an optional native-boundary pair-queue sidecar.')
    args=parser.parse_args()
    if args.dictionary_import and args.native_state:parser.error('Choose one driver variant.')
    driver_name='resumable_state_driver.c' if args.native_state else 'resumable_dictionary_driver.c' if args.dictionary_import else 'resumable_driver.c'
    patches=['msolve_compact_hash.patch','msolve_selective_columns.patch']
    if args.native_state:patches.append('msolve_pair_selection_bounds.patch')
    inputs=patches+[driver_name]
    fingerprints={name:sha(HERE/name) for name in inputs}
    cpu=set()
    for line in Path('/proc/cpuinfo').read_text().splitlines():
        if line.startswith('flags'):
            cpu=set(line.split(':',1)[1].split());break
    assert 'avx2' in cpu,'Requested SIMD build requires verified CPU AVX2 support.'
    vector_flags=['-DHAVE_AVX2']
    if 'avx512f' in cpu:vector_flags.append('-DHAVE_AVX512_F')
    key=hashlib.sha256(json.dumps([fingerprints,vector_flags,args.audit],sort_keys=True).encode()).hexdigest()[:16]
    build=VENDOR/('resumable_'+key);tree=build/'source';source=VENDOR/'msolve-0.11.0'
    if build.exists():
        raise RuntimeError('This immutable build directory already exists: '+str(build))
    shutil.copytree(source/'src/neogb',tree/'src/neogb')
    (tree/'src/msolve').mkdir(parents=True);shutil.copy2(source/'src/msolve/streams.h',tree/'src/msolve/streams.h')
    logs=[]
    for name in patches:
        result=subprocess.run(['patch','-p1','-i',str(HERE/name)],cwd=tree,capture_output=True,text=True,check=True)
        logs.append(result.stdout+result.stderr)
    f4=tree/'src/neogb/f4.c';text=f4.read_text();needle='        done = preprocessing(mat, bs, md);'
    assert text.count(needle)==1 and 'uint64_t hc_round' in text
    text=text.replace(needle,'        hc_safe_boundary(bs, md, hc_round);\n\n'+needle,1)
    if args.native_state:
        initialize='    bs_t *bs     = *lbsp;'
        assert text.count(initialize)==1 and text.count('uint64_t hc_round = 0;')==1
        text=text.replace(initialize,'    if (hc_state_input) return hc_restore_native_state(lbsp, lmdp, matp, gmd, gbs, fc);\n\n'+initialize,1)
        text=text.replace('uint64_t hc_round = 0;','uint64_t hc_round = hc_resume_round;',1)
    f4.write_text(text)
    driver=build/'driver.c';shutil.copy2(HERE/driver_name,driver)
    binary=build/'resumable_f4';gmp=VENDOR/'gmp-6.3.0'
    command=['gcc','-O3','-march=native','-D_GNU_SOURCE',*vector_flags,
             '-I'+str(tree/'src/neogb'),'-I'+str(gmp)]
    if args.audit:command+=['-DHC_COMPACT_AUDIT=1']
    command+=['-o',str(binary),str(driver),'/usr/lib/x86_64-linux-gnu/libgmp.so.10.5.0','-lm']
    started=time.monotonic()
    with (build/'build.log').open('w') as out:
        out.write(''.join(logs));out.flush();subprocess.run(command,stdout=out,stderr=subprocess.STDOUT,check=True)
    receipt={'status':'BUILT_NOT_YET_VALIDATED','build_directory':str(build),'binary':str(binary),
             'binary_sha256':sha(binary),'source_fingerprints':fingerprints,'compile_command':command,
             'cpu_support':{'avx2':'avx2' in cpu,'avx512f':'avx512f' in cpu},
             'compaction_internal_audit':args.audit,'dictionary_native_import':args.dictionary_import or args.native_state,
             'native_boundary_state':args.native_state,'seconds':time.monotonic()-started,
             'active_compact_library_overwritten':False,'complete_basis_validation_pending':True}
    receipt_name='resumable_state_build_receipt.json' if args.native_state else 'resumable_dictionary_build_receipt.json' if args.dictionary_import else 'resumable_build_receipt.json'
    (HERE/receipt_name).write_text(json.dumps(receipt,indent=2)+'\n')
    (build/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2),flush=True)

if __name__=='__main__':main()
