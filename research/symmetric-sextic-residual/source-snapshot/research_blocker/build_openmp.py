#!/usr/bin/env python3
"""Isolated OpenMP build of the frozen native-state driver; no old file mutation."""
from pathlib import Path
import hashlib,json,shutil,subprocess,time
HERE=Path(__file__).resolve().parent
VENDOR=HERE/'vendor'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    frozen={'resumable_state_driver.c':'6aed81e4d33c82f8e4787c480adf48e5c8a405b864e20a828d8b34076f1f0ec0'}
    for name,digest in frozen.items():assert sha(HERE/name)==digest,(name,'frozen source changed')
    patches=['msolve_compact_hash.patch','msolve_selective_columns.patch','msolve_pair_selection_bounds.patch','msolve_openmp_private_degree.patch']
    fingerprints={name:sha(HERE/name) for name in patches+['resumable_openmp_driver.c','build_openmp.py']}
    flags=set(next(line for line in Path('/proc/cpuinfo').read_text().splitlines() if line.startswith('flags')).split(':',1)[1].split())
    assert 'avx2' in flags
    vector=['-DHAVE_AVX2']+(['-DHAVE_AVX512_F'] if 'avx512f' in flags else [])
    key=hashlib.sha256(json.dumps([fingerprints,vector],sort_keys=True).encode()).hexdigest()[:16]
    build=VENDOR/('openmp_'+key);tree=build/'source';source=VENDOR/'msolve-0.11.0'
    if build.exists():raise RuntimeError('Immutable build already exists: '+str(build))
    shutil.copytree(source/'src/neogb',tree/'src/neogb')
    (tree/'src/msolve').mkdir(parents=True);shutil.copy2(source/'src/msolve/streams.h',tree/'src/msolve/streams.h')
    logs=[]
    for name in patches:
        r=subprocess.run(['patch','-p1','-i',str(HERE/name)],cwd=tree,capture_output=True,text=True,check=True);logs.append(r.stdout+r.stderr)
    f4=tree/'src/neogb/f4.c';text=f4.read_text();needle='        done = preprocessing(mat, bs, md);'
    assert text.count(needle)==1
    text=text.replace(needle,'        hc_safe_boundary(bs, md, hc_round);\n\n'+needle,1)
    needle='    bs_t *bs     = *lbsp;';assert text.count(needle)==1
    text=text.replace(needle,'    if (hc_state_input) return hc_restore_native_state(lbsp, lmdp, matp, gmd, gbs, fc);\n\n'+needle,1)
    assert text.count('uint64_t hc_round = 0;')==1
    text=text.replace('uint64_t hc_round = 0;','uint64_t hc_round = hc_resume_round;',1);f4.write_text(text)
    driver=build/'driver.c';shutil.copy2(HERE/'resumable_openmp_driver.c',driver)
    binary=build/'resumable_f4_openmp'
    command=['gcc','-O3','-march=native','-fopenmp','-D_GNU_SOURCE',*vector,'-I'+str(tree/'src/neogb'),'-I'+str(VENDOR/'gmp-6.3.0'),'-o',str(binary),str(driver),'/usr/lib/x86_64-linux-gnu/libgmp.so.10.5.0','-lm']
    started=time.monotonic()
    with (build/'build.log').open('w') as out:
        out.write(''.join(logs));out.flush();subprocess.run(command,stdout=out,stderr=subprocess.STDOUT,check=True)
    receipt={'status':'BUILT_NOT_YET_VALIDATED','build_directory':str(build),'binary':str(binary),'binary_sha256':sha(binary),
             'source_fingerprints':fingerprints,'frozen_serial_source':frozen,'compile_command':command,
             'openmp':True,'default_threads':1,'allowed_threads':[1,8],'cpu_support':{'avx2':True,'avx512f':'avx512f' in flags},
             'serial_sources_and_binaries_overwritten':False,'seconds':time.monotonic()-started,
             'validation_pending':True,'target_run_performed':False}
    (HERE/'resumable_openmp_build_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    (build/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2),flush=True)
if __name__=='__main__':main()
