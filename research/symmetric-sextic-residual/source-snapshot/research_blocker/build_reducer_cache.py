#!/usr/bin/env python3
"""Isolated exact-key reducer-cache variant of the frozen OpenMP state driver."""
from pathlib import Path
import argparse,hashlib,json,shutil,subprocess,time
HERE=Path(__file__).resolve().parent;VENDOR=HERE/'vendor'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--audit',action='store_true');args=ap.parse_args()
    assert sha(HERE/'resumable_openmp_driver.c')=='8e9d491f376e6ea2230816c017a1320b59999f1b9c8d603d63761f42656e4782'
    patches=['msolve_compact_hash.patch','msolve_selective_columns.patch','msolve_pair_selection_bounds.patch','msolve_openmp_private_degree.patch','msolve_reducer_cache.patch']
    inputs=patches+['reducer_cache.h','resumable_reducer_cache_driver.c','build_reducer_cache.py']
    fingerprints={n:sha(HERE/n) for n in inputs}
    flags=set(next(l for l in Path('/proc/cpuinfo').read_text().splitlines() if l.startswith('flags')).split(':',1)[1].split());assert 'avx2' in flags
    vector=['-DHAVE_AVX2']+(['-DHAVE_AVX512_F'] if 'avx512f' in flags else [])
    key=hashlib.sha256(json.dumps([fingerprints,vector,args.audit],sort_keys=True).encode()).hexdigest()[:16]
    build=VENDOR/('reducer_cache_'+key);tree=build/'source';source=VENDOR/'msolve-0.11.0'
    if build.exists():raise RuntimeError('Immutable build already exists: '+str(build))
    shutil.copytree(source/'src/neogb',tree/'src/neogb');(tree/'src/msolve').mkdir(parents=True)
    shutil.copy2(source/'src/msolve/streams.h',tree/'src/msolve/streams.h');logs=[]
    for name in patches:
        r=subprocess.run(['patch','-p1','-i',str(HERE/name)],cwd=tree,capture_output=True,text=True,check=True);logs.append(r.stdout+r.stderr)
    shutil.copy2(HERE/'reducer_cache.h',tree/'src/neogb/reducer_cache.h')
    f4=tree/'src/neogb/f4.c';text=f4.read_text();needle='        done = preprocessing(mat, bs, md);';assert text.count(needle)==1
    text=text.replace(needle,'        hc_safe_boundary(bs, md, hc_round);\n\n'+needle,1)
    needle='    bs_t *bs     = *lbsp;';assert text.count(needle)==1
    text=text.replace(needle,'    if (hc_state_input) return hc_restore_native_state(lbsp, lmdp, matp, gmd, gbs, fc);\n\n'+needle,1)
    assert text.count('uint64_t hc_round = 0;')==1;text=text.replace('uint64_t hc_round = 0;','uint64_t hc_round = hc_resume_round;',1);f4.write_text(text)
    driver=build/'driver.c';shutil.copy2(HERE/'resumable_reducer_cache_driver.c',driver);binary=build/'resumable_f4_reducer_cache'
    command=['gcc','-O3','-march=native','-fopenmp','-D_GNU_SOURCE',*vector,'-I'+str(tree/'src/neogb'),'-I'+str(VENDOR/'gmp-6.3.0')]
    if args.audit:command+=['-DHC_REDUCER_CACHE_AUDIT=1']
    command+=['-o',str(binary),str(driver),'/usr/lib/x86_64-linux-gnu/libgmp.so.10.5.0','-lm'];started=time.monotonic()
    with (build/'build.log').open('w') as out:
        out.write(''.join(logs));out.flush();subprocess.run(command,stdout=out,stderr=subprocess.STDOUT,check=True)
    receipt={'status':'BUILT_NOT_YET_VALIDATED','build_directory':str(build),'binary':str(binary),'binary_sha256':sha(binary),'source_fingerprints':fingerprints,
             'compile_command':command,'audit_every_lookup_against_upstream_first_divisor':args.audit,'cache_slots':2**18,
             'cache_can_be_disabled':'--reducer-cache 0','lookup_and_materialization_profile':True,'seconds':time.monotonic()-started,
             'frozen_sources_or_binaries_overwritten':False,'target_run_performed':False}
    name='reducer_cache_audit_build_receipt.json' if args.audit else 'reducer_cache_build_receipt.json'
    (HERE/name).write_text(json.dumps(receipt,indent=2)+'\n');(build/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2),flush=True)
if __name__=='__main__':main()
