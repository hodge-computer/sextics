#!/usr/bin/env python3
"""Compile existing upstream transport dependencies without editing their sources."""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
REPO=ROOT/'sextics/formal/lean'
MATHLIB=REPO/'.lake/packages/mathlib'
TARGETS=['HodgeComputer.Constructions.HoldoutCover.FiniteResidueClearing',
         'HodgeComputer.Constructions.HoldoutCover.PolynomialCalculus']

def main():
    global REPO,MATHLIB
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,default=ROOT/'sextics',
                    help='Pinned sextics checkout (required outside the development layout).')
    ap.add_argument('--lock-file',type=Path,
                    help='Optional shared lock for serial Lean compilation.')
    args=ap.parse_args()
    REPO=args.repo.resolve()/'formal/lean'
    MATHLIB=REPO/'.lake/packages/mathlib'
    env=os.environ.copy()
    local_toolchain=ROOT/'toolchains/lean-4.33.1-linux/bin'
    local_shim=ROOT/'runtime_compat/own_exe_path.so'
    if local_toolchain.is_dir():
        env['PATH']=str(local_toolchain)+os.pathsep+env['PATH']
    if local_shim.is_file():
        env['LD_PRELOAD']=str(local_shim)
    lock=args.lock_file or (ROOT/'lean_compile.lock' if local_toolchain.is_dir() else None)
    env['LEAN_PATH']=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],
                                            cwd=REPO,env=env,text=True).strip()
    seen=set();order=[]
    def visit(module):
        if module in seen:return
        seen.add(module)
        package=MATHLIB if module.startswith('Mathlib.') else REPO
        source=package/(module.replace('.','/')+'.lean')
        if not source.exists():return
        for line in source.read_text().splitlines():
            words=line.split()
            if 'import' in words[:3]:
                for dependency in words[words.index('import')+1:]:visit(dependency)
        obj=package/'.lake/build/lib/lean'/(module.replace('.','/')+'.olean')
        if not obj.exists():order.append((module,package,source,obj))
    for target in TARGETS:visit(target)
    results=[]
    logs=HERE/'compilation_logs';logs.mkdir(exist_ok=True)
    print('Missing unchanged dependencies:',[m for m,_,_,_ in order],flush=True)
    for module,package,source,obj in order:
        obj.parent.mkdir(parents=True,exist_ok=True)
        log=logs/(module.rsplit('.',1)[1]+'_dependency.log')
        prefix=['flock',str(lock.resolve())] if lock else []
        command=prefix+['lean','-j1','-M4096','-R',str(package),'-o',str(obj),str(source)]
        before=hashlib.sha256(source.read_bytes()).hexdigest()
        start=time.monotonic()
        with log.open('w') as stream:
            result=subprocess.run(command,cwd=REPO,env=env,stdout=stream,stderr=subprocess.STDOUT)
        after=hashlib.sha256(source.read_bytes()).hexdigest()
        status='PASS' if result.returncode==0 and before==after else 'FAIL'
        record={'module':module,'status':status,'exit_code':result.returncode,
                'seconds':time.monotonic()-start,'source_sha256':after,
                'source_unchanged_during_compile':before==after,
                'object_sha256':hashlib.sha256(obj.read_bytes()).hexdigest() if status=='PASS' else None,
                'log':str(log),'command':command}
        results.append(record)
        (HERE/'transport_dependencies_receipt.json').write_text(json.dumps(results,indent=2)+'\n')
        print(json.dumps({k:record[k] for k in ['module','status','seconds']}),flush=True)
        if status!='PASS':
            print(log.read_text(),flush=True)
            raise SystemExit(result.returncode or 1)

if __name__=='__main__':main()
