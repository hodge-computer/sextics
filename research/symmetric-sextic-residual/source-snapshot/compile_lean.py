#!/usr/bin/env python3
"""Compile one new module against the unchanged pinned Lean environment."""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
REPO=ROOT/'sextics/formal/lean'


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('module')
    args=ap.parse_args()
    if not args.module.replace('_','').isalnum():raise ValueError('Use a local module basename')
    env=os.environ.copy()
    env['PATH']=str(ROOT/'toolchains/lean-4.33.1-linux/bin')+os.pathsep+env['PATH']
    env['LD_PRELOAD']=str(ROOT/'runtime_compat/own_exe_path.so')
    lake_path=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=REPO,env=env,text=True).strip()
    prior=[ROOT/('proof_attempt'+str(i)) for i in range(5,1,-1)]+[ROOT/'proof_attempt']
    env['LEAN_PATH']=os.pathsep.join([str(HERE)]+list(map(str,prior))+[lake_path])
    source=HERE/(args.module+'.lean');output=HERE/(args.module+'.olean')
    logdir=HERE/'compilation_logs';logdir.mkdir(exist_ok=True)
    logfile=logdir/(args.module+'.log')
    command=['flock',str(ROOT/'lean_compile.lock'),'lean','-j1','-M4096',
             '-R',str(HERE),'-o',str(output),str(source)]
    start=time.monotonic()
    with logfile.open('w') as stream:
        result=subprocess.run(command,cwd=REPO,env=env,stdout=stream,stderr=subprocess.STDOUT)
    record={'status':'PASS' if result.returncode==0 else 'FAIL','module':args.module,
            'exit_code':result.returncode,'seconds':time.monotonic()-start,
            'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
            'object_sha256':hashlib.sha256(output.read_bytes()).hexdigest() if result.returncode==0 else None,
            'log':str(logfile),'command':command,'full_certificate_proved':False}
    (HERE/(args.module+'_compile_receipt.json')).write_text(json.dumps(record,indent=2)+'\n')
    print(logfile.read_text(),end='')
    print(json.dumps(record,indent=2),flush=True)
    raise SystemExit(result.returncode)


if __name__=='__main__':main()
