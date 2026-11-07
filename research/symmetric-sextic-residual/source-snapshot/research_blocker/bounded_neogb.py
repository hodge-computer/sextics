#!/usr/bin/env python3
"""One guarded native-core computation, with actual RSS and no trace claims."""
from pathlib import Path
import argparse,hashlib,json,os,resource,signal,subprocess,sys,time
HERE=Path(__file__).resolve().parent
def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--input',type=Path,required=True)
    ap.add_argument('--library',type=Path,default=HERE/'vendor/libneogb_compact.so')
    ap.add_argument('--tag',required=True)
    ap.add_argument('--seconds',type=int,default=600)
    ap.add_argument('--memory-mib',type=int,default=3072)
    ap.add_argument('--pairs',type=int,default=32)
    ap.add_argument('--reset',type=int,default=1)
    ap.add_argument('--elim',type=int,default=0)
    args=ap.parse_args()
    output=HERE/(args.tag+'.basis.jsonl');log=HERE/(args.tag+'.log')
    cmd=[sys.executable,str(HERE/'neogb_solver.py'),'--input',str(args.input.resolve()),
         '--library',str(args.library.resolve()),'--output',str(output),'--pairs',str(args.pairs),
         '--reset',str(args.reset),'--elim',str(args.elim)]
    def limits():resource.setrlimit(resource.RLIMIT_AS,(args.memory_mib*1024**2,)*2)
    start=time.monotonic();reason=None;samples=[]
    with log.open('w') as stream:
        proc=subprocess.Popen(cmd,stdout=stream,stderr=subprocess.STDOUT,preexec_fn=limits,start_new_session=True)
        while proc.poll() is None:
            elapsed=time.monotonic()-start
            used=int(Path('/sys/fs/cgroup/memory.current').read_text())
            samples.append({'seconds':round(elapsed,3),'shared_cgroup_bytes':used})
            if elapsed>=args.seconds:reason='TIME_LIMIT'
            elif used>=int(6.75*1024**3):reason='SHARED_MEMORY_GUARD'
            if reason:
                os.killpg(proc.pid,signal.SIGTERM)
                try:proc.wait(timeout=2)
                except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait()
                break
            time.sleep(.25)
        code=proc.wait()
    rec={'tag':args.tag,'status':reason or ('FINISHED' if code==0 else 'PROCESS_FAILED'),
         'exit_code':code,'seconds':time.monotonic()-start,'command':cmd,
         'address_space_limit_mib':args.memory_mib,
         'peak_rss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
         'rss_measurement':'Linux getrusage, fresh runner with one child',
         'max_sampled_shared_cgroup_bytes':max(x['shared_cgroup_bytes'] for x in samples),
         'samples':samples,'input_sha256':hashlib.sha256(args.input.read_bytes()).hexdigest(),
         'library_sha256':hashlib.sha256(args.library.read_bytes()).hexdigest(),
         'output_bytes':output.stat().st_size if output.exists() else 0,
         'basis_independently_verified':False,'full_trace_evaluated':False}
    (HERE/(args.tag+'_receipt.json')).write_text(json.dumps(rec,indent=2)+'\n')
    print(json.dumps({k:v for k,v in rec.items() if k not in ['samples','command']},indent=2),flush=True)
if __name__=='__main__':main()
