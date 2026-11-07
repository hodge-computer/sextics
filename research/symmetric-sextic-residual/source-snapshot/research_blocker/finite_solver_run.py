#!/usr/bin/env python3
"""One bounded solver child, with RSS measurement and shared-memory guard."""
from pathlib import Path
import argparse,hashlib,json,os,resource,signal,subprocess,time

HERE=Path(__file__).resolve().parent

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--input',type=Path,required=True);ap.add_argument('--binary',type=Path,required=True)
    ap.add_argument('--tag',required=True);ap.add_argument('--pairs',type=int,default=64)
    ap.add_argument('--seconds',type=int,default=600);ap.add_argument('--memory-mib',type=int,default=3072)
    ap.add_argument('--eliminate',type=int,default=0);ap.add_argument('--hash-reset',type=int,default=1)
    ap.add_argument('--cgroup-stop-mib',type=int,default=6912);args=ap.parse_args()
    inp=args.input.resolve();binary=args.binary.resolve()
    log=HERE/(args.tag+'.log');out=HERE/(args.tag+'.out')
    command=[str(binary),'-v','2','-g','2','-t','1','-m',str(args.pairs),'-u',str(args.hash_reset),'-l','2','-f',str(inp),'-o',str(out)]
    if args.eliminate:command+=['-e',str(args.eliminate)]
    def limit():resource.setrlimit(resource.RLIMIT_AS,(args.memory_mib*1024**2,)*2)
    started=time.monotonic();samples=[];reason=None
    with log.open('w') as f:
        proc=subprocess.Popen(command,stdout=f,stderr=subprocess.STDOUT,preexec_fn=limit,start_new_session=True)
        while proc.poll() is None:
            row={'seconds':round(time.monotonic()-started,3)}
            try:row['cgroup_bytes']=int(Path('/sys/fs/cgroup/memory.current').read_text())
            except (FileNotFoundError,ValueError):pass
            samples.append(row)
            if row.get('cgroup_bytes',0)>=args.cgroup_stop_mib*1024**2:reason='SHARED_MEMORY_GUARD'
            elif time.monotonic()-started>=args.seconds:reason='TIME_LIMIT'
            if reason:
                os.killpg(proc.pid,signal.SIGTERM)
                try:proc.wait(timeout=2)
                except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait()
                break
            time.sleep(.5)
        exit_code=proc.wait()
    receipt={
        'tag':args.tag,'status':reason or ('FINISHED' if exit_code==0 else 'PROCESS_FAILED'),
        'exit_code':exit_code,'seconds':time.monotonic()-started,'command':command,
        'input_sha256':hashlib.sha256(inp.read_bytes()).hexdigest(),
        'binary_sha256':hashlib.sha256(binary.read_bytes()).hexdigest(),
        'address_space_limit_mib':args.memory_mib,'max_pairs_option':args.pairs,
        'hash_reset_every':args.hash_reset,'elimination_block_size':args.eliminate,
        'measured_peak_rss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
        'rss_measurement':'Linux getrusage(RUSAGE_CHILDREN), fresh runner with one subprocess',
        'cgroup_stop_mib':args.cgroup_stop_mib,
        'max_sampled_cgroup_bytes':max((x.get('cgroup_bytes',0) for x in samples),default=0),
        'output_bytes':out.stat().st_size if out.exists() else 0,'samples':samples,
        'completed_basis_independently_verified':False,'quotient_degree_known':False,'trace_values_computed':False,
        'scope':'A completed solver process still requires an independent mathematical audit; partial output is not a quotient or trace.',
    }
    (HERE/(args.tag+'_receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k not in ['samples','command']},indent=2),flush=True)

if __name__=='__main__':main()
