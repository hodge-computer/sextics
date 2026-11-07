#!/usr/bin/env python3
"""Guard a checkpoint-capable native F4 job and retain measured evidence.

An exit75 checkpoint contains a generating set for the same ideal, not a
completed Groebner basis.  This runner never promotes it to a certificate.
"""
from pathlib import Path
import argparse,hashlib,json,os,resource,signal,subprocess,time

HERE=Path(__file__).resolve().parent

def digest(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as f:
        for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
    return h.hexdigest()

def cgroup_memory():
    """Conservatively separate reclaimable clean file cache from pressure.

    Raw memory.current includes the multi-gigabyte checkpoints just hashed.
    Clean, unmapped, non-shmem file pages can be reclaimed by the kernel.
    Dirty/writeback/mapped/unevictable pages and all kernel memory remain in
    the pressure estimate. This is a guard estimate, not a measured RSS.
    """
    root=Path('/sys/fs/cgroup')
    used=int((root/'memory.current').read_text())
    stat={k:int(v) for k,v in (row.split() for row in (root/'memory.stat').read_text().splitlines())}
    reclaimable=max(0,stat.get('file',0)-sum(stat.get(k,0) for k in
                    ['shmem','file_dirty','file_writeback','file_mapped','unevictable']))
    reclaimable=min(used,reclaimable)
    return used,reclaimable,used-reclaimable

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--input',type=Path,required=True)
    ap.add_argument('--binary',type=Path)
    ap.add_argument('--resume-state',type=Path)
    ap.add_argument('--tag',required=True)
    ap.add_argument('--seconds',type=int,default=300)
    ap.add_argument('--grace-seconds',type=int,default=180)
    ap.add_argument('--memory-mib',type=int,default=3072)
    ap.add_argument('--pairs',type=int,default=64)
    ap.add_argument('--round-budget',type=int)
    ap.add_argument('--threads',type=int)
    ap.add_argument('--signal-checkpoint',action='store_true')
    args=ap.parse_args()
    binary=args.binary or Path(json.loads((HERE/'resumable_build_receipt.json').read_text())['binary'])
    if not args.tag or any(c not in 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_-' for c in args.tag):
        raise ValueError('Tag must be a simple local basename')
    output=HERE/(args.tag+'.complete.hcf')
    checkpoint=HERE/(args.tag+'.checkpoint.hcf')
    log=HERE/(args.tag+'.log')
    for p in (output,checkpoint,log):
        if p.exists():raise FileExistsError('Use a fresh tag: '+str(p))
    cmd=[str(binary.resolve()),'--input',str(args.input.resolve()),'--output',str(output),
         '--checkpoint',str(checkpoint),'--seconds',str(args.seconds),
         '--pairs',str(args.pairs),'--reset','1','--info','2']
    if args.resume_state:
        cmd+=['--resume-state',str(args.resume_state.resolve())]
    if args.threads is not None:
        if not 1<=args.threads<=8:raise ValueError('Use between 1 and 8 threads in this workspace')
        cmd+=['--threads',str(args.threads)]
    if args.round_budget is not None:
        if args.round_budget<1:raise ValueError('Round budget must be positive')
        cmd+=['--round-budget',str(args.round_budget)]
    def limits():resource.setrlimit(resource.RLIMIT_AS,(args.memory_mib*1024**2,)*2)
    start=time.monotonic();reason=None;request=None;samples=[]
    with log.open('w') as stream:
        proc=subprocess.Popen(cmd,stdout=stream,stderr=subprocess.STDOUT,
                              preexec_fn=limits,start_new_session=True)
        while proc.poll() is None:
            elapsed=time.monotonic()-start
            used,reclaimable,pressure=cgroup_memory()
            rss_kib=0;vms_kib=0
            try:
                for row in Path(f'/proc/{proc.pid}/status').read_text().splitlines():
                    if row.startswith('VmRSS:'):rss_kib=int(row.split()[1])
                    elif row.startswith('VmSize:'):vms_kib=int(row.split()[1])
            except FileNotFoundError:pass
            samples.append({'seconds':round(elapsed,3),'shared_cgroup_bytes':used,
                            'estimated_reclaimable_clean_file_bytes':reclaimable,
                            'estimated_nonreclaimable_bytes':pressure,
                            'rss_kib':rss_kib,'vms_kib':vms_kib})
            if args.signal_checkpoint and request is None and (
                    vms_kib>args.memory_mib*1024*.80 or pressure>6.25*1024**3):
                os.kill(proc.pid,signal.SIGUSR1);request={'seconds':elapsed,'reason':'MEMORY_HEADROOM'}
            if elapsed>=args.seconds+args.grace_seconds:reason='HARD_TIME_LIMIT'
            elif pressure>=int(6.75*1024**3):reason='SHARED_NONRECLAIMABLE_MEMORY_GUARD'
            if reason:
                os.killpg(proc.pid,signal.SIGTERM)
                try:proc.wait(timeout=2)
                except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait()
                break
            time.sleep(.5)
        code=proc.wait()
    from packed_f4 import header
    files={}
    for label,path in [('complete',output),('checkpoint',checkpoint)]:
        if path.exists():files[label]={'file':path.name,'bytes':path.stat().st_size,
            'sha256':digest(path),'header':header(path)}
    sidecar=checkpoint.with_suffix(checkpoint.suffix+'.state')
    if sidecar.exists():
        files['native_state']={'file':sidecar.name,'bytes':sidecar.stat().st_size,
                               'sha256':digest(sidecar)}
    status=reason or ('NATIVE_COMPLETE_UNVERIFIED' if code==0 else
                      'PARTIAL_BASIS_CHECKPOINT' if code==75 and 'checkpoint' in files else 'PROCESS_FAILED')
    rec={'schema':'guarded-packed-f4-run-v1','tag':args.tag,'status':status,
         'exit_code':code,'seconds':time.monotonic()-start,'native_time_budget_seconds':args.seconds,
         'hard_grace_seconds':args.grace_seconds,'address_space_limit_mib':args.memory_mib,
         'requested_threads':args.threads or 1,
         'requested_round_budget':args.round_budget,
         'selected_runtime_environment':{key:os.environ.get(key) for key in
             ['MALLOC_ARENA_MAX','OMP_WAIT_POLICY','OMP_STACKSIZE']},
         'peak_rss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
         'rss_measurement':'Linux getrusage, fresh runner with one child',
         'max_sampled_shared_cgroup_bytes':max(x['shared_cgroup_bytes'] for x in samples),
         'max_estimated_nonreclaimable_bytes':max(x['estimated_nonreclaimable_bytes'] for x in samples),
         'shared_memory_guard_basis':'Raw cgroup usage less conservatively estimated reclaimable clean file cache; process peak RSS is measured separately.',
         'command':cmd,'signal_checkpoint_request':request,'samples':samples,
         'input_file':str(args.input),'input_sha256':digest(args.input),
         'input_native_state_file':str(args.resume_state) if args.resume_state else None,
         'input_native_state_sha256':digest(args.resume_state) if args.resume_state else None,
         'binary_sha256':digest(binary),'outputs':files,
         'basis_independently_verified':False,'full_trace_evaluated':False,'full_certificate_proved':False}
    (HERE/(args.tag+'_receipt.json')).write_text(json.dumps(rec,indent=2)+'\n')
    print(json.dumps({k:v for k,v in rec.items() if k not in ['samples','command']},indent=2),flush=True)

if __name__=='__main__':main()
