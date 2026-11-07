#!/usr/bin/env python3
"""Independent small-basis and cross-thread native-state checks; no target solve."""
from pathlib import Path
import hashlib,json,os,re,resource,struct,subprocess,time
import sympy as S
from sympy.polys.orderings import grevlex
from packed_f4 import write,rows,header
from check_resumable import canon
HERE=Path(__file__).resolve().parent
TEAM=re.compile(r'\[parallel\] requested_threads=(\d+) actual_threads=(\d+) dynamic=(\d+) md_abi_bytes=(\d+)')
ROUND=re.compile(r'^\s*(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s+x\s+(\d+)\s+[\d.]+%\s+(\d+) new\s+(\d+) zero',re.M)
ENV={**os.environ,'MALLOC_ARENA_MAX':'2','OMP_WAIT_POLICY':'PASSIVE','OMP_STACKSIZE':'4M','OPENBLAS_NUM_THREADS':'1'}
def limit():resource.setrlimit(resource.RLIMIT_AS,(1024**3,)*2)
def run(exe,inp,out,threads=None,checkpoint=None,state=None,budget=None):
    command=[str(exe),'--input',str(inp),'--output',str(out),'--pairs','1','--info','2']
    if threads is not None:command+=['--threads',str(threads)]
    if checkpoint:command+=['--checkpoint',str(checkpoint)]
    if state:command+=['--resume-state',str(state)]
    if budget:command+=['--round-budget',str(budget)]
    p=subprocess.run(command,capture_output=True,text=True,timeout=30,env=ENV,preexec_fn=limit)
    out.with_suffix('.log').write_text(p.stderr+p.stdout)
    assert p.returncode in (0,75),(p.returncode,p.stderr,p.stdout)
    if threads is not None:
        team=TEAM.search(p.stderr);assert team and tuple(map(int,team.groups()[:3]))==(threads,threads,0)
    return p,[tuple(map(int,m)) for m in ROUND.findall(p.stderr)]
def main():
    started=time.monotonic();build=json.loads((HERE/'resumable_openmp_build_receipt.json').read_text());omp=Path(build['binary'])
    serial=Path(json.loads((HERE/'resumable_state_build_receipt.json').read_text())['binary'])
    folder=Path(build['build_directory'])/'checks';folder.mkdir(exist_ok=True)
    x,y,z,w=S.symbols('x y z w')
    cases=[('quadratic',(x,y),[x*x+y*y-1,x-y],37,0),
           ('nonreduced',(x,y),[x*x,x*y,y*y],101,0),
           ('unit',(x,y),[x*x,y-x,x*y-1,x*y],37,0),
           ('positive_dimension',(x,y,z),[x*y-z*z,x*x-y*z],101,0),
           ('mixed16',(x,y,z),[7*x*x+5*y*z+1,3*y*y+4*x*z+2,6*z*z+2*x*y+3],1009,0),
           ('mixed32',(x,y,z),[x*x+y*z+1,y*y+x*z+2,z*z+x*y+3],65537,0),
           ('degree_fall',(x,y,z),[x*x*y+x*z+y,y*y*z+y*x+z,z*z*x+z*y+x],1073741827,0),
           ('cyclic4',(x,y,z,w),[x+y+z+w,x*y+y*z+z*w+w*x,x*y*z+y*z*w+z*w*x+w*x*y,x*y*z*w-1],101,0),
           ('block1',(x,y,z),[7*x*x+5*y*z+1,3*y*y+4*x*z+2,6*z*z+2*x*y+3],37,1),
           ('block2',(x,y,z),[7*x*x+5*y*z+1,3*y*y+4*x*z+2,6*z*z+2*x*y+3],65537,2)]
    results=[];restart=[];abi=set()
    for name,vs,polys,p,elim in cases:
        inputs=[{e:int(c)%p for e,c in S.Poly(f,*vs,modulus=p).terms()} for f in polys]
        order=grevlex if not elim else lambda m,e=elim:(grevlex(m[:e]),grevlex(m[e:]))
        reference=S.groebner(polys,*vs,modulus=p,order=order)
        expected=canon([dict(f.terms()) for f in reference.polys],p)
        inp=folder/(name+'.hcf');write(inp,[str(v) for v in vs],p,inputs,elim=elim)
        sr,sr_rounds=run(serial,inp,folder/(name+'_serial.hcf'))
        assert canon(rows(folder/(name+'_serial.hcf')),p)==expected
        for threads in (4,8):
            out=folder/f'{name}_omp{threads}.hcf';r,rounds=run(omp,inp,out,threads)
            assert r.returncode==0 and header(out)['complete'] and canon(rows(out),p)==expected,(name,threads)
            abi.add(int(TEAM.search(r.stderr)[4]));summary=json.loads(r.stdout.splitlines()[-1])
            results.append({'case':name,'prime':p,'elimination_block':elim,'threads':threads,
                            'actual_OpenMP_team_verified':True,'basis_matches_serial_and_SymPy':True,
                            'matrix_round_data_matches_serial':rounds==sr_rounds,'peak_rss_kib':summary['peak_rss_kib']})
        if name in ('cyclic4','mixed16','block1','block2'):
            for producer,consumer in [(1,4),(1,8),(4,8),(8,4),(4,1),(8,1)]:
                cp=folder/f'{name}_from{producer}_to{consumer}.hcf';unused=folder/f'{name}_unused_{producer}_{consumer}.hcf'
                first,first_rounds=run(serial if producer==1 else omp,inp,unused,None if producer==1 else producer,checkpoint=cp,budget=2)
                assert first.returncode==75
                state=cp.with_suffix('.hcf.state');raw=state.read_bytes();a=struct.unpack_from('<12I',raw,8);b=struct.unpack_from('<3Q',raw,56)
                abi.add(a[1]);out=folder/f'{name}_resumed_{producer}_{consumer}.hcf'
                second,second_rounds=run(serial if consumer==1 else omp,cp,out,None if consumer==1 else consumer,state=state)
                assert second.returncode==0 and 'initial pair generation skipped' in second.stderr
                restored=re.search(r'\[state\] restored completed_rounds=(\d+) pending_pairs=(\d+)',second.stderr)
                assert restored and (int(restored[1]),int(restored[2]))==(b[1],a[10])
                assert canon(rows(out),p)==expected
                for f in rows(cp):
                    expression=sum(c*S.prod(v**k for v,k in zip(vs,e)) for e,c in f.items())
                    assert reference.reduce(expression)[1]==0
                restart.append({'case':name,'producer_threads':producer,'consumer_threads':consumer,
                                'restored_queue_and_round_count_exact':True,'initial_pair_generation_skipped':True,
                                'complete_basis_matches_serial_and_SymPy':True,
                                'matrix_round_data_matches_serial':first_rounds+second_rounds==sr_rounds,
                                'all_checkpoint_rows_in_original_ideal':True})
    assert len(abi)==1
    receipt={'status':'PASS','binary_sha256':build['binary_sha256'],'serial_binary_sha256':hashlib.sha256(serial.read_bytes()).hexdigest(),
             'source_fingerprints':build['source_fingerprints'],'complete_basis_checks':results,'cross_thread_state_checks':restart,
             'native_metadata_ABI_bytes':abi.pop(),'serial_OpenMP_sidecar_ABI_compatible_on_tested_build':True,
             'runtime_environment':{k:ENV[k] for k in ['MALLOC_ARENA_MAX','OMP_WAIT_POLICY','OMP_STACKSIZE']},
             'seconds':time.monotonic()-started,'target_run_performed':False,
             'scope':'Small exact basis and real native-state compatibility checks. No claim of target completion, trace evaluation, or measured target speedup.'}
    (HERE/'resumable_openmp_validation_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'status':'PASS','binary':str(omp),'binary_sha256':build['binary_sha256'],
                      'complete_basis_checks':len(results),'cross_thread_state_checks':len(restart),'native_metadata_ABI_bytes':receipt['native_metadata_ABI_bytes'],
                      'all_matrix_round_sequences_match_serial':all(r['matrix_round_data_matches_serial'] for r in results+restart),
                      'seconds':receipt['seconds']}),flush=True)
if __name__=='__main__':main()
