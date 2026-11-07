#!/usr/bin/env python3
"""Exact cache-choice, complete-basis, scan-count, and native-state checks."""
from pathlib import Path
import hashlib,json,os,re,resource,subprocess,time
import sympy as S
from sympy.polys.orderings import grevlex
from packed_f4 import write,rows,header
from check_resumable import canon
HERE=Path(__file__).resolve().parent
ENV={**os.environ,'MALLOC_ARENA_MAX':'2','OMP_WAIT_POLICY':'PASSIVE','OMP_STACKSIZE':'4M','OPENBLAS_NUM_THREADS':'1'}
ROUND=re.compile(r'^\s*(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s+x\s+(\d+)\s+[\d.]+%\s+(\d+) new\s+(\d+) zero',re.M)
def limit():resource.setrlimit(resource.RLIMIT_AS,(1024**3,)*2)
def invoke(exe,inp,out,cache=None,state=None,checkpoint=None,budget=None):
    command=[str(exe),'--input',str(inp),'--output',str(out),'--threads','4','--pairs','1','--info','2']
    if cache is not None:command+=['--reducer-cache',str(cache)]
    if state:command+=['--resume-state',str(state)]
    if checkpoint:command+=['--checkpoint',str(checkpoint)]
    if budget:command+=['--round-budget',str(budget)]
    run=subprocess.run(command,env=ENV,preexec_fn=limit,capture_output=True,text=True,timeout=30)
    out.with_suffix('.log').write_text(run.stderr+run.stdout)
    assert run.returncode in (0,75),(run.returncode,run.stderr,run.stdout)
    profiles=[dict(re.findall(r'(\w+)=([^ ]+)',line)) for line in run.stderr.splitlines() if line.startswith('[reducer]')]
    return run,[tuple(map(int,t)) for t in ROUND.findall(run.stderr)],profiles[-1] if profiles else {}
def main():
    start=time.monotonic();build=json.loads((HERE/'reducer_cache_build_receipt.json').read_text());audit=json.loads((HERE/'reducer_cache_audit_build_receipt.json').read_text())
    for n in ['reducer_cache.h','msolve_reducer_cache.patch','resumable_reducer_cache_driver.c']:
        assert build['source_fingerprints'][n]==audit['source_fingerprints'][n]==hashlib.sha256((HERE/n).read_bytes()).hexdigest()
    exe=Path(build['binary']);aud=Path(audit['binary']);baseline=Path(json.loads((HERE/'resumable_openmp_build_receipt.json').read_text())['binary'])
    folder=Path(build['build_directory'])/'checks';folder.mkdir(exist_ok=True)
    x,y,z,w=S.symbols('x y z w')
    cases=[('quadratic',(x,y),[x*x+y*y-1,x-y],37,0),('nonreduced',(x,y),[x*x,x*y,y*y],101,0),
           ('unit',(x,y),[x*x,y-x,x*y-1,x*y],37,0),('positive_dimension',(x,y,z),[x*y-z*z,x*x-y*z],101,0),
           ('mixed16',(x,y,z),[7*x*x+5*y*z+1,3*y*y+4*x*z+2,6*z*z+2*x*y+3],1009,0),
           ('mixed32',(x,y,z),[x*x+y*z+1,y*y+x*z+2,z*z+x*y+3],65537,0),
           ('degree_fall',(x,y,z),[x*x*y+x*z+y,y*y*z+y*x+z,z*z*x+z*y+x],1073741827,0),
           ('cyclic4',(x,y,z,w),[x+y+z+w,x*y+y*z+z*w+w*x,x*y*z+y*z*w+z*w*x+w*x*y,x*y*z*w-1],101,0),
           ('block1',(x,y,z),[7*x*x+5*y*z+1,3*y*y+4*x*z+2,6*z*z+2*x*y+3],37,1),
           ('block2',(x,y,z),[7*x*x+5*y*z+1,3*y*y+4*x*z+2,6*z*z+2*x*y+3],65537,2)]
    results=[];restarts=[];totals={'queries':0,'positive_hits':0,'negative_hits':0,'scanned_entries':0,'avoided_entries':0}
    for name,vs,polys,p,elim in cases:
        inputs=[{e:int(c)%p for e,c in S.Poly(f,*vs,modulus=p).terms()} for f in polys]
        order=grevlex if not elim else lambda m,e=elim:(grevlex(m[:e]),grevlex(m[e:]))
        oracle=S.groebner(polys,*vs,modulus=p,order=order);expected=canon([dict(f.terms()) for f in oracle.polys],p)
        inp=folder/(name+'.hcf');write(inp,[str(v) for v in vs],p,inputs,elim=elim)
        br,base_rounds,_=invoke(baseline,inp,folder/(name+'_base.hcf'))
        assert br.returncode==0 and canon(rows(folder/(name+'_base.hcf')),p)==expected
        summaries={}
        for label,program,enabled in [('on',exe,1),('off',exe,0),('audit',aud,1)]:
            out=folder/f'{name}_{label}.hcf';run,rounds,profile=invoke(program,inp,out,enabled)
            assert run.returncode==0 and canon(rows(out),p)==expected
            assert rounds==base_rounds,(name,label,'round sequence changed')
            summaries[label]=profile
            if label=='audit' and profile:assert int(profile['audited'])==int(profile['total_queries'])
        if summaries['on']:
            on,off=summaries['on'],summaries['off']
            assert int(off['total_scanned_entries'])==int(on['total_scanned_entries'])+int(on['total_avoided_entries'])
            for k in totals:totals[k]+=int(on['total_'+k])
        results.append({'case':name,'prime':p,'elimination_block':elim,'cache_on_off_audit_bases_and_rounds_match_frozen_and_SymPy':True,
                        'every_audit_lookup_equals_original_first_divisor':True,'scan_reduction_exactly_accounted_for':True,'profile':summaries['on']})
        if name in ('cyclic4','mixed16','block1','block2'):
            for direction in ('baseline_to_cache','cache_to_baseline','cache_to_cache'):
                producer=baseline if direction=='baseline_to_cache' else exe;consumer=baseline if direction=='cache_to_baseline' else exe
                cp=folder/f'{name}_{direction}_partial.hcf';unused=folder/f'{name}_{direction}_unused.hcf'
                first,first_rounds,_=invoke(producer,inp,unused,None if producer==baseline else 1,checkpoint=cp,budget=2)
                assert first.returncode==75
                out=folder/f'{name}_{direction}_complete.hcf'
                second,second_rounds,_=invoke(consumer,cp,out,None if consumer==baseline else 1,state=cp.with_suffix('.hcf.state'))
                assert second.returncode==0 and 'initial pair generation skipped' in second.stderr
                assert canon(rows(out),p)==expected and first_rounds+second_rounds==base_rounds
                for f in rows(cp):assert oracle.reduce(sum(c*S.prod(v**k for v,k in zip(vs,e)) for e,c in f.items()))[1]==0
                restarts.append({'case':name,'direction':direction,'basis_and_rounds_match':True,'saved_rows_in_original_ideal':True})
    assert totals['positive_hits']>0 and totals['negative_hits']>0 and totals['avoided_entries']>0
    # Rebuild the tiny isolated semantic fixture with the exact current header.
    fixture=Path(build['build_directory'])/'cache_invariants'
    command=['gcc','-O2','-I'+str(HERE/'vendor/msolve-0.11.0/src/neogb'),'-I'+str(HERE/'vendor/gmp-6.3.0'),'-I'+str(HERE),str(HERE/'reducer_cache_invariants.c'),'-o',str(fixture)]
    subprocess.run(command,capture_output=True,check=True)
    invariant=json.loads(subprocess.run([str(fixture)],capture_output=True,text=True,check=True).stdout)
    receipt={'status':'PASS','binary_sha256':build['binary_sha256'],'audit_binary_sha256':audit['binary_sha256'],'source_fingerprints':build['source_fingerprints'],
             'complete_systems':results,'native_state_tests':restarts,'semantic_fixture':invariant,'aggregate_cache_counters':totals,
             'all_first_divisor_choices_shadow_checked_in_audit_build':True,'timers':'CLOCK_MONOTONIC, separately lookup/preparation/materialization',
             'seconds':time.monotonic()-start,'target_run_performed':False,'scope':'Exact small-system implementation checks; performance relevance awaits a real target subphase profile.'}
    (HERE/'reducer_cache_validation_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'status':'PASS','complete_systems':len(results),'native_state_tests':len(restarts),'semantic_fixture':invariant,
                      'aggregate_cache_counters':totals,'binary':str(exe),'binary_sha256':build['binary_sha256'],'seconds':receipt['seconds']}),flush=True)
if __name__=='__main__':main()
