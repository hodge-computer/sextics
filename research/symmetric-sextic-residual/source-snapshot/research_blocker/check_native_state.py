#!/usr/bin/env python3
"""Check exact continuation of the pinned F4 state across process restarts."""
from pathlib import Path
import hashlib,json,re,resource,struct,subprocess,time
import sympy as S
from sympy.polys.orderings import grevlex
from packed_f4 import write,rows,header
from check_resumable import canon
HERE=Path(__file__).resolve().parent
ROUND=re.compile(r'^\s*(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s+x\s+(\d+)\s+[\d.]+%\s+(\d+) new\s+(\d+) zero',re.M)

def limits():resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
def call(binary,inp,out,checkpoint=None,budget=None,state=None):
    command=[str(binary),'--input',str(inp),'--output',str(out),'--pairs','1','--info','2']
    if checkpoint:command+=['--checkpoint',str(checkpoint)]
    if budget:command+=['--round-budget',str(budget)]
    if state:command+=['--resume-state',str(state)]
    run=subprocess.run(command,capture_output=True,text=True,timeout=30,preexec_fn=limits)
    out.with_suffix('.log').write_text(run.stderr+run.stdout)
    return run,[tuple(map(int,m)) for m in ROUND.findall(run.stderr)]

def main():
    start=time.monotonic();build=json.loads((HERE/'resumable_state_build_receipt.json').read_text());binary=Path(build['binary'])
    folder=Path(build['build_directory'])/'state_checks';folder.mkdir(exist_ok=True)
    x,y,z,w=S.symbols('x y z w')
    cases=[('cyclic4',101,(x,y,z,w),[x+y+z+w,x*y+y*z+z*w+w*x,x*y*z+y*z*w+z*w*x+w*x*y,x*y*z*w-1],0),
           ('mixed16',1009,(x,y,z),[7*x*x+5*y*z+1,3*y*y+4*x*z+2,6*z*z+2*x*y+3],0),
           ('block1',37,(x,y,z),[7*x*x+5*y*z+1,3*y*y+4*x*z+2,6*z*z+2*x*y+3],1),
           ('block2',65537,(x,y,z),[7*x*x+5*y*z+1,3*y*y+4*x*z+2,6*z*z+2*x*y+3],2)]
    results=[]
    for name,p,variables,polys,elim in cases:
        inputs=[{e:int(c)%p for e,c in S.Poly(f,*variables,modulus=p).terms()} for f in polys]
        order=grevlex if not elim else lambda m,e=elim:(grevlex(m[:e]),grevlex(m[e:]))
        reference=S.groebner(polys,*variables,modulus=p,order=order)
        expected=canon([dict(f.terms()) for f in reference.polys],p)
        inp=folder/f'{name}_input.hcf';write(inp,[str(v) for v in variables],p,inputs,elim=elim)
        direct=folder/f'{name}_direct.hcf';run,direct_rounds=call(binary,inp,direct)
        assert run.returncode==0,(name,run.stderr);assert canon(rows(direct),p)==expected
        previous=inp;state=None;combined=[];checkpoints=0
        for step in range(30):
            out=folder/f'{name}_resume_{step}.hcf';partial=folder/f'{name}_partial_{step}.hcf'
            run,rounds=call(binary,previous,out,partial,2,state);combined+=rounds
            assert run.returncode in (0,75),(name,step,run.returncode,run.stderr)
            if state:
                assert 'initial pair generation skipped' in run.stderr
            if run.returncode==0:
                assert canon(rows(out),p)==expected
                assert combined==direct_rounds,(name,combined,direct_rounds)
                assert hashlib.sha256(out.read_bytes()).hexdigest()==hashlib.sha256(direct.read_bytes()).hexdigest()
                break
            checkpoints+=1;meta=header(partial);assert not meta['complete']
            partial_rows=list(rows(partial));assert canon(partial_rows[:len(inputs)],p)==canon(inputs,p)
            for f in partial_rows:
                expression=sum(c*S.prod(v**k for v,k in zip(variables,e)) for e,c in f.items())
                assert reference.reduce(expression)[1]==0
            raw=(partial.with_suffix('.hcf.state')).read_bytes()
            assert raw[:8]==b'HCF4ST01'
            a=struct.unpack_from('<12I',raw,8);b=struct.unpack_from('<3Q',raw,56)
            assert b[1]==len(combined) and a[10]>0
            state=partial.with_suffix('.hcf.state');previous=partial
        else:raise AssertionError('small native restart did not finish')
        results.append({'case':name,'prime':p,'elimination_block':elim,'checkpoints':checkpoints,
                        'matrix_rounds':len(direct_rounds),'every_degree_selection_paircount_matrix_shape_new_and_zero_count_matches_uninterrupted':True,
                        'complete_basis_matches_SymPy':True,'complete_packed_file_byte_identical_to_uninterrupted':True,
                        'every_checkpoint_row_reduces_to_zero_in_original_ideal':True,'original_prefix_preserved':True})
    assert all(r['checkpoints'] for r in results)
    # A valid packed file whose original-prefix coefficient was accidentally
    # changed must fail before any pending pair is consumed.
    first=folder/'cyclic4_partial_0.hcf';bad=folder/'mismatched_basis.hcf';raw=bytearray(first.read_bytes());meta=header(first)
    offset=64+2*meta['variables']*meta['monomials']+8+4
    c,=struct.unpack_from('<I',raw,offset);struct.pack_into('<I',raw,offset,(c%100)+1);bad.write_bytes(raw)
    run,_=call(binary,bad,folder/'bad_out.hcf',state=first.with_suffix('.hcf.state'))
    assert run.returncode==2 and 'fingerprint' in run.stderr
    receipt={'status':'PASS','binary_sha256':build['binary_sha256'],'source_sha256':build['source_fingerprints']['resumable_state_driver.c'],
             'cases':results,'mismatched_packed_basis_rejected_before_native_resume':True,
             'pending_pairs_restored_without_initial_update':True,'pair_LCMs_checked_against_generator_leading_monomials':True,
             'divisor_masks_and_leading_masks_recomputed':True,'signature_and_tracer_paths_disabled':True,
             'state_format_scope':'Pinned native md_t ABI; FNV-1a accidental-mismatch check, not a cryptographic certificate. Distribution files receive SHA256 receipts.',
             'seconds':time.monotonic()-start,'scope':'Exact small-system continuation checks. No target quotient or trace has been obtained.'}
    (HERE/'resumable_native_state_audit.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
