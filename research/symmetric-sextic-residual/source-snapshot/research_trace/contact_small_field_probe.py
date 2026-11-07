#!/usr/bin/env python3
"""Discovery-only probe for a small number field behind the certified contact.

Failure to find a relation is not a degree lower bound. A numerical relation
would require separate exact algebraic verification before any proof claim.
"""
from pathlib import Path
import json,sys,time
ROOT=Path(__file__).resolve().parent.parent
CONTACT=ROOT/'research_contact'
if not CONTACT.exists():CONTACT=ROOT/'proof_attempt4'
WORKAROUND=ROOT/'research_workaround'
if not WORKAROUND.exists():WORKAROUND=ROOT/'proof_attempt3'
sys.path.insert(0,str(CONTACT))
if (WORKAROUND/'python_deps').exists():
    sys.path.insert(0,str(WORKAROUND/'python_deps'))
import contact_certify as C
import mpmath as mp
from flint import fmpz_mat

def main():
    mp.mp.dps=600;C.mp=mp
    data=json.loads((CONTACT/'contact_exact_ball.json').read_text())
    x=[mp.mpc(C.mpq(C.F(a)),C.mpq(C.F(b))) for a,b in data['center']]
    for k in range(5):
        f,J=C.eval_mp(x,C.ACTIVE)
        print('refine',k,mp.nstr(max(abs(z) for z in f),5),flush=True)
        dx=mp.lu_solve(J,f)
        for i,d in zip(C.ACTIVE,dx):x[i]-=d
    results=[]
    for index in [1,5,6,10,18]:
        z=x[index];done=False
        for degree in [4,8,12,16,20]:
            scale=10**450
            rows=[]
            for k in range(degree+1):
                rows.append([int(j==k) for j in range(degree+1)]+
                            [int(mp.nint(mp.re(z**k)*scale)),
                             int(mp.nint(mp.im(z**k)*scale))])
            start=time.time()
            reduced=fmpz_mat(rows).lll()
            relation=None
            for row in range(degree+1):
                candidate=[int(reduced[row,k]) for k in range(degree+1)]
                if max(map(abs,candidate))>10**16:continue
                if abs(sum(a*z**k for k,a in enumerate(candidate)))<mp.mpf('1e-400'):
                    relation=candidate;break
            item={'index':index,'degree_tested':degree,'coefficient_bound':10**16,
                  'relation_found':relation,'seconds':time.time()-start}
            if relation:
                error=abs(sum(a*z**k for k,a in enumerate(relation)))
                item['complex_residual']=mp.nstr(error,8)
                item['passes_both_real_and_imaginary_numeric_check']=bool(error<mp.mpf('1e-400'))
                done=item['passes_both_real_and_imaginary_numeric_check']
            results.append(item);print(json.dumps(item),flush=True)
            if done:break
    out={'status':'DISCOVERY_ONLY','precision_decimal_digits':600,
         'method':'Simultaneous real-and-imaginary integer lattice reduction at scale10^450',
         'traces_computed':False,'full_certificate_proved':False,
         'scope':'Bounded integer-relation probe, neither a field-degree proof nor a trace calculation.',
         'tests':results}
    (Path(__file__).resolve().parent/'contact_small_field_probe.json').write_text(json.dumps(out,indent=2)+'\n')
if __name__=='__main__':main()
