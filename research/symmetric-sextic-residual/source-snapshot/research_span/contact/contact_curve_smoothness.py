#!/usr/bin/env python3
"""Certified Jacobian criterion for the actual norm-contact curve.

On the previously certified contact ball, prove a Macaulay minor for
(Q2,h, all two-by-two minors of d(Q2,h)) invertible. This rules out every
nonzero common zero and proves the projective (2,3) curve smooth. No trace
or final certificate is claimed. Selection is numerical; verification uses
outward-rounded Arb enclosures, followed by an exact rational integer check.
"""
from pathlib import Path
from itertools import product,combinations
from fractions import Fraction
import json,hashlib,sys,time

HERE=Path(__file__).resolve().parent
PREVIOUS=next(p for p in [HERE.parents[1]/'proof_attempt4',
                         HERE.parents[1]/'research_contact'] if p.is_dir())
sys.path.insert(0,str(PREVIOUS))
import contact_certify as C
from flint import acb,arb,acb_mat,fmpq,ctx
import numpy as np
import scipy.linalg as la

def mons(d):return sorted(e for e in product(range(d+1),repeat=4) if sum(e)==d)
def mul(f,g):
    out={}
    for e,c in f.items():
        for m,v in g.items():
            k=tuple(x+y for x,y in zip(e,m));out[k]=out.get(k,0)+c*v
    return out
def sub(f,g):
    out=f.copy()
    for m,c in g.items():out[m]=out.get(m,0)-c
    return out
def derivative(f,i):
    out={}
    for e,c in f.items():
        if e[i]:
            m=list(e);m[i]-=1;out[tuple(m)]=e[i]*c
    return out
def enc(z):
    return [[int(y) for y in z.mid().man_exp()],
            [int(y) for y in z.rad().man_exp()]]
def enc_c(z):return [enc(z.real),enc(z.imag)]
def l1(z):return (z.real.abs_upper()+z.imag.abs_upper()).upper()
def main():
    ctx.dps=100;ctx.threads=1;start=time.time()
    ball=json.loads((PREVIOUS/'contact_exact_ball.json').read_text())
    rad=fmpq(ball['radius'])
    x=[acb(arb(fmpq(z[0]),rad),arb(fmpq(z[1]),rad)) for z in ball['center'][:45]]
    q=dict(zip(C.QBASE,x[5:10]));q[C.AB]=acb(1)
    h=dict(zip(C.ABASE+C.BBASE,x[10:26]))
    minors=[sub(mul(derivative(q,i),derivative(h,j)),
                mul(derivative(q,j),derivative(h,i))) for i,j in combinations(range(4),2)]
    forms=[q,h]+minors;degrees=[2]+[3]*7
    attempts=[]
    for degree in [6,7,8]:
        rows=mons(degree);idx={m:i for i,m in enumerate(rows)};cols=[]
        for f,d in zip(forms,degrees):
            for m in mons(degree-d):
                col={idx[tuple(a+b for a,b in zip(e,m))]:c for e,c in f.items()}
                cols.append(col)
        M=np.zeros((len(rows),len(cols)),dtype=complex)
        for j,col in enumerate(cols):
            for i,z in col.items():M[i,j]=complex(float(z.real.mid()),float(z.imag.mid()))
        _,_,piv=la.qr(M,mode='economic',pivoting=True)
        selected=list(map(int,piv[:len(rows)]))
        smallest=float(la.svdvals(M[:,selected])[-1])
        attempts.append({'degree':degree,'shape':[len(rows),len(cols)],'numerical_smallest_singular_value':smallest})
        print(attempts[-1],flush=True)
        if smallest<1e-12:continue
        exact=acb_mat([[cols[j].get(i,0) for j in selected] for i in range(len(rows))])
        B=exact.inv().mid()
        error=acb_mat([[int(i==j) for j in range(len(rows))] for i in range(len(rows))])-B*exact
        defect=max(sum((l1(error[i,j]) for j in range(len(rows))),arb(0)).upper()
                   for i in range(len(rows)))
        assert defect<1
        witness={'status':'PASS','method':'Arb enclosure of I-BM throughout original rational contact ball',
             'source_ball_sha256':hashlib.sha256((PREVIOUS/'contact_exact_ball.json').read_bytes()).hexdigest(),
             'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
             'degree':degree,'row_count':len(rows),'column_count':len(cols),
             'selected_columns':selected,'inverse_midpoint':[[enc_c(B[i,j]) for j in range(len(rows))] for i in range(len(rows))],
             'inverse_defect':enc(defect),'prior_attempts':attempts,
             'claim':'The forms Q2,h and all six 2x2 Jacobian minors have no common nonzero zero. The projective complete intersection Q2=h=0 is smooth.',
             'Lean_proof':False,'full_certificate_proved':False,'seconds':time.time()-start}
        (HERE/'contact_curve_smoothness.json').write_text(json.dumps(witness,separators=(',',':'))+'\n')
        print('PASS degree',degree,'defect',defect.str(12),flush=True)
        return
    raise RuntimeError('No complete smoothness minor found within degree8')
if __name__=='__main__':main()
