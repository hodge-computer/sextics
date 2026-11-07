#!/usr/bin/env python3
"""Exact rational replay of the actual curve's degree-six smoothness minor.

This checker does not import Arb or a numerical linear algebra package. It
reconstructs all coefficient polynomials from Q2 and h, and verifies the
provided dyadic preconditioner by exact rational matrix multiplication and
a global coefficient Lipschitz bound on the original contact ball.
"""
from pathlib import Path
from fractions import Fraction
from itertools import product,combinations
import json,hashlib,time
from flint import fmpq as Q
import check_contact_jet_witness as V

HERE=Path(__file__).resolve().parent
PREVIOUS=V.PREVIOUS
C=V.C

def mons(d):return sorted(e for e in product(range(d+1),repeat=4) if sum(e)==d)

def term(f,e,c,m=()):
    p=f.setdefault(e,{});m=tuple(sorted(m));p[m]=p.get(m,Fraction())+Fraction(c)

def derivative(f,i):
    out={}
    for e,p in f.items():
        if e[i]:
            m=list(e);m[i]-=1
            for v,c in p.items():term(out,tuple(m),e[i]*c,v)
    return out

def multiply(f,g):
    out={}
    for e,p in f.items():
        for n,q in g.items():
            m=tuple(x+y for x,y in zip(e,n))
            for a,c in p.items():
                for b,d in q.items():term(out,m,c*d,a+b)
    return out

def subtract(f,g):
    out={}
    for e,p in f.items():
        for m,c in p.items():term(out,e,c,m)
    for e,p in g.items():
        for m,c in p.items():term(out,e,-c,m)
    return {e:{m:c for m,c in p.items() if c} for e,p in out.items() if any(p.values())}

def main():
    start=time.time()
    file=HERE/'contact_curve_smoothness.json';w=json.loads(file.read_text())
    ballfile=PREVIOUS/'contact_exact_ball.json';ball=json.loads(ballfile.read_text())
    assert w['source_ball_sha256']==hashlib.sha256(ballfile.read_bytes()).hexdigest()
    q={};h={};term(q,C.AB,1)
    for i,e in enumerate(C.QBASE):term(q,e,1,(5+i,))
    for i,e in enumerate(C.ABASE):term(h,e,1,(10+i,))
    for i,e in enumerate(C.BBASE):term(h,e,1,(18+i,))
    minors=[subtract(multiply(derivative(q,i),derivative(h,j)),
                     multiply(derivative(q,j),derivative(h,i))) for i,j in combinations(range(4),2)]
    forms=[q,h]+minors;degrees=[2]+[3]*7
    degree=w['degree'];rows=mons(degree);index={e:i for i,e in enumerate(rows)};cols=[]
    for f,d in zip(forms,degrees):
        for m in mons(degree-d):
            cols.append({index[tuple(a+b for a,b in zip(e,m))]:p for e,p in f.items()})
    assert len(rows)==w['row_count']==84 and len(cols)==w['column_count']==175
    selected=w['selected_columns'];assert len(set(selected))==84
    assert all(0<=j<len(cols) for j in selected)
    x=[(Q(a),Q(b)) for a,b in ball['center'][:45]]
    cache={(): (Q(1),Q(0))}
    def mon(m):
        if m not in cache:cache[m]=V.cmul(mon(m[:-1]),x[m[-1]])
        return cache[m]
    def value(p):
        z=(Q(0),Q(0))
        for m,c in p.items():
            a,b=mon(m);c=V.rational(c);z=V.cadd(z,(c*a,c*b))
        return z
    M=V.complex_matrix([[value(cols[j].get(i,{})) for j in selected] for i in range(84)])
    # The stored approximate inverse has exact dyadic midpoints; its stored
    # zero-radius encodings must agree with that declaration.
    bd=[]
    for row in w['inverse_midpoint']:
        br=[]
        for z in row:
            assert z[0][1][0]==0 and z[1][1][0]==0
            br.append((V.dyad(z[0][0]),V.dyad(z[1][0])))
        bd.append(br)
    B=V.complex_matrix(bd)
    defect=V.matrix_defect(B,M);nb=V.matrix_norm(B);radius=Q(ball['radius'])
    coord=max(V.cabs(z) for z in x)+radius
    bound=int(coord.p//coord.q)+1
    lips=[]
    for i in range(84):
        lips.append(sum((abs(V.rational(c))*len(m)*bound**max(0,len(m)-1)
                         for j in selected for m,c in cols[j].get(i,{}).items()),Q(0)))
    lip=max(lips);total=defect+nb*lip*radius
    assert total<1
    receipt={'status':'PASS','verification_arithmetic':'Exact rational arithmetic; no Arb or floating point.',
        'source_ball_sha256':w['source_ball_sha256'],'witness_sha256':hashlib.sha256(file.read_bytes()).hexdigest(),
        'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'rational_helpers_sha256':hashlib.sha256((HERE/'check_contact_jet_witness.py').read_bytes()).hexdigest(),
        'degree':degree,'Macaulay_shape':[84,175],'selected_minor_size':84,
        'exact_center_inverse_defect':str(defect),'exact_inverse_norm':str(nb),
        'exact_matrix_Lipschitz_bound':str(lip),'exact_root_ball_radius':str(radius),
        'ball_inverse_defect_binary_exponent':V.exponent_bound(total),
        'claim':'All degree6 monomials are in (Q2,h,2x2 Jacobian minors) at every contact parameter in the ball. Hence Q2=h=0 is a smooth projective curve wherever the already certified complete-intersection hypotheses hold.',
        'seconds':time.time()-start,'Lean_proof':False,'full_certificate_proved':False}
    (HERE/'contact_curve_smoothness_rational_replay.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print('EXACT RATIONAL CURVE SMOOTHNESS PASS; defect <= 2^',V.exponent_bound(total),
          '; seconds',receipt['seconds'],flush=True)

if __name__=='__main__':main()
