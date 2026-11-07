#!/usr/bin/env python3
"""Exact F25 norm-map rank checks for a structured symmetric-target seed.

This checks the actual lambda=1, characteristic-five reduction. No Hensel
lifting, characteristic-zero family, source trace, or certificate is asserted.
"""
from pathlib import Path
import itertools
import json
from types import SimpleNamespace
import numpy as np

HERE=Path(__file__).resolve().parent
ZERO=(0,0); ONE=(1,0); H=(0,1)

# Self-contained exact F25 coefficient and rank routines. No downloaded
# witness, saved matrix, or repository verifier is used as an input.
def array_mul(a,b):
    a,b=np.asarray(a),np.asarray(b)
    return np.stack(((a[...,0]*b[...,0]+2*a[...,1]*b[...,1])%5,
                     (a[...,0]*b[...,1]+a[...,1]*b[...,0])%5),axis=-1)
def array_inv(a):
    a=np.asarray(a)
    d=pow(int(a[0]*a[0]-2*a[1]*a[1])%5,-1,5)
    return np.array([a[0]*d%5,-a[1]*d%5],dtype=np.int64)
def array_matmul(a,b):
    return np.stack(((a[...,0]@b[...,0]+2*(a[...,1]@b[...,1]))%5,
                     (a[...,0]@b[...,1]+a[...,1]@b[...,0])%5),axis=-1)
def extension_rank(matrix):
    a=np.array(matrix,dtype=np.int64,copy=True)%5
    rows=list(range(len(a)));rank=0;columns=[]
    for j in range(a.shape[1]):
        choices=np.flatnonzero(np.any(a[rank:,j],axis=-1))
        if not len(choices):continue
        k=rank+int(choices[0])
        a[[rank,k]]=a[[k,rank]];rows[rank],rows[k]=rows[k],rows[rank]
        a[rank]=array_mul(a[rank],array_inv(a[rank,j]))
        if rank+1<len(a):
            a[rank+1:]=(a[rank+1:]-array_mul(a[rank+1:,j,None,:],a[rank]))%5
        columns.append(j);rank+=1
        if rank==len(a):break
    return rank,rows[:rank],columns
def weighted_monomials(degree,parity):
    return sorted(e+(u,) for e in itertools.product(range(degree+1),repeat=4)
                  for u in range(degree//2+1)
                  if sum(e)+2*u==degree and (e[2]+e[3])%2==parity)
blocks=[(2,0),(2,0),(4,0),(4,0),(3,0),(3,1)]
parameter_bases=[weighted_monomials(d,p) for d,p in blocks]
offsets=np.cumsum([0]+[len(b) for b in parameter_bases]).tolist()
plus_basis=weighted_monomials(6,0)
assert offsets[-1]==90 and len(plus_basis)==70
plus_index={e:j for j,e in enumerate(plus_basis)}
term_i=[];term_j=[];term_row=[];term_sign=[]
for b1,b2,sign in [(0,2,1),(1,3,1),(4,4,1),(5,5,-1)]:
    for i,e in enumerate(parameter_bases[b1]):
        for j,m in enumerate(parameter_bases[b2]):
            term_i.append(offsets[b1]+i);term_j.append(offsets[b2]+j)
            term_row.append(plus_index[tuple(x+y for x,y in zip(e,m))]);term_sign.append(sign)
term_i,term_j,term_row,term_sign=[np.array(a,dtype=np.int64)
                                for a in (term_i,term_j,term_row,term_sign)]
def quadratic(v,w):
    out=np.zeros((70,2),dtype=np.int64)
    np.add.at(out,term_row,term_sign[:,None]*array_mul(v[term_i],w[term_j]))
    return out%5
def differential(z):
    out=np.zeros((70,90),dtype=np.int64)
    np.add.at(out,(term_row,term_i),term_sign*z[term_j])
    np.add.at(out,(term_row,term_j),term_sign*z[term_i])
    return out%5
span=SimpleNamespace(mul=array_mul,inv=array_inv,matmul=array_matmul,
    extension_rank=extension_rank,parameter_bases=parameter_bases,offsets=offsets,
    quadratic=quadratic,differential=differential)

def add(x,y):return ((x[0]+y[0])%5,(x[1]+y[1])%5)
def neg(x):return ((-x[0])%5,(-x[1])%5)
def mul(x,y):return ((x[0]*y[0]+2*x[1]*y[1])%5,(x[0]*y[1]+x[1]*y[0])%5)
def const(x):return (x%5,0)
def powf(x,n):
    y=ONE
    for _ in range(n):y=mul(y,x)
    return y
def scale(f,k):return {e:mul(c,k) for e,c in f.items() if mul(c,k)!=ZERO}
def plus(*fs):
    out={}
    for f in fs:
        for e,c in f.items():out[e]=add(out.get(e,ZERO),c)
    return {e:c for e,c in out.items() if c!=ZERO}
def times(f,g):
    out={}
    for e,c in f.items():
        for d,b in g.items():
            m=tuple(i+j for i,j in zip(e,d))
            out[m]=add(out.get(m,ZERO),mul(c,b))
    return {e:c for e,c in out.items() if c!=ZERO}
def singleton(e,c=ONE):return {e:c}

QBASE=[(2,0,0,0),(0,2,0,0),(0,0,2,0),(0,0,1,1),(0,0,0,2)]
ABASE=[(3,0,0,0),(0,3,0,0),(1,0,2,0),(1,0,1,1),
       (1,0,0,2),(0,1,2,0),(0,1,1,1),(0,1,0,2)]
BBASE=[(2,0,1,0),(2,0,0,1),(0,2,1,0),(0,2,0,1),
       (0,0,3,0),(0,0,2,1),(0,0,1,2),(0,0,0,3)]
FREE=sorted(e for e in itertools.product(range(7),repeat=4)
            if sum(e)==6 and (e[2]+e[3])%2==0 and not(e[0] and e[1]))
assert len(FREE)==25

def reduce_ab(f,chi):
    """Normal form modulo ab-chi*cd on this particular chart."""
    out={}
    for (a,b,c,d),v in f.items():
        n=min(a,b)
        e=(a-n,b-n,c+n,d+n)
        out[e]=add(out.get(e,ZERO),mul(v,powf(chi,n)))
    return {e:c for e,c in out.items() if c!=ZERO}

def forms(k,p,q,chi):
    f1={(0,0,0,0,1):ONE,(2,0,0,0,0):k}
    f2={(1,1,0,0,0):ONE,(0,0,1,1,0):neg(chi)}
    g1={(0,0,0,0,2):const(4),(2,0,0,0,1):mul(const(-4),k),
        (4,0,0,0,0):mul(const(4),powf(k,2))}
    factor=mul(const(-2),p)
    g2={(2,2,0,0,0):factor,(1,1,1,1,0):mul(factor,chi),
        (0,0,2,2,0):mul(factor,powf(chi,2))}
    aa={(3,0,0,0,0):p,(0,3,0,0,0):ONE}
    bb={(0,0,3,0,0):q,(0,0,0,3,0):const(2)}
    return [f1,f2,g1,g2,aa,bb]

def check(k,p,q,chi,include_matrices=False):
    assert add(powf(p,2),mul(const(4),powf(k,3)))==const(2)
    assert powf(q,2)==const(3)
    assert mul(p,powf(chi,3))==mul(const(2),q)
    fs=forms(k,p,q,chi)
    f1,f2,g1,g2,aa,bb=fs
    phi=plus(times(f1,g1),times(f2,g2),times(aa,aa),scale(times(bb,bb),const(-1)))
    expected={(6,0,0,0,0):const(2),(0,6,0,0,0):ONE,
              (0,0,6,0,0):const(2),(0,0,0,6,0):ONE,
              (0,0,0,0,3):const(4)}
    assert phi==expected
    z=np.zeros((90,2),dtype=np.int64)
    for i,f in enumerate(fs):
        for j,e in enumerate(span.parameter_bases[i]):z[span.offsets[i]+j]=f.get(e,ZERO)
    D=np.stack([span.differential(z[:,0]),span.differential(z[:,1])],axis=-1)
    assert D.shape==(70,90,2)
    full_rank=span.extension_rank(D)[0]

    # The intrinsic residual is rem_Q2(G(-Q1)-A^2+B^2).
    # At the seed its un-reduced residual is Q2*g2.
    # Its derivatives are -G_u(-Q1)*delta Q1, -g2*delta Q2,
    # -2*A*delta A, and +2*B*delta B.
    aa4={e[:4]:v for e,v in aa.items()}
    bb4={e[:4]:v for e,v in bb.items()}
    gg4={e[:4]:v for e,v in g2.items()}
    gu=singleton((4,0,0,0),mul(const(-12),powf(k,2)))
    columns=[]
    for m in QBASE:columns.append(reduce_ab(times(gu,singleton(m)),chi))
    for m in QBASE:columns.append(reduce_ab(scale(times(gg4,singleton(m)),const(-1)),chi))
    for m in ABASE:columns.append(reduce_ab(scale(times(aa4,singleton(m)),const(-2)),chi))
    for m in BBASE:columns.append(reduce_ab(scale(times(bb4,singleton(m)),const(2)),chi))
    J=np.array([[f.get(e,ZERO) for f in columns] for e in FREE],dtype=np.int64)
    assert J.shape==(25,26,2)
    intrinsic_rank,rows,cols=span.extension_rank(J)
    assert full_rank==45+intrinsic_rank
    result={"k":k,"p":p,"q":q,"chi":chi,"decomposition_checked":True,
            "norm_map_shape":[70,90],"norm_map_rank":full_rank,
            "intrinsic_shape":[25,26],"intrinsic_rank":intrinsic_rank,
            "intrinsic_row_pivots":rows,"intrinsic_column_pivots":cols}
    if include_matrices:
        result.update({"forms":[{','.join(map(str,e)):v for e,v in f.items()} for f in fs],
                       "intrinsic_matrix":J.tolist(),"norm_map_matrix":D.tolist()})
    return result

def main():
    seed=check(const(3),const(2),mul(const(2),H),H,True)
    (HERE/'contact_lift_seed.json').write_text(json.dumps(seed,indent=2)+'\n')
    print(json.dumps({k:v for k,v in seed.items() if k not in ['forms','intrinsic_matrix','norm_map_matrix']},indent=2),flush=True)
    elements=[(a,b) for a in range(5) for b in range(5)]
    family=[]
    for k in elements:
        for p in elements:
            if p==ZERO or add(powf(p,2),mul(const(4),powf(k,3)))!=const(2):continue
            for q in elements:
                if powf(q,2)!=const(3):continue
                for chi in elements:
                    if mul(p,powf(chi,3))==mul(const(2),q):family.append(check(k,p,q,chi))
    rank_counts={}
    for result in family:
        key=str(result['intrinsic_rank'])
        rank_counts[key]=rank_counts.get(key,0)+1
    receipt={"field":"F5[h]/(h^2-2)","coefficient_encoding":"[constant,h coefficient]",
             "family":"f1=u+k*a^2; f2=ab-chi*cd; A=p*a^3+b^3; B=q*c^3+2*d^3",
             "constraints":["p^2+4*k^3=2","q^2=3","p*chi^3=2*q","p!=0"],
             "tested_points":len(family),"intrinsic_rank_counts":rank_counts,
             "points":family,
             "scope":"Exact finite-field checks on this structured family only. No characteristic-zero contact, Hensel lift, trace, or certificate inferred."}
    (HERE/'contact_lift_seed_family.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k!='points'},indent=2),flush=True)

if __name__=='__main__':main()
