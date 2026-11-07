#!/usr/bin/env python3
"""The two quadratic obstructions on the 3D kernel of the F25 seed.

This computes the tangent cone only. It does not assert convergence, a lifted
contact, a higher-order formal branch, or a source trace.
"""
import json
from pathlib import Path
import itertools
import numpy as np
import norm_contact_exact_seed as nc

HERE=Path(__file__).resolve().parent
data=nc.check(nc.const(3),nc.const(2),nc.mul(nc.const(2),nc.H),nc.H,True)
J=np.array(data['intrinsic_matrix'],dtype=np.int64)
mm=nc.span.matmul; fm=nc.span.mul; fi=nc.span.inv

def rref_with_transform(A):
    original=A.copy()
    A=A.copy()
    n,m,_=A.shape
    T=np.zeros((n,n,2),dtype=np.int64)
    T[:,:,0]=np.eye(n,dtype=np.int64)
    piv=[];r=0
    for c in range(m):
        choices=np.flatnonzero(np.any(A[r:,c],axis=-1))
        if not len(choices):continue
        k=r+int(choices[0])
        A[[r,k]]=A[[k,r]];T[[r,k]]=T[[k,r]]
        inv=fi(A[r,c]);A[r]=fm(A[r],inv);T[r]=fm(T[r],inv)
        factor=A[:,c].copy();factor[r]=0
        A=(A-fm(factor[:,None,:],A[r][None,:,:]))%5
        T=(T-fm(factor[:,None,:],T[r][None,:,:]))%5
        piv.append(c);r+=1
        if r==n:break
    free=[c for c in range(m) if c not in piv]
    K=np.zeros((m,len(free),2),dtype=np.int64)
    for j,c in enumerate(free):
        K[c,j]=[1,0]
        for i,p in enumerate(piv):K[p,j]=-A[i,c]%5
    assert not np.any(mm(original,K))
    assert not np.any(mm(T[r:],original))
    return A,T,K,piv,free

rr,T,K,piv,free=rref_with_transform(J)
L=T[len(piv):]
assert K.shape==(26,3,2) and L.shape==(2,25,2)
k=nc.const(3);p=nc.const(2);q=nc.mul(nc.const(2),nc.H);chi=nc.H
fs=nc.forms(k,p,q,chi)
f1,f2,g1,g2,A,B=fs
Q1={(2,0,0,0):k}
A={e[:4]:v for e,v in A.items()}
B={e[:4]:v for e,v in B.items()}
g2={e[:4]:v for e,v in g2.items()}
Q2={(1,1,0,0):nc.ONE,(0,0,1,1):nc.neg(chi)}

def divide_ab(f):
    quotient={};remainder={}
    for (a,b,c,d),v in f.items():
        n=min(a,b)
        for i in range(n):
            e=(a-1-i,b-1-i,c+i,d+i)
            quotient[e]=nc.add(quotient.get(e,nc.ZERO),nc.mul(v,nc.powf(chi,i)))
        e=(a-n,b-n,c+n,d+n)
        remainder[e]=nc.add(remainder.get(e,nc.ZERO),nc.mul(v,nc.powf(chi,n)))
    quotient={e:c for e,c in quotient.items() if c!=nc.ZERO}
    remainder={e:c for e,c in remainder.items() if c!=nc.ZERO}
    assert nc.plus(nc.times(Q2,quotient),remainder)==f
    return quotient,remainder

def poly(coords,basis):
    return {e:tuple(int(z) for z in c) for e,c in zip(basis,coords) if np.any(c)}

def second_order(direction):
    dQ1=poly(direction[:5],nc.QBASE)
    dQ2=poly(direction[5:10],nc.QBASE)
    dA=poly(direction[10:18],nc.ABASE)
    dB=poly(direction[18:],nc.BBASE)
    R1=nc.plus(nc.scale(nc.times(nc.times(Q1,Q1),dQ1),nc.const(-12)),
               nc.scale(nc.times(A,dA),nc.const(-2)),nc.scale(nc.times(B,dB),nc.const(2)))
    dg,rem=divide_ab(nc.plus(R1,nc.scale(nc.times(dQ2,g2),nc.const(-1))))
    assert not rem
    R2=nc.plus(nc.scale(nc.times(Q1,nc.times(dQ1,dQ1)),nc.const(-12)),
               nc.scale(nc.times(dA,dA),nc.const(-1)),nc.times(dB,dB))
    _,F2=divide_ab(nc.plus(R2,nc.scale(nc.times(dQ2,dg),nc.const(-1))))
    v=np.array([F2.get(e,nc.ZERO) for e in nc.FREE],dtype=np.int64)
    return mm(L,v[:,None,:])[:,0,:]

def lift_full_tangent(direction):
    dQ1=poly(direction[:5],nc.QBASE)
    dQ2=poly(direction[5:10],nc.QBASE)
    dA=poly(direction[10:18],nc.ABASE)
    dB=poly(direction[18:],nc.BBASE)
    R1=nc.plus(nc.scale(nc.times(nc.times(Q1,Q1),dQ1),nc.const(-12)),
               nc.scale(nc.times(A,dA),nc.const(-2)),nc.scale(nc.times(B,dB),nc.const(2)))
    dg,rem=divide_ab(nc.plus(R1,nc.scale(nc.times(dQ2,g2),nc.const(-1))))
    assert not rem
    lift=lambda f:{e+(0,):c for e,c in f.items()}
    dQ15=lift(dQ1)
    u={(0,0,0,0,1):nc.ONE}
    dgg1=nc.plus(nc.scale(nc.times(u,dQ15),nc.const(-4)),
                 nc.scale(nc.times(lift(Q1),dQ15),nc.const(8)))
    forms=[dQ15,lift(dQ2),dgg1,lift(dg),lift(dA),lift(dB)]
    v=np.zeros((90,2),dtype=np.int64)
    for i,f in enumerate(forms):
        for j,e in enumerate(nc.span.parameter_bases[i]):v[nc.span.offsets[i]+j]=f.get(e,nc.ZERO)
    return v

exponents=[(2,0,0),(1,1,0),(1,0,1),(0,2,0),(0,1,1),(0,0,2)]
squares=[second_order(K[:,i]) for i in range(3)]
coefficients=np.stack([squares[0],(second_order((K[:,0]+K[:,1])%5)-squares[0]-squares[1])%5,
    (second_order((K[:,0]+K[:,2])%5)-squares[0]-squares[2])%5,squares[1],
    (second_order((K[:,1]+K[:,2])%5)-squares[1]-squares[2])%5,squares[2]],axis=1)

# Independent check using the original quadratic 90-to-70 norm map.
full_J=np.array(data['norm_map_matrix'],dtype=np.int64)
_,full_T,_,full_piv,_=rref_with_transform(full_J)
full_L=full_T[len(full_piv):]
for direction in [K[:,i] for i in range(3)]+[(K[:,i]+K[:,j])%5 for i,j in [(0,1),(0,2),(1,2)]]:
    full_direction=lift_full_tangent(direction)
    assert not np.any(mm(full_J,full_direction[:,None,:]))
    full_quadratic=nc.span.quadratic(full_direction,full_direction)
    assert not np.any(mm(full_L,full_quadratic[:,None,:]))

# G_actual=G_Fermat+5*B at lambda=1. Work modulo five after evaluating u=-3a².
u2={(2,0,0,0):nc.const(2)}
a2={(2,0,0,0):nc.ONE};c2={(0,0,2,0):nc.ONE}
ab={(1,1,0,0):nc.ONE};cd={(0,0,1,1):nc.ONE}
QX=nc.plus(a2,nc.scale(ab,nc.const(2)),nc.scale(u2,nc.const(-1)))
QY=nc.plus(c2,nc.scale(cd,nc.const(2)),nc.scale(u2,nc.const(-1)))
Bperturb=nc.plus(nc.times(u2,nc.plus(nc.times(a2,a2),nc.times(c2,c2))),
                 nc.times(nc.times(u2,u2),nc.plus(a2,c2)),
                 nc.scale(nc.times(nc.times(QX,QX),QY),nc.const(3)),
                 nc.times(QX,nc.times(QY,QY)))
_,Brem=divide_ab(Bperturb)
Bvec=np.array([Brem.get(e,nc.ZERO) for e in nc.FREE],dtype=np.int64)
lift_obstructions=mm(L,Bvec[:,None,:])[:,0,:]

# Check the stated Fermat coefficient lift over (Z/25)[h]/(h²-2).
def add25(a,b):return ((a[0]+b[0])%25,(a[1]+b[1])%25)
def mul25(a,b):return ((a[0]*b[0]+2*a[1]*b[1])%25,(a[0]*b[1]+a[1]*b[0])%25)
def sum25(*fs):
    out={}
    for f in fs:
        for e,c in f.items():out[e]=add25(out.get(e,(0,0)),c)
    return {e:c for e,c in out.items() if c!=(0,0)}
def scale25(f,k):return {e:mul25(c,k) for e,c in f.items() if mul25(c,k)!=(0,0)}
def times25(f,g):
    out={}
    for e,c in f.items():
        for m,d in g.items():
            n=tuple(a+b for a,b in zip(e,m))
            out[n]=add25(out.get(n,(0,0)),mul25(c,d))
    return {e:c for e,c in out.items() if c!=(0,0)}
f125={(0,0,0,0,1):(1,0),(2,0,0,0,0):(3,0)}
f225={(1,1,0,0,0):(1,0),(0,0,1,1,0):(0,24)}
g125={(0,0,0,0,2):(4,0),(2,0,0,0,1):(13,0),(4,0,0,0,0):(11,0)}
g225={(2,2,0,0,0):(1,0),(1,1,1,1,0):(0,1),(0,0,2,2,0):(2,0)}
A25={(3,0,0,0,0):(12,0),(0,3,0,0,0):(1,0)}
B25={(0,0,3,0,0):(0,7),(0,0,0,3,0):(7,0)}
fermat25={(6,0,0,0,0):(2,0),(0,6,0,0,0):(1,0),
          (0,0,6,0,0):(2,0),(0,0,0,6,0):(1,0),(0,0,0,0,3):(4,0)}
assert sum25(times25(f125,g125),times25(f225,g225),times25(A25,A25),
             scale25(times25(B25,B25),(24,0)))==fermat25
assert (7*7+1)%25==0 and (12*12+4*3**3-2)%25==0

# Reconstruct the actual lambda=1 sextic modulo 25, then independently divide
# its coefficientwise difference from Fermat by five before reducing modulo 5.
QX25={(2,0,0,0,0):(1,0),(1,1,0,0,0):(2,0),(0,0,0,0,1):(24,0)}
QY25={(0,0,2,0,0):(1,0),(0,0,1,1,0):(2,0),(0,0,0,0,1):(24,0)}
pair25={(4,0,0,0,1):(1,0),(2,0,0,0,2):(1,0),
        (0,0,4,0,1):(1,0),(0,0,2,0,2):(1,0)}
G25=sum25(fermat25,scale25(pair25,(30,0)),
          scale25(times25(times25(QX25,QX25),QY25),(15,0)),
          scale25(times25(QX25,times25(QY25,QY25)),(5,0)))
diff25=sum25(G25,scale25(fermat25,(24,0)))
assert all(c[0]%5==0 and c[1]%5==0 for c in diff25.values())
evaluated={}
for e,c in diff25.items():
    m=(e[0]+2*e[4],e[1],e[2],e[3])
    value=nc.mul((c[0]//5,c[1]//5),nc.powf(nc.const(2),e[4]))
    evaluated[m]=nc.add(evaluated.get(m,nc.ZERO),value)
evaluated={e:c for e,c in evaluated.items() if c!=nc.ZERO}
assert evaluated==Bperturb

def evaluate(point):
    out=[nc.ZERO,nc.ZERO]
    for j,e in enumerate(exponents):
        value=nc.ONE
        for coordinate,power in zip(point,e):value=nc.mul(value,nc.powf(coordinate,power))
        for i in range(2):out[i]=nc.add(out[i],nc.mul(tuple(coefficients[i,j]),value))
    return out

def gradient(point):
    mat=np.zeros((2,3,2),dtype=np.int64)
    for i in range(2):
        for j,e in enumerate(exponents):
            for col,power in enumerate(e):
                if not power:continue
                value=nc.mul(nc.const(power),tuple(coefficients[i,j]))
                for l,ex in enumerate(e):value=nc.mul(value,nc.powf(point[l],ex-(l==col)))
                mat[i,col]=(mat[i,col]+np.array(value))%5
    return mat

elements=[(a,b) for a in range(5) for b in range(5)]
points=[(nc.ONE,u,v) for u in elements for v in elements]
points += [(nc.ZERO,nc.ONE,v) for v in elements]+[(nc.ZERO,nc.ZERO,nc.ONE)]
zeros=[]
for point in points:
    if evaluate(point)==[nc.ZERO,nc.ZERO]:
        grad=gradient(point)
        zeros.append({"point":point,"gradient_rank":nc.span.extension_rank(grad)[0],"gradient":grad.tolist()})
receipt={"field":"F5[h]/(h^2-2)","kernel_free_parameter_indices":free,
         "kernel_basis_columns":K.tolist(),"left_cokernel_rows":L.tolist(),
         "quadratic_monomial_exponents":exponents,"quadratic_coefficients":coefficients.tolist(),
         "quadratic_identically_zero":not bool(np.any(coefficients)),
         "independent_full_norm_map_quadratic_check":True,
         "projective_points_checked":len(points),"projective_zero_count":len(zeros),
         "transverse_projective_zeros":[v for v in zeros if v['gradient_rank']==2],
         "actual_target_first_lift_obstructions":lift_obstructions.tolist(),
         "Fermat_mod25_decomposition_checked":True,
         "actual_target_mod25_perturbation_checked":True,
         "Fermat_seed_mod25_lift":{"i":7,"p":12,"q":"7h","chi":"h","k":3,
             "equations":["i^2=-1","p^2=2-4*k^3","q=i*h","p*chi^3=q*i"],
             "modulus":25},
         "scope":"Exact rank, quadratic obstruction, and first mod25 obstruction checks at this fixed lambda=1 seed. The quadratic obstruction is zero and the first target obstruction is nonzero, excluding the ordinary and pi^2=5 lifts of this seed. No higher-order solution, general contact nonexistence, trace, or certificate asserted."}
(HERE/'norm_contact_seed_tangent.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k not in ['kernel_basis_columns','left_cokernel_rows']},indent=2))
