#!/usr/bin/env python3
"""Exact Kuranishi series for the structured symmetric contact over F25.

Solve the 68 image equations of the full quadratic norm map in a fixed affine
slice, leaving three formal parameters. Compute the two remaining equations
order by order and compare their first nonzero homogeneous part with actual
target perturbations. All coefficient arithmetic is exact in F5[h]/(h²-2).

No Hensel lift or certificate is inferred unless separate stated checks have
been completed. Dependencies: Python 3, NumPy, adjacent contact_lift_seed.py.
"""
from pathlib import Path
import argparse
import itertools
import json
import time
import numpy as np
import contact_lift_seed as nc

HERE=Path(__file__).resolve().parent
fm=nc.span.mul;mm=nc.span.matmul;fi=nc.span.inv

def rref(A):
    original=A.copy();A=A.copy()
    n,m,_=A.shape
    T=np.zeros((n,n,2),dtype=np.int64);T[:,:,0]=np.eye(n,dtype=np.int64)
    piv=[];r=0
    for c in range(m):
        choices=np.flatnonzero(np.any(A[r:,c],axis=-1))
        if not len(choices):continue
        k=r+int(choices[0]);A[[r,k]]=A[[k,r]];T[[r,k]]=T[[k,r]]
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
    assert np.array_equal(mm(T,original),A)
    assert not np.any(mm(original,K))
    assert not np.any(mm(T[r:],original))
    return A,T,K,piv,free

def polynomial(coords,basis):
    return {e:tuple(int(x) for x in c) for e,c in zip(basis,coords) if np.any(c)}

def divide_ab(f,chi=nc.H):
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
    q={(1,1,0,0):nc.ONE,(0,0,1,1):nc.neg(chi)}
    assert nc.plus(nc.times(q,quotient),remainder)==f
    return quotient,remainder

def seed_data():
    data=nc.check(nc.const(3),nc.const(2),nc.mul(nc.const(2),nc.H),nc.H,True)
    J=np.array(data['intrinsic_matrix'],dtype=np.int64)
    D=np.array(data['norm_map_matrix'],dtype=np.int64)
    _,_,K,_,free=rref(J)
    _,T,_,piv,full_free=rref(D)
    assert free==[5,10,13] and len(piv)==68
    fs=nc.forms(nc.const(3),nc.const(2),nc.mul(nc.const(2),nc.H),nc.H)
    Q1={(2,0,0,0):nc.const(3)}
    g2={e[:4]:v for e,v in fs[3].items()}
    A={e[:4]:v for e,v in fs[4].items()}
    B={e[:4]:v for e,v in fs[5].items()}
    def lift(direction):
        dq1=polynomial(direction[:5],nc.QBASE)
        dq2=polynomial(direction[5:10],nc.QBASE)
        da=polynomial(direction[10:18],nc.ABASE)
        db=polynomial(direction[18:],nc.BBASE)
        first=nc.plus(nc.scale(nc.times(nc.times(Q1,Q1),dq1),nc.const(-12)),
            nc.scale(nc.times(A,da),nc.const(-2)),nc.scale(nc.times(B,db),nc.const(2)),
            nc.scale(nc.times(dq2,g2),nc.const(-1)))
        dg2,rem=divide_ab(first);assert not rem
        lift4=lambda f:{e+(0,):c for e,c in f.items()}
        dq15=lift4(dq1);u={(0,0,0,0,1):nc.ONE}
        dg1=nc.plus(nc.scale(nc.times(u,dq15),nc.const(-4)),
             nc.scale(nc.times(lift4(Q1),dq15),nc.const(8)))
        output=np.zeros((90,2),dtype=np.int64)
        for i,f in enumerate([dq15,lift4(dq2),dg1,lift4(dg2),lift4(da),lift4(db)]):
            for j,e in enumerate(nc.span.parameter_bases[i]):output[nc.span.offsets[i]+j]=f.get(e,nc.ZERO)
        assert not np.any(mm(D,output[:,None,:]))
        return output
    Kfull=np.stack([lift(K[:,i]) for i in range(3)],axis=1)
    return data,D,T,piv,full_free,Kfull

def monomials3(n):
    return [(i,j,n-i-j) for i in range(n+1) for j in range(n-i+1)]

def encode_series(series):
    return {','.join(map(str,e)):v.tolist() for e,v in sorted(series.items())}

def compute_series(max_order):
    seed,D,T,piv,full_free,K=seed_data()
    leading={(1,0,0):K[:,0],(0,1,0):K[:,1],(0,0,1):K[:,2]}
    series={1:leading};obstructions={}
    for n in range(2,max_order+1):
        start=time.monotonic()
        rhs={e:np.zeros((70,2),dtype=np.int64) for e in monomials3(n)}
        for i in range(1,n):
            for e,v in series[i].items():
                for f,w in series[n-i].items():
                    m=tuple(x+y for x,y in zip(e,f))
                    rhs[m]=(rhs[m]+nc.span.quadratic(v,w))%5
        corr={};obs={}
        for e,v in rhs.items():
            tr=mm(T,v[:,None,:])[:,0,:]
            out=np.zeros((90,2),dtype=np.int64)
            out[piv]=-tr[:68]%5
            assert not np.any((mm(T,mm(D,out[:,None,:])+v[:,None,:]))[:68])
            if np.any(out):corr[e]=out
            if np.any(tr[68:]):obs[e]=tr[68:]
        series[n]=corr;obstructions[n]=obs
        print(json.dumps({'order':n,'nonzero_correction_monomials':len(corr),
              'nonzero_obstruction_monomials':len(obs),'seconds':round(time.monotonic()-start,3)}),flush=True)
    return seed,D,T,piv,full_free,K,series,obstructions

def target_direction(lam,L):
    lam2=nc.powf(lam,2);lam4=nc.powf(lam,4);lam6=nc.powf(lam,6)
    leading=nc.mul(nc.const(2),nc.add(nc.ONE,lam6))
    if leading==nc.ZERO:return None
    rho=next(nc.const(t) for t in range(1,5) if nc.mul(nc.const(4),nc.powf(nc.const(t),3))==leading)
    ri=tuple(int(t) for t in fi(np.array(rho)))
    a2={(2,0,0,0,0):nc.ONE};c2={(0,0,2,0,0):nc.ONE}
    ab={(1,1,0,0,0):nc.ONE};cd={(0,0,1,1,0):nc.ONE}
    u={(0,0,0,0,1):ri}
    Q=nc.plus(a2,nc.scale(ab,nc.const(2)),nc.scale(u,nc.const(-1)))
    R=nc.plus(c2,nc.scale(cd,nc.const(2)),nc.scale(u,nc.neg(lam2)))
    B=nc.plus(nc.times(nc.times(a2,a2),u),nc.times(a2,nc.times(u,u)),
        nc.scale(nc.times(nc.times(c2,c2),u),lam2),
        nc.scale(nc.times(c2,nc.times(u,u)),lam4),
        nc.scale(nc.times(nc.times(Q,Q),R),nc.const(3)),nc.times(Q,nc.times(R,R)))
    vector=np.array([B.get(e,nc.ZERO) for e in nc.plus_basis],dtype=np.int64)
    c=mm(L,vector[:,None,:])[:,0,:]
    return {'lambda':lam,'rho':rho,'cokernel_target':c.tolist()}

def polynomial_values(coefficients,points):
    out=np.zeros((len(points),2,2),dtype=np.int64)
    for e,c in coefficients.items():
        value=np.zeros((len(points),2),dtype=np.int64);value[:,0]=1
        for i,n in enumerate(e):
            for _ in range(n):value=fm(value,points[:,i,:])
        out=(out+fm(value[:,None,:],c[None,:,:]))%5
    return out

def derivatives(coefficients,col):
    out={}
    for e,c in coefficients.items():
        if not e[col]:continue
        f=list(e);f[col]-=1;f=tuple(f)
        value=c*e[col]%5
        if np.any(value):out[f]=value
    return out

def match_first_obstruction(obstructions,T):
    first=next((n for n in sorted(obstructions) if obstructions[n]),None)
    directions=[target_direction((a,b),T[68:]) for a in range(5) for b in range(5)]
    directions=[d for d in directions if d is not None]
    if first is None:return {'first_nonzero_order':None,'target_directions':directions}
    elements=np.array([(a,b) for a in range(5) for b in range(5)],dtype=np.int64)
    points=elements[np.array(list(itertools.product(range(25),repeat=3)),dtype=np.int64)]
    values=polynomial_values(obstructions[first],points)
    gradients=np.stack([polynomial_values(derivatives(obstructions[first],j),points) for j in range(3)],axis=2)
    regular=np.zeros(len(points),dtype=bool)
    for i,j in [(0,1),(0,2),(1,2)]:
        det=(fm(gradients[:,0,i,:],gradients[:,1,j,:])-fm(gradients[:,0,j,:],gradients[:,1,i,:]))%5
        regular|=np.any(det,axis=-1)
    results=[]
    for d in directions:
        target=np.array(d['cokernel_target'],dtype=np.int64)
        equal=np.all(values==target[None,:,:],axis=(1,2))
        hits=np.flatnonzero(equal&regular)
        entry={**d,'affine_solutions':int(np.sum(equal)),'regular_affine_solutions':int(len(hits))}
        if len(hits):
            j=int(hits[0]);entry.update({'first_regular_point':points[j].tolist(),
                                         'Jacobian':gradients[j].tolist()})
        results.append(entry)
    return {'first_nonzero_order':first,'affine_points_checked':len(points),
            'regular_points_total':int(np.sum(regular)),'target_matches':results}

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--order',type=int,default=4)
    args=parser.parse_args()
    seed,D,T,piv,full_free,K,series,obs=compute_series(args.order)
    matches=match_first_obstruction(obs,T)
    receipt={'field':'F5[h]/(h^2-2)','slice_image_dimension':68,'slice_kernel_dimension':3,
        'full_norm_pivot_columns':piv,'full_norm_nonpivot_columns':full_free,
        'row_transform':T.tolist(),'kernel_directions':K.tolist(),
        'series_coefficients':{str(n):encode_series(v) for n,v in series.items()},
        'obstruction_coefficients':{str(n):encode_series(v) for n,v in obs.items()},
        'matching_equation':'first_obstruction(v)=projected_target_B',
        'matches':matches,
        'scope':'Exact finite Kuranishi jets and leading target-direction matching only. No full formal lift, trace, or certificate asserted.'}
    output=HERE/f'contact_lift_kuranishi_order{args.order}.json'
    output.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'receipt':output.name,'obstructions':{str(n):encode_series(v) for n,v in obs.items()},
                      'matches':matches},indent=2),flush=True)

if __name__=='__main__':main()
