"""Exact invariant degree-six certificate equations over Q.

Variables are elementary symmetric p,q,r,P,Q,R with weights 1,2,3,1,2,3.
Every equivariant polynomial vector field is expressed in the free S3 bases
E_k=sum x_i^k d/dx_i, k=0,1,2, on each block. We retain their true ambient
divergence. This script searches no prime-field point grid: it produces the
complete characteristic-zero incidence equations for algebraic denominators.
"""
from pathlib import Path
from flint import fmpq, fmpq_mat
import json, time, itertools

HERE=Path(__file__).resolve().parent
W=(1,2,3,1,2,3)
Z=(0,)*6

def add(a,b):
    out=a.copy()
    for e,c in b.items():
        v=out.get(e,0)+c
        if v: out[e]=v
        else: out.pop(e,None)
    return out

def scale(a,c): return {e:v*c for e,v in a.items() if v*c}

def mul(a,b):
    out={}
    for e,x in a.items():
        for f,y in b.items():
            g=tuple(i+j for i,j in zip(e,f))
            out[g]=out.get(g,0)+x*y
    return {e:c for e,c in out.items() if c}

def power(a,k):
    out={Z:1}
    for _ in range(k): out=mul(out,a)
    return out

def deriv(a,i):
    out={}
    for e,c in a.items():
        if e[i]:
            f=list(e); f[i]-=1
            out[tuple(f)]=c*e[i]
    return out

def var(i):
    e=list(Z);e[i]=1
    return {tuple(e):1}

def monomials(deg,weights=W):
    if len(weights)==1:
        if deg%weights[0]==0: yield (deg//weights[0],)
    else:
        for j in range(deg//weights[0]+1):
            for e in monomials(deg-j*weights[0],weights[1:]): yield (j,)+e

def y_parity(e): return (e[3]+e[5])%2

def newton6(p,q,r):
    out=power(p,6)
    for poly,c in [(mul(power(p,4),q),-6),(mul(power(p,2),power(q,2)),9),
                   (power(q,3),-2),(mul(power(p,3),r),6),(mul(mul(p,q),r),-12),
                   (power(r,2),3)]:out=add(out,scale(poly,c))
    return out

def data():
    p,q,r,P,Q,R=[var(i) for i in range(6)]
    U,V=newton6(p,q,r),newton6(P,Q,R)
    F=add(scale(add(U,V),7),add(scale(mul(power(q,2),Q),5),scale(mul(q,power(Q,2)),10)))
    A=mul(r,R)
    fields=[]
    for shift in [0,3]:
        a,b,c=[var(shift+i) for i in range(3)]
        local=[([{Z:3},scale(a,2),b],{}),
               ([a,scale(b,2),scale(c,3)],{Z:3}),
               ([add(power(a,2),scale(b,-2)),add(mul(a,b),scale(c,-3)),mul(a,c)],scale(a,2))]
        for k,(v,div) in enumerate(local):
            full=[{} for _ in range(6)]
            full[shift:shift+3]=v
            fields.append((shift//3,k,full,div))
    return F,A,U,V,fields

def act(v,P):
    out={}
    for i in range(6):out=add(out,mul(v[i],deriv(P,i)))
    return out

def divide_F(poly,F):
    lead=(0,0,2,0,0,0)
    tail={e:c for e,c in F.items() if e!=lead}
    out=poly.copy();quot={}
    todo={e for e in out if e[2]>=2}
    while todo:
        e=max(todo,key=lambda e:(e[2],e));todo.remove(e)
        c=out.pop(e,0)
        if not c:continue
        m=list(e);m[2]-=2
        quot[tuple(m)]=quot.get(tuple(m),0)+fmpq(c,F[lead])
        for f,a in tail.items():
            g=tuple(x+y for x,y in zip(m,f))
            v=out.get(g,0)-fmpq(c,F[lead])*a
            if v:
                out[g]=v
                if g[2]>=2:todo.add(g)
            else:out.pop(g,None)
    return out,{e:c for e,c in quot.items() if c}

def reduce_F(poly,F):return divide_F(poly,F)[0]

def columns_matrix(columns):
    rows=sorted({e for c in columns for e in c})
    return rows,fmpq_mat([[c.get(e,0) for c in columns] for e in rows])

def kernel(columns):
    rows,M=columns_matrix(columns)
    rr,rank=M.rref()
    piv=[]
    for i in range(rank):
        piv.append(next(j for j in range(rr.ncols()) if rr[i,j]))
    result=[]
    for j in range(rr.ncols()):
        if j not in piv:
            v={j:fmpq(1)}
            for i,c in enumerate(piv):
                if rr[i,j]:v[c]=-rr[i,j]
            result.append(v)
    return result,rank,len(rows)

def combo(coeffs,basis):
    out={}
    for i,c in coeffs.items():out=add(out,scale(basis[i],c))
    return out

def coeffs_to_field(coeffs,NB):
    field=[{} for _ in range(6)];div={}
    for i,c in coeffs.items():
        _,_,_,v,d=NB[i]
        for j in range(6):field[j]=add(field[j],scale(v[j],c))
        div=add(div,scale(d,c))
    return field,div

def bilinear(D,N,F):
    v,div=N
    return reduce_F(add(mul(D,div),scale(act(v,D),-1)),F)

def enc(poly):return [[list(e),str(c)] for e,c in sorted(poly.items())]

def dec(poly):return {tuple(e):fmpq(c) for e,c in poly}

def first_equation(degree=6):
    started=time.time()
    F,A,U,V,fields=data()
    NB=[]
    for block,k,v,d in fields:
        for e in monomials(degree+1-k):
            desired=1 if block==0 else k%2
            if y_parity(e)!=desired:continue
            b={e:1}
            vf=[mul(b,z) for z in v]
            div=add(act(v,b),mul(b,d))
            NB.append((block,k,e,vf,div))
    DB=[{e:1} for e in monomials(degree) if y_parity(e)==0]
    columns=[act(row[3],F) for row in NB]+[scale(mul(A,D),-1) for D in DB]
    rels,rank,rows=kernel(columns);n=len(NB)
    kernels=[];eligible=[]
    for rel in rels:
        nc={i:c for i,c in rel.items() if i<n}
        dc={i-n:c for i,c in rel.items() if i>=n}
        N=coeffs_to_field(nc,NB)
        assert add(act(N[0],F),scale(mul(A,combo(dc,DB)),-1))=={}
        if dc:eligible.append((combo(dc,DB),N))
        else:kernels.append(N)
    # Remove F-multiples by D -> D - BF, N -> N - AB E/6.
    shifted=[]
    for D,N in eligible:
        D1,B=divide_F(D,F)
        AB=mul(A,B)
        euler=[scale(mul(AB,var(i)),fmpq(W[i],6)) for i in range(6)]
        eulerdiv=scale(AB,fmpq(degree+6,6))
        N1=([add(v,scale(w,-1)) for v,w in zip(N[0],euler)],add(N[1],scale(eulerdiv,-1)))
        assert act(N1[0],F)==mul(A,D1)
        shifted.append((D1,N1))
    _,Dmat=columns_matrix([D for D,N in shifted])
    rr,drank=Dmat.rref()
    inds=[next(j for j in range(rr.ncols()) if rr[i,j]) for i in range(drank)]
    eligible=[shifted[i] for i in inds]
    print(json.dumps({'stage':'first_equation','N_columns':n,'D_columns':len(DB),'normal_rows':rows,
                      'normal_rank':rank,'kernelN':len(kernels),'eligibleD_modF':len(eligible),'seconds':time.time()-started}),flush=True)
    packet={'degree':degree,'variables':['p','q','r','P','Q','R'],'weights':W,'F':enc(F),'A':enc(A),
            'numerator_basis':[{'block':b,'power':k,'exponent':e} for b,k,e,_,_ in NB],
            'kernelN':[{'field':[enc(p) for p in N[0]],'div':enc(N[1])} for N in kernels],
            'eligible':[{'D':enc(D),'field':[enc(p) for p in N[0]],'div':enc(N[1])} for D,N in eligible],
            'first_equation_exactly_checked':True,'normal_rank':rank,'normal_rows':rows}
    (HERE/f'degree{degree}_exact_first_equation.json').write_text(json.dumps(packet,indent=2)+'\n')
    return F,A,kernels,eligible

def second_equation(F,A,kernels,eligible,degree=6):
    started=time.time()
    columns=[];types=[]
    for i,(D,N) in enumerate(eligible):
        for j in range(i,len(eligible)):
            E,M=eligible[j]
            col=bilinear(D,M,F)
            if i!=j:col=add(col,bilinear(E,N,F))
            columns.append(col);types.append(('b',i,j))
        for j,K in enumerate(kernels):
            columns.append(bilinear(D,K,F));types.append(('c',i,j))
    rows,M=columns_matrix(columns)
    rr,rank=M.rref()
    eqs=[{j:rr[i,j] for j in range(rr.ncols()) if rr[i,j]} for i in range(rank)]
    packet={'status':'EXACT_EQUATIONS','types':types,'equations':[[[j,str(c)] for j,c in eq.items()] for eq in eqs],
            'raw_coefficient_rows':len(rows),'independent_equations':rank,'D_parameters':len(eligible),
            'kernel_parameters':len(kernels),'full_certificate_proved':False}
    (HERE/f'degree{degree}_exact_second_equations.json').write_text(json.dumps(packet,indent=2)+'\n')
    print(json.dumps({'stage':'second_equation','rows':len(rows),'rank':rank,'terms':len(types),'seconds':time.time()-started}),flush=True)

if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser();parser.add_argument('--degree',type=int,default=6)
    args=parser.parse_args()
    second_equation(*first_equation(args.degree),degree=args.degree)
