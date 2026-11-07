"""Exact small F_25 contact calculations for the unchanged mod-5 target.

No solver, no characteristic-zero lift and no certificate claim. Elements are
a+5*b with j^2=2. Polynomial exponents are in (a,b,c,d).
"""
import itertools
import json
from pathlib import Path

P = 5

def add(x, y):
    return (x % 5 + y % 5) % 5 + 5 * ((x // 5 + y // 5) % 5)

def neg(x):
    return (-x % 5) + 5 * ((- (x // 5)) % 5)

def sub(x, y):
    return add(x, neg(y))

def mul(x, y):
    a, b, c, d = x % 5, x // 5, y % 5, y // 5
    return (a*c+2*b*d) % 5 + 5*((a*d+b*c) % 5)

def power(x, n):
    z = 1
    while n:
        if n & 1:
            z = mul(z, x)
        x = mul(x, x)
        n >>= 1
    return z

def inv(x):
    assert x != 0
    return power(x, 23)

def padd(f, g):
    out = f.copy()
    for m, c in g.items():
        v = add(out.get(m, 0), c)
        if v: out[m] = v
        elif m in out: del out[m]
    return out

def scale(f, c):
    return {m:mul(v,c) for m,v in f.items() if mul(v,c)}

def pmul(f, g):
    out = {}
    for m,c in f.items():
        for n,d in g.items():
            e = tuple(x+y for x,y in zip(m,n))
            out[e] = add(out.get(e,0),mul(c,d))
    return {m:c for m,c in out.items() if c}

def ppow(f, n):
    out = {(0,0,0,0):1}
    for _ in range(n): out = pmul(out,f)
    return out

def monos(d, parity=None, noab=False):
    out = []
    for m in itertools.product(range(d+1),repeat=4):
        if sum(m)!=d: continue
        if parity is not None and (m[2]+m[3])%2!=parity: continue
        if noab and m[0] and m[1]: continue
        out.append(m)
    return out

def rank(rows):
    A = [r[:] for r in rows]
    r=0; pivots=[]
    for c in range(len(A[0])):
        p=next((i for i in range(r,len(A)) if A[i][c]),None)
        if p is None: continue
        A[r],A[p]=A[p],A[r]
        k=inv(A[r][c]);A[r]=[mul(x,k) for x in A[r]]
        for i in range(len(A)):
            if i==r or not A[i][c]: continue
            k=A[i][c]
            A[i]=[sub(x,mul(k,y)) for x,y in zip(A[i],A[r])]
        pivots.append(c);r+=1
        if r==len(A):break
    return r,pivots,A

def kernel(rows):
    _,piv,R=rank(rows)
    out=[]
    for c in range(len(rows[0])):
        if c in piv:continue
        v=[0]*len(rows[0]);v[c]=1
        for i,j in enumerate(piv):v[j]=neg(R[i][c])
        out.append(v)
    return out

def split_vector(v):
    out=[];i=0
    for basis in [Q1basis,Q2basis,Abasis,Bbasis,g2basis]:
        out.append({m:c for m,c in zip(basis,v[i:i+len(basis)]) if c})
        i+=len(basis)
    return out

def quadratic_vector(q1,v):
    dq,dm,da,db,dg=split_vector(v)
    f=padd(padd(scale(pmul(q1,ppow(dq,2)),3),ppow(da,2)),scale(ppow(db,2),4))
    f=padd(f,pmul(dm,dg))
    return [f.get(m,0) for m in rows6]

def dot(v,w):
    out=0
    for a,b in zip(v,w):out=add(out,mul(a,b))
    return out

def quadratic_obstructions(q1,J):
    ker=kernel(J)
    cok=kernel([list(x) for x in zip(*J)])
    ds=[quadratic_vector(q1,k) for k in ker]
    terms=[];cols=[]
    for i in range(len(ker)):
        terms.append((i,i));cols.append(ds[i])
        for j in range(i+1,len(ker)):
            v=quadratic_vector(q1,[add(a,b) for a,b in zip(ker[i],ker[j])])
            terms.append((i,j));cols.append([sub(sub(a,b),c) for a,b,c in zip(v,ds[i],ds[j])])
    coeffs=[[dot(c,col) for col in cols] for c in cok]
    points=[]
    for pivot in range(len(ker)):
        for tail in itertools.product(range(25),repeat=len(ker)-pivot-1):
            v=[0]*pivot+[1]+list(tail)
            vals=[dot(q,[mul(v[i],v[j]) for i,j in terms]) for q in coeffs]
            if any(vals):continue
            grad=[]
            for q in coeffs:
                row=[0]*len(ker)
                for c,(i,j) in zip(q,terms):
                    row[i]=add(row[i],mul(c,v[j]));row[j]=add(row[j],mul(c,v[i]))
                grad.append(row)
            points.append({'coordinates':v,'gradient_rank':rank(grad)[0]})
    return {'kernel':ker,'cokernel':cok,'quadratic_terms':terms,
            'quadratic_coefficients':coeffs,'projective_F25_points':points}

Q1basis=[m for m in monos(2,0) if m!=(1,1,0,0)]
Q2basis=Q1basis
Abasis=monos(3,0,True)
Bbasis=monos(3,1,True)
g2basis=monos(4,0)
rows6=monos(6,0)

def contact_jacobian(q1,q2,A,B,g2):
    cols=[]
    g1=scale(ppow(q1,2),3)
    for basis,f in [(Q1basis,g1),(Q2basis,g2),
                    (Abasis,scale(A,2)),(Bbasis,scale(B,3)),
                    (g2basis,q2)]:
        cols.extend(pmul({m:1},f) for m in basis)
    return [[f.get(m,0) for f in cols] for m in rows6]

def main():
    a,b,c,d=[{tuple(int(i==j) for i in range(4)):1} for j in range(4)]
    j=5
    Q1=ppow(a,2)
    Q2=padd(pmul(a,b),scale(pmul(c,d),2))
    A=padd(scale(ppow(a,3),neg(j)),scale(ppow(b,3),2))
    B=padd(scale(ppow(c,3),j),ppow(d,3))
    X,Y=pmul(a,b),pmul(c,d)
    g2=scale(padd(padd(ppow(X,2),scale(pmul(X,Y),3)),scale(ppow(Y,2),4)),neg(j))
    target={}
    for f,k in [(a,3),(b,4),(c,3),(d,4)]:
        target=padd(target,scale(ppow(f,6),k))
    identity=padd(padd(padd(ppow(Q1,3),ppow(A,2)),scale(ppow(B,2),4)),pmul(Q2,g2))
    assert identity==target
    J=contact_jacobian(Q1,Q2,A,B,g2)
    r,piv,_=rank(J)
    obstructions=quadratic_obstructions(Q1,J)
    report={
       'field':'F_5[j]/(j^2-2)',
       'target':'G=u^3+3a^6+4b^6+3c^6+4d^6',
       'target_binding':'Exact normalized protected reflection pencil at lambda=1 modulo 5',
       'Q1':'a^2','Q2':'ab+2cd','A':'-j*a^3+2b^3','B':'j*c^3+d^3',
       'g2':'-j*(a^2*b^2-2abcd+4c^2*d^2)',
       'norm_identity_passed':True,
       'intrinsic_full_jacobian_shape':[len(J),len(J[0])],
       'intrinsic_full_jacobian_rank':r,'pivot_columns':piv,
       'square_etale_lift_available':r==44,
       'quadratic_obstruction':obstructions,
       'full_certificate_proved':False,
    }
    Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
