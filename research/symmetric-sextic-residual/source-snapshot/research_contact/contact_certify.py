#!/usr/bin/env python3
"""Exact rational contraction certificate for an actual contact incidence.

Discovery uses mpmath; verification uses Fraction arithmetic. The theorem
justifying the reported bounds is a Banach fixed-point argument on a complex
polydisc using |Re z|+|Im z| as the scalar norm. This is not yet a Lean proof.
No source trace or HasCertificate theorem is asserted.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import defaultdict
from itertools import product
from functools import lru_cache
from types import SimpleNamespace
import sys,json,hashlib,argparse,time,math

HERE=Path(__file__).resolve().parent
CIRCUIT=HERE/'contact_target_circuit.json'
QBASE=[(2,0,0,0),(0,2,0,0),(0,0,2,0),(0,0,1,1),(0,0,0,2)]
ABASE=[(3,0,0,0),(0,3,0,0),(1,0,2,0),(1,0,1,1),
       (1,0,0,2),(0,1,2,0),(0,1,1,1),(0,1,0,2)]
BBASE=[(2,0,1,0),(2,0,0,1),(0,2,1,0),(0,2,0,1),
       (0,0,3,0),(0,0,2,1),(0,0,1,2),(0,0,0,3)]
AB=(1,1,0,0)
def mons(d):
    return sorted(e for e in product(range(d+1),repeat=4)
                  if sum(e)==d and (e[2]+e[3])%2==0)
M2,M4,M6=mons(2),mons(4),mons(6)
def coefficient_blocks(data):
    nodes=data['nodes']
    @lru_cache(None)
    def ev(k):
        op,z=nodes[k]['op'],nodes[k]['data']
        if op=='rational':return F(*z)
        if op=='variable':
            assert z=='lam';return F(1)
        if op=='add':return sum(map(ev,z),F())
        if op=='multiply':return math.prod(map(ev,z))
        if op=='power':return ev(z[0])**z[1]
        if op=='inverse':return 1/ev(z)
        raise ValueError(op)
    out=[]
    for power,ms in [(2,M2),(1,M4),(0,M6)]:
        p={tuple(z['exponent'][:4]):ev(z['coefficient_node'])
           for z in data['polynomials']['G'] if z['exponent'][4]==power}
        out.append([p.get(e,F()) for e in ms])
    return out
H=SimpleNamespace(CIRCUIT=CIRCUIT,QBASE=QBASE,ABASE=ABASE,BBASE=BBASE,AB=AB,
 M2=M2,M4=M4,M6=M6,I6={e:i for i,e in enumerate(M6)},coef_as_fraction=coefficient_blocks)
N=47
ACTIVE=list(range(1,47))             # rho0 fixed; r and alpha vary.
INCIDENCE=list(range(45))+[46]       # r fixed; rho0 and alpha vary.

def equations():
    """47 ambient variables, 46 exact equations at lambda=s=1."""
    exact=H.coef_as_fraction(json.loads(H.CIRCUIT.read_text()))
    h2,h4,h6=[dict(zip(ms,b)) for ms,b in zip([H.M2,H.M4,H.M6],exact)]
    ps=[defaultdict(F) for _ in range(46)]
    def add(i,c,indices=()):ps[i][tuple(sorted(indices))]+=c
    def sextic(c,exps,indices):
        e=tuple(map(sum,zip(*exps)));add(H.I6[e],c,indices)
    for i,e in enumerate(H.QBASE):
        for j,f in enumerate(H.QBASE):
            for k,g in enumerate(H.QBASE):sextic(F(1),[e,f,g],(i,j,k))
            for g,c in h2.items():sextic(-c,[e,f,g],(i,j))
        for f,c in h4.items():sextic(c,[e,f],(i,))
    for basis,offset,sign in [(H.ABASE,10,1),(H.BBASE,18,-1)]:
        for i,e in enumerate(basis):
            for j,f in enumerate(basis):sextic(F(sign),[e,f],(offset+i,offset+j))
    for j,f in enumerate(H.M4):
        sextic(F(1),[H.AB,f],(26+j,))
        for i,e in enumerate(H.QBASE):sextic(F(1),[e,f],(5+i,26+j))
    for i,e in enumerate(H.M6):add(i,-h6[e])
    # q=Q2(1,r,alpha,alpha), h=(A+B)(1,r,alpha,alpha).
    add(44,F(1),(45,))
    for i,e in enumerate(H.QBASE):
        add(44,F(1),(5+i,)+(45,)*e[1]+(46,)*(e[2]+e[3]))
    for basis,offset in [(H.ABASE,10),(H.BBASE,18)]:
        for i,e in enumerate(basis):
            add(45,F(1),(offset+i,)+(45,)*e[1]+(46,)*(e[2]+e[3]))
    return [{m:c for m,c in p.items() if c} for p in ps]

POLYS=equations()
def derivative(p,j):
    q=defaultdict(F)
    for m,c in p.items():
        count=m.count(j)
        if count:
            a=list(m);a.remove(j);q[tuple(a)]+=c*count
    return dict(q)
DERIVS=[[derivative(p,j) for j in range(N)] for p in POLYS]
def point_open_polynomials():
    def multiply(p,q):
        out=defaultdict(F)
        for m,c in p.items():
            for n,d in q.items():out[tuple(sorted(m+n))]+=c*d
        return dict(out)
    def combine(*items):
        out=defaultdict(F)
        for scale,p in items:
            for m,c in p.items():out[m]+=scale*c
        return dict(out)
    beta={(i,)+(45,)*e[1]+(46,)*(e[2]+e[3]):F(-1)
          for i,e in enumerate(QBASE)}
    blocks=coefficient_blocks(json.loads(CIRCUIT.read_text()))
    def point_coeff(ms,coeffs):
        out=defaultdict(F)
        for e,c in zip(ms,coeffs):out[(45,)*e[1]+(46,)*(e[2]+e[3])]+=c
        return dict(out)
    h2=point_coeff(M2,blocks[0]);h4=point_coeff(M4,blocks[1])
    normal=combine((3,multiply(beta,beta)),(2,multiply(h2,beta)),(1,h4))
    return {'r':{(45,):F(1)},'alpha':{(46,):F(1)},'beta':beta,'G_u_at_point':normal}
def value(p,x,coerce=lambda c:c,zero=0):
    s=zero
    for m,c in p.items():
        a=coerce(c)
        for i in m:a*=x[i]
        s+=a
    return s
def mpq(q):return mp.mpf(q.numerator)/q.denominator
def eval_mp(x,columns):
    return mp.matrix([value(p,x,mpq) for p in POLYS]),\
           mp.matrix([[value(row[j],x,mpq) for j in columns] for row in DERIVS])

class QC:
    __slots__=('a','b')
    def __init__(self,a=0,b=0):self.a,self.b=F(a),F(b)
    def __add__(self,y):
        if not isinstance(y,QC):y=QC(y)
        return QC(self.a+y.a,self.b+y.b)
    __radd__=__add__
    def __neg__(self):return QC(-self.a,-self.b)
    def __sub__(self,y):return self+-asqc(y)
    def __rsub__(self,y):return asqc(y)+-self
    def __mul__(self,y):
        y=asqc(y);return QC(self.a*y.a-self.b*y.b,self.a*y.b+self.b*y.a)
    __rmul__=__mul__
    def norm(self):return abs(self.a)+abs(self.b)
    def encode(self):return [str(self.a),str(self.b)]
def asqc(x):return x if isinstance(x,QC) else QC(x)
def decode(x):return QC(*x)
def round_mp(x,digits=72):
    d=10**digits
    return QC(F(int(mp.nint(mp.re(x)*d)),d),F(int(mp.nint(mp.im(x)*d)),d))
def matrix_norm(a):return max(sum(x.norm() for x in row) for row in a)
def dot(x,y):return sum((a*b for a,b in zip(x,y)),QC())

def initial_incidence():
    import numpy as np
    data=json.loads((HERE/'contact_homotopy_42.json').read_text())
    x=np.array([complex(*z) for z in data['candidate']])
    P=np.polynomial.Polynomial
    mu=x[5:10];aa=x[10:18];bb=x[18:26]
    q=-P([mu[0],1,mu[1]])/sum(mu[2:])
    even=P([aa[0],0,0,aa[1]])+P([sum(aa[2:5]),sum(aa[5:])])*q
    odd=P([sum(bb[:2]),0,sum(bb[2:4])])+sum(bb[4:])*q
    poly=even*even-q*odd*odd
    choices=[]
    for r in poly.roots():
        alpha=-even(r)/odd(r)
        y=np.concatenate([x,[r,alpha]])
        J=np.array([[value(row[j],y,complex) for j in INCIDENCE] for row in DERIVS])
        condition=float(np.linalg.cond(J))
        choices.append((condition,y))
    condition,y=min(choices,key=lambda a:a[0])
    print('moving-point initial condition',condition,flush=True)
    return y

def discover():
    global mp
    try:import mpmath as mp
    except ImportError:
        sys.path.insert(0,str(HERE.parent/'proof_attempt3/python_deps'))
        import mpmath as mp
    mp.mp.dps=105
    x=[mp.mpc(z) for z in initial_incidence()]
    x[0]=mp.mpf(1)/4
    for step in range(8):
        v,J=eval_mp(x,ACTIVE)
        residual=max(abs(z) for z in v)
        print('refine',step,mp.nstr(residual,8),flush=True)
        if residual<mp.mpf('1e-95'):break
        dx=mp.lu_solve(J,v)
        for i,d in zip(ACTIVE,dx):x[i]-=d
    assert residual<mp.mpf('1e-90')
    _,J=eval_mp(x,ACTIVE)
    _,Ji=eval_mp(x,INCIDENCE)
    B=J**-1;Bi=Ji**-1
    center=[round_mp(z) for z in x]
    rounded=lambda A:[[round_mp(A[i,j]).encode() for j in range(A.cols)] for i in range(A.rows)]
    data={'schema':'symmetric-contact-rational-contraction-v1',
      'lambda':'1','s':'1','rho0':'1/4','ambient_variable_order':
       [f'rho{i}' for i in range(5)]+[f'mu{i}' for i in range(5)]+
       [f'A{i}' for i in range(8)]+[f'B{i}' for i in range(8)]+
       [f'g2_{i}' for i in range(19)]+['r','alpha'],
      'active_columns':ACTIVE,'incidence_columns':INCIDENCE,
      'center':[z.encode() for z in center],
      'inverse':rounded(B),'incidence_inverse':rounded(Bi),
      'radius':'1/'+str(10**35),
      'scalar_norm':'abs(real)+abs(imaginary)',
      'circuit_sha256':hashlib.sha256(H.CIRCUIT.read_bytes()).hexdigest(),
      'source_trace_proved':False,'full_certificate_proved':False}
    path=HERE/'contact_exact_ball.json'
    path.write_text(json.dumps(data,separators=(',',':'))+'\n')
    print('saved exact rational center and matrices',path.stat().st_size,flush=True)
    return data

def upper_power(q):
    if not q:return '0'
    n=0;v=F(1)
    if q<=1:
        while q<=v/10:v/=10;n-=1
    else:
        while q>v:v*=10;n+=1
    assert q<=v
    return f'10^{n}'

def verify(data):
    start=time.time()
    assert data['circuit_sha256']==hashlib.sha256(H.CIRCUIT.read_bytes()).hexdigest()
    assert data['active_columns']==ACTIVE and data['incidence_columns']==INCIDENCE
    x=list(map(decode,data['center']));B=[[decode(z) for z in row] for row in data['inverse']]
    Bi=[[decode(z) for z in row] for row in data['incidence_inverse']]
    rad=F(data['radius'])
    assert x[0].a==F(1,4) and x[0].b==0 and rad>0
    v=[value(p,x,QC,QC()) for p in POLYS]
    J=[[value(row[j],x,QC,QC()) for j in ACTIVE] for row in DERIVS]
    Ji=[[value(row[j],x,QC,QC()) for j in INCIDENCE] for row in DERIVS]
    print('exact residual/Jacobians built',flush=True)
    eta=max(dot(row,v).norm() for row in B)
    def defect(C,K):
        cols=list(zip(*K));z=F(0)
        for i,row in enumerate(C):
            z=max(z,sum((QC(int(i==j))-dot(row,col)).norm() for j,col in enumerate(cols)))
        return z
    z=defect(B,J);zi=defect(Bi,Ji)
    nb,nbi=matrix_norm(B),matrix_norm(Bi)
    M=math.ceil(max(t.norm() for t in x)+rad)
    M=max(1,M)
    # Universal sum-of-absolute-Hessian bound for each equation. Includes
    # all ordered variable pairs and so bounds either column selection.
    h=max(sum(abs(c)*len(m)*(len(m)-1)*M**max(0,len(m)-2)
              for m,c in p.items()) for p in POLYS)
    L,Li=nb*h,nbi*h
    contraction=z+L*rad
    incidence_defect=zi+Li*rad
    assert contraction<1
    assert eta+contraction*rad<rad
    assert incidence_defect<1
    # All three chart determinant factors stay nonzero on this ball.
    zmu=x[5]*x[6]
    product_error=(x[5].norm()+x[6].norm())*rad+rad*rad
    delta_checks=[]
    for k in [1,2,3]:
        real_margin=abs(1-k*zmu.a)-k*product_error
        assert real_margin>0
        delta_checks.append({'factor':f'1-{k}*mu0*mu1','real_part_separated_from_zero':True})
    point_opens=[]
    for name,p in point_open_polynomials().items():
        center_value=value(p,x,QC,QC())
        lip=sum(abs(c)*len(m)*M**max(0,len(m)-1) for m,c in p.items())
        assert center_value.norm()>lip*rad
        point_opens.append({'function':name,'nonzero_on_entire_ball':True})
    receipt={'status':'PASS','method':'Exact rational Banach contraction and inverse-Jacobian bounds',
      'complex_unknown_count':46,'complex_equation_count':46,
      'rho0_fixed':'1/4','lambda_fixed':'1','s_fixed':'1',
      'radius':str(rad),'eta_upper_bound':upper_power(eta),
      'center_derivative_defect_upper_bound':upper_power(z),
      'center_incidence_defect_upper_bound':upper_power(zi),
      'inverse_norm_upper_bound':upper_power(nb),
      'incidence_inverse_norm_upper_bound':upper_power(nbi),
      'hessian_bound':str(h),'coordinate_bound':M,
      'contraction_constant_upper_bound':upper_power(contraction),
      'incidence_derivative_defect_upper_bound':upper_power(incidence_defect),
      'self_mapping_inequality':True,'contraction_inequality':True,
      'incidence_jacobian_invertible_at_actual_solution':True,
      'chart_factor_checks':delta_checks,
      'point_open_checks':point_opens,
      'interpretation':'Unique exact complex contact incidence in the stated ball; actual moving incidence Jacobian is nonsingular. Classical fixed-point and algebraic implicit-function arguments, not Lean.',
      'source_trace_proved':False,'full_certificate_proved':False,
      'witness_sha256':hashlib.sha256((HERE/'contact_exact_ball.json').read_bytes()).hexdigest(),
      'equation_source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'circuit_sha256':data['circuit_sha256'],'verification_seconds':time.time()-start}
    (HERE/'contact_exact_ball_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2),flush=True)
    return receipt

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--verify-only',action='store_true');args=ap.parse_args()
    data=json.loads((HERE/'contact_exact_ball.json').read_text()) if args.verify_only else discover()
    verify(data)
