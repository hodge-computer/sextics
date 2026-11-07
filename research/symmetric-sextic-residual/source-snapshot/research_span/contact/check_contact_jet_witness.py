#!/usr/bin/env python3
"""Independent exact-rational verification of a finite contact-jet witness.

No Arb, floating-point linear algebra, root finder, series generator, or
Groebner basis is used here. All arithmetic is rational, using python-flint.
Dyadic arrays in the witness are approximations only. This checker constructs
its own error bounds for the actual implicit contact series and its normalized
negative-ideal functional, and proves the selected source-jet minor invertible.

The interpretation of that functional as the canonical residue/Abel-Jacobi
row is stated separately. No rational primitive or HasCertificate is claimed.
"""
from pathlib import Path
from fractions import Fraction
from itertools import product
from collections import defaultdict
import argparse,hashlib,json,sys,time
from flint import fmpq as Q, fmpq_poly as Poly, fmpq_mat as Mat

HERE=Path(__file__).resolve().parent
PREVIOUS=next(p for p in [HERE.parents[1]/'proof_attempt4',
                         HERE.parents[1]/'research_contact'] if p.is_dir())
sys.path.insert(0,str(PREVIOUS))
import contact_certify as C
N=48

def rational(x):
    return Q(x.numerator,x.denominator) if isinstance(x,Fraction) else Q(x)

def dyad(z):
    a,e=z
    return Q(a*(1<<e)) if e>=0 else Q(a,1<<(-e))

def cdecode(z):return dyad(z[0]),dyad(z[1])
def cabs(z):return abs(z[0])+abs(z[1])
def cadd(z,w):return z[0]+w[0],z[1]+w[1]
def cmul(z,w):return z[0]*w[0]-z[1]*w[1],z[0]*w[1]+z[1]*w[0]

def pow2(e):return Q(1<<e) if e>=0 else Q(1,1<<(-e))

def upper_pow2(x):
    assert x>=0
    if not x:return Q(0)
    e=int(x.p).bit_length()-int(x.q).bit_length()
    y=pow2(e)
    return y if y>=x else 2*y

def exponent_bound(x):
    if not x:return None
    y=upper_pow2(x)
    return int(y.p).bit_length()-int(y.q).bit_length()

class CP:
    """Complex polynomial in t, truncated modulo t^N, over exact Q(i)."""
    __slots__=('re','im')
    def __init__(self,re=0,im=0):
        self.re=re if isinstance(re,Poly) else Poly([rational(re)])
        self.im=im if isinstance(im,Poly) else Poly([rational(im)])
    def __add__(self,z):
        if not isinstance(z,CP):z=CP(z)
        return CP(self.re+z.re,self.im+z.im)
    __radd__=__add__
    def __neg__(self):return CP(-self.re,-self.im)
    def __sub__(self,z):return self+-z if isinstance(z,CP) else self+CP(-rational(z))
    def __mul__(self,z):
        if not isinstance(z,CP):
            q=rational(z);return CP(self.re*q,self.im*q)
        if not self.im and not z.im:return CP((self.re*z.re).truncate(N))
        return CP((self.re*z.re-self.im*z.im).truncate(N),
                  (self.re*z.im+self.im*z.re).truncate(N))
    __rmul__=__mul__
    def __getitem__(self,k):return self.re[k],self.im[k]

def cp_from_data(v):
    z=[cdecode(a) for a in v]
    return CP(Poly([a for a,b in z]),Poly([b for a,b in z]))

def complex_matrix(rows):
    return Mat([[z[0] for z in row] for row in rows]),Mat([[z[1] for z in row] for row in rows])

def matrix_from_data(rows):return complex_matrix([[cdecode(z) for z in row] for row in rows])

def mat_product(B,A):
    br,bi=B;ar,ai=A
    return br*ar-bi*ai,br*ai+bi*ar

def matrix_norm(A):
    r,i=A
    return max(sum((abs(r[a,b])+abs(i[a,b]) for b in range(r.ncols())),Q(0))
               for a in range(r.nrows()))

def matrix_defect(B,A):
    r,i=mat_product(B,A);n=r.nrows()
    return max(sum((abs(Q(int(a==b))-r[a,b])+abs(i[a,b]) for b in range(n)),Q(0))
               for a in range(n))

def row_bounds(polys):
    out=[Q(0)]*4
    for p in polys:
        sums=[Q(0)]*4
        for m,c in p.items():sums[len(m)]+=abs(rational(c))
        out=[max(x,y) for x,y in zip(out,sums)]
    return out

def evaluate_polynomials(polys,X,cache=None):
    if cache is None:cache={():CP(1)}
    def mon(m):
        if m not in cache:cache[m]=mon(m[:-1])*X[m[-1]]
        return cache[m]
    out=[]
    for p in polys:
        out.append(sum((rational(c)*mon(m) for m,c in p.items()),CP()))
    return out,cache

def perturbation(M,E,degree_sums):
    """Coefficient majorant for polynomial evaluation under |dx_k|<=E_k."""
    base=Poly(M);expanded=base+Poly(E);out=Poly()
    for d,c in enumerate(degree_sums):
        if c and d:
            out+=(expanded.pow_trunc(d,N)-base.pow_trunc(d,N))*c
    return out.truncate(N)

def monomials(d,parity):
    return sorted(e for e in product(range(d+1),repeat=4)
                  if sum(e)==d and (e[2]+e[3])%2==parity)

def add_coeff(form,e,coefficient,variables=()):
    p=form.setdefault(e,{})
    m=tuple(sorted(variables));p[m]=p.get(m,Fraction())+Fraction(coefficient)

def negative_ideal_polynomials():
    """Rebuild all 44 columns independently from the five defining forms."""
    blocks=C.coefficient_blocks(json.loads(C.CIRCUIT.read_text()))
    h2=dict(zip(C.M2,blocks[0]));h4=dict(zip(C.M4,blocks[1]))
    forms=[{}, {}, {}, {}, {}]
    add_coeff(forms[0],C.AB,1)
    for i,e in enumerate(C.QBASE):
        add_coeff(forms[0],e,1,(5+i,))
        for j,f in enumerate(C.QBASE):
            add_coeff(forms[1],tuple(a+b for a,b in zip(e,f)),3,(i,j))
        for f,c in h2.items():
            if c:add_coeff(forms[1],tuple(a+b for a,b in zip(e,f)),-2*c,(i,))
    for e,c in h4.items():
        if c:add_coeff(forms[1],e,c)
    for i,e in enumerate(C.M4):add_coeff(forms[2],e,1,(26+i,))
    for i,e in enumerate(C.ABASE):add_coeff(forms[3],e,1,(10+i,))
    for i,e in enumerate(C.BBASE):add_coeff(forms[4],e,1,(18+i,))
    rows=monomials(6,1);index={m:i for i,m in enumerate(rows)};cols=[]
    for f,d,p in zip(forms,[2,4,4,3,3],[0,0,0,0,1]):
        for m in monomials(6-d,1-p):
            col=[{} for _ in rows]
            for e,c in f.items():
                col[index[tuple(a+b for a,b in zip(e,m))]]={v:a for v,a in c.items() if a}
            cols.append(col)
    assert len(rows)==40 and len(cols)==44
    return rows,cols

def source_polynomials(X,L,rows):
    Q1=dict(zip(C.QBASE,X[:5]));zero=(0,0,0,0)
    powers=[{zero:CP(1)}]
    for k in range(2):
        out={}
        for m,a in powers[-1].items():
            for e,b in Q1.items():
                z=tuple(x+y for x,y in zip(m,e));out[z]=out.get(z,CP())-a*b
        powers.append(out)
    weighted=sorted(e+(u,) for u in range(4) for e in monomials(6-2*u,1))
    index={m:i for i,m in enumerate(rows)};out=[]
    for m in weighted:
        p=CP()
        for e,c in powers[m[4]].items():p+=c*L[index[tuple(a+b for a,b in zip(e,m[:4]))]]
        out.append(p)
    return weighted,out

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--witness',default='exact_target_contact_jet_witness.json')
    args=ap.parse_args();start=time.time()
    path=HERE/args.witness;w=json.loads(path.read_text())
    assert w['Taylor_order']==47
    assert w['source_circuit_sha256']==hashlib.sha256(C.CIRCUIT.read_bytes()).hexdigest()
    assert w['prior_contact_ball_sha256']==hashlib.sha256((PREVIOUS/'contact_exact_ball.json').read_bytes()).hexdigest()
    X=[cp_from_data(v) for v in w['contact_coefficients']]
    L=[cp_from_data(v) for v in w['functional_coefficients']]
    assert len(X)==45 and len(L)==40
    assert all(len(v)==N for v in w['contact_coefficients']+w['functional_coefficients'])
    assert Q(w['curve_parameter_scale'])==Q(1,4096)
    assert X[0][0]==(Q(1,4),Q(0)) and X[0][1]==(Q(w['curve_parameter_scale']),Q(0))
    assert all(X[0][n]==(0,0) for n in range(2,N))
    hpolys=C.POLYS[:44]
    H,cache=evaluate_polynomials(hpolys,X)
    print('Exact contact residual series reconstructed.',flush=True)
    js,cache=evaluate_polynomials([C.DERIVS[i][j] for i in range(44) for j in range(1,45)],X,cache)
    J0=complex_matrix([[js[44*i+j][0] for j in range(44)] for i in range(44)])
    B=matrix_from_data(w['contact_constant_preconditioner'])
    nb=matrix_norm(B);z=matrix_defect(B,J0)
    residual0=complex_matrix([[p[0]] for p in H]);eta=matrix_norm(mat_product(B,residual0))
    radius=Q(w['root_radius'])
    assert 0<radius<1
    constant_norm=max(cabs(x[0]) for x in X)
    M=int(constant_norm.p//constant_norm.q)+2
    h=max(sum(abs(rational(c))*len(m)*(len(m)-1)*M**max(0,len(m)-2)
              for m,c in p.items()) for p in hpolys)
    contraction=z+nb*h*radius
    assert contraction<1 and eta+contraction*radius<radius
    previous=json.loads((PREVIOUS/'contact_exact_ball.json').read_text())
    distance=max(abs(x[0][0]-Q(old[0]))+abs(x[0][1]-Q(old[1]))
                 for x,old in zip(X,previous['center'][:45]))
    oldradius=Q(previous['radius'])
    assert distance+radius<oldradius
    e0=upper_pow2(radius)
    assert constant_norm+max(e0,distance+oldradius)<M
    assert z+nb*h*(distance+oldradius)<1
    assert z+nb*h*e0<1
    D=upper_pow2(nb/(1-z-nb*h*e0))
    print('Exact root contraction and original-ball binding PASS.',flush=True)
    mids=[max(cabs(p[n]) for p in X) for n in range(N)]
    eps=[e0]+[Q(0)]*(N-1);sums=row_bounds(hpolys)
    hres=[max(cabs(p[n]) for p in H) for n in range(N)]
    for n in range(1,N):
        delta=perturbation(mids,eps,sums)[n]
        eps[n]=upper_pow2(D*(hres[n]+delta))
    print('Contact coefficient error exponents:',[exponent_bound(eps[n]) for n in [0,1,8,16,32,47]],flush=True)

    rows,cols=negative_ideal_polynomials()
    chosen=w['ideal_selected_columns'];normal=w['ideal_normalization_coordinate']
    assert len(set(chosen))==39 and all(0<=j<44 for j in chosen) and 0<=normal<40
    cpolys=[cols[j] for j in chosen]+[[{():Fraction(int(i==normal))} for i in range(40)]]
    flat,cache=evaluate_polynomials([p for row in cpolys for p in row],X,cache)
    CM=[flat[40*i:40*(i+1)] for i in range(40)]
    C0=complex_matrix([[p[0] for p in row] for row in CM])
    BC=matrix_from_data(w['functional_constant_preconditioner']);nc=matrix_norm(BC);zc=matrix_defect(BC,C0)
    csums=[Q(0)]*4
    for row in cpolys:
        r=[Q(0)]*4
        for p in row:
            for m,c in p.items():r[len(m)]+=abs(rational(c))
        csums=[max(a,b) for a,b in zip(csums,r)]
    u=perturbation(mids,eps,csums)
    assert zc+nc*u[0]<1
    DC=upper_pow2(nc/(1-zc-nc*u[0]))
    c_norm=[max(sum((cabs(p[n]) for p in row),Q(0)) for row in CM) for n in range(N)]
    R=[sum((p*l for p,l in zip(row,L)),CP())-int(i==39) for i,row in enumerate(CM)]
    rnorm=[max(cabs(p[n]) for p in R) for n in range(N)]
    lmids=[max(cabs(p[n]) for p in L) for n in range(N)]
    input_error=(u*Poly(lmids)).truncate(N)
    leps=[]
    for n in range(N):
        recurrence=sum(((c_norm[k]+u[k])*leps[n-k] for k in range(1,n+1)),Q(0))
        leps.append(upper_pow2(DC*(rnorm[n]+input_error[n]+recurrence)))
    print('Functional coefficient error exponents:',[exponent_bound(leps[n]) for n in [0,1,8,16,32,47]],flush=True)

    weighted,sources=source_polynomials(X,L,rows)
    assert [list(m) for m in weighted]==w['weighted_degree_six_negative_basis']
    MP,EP,ML,EL=Poly(mids),Poly(eps),Poly(lmids),Poly(leps)
    source_errors=[]
    for d in range(3):
        source_errors.append((((MP+EP).pow_trunc(d,N)*(ML+EL)-MP.pow_trunc(d,N)*ML)*5**d).truncate(N))
    errors=[max(p[n] for p in source_errors) for n in range(N)]
    columns=w['span_selected_columns'];exponents=w['span_row_scale_binary_exponents']
    assert len(set(columns))==48 and all(0<=j<60 for j in columns) and len(exponents)==48
    data=[[(sources[j][n][0]*pow2(-exponents[n]),sources[j][n][1]*pow2(-exponents[n]))
           for j in columns] for n in range(48)]
    A=complex_matrix(data);BS=matrix_from_data(w['span_preconditioner'])
    zs=matrix_defect(BS,A)
    br,bi=BS
    error_bound=max(sum(((abs(br[i,k])+abs(bi[i,k]))*48*errors[k]*pow2(-exponents[k])
                         for k in range(48)),Q(0)) for i in range(48))
    total=zs+error_bound
    print('Span exact center defect <=2^',exponent_bound(zs),flush=True)
    print('Span propagated error <=2^',exponent_bound(error_bound),flush=True)
    assert total<1
    receipt={'status':'PASS','verification_arithmetic':'Exact rational arithmetic only; no Arb or floating point.',
        'witness_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
        'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'coefficient_builder_sha256':hashlib.sha256((PREVIOUS/'contact_certify.py').read_bytes()).hexdigest(),
        'source_circuit_sha256':w['source_circuit_sha256'],'Taylor_order':47,
        'contact_system_shape':[44,44],'negative_ideal_system_shape':[40,40],
        'source_jet_matrix_shape':[48,60],'certified_rank':48,
        'constant_contact_inverse_bound_binary_exponent':exponent_bound(D),
        'constant_functional_inverse_bound_binary_exponent':exponent_bound(DC),
        'root_contraction_bound_binary_exponent':exponent_bound(contraction),
        'root_mapping_bound_binary_exponent':exponent_bound(eta+contraction*radius),
        'root_radius':str(radius),'root_in_prior_contact_ball':True,
        'unique_fixed_rho0_contact_root_in_prior_ball':True,
        'contact_coefficient_error_binary_exponents':list(map(exponent_bound,eps)),
        'functional_coefficient_error_binary_exponents':list(map(exponent_bound,leps)),
        'source_coefficient_error_binary_exponents':list(map(exponent_bound,errors)),
        'span_center_defect_binary_exponent':exponent_bound(zs),
        'span_propagated_error_binary_exponent':exponent_bound(error_bound),
        'span_total_defect_binary_exponent':exponent_bound(total),
        'seconds':time.time()-start,'Lean_proof':False,'full_certificate_proved':False,
        'scope':'Actual lambda=1 contact root and implicit normalized functional have a full-rank48 finite source jet. Identification with the canonical residue functional uses the separately explained exact norm-derivative identity, the previously certified regular sequence, and its nonzero prescribed-source residue.'}
    (HERE/'contact_jet_rational_replay.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print('EXACT RATIONAL FINITE-JET RANK48 PASS',receipt['seconds'],'seconds',flush=True)

if __name__=='__main__':main()
