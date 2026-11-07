#!/usr/bin/env python3
"""Independent exact audit of the symmetric norm-contact existence witness.

Reconstructs the weighted cubic from the original six-variable sextic with
coefficients 5/7 and 10/7. Does not import the circuit, homotopy, or certificate
generator. Builds the 44 coefficient equations and two moving-point equations
by polynomial substitution, then independently checks exact Banach bounds.

Input: adjacent contact_exact_ball.json. Dependencies: Python 3 and NumPy.
The fixed-point argument is classical mathematics, not a Lean proof. No source
trace or final HodgeComputer certificate is claimed.
"""
from pathlib import Path
from fractions import Fraction as Q
from itertools import product
from collections import defaultdict
import hashlib
import json
import math
import time
import numpy as np

HERE=Path(__file__).resolve().parent
QBASE=[(2,0,0,0),(0,2,0,0),(0,0,2,0),(0,0,1,1),(0,0,0,2)]
ABASE=[(3,0,0,0),(0,3,0,0),(1,0,2,0),(1,0,1,1),
       (1,0,0,2),(0,1,2,0),(0,1,1,1),(0,1,0,2)]
BBASE=[(2,0,1,0),(2,0,0,1),(0,2,1,0),(0,2,0,1),
       (0,0,3,0),(0,0,2,1),(0,0,1,2),(0,0,0,3)]
AB=(1,1,0,0)
M4=sorted(e for e in product(range(5),repeat=4) if sum(e)==4 and (e[2]+e[3])%2==0)
M6=sorted(e for e in product(range(7),repeat=4) if sum(e)==6 and (e[2]+e[3])%2==0)
assert len(M4)==19 and len(M6)==44

def add_plain(*polys):
    out=defaultdict(Q)
    for p in polys:
        for e,c in p.items():out[e]+=c
    return {e:c for e,c in out.items() if c}
def scale_plain(p,c):return {e:v*c for e,v in p.items() if v*c}
def mul_plain(p,q):
    out=defaultdict(Q)
    for e,c in p.items():
        for f,d in q.items():out[tuple(a+b for a,b in zip(e,f))]+=c*d
    return {e:c for e,c in out.items() if c}
def power_plain(p,n):
    out={(0,)*len(next(iter(p))):Q(1)}
    for _ in range(n):out=mul_plain(out,p)
    return out

def original_target():
    """Original X0,X1,X2,Y0,Y1,Y2, then lambda=1 reflection substitution."""
    basis=[{tuple(int(i==j) for i in range(5)):Q(1)} for j in range(5)]
    a,b,c,d,v=basis
    coordinates=[add_plain(a,v),add_plain(a,scale_plain(v,-1)),b,
                 add_plain(c,v),add_plain(c,scale_plain(v,-1)),d]
    qx=add_plain(*(mul_plain(coordinates[i],coordinates[j]) for i,j in [(0,1),(0,2),(1,2)]))
    qy=add_plain(*(mul_plain(coordinates[i],coordinates[j]) for i,j in [(3,4),(3,5),(4,5)]))
    F=add_plain(*(power_plain(z,6) for z in coordinates),
        scale_plain(mul_plain(power_plain(qx,2),qy),Q(5,7)),
        scale_plain(mul_plain(qx,power_plain(qy,2)),Q(10,7)))
    assert all(e[4]%2==0 for e in F)
    Graw={e[:4]+(e[4]//2,):c for e,c in F.items()}
    leading=Graw[(0,0,0,0,3)]
    assert leading==Q(13,7)
    G=scale_plain(Graw,1/leading)
    assert G[(0,0,0,0,3)]==1
    assert all(sum(e[:4])+2*e[4]==6 for e in G)
    return Graw,G

# Coefficient ring: rational polynomials in the 47 contact/point coordinates.
# A coefficient monomial is a sorted tuple of repeated coordinate indices.
def cadd(*polys):
    out=defaultdict(Q)
    for p in polys:
        for e,c in p.items():out[e]+=c
    return {e:c for e,c in out.items() if c}
def cmul(p,q):
    out=defaultdict(Q)
    for e,c in p.items():
        for f,d in q.items():out[tuple(sorted(e+f))]+=c*d
    return {e:c for e,c in out.items() if c}
def cscale(p,q):return {e:c*q for e,c in p.items() if c*q}
def outer_add(*polys):
    out={}
    for p in polys:
        for e,c in p.items():out[e]=cadd(out.get(e,{}),c)
    return {e:c for e,c in out.items() if c}
def outer_mul(p,q):
    out={}
    for e,c in p.items():
        for f,d in q.items():
            m=tuple(a+b for a,b in zip(e,f))
            out[m]=cadd(out.get(m,{}),cmul(c,d))
    return {e:c for e,c in out.items() if c}
def outer_scale(p,q):return {e:cscale(c,q) for e,c in p.items() if cscale(c,q)}
def outer_power(p,n):
    out={(0,0,0,0):{():Q(1)}}
    for _ in range(n):out=outer_mul(out,p)
    return out
def unknown_form(basis,offset):return {e:{(offset+i,):Q(1)} for i,e in enumerate(basis)}
def moving_point(poly):
    out=defaultdict(Q)
    for e,c in poly.items():
        for m,v in c.items():out[tuple(sorted(m+(45,)*e[1]+(46,)*(e[2]+e[3])))]+=v
    return {m:c for m,c in out.items() if c}

def reconstruct_equations():
    Graw,G=original_target()
    q1=unknown_form(QBASE,0)
    q2=outer_add({AB:{():Q(1)}},unknown_form(QBASE,5))
    A=unknown_form(ABASE,10);B=unknown_form(BBASE,18);g2=unknown_form(M4,26)
    substituted={}
    for e,c in G.items():
        term=outer_mul({e[:4]:{():c}},outer_power(outer_scale(q1,-1),e[4]))
        substituted=outer_add(substituted,term)
    # Negative residual, matching the witness's inverse orientation:
    # A²-B²+Q2*g2-G(a,b,c,d,-Q1).
    residual=outer_add(outer_mul(A,A),outer_scale(outer_mul(B,B),-1),
                       outer_mul(q2,g2),outer_scale(substituted,-1))
    assert set(residual)<=set(M6)
    equations=[residual.get(e,{}) for e in M6]+[moving_point(q2),moving_point(outer_add(A,B))]
    assert len(equations)==46
    return Graw,G,equations

def derivative(p,j):
    out=defaultdict(Q)
    for m,c in p.items():
        k=m.count(j)
        if k:
            reduced=list(m);reduced.remove(j)
            out[tuple(reduced)]+=k*c
    return {m:c for m,c in out.items() if c}

# Independent Gaussian-rational arithmetic represented as pairs of Fraction.
ZERO=(Q(0),Q(0))
def gadd(a,b):return (a[0]+b[0],a[1]+b[1])
def gsub(a,b):return (a[0]-b[0],a[1]-b[1])
def gmul(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def gnorm(a):return abs(a[0])+abs(a[1])
def decode(a):return (Q(a[0]),Q(a[1]))
def evaluate(p,x):
    out=ZERO
    for m,c in p.items():
        value=(c,Q(0))
        for j in m:value=gmul(value,x[j])
        out=gadd(out,value)
    return out
def dot(a,b):
    out=ZERO
    for x,y in zip(a,b):out=gadd(out,gmul(x,y))
    return out
def matnorm(A):return max(sum(gnorm(x) for x in row) for row in A)
def defect(B,J):
    columns=list(zip(*J));rows=[]
    for i,row in enumerate(B):
        rows.append(sum(gnorm(gsub((Q(int(i==j)),Q(0)),dot(row,col))) for j,col in enumerate(columns)))
    return max(rows)
def power_upper(q):
    assert q>=0
    if q==0:return '0'
    k=0;v=Q(1)
    if q<=1:
        while q<=v/10:k-=1;v/=10
    else:
        while q>v:k+=1;v*=10
    assert q<=v
    return '10^'+str(k)
def canonical(polys):
    return [[{'monomial':list(m),'coefficient':str(c)} for m,c in sorted(p.items())] for p in polys]

def main():
    start=time.monotonic()
    witness_path=HERE/'contact_exact_ball.json'
    data=json.loads(witness_path.read_text())
    assert data['lambda']=='1' and data['s']=='1' and data['rho0']=='1/4'
    active=list(range(1,47));incidence=list(range(45))+[46]
    assert data['active_columns']==active and data['incidence_columns']==incidence
    x=list(map(decode,data['center']))
    B=[[decode(z) for z in row] for row in data['inverse']]
    Bi=[[decode(z) for z in row] for row in data['incidence_inverse']]
    assert len(x)==47 and x[0]==(Q(1,4),Q(0))
    assert len(B)==len(Bi)==46 and all(len(row)==46 for row in B+Bi)
    radius=Q(data['radius']);assert radius>0
    Graw,G,polys=reconstruct_equations()
    eqdata=canonical(polys)
    eqtext=json.dumps(eqdata,separators=(',',':'))
    (HERE/'contact_lift_independent_equations.json').write_text(eqtext+'\n')
    derivs=[[derivative(p,j) for j in range(47)] for p in polys]
    values=[evaluate(p,x) for p in polys]
    J=[[evaluate(row[j],x) for j in active] for row in derivs]
    Ji=[[evaluate(row[j],x) for j in incidence] for row in derivs]
    print('Independent original-target equations and exact Jacobians constructed.',flush=True)
    eta=max(gnorm(dot(row,values)) for row in B)
    z=defect(B,J);zi=defect(Bi,Ji)
    bnorm=matnorm(B);binorm=matnorm(Bi)
    M=max(1,math.ceil(max(map(gnorm,x))+radius))
    hessian=max(sum(abs(c)*len(m)*(len(m)-1)*M**max(0,len(m)-2) for m,c in p.items()) for p in polys)
    contraction=z+bnorm*hessian*radius
    selfmap=eta+contraction*radius
    incidence_defect=zi+binorm*hessian*radius
    assert z<1 and contraction<1 and selfmap<radius and incidence_defect<1
    product_mu=gmul(x[5],x[6])
    product_error=(gnorm(x[5])+gnorm(x[6]))*radius+radius**2
    chart_margins=[abs(1-k*product_mu[0])-k*product_error for k in [1,2,3]]
    assert all(m>0 for m in chart_margins)
    assert gnorm(x[46])>radius
    assert gnorm(x[45])>radius
    # Numerical ranks are supplementary information only; the exact inverse
    # defects above, not these floating computations, certify nonsingularity.
    complex_array=lambda A:np.array([[complex(float(z[0]),float(z[1])) for z in row] for row in A])
    sj=np.linalg.svd(complex_array(J),compute_uv=False)
    si=np.linalg.svd(complex_array(Ji),compute_uv=False)
    receipt={'status':'PASS','target_reconstructed_from_original_six_coordinates':True,
      'imports_circuit_or_homotopy_generator':False,
      'original_cubic_leading_coefficient':'13/7','fixed_lambda':'1','fixed_s':'1','fixed_rho0':'1/4',
      'equation_count':46,'ambient_coordinate_count':47,'active_coordinate_count':46,
      'radius':str(radius),'eta_upper_bound':power_upper(eta),
      'root_center_inverse_defect_upper_bound':power_upper(z),
      'incidence_center_inverse_defect_upper_bound':power_upper(zi),
      'root_inverse_norm_upper_bound':power_upper(bnorm),'incidence_inverse_norm_upper_bound':power_upper(binorm),
      'coordinate_bound':M,'hessian_bound':str(hessian),
      'contraction_upper_bound':power_upper(contraction),'self_mapping_strict':True,
      'incidence_defect_upper_bound':power_upper(incidence_defect),'incidence_invertible_throughout_ball':True,
      'all_three_chart_factors_nonzero_throughout_ball':True,'alpha_nonzero_throughout_ball':True,
      'supplementary_numerical_root_min_singular_value':float(sj[-1]),
      'supplementary_numerical_incidence_min_singular_value':float(si[-1]),
      'witness_sha256':hashlib.sha256(witness_path.read_bytes()).hexdigest(),
      'independent_equations_sha256':hashlib.sha256(eqtext.encode()).hexdigest(),
      'audit_source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'seconds':round(time.monotonic()-start,3),
      'scope':'Independent exact rational audit of a complex contact incidence and nonsingular moving-incidence Jacobian. Classical Banach and implicit-function reasoning; not yet Lean, no source trace, no final certificate.'}
    (HERE/'contact_lift_independent_audit_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2),flush=True)

if __name__=='__main__':main()
