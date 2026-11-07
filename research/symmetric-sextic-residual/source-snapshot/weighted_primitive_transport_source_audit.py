#!/usr/bin/env python3
"""Independent exact source/Jacobian audit; does not assert primitive existence."""
from pathlib import Path
import hashlib,json
import sympy as s

HERE=Path(__file__).resolve().parent

def main():
    a,lam,b,c,d,v,u=s.symbols('a lambda b c d v u')
    x=[a*(1+v),a*(1-v),a*b,a*(c+lam*v),a*(c-lam*v),a*d]
    coords=[a,lam,b,c,d,v]
    determinant=s.factor(s.Matrix(x).jacobian(coords).det())
    qx=1+2*b-u
    qy=c*c+2*c*d-lam*lam*u
    f=(2+b**6+2*c**6+d**6+30*u+30*u*u+2*u**3+
       30*lam**2*c**4*u+30*lam**4*c*c*u*u+2*lam**6*u**3+
       s.Rational(5,7)*qx*qx*qy+s.Rational(10,7)*qx*qy*qy)
    qX=x[0]*x[1]+x[0]*x[2]+x[1]*x[2]
    qY=x[3]*x[4]+x[3]*x[5]+x[4]*x[5]
    original=sum(z**6 for z in x)+s.Rational(5,7)*qX*qX*qY+s.Rational(10,7)*qX*qY*qY
    p=b*d*(1-u)*(c*c-lam*lam*u)
    checks={
        'jacobian_det_4_a5_v':s.expand(determinant-4*a**5*v)==0,
        'homogeneous_equation_binding':s.Poly(s.expand(original-a**6*f.subs(u,v*v)),*coords).is_zero,
        'homogeneous_numerator_binding':s.Poly(s.expand(s.prod(x)-a**6*p.subs(u,v*v)),*coords).is_zero,
        'ell_leading_coefficient':s.expand(s.Poly(f,u).coeff_monomial(u**3)-
            (14*lam**6-10*lam**4-5*lam**2+14)/7)==0,
    }
    fu,fuu,P,Pu=s.symbols('fu fuu P Pu')
    g=2*v*fu
    source_v=4*P+8*v*v*Pu
    source=4*v*P
    g_v=2*fu+4*v*v*fuu
    rho=2*(fu*Pu-fuu*P)/fu**3
    checks['residue_density_cleared_identity']=s.cancel((source_v*g-source*g_v)/g**2-g*rho)==0
    record={
        'status':'PASS' if all(checks.values()) else 'FAIL',
        'checks':checks,
        'chart_order':['a','lambda','b','c','d','v'],
        'jacobian_det':str(determinant),
        'ambient_volume_pullback':'4*a^5*v da wedge dlambda wedge db wedge dc wedge dd wedge dv',
        'projective_volume_pullback':'4*a^6*v dlambda wedge db wedge dc wedge dd wedge dv',
        'relative_primitive_needed':'sum E_{b,c,d}(beta_i) = 2*(f_u*P_u-f_uu*P)/f_u^3',
        'source_hashes':{
            name:hashlib.sha256((HERE/name).read_bytes()).hexdigest()
            for name in ['WeightedPrimitiveTransportCore.lean','WeightedPrimitiveTransport.lean',
                         'SymmetricAffineJacobian.lean']},
        'scope':'Independent exact polynomial/source audit, not a Lean kernel replay or proof that a relative primitive exists.',
    }
    (HERE/'weighted_primitive_transport_source_audit.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record,indent=2))
    if record['status']!='PASS':raise SystemExit(1)

if __name__=='__main__':main()
