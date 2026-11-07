#!/usr/bin/env python3
"""A bounded obstruction to one structured norm-contact candidate.

Checks smoothness modulo 11 for the restriction to QX=QY=0 at lambda=1.
This is not a certificate obstruction and does not concern other quadrics,
other denominators, or powers of a fixed denominator.
"""
import json
import sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/"python_deps"))
import sympy as S
z,h=S.symbols("z h")
a=(1-z)*(1-h)
b=h+z
c=(1+z)*(1-h)
d=h-z
w=S.expand(a*a+2*a*b)
assert S.expand(c*c+2*c*d-w)==0
FX=b**6+2*a**6+30*a**4*w+30*a*a*w*w+2*w**3
FY=d**6+2*c**6+30*c**4*w+30*c*c*w*w+2*w**3
f=S.Poly(S.expand(FX+FY),z,h)
assert (f.degree(z),f.degree(h))==(6,6)
charts=[]
for iz,ih in [(0,0),(1,0),(0,1),(1,1)]:
    expr=sum(v*z**(6-i if iz else i)*h**(6-j if ih else j)
             for (i,j),v in f.terms())
    gb=S.groebner([expr,S.diff(expr,z),S.diff(expr,h)],z,h,modulus=11)
    assert list(gb)==[1]
    charts.append({"inverse_z":bool(iz),"inverse_h":bool(ih),"jacobian_groebner_basis":[1]})
receipt={
    "candidate_quadrics":["a^2+2*a*b-w","c^2+2*c*d-w"],
    "pencil_parameter":1,
    "quadric_parametrization":{"a":str(a),"b":str(b),"c":str(c),"d":str(d),"w":str(w)},
    "restricted_polynomial":str(f.as_expr()),
    "bidegree":[6,6],"prime":11,"charts":charts,
    "classical_implication":"The proper (6,6) divisor has smooth reduction, hence is smooth in characteristic zero. A smooth (6,6) divisor is connected and absolutely irreducible. It cannot be the product of two (3,3) sections. Smoothness is open in lambda, so this excludes QX,QY as a norm-contact pair for generic lambda.",
    "scope":"Only this pair of quadrics. Not a Lean theorem, no general certificate nonexistence claim, and no conclusion about other denominators or denominator powers."
}
(HERE/"qxy_norm_contact_obstruction.json").write_text(json.dumps(receipt,indent=2)+"\n")
print(json.dumps({k:v for k,v in receipt.items() if k!="restricted_polynomial"},indent=2))
