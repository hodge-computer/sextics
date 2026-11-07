#!/usr/bin/env python3
"""Exact small algebra behind the U/V support and cubic-denominator analysis.

This checks polynomial identities and Bézout certificates.  The geometric
support argument using these identities is separately explained, not claimed
as a Lean theorem or as a newly constructed certificate.
"""
from pathlib import Path
from itertools import product
from math import comb
import json
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / "python_deps"))
import sympy as s


def exponents(n):
    if n == 0:
        return [(0,)*6]
    def rec(total, length):
        if length == 1:
            yield (total,)
        else:
            for i in range(total+1):
                for e in rec(total-i,length-1):
                    yield (i,)+e
    return list(rec(n,6))


def main():
    z = s.symbols("z0:3")
    x = s.symbols("x0:3")
    t,u,a,b,p,q,r,c,T = s.symbols("t u a b p q r c T")
    Qz = z[0]*z[1]+z[0]*z[2]+z[1]*z[2]
    Qx = x[0]*x[1]+x[0]*x[2]+x[1]*x[2]
    U = sum(v**6 for v in x)
    V = sum(v**6 for v in z)
    W = V+a*Qz*u**4+b*Qz**2*u**2
    assert s.expand(s.diff(W,u)-2*u*Qz*(2*a*u*u+b*Qz)) == 0
    for zi in z:
        assert s.expand(s.diff(W,zi).subs(u,1) -
                        (6*zi**5+(a+2*b*Qz)*(sum(z)-zi))) == 0

    cubic = T**3-p*T*T+q*T-r
    quintic = 6*T**5+c*(p-T)
    remainder = 6*(p**3-2*p*q+r)*T*T + (6*(-p*p*q+q*q+p*r)-c)*T + 6*(p*p-q)*r+c*p
    assert s.rem(quintic,cubic,T).expand() == remainder.expand()
    assert s.factor(remainder.coeff(T,1).subs({q:0,r:-p**3})) == -c-6*p**4
    assert s.factor(remainder.subs(T,0).subs({q:0,r:-p**3,c:-6*p**4})) == -12*p**5

    # Distinct-root elimination at q=-2a/b, c=-3a.
    h, k = s.symbols("h k")
    f1 = h*h-h-1-k
    f2 = -h*h+3*h-2-k
    assert s.resultant(f1,f2,h).factor() == 4*k*k+4*k-1
    assert s.factor((4*k*k+4*k-1).subs(k,b*b/(8*a))*16*a*a) == b**4+8*a*b*b-16*a*a

    # Repeated-root elimination, with two coordinates x and the third t*x.
    f = t**6+t**5-2
    repeated_second = b*b*(1+t)*(1+2*t)**2-8*a
    cases = [
        ("U",s.Rational(5,7),s.Rational(10,7),
         20*t**3+40*t*t+25*t-9,
         -57618500*t*t-654961500*t-1116325025,
         2880925*t**5+29867150*t**4+25228870*t**3-30679010*t*t+43262150*t-36822546,
         2564052964),
        ("V",s.Rational(10,7),s.Rational(5,7),
         20*t**3+40*t*t+25*t-107,
         3981739500*t*t+11921555500*t+18432513275,
         -199086975*t**5-396990800*t**4-474863120*t**3-540776240*t*t-448769400*t-967008592,
         66604892794)
    ]
    surface_receipts=[]
    for name,aa,bb,g,S,Tpoly,C in cases:
        ratio=s.cancel(repeated_second.subs({a:aa,b:bb})/g)
        assert not ratio.free_symbols and ratio != 0
        assert s.expand(S*f+Tpoly*g) == C and C != 0
        exceptional1 = bb*bb+8*aa
        exceptional2 = bb**4+8*aa*bb*bb-16*aa*aa
        assert exceptional1 != 0 and exceptional2 != 0
        hessian=s.hessian(W.subs({u:1,a:aa,b:bb}),z).subs(dict.fromkeys(z,0))
        assert hessian.det() == 2*aa**3 != 0
        surface_receipts.append({"support":name,"a":str(aa),"b":str(bb),
            "distinct_root_exceptional_values":[str(exceptional1),str(exceptional2)],
            "repeated_root_f":str(f),"repeated_root_g":str(g),
            "bezout_S":str(S),"bezout_T":str(Tpoly),"bezout_nonzero_constant":C,
            "origin_hessian_determinant":str(hessian.det()),
            "interpretation":"The case analysis in the scope note proves the origin is the sole singular point, an ordinary node."})

    # Exact identity for the rational domination by the curve-surface product.
    Fscaled = u**6*U + t**6*V+a*u**4*t*t*Qx**2*Qz+b*u*u*t**4*Qx*Qz**2
    target = t**6*W
    residual=s.expand(Fscaled-target-u**6*U)
    assert s.rem(residual,t*t-Qx,t).expand() == 0

    # The actual integral sextic reduces to a Fermat polynomial modulo five.
    zz=x+z
    G=7*(U+V)+5*Qx**2*Qz+10*Qx*Qz**2
    for i,zi in enumerate(zz):
        assert s.Poly(s.diff(G,zi)-2*zi**5,zz,modulus=5).is_zero
    degree_receipts=[]
    for d in range(4):
        columns=[]
        for i in range(6):
            for e in exponents(d+1):
                columns.append(tuple(e[j]+(5 if j==i else 0) for j in range(6)))
        for e in exponents(d):
            columns.append(tuple(v+1 for v in e))
        expected=6*comb(d+6,5)+comb(d+5,5)
        assert len(columns)==len(set(columns))==expected
        assert all(sum(e)==d+6 for e in columns)
        det_mod_five=pow(2,6*comb(d+6,5),5)*pow(-1,comb(d+5,5),5)%5
        assert det_mod_five
        degree_receipts.append({"denominator_degree":d,"coefficient_columns":expected,
            "distinct_selected_rows":len(set(columns)),"diagonal_minor_determinant_mod_5":det_mod_five})

    receipt={"status":"PASS","surfaces":surface_receipts,
        "product_map_identity_checked":True,
        "small_denominator_obstruction":degree_receipts,
        "scope":"Exact algebraic identities only. The geometric U/V support obstruction additionally uses resolution, rationality of ordinary surface nodes, projective-space cohomology, pullback of holomorphic forms, and the Gysin description of supported Hodge classes. No primitive or full certificate is asserted."}
    (HERE/"norm_support_audit.json").write_text(json.dumps(receipt,indent=2)+"\n")
    print(json.dumps(receipt,indent=2))


if __name__=="__main__":
    main()
