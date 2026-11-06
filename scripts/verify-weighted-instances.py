#!/usr/bin/env python3
"""Check the two exact applications of the weighted two-reflection theorem.

Uses scripts/requirements-content.txt and reads the protected instance records.
This verifies polynomial hypotheses and smooth good reduction, not the Hodge
theorem or a Lean certificate. No files are written.
"""

from pathlib import Path

import sympy as sp
import yaml

from polynomials import exact_polynomial


ROOT = Path(__file__).resolve().parents[1]
Z = sp.symbols("X0 X1 X2 Y0 Y1 Y2")
X0, X1, X2, Y0, Y1, Y2 = Z
FERMAT = sum(z**6 for z in Z)


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def same(left, right):
    return sp.Poly(left - right, *Z, domain=sp.QQ).is_zero


def reduction(poly, prime):
    return {
        exponent: residue
        for exponent, coefficient in sp.Poly(poly, *Z, domain=sp.QQ).terms()
        if (residue := int(coefficient.p) * pow(int(coefficient.q), -1, prime) % prime)
    }


def record(instance):
    data = yaml.safe_load((ROOT / "data" / instance / "instance.rec").read_text())
    require(data["id"] == instance and data["q"] == 1, instance + ": protected target")
    F, A = (exact_polynomial(data[name], Z) for name in ("F", "A"))
    for name, poly in (("F", F), ("A", A)):
        p = sp.Poly(poly, *Z, domain=sp.QQ)
        require(not p.is_zero and p.is_homogeneous and p.total_degree() == 6,
                instance + ": degree of " + name)
    tau = {Y0: -Y0, Y1: -Y1, Y2: -Y2}
    require(same(F.xreplace(tau), F), instance + ": invariant equation")
    require(same(A.xreplace(tau), -A), instance + ": invariant residue")
    require(reduction(F, 5) == reduction(FERMAT, 5), instance + ": Fermat reduction")
    # In characteristic five the partials are exactly Zi^5, with no common
    # projective zero. Properness of the relative singular locus then gives
    # smoothness of the characteristic-zero projective hypersurface.
    for z in Z:
        require(reduction(sp.diff(F, z), 5) == reduction(z**5, 5),
                instance + ": smooth-reduction partial " + str(z))
    return F, A


def main():
    instance = "four-plus-two-residual"
    F, A = record(instance)
    binary = X2**6 + sp.Rational(15, 7)*X2**4*Y2**2 + sp.Rational(10, 7)*X2**2*Y2**4 + Y2**6
    require(same(F, F.subs({X2: 0, Y2: 0}) + binary), instance + ": four-plus-two split")
    require(same(A, X0**3 * Y0**3), instance + ": exact numerator")
    for z in (X2, Y2):
        require(same(F.xreplace({z: -z}), F), instance + ": reflection in " + str(z))
        require(same(A.xreplace({z: -z}), A), instance + ": negative residue character")
    print(instance + ": exact split, both reflections, residual target, and smooth reduction verified")

    instance = "symmetric-sextic-residual"
    F, A = record(instance)
    QX = X0*X1 + X0*X2 + X1*X2
    QY = Y0*Y1 + Y0*Y2 + Y1*Y2
    require(same(F, FERMAT + sp.Rational(5, 7)*QX**2*QY + sp.Rational(10, 7)*QX*QY**2),
            instance + ": compact equation")
    require(same(A, sp.prod(Z)), instance + ": exact numerator")
    for i, j in ((0, 1), (3, 4)):
        swap = {Z[i]: Z[j], Z[j]: Z[i]}
        require(same(F.xreplace(swap), F), instance + ": independent transposition")
        require(same(A.xreplace(swap), A), instance + ": sign residue character")
    a, b, c, d, s, t = sp.symbols("a b c d s t")
    images = (a+s, a-s, b, c+t, c-t, d)
    substitution = dict(zip(Z, images))
    variables = (a, b, c, d, s, t)
    require(sp.Matrix(images).jacobian(variables).det() == 4, instance + ": invertible coordinate change")
    Fnew, Anew = (sp.expand(poly.xreplace(substitution)) for poly in (F, A))
    require(sp.expand(Anew - (a*a-s*s)*b*(c*c-t*t)*d) == 0, instance + ": transformed target")
    for z in (s, t):
        require(sp.expand(Fnew.xreplace({z: -z}) - Fnew) == 0, instance + ": transformed reflection")
        require(sp.expand(Anew.xreplace({z: -z}) - Anew) == 0, instance + ": transformed residue character")
    print(instance + ": compact equation, independent reflections, residual target, and smooth reduction verified")


if __name__ == "__main__":
    main()
