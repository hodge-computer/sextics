#!/usr/bin/env python3
"""Independent exact audit of the invariant degree-six obstruction.

This imports no polynomial routines from invariant_degree6.py.  SymPy's
symbolic differentiation, polynomial division, and rational linear algebra
reconstruct the equations.  The receipt is computational evidence, not Lean.
"""
from pathlib import Path
import hashlib
import itertools
import json
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / "python_deps"))
import sympy as s
from sympy.polys.matrices import DomainMatrix

z = s.symbols("p q r P Q R")
p, q, r, P, Q, R = z
weights = (1, 2, 3, 1, 2, 3)


def decode(entries):
    return s.Poly.from_dict({tuple(e): s.Rational(c) for e, c in entries}, z).as_expr()


def weighted_monomials(degree, parity):
    return [e for e in itertools.product(*(range(degree // w + 1) for w in weights))
            if sum(a * w for a, w in zip(e, weights)) == degree
            and (e[3] + e[5]) % 2 == parity]


def monomial(e):
    return s.prod(t ** a for t, a in zip(z, e))


def poly_dict(a):
    return s.Poly(s.expand(a), z).as_dict()


def matrix(columns):
    polys = [poly_dict(c) for c in columns]
    rows = sorted(set().union(*(a.keys() for a in polys)))
    M = s.Matrix([[a.get(e, 0) for a in polys] for e in rows])
    return rows, M


def rank(M):
    return DomainMatrix.from_Matrix(M).convert_to(s.QQ).rank()


def act(v, f):
    return s.expand(sum(a * s.diff(f, t) for a, t in zip(v, z)))


def discriminant(a, b, c):
    return a*a*b*b - 4*b**3 - 4*a**3*c - 27*c*c + 18*a*b*c


def main():
    first_path = HERE / "degree6_exact_first_equation.json"
    second_path = HERE / "degree6_exact_second_equations.json"
    witness_path = HERE / "degree6_square_obstruction_witnesses.json"
    first = json.loads(first_path.read_text())
    second = json.loads(second_path.read_text())
    witness = json.loads(witness_path.read_text())

    # Derive each invariant-coordinate field from its actual ambient field.
    x = s.symbols("x0:3")
    elementary = (sum(x), x[0]*x[1]+x[0]*x[2]+x[1]*x[2], s.prod(x))
    local = ((3, 2*p, q), (p, 2*q, 3*r),
             (p*p - 2*q, p*q - 3*r, p*r))
    local_divergence = (0, 3, 2*p)
    subst = dict(zip((p, q, r), elementary))
    for k in range(3):
        for j in range(3):
            assert s.expand(sum(xi**k * s.diff(elementary[j], xi) for xi in x)
                            - s.sympify(local[k][j]).subs(subst)) == 0
        assert s.expand(sum(s.diff(xi**k, xi) for xi in x)
                        - s.sympify(local_divergence[k]).subs(subst)) == 0

    newton = p**6 - 6*p**4*q + 9*p*p*q*q - 2*q**3 + 6*p**3*r - 12*p*q*r + 3*r*r
    assert s.expand(newton.subs(subst) - sum(xi**6 for xi in x)) == 0
    G = s.expand(7*(newton + newton.xreplace({p:P, q:Q, r:R})) + 5*q*q*Q + 10*q*Q*Q)
    A = r*R
    assert s.expand(G-decode(first["F"])) == 0
    assert A == decode(first["A"])

    # Enumerate the whole free equivariant module with the required parity.
    basis = []
    descriptors = []
    divs = []
    for block in range(2):
        rename = {} if block == 0 else {p:P, q:Q, r:R}
        for k in range(3):
            vk = [s.S(0)] * 6
            vk[3*block:3*block+3] = [s.sympify(a).xreplace(rename) for a in local[k]]
            dk = s.sympify(local_divergence[k]).xreplace(rename)
            for e in weighted_monomials(7-k, 1 if block == 0 else k % 2):
                m = monomial(e)
                basis.append([s.expand(m*a) for a in vk])
                divs.append(s.expand(act(vk, m) + m*dk))
                descriptors.append({"block":block, "power":k, "exponent":list(e)})
    assert descriptors == first["numerator_basis"]
    denominators = [monomial(e) for e in weighted_monomials(6, 0)]
    _, first_matrix = matrix([act(v, G) for v in basis] + [-A*d for d in denominators])
    first_rank = rank(first_matrix)
    assert len(basis) == 142 and len(denominators) == 30
    assert first_rank == first["normal_rank"] == 158
    assert first_matrix.rows == first["normal_rows"] == 184

    # Check the supplied divergence using the change-of-volume formula,
    # independently of E_k's stored divergence.  J^2 is the discriminant.
    delta = discriminant(p,q,r)*discriminant(P,Q,R)
    E = s.Matrix.hstack(*(s.Matrix(v) for v in local))
    E_inverse = E.inv()

    def check_field(packet, D):
        v = [decode(a) for a in packet["field"]]
        div = decode(packet["div"])
        assert act(v, G) == s.expand(A*D)
        assert s.expand(2*delta*(sum(s.diff(a,t) for a,t in zip(v,z))-div)-act(v,delta)) == 0
        coeffs = []
        for block in range(2):
            inverse = E_inverse if block == 0 else E_inverse.xreplace({p:P,q:Q,r:R})
            fs = inverse*s.Matrix(v[3*block:3*block+3])
            for k, f in enumerate(fs):
                f = s.cancel(f)
                fd = s.Poly(f, z, domain=s.QQ).as_dict()
                allowed = set(weighted_monomials(7-k, 1 if block == 0 else k % 2))
                assert set(fd) <= allowed
                coeffs.extend(fd.get(e, 0) for e in weighted_monomials(7-k, 1 if block == 0 else k % 2))
        for j in range(6):
            assert s.expand(sum(c*b[j] for c,b in zip(coeffs,basis))-v[j]) == 0
        assert s.expand(sum(c*d for c,d in zip(coeffs,divs))-div) == 0
        return (D,v,div,coeffs)

    kernels = [check_field(k, s.S(0)) for k in first["kernelN"]]
    eligible = [check_field(e, decode(e["D"])) for e in first["eligible"]]
    assert len(kernels) == 10 and len(eligible) == 3
    gauge_v = [A*w*t/6 for w,t in zip(weights,z)]
    gauge = {"field": [[[list(e),str(c)] for e,c in poly_dict(v).items()] for v in gauge_v],
             "div": [[list(e),str(c)] for e,c in poly_dict(2*A).items()]}
    gauge_data = check_field(gauge,G)
    solutions = kernels + eligible + [gauge_data]
    dmons = weighted_monomials(6,0)
    vectors = [a[3] + [poly_dict(a[0]).get(e,0) for e in dmons] for a in solutions]
    solution_rank = rank(s.Matrix.hstack(*(s.Matrix(v) for v in vectors)))
    assert solution_rank == 14 == first_matrix.cols-first_rank
    assert first_matrix*s.Matrix.hstack(*(s.Matrix(v) for v in vectors)) == s.zeros(first_matrix.rows,14)

    # An intrinsic description of all eligible denominators.
    directions = []
    for block in range(2):
        rename = {} if block == 0 else {p:P,q:Q,r:R}
        for k in (0,1):
            vk = [s.S(0)]*6
            vk[3*block:3*block+3] = [s.sympify(a).xreplace(rename) for a in local[k]]
            directions.append(s.expand((z[3*block] if k == 0 else 1)*act(vk,G)))
    _, direction_matrix = matrix(directions)
    _, extended_direction_matrix = matrix(directions + [a[0] for a in eligible]+[G])
    assert rank(direction_matrix) == rank(extended_direction_matrix) == 4

    # Independently reconstruct all quadratic obstruction coefficients.
    def bilinear(D,N):
        return s.Poly(s.rem(s.expand(D*N[2]-act(N[1],D)),G,r),z,domain=s.QQ).as_expr()
    columns = []
    types = []
    for i, ni in enumerate(eligible):
        for j in range(i,len(eligible)):
            c = bilinear(ni[0],eligible[j])
            if i != j:
                c += bilinear(eligible[j][0],ni)
            columns.append(s.expand(c)); types.append(["b",i,j])
        for j,n in enumerate(kernels):
            columns.append(bilinear(ni[0],n)); types.append(["c",i,j])
    assert types == second["types"]
    rows, M = matrix(columns)
    rr, pivots = DomainMatrix.from_Matrix(M).convert_to(s.QQ).rref()
    rr = rr.to_Matrix()
    reconstructed = [[[j,str(rr[i,j])] for j in range(rr.cols) if rr[i,j]] for i in range(len(pivots))]
    assert reconstructed == second["equations"]
    assert (len(rows),len(pivots)) == (161,30)
    for w in witness["witnesses"]:
        j = types.index(["b",w["parameter"],w["parameter"]])
        coeffs = {tuple(e):s.Rational(c) for e,c in w["coefficient_weights"]}
        result = s.Matrix(1,len(rows),lambda _,i:coeffs.get(rows[i],0))*M
        assert result == s.Matrix(1,M.cols,lambda _,i: int(i == j))

    receipt = {
        "status":"PASS",
        "method":"Independent SymPy symbolic differentiation, rational polynomial division and QQ linear algebra; no upstream polynomial routines imported.",
        "scope":"Exact computational audit, not a formal Lean theorem. Completeness uses the free equivariant module argument documented in norm_support_scope.txt.",
        "first_equation":{"numerator_columns":142,"denominator_columns":30,"rows":184,"rank":158,
                          "verified_solution_basis_dimension":14,"pure_numerator_kernel":10,
                          "eligible_denominators_mod_G":3},
        "ambient_divergences":"All 14 solution fields independently checked by the discriminant Jacobian volume formula, and by reconstructed E_k coefficients.",
        "eligible_denominator_space":"span(p E_X0(G), E_X1(G), P E_Y0(G), E_Y1(G)); dimension 4 includes G.",
        "second_equation":{"coefficient_rows":161,"quadratic_terms":36,"rank":30,
                           "all_three_square_row_witnesses_verified":True},
        "conclusion":"Every S3(X) x S3(Y)-invariant, Y-even homogeneous degree-six denominator satisfying the normalized certificate equations over a characteristic-zero field is a scalar multiple of G=7F. Such a denominator is illegal.",
        "limitations":"Does not exclude general noninvariant denominators or denominators of larger degree. This is an obstruction, not a certificate.",
        "inputs":{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (first_path,second_path,witness_path)}
    }
    (HERE/"independent_degree6_audit.json").write_text(json.dumps(receipt,indent=2)+"\n")
    print(json.dumps(receipt,indent=2))


if __name__ == "__main__":
    main()
