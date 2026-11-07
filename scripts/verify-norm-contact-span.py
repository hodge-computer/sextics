#!/usr/bin/env python3
"""Reconstruct the book's smooth full-span norm-contact witness.

Python 3.9+ and NumPy; no witness files, extra packages, or network required.
Run: python3 scripts/verify-norm-contact-span.py
Pass --output PATH to save the reconstructed finite-arithmetic receipt.

The maintained witness comes from a line on a cubic surface and a smooth
contact curve.  All main calculations are exact modulo 37.  A simple line
root, unit pivot minors, and the geometric normal-rank bound in Chapter 3B
lift the result to characteristic zero.  The weighted equation is fixed
throughout the coefficient recurrence.

The coefficient-map, presentation-gauge, and Artinian-residue infrastructure
is retained from the earlier nodal computation.  Generic helper APIs remain
available for the published research scripts that import this module; the
superseded nodal branch itself is no longer a maintained witness.
"""
from functools import lru_cache
from itertools import permutations, product
from pathlib import Path
from fractions import Fraction
import argparse
import json
import time
import numpy as np

P, NONSQUARE = 37, 2
assert pow(NONSQUARE, (P-1)//2, P) == P-1
blocks = [(2, 0), (2, 0), (4, 0), (4, 0), (3, 0), (3, 1)]


@lru_cache(None)
def monomials(degree, parity=None):
    return tuple(sorted(e+(u,)
                 for e in product(range(degree+1), repeat=4)
                 for u in range(degree//2+1)
                 if sum(e)+2*u == degree
                 and (parity is None or (e[2]+e[3]) % 2 == parity)))


def mul(a, b):
    a, b = np.asarray(a), np.asarray(b)
    return np.stack(((a[..., 0]*b[..., 0] +
                      NONSQUARE*a[..., 1]*b[..., 1]) % P,
                     (a[..., 0]*b[..., 1] +
                      a[..., 1]*b[..., 0]) % P), axis=-1)


def inv(a):
    a = np.asarray(a)
    denominator = pow(int(a[0]*a[0]-NONSQUARE*a[1]*a[1]) % P, -1, P)
    return np.array([a[0]*denominator % P,
                     -a[1]*denominator % P], dtype=np.int64)


def matmul(a, b):
    """Matrix multiplication over the quadratic field."""
    return np.stack(((a[..., 0] @ b[..., 0] +
                      NONSQUARE*(a[..., 1] @ b[..., 1])) % P,
                     (a[..., 0] @ b[..., 1] +
                      a[..., 1] @ b[..., 0]) % P), axis=-1)


def base_rref(matrix):
    a = np.array(matrix, dtype=np.int64, copy=True) % P
    rank, pivots = 0, []
    for j in range(a.shape[1]):
        choices = np.flatnonzero(a[rank:, j])
        if not len(choices):
            continue
        k = rank+int(choices[0])
        a[[rank, k]] = a[[k, rank]]
        a[rank] = a[rank]*pow(int(a[rank, j]), -1, P) % P
        coeff = a[:, j].copy()
        coeff[rank] = 0
        a = (a-coeff[:, None]*a[rank]) % P
        pivots.append(j)
        rank += 1
        if rank == len(a):
            break
    return a[:rank], pivots


def base_inverse(matrix):
    n = len(matrix)
    augmented = np.concatenate(
        (np.asarray(matrix, dtype=np.int64), np.eye(n, dtype=np.int64)),
        axis=1)
    r, pivots = base_rref(augmented)
    assert pivots[:n] == list(range(n))
    assert np.array_equal(r[:, :n], np.eye(n, dtype=np.int64))
    return r[:, n:]


def extension_rank(matrix):
    """Rank over the configured quadratic field, and row/column pivots."""
    a = np.array(matrix, dtype=np.int64, copy=True) % P
    row_order = list(range(len(a)))
    rank, columns = 0, []
    for j in range(a.shape[1]):
        choices = np.flatnonzero(np.any(a[rank:, j], axis=-1))
        if not len(choices):
            continue
        k = rank+int(choices[0])
        a[[rank, k]] = a[[k, rank]]
        row_order[rank], row_order[k] = row_order[k], row_order[rank]
        a[rank] = mul(a[rank], inv(a[rank, j]))
        if rank+1 < len(a):
            a[rank+1:] = (a[rank+1:] -
                          mul(a[rank+1:, j, None, :], a[rank])) % P
        columns.append(j)
        rank += 1
        if rank == len(a):
            break
    return rank, row_order[:rank], columns


def extension_determinant(matrix):
    a = np.array(matrix, dtype=np.int64, copy=True) % P
    result = np.array([1, 0], dtype=np.int64)
    for j in range(len(a)):
        choices = np.flatnonzero(np.any(a[j:, j], axis=-1))
        if not len(choices):
            return [0, 0]
        k = j+int(choices[0])
        if j != k:
            a[[j, k]] = a[[k, j]]
            result = -result % P
        result = mul(result, a[j, j])
        for i in range(j+1, len(a)):
            factor = mul(a[i, j], inv(a[j, j]))
            a[i] = (a[i]-mul(factor, a[j])) % P
    return result.tolist()


parameter_bases = [monomials(d, parity) for d, parity in blocks]
offsets = np.cumsum([0]+[len(b) for b in parameter_bases]).tolist()
assert offsets[-1] == 90
plus_basis, minus_basis = monomials(6, 0), monomials(6, 1)
assert (len(plus_basis), len(minus_basis)) == (70, 60)


def encode(polys):
    ans = np.zeros(90, dtype=np.int64)
    for i, f in enumerate(polys):
        for j, e in enumerate(parameter_bases[i]):
            ans[offsets[i]+j] = f.get(e, 0) % P
    return ans


def decode(v):
    return [{e: int(v[offsets[i]+j]) % P
             for j, e in enumerate(parameter_bases[i])
             if v[offsets[i]+j] % P}
            for i in range(6)]


def poly_add(f, g, scalar=1, prime=P):
    h = f.copy()
    for e, c in g.items():
        coefficient = h.get(e, 0)+scalar*c
        h[e] = coefficient if prime is None else coefficient % prime
    return {e: c for e, c in h.items() if c}


def poly_mul(f, g, prime=P):
    h = {}
    for e, c in f.items():
        for m, d in g.items():
            n = tuple(x+y for x, y in zip(e, m))
            coefficient = h.get(n, 0)+c*d
            h[n] = coefficient if prime is None else coefficient % prime
    return {e: c for e, c in h.items() if c}


# Sparse quadratic coefficient map.  The bilinear map is not symmetrized;
# its value at (z,z) is exactly Phi(z).
plus_index = {e: j for j, e in enumerate(plus_basis)}
term_i, term_j, term_row, term_sign = [], [], [], []
for b1, b2, sign in [(0, 2, 1), (1, 3, 1), (4, 4, 1), (5, 5, -1)]:
    for i, e in enumerate(parameter_bases[b1]):
        for j, m in enumerate(parameter_bases[b2]):
            term_i.append(offsets[b1]+i)
            term_j.append(offsets[b2]+j)
            term_row.append(plus_index[tuple(x+y for x, y in zip(e, m))])
            term_sign.append(sign)
term_i, term_j, term_row, term_sign = [
    np.array(a, dtype=np.int64)
    for a in (term_i, term_j, term_row, term_sign)]


def quadratic(v, w):
    out = np.zeros((70, 2), dtype=np.int64)
    np.add.at(out, term_row,
              term_sign[:, None]*mul(v[term_i], w[term_j]))
    return out % P


def differential(z):
    out = np.zeros((70, 90), dtype=np.int64)
    np.add.at(out, (term_row, term_i), term_sign*z[term_j])
    np.add.at(out, (term_row, term_j), term_sign*z[term_i])
    return out % P


# I_6^- matrix columns: each defining form times monomials of complementary
# degree and character.  Its generic cokernel is the normal obstruction.
minus_index = {e: j for j, e in enumerate(minus_basis)}
ideal_rows, ideal_cols, ideal_parameters = [], [], []
column_count = 0
for b, (degree, parity) in enumerate(blocks):
    for m in monomials(6-degree, 1-parity):
        for j, e in enumerate(parameter_bases[b]):
            ideal_rows.append(minus_index[tuple(x+y for x, y in zip(e, m))])
            ideal_cols.append(column_count)
            ideal_parameters.append(offsets[b]+j)
        column_count += 1
assert column_count == 72
ideal_rows, ideal_cols, ideal_parameters = [
    np.array(a, dtype=np.int64)
    for a in (ideal_rows, ideal_cols, ideal_parameters)]


def ideal_matrix(z):
    out = np.zeros((60, 72, 2), dtype=np.int64)
    out[ideal_rows, ideal_cols] = z[ideal_parameters]
    return out


def phi_polynomials(forms, prime=P):
    f1, f2, g1, g2, A, B = forms
    return poly_add(
        poly_add(poly_mul(f1, g1, prime), poly_mul(f2, g2, prime),
                 prime=prime),
        poly_add(poly_mul(A, A, prime), poly_mul(B, B, prime),
                 -1, prime),
        prime=prime)


def base_determinant(matrix):
    ext = np.stack((matrix, np.zeros_like(matrix)), axis=-1)
    determinant = extension_determinant(ext)
    assert determinant[1] == 0
    return determinant[0]


def base_receipt(matrix):
    _, columns = base_rref(matrix)
    _, rows = base_rref(matrix[:, columns].T)
    assert len(rows) == len(columns)
    determinant = base_determinant(matrix[np.ix_(rows, columns)])
    assert determinant
    return {
        "rows": matrix.shape[0], "columns": matrix.shape[1],
        "rank": len(columns), "minor_rows": rows,
        "minor_columns": columns, "minor_determinant": determinant,
    }


def nullspace(matrix):
    reduced, pivots = base_rref(matrix)
    answer = []
    for j in range(matrix.shape[1]):
        if j in pivots:
            continue
        vector = np.zeros(matrix.shape[1], dtype=np.int64)
        vector[j] = 1
        vector[pivots] = -reduced[:, j] % P
        answer.append(vector)
    return np.array(answer, dtype=np.int64)


class GradedQuotient:
    def __init__(self, degree, forms, degrees, core_only=False):
        self.basis = [e for e in monomials(degree)
                      if not core_only or e[4] == 0]
        relations = []
        for form, d in zip(forms, degrees):
            for m in monomials(degree-d):
                if core_only and m[4]:
                    continue
                f = poly_mul(form, {m: 1})
                relations.append([f.get(e, 0) for e in self.basis])
        self.rows, self.pivots = base_rref(relations)
        self.free = [j for j in range(len(self.basis))
                     if j not in self.pivots]

    def reduce(self, form):
        vector = np.array([form.get(e, 0) for e in self.basis],
                          dtype=np.int64)
        vector = (vector-vector[self.pivots] @ self.rows) % P
        return vector[self.free]


def gauge_vectors(forms):
    """Infinitesimal changes of presentation of the same embedded curve."""
    f1, f2, g1, g2, A, B = forms
    f, g = [f1, f2], [g1, g2]
    answer = []
    for i in range(2):
        for j in range(2):
            delta = [{} for _ in blocks]
            delta[i] = f[j]
            delta[2+j] = poly_add({}, g[i], -1)
            answer.append(encode(delta))
    for i in range(2):
        for parity, cubic, scalar in [(0, A, -2), (1, B, 2)]:
            for m in monomials(1, parity):
                delta = [{} for _ in blocks]
                delta[4+parity] = poly_mul(f[i], {m: 1})
                delta[2+i] = poly_mul(cubic, {m: scalar})
                answer.append(encode(delta))
    for m in monomials(2, 0):
        delta = [{} for _ in blocks]
        delta[2] = poly_mul(f2, {m: 1})
        delta[3] = poly_mul(f1, {m: -1})
        answer.append(encode(delta))
    return np.array(answer, dtype=np.int64).T


def fixed_jacobian_directions(z0):
    Gcoeff = quadratic(np.stack((z0, np.zeros(90, dtype=np.int64)), axis=-1),
                       np.stack((z0, np.zeros(90, dtype=np.int64)), axis=-1))[:, 0]
    G = {e: int(c) for e, c in zip(plus_basis, Gcoeff) if c}
    cols = []
    for i in range(5):
        deriv = {}
        for e, c in G.items():
            if e[i]:
                m = list(e); m[i] -= 1
                deriv[tuple(m)] = e[i]*c % P
        degree, parity = (1, 1) if i in (0, 1) else (
            (1, 0) if i in (2, 3) else (2, 1))
        for m in monomials(degree, parity):
            f = poly_mul(deriv, {m: 1})
            cols.append([f.get(e, 0) for e in minus_basis])
    result = np.array(cols, dtype=np.int64).T
    assert len(base_rref(result)[1]) == 12
    return result


def rank_receipt(a):
    rank, rows, cols = extension_rank(a)
    minor = a[np.ix_(rows, cols)]
    determinant = extension_determinant(minor)
    return {"rank": rank, "rows": rows, "columns": cols,
            "minor_determinant": determinant}


# The smooth witness.  The constants below are residues of algebraic numbers,
# not literal characteristic-zero line coefficients.  The four line equations
# and their unit Jacobian specify the exact algebraic lift in Chapter 3B.
LINE = (2, -3, -2, 15)
SQRT_MINUS_ONE, SQRT_THREE = 6, 15
REFLECTION_PARAMETER = 1
ZERO_EXPONENT = (0, 0, 0, 0, 0)
ONE = {ZERO_EXPONENT: 1}
VARIABLES = [{tuple(int(i == j) for i in range(5)): 1} for j in range(5)]


def poly_scale(f, scalar, prime=P):
    return poly_add({}, f, scalar, prime)


def poly_sum(terms, prime=P):
    result = {}
    for scalar, form in terms:
        result = poly_add(result, form, scalar, prime)
    return result


def poly_power(f, exponent, prime=P):
    number_of_variables = len(next(iter(f), ZERO_EXPONENT))
    result = {(0,)*number_of_variables: 1}
    for _ in range(exponent):
        result = poly_mul(result, f, prime)
    return result


def poly_derivative(f, variable, prime=P):
    result = {}
    for e, coefficient in f.items():
        if e[variable]:
            m = list(e)
            m[variable] -= 1
            value = e[variable]*coefficient
            result[tuple(m)] = value if prime is None else value % prime
    return {e: c for e, c in result.items() if c}


def poly_evaluate(f, point, prime=P):
    result = 0
    for e, coefficient in f.items():
        term = int(coefficient)
        for x, n in zip(point, e):
            term = term*pow(int(x), n, prime) % prime
        result = (result+term) % prime
    return result


def substitute_u(f, value):
    powers = [poly_power(value, n) for n in range(1+max((e[4] for e in f), default=0))]
    result = {}
    for e, coefficient in f.items():
        result = poly_add(result, poly_mul({e[:4]+(0,): coefficient}, powers[e[4]]))
    return result


def cubic(S, Q, prime=P):
    return poly_sum([
        (-2, poly_power(S, 3, prime)),
        (6, poly_mul(poly_power(S, 2, prime), Q, prime)),
        (-3, poly_mul(S, poly_power(Q, 2, prime), prime)),
        (-2, poly_power(Q, 3, prime)),
    ], prime)


def weighted_equation(prime=P, parameter=REFLECTION_PARAMETER):
    """The weighted sextic and its square completion, over Q or a prime field."""
    a, b, c, d, u = VARIABLES
    power = lambda f, n: poly_power(f, n, prime)
    multiply = lambda f, g: poly_mul(f, g, prime)
    combine = lambda terms: poly_sum(terms, prime)
    sx, sy = combine([(2, a), (1, b)]), combine([(2, c), (1, d)])
    qx = combine([(1, power(a, 2)), (2, multiply(a, b)), (-1, u)])
    qy = combine([(1, power(c, 2)), (2, multiply(c, d)), (-parameter**2, u)])
    rx = combine([(4, power(a, 3)), (3, multiply(power(a, 2), b)),
                  (2, multiply(a, power(b, 2))), (1, power(b, 3)),
                  (1, multiply(combine([(4, a), (1, b)]), u))])
    ry = combine([(4, power(c, 3)), (3, multiply(power(c, 2), d)),
                  (2, multiply(c, power(d, 2))), (1, power(d, 3)),
                  (parameter**2, multiply(combine([(4, c), (1, d)]), u))])
    x6 = combine([(2, power(a, 6)), (30, multiply(power(a, 4), u)),
                  (30, multiply(power(a, 2), power(u, 2))),
                  (2, power(u, 3)), (1, power(b, 6))])
    y6 = combine([(2, power(c, 6)), (30*parameter**2, multiply(power(c, 4), u)),
                  (30*parameter**4, multiply(power(c, 2), power(u, 2))),
                  (2*parameter**6, power(u, 3)), (1, power(d, 6))])
    S, T = power(sx, 2), power(sy, 2)
    assert x6 == combine([(3, power(rx, 2)), (1, cubic(S, qx, prime))])
    assert y6 == combine([(3, power(ry, 2)), (1, cubic(T, qy, prime))])
    coefficient = Fraction(5, 7) if prime is None else 5*pow(7, -1, prime) % prime
    F = combine([(1, x6), (1, y6),
                 (coefficient, multiply(power(qx, 2), qy)),
                 (2*coefficient, multiply(qx, power(qy, 2)))])
    source = multiply(multiply(combine([(1, power(a, 2)), (-1, u)]), b),
                      multiply(combine([(1, power(c, 2)), (-parameter**2, u)]), d))
    return F, source, (S, qx, T, qy, rx, ry)


def line_equation_polynomials():
    """Coefficients of G(S,Q,kS+lQ,nS+mQ), in four line coordinates."""
    variables = [{tuple(int(i == j) for i in range(6)): 1} for j in range(6)]
    k, l, n, m, S, Q = variables
    T = poly_add(poly_mul(k, S), poly_mul(l, Q))
    V = poly_add(poly_mul(n, S), poly_mul(m, Q))
    restriction = poly_sum([
        (1, cubic(S, Q)), (1, cubic(T, V)),
        (5*pow(7, -1, P), poly_mul(poly_power(Q, 2), V)),
        (10*pow(7, -1, P), poly_mul(Q, poly_power(V, 2))),
    ])
    equations = [{} for _ in range(4)]
    for e, coefficient in restriction.items():
        assert e[4]+e[5] == 3
        equations[e[5]][e[:4]] = coefficient
    return equations


def smooth_seed():
    # The identities also hold literally over Q, before modular specialization.
    weighted_equation(prime=None)
    reduced, _, _ = weighted_equation(prime=5)
    assert reduced == {(6, 0, 0, 0, 0): 2, (0, 6, 0, 0, 0): 1,
                       (0, 0, 6, 0, 0): 2, (0, 0, 0, 6, 0): 1,
                       (0, 0, 0, 0, 3): 4}
    F, source, (S, Q, T, V, rx, ry) = weighted_equation()
    k, l, n, m = LINE
    equations = line_equation_polynomials()
    assert all(poly_evaluate(eq, LINE) == 0 for eq in equations)
    jac = np.array([[poly_evaluate(poly_derivative(eq, j), LINE) for j in range(4)]
                    for eq in equations], dtype=np.int64)
    line_det = base_determinant(jac)
    assert line_det == 3
    assert SQRT_MINUS_ONE**2 % P == P-1 and SQRT_THREE**2 % P == 3
    t0, v0 = poly_sum([(k, S), (l, Q)]), poly_sum([(n, S), (m, Q)])
    surface_restriction = poly_sum([
        (1, cubic(S, Q)), (1, cubic(t0, v0)),
        (5*pow(7, -1, P), poly_mul(poly_power(Q, 2), v0)),
        (10*pow(7, -1, P), poly_mul(Q, poly_power(v0, 2))),
    ])
    assert not surface_restriction
    f1, f2 = poly_add(T, t0, -1), poly_add(V, v0, -1)
    g1 = poly_sum([(-2, poly_power(T, 2)), (-2, poly_mul(T, t0)),
                   (-2, poly_power(t0, 2)), (6, poly_mul(poly_add(T, t0), V)),
                   (-3, poly_power(V, 2))])
    g2 = poly_sum([(6, poly_power(t0, 2)), (-3, poly_mul(t0, poly_add(V, v0))),
                   (-2, poly_power(V, 2)), (-2, poly_mul(V, v0)), (-2, poly_power(v0, 2)),
                   (5*pow(7, -1, P), poly_power(Q, 2)),
                   (10*pow(7, -1, P), poly_mul(Q, poly_add(V, v0)))])
    A, B = poly_scale(rx, SQRT_THREE), poly_scale(ry, SQRT_MINUS_ONE*SQRT_THREE)
    forms = [f1, f2, g1, g2, A, B]
    assert phi_polynomials(forms) == F
    h = poly_add(A, B)
    u_coefficient = f1.get((0, 0, 0, 0, 1), 0)
    assert u_coefficient
    value = poly_scale({e: co for e, co in f1.items() if e[4] == 0},
                       -pow(u_coefficient, -1, P))
    q, h3 = substitute_u(f2, value), substitute_u(h, value)
    minors = [poly_add(poly_mul(poly_derivative(q, i), poly_derivative(h3, j)),
                       poly_mul(poly_derivative(q, j), poly_derivative(h3, i)), -1)
              for i in range(4) for j in range(i+1, 4)]
    singular = GradedQuotient(6, [q, h3]+minors, [2]+[3]*7, core_only=True)
    assert len(singular.basis) == 84 and not singular.free
    regular = GradedQuotient(10, [f1, f2, h, g1, g2], [2, 2, 3, 4, 4])
    assert len(regular.basis) == 581 and not regular.free
    u1, u2 = [f.get((0, 0, 0, 0, 1), 0) for f in (f1, f2)]
    ab1, ab2 = [f.get((1, 1, 0, 0, 0), 0) for f in (f1, f2)]
    chart_det = (u1*ab2-u2*ab1) % P
    assert chart_det == 20
    second_quadric = poly_scale(poly_sum([(-u2, f1), (u1, f2)]), pow(chart_det, -1, P))
    product_value = second_quadric.get((2, 0, 0, 0, 0), 0)*second_quadric.get((0, 2, 0, 0, 0), 0) % P
    chart_delta = (1-product_value)*(1-3*product_value)*(1-2*product_value)**3 % P
    assert product_value == 10 and chart_delta == 9
    receipt = {
        "line_residues": [x % P for x in LINE], "line_equation_jacobian_determinant": line_det,
        "sqrt_minus_one_residue": SQRT_MINUS_ONE, "sqrt_three_residue": SQRT_THREE,
        "square_completion_verified_over_Q": True, "norm_presentation_verified": True,
        "smooth_weighted_equation_mod5": "2a^6+b^6+2c^6+d^6+4u^3",
        "curve_singular_ideal_degree": 6, "curve_singular_ideal_rank": 84,
        "regular_sequence_degree": 10, "regular_sequence_rank": 581,
        "intrinsic_chart_pivot_determinant": chart_det,
        "intrinsic_chart_product": product_value, "intrinsic_chart_reduction_denominator": chart_delta,
    }
    return forms, source, receipt


def smooth_slice(forms):
    z0 = encode(forms)
    M = differential(z0)
    incidence = base_receipt(M)
    assert incidence["rank"] == 70 and incidence["minor_determinant"] == 21
    tangents = nullspace(M)
    gauge = gauge_vectors(forms)
    assert tangents.shape == (20, 90) and gauge.shape == (90, 19)
    assert not np.any(M @ gauge % P) and len(base_rref(gauge)[1]) == 19
    chosen = next(j for j, v in enumerate(tangents)
                  if len(base_rref(np.column_stack((gauge, v)))[1]) == 20)
    tangent = tangents[chosen]
    coordinates = np.eye(90, dtype=np.int64)[:, incidence["minor_columns"]]
    transverse_det = base_determinant(np.column_stack((coordinates, tangent, gauge)))
    assert transverse_det == 10
    f1, f2, _, _, A, B = forms
    curve = [f1, f2, poly_add(A, B)]
    q2, q3 = [GradedQuotient(degree, curve, [2, 2, 3]) for degree in (2, 3)]
    delta = decode(tangent)
    velocity = np.concatenate((q2.reduce(delta[0]), q2.reduce(delta[1]),
                               q3.reduce(poly_add(delta[4], delta[5]))))
    assert np.any(velocity)
    receipt = {"incidence_derivative": incidence, "presentation_gauge_rank": 19,
               "essential_kernel_index": chosen, "slice_plus_gauge_determinant": transverse_det,
               "normal_velocity_nonzero": True, "normal_velocity": velocity.tolist()}
    return z0, tangent, coordinates, receipt


def base_quadratic(v, w):
    result = np.zeros(70, dtype=np.int64)
    np.add.at(result, term_row, term_sign*v[term_i]*w[term_j])
    return result % P


def smooth_branch(z0, tangent, coordinates, order):
    inverse = base_inverse(differential(z0) @ coordinates % P)
    coefficients = [z0, tangent]
    for n in range(2, order+1):
        forcing = sum((base_quadratic(coefficients[i], coefficients[n-i])
                       for i in range(1, n)), np.zeros(70, dtype=np.int64)) % P
        coefficients.append(coordinates @ (-inverse @ forcing % P) % P)
    for n in range(1, order+1):
        coefficient = sum((base_quadratic(coefficients[i], coefficients[n-i])
                           for i in range(n+1)), np.zeros(70, dtype=np.int64)) % P
        assert not np.any(coefficient), ("fixed weighted equation", n)
    return coefficients


def base_ideal_matrix(z):
    result = np.zeros((60, 72), dtype=np.int64)
    result[ideal_rows, ideal_cols] = z[ideal_parameters]
    return result


def smooth_obstruction_series(z):
    matrices = [base_ideal_matrix(coefficient) for coefficient in z]
    ideal = base_receipt(matrices[0])
    assert ideal["rank"] == 59 and ideal["minor_determinant"] == 4
    rows, cols = ideal["minor_rows"], ideal["minor_columns"]
    free = next(j for j in range(60) if j not in rows)
    inverse = base_inverse(matrices[0][np.ix_(rows, cols)])
    coefficients = []
    for n in range(len(z)):
        forcing = matrices[n][free, cols].copy()
        for i in range(n):
            forcing = (forcing+coefficients[i][rows] @ matrices[n-i][np.ix_(rows, cols)]) % P
        row = np.zeros(60, dtype=np.int64)
        row[rows] = -forcing @ inverse % P
        if n == 0:
            row[free] = 1
        coefficients.append(row)
        total = sum((coefficients[i] @ matrices[n-i] for i in range(n+1)),
                    np.zeros(72, dtype=np.int64)) % P
        assert not np.any(total), ("all 72 normal ideal columns", n)
    ideal["normalization_free_coordinate"] = free
    return np.array(coefficients, dtype=np.int64), ideal


def smooth_residue_normalization(forms, tangent, ell0, source):
    f1, f2, g1, g2, A, B = forms
    defining = [f1, f2, poly_add(A, B), g1, g2]
    quotient = GradedQuotient(9, defining, [2, 2, 3, 4, 4])
    assert len(quotient.free) == 1
    jacobian = {}
    for permutation in permutations(range(5)):
        sign = (-1)**sum(permutation[i] > permutation[j] for i in range(5) for j in range(i+1, 5))
        term = ONE
        for row, col in enumerate(permutation):
            term = poly_mul(term, poly_derivative(defining[row], col))
        jacobian = poly_add(jacobian, term, sign)
    top_jacobian = int(quotient.reduce(jacobian)[0])
    assert top_jacobian == 3
    normalization = 96*pow(top_jacobian, -1, P) % P
    delta = decode(tangent)
    dh = poly_add(delta[4], delta[5])
    eta = np.array([normalization*int(quotient.reduce(poly_mul({m: 1}, dh))[0]) % P
                    for m in minus_basis], dtype=np.int64)
    nonzero = next(j for j, value in enumerate(ell0) if value)
    scalar = int(eta[nonzero])*pow(int(ell0[nonzero]), -1, P) % P
    assert scalar == 14 and np.array_equal(eta, scalar*ell0 % P)
    source_vector = np.array([source.get(m, 0) for m in minus_basis], dtype=np.int64)
    assert int(eta @ source_vector % P) == 20
    return {"socle_degree": 9, "socle_dimension": 1, "length": 96,
            "Jacobian_top_coordinate": top_jacobian,
            "trace_normalization_multiplier": normalization,
            "normalized_form_over_obstruction_functional": scalar,
            "all_60_negative_source_columns_verified": True,
            "example_source_value": 20}


def moving_point_check(forms, tangent, source):
    f1, f2, _, _, A, B = forms
    curve = [f1, f2, poly_add(A, B)]
    delta = decode(tangent)
    velocity = [delta[0], delta[1], poly_add(delta[4], delta[5])]
    point, ratio = (1, 3, 27, 18, 4), 13
    assert point[3]*pow(point[2], -1, P) % P == ratio
    assert all(poly_evaluate(f, point) == 0 for f in curve)
    jac = np.array([
        [poly_evaluate(velocity[j], point),
         (poly_evaluate(poly_derivative(f, 2), point)+ratio*poly_evaluate(poly_derivative(f, 3), point)) % P,
         poly_evaluate(poly_derivative(f, 4), point)]
        for j, f in enumerate(curve)], dtype=np.int64)
    determinant = base_determinant(jac)
    assert determinant == 11 and poly_evaluate(source, point) == 25
    return {"a_b_c_d_u": list(point), "ratios_b_over_a_d_over_c": [3, ratio],
            "unknowns_at_fixed_ratios": ["contact parameter", "c", "u"],
            "local_jacobian_determinant": determinant, "example_source_value": 25}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--order", type=int, default=50,
                        help="last Taylor order, at least 47 (default: 50)")
    parser.add_argument("--output", type=Path,
                        help="optional path for the reconstructed JSON receipt")
    args = parser.parse_args()
    if args.order < 47:
        parser.error("--order must be at least 47 to check the full-span witness")
    started = time.time()
    forms, source, seed = smooth_seed()
    z0, tangent, coordinates, slice_receipt = smooth_slice(forms)
    z = smooth_branch(z0, tangent, coordinates, args.order)
    ell, obstruction = smooth_obstruction_series(z)
    J = fixed_jacobian_directions(z0)
    assert not np.any(ell @ J % P)
    full = base_receipt(ell[:48])
    assert full["rank"] == 48 and full["minor_rows"] == list(range(48))
    assert full["minor_determinant"] == 17
    example_vector = np.array([source.get(m, 0) for m in minus_basis], dtype=np.int64)
    assert len(base_rref(np.column_stack((base_ideal_matrix(z0), example_vector)))[1]) == 60
    normalization = smooth_residue_normalization(forms, tangent, ell[0], source)
    moving = moving_point_check(forms, tangent, source)
    receipt = {
        "prime": P, "reflection_parameter": REFLECTION_PARAMETER,
        "fixed_equation": "sum(X_i^6+Y_i^6)+(5/7)Q_X^2 Q_Y+(10/7)Q_X Q_Y^2 in the reflection chart",
        "smooth_seed": seed, "slice": slice_receipt,
        "last_Taylor_order": args.order,
        "fixed_equation_verified_through_order": args.order,
        "all_72_ideal_columns_verified_through_order": args.order,
        "obstruction": obstruction, "jacobian_direction_rank": 12,
        "full_span_first_48_rows": full, "canonical_residue": normalization,
        "moving_point": moving,
        "checks": [
            "square completion over Q and fixed weighted-equation identity",
            "simple algebraic cubic-surface line root modulo 37",
            "smooth weighted equation by reduction modulo 5",
            "smooth genus-four contact curve and regular Artinian sequence",
            "rank-70 incidence differential and genuine nongauge normal motion",
            "fixed-equation coefficient recurrence without factorial division",
            "all 72 negative ideal columns and all 12 fixed Jacobian columns",
            "nonzero 48-minor of exactly the first 48 obstruction coefficient rows",
            "canonical residue normalization on all 60 negative monomials",
            "etale moving-point component over the ratio plane",
        ],
        "elapsed_seconds": round(time.time()-started, 3),
        "scope": (
            "Finite exact algebra for the general norm-contact theorem. "
            "Chapter 3B supplies the characteristic-zero algebraic line lift, "
            "the geometric normal-rank upper bound 59, and the Abel--Jacobi interpretation. "
            "This verifier does not construct a prescribed-source rational primitive."
        ),
    }
    if args.output:
        args.output.write_text(json.dumps(receipt, indent=2)+"\n")
    print(json.dumps({
        "incidence_rank_at_seed": 70, "anti_ideal_rank_at_seed": 59,
        "line_equation_jacobian_determinant": seed["line_equation_jacobian_determinant"],
        "contact_curve_smooth": True, "actual_normal_motion": True,
        "fixed_equation_checked_through_order": args.order,
        "Taylor_rows": 48, "span_rank": full["rank"],
        "minor_determinant": full["minor_determinant"],
        "canonical_residue_scalar": normalization["normalized_form_over_obstruction_functional"],
        "moving_point_jacobian_determinant": moving["local_jacobian_determinant"],
        "seconds": receipt["elapsed_seconds"],
    }, indent=2))


if __name__ == "__main__":
    main()
