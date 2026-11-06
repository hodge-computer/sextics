#!/usr/bin/env python3
"""Reconstruct a full-span norm-contact witness for weighted threefolds.

Python 3.9+ and NumPy; no input files or network access required.
Run: python3 scripts/verify-norm-contact-span.py
Pass --output PATH to save the finite arithmetic receipt as JSON.

All computations are exact integer arithmetic modulo 23, or in
F_23[v]/(v^2-15). No floating-point linear algebra is used. The integral
seed is defined below, independently of any catalogue instance. The
script checks its smoothness reduction, nodal curve, incidence slice,
fixed-equation branch, normalized residue and full 48-dimensional span.

Nonzero modular minors give characteristic-zero lower bounds. The exact
central upper bounds and the geometric interpretation are proved in
Chapter 3B; they are not inferred from modular ranks.
"""
from functools import lru_cache
from itertools import permutations, product
from pathlib import Path
import argparse
import json
import time
import numpy as np

P, NONSQUARE = 23, 15
assert pow(NONSQUARE, (P-1)//2, P) == P-1
blocks = [(2, 0), (2, 0), (4, 0), (4, 0), (3, 0), (3, 1)]
INTEGRAL_SEED = {
    "kappa": 50,
    "C": [61, 110, 85],
    "B": [50, 75, 40, 22],
}


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
    """Rank over F_23[v]/(v^2-15), and row/column pivots."""
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
        h[e] = (h.get(e, 0)+scalar*c) % prime
    return {e: c for e, c in h.items() if c}


def poly_mul(f, g, prime=P):
    h = {}
    for e, c in f.items():
        for m, d in g.items():
            n = tuple(x+y for x, y in zip(e, m))
            h[n] = (h.get(n, 0)+c*d) % prime
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


def seed_forms(prime):
    """Reduce one fixed integral norm presentation at the specified prime."""
    C = {(0, 0, 2-j, j, 0): c % prime
         for j, c in enumerate(INTEGRAL_SEED["C"]) if c % prime}
    B = {(0, 0, 3-j, j, 0): c % prime
         for j, c in enumerate(INTEGRAL_SEED["B"]) if c % prime}
    u = {(0, 0, 0, 0, 1): 1}
    f1 = poly_add(u, C, prime=prime)
    f2 = {(1, 1, 0, 0, 0): 1}
    g1 = poly_add(
        poly_add(poly_mul(u, u, prime), poly_mul(u, C, prime),
                 -1, prime),
        poly_mul(C, C, prime), prime=prime)
    k = INTEGRAL_SEED["kappa"]
    g2 = {e: c % prime for e, c in [
        ((4, 0, 0, 0, 0), k), ((0, 4, 0, 0, 0), 2*k),
        ((2, 2, 0, 0, 0), -2), ((2, 0, 1, 1, 0), k),
        ((0, 0, 3, 1, 0), 2*k)] if c % prime}
    A = {(3, 0, 0, 0, 0): 1, (0, 3, 0, 0, 0): 1}
    return [f1, f2, g1, g2, A, B], C


def phi_polynomials(forms, prime=P):
    f1, f2, g1, g2, A, B = forms
    return poly_add(
        poly_add(poly_mul(f1, g1, prime), poly_mul(f2, g2, prime),
                 prime=prime),
        poly_add(poly_mul(A, A, prime), poly_mul(B, B, prime),
                 -1, prime),
        prime=prime)


def smoothness_check():
    # This reduction only certifies smoothness of the integral witness.
    # The moving contact family is constructed below at prime 23.
    forms, _ = seed_forms(5)
    reduced = phi_polynomials(forms, 5)
    expected = {
        (6, 0, 0, 0, 0): 1, (0, 6, 0, 0, 0): 1,
        (0, 0, 6, 0, 0): 1, (0, 0, 0, 6, 0): 1,
        (0, 0, 0, 0, 3): 1,
    }
    assert reduced == expected
    return {
        "prime": 5,
        "equation": "a^6+b^6+c^6+d^6+u^3",
        "partial_derivative_coefficients": [1, 1, 1, 1, 3],
        "weighted_vertex_avoided": True,
    }


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


def univariate(form):
    """Binary homogeneous form at c=1, in ascending powers of d."""
    degree = next(iter(form))[2]+next(iter(form))[3]
    result = [0]*(degree+1)
    for e, c in form.items():
        assert e[0] == e[1] == e[4] == 0
        result[e[3]] = int(c) % P
    return trim(result)


def trim(poly):
    result = [int(c) % P for c in poly]
    while result and result[-1] == 0:
        result.pop()
    return result


def polynomial_gcd(left, right):
    left, right = trim(left), trim(right)
    while right:
        remainder = left[:]
        inverse = pow(right[-1], -1, P)
        while len(remainder) >= len(right):
            scalar = remainder[-1]*inverse % P
            shift = len(remainder)-len(right)
            for j, c in enumerate(right):
                remainder[shift+j] = (remainder[shift+j]-scalar*c) % P
            remainder = trim(remainder)
        left, right = right, remainder
    return [(c*pow(left[-1], -1, P)) % P for c in left] if left else []


def node_value(form, C):
    """Restrict a quadratic variation to a=b=0, u=-C."""
    result = {}
    for e, c in form.items():
        if e[0] or e[1]:
            continue
        if e[4]:
            assert e == (0, 0, 0, 0, 1)
            result = poly_add(result, C, -c)
        else:
            result = poly_add(result, {e: c})
    return result


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


def source_data():
    forms, C = seed_forms(P)
    z0 = encode(forms)
    M = differential(z0)
    incidence = base_receipt(M)
    assert incidence["rank"] == 69
    tangents = nullspace(M)
    assert tangents.shape == (21, 90)
    f1, f2, g1, g2, A, B = forms
    curve_forms = [f1, f2, poly_add(A, B)]
    quotients = {d: GradedQuotient(d, curve_forms, [2, 2, 3])
                 for d in (2, 3, 6)}
    dimensions = [len(quotients[d].free) for d in (2, 3, 6)]
    assert dimensions == [9, 15, 33]
    images = []
    for tangent in tangents:
        delta = decode(tangent)
        images.append(np.concatenate((
            quotients[2].reduce(delta[0]),
            quotients[2].reduce(delta[1]),
            quotients[3].reduce(poly_add(delta[4], delta[5])))))
    image = base_receipt(np.array(images, dtype=np.int64).T)
    assert image["rank"] == 2
    ds = tangents[image["minor_columns"]]

    gauge = gauge_vectors(forms)
    assert gauge.shape == (90, 19)
    assert not np.any(M @ gauge % P)
    assert len(base_rref(gauge)[1]) == 19
    coordinate_vectors = np.eye(90, dtype=np.int64)[
        :, incidence["minor_columns"]]
    slice_and_gauge = np.concatenate((coordinate_vectors, ds.T, gauge), axis=1)
    assert slice_and_gauge.shape == (90, 90)
    transverse_determinant = base_determinant(slice_and_gauge)
    assert transverse_determinant

    left = nullspace(M.T)
    assert left.shape == (1, 70)
    ell = left[0]
    d1, d2 = [np.stack((d, np.zeros(90, dtype=np.int64)), axis=-1)
              for d in ds]
    q = [int(ell @ quadratic(d1, d1)[:, 0] % P),
         int(ell @ (quadratic(d1, d2)+quadratic(d2, d1))[:, 0] % P),
         int(ell @ quadratic(d2, d2)[:, 0] % P)]
    assert q == [10, 12, 13]
    discriminant = (q[1]**2-4*q[0]*q[2]) % P
    assert discriminant == NONSQUARE
    K1, K2 = [node_value(decode(d)[1], C) for d in ds]
    bad = poly_add(poly_add({}, poly_mul(K2, K2), q[0]),
                   poly_mul(K1, K2), -q[1])
    bad = poly_add(bad, poly_mul(K1, K1), q[2])
    Cu, Bu = univariate(C), univariate(B)
    derivative_B = [j*Bu[j] % P for j in range(1, len(Bu))]
    assert len(Bu) == 4  # No root at c=0.
    assert polynomial_gcd(Bu, derivative_B) == [1]
    assert polynomial_gcd(Bu, Cu) == [1]
    assert polynomial_gcd(Bu, univariate(bad)) == [1]
    receipt = {
        "incidence_derivative": incidence,
        "curve_graded_dimensions": dict(zip(("2", "3", "6"), dimensions)),
        "normal_tangent_image": image,
        "essential_kernel_basis_indices": image["minor_columns"],
        "presentation_gauge_rank": 19,
        "slice_plus_gauge_determinant": transverse_determinant,
        "quadratic_obstruction": q,
        "quadratic_discriminant": discriminant,
        "node_smoothing_quadratics": [
            [int(K.get((0, 0, 2-j, j, 0), 0)) for j in range(3)]
            for K in (K1, K2)],
        "B_squarefree": True, "C_B_coprime": True,
        "both_branches_smooth_all_nodes": True,
        "node_smoothing_gcd": [1],
    }
    return z0, ds, receipt


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


def continue_branch(z0, ds, source, degree):
    M = differential(z0)
    selected_rows = source["incidence_derivative"]["minor_rows"]
    selected_cols = source["incidence_derivative"]["minor_columns"]
    missing = next(i for i in range(70) if i not in selected_rows)
    inverse = base_inverse(M[np.ix_(selected_rows, selected_cols)])
    ell = np.zeros(70, dtype=np.int64)
    ell[missing] = 1
    ell[selected_rows] = -M[missing, selected_cols] @ inverse % P
    assert not np.any(ell @ M % P)
    assert not np.any(M @ ds[0] % P) and not np.any(M @ ds[1] % P)
    d1 = np.stack((ds[0], np.zeros(90, dtype=np.int64)), axis=-1)
    d2 = np.stack((ds[1], np.zeros(90, dtype=np.int64)), axis=-1)
    alpha = np.array([19, 8], dtype=np.int64)
    q_alpha = (np.array([10, 0])+mul([12, 0], alpha) +
               mul([13, 0], mul(alpha, alpha))) % P
    assert not np.any(q_alpha)
    z = np.zeros((degree+1, 90, 2), dtype=np.int64)
    z[0, :, 0] = z0
    z[1] = (d1+mul(alpha, d2)) % P
    denominator = ell @ (quadratic(z[1], d2)+quadratic(d2, z[1])) % P
    assert denominator.tolist() == [0, 1]
    denominator_inverse = inv(denominator)
    assert not np.any(ell @ quadratic(z[1], z[1]) % P)
    for n in range(2, degree+1):
        forcing = np.zeros((70, 2), dtype=np.int64)
        for i in range(1, n):
            forcing = (forcing+quadratic(z[i], z[n-i])) % P
        assert not np.any(ell @ forcing % P), ("obstruction", n)
        normal = np.zeros((90, 2), dtype=np.int64)
        normal[selected_cols] = -inverse @ forcing[selected_rows] % P
        assert not np.any((M @ normal+forcing) % P), ("coefficient", n)
        next_forcing = quadratic(z[1], normal)+quadratic(normal, z[1])
        for i in range(2, n):
            next_forcing += quadratic(z[i], z[n+1-i])
        correction = -mul(ell @ next_forcing % P,
                          denominator_inverse) % P
        z[n] = (normal+mul(correction, d2)) % P
    return z, {"slope": alpha.tolist(),
               "quadratic_root_derivative": denominator.tolist(),
               "verified_fixed_equation_through_degree": degree}


def obstruction_series(z, order):
    matrices = np.array([ideal_matrix(a) for a in z], dtype=np.int64)
    M0 = matrices[0, :, :, 0]
    _, cols = base_rref(M0)
    assert len(cols) == 58
    _, rows = base_rref(M0[:, cols].T)
    assert len(rows) == 58
    free = [j for j in range(60) if j not in rows]
    inverse = base_inverse(M0[np.ix_(rows, cols)].T)
    # L is a formal basis of the left kernel of the 58 selected columns.
    # Axes: order, functional coordinate, basis vector, field coordinate.
    L = np.zeros((order+2, 60, 2, 2), dtype=np.int64)
    for k in range(2):
        L[0, free[k], k, 0] = 1
        L[0, rows, k, 0] = -inverse @ M0[free[k], cols] % P
    for n in range(1, order+2):
        rhs = np.zeros((58, 2, 2), dtype=np.int64)
        for i in range(1, n+1):
            # Shape 58 equations by 60 functional coordinates.
            a = matrices[i][:, cols, :].transpose(1, 0, 2)
            rhs = (rhs+matmul(a, L[n-i])) % P
        L[n, rows] = (-inverse @ rhs.reshape(58, 4)).reshape(58, 2, 2) % P

    # Any extra column with first-order rank gain fixes the remaining ratio.
    candidates = [j for j in range(72) if j not in cols]
    chosen, K = None, None
    for col in candidates:
        k1 = np.zeros((2, 2), dtype=np.int64)
        for i in range(2):
            k1 = (k1+matmul(L[i].transpose(1, 0, 2),
                            matrices[1-i, :, col, :])) % P
        if np.any(k1):
            chosen = col
            break
    assert chosen is not None, "No first-order rank gain in the anti ideal"
    K = np.zeros((order+2, 2, 2), dtype=np.int64)
    for n in range(order+2):
        for i in range(n+1):
            K[n] = (K[n]+matmul(L[i].transpose(1, 0, 2),
                               matrices[n-i, :, chosen, :])) % P
    assert not np.any(K[0])
    assert np.any(K[1])
    ell = np.zeros((order+1, 60, 2), dtype=np.int64)
    for n in range(order+1):
        for i in range(n+1):
            ell[n] = (ell[n]+
                      mul(K[i+1, 1], L[n-i, :, 0]) -
                      mul(K[i+1, 0], L[n-i, :, 1])) % P
    assert np.any(ell[0])
    # Verify the kernel identity against ALL 72 columns, not only those used.
    for n in range(order+1):
        total = np.zeros((72, 2), dtype=np.int64)
        for i in range(n+1):
            total = (total+matmul(matrices[i].transpose(1, 0, 2),
                                  ell[n-i])) % P
        assert not np.any(total), ("full ideal kernel", n)
    return ell, {"constant_ideal_rank": 58,
                 "constant_ideal_minor_determinant":
                     base_determinant(M0[np.ix_(rows, cols)]),
                 "selected_extra_column": chosen,
                 "first_order_relation": K[1].tolist(),
                 "selected_ideal_columns": cols,
                 "selected_ideal_rows": rows}


def rank_receipt(a):
    rank, rows, cols = extension_rank(a)
    minor = a[np.ix_(rows, cols)]
    determinant = extension_determinant(minor)
    return {"rank": rank, "rows": rows, "columns": cols,
            "minor_determinant": determinant}


def residue_normalization(z0, z1, ell0):
    """Check the canonical Artinian trace and its nonzero AJ scalar."""
    f1, f2, g1, g2, A, B = decode(z0)
    C = {e: c for e, c in f1.items() if e[4] == 0}
    f3 = poly_add(A, B)
    reduced_g1 = {e: 3*c % P for e, c in poly_mul(C, C).items()}
    forms = [f2, f3, reduced_g1, g2]
    q9 = GradedQuotient(9, forms, [2, 3, 4, 4], core_only=True)
    q10 = GradedQuotient(10, forms, [2, 3, 4, 4], core_only=True)
    assert len(q9.free) == 1 and not q10.free

    def derivative(f, variable):
        result = {}
        for e, c in f.items():
            if e[variable]:
                m = list(e)
                m[variable] -= 1
                result[tuple(m)] = e[variable]*c % P
        return result

    jacobian = {}
    for permutation in permutations(range(4)):
        inversions = sum(permutation[i] > permutation[j]
                         for i in range(4) for j in range(i+1, 4))
        term = {(0, 0, 0, 0, 0): 1}
        for row, col in enumerate(permutation):
            term = poly_mul(term, derivative(forms[row], col))
        jacobian = poly_add(jacobian, term, (-1)**inversions)
    top_jacobian = int(q9.reduce(jacobian)[0])
    assert top_jacobian
    normalization = 96*pow(top_jacobian, -1, P) % P

    def substitute_u(poly):
        powers = [{(0, 0, 0, 0, 0): 1}]
        for _ in range(4):
            powers.append(poly_mul(powers[-1],
                                   {e: -c % P for e, c in C.items()}))
        out = {}
        for e, coefficient in poly.items():
            m = tuple(e[:4])+(0,)
            out = poly_add(out, poly_mul({m: coefficient}, powers[e[4]]))
        return out

    # Differentiate f3 in the ambient coordinates BEFORE substituting u=-C.
    df3 = []
    for field_part in (0, 1):
        delta = decode(z1[:, field_part])
        df3.append(poly_add(delta[4], delta[5]))
    eta0 = []
    for m in minus_basis:
        values = []
        for derivative_f3 in df3:
            numerator = substitute_u(poly_mul({m: 1}, derivative_f3))
            values.append(normalization*int(q9.reduce(numerator)[0]) % P)
        eta0.append(values)
    eta0 = np.array(eta0, dtype=np.int64)
    nonzero = next(i for i, e in enumerate(ell0) if np.any(e))
    ratio = mul(eta0[nonzero], inv(ell0[nonzero]))
    assert np.any(ratio)
    assert np.array_equal(eta0, mul(ratio, ell0))
    assert ratio.tolist() == [0, 17]
    return {
        "degrees_after_eliminating_u": [2, 3, 4, 4],
        "degree9_quotient_dimension": 1,
        "degree10_quotient_dimension": 0,
        "length": 96, "socle_degree": 9,
        "top_monomial": q9.basis[q9.free[0]],
        "Jacobian_top_coordinate": top_jacobian,
        "trace_normalization_multiplier": normalization,
        "normalized_form_over_obstruction_functional": ratio.tolist(),
        "convention": "eta_S=Res_f(S*d_B(f3)); a global contraction sign is immaterial",
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--order", type=int, default=47,
                        help="last Taylor order, at least 47 (default: 47)")
    parser.add_argument("--output", type=Path,
                        help="optional path for the reconstructed JSON receipt")
    args = parser.parse_args()
    if args.order < 47:
        parser.error("--order must be at least 47 to check the full-span witness")
    started = time.time()
    smoothness = smoothness_check()
    z0, ds, source = source_data()
    forms, _ = seed_forms(P)
    target = phi_polynomials(forms)
    z0_ext = np.stack((z0, np.zeros(90, dtype=np.int64)), axis=-1)
    assert np.array_equal(quadratic(z0_ext, z0_ext)[:, 0],
                          np.array([target.get(e, 0) for e in plus_basis]))
    z, branch = continue_branch(z0, ds, source, args.order+2)
    # Reconstruct every coefficient of Phi(z(t)), including all cross terms.
    for n in range(1, len(z)):
        coefficient = np.zeros((70, 2), dtype=np.int64)
        for i in range(n+1):
            coefficient = (coefficient+quadratic(z[i], z[n-i])) % P
        assert not np.any(coefficient), ("fixed equation", n)
    ell, obstruction = obstruction_series(z, args.order)
    J = fixed_jacobian_directions(z0)
    assert not np.any(np.einsum("nif,ij->njf", ell, J) % P)
    full = rank_receipt(ell[:48])
    assert full["rank"] == 48
    assert full["minor_determinant"] == [22, 2]
    determinant_norm = (22**2-NONSQUARE*2**2) % P
    assert determinant_norm == 10
    normalization = residue_normalization(z0, z[1], ell[0])
    receipt = {
        "prime": P, "quadratic_extension": "v^2=15",
        "integral_seed": INTEGRAL_SEED,
        "fixed_equation": "G=f1*g1+f2*g2+A^2-B^2 from the integral seed",
        "smoothness": smoothness,
        "central_contact": source,
        "last_Taylor_order": args.order,
        "branch": branch, "obstruction": obstruction,
        "canonical_residue": normalization,
        "jacobian_direction_rank": 12,
        "full_span": full, "full_minor_norm": determinant_norm,
        "checks": [
            "smooth weighted integral witness by reduction modulo 5",
            "squarefree B, coprime C and B, and three simultaneously smoothed nodes",
            "rank-69 incidence differential and rank-90 slice/gauge decomposition",
            "simple tangent-cone root and nonzero punctured-branch rank gain",
            "every fixed-equation coefficient through the reported branch order",
            "every coefficient annihilates all 72 anti-ideal columns",
            "every coefficient annihilates all 12 fixed Jacobian directions",
            "regular Artinian sequence and canonical residue scalar",
            "48-by-48 minor of the first 48 obstruction coefficient rows",
        ],
        "elapsed_seconds": round(time.time()-started, 3),
        "scope": (
            "Finite exact algebra for the general norm-contact theorem. "
            "Characteristic-zero central upper bounds, branch lifting and "
            "the Abel--Jacobi interpretation are proved in Chapter 3B."
        ),
    }
    if args.output:
        args.output.write_text(json.dumps(receipt, indent=2)+"\n")
    print(json.dumps({
        "incidence_rank_at_seed": source["incidence_derivative"]["rank"],
        "slice_and_gauge_rank": 90,
        "anti_ideal_rank_at_seed": obstruction["constant_ideal_rank"],
        "both_branches_smooth_all_nodes": True,
        "fixed_equation_checked_through_order":
            branch["verified_fixed_equation_through_degree"],
        "Taylor_rows": 48, "span_rank": full["rank"],
        "minor_determinant": full["minor_determinant"],
        "minor_norm": determinant_norm,
        "canonical_residue_scalar":
            normalization["normalized_form_over_obstruction_functional"],
        "seconds": receipt["elapsed_seconds"],
    }, indent=2))


if __name__ == "__main__":
    main()
