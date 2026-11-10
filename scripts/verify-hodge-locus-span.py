#!/usr/bin/env python3
"""Reconstruct the Hodge-locus spanning witness of Chapter 3D.

Python 3.9+ and NumPy; no witness files, extra packages, or network required.
Run: python3 scripts/verify-hodge-locus-span.py
Pass --output PATH to save the finite-arithmetic receipt.

The witness is the Fermat weighted sextic T = {x0^6+x1^6+x2^6+x3^6+w^3 = 0}
in P(1,1,1,1,2) with the order-three symmetry g = (omega^2, omega^2, omega, 1; 1),
the del Pezzo fourfold Y = {F0 + t*a + t^2 = 0} in P(1,1,1,1,2,3) with
    a = 5*(x0^3 + x1^3 + x2^3 + x3^3 + x0*x2*x3 + x1*x2*x3 + x3*w),
and the invariant class Q = x2*w^4 on it.  Nothing is read from disk.

The script computes, modulo the prime 2^31 - 1,
  * the rank of mu_Q : K -> [t*K*Q] from the invariant cubics to R(Ft)_15,
  * its kernel, and for each kernel vector a solution of
        t*K*Q = sum_z c_z * dFt/dz ,
  * the class of c_t restricted to t = 0 in R(F0)_12,
and checks that every one of the 33 standard monomials of R(F0)_12 of
character omega has a nonzero coefficient in one of these classes.  The
diagonal automorphisms of the Fermat sextic act on those monomials through
pairwise distinct characters, so the translates of the classes span
(Chapter 3D).  Surjectivity of mu_Q together with a nonzero coordinate is full
row rank of an integer matrix, so the modular computation settles the statement
over the rational numbers.  Smoothness is not computed: the fourfold reduces to
a Fermat equation modulo five.

The script first runs the same recipe on a quartic surface containing a line,
where the answer is known: the classes must be multiples of evaluation at the
point where the line meets the plane section.
"""
from itertools import permutations
import argparse
import json
import time
import numpy as np

P = 2**31 - 1


def coefficient(seed, k):
    """Coefficient of the k-th monomial (k = 0, 1, ...) of the polynomial with this seed."""
    return (seed * (k + 2)**3 + k) % 13 - 6


def monomials(degree, weights, characters=None, order=1, character=0):
    """Exponent vectors of weighted degree `degree`, in lexicographic order."""
    out, n = [], len(weights)

    def extend(i, remaining, current):
        if i == n:
            if remaining == 0 and (characters is None or
                                   (sum(a*b for a, b in zip(current, characters)) - character) % order == 0):
                out.append(tuple(current))
            return
        for a in range(remaining // weights[i] + 1):
            extend(i + 1, remaining - a*weights[i], current + [a])

    extend(0, degree, [])
    return out


def mul(a, b):
    r = {}
    for e1, c1 in a.items():
        for e2, c2 in b.items():
            e = tuple(x + y for x, y in zip(e1, e2))
            r[e] = (r.get(e, 0) + c1*c2) % P
    return {e: c for e, c in r.items() if c}


def add(a, b, sign=1):
    r = dict(a)
    for e, c in b.items():
        r[e] = (r.get(e, 0) + sign*c) % P
    return {e: c for e, c in r.items() if c}


def diff(a, i):
    r = {}
    for e, c in a.items():
        if e[i]:
            f = list(e)
            f[i] -= 1
            r[tuple(f)] = c*e[i] % P
    return r


def eliminate(M, pivot_columns):
    """Gauss-Jordan elimination modulo P, pivoting only in the first columns.

    Entries stay in [0, P); every product is below 2^62.
    """
    M %= P
    rank, pivots = 0, []
    for c in range(pivot_columns):
        nonzero = np.nonzero(M[rank:, c])[0]
        if len(nonzero) == 0:
            continue
        r = rank + nonzero[0]
        if r != rank:
            M[[rank, r]] = M[[r, rank]]
        M[rank] = M[rank] * pow(int(M[rank, c]), P - 2, P) % P
        rows = np.nonzero(M[:, c])[0]
        rows = rows[rows != rank]
        if len(rows):
            M[rows] = (M[rows] - M[rows, c][:, None] * M[rank][None, :] % P) % P
        pivots.append(c)
        rank += 1
        if rank == M.shape[0]:
            break
    return rank, pivots


def nullspace(A):
    A = A.copy() % P
    _, pivots = eliminate(A, A.shape[1])
    basis = []
    for free in [j for j in range(A.shape[1]) if j not in pivots]:
        v = [0]*A.shape[1]
        v[free] = 1
        for i, c in enumerate(pivots):
            v[c] = int(-A[i, free]) % P
        basis.append(v)
    return basis


def combine(columns, vector):
    """Linear combination of matrix columns, reduced term by term."""
    total = np.zeros(columns.shape[0], dtype=np.int64)
    for j, c in enumerate(vector):
        if c:
            total = (total + columns[:, j] * int(c) % P) % P
    return total


def normal_function_classes(Ft, Q, K_monomials, t_index, weights, degree,
                            characters=None, order=1, character=0, extra=()):
    """Kernel of K -> [t*K*Q] modulo J(Ft), and c_t|_{t=0} for each kernel vector.

    `extra` lists further polynomials Q sharing the same Jacobian ideal; one
    elimination serves all of them.  Returns (dim R, [(rank, classes), ...]).
    """
    n = len(weights)
    t = tuple(int(i == t_index) for i in range(n))
    rows = monomials(degree, weights, characters, order, character)
    index = {m: i for i, m in enumerate(rows)}
    generators = []
    for z in range(n):
        dz = diff(Ft, z)
        if not dz:
            continue
        dz_degree = sum(a*b for a, b in zip(next(iter(dz)), weights))
        dz_character = 0 if characters is None else sum(
            a*b for a, b in zip(next(iter(dz)), characters)) % order
        for m in monomials(degree - dz_degree, weights, characters, order,
                           (character - dz_character) % order if characters else 0):
            generators.append((z, m, mul({m: 1}, dz)))
    Qs = (Q,) + tuple(extra)
    width = len(K_monomials)
    M = np.zeros((len(rows), len(generators) + width*len(Qs)), dtype=np.int64)
    for j, (_, _, g) in enumerate(generators):
        for e, c in g.items():
            M[index[e], j] = c
    for q, poly in enumerate(Qs):
        for k, K in enumerate(K_monomials):
            for e, c in mul(mul({t: 1}, {K: 1}), poly).items():
                M[index[e], len(generators) + width*q + k] = c
    rank_J, pivots = eliminate(M, len(generators))
    results = []
    for q in range(len(Qs)):
        block = slice(len(generators) + width*q, len(generators) + width*(q + 1))
        kernel = nullspace(M[rank_J:, block])
        classes = []
        for v in kernel:
            assert not combine(M[rank_J:, block], v).any()
            solution = combine(M[:rank_J, block], v)
            B = {}
            for i, c in enumerate(pivots):
                z, m, _ = generators[c]
                if z == t_index and m[t_index] == 0 and solution[i]:
                    e = m[:t_index] + m[t_index + 1:]
                    B[e] = (B.get(e, 0) + int(solution[i])) % P
            classes.append(B)
        results.append((width - len(kernel), classes))
    return len(rows) - rank_J, results


def line_on_quartic():
    """A quartic surface l1*G1 + l2*G2 = 0 in P^3 containing the line l1 = l2 = 0."""
    weights = (1, 1, 1, 1)

    def form(seed, degree):
        return {m: coefficient(seed, k) % P
                for k, m in enumerate(monomials(degree, weights)) if coefficient(seed, k) % P}

    l1, l2, G1, G2 = form(1, 1), form(2, 1), form(3, 3), form(4, 3)
    Ft = add(mul(l1, G1), mul(l2, G2))
    jacobian = [[diff(f, i) for i in range(4)] for f in (l1, G1, l2, G2)]
    Q = {}
    for perm in permutations(range(4)):
        sign = 1
        for i in range(4):
            for j in range(i + 1, 4):
                if perm[i] > perm[j]:
                    sign = -sign
        term = {(0, 0, 0, 0): 1}
        for i in range(4):
            term = mul(term, jacobian[i][perm[i]])
        Q = add(Q, term, sign)
    dim_R8, [(rank, classes)] = normal_function_classes(
        Ft, Q, monomials(3, weights), 3, weights, 8)
    assert (dim_R8, rank, len(classes)) == (1, 1, 19)
    # Socle functional of the plane quartic F0 = Ft|_{t=0}, in degree six.
    F0 = {e[:3]: c for e, c in Ft.items() if e[3] == 0}
    sextics = monomials(6, (1, 1, 1))
    position = {m: i for i, m in enumerate(sextics)}
    relations = [mul({m: 1}, diff(F0, z)) for z in range(3) for m in monomials(3, (1, 1, 1))]
    A = np.zeros((len(relations), len(sextics)), dtype=np.int64)
    for i, g in enumerate(relations):
        for e, c in g.items():
            A[i, position[e]] = c
    socle = nullspace(A)
    assert len(socle) == 1          # the plane quartic is smooth
    def pairing(poly):
        return sum(socle[0][position[e]]*c for e, c in poly.items()) % P
    linear = ((1, 0, 0), (0, 1, 0), (0, 0, 1))
    functionals = [[pairing(mul({e: 1}, B)) for e in linear] for B in classes]
    u = [[l.get(e + (0,), 0) for e in linear] for l in (l1, l2)]
    point = [(u[0][1]*u[1][2] - u[0][2]*u[1][1]) % P,
             (u[0][2]*u[1][0] - u[0][0]*u[1][2]) % P,
             (u[0][0]*u[1][1] - u[0][1]*u[1][0]) % P]
    assert any(point)
    nonzero = sum(any(f) for f in functionals)
    assert nonzero >= 1
    assert all((f[i]*point[j] - f[j]*point[i]) % P == 0
               for f in functionals for i in range(3) for j in range(3))
    return {'kernelDimension': 19, 'nonzeroFunctionals': nonzero,
            'allProportionalToEvaluationAtLinePoint': True}


def weighted_sextic():
    weights = (1, 1, 1, 1, 2, 3)
    characters = (2, 2, 1, 0, 0, 0)

    def invariant(degree, character, variables=6):
        return [m for m in monomials(degree, weights, characters, 3, character)
                if not any(m[variables:])]

    F0 = {tuple(6//weights[i] if j == i else 0 for j in range(6)): 1 for i in range(5)}
    K_monomials = invariant(3, 0)
    assert len(K_monomials) == 10
    assert len(monomials(15, weights, characters, 3, 1)) == 1247
    t = (0, 0, 0, 0, 0, 1)
    # a = 5*(x0^3 + x1^3 + x2^3 + x3^3 + x0*x2*x3 + x1*x2*x3 + x3*w) and Q = x2*w^4.
    # Modulo five the equation is F0 + t^2, whose partial derivatives are
    # 6*x_i^5, 3*w^2 and 2*t: the fourfold is quasismooth.
    a = {m: 5 for m in [(3, 0, 0, 0, 0, 0), (0, 3, 0, 0, 0, 0), (0, 0, 3, 0, 0, 0),
                        (0, 0, 0, 3, 0, 0), (1, 0, 1, 1, 0, 0), (0, 1, 1, 1, 0, 0),
                        (0, 0, 0, 1, 1, 0)]}
    Q = {(0, 0, 1, 0, 4, 0): 1}
    assert set(a) <= set(invariant(3, 0, 5)) and set(Q) <= set(invariant(9, 1))
    Ft = add(add(F0, mul({t: 1}, a)), {(0, 0, 0, 0, 0, 2): 1})
    dim_R15, [(rank, classes)] = normal_function_classes(
        Ft, Q, K_monomials, 5, weights, 15, characters, 3, 1)
    assert (dim_R15, rank, len(classes)) == (7, 7, 3)
    # Classes in R(F0)_12 of character one.  F0 is Fermat: J(F0) is spanned by
    # the monomials divisible by some x_i^5 or by w^2.
    standard = [m[:5] for m in invariant(12, 1, 5) if max(m[:4]) <= 4 and m[4] <= 1]
    position = {m: i for i, m in enumerate(standard)}
    assert len(standard) == 33
    # The diagonal group mu_6^4 x mu_3 sees exponents modulo (6, 6, 6, 6, 3).
    assert len({tuple(e % 6 for e in m[:4]) + (m[4] % 3,) for m in standard}) == 33
    M = np.zeros((len(classes), len(standard)), dtype=np.int64)
    for i, B in enumerate(classes):
        for e, c in B.items():
            if e in position:
                M[i, position[e]] = c
    reached = int(np.count_nonzero(M.any(axis=0)))
    supports = sorted(int(np.count_nonzero(row)) for row in M)
    image_rank, _ = eliminate(M.copy(), M.shape[1])
    assert image_rank == 2
    assert reached == 33, reached
    return {'prime': P, 'a': '5*(x0^3+x1^3+x2^3+x3^3+x0*x2*x3+x1*x2*x3+x3*w)', 'Q': 'x2*w^4',
            'dimS15': 1247, 'dimR15': dim_R15, 'rankMu': rank, 'kernel': len(classes),
            'imageRank': image_rank, 'classSupports': supports,
            'standardMonomials': len(standard), 'monomialsReached': reached}


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--output')
    args = parser.parse_args()
    start = time.time()
    line = line_on_quartic()
    print('Line on a quartic surface: 19 kernel directions, all classes '
          'proportional to evaluation at the point of the line.', flush=True)
    sextic = weighted_sextic()
    print(f"Fermat weighted sextic, a = {sextic['a']}, Q = {sextic['Q']}:")
    print(f"  dim R(Ft)_15 of character omega = {sextic['dimR15']}, rank mu_Q = {sextic['rankMu']}, "
          f"kernel = {sextic['kernel']}, rank of the normal-function classes = {sextic['imageRank']}")
    print(f"  standard monomials with a nonzero coefficient in some class: "
          f"{sextic['monomialsReached']} of {sextic['standardMonomials']}; "
          f"their diagonal characters are pairwise distinct.")
    print(f'All Hodge-locus checks passed in {time.time() - start:.0f}s.')
    if args.output:
        with open(args.output, 'w') as handle:
            json.dump({'lineOnQuartic': line, 'weightedSextic': sextic}, handle, indent=2)
            handle.write('\n')


if __name__ == '__main__':
    main()
