#!/usr/bin/env python3
"""Reconstruct the Hodge-locus spanning witness of Chapter 3D.

Python 3.9+ and NumPy; no witness files, extra packages, or network required.
Run: python3 scripts/verify-hodge-locus-span.py
Pass --output PATH to save the finite-arithmetic receipt.

The witness is the Fermat weighted sextic T = {x0^6+x1^6+x2^6+x3^6+w^3 = 0}
in P(1,1,1,1,2) with the order-three symmetry g = (omega^2, omega^2, omega, 1; 1),
three del Pezzo fourfolds Y = {F0 + t*a + t^2 = 0} in P(1,1,1,1,2,3), and
eighteen invariant classes Q on them.  Every polynomial is generated from the
rule in `coefficient`; nothing is read from disk.

For each pair (a, Q) the script computes, modulo the prime 2^31 - 1,
  * the rank of mu_Q : K -> [t*K*Q] from the invariant cubics to R(Ft)_15,
  * its kernel, and for each kernel vector a solution of
        t*K*Q = sum_z c_z * dFt/dz ,
  * the class of c_t restricted to t = 0 in R(F0)_12,
and then the dimension of the span of these classes.  Surjectivity of every
mu_Q together with a full span is equivalent to full row rank of one integer
matrix (Chapter 3D), so the modular ranks are lower bounds that settle the
statement over the rational numbers.  Smoothness is not computed: the three
fourfolds reduce to a Fermat equation modulo five.

The script first runs the same recipe on a quartic surface containing a line,
where the answer is known: the classes must be multiples of evaluation at the
point where the line meets the plane section.
It also checks smoothness of the
cyclic three-link sextic used as an example in the same chapter.
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
    cubics = invariant(3, 0, 5)
    K_monomials = invariant(3, 0)
    Q_monomials = invariant(9, 1)
    assert (len(cubics), len(K_monomials)) == (9, 10)
    t = (0, 0, 0, 0, 0, 1)
    classes, table = [], []
    for i in (1, 2, 3):
        integral = {m: 5*coefficient(i, k) for k, m in enumerate(cubics) if coefficient(i, k)}
        # Modulo five the equation is F0 + t^2, whose partial derivatives are
        # 6*x_i^5, 3*w^2 and 2*t: the fourfold is quasismooth.
        assert integral and all(c % 5 == 0 for c in integral.values())
        a = {m: c % P for m, c in integral.items()}
        Ft = add(add(F0, mul({t: 1}, a)), {(0, 0, 0, 0, 0, 2): 1})
        Qs = [{m: coefficient(10*i + j, k) % P for k, m in enumerate(Q_monomials)
               if coefficient(10*i + j, k) % P} for j in range(1, 7)]
        dim_R15, results = normal_function_classes(
            Ft, Qs[0], K_monomials, 5, weights, 15, characters, 3, 1, extra=Qs[1:])
        assert dim_R15 == 7
        for j, (rank, found) in enumerate(results, start=1):
            assert rank == 7 and len(found) == 3
            classes.append(found)
            table.append({'a': i, 'Q': 10*i + j, 'rankMu': rank, 'kernel': len(found)})
    # Classes in R(F0)_12 of character one.  F0 is Fermat: J(F0) is spanned by
    # the monomials divisible by some x_i^5 or by w^2.
    standard = [m[:5] for m in invariant(12, 1, 5) if max(m[:4]) <= 4 and m[4] <= 1]
    position = {m: i for i, m in enumerate(standard)}
    assert len(standard) == 33
    flat = [B for found in classes for B in found]
    M = np.zeros((len(standard), len(flat)), dtype=np.int64)
    for j, B in enumerate(flat):
        for e, c in B.items():
            if e in position:
                M[position[e], j] = c
    _, pivots = eliminate(M, M.shape[1])
    cumulative, seen = [], 0
    for row, found in zip(table, classes):
        seen += len(found)
        row['cumulativeSpan'] = sum(1 for c in pivots if c < seen)
        cumulative.append(row['cumulativeSpan'])
    assert cumulative[-1] == 33, cumulative
    return {'prime': P, 'invariantCubics': 9, 'dimR15': 7, 'dimH12Invariant': 33,
            'pairs': table, 'span': cumulative[-1]}


def cyclic_three_links():
    """Smoothness of F = sum(X_i^6 + Y_i^6) + (1/2) sum M_i, M_i = X_i^3 X_{i+1} Y_i Y_{i+1}.

    At a singular point the products X_i dF/dX_i and Y_i dF/dY_i vanish, so
    12 X_i^6 = -(3 m_i + m_{i-1}) and 12 Y_i^6 = -(m_i + m_{i-1}) for m_i = M_i.
    Substituting into m_i^6 gives three ternary sextics in (m_0, m_1, m_2), not
    all zero.  They generate every form of degree sixteen, so they have no
    common zero and the sextic is smooth.
    """
    unit = [{tuple(int(i == j) for j in range(3)): 1} for i in range(3)]
    A = [add({e: 3*c for e, c in unit[i].items()}, unit[i - 1]) for i in range(3)]
    B = [add(unit[i], unit[i - 1]) for i in range(3)]

    def power(poly, k):
        result = {(0, 0, 0): 1}
        for _ in range(k):
            result = mul(result, poly)
        return result

    sextics = []
    for i in range(3):
        left = {e: c * 12**6 % P for e, c in power(unit[i], 6).items()}
        right = mul(mul(power(A[i], 3), A[(i + 1) % 3]), mul(B[i], B[(i + 1) % 3]))
        sextics.append(add(left, right, -1))
    rows = monomials(16, (1, 1, 1))
    position = {m: i for i, m in enumerate(rows)}
    columns = [mul({m: 1}, f) for f in sextics for m in monomials(10, (1, 1, 1))]
    M = np.zeros((len(rows), len(columns)), dtype=np.int64)
    for j, g in enumerate(columns):
        for e, c in g.items():
            M[position[e], j] = c
    rank, _ = eliminate(M, M.shape[1])
    assert (len(rows), rank) == (153, 153)
    return {'degreeSixteenForms': 153, 'rank': rank}


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--output')
    args = parser.parse_args()
    start = time.time()
    line = line_on_quartic()
    print('Line on a quartic surface: 19 kernel directions, all classes '
          'proportional to evaluation at the point of the line.', flush=True)
    cyclic = cyclic_three_links()
    print('Cyclic three-link sextic: the three ternary sextics span all 153 forms '
          'of degree sixteen; the fourfold is smooth.', flush=True)
    sextic = weighted_sextic()
    for row in sextic['pairs']:
        print(f"a_{row['a']}, Q_{row['Q']}: rank mu = {row['rankMu']}, kernel = {row['kernel']}, "
              f"cumulative span = {row['cumulativeSpan']}", flush=True)
    print(f"Span of the normal-function classes: {sextic['span']} of {sextic['dimH12Invariant']}.")
    print(f'All Hodge-locus checks passed in {time.time() - start:.0f}s.')
    if args.output:
        with open(args.output, 'w') as handle:
            json.dump({'lineOnQuartic': line, 'cyclicThreeLinks': cyclic,
                       'weightedSextic': sextic}, handle, indent=2)
            handle.write('\n')


if __name__ == '__main__':
    main()
