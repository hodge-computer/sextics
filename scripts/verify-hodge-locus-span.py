#!/usr/bin/env python3
"""Reconstruct the two finite inputs of Chapter 3D.

Python 3.9+ and NumPy; no witness files, extra packages, or network required.
Run: python3 scripts/verify-hodge-locus-span.py
Pass --output PATH to save the receipt.

Coordinates (x0, x1, x2, x3; w) have weights (1, 1, 1, 1; 2), and the
order-three symmetry g = (omega^2, omega^2, omega, 1; 1) gives them the
characters (2, 2, 1, 0; 0) modulo three.

1. The seed divisor.  With F0 = x0^6 + x1^6 + x2^6 + x3^6 + w^3 and an
   invariant cubic b, the sextic F0 + b^2 equals f1*g1 + f2*g2 + h*k for

       f1 = x0^2 - r*x1*x3,   g1 = x0^4 + r*x0^2*x1*x3 + r^2*x1^2*x3^2,
       f2 = w + x2^2,         g2 = w^2 - w*x2^2 + x2^4,
       h  = b - i*(x1^3 + x3^3),   k = b + i*(x1^3 + x3^3),

   where r^3 = 2 and i^2 = -1.  The script works modulo 109 with r = 57 and
   i = 33.  It computes the trace tau on the socle of the Artinian algebra
   A = S/(f1, f2, g1, g2, h), in degree nine, and the 8 x 9 matrix whose rows
   are the functionals

       L -> tau(k*L*sigma)    for the seven cubic monomials sigma of character one,
       L -> tau(x2*x3^3*w*L)

   on the nine invariant cubic monomials L.  Rank eight says that the
   Noether-Lefschetz map of the divisor class is surjective and that the
   derivative of the normal function is nonzero on its kernel.  A rank modulo
   a prime is a lower bound for the rank in characteristic zero.

2. The Higgs field at the Fermat member.  E is the span of the 33 standard
   monomials of degree six and character one in R = Q[x, w]/(x_i^5, w^2).  For
   each of the 35 invariant standard monomials m of degree six, H_m(a, b) is
   one if a*b*m = x0^4*x1^4*x2^4*x3^4*w and zero otherwise.  Every equation of
   the system P^T H_m = H_m P identifies two entries of P or annihilates one,
   so its solutions are found exactly by merging entries.  The script checks
   that the only solutions are the scalar matrices.
"""
import argparse
import json
import time
import numpy as np

P = 109
R_CUBE_ROOT_OF_TWO = 57
I_SQUARE_ROOT_OF_MINUS_ONE = 33
WEIGHTS = (1, 1, 1, 1, 2)
CHARACTERS = (2, 2, 1, 0, 0)


def monomials(degree, character=None):
    """Exponent vectors of this weighted degree, in lexicographic order."""
    out = []

    def extend(i, remaining, current):
        if i == 5:
            if remaining == 0 and (character is None or
                                   (sum(a*b for a, b in zip(current, CHARACTERS)) - character) % 3 == 0):
                out.append(tuple(current))
            return
        for a in range(remaining // WEIGHTS[i] + 1):
            extend(i + 1, remaining - a*WEIGHTS[i], current + [a])

    extend(0, degree, [])
    return out


def degree_of(poly):
    return sum(a*b for a, b in zip(next(iter(poly)), WEIGHTS))


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


def poly(terms):
    return {e: c % P for e, c in terms.items() if c % P}


def eliminate(M):
    """Gauss-Jordan elimination modulo P; returns the rank and pivot columns."""
    M %= P
    rank, pivots = 0, []
    for c in range(M.shape[1]):
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
            M[rows] = (M[rows] - M[rows, c][:, None] * M[rank][None, :]) % P
        pivots.append(c)
        rank += 1
        if rank == M.shape[0]:
            break
    return rank, pivots


def nullspace(A):
    A = A.copy() % P
    _, pivots = eliminate(A)
    basis = []
    for free in [j for j in range(A.shape[1]) if j not in pivots]:
        v = [0]*A.shape[1]
        v[free] = 1
        for i, c in enumerate(pivots):
            v[c] = int(-A[i, free]) % P
        basis.append(v)
    return basis


def seed_divisor():
    r, im = R_CUBE_ROOT_OF_TWO, I_SQUARE_ROOT_OF_MINUS_ONE
    assert pow(r, 3, P) == 2 and (im*im + 1) % P == 0
    F0 = poly({(6, 0, 0, 0, 0): 1, (0, 6, 0, 0, 0): 1, (0, 0, 6, 0, 0): 1,
               (0, 0, 0, 6, 0): 1, (0, 0, 0, 0, 3): 1})
    # b = 5 x0^3 + 10 x0^2 x1 + 25 x0 x1^2 + 20 x0 x2 x3 + 30 x1^3 + 25 x1 x2 x3
    #     - 25 x2^3 - 20 x3^3 + 10 x3 w
    b = poly({(3, 0, 0, 0, 0): 5, (2, 1, 0, 0, 0): 10, (1, 2, 0, 0, 0): 25,
              (1, 0, 1, 1, 0): 20, (0, 3, 0, 0, 0): 30, (0, 1, 1, 1, 0): 25,
              (0, 0, 3, 0, 0): -25, (0, 0, 0, 3, 0): -20, (0, 0, 0, 1, 1): 10})
    assert set(b) == set(monomials(3, 0))
    f1 = poly({(2, 0, 0, 0, 0): 1, (0, 1, 0, 1, 0): -r})
    g1 = poly({(4, 0, 0, 0, 0): 1, (2, 1, 0, 1, 0): r, (0, 2, 0, 2, 0): r*r})
    f2 = poly({(0, 0, 0, 0, 1): 1, (0, 0, 2, 0, 0): 1})
    g2 = poly({(0, 0, 0, 0, 2): 1, (0, 0, 2, 0, 1): -1, (0, 0, 4, 0, 0): 1})
    B = poly({(0, 3, 0, 0, 0): im, (0, 0, 0, 3, 0): im})
    h, k = add(b, B, -1), add(b, B)
    assert add(add(mul(f1, g1), mul(f2, g2)), mul(h, k)) == add(F0, mul(b, b))
    # The Artinian algebra A = S/(f1, f2, g1, g2, h): Hilbert function and socle.
    generators = (f1, f2, g1, g2, h)
    hilbert = []
    trace = None
    for degree in range(11):
        columns = monomials(degree)
        position = {m: j for j, m in enumerate(columns)}
        rows = [mul({m: 1}, g) for g in generators if degree_of(g) <= degree
                for m in monomials(degree - degree_of(g))]
        M = np.zeros((max(len(rows), 1), len(columns)), dtype=np.int64)
        for i, row in enumerate(rows):
            for e, c in row.items():
                M[i, position[e]] = c
        if degree == 9:
            kernel = nullspace(M)
            assert len(kernel) == 1
            trace = dict(zip(columns, kernel[0]))
        rank, _ = eliminate(M)
        hilbert.append(len(columns) - rank)
    assert sum(hilbert) == 96 and hilbert[9] == 1 and hilbert[10] == 0

    def tau(q):
        return sum(trace[e]*c for e, c in q.items()) % P

    cubics = monomials(3, 0)
    forms = monomials(3, 1)
    A0 = {(0, 0, 1, 3, 1): 1}
    assert (len(cubics), len(forms)) == (9, 7) and A0.keys() <= set(monomials(6, 1))
    table = [[tau(mul(mul(k, {L: 1}), {s: 1})) for L in cubics] for s in forms]
    noether_lefschetz_rank, _ = eliminate(np.array(table, dtype=np.int64))
    table.append([tau(mul(A0, {L: 1})) for L in cubics])
    rank, _ = eliminate(np.array(table, dtype=np.int64))
    assert (noether_lefschetz_rank, rank) == (7, 8)
    return {'prime': P, 'r': r, 'i': im, 'length': sum(hilbert), 'socleDegree': 9,
            'noetherLefschetzRank': noether_lefschetz_rank, 'rankWithDerivativeRow': rank}


def higgs_field():
    def standard(character):
        return [m for m in monomials(6, character) if max(m[:4]) <= 4 and m[4] <= 1]

    E, directions = standard(1), standard(0)
    socle = (4, 4, 4, 4, 1)
    n = len(E)
    assert (n, len(directions)) == (33, 35)
    position = {m: i for i, m in enumerate(E)}
    zero = n*n                       # an extra node standing for the value zero
    parent = list(range(n*n + 1))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for m in directions:
        # H_m(a, b) = 1 exactly when b is the partner of a.
        partner = {}
        for a in E:
            c = tuple(s - x - y for s, x, y in zip(socle, m, a))
            if c in position:
                partner[a] = c
        # (P^T H_m - H_m P)[a, b] = P[partner(b), a] - P[partner(a), b].
        for a in E:
            for c in E:
                left = position[partner[c]]*n + position[a] if c in partner else zero
                right = position[partner[a]]*n + position[c] if a in partner else zero
                parent[find(left)] = find(right)
    free = {}
    for entry in range(n*n):
        if find(entry) != find(zero):
            free.setdefault(find(entry), []).append(entry)
    assert len(free) == 1
    assert sorted(next(iter(free.values()))) == [i*n + i for i in range(n)]
    return {'dimension': n, 'directions': len(directions), 'solutionDimension': len(free)}


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--output')
    args = parser.parse_args()
    start = time.time()
    seed = seed_divisor()
    print(f"Seed divisor modulo {seed['prime']}: the algebra has length {seed['length']} and socle "
          f"degree {seed['socleDegree']}; the Noether-Lefschetz map has rank "
          f"{seed['noetherLefschetzRank']}, and rank {seed['rankWithDerivativeRow']} with the "
          f"derivative row.", flush=True)
    higgs = higgs_field()
    print(f"Higgs field at the Fermat member: on the {higgs['dimension']}-dimensional space, the "
          f"matrices P with P^T H_m = H_m P for all {higgs['directions']} monomial directions are "
          f"the scalars.")
    print(f'All Hodge-locus checks passed in {time.time() - start:.0f}s.')
    if args.output:
        with open(args.output, 'w') as handle:
            json.dump({'seedDivisor': seed, 'higgsField': higgs}, handle, indent=2)
            handle.write('\n')


if __name__ == '__main__':
    main()
