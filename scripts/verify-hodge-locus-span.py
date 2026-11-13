#!/usr/bin/env python3
"""Reconstruct the finite results of Chapter 3D.

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

3. The fourfold through the Fermat member.  A further coordinate t has weight
   three and character zero.  On Ft = F0 + t*a + t^2 with

       a = 5*(x0^3 + x1^3 + x2^3 + x3^3 + x0*x2*x3 + x1*x2*x3 + x3*w)

   and Q = x2*w^4, the script computes modulo 109 the map mu_Q : K -> [t*K*Q]
   from the ten invariant cubics to R(Ft)_15, its kernel, a solution of
   t*K*Q = sum_z c_z * dFt/dz for each kernel vector, and the class of c_t at
   t = 0 in R(F0)_12.  It checks that mu_Q has rank seven, that the classes
   span a space of dimension two, and that each of the 33 standard monomials
   has a nonzero coefficient in one of them.  The diagonal automorphisms of
   F0 act on those monomials through pairwise distinct characters.

4. The fourfold through the seed.  On

       Ft = F0 + b^2 + 2*b*t + t^2 = (t + h)*(t + k) + f1*g1 + f2*g2,

   Q is the part of character one of the Jacobian determinant of
   (f1, g1, f2, g2, t + h, t + k).  The script checks that mu_Q has rank seven,
   that its kernel is spanned by dFt/dt, by x1^3 + x3^3 and by one further
   cubic, that the classes of the first two vanish in R(F0 + b^2)_12, and that
   the class B of the third is nonzero with A -> soc(A*B) proportional to
   A -> tau(A*L).  Here A runs over the sextic monomials of character one, soc
   is the socle form of R(F0 + b^2), and L spans the kernel of the
   Noether-Lefschetz map modulo h.
"""
import argparse
import json
import time
import numpy as np

P = 109
R_CUBE_ROOT_OF_TWO = 57
I_SQUARE_ROOT_OF_MINUS_ONE = 33
WEIGHTS = (1, 1, 1, 1, 2, 3)          # the last coordinate is t
CHARACTERS = (2, 2, 1, 0, 0, 0)
T = (0, 0, 0, 0, 0, 1)


def character_of(exponents):
    return sum(a*b for a, b in zip(exponents, CHARACTERS)) % 3


def monomials(degree, character=None, variables=5):
    """Exponent vectors of this weighted degree, in lexicographic order."""
    out = []

    def extend(i, remaining, current):
        if i == variables:
            if remaining == 0 and (character is None or character_of(current) == character % 3):
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


def diff(a, i):
    r = {}
    for e, c in a.items():
        if e[i] % P:
            f = list(e)
            f[i] -= 1
            r[tuple(f)] = c*e[i] % P
    return r


def with_t(a):
    """A polynomial in (x, w), as a polynomial in (x, w, t)."""
    return {e + (0,): c for e, c in a.items()}


def determinant(rows):
    """Determinant of a square matrix of polynomials, by expansion along rows."""
    n = len(rows)
    one = {tuple([0]*len(WEIGHTS)): 1}
    minors = {(): one}
    for i in reversed(range(n)):
        step = {}
        for columns, minor in minors.items():
            for j in range(n):
                if j in columns or not rows[i][j]:
                    continue
                key = tuple(sorted(columns + (j,)))
                sign = -1 if sum(c < j for c in columns) % 2 else 1
                step[key] = add(step.get(key, {}), mul(rows[i][j], minor), sign)
        minors = step
    return minors.get(tuple(range(n)), {})


def matrix_of(polynomials, columns):
    position = {m: j for j, m in enumerate(columns)}
    M = np.zeros((max(len(polynomials), 1), len(columns)), dtype=np.int32)
    for i, q in enumerate(polynomials):
        for e, c in q.items():
            M[i, position[e]] = c
    return M


def eliminate(M, pivot_columns=None):
    """Gauss-Jordan elimination modulo P, in place; returns the rank and pivot columns.

    With pivot_columns, pivots are taken only among the first columns.  Entries
    stay in [0, P), so every product is below 2^14.
    """
    M %= P
    rank, pivots = 0, []
    for c in range(M.shape[1] if pivot_columns is None else pivot_columns):
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
            # The pivot row vanishes to the left of column c.
            M[rows, c:] = (M[rows, c:] - M[rows, c][:, None] * M[rank, c:][None, :]) % P
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
        rows = [mul({m: 1}, g) for g in generators if degree_of(g) <= degree
                for m in monomials(degree - degree_of(g))]
        M = matrix_of(rows, columns)
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
    kernel = [{L: c for L, c in zip(cubics, v) if c}
              for v in nullspace(np.array(table, dtype=np.int32))]
    noether_lefschetz_rank, _ = eliminate(np.array(table, dtype=np.int32))
    table.append([tau(mul(A0, {L: 1})) for L in cubics])
    rank, _ = eliminate(np.array(table, dtype=np.int32))
    assert (noether_lefschetz_rank, rank) == (7, 8)
    receipt = {'prime': P, 'r': r, 'i': im, 'length': sum(hilbert), 'socleDegree': 9,
               'noetherLefschetzRank': noether_lefschetz_rank, 'rankWithDerivativeRow': rank}
    return receipt, {'F': add(F0, mul(b, b)), 'b': b, 'B': B, 'h': h, 'k': k,
                     'factors': (f1, g1, f2, g2), 'tau': tau, 'kernel': kernel}


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


def normal_function(Ft, Q):
    """The map mu_Q on the invariant cubics in (x, w, t), and the classes on its kernel.

    Returns dim R(Ft)_15 of character one, the ten cubic monomials, a basis of
    the kernel of K -> [t*K*Q], and a function sending a kernel vector to
    c_t at t = 0, for a solution of t*K*Q = sum_z c_z * dFt/dz.
    """
    cubics = monomials(3, 0, 6)
    rows = monomials(15, 1, 6)
    generators = []
    for z in range(6):
        dz = diff(Ft, z)
        for m in monomials(15 - degree_of(dz), 1 - character_of(next(iter(dz))), 6):
            generators.append((z, m, mul({m: 1}, dz)))
    columns = [g for _, _, g in generators] + [mul(mul({T: 1}, {K: 1}), Q) for K in cubics]
    M = matrix_of(columns, rows).T.copy()
    rank_J, pivots = eliminate(M, len(generators))
    block = M[:, len(generators):]
    kernel = nullspace(block[rank_J:])

    def beta(v):
        v = np.array(v, dtype=np.int32) % P
        assert not (block[rank_J:] @ v % P).any()        # v lies in the kernel
        solution = block[:rank_J] @ v % P
        c_t = {}
        for i, c in enumerate(pivots):
            z, m, _ = generators[c]
            if z == 5 and m[5] == 0 and solution[i]:
                c_t[m[:5]] = (c_t.get(m[:5], 0) + int(solution[i])) % P
        return {e: c for e, c in c_t.items() if c}

    return len(rows) - rank_J, cubics, kernel, beta


def fermat_fourfold():
    F0 = poly({(6, 0, 0, 0, 0): 1, (0, 6, 0, 0, 0): 1, (0, 0, 6, 0, 0): 1,
               (0, 0, 0, 6, 0): 1, (0, 0, 0, 0, 3): 1})
    # Modulo five the fourfold is F0 + t^2 = 0, which is quasismooth.
    a = poly({m: 5 for m in [(3, 0, 0, 0, 0), (0, 3, 0, 0, 0), (0, 0, 3, 0, 0), (0, 0, 0, 3, 0),
                             (1, 0, 1, 1, 0), (0, 1, 1, 1, 0), (0, 0, 0, 1, 1)]})
    Q = {(0, 0, 1, 0, 4, 0): 1}
    assert set(a) <= set(monomials(3, 0)) and set(Q) <= set(monomials(9, 1, 6))
    Ft = add(add(with_t(F0), mul({T: 1}, with_t(a))), {(0, 0, 0, 0, 0, 2): 1})
    dimension, cubics, kernel, beta = normal_function(Ft, Q)
    assert (len(cubics), dimension, len(kernel)) == (10, 7, 3)
    # J(F0) is spanned by the monomials divisible by some x_i^5 or by w^2.
    standard = [m for m in monomials(12, 1) if max(m[:4]) <= 4 and m[4] <= 1]
    assert len(standard) == 33
    # The diagonal group mu_6^4 x mu_3 sees exponents modulo (6, 6, 6, 6, 3).
    assert len({tuple(e % 6 for e in m[:4]) + (m[4] % 3,) for m in standard}) == 33
    M = np.array([[beta(v).get(m, 0) for m in standard] for v in kernel], dtype=np.int32)
    reached = int(np.count_nonzero(M.any(axis=0)))
    image_rank, _ = eliminate(M.copy())
    assert (image_rank, reached) == (2, 33)
    return {'prime': P, 'a': '5*(x0^3+x1^3+x2^3+x3^3+x0*x2*x3+x1*x2*x3+x3*w)', 'Q': 'x2*w^4',
            'dimR15': dimension, 'rankMu': len(cubics) - len(kernel), 'kernel': len(kernel),
            'imageRank': image_rank, 'standardMonomials': len(standard),
            'monomialsReached': reached}


def seed_fourfold(seed):
    F, b, B, h, k = (seed[name] for name in ('F', 'b', 'B', 'h', 'k'))
    t = {T: 1}
    th, tk = add(t, with_t(h)), add(t, with_t(k))
    factors = [with_t(q) for q in seed['factors']] + [th, tk]
    Ft = add(add(with_t(F), mul(t, with_t(add(b, b)))), mul(t, t))
    assert Ft == add(add(mul(factors[0], factors[1]), mul(factors[2], factors[3])), mul(th, tk))
    jacobian = determinant([[diff(q, z) for z in range(6)] for q in factors])
    Q = {e: c for e, c in jacobian.items() if character_of(e) == 1}
    assert Q and degree_of(Q) == 9
    dimension, cubics, kernel, beta = normal_function(Ft, Q)
    assert (dimension, len(kernel)) == (7, 3)

    def vector(q):
        return [q.get(m, 0) for m in cubics]

    # The socle form of R(F): the linear form on sextic times class that kills J(F).
    columns = monomials(18, 2)
    rows = []
    for z in range(5):
        dz = diff(F, z)
        rows += [mul({m: 1}, dz)
                 for m in monomials(18 - degree_of(dz), 2 - character_of(next(iter(dz))))]
    socle = nullspace(matrix_of(rows, columns))
    assert len(socle) == 1
    socle = dict(zip(columns, socle[0]))
    sextics = monomials(6, 1)

    def functional(v):
        c_t = beta(v)
        return [sum(socle[e]*c for e, c in mul({A: 1}, c_t).items()) % P for A in sextics]

    rescaling = vector(diff(Ft, 5))                      # dFt/dt = 2*b + 2*t
    difference = vector(with_t(B))                       # a multiple of h - k
    further = next(v for v in kernel if eliminate(
        np.array([rescaling, difference, v], dtype=np.int32))[0] == 3)
    assert not any(functional(rescaling)) and not any(functional(difference))
    fourfold = functional(further)
    surface = [[seed['tau'](mul({A: 1}, L)) for A in sextics] for L in seed['kernel']]
    assert any(fourfold)
    assert eliminate(np.array(surface, dtype=np.int32))[0] == 1
    assert eliminate(np.array([fourfold] + surface, dtype=np.int32))[0] == 1
    return {'prime': P, 'dimR15': dimension, 'rankMu': len(cubics) - len(kernel),
            'kernel': len(kernel), 'sextics': len(sextics), 'rankOfBothFunctionals': 1}


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--output')
    args = parser.parse_args()
    start = time.time()
    seed, context = seed_divisor()
    print(f"Seed divisor modulo {seed['prime']}: the algebra has length {seed['length']} and socle "
          f"degree {seed['socleDegree']}; the Noether-Lefschetz map has rank "
          f"{seed['noetherLefschetzRank']}, and rank {seed['rankWithDerivativeRow']} with the "
          f"derivative row.", flush=True)
    higgs = higgs_field()
    print(f"Higgs field at the Fermat member: on the {higgs['dimension']}-dimensional space, the "
          f"matrices P with P^T H_m = H_m P for all {higgs['directions']} monomial directions are "
          f"the scalars.", flush=True)
    fermat = fermat_fourfold()
    print(f"Fourfold through the Fermat member modulo {fermat['prime']}: mu_Q has rank "
          f"{fermat['rankMu']} and kernel of dimension {fermat['kernel']}; the classes span "
          f"dimension {fermat['imageRank']} and reach {fermat['monomialsReached']} of the "
          f"{fermat['standardMonomials']} standard monomials.", flush=True)
    fourfold = seed_fourfold(context)
    print(f"Fourfold through the seed modulo {fourfold['prime']}: mu_Q has rank "
          f"{fourfold['rankMu']}; the classes vanish on dFt/dt and on h - k, and on the further "
          f"kernel direction the class is proportional to A -> tau(A*L) on the "
          f"{fourfold['sextics']} sextics.")
    print(f'All Hodge-locus checks passed in {time.time() - start:.0f}s.')
    if args.output:
        with open(args.output, 'w') as handle:
            json.dump({'seedDivisor': seed, 'higgsField': higgs, 'fermatFourfold': fermat,
                       'seedFourfold': fourfold}, handle, indent=2)
            handle.write('\n')


if __name__ == '__main__':
    main()
