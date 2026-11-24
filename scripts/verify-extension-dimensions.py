#!/usr/bin/env python3
"""Reconstruct the dimension counts of Chapter 4, section 4.6.

1. The ordinary sixfold dimension obstruction.
2. Moving weighted-Fano fourfold extensions W_6 subset P(1^5, 3) and
   W_{(2,6)} subset P(1^6, 3).
3. Motions against invariant two-forms for the surface sections
   D = X ∩ {h1 = h2 = 0} of an even sextic fourfold, from the parity-graded
   dimensions of C[Z]/(F, h1, h2) given by the Koszul formula.

Pure integer monomial enumeration; no third-party dependencies or input files.
Run: python3 scripts/verify-extension-dimensions.py
"""

from math import prod


def compositions(n, degree, cap=None):
    if n == 1:
        if cap is None or degree <= cap:
            yield (degree,)
        return
    for a in range((min(degree, cap) if cap is not None else degree) + 1):
        for b in compositions(n - 1, degree - a, cap):
            yield (a,) + b


def character(exponent, signs):
    return prod(s ** a for s, a in zip(signs, exponent))


def surface_sections():
    """Largest value of motions minus invariant two-forms, for each bidegree."""
    counts = {}

    def monomials(degree, parity):
        """Number of monomials of this degree with this parity of the Y-degree."""
        if degree < 0:
            return 0
        if degree not in counts:
            odd = sum(sum(e[3:]) % 2 for e in compositions(6, degree))
            counts[degree] = (sum(1 for _ in compositions(6, degree)) - odd, odd)
        return counts[degree][parity]

    def quotient(degree, parity, relations):
        """Graded dimension of the quotient by a regular sequence of (degree, parity)."""
        total = 0
        for subset in range(1 << len(relations)):
            d, p, sign = degree, parity, 1
            for j, (e, a) in enumerate(relations):
                if subset >> j & 1:
                    d, p, sign = d - e, p ^ a, -sign
            total += sign * monomials(d, p)
        return total

    best = {}
    for e1 in range(1, 5):
        for e2 in range(e1, 5):
            for a1 in (0, 1):
                for a2 in (0, 1):
                    relations = [(6, 0), (e1, a1), (e2, a2)]
                    motions = quotient(e1, a1, relations) + quotient(e2, a2, relations)
                    # tau negates the volume form, so invariant two-forms have
                    # numerators of parity 1 + a1 + a2.
                    forms = quotient(e1 + e2, 1 ^ a1 ^ a2, relations)
                    if (e1, e2) == (1, 1):
                        assert (motions, forms) == ((2, 3) if a1 == a2 else (4, 6))
                    best[e1, e2] = max(best.get((e1, e2), motions - forms), motions - forms)
    expected = {(1, 1): -1, (1, 2): -6, (1, 3): -12, (1, 4): -24, (2, 2): -22,
                (2, 3): -54, (2, 4): -93, (3, 3): -118, (3, 4): -216, (4, 4): -379}
    assert best == expected, best
    # Linear sections that are not tau-stable: h^0(N) = 4 + 4 and p_g = 10.
    plain = [sum(1 for _ in compositions(6, d)) for d in range(3)]
    assert (2 * (plain[1] - 2), plain[2] - 2 * plain[1] + plain[0]) == (8, 10)
    return best


def weighted_fano_extensions():
    """Verify moving weighted-Fano fourfold extension counts in P(1^5,3) and P(1^6,3)."""
    def sgn_cnt(signs, degree, target):
        return sum(character(e, signs) == target
                   for e in compositions(len(signs), degree))

    # 1. W_6 = {H_1 = 0, F + t*A_3 + t^2 = 0} subset P(1^5, 3):
    #    unrestricted: dim(H_1) = 5, dim(A_3 on P^4) = 35, h^{3,1}(W_6) = dim S_4(P^4) = 70.
    dim_A3_P4 = sum(1 for _ in compositions(5, 3))
    h31_W6 = sum(1 for _ in compositions(5, 4))
    assert (5 + dim_A3_P4, h31_W6) == (40, 70)
    for signs5 in ((1, 1, -1, -1, -1), (1, 1, 1, -1, -1)):
        det5 = prod(signs5)
        for t_sgn in (1, -1):
            params = 2 + sgn_cnt(signs5, 3, t_sgn)
            h31_tau = sgn_cnt(signs5, 4, det5 * t_sgn)
            expected = (18, 32) if det5 * t_sgn == -1 else (21, 38)
            assert (params, h31_tau) == expected, (signs5, t_sgn, params, h31_tau)

    # 2. W_{(2,6)} = {Q_2 = 0, F + t*A_3 + t^2 = 0} subset P(1^6, 3):
    #    unrestricted: dim P(S_2) = 20, dim(S_3 / Q_2 S_1) = 56 - 6 = 50,
    #    Cayley bidegree (1,5): h^{3,1} = dim S_1 + dim S_5 - dim S_3 - 6 = 6 + 252 - 56 - 6 = 196.
    s_tot = {d: sum(1 for _ in compositions(6, d)) for d in (1, 2, 3, 5)}
    assert (s_tot[2] - 1, s_tot[3] - s_tot[1]) == (20, 50)
    assert s_tot[1] + s_tot[5] - s_tot[3] - 6 == 196
    base = (1, 1, 1, -1, -1, -1)
    det6 = prod(base)
    for q_sgn in (1, -1):
        dim_Q = sgn_cnt(base, 2, q_sgn) - 1
        for t_sgn in (1, -1):
            dim_A3 = sgn_cnt(base, 3, t_sgn) - sgn_cnt(base, 1, t_sgn * q_sgn)
            sB5 = det6 * t_sgn * q_sgn
            sB1 = det6 * t_sgn
            sB3 = sB5 * q_sgn
            dG_cnt = sum(1 for s in base if s == sB5)
            h31_tau = (sgn_cnt(base, 1, sB1) + sgn_cnt(base, 5, sB5)
                       - sgn_cnt(base, 3, sB3) - dG_cnt)
            expected = (36, 98) if q_sgn == 1 else (33, 98)
            assert (dim_Q + dim_A3, h31_tau) == expected, (q_sgn, t_sgn, dim_Q + dim_A3, h31_tau)


def main():
    base = (1, 1, 1, -1, -1, -1)
    fixed = sum(character(e, base) == 1 for e in compositions(6, 6))
    assert fixed == 236
    for added, automorphisms in (((1, 1), 10), ((1, -1), 8), ((-1, -1), 10)):
        signs = base + added
        raw = sum(character(e, signs) == 1 for e in compositions(8, 6)) - fixed
        # Residue volume contributes det(sigma); retain that character twist.
        h42 = sum(character(e, signs) * prod(signs) == 1
                  for e in compositions(8, 10, 4))
        h51 = sum(character(e, signs) * prod(signs) == 1
                  for e in compositions(8, 4, 4))
        observed = (raw, raw - automorphisms, h42, h51)
        expected = ((632, 624, 6596, 170) if added == (1, -1)
                    else (647, 637, 6503, 155))
        assert observed == expected, (added, observed, expected)
        print(f"Signs {added}: {raw + fixed} coefficients; "
              f"{raw} fixed-section directions; {raw - automorphisms} effective; "
              f"h42={h42}; h51={h51}")
    weighted_fano_extensions()
    print("Weighted Fano extensions: W_6 in P(1^5,3) (40 vs 70; tau: 18 vs 32 / 21 vs 38); "
          "W_(2,6) in P(1^6,3) (70 vs 196; tau: 36 or 33 vs 98).")
    best = surface_sections()
    print("Surface sections, motions minus invariant two-forms: "
          + ", ".join(f"{e}: {v}" for e, v in sorted(best.items())))
    print("All extension dimension counts passed.")


if __name__ == "__main__":
    main()
