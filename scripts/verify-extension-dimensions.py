#!/usr/bin/env python3
"""Reconstruct the dimension counts of Chapter 4, section 4.6.

1. The ordinary sixfold dimension obstruction.
2. Motions against invariant two-forms for the surface sections
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
    best = surface_sections()
    print("Surface sections, motions minus invariant two-forms: "
          + ", ".join(f"{e}: {v}" for e, v in sorted(best.items())))
    print("All extension dimension counts passed.")


if __name__ == "__main__":
    main()
