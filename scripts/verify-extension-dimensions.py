#!/usr/bin/env python3
"""Reconstruct the ordinary sixfold dimension obstruction in Chapter 4.

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
    print("All extension dimension counts passed.")


if __name__ == "__main__":
    main()
