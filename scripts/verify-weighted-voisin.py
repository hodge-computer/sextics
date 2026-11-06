#!/usr/bin/env python3
"""Reconstruct exact rank witnesses for the Voisin and weighted calculations.

Python 3.8+; standard library only. No input files or network access required.
Run: python3 scripts/verify-weighted-voisin.py
Pass --output PATH to save the reconstructed minor indices as JSON.

Every matrix is the reduction of an integral multiplication matrix. A recorded
maximal minor nonzero modulo a prime proves the claimed rank over Q.
This script checks finite-dimensional algebra, not the geometric proof.
"""

from itertools import product
from math import factorial, prod
from pathlib import Path
import argparse
import json


class Ring:
    """A monomial complete intersection, with a double-swap involution."""

    def __init__(self, caps, weights):
        self.caps = tuple(caps)
        self.weights = tuple(weights)
        self.n = len(caps)
        self.monomials = list(product(*(range(c + 1) for c in caps)))

    @staticmethod
    def sigma(exponent):
        return (exponent[1], exponent[0], exponent[3], exponent[2],
                exponent[4], exponent[5])

    def degree(self, exponent):
        return sum(a * w for a, w in zip(exponent, self.weights))

    def basis(self, degree, sign):
        answer = []
        for a in self.monomials:
            if self.degree(a) != degree:
                continue
            b = self.sigma(a)
            if a == b and sign == 1:
                answer.append({a: 1})
            elif a < b:
                answer.append({a: 1, b: sign})
        return answer

    def linear(self, coefficients):
        answer = {}
        for i, c in enumerate(coefficients):
            if c:
                a = tuple(int(j == i) for j in range(self.n))
                answer[a] = c
        return answer

    def linear_power(self, coefficients, power):
        """Ordinary power; coefficients may be zero in weighted variables."""
        answer = {}
        for a in self.monomials:
            if sum(a) != power:
                continue
            denominator = 1
            for e in a:
                denominator *= factorial(e)
            c = factorial(power) // denominator
            for b, e in zip(coefficients, a):
                c *= b ** e
            if c:
                answer[a] = c
        return answer

    def multiply(self, left, right):
        answer = {}
        for a, ca in left.items():
            for b, cb in right.items():
                e = tuple(x + y for x, y in zip(a, b))
                if any(x > cap for x, cap in zip(e, self.caps)):
                    continue
                answer[e] = answer.get(e, 0) + ca * cb
        return {e: c for e, c in answer.items() if c}

    @staticmethod
    def add(left, right):
        answer = left.copy()
        for e, c in right.items():
            answer[e] = answer.get(e, 0) + c
        return {e: c for e, c in answer.items() if c}

    def matrix(self, polynomial, source_degree, target_degree, prime):
        source = self.basis(source_degree, +1)
        target = self.basis(target_degree, -1)
        reps = [next(iter(b)) for b in target]
        answer = [[0] * len(source) for _ in target]
        assert all(self.degree(e) == target_degree - source_degree
                   for e in polynomial)
        assert all(polynomial.get(self.sigma(e), 0) == -c
                   for e, c in polynomial.items())
        for j, b in enumerate(source):
            result = self.multiply(polynomial, b)
            # Check that the product actually lies in the minus eigenspace.
            assert all(result.get(self.sigma(e), 0) == -c
                       for e, c in result.items())
            for i, e in enumerate(reps):
                answer[i][j] = result.get(e, 0) % prime
        return answer


def determinant(matrix, prime):
    a = [row[:] for row in matrix]
    n = len(a)
    result = 1
    for j in range(n):
        k = next((i for i in range(j, n) if a[i][j] % prime), None)
        if k is None:
            return 0
        if k != j:
            a[j], a[k] = a[k], a[j]
            result = -result
        pivot = a[j][j] % prime
        result = result * pivot % prime
        inverse = pow(pivot, -1, prime)
        for i in range(j + 1, n):
            factor = a[i][j] * inverse % prime
            if factor:
                for k in range(j + 1, n):
                    a[i][k] = (a[i][k] - factor * a[j][k]) % prime
    return result % prime


def rank_receipt(matrix, prime):
    a = [row[:] for row in matrix]
    row_ids = list(range(len(a)))
    rank = 0
    columns = []
    for j in range(len(a[0])):
        k = next((i for i in range(rank, len(a)) if a[i][j] % prime), None)
        if k is None:
            continue
        a[rank], a[k] = a[k], a[rank]
        row_ids[rank], row_ids[k] = row_ids[k], row_ids[rank]
        inverse = pow(a[rank][j], -1, prime)
        a[rank] = [inverse * x % prime for x in a[rank]]
        for i in range(rank + 1, len(a)):
            factor = a[i][j]
            if factor:
                a[i] = [(x - factor * y) % prime
                        for x, y in zip(a[i], a[rank])]
        columns.append(j)
        rank += 1
        if rank == len(a):
            break
    rows = row_ids[:rank]
    minor = [[matrix[i][j] for j in columns] for i in rows]
    det = determinant(minor, prime)
    assert det != 0
    return {
        "source_dimension": len(matrix[0]),
        "target_dimension": len(matrix),
        "rank": rank,
        "minor_rows_zero_based": rows,
        "minor_columns_zero_based": columns,
        "minor_determinant_mod_prime": det,
    }


def run_case(name, ring, q, h, source_degree, targets, prime, expected):
    receipts = {}
    for label, polynomial, degree, want in zip(
        ("Q", "HQ"), (q, ring.multiply(h, q)), targets, expected
    ):
        receipt = rank_receipt(ring.matrix(polynomial, source_degree, degree, prime), prime)
        observed = (receipt["source_dimension"], receipt["target_dimension"],
                    receipt["rank"], receipt["minor_determinant_mod_prime"])
        assert observed == want, (name, label, observed, want)
        receipts[label] = receipt
        print("{} {}: {} -> {}, rank {}, minor {} mod {}".format(
            name, label, *observed, prime))
    return {
        "caps": ring.caps, "weights": ring.weights,
        "prime": prime, "maps": receipts,
    }


def compositions(n, degree, cap=None):
    if n == 1:
        if cap is None or degree <= cap:
            yield (degree,)
        return
    for a in range((min(degree, cap) if cap is not None else degree) + 1):
        for b in compositions(n - 1, degree - a, cap):
            yield (a,) + b


def extension_dimensions():
    """Necessary dimension test for the direct ordinary sixfold extension."""
    def character(exponent, signs):
        return prod(s ** a for s, a in zip(signs, exponent))

    base = (1, 1, 1, -1, -1, -1)
    fixed = sum(character(e, base) == 1 for e in compositions(6, 6))
    assert fixed == 236
    receipts = []
    for added, automorphisms in (((1, 1), 10), ((1, -1), 8), ((-1, -1), 10)):
        signs = base + added
        raw = sum(character(e, signs) == 1 for e in compositions(8, 6)) - fixed
        # The residue volume contributes det(sigma), so keep this twist.
        h42 = sum(character(e, signs) * prod(signs) == 1
                  for e in compositions(8, 10, 4))
        h51 = sum(character(e, signs) * prod(signs) == 1
                  for e in compositions(8, 4, 4))
        observed = (raw, raw - automorphisms, h42, h51)
        expected = ((632, 624, 6596, 170) if added == (1, -1)
                    else (647, 637, 6503, 155))
        assert observed == expected
        receipts.append({
            "added_signs": added, "raw_extension_dimension": raw,
            "effective_extension_dimension": raw - automorphisms,
            "invariant_h42": h42, "invariant_h51": h51,
        })
        print("Sixfold signs {}: {} raw directions, {} effective, h42={}, h51={}".format(
            added, *observed))
    return receipts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Optional JSON receipt path")
    args = parser.parse_args()
    quintic = Ring((3,) * 6, (1,) * 6)
    d5 = quintic.linear((1, -1, 1, -1, 0, 0))
    q5 = quintic.multiply(d5, quintic.linear_power((1,) * 6, 8))
    h5 = quintic.linear((1, 1, 1, 1, 0, 1))
    qreceipt = run_case(
        "ordinary quintic", quintic, q5, h5, 4, (13, 14), 101,
        ((66, 100, 66, 85), (66, 54, 54, 77)),
    )
    qreceipt["formula"] = "L=sum(z0,...,z5), D=z0-z1+z2-z3, Q=D*L^8, H=L-z4"

    weighted = Ring((4, 4, 4, 4, 4, 1), (1, 1, 1, 1, 1, 2))
    d6 = weighted.linear((1, -1, 1, -1, 0, 0))
    h6 = weighted.linear((1, 1, 1, 1, 0, 0))
    lco = (1, 1, 1, 1, 1, 0)
    five_u = {(0, 0, 0, 0, 0, 1): 5}
    q6 = weighted.multiply(d6, weighted.add(
        weighted.linear_power(lco, 10),
        weighted.multiply(five_u, weighted.linear_power(lco, 8)),
    ))
    wreceipt = run_case(
        "weighted sextic", weighted, q6, h6, 5, (16, 17), 1009,
        ((82, 120, 82, 45), (82, 74, 74, 286)),
    )
    wreceipt["formula"] = "L=sum(z0,...,z4), D=z0-z1+z2-z3, Q=D*(L^2+u)^5, H=L-z4"

    wreceipt101 = run_case(
        "weighted sextic", weighted, q6, h6, 5, (16, 17), 101,
        ((82, 120, 82, 62), (82, 74, 74, 89)),
    )

    result = {
        "basis": "Lexicographic exponent tuples; sigma swaps 0,1 and 2,3. "
                 "For a<sigma(a), use z^a+/-z^sigma(a). "
                 "Fixed monomials occur only in the plus basis.",
        "ordinary_quintic": qreceipt,
        "weighted_sextic_mod1009": wreceipt,
        "weighted_sextic_mod101": wreceipt101,
        "ordinary_sixfold_extension": extension_dimensions(),
    }
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
        print("Wrote exact minor indices to " + str(args.output))
    print("All exact rank checks passed.")


if __name__ == "__main__":
    main()
