#!/usr/bin/env python3
"""Exact finite-trace countermodel, not a target certificate.

Pure standard-library arithmetic. Laurent monomials use the coordinates
(r,s,alpha) with alpha**48=r. No floating-point or external CAS is used.
"""

from fractions import Fraction
from hashlib import sha256
from math import factorial, prod
from pathlib import Path
import json

N = 48
HERE = Path(__file__).resolve().parent


def reduce_monomial(coefficient, r_power=0, s_power=0, alpha_power=0):
    q, a = divmod(alpha_power, N)
    return (Fraction(coefficient), r_power + q, s_power, a)


def trace(monomial):
    c, r, s, a = monomial
    return (N * c, r, s) if a == 0 else (Fraction(0), 0, 0)


def operand(j):
    return (1, 0, 0 if j == 0 else 1, j)


def multiply(x, y):
    c, r, s, a = x
    cc, rr, ss, aa = y
    return reduce_monomial(c * cc, r + rr, s + ss, a + aa)


def main():
    matrix = []
    nonzero_positions = []
    for i in range(N):
        row = []
        for j in range(N):
            value = trace(multiply(reduce_monomial(1, alpha_power=i), operand(j)))
            expected = (Fraction(0), 0, 0)
            if i == 0 and j == 0:
                expected = (Fraction(N), 0, 0)
            elif i + j == N:
                expected = (Fraction(N), 1, 1)
            assert value == expected, (i, j, value, expected)
            row.append(value)
            if value[0]:
                nonzero_positions.append((i, j))
        matrix.append(row)
    assert len(nonzero_positions) == N
    permutation = [next(j for j in range(N) if matrix[i][j][0]) for i in range(N)]
    assert len(set(permutation)) == N
    inversions = sum(permutation[i] > permutation[j] for i in range(N) for j in range(i + 1, N))
    sign = (-1) ** inversions
    assert sign == -1 and inversions == 1081

    f = reduce_monomial(Fraction(1, N), s_power=-1, alpha_power=-1)
    image = [trace(multiply(operand(j), f)) for j in range(N)]
    assert image == [(Fraction(int(j == 1)), 0, 0) for j in range(N)]

    # The coefficient of ds wedge d(alpha) in d(f d(alpha)).
    c, r, s, a = f
    derivative_s = reduce_monomial(c * s, r, s - 1, a)
    expected_derivative = reduce_monomial(Fraction(-1, N), s_power=-2, alpha_power=-1)
    assert derivative_s == expected_derivative and derivative_s[0] != 0

    # W[k,j] = D_alpha^k(alpha^j)|_{alpha=1}.
    wronskian = [[0 if k > j else factorial(j) // factorial(j - k)
                  for j in range(N)] for k in range(N)]
    assert all(wronskian[k][j] == 0 for k in range(N) for j in range(k))
    determinant = prod(factorial(j) for j in range(N))
    assert determinant != 0

    receipt = {
        "status": "PASS",
        "scope": "Exact countermodel to unrestricted trace weights implying closed contact weights; not a symmetric-sextic obstruction",
        "degree": N,
        "trace_pairing_entries_checked": N * N,
        "trace_pairing_determinant": "-48^48*r^47*s^47",
        "permutation_inversions": inversions,
        "wronskian_determinant": "product(factorial(j),j=0..47)",
        "wronskian_determinant_sha256": sha256(str(determinant).encode()).hexdigest(),
        "unrestricted_weight": "1/(48*s*alpha)",
        "computed_trace_vector": "e_1 with zero-based indices 0..47",
        "closedness_defect": "-ds wedge d(alpha)/(48*s^2*alpha)",
        "allowed_weight_obstruction": "For f in k(alpha), Tr(s*alpha*f) is in s*k(r), hence cannot be 1",
        "source_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    output = HERE / "trace_closedness_counterexample_receipt.json"
    output.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
