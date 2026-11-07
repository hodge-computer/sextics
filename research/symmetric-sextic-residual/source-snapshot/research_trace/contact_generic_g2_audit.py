#!/usr/bin/env python3
"""Independent generic characteristic-zero audit of quotient elimination.

The coefficient ring is QQ[mu0,...,mu4,R0,...,R43].  The 19 quotient
numerators are reconstructed with actual small determinant/adjugate matrices,
not the continuant inverse formula used by the modular solver.  Multiplying
Q2 by the resulting polynomial and collecting all 44 coefficients verifies
the elimination identity.  An optional FLINT comparison binds the solver to
the same generic equations over F101, with all 49 variables still symbolic.
"""
from hashlib import sha256
from itertools import product
from pathlib import Path
import json
import sys
import time

HERE = Path(__file__).resolve().parent
for dependency_directory in (HERE.parent / "research_workaround" / "python_deps",
                             HERE.parent / "proof_attempt3" / "python_deps"):
    if dependency_directory.exists():
        sys.path.insert(0, str(dependency_directory))
        break
import sympy as sp
from sympy.polys.rings import ring
from sympy.polys.domains import QQ


def monomials(d):
    return sorted(e for e in product(range(d + 1), repeat=4)
                  if sum(e) == d and (e[2] + e[3]) % 2 == 0)


def main():
    started = time.monotonic()
    exponents = monomials(6)
    assert len(exponents) == 44
    names = [f"mu{i}" for i in range(5)] + [f"R{i}" for i in range(44)]
    coefficient_ring, *generators = ring(",".join(names), QQ)
    V = dict(zip(names, generators))
    mu = generators[:5]
    R = dict(zip(exponents, generators[5:]))
    zero, one = coefficient_ring.zero, coefficient_ring.one
    Q = {(2, 0, 0, 0): mu[0], (1, 1, 0, 0): one, (0, 2, 0, 0): mu[1],
         (0, 0, 2, 0): mu[2], (0, 0, 1, 1): mu[3], (0, 0, 0, 2): mu[4]}
    z = mu[0] * mu[1]
    factors = (one-z, one-2*z, one-3*z)
    D = factors[0] * factors[1] * factors[2]
    x0, x1 = sp.symbols("mu0 mu1")
    Qx = {(2, 0): x0, (1, 1): sp.Integer(1), (0, 2): x1}
    matrices = {}
    for n in (5, 3, 1):
        rows = [(i+1, n-i) for i in range(n)]
        cols = [(j, n-1-j) for j in range(n)]
        matrix = sp.Matrix([[Qx.get((e[0]-f[0], e[1]-f[1]), sp.Integer(0))
                             for f in cols] for e in rows])
        det = sp.expand(matrix.det(method="bareiss"))
        adj = matrix.adjugate(method="berkowitz")
        assert (matrix * adj - sp.eye(n)*det).applyfunc(sp.expand) == sp.zeros(n)
        matrices[n] = (coefficient_ring.from_expr(det),
                       [[coefficient_ring.from_expr(sp.expand(adj[i, j])) for j in range(n)]
                        for i in range(n)])
    assert matrices[5][0] == factors[0]*factors[2]
    assert matrices[3][0] == factors[1]
    assert matrices[1][0] == one
    # Each group is solved after subtracting products already known at lower
    # c,d degree.  The multiplier coefficients have the common denominator D.
    N = {}
    minus = lambda e, f: tuple(a-b for a, b in zip(e, f))
    for degree_cd in (0, 2, 4):
        n = 5-degree_cd
        determinant, adjugate = matrices[n]
        for c_exp in range(degree_cd+1):
            d_exp = degree_cd-c_exp
            rows = [(i+1, n-i, c_exp, d_exp) for i in range(n)]
            rhs = [D*R[e] - sum((coef*N.get(minus(e, f), zero)
                                for f, coef in Q.items() if f[2]+f[3]), zero) for e in rows]
            for i in range(n):
                numerator = sum((adjugate[i][j]*rhs[j] for j in range(n)), zero)
                # Exact multivariate polynomial division, including the
                # divisibility required to use D rather than det(M_19).
                N[(i, n-1-i, c_exp, d_exp)] = numerator.exquo(determinant)
    assert set(N) == set(monomials(4)) and len(N) == 19
    error = {e: D*R[e] - sum((coef*N.get(minus(e, f), zero) for f, coef in Q.items()), zero)
             for e in exponents}
    pivots = [e for e in exponents if e[0] and e[1]]
    free = [e for e in exponents if not (e[0] and e[1])]
    assert len(pivots) == 19 and len(free) == 25
    assert all(error[e] == zero for e in pivots)
    assert all(c.denominator == 1 for f in N.values() for c in f.values())
    # Independent saturation simplification, recorded with its exact factors.
    normalized = []
    powers = []
    for e in free:
        value = error[e]
        counts = []
        for factor in factors:
            count = 0
            while value:
                quotient, remainder = divmod(value, factor)
                if remainder:
                    break
                value, count = quotient, count+1
            counts.append(count)
        normalized.append(value)
        powers.append(counts)

    comparison = {"status": "NOT RUN", "reason": "python-flint unavailable"}
    try:
        import flint
    except ImportError:
        pass
    else:
        from finite_modular_groebner import quotient_eliminate
        prime = 101
        ctx = flint.nmod_mpoly_ctx.get(tuple(names), prime, "degrevlex")
        modvars = dict(zip(names, ctx.gens()))
        actual = quotient_eliminate(ctx, modvars, [-modvars[f"R{i}"] for i in range(44)], exponents)
        def reduce_mod(f):
            return ctx.from_dict({e: int(c.numerator)*pow(int(c.denominator), -1, prime) % prime
                                  for e, c in f.items()})
        expected = [reduce_mod(f) for f in normalized]
        assert actual == expected
        comparison = {"status": "PASS", "modulus": prime, "symbolic_variables": len(names),
                      "equations_compared": len(actual), "numerical_samples": 0,
                      "builder_sha256": sha256((HERE / "finite_modular_groebner.py").read_bytes()).hexdigest()}

    witness = {
        "schema": "generic-contact-g2-numerators-v1",
        "coefficient_variables": names,
        "R_monomial_order": [list(e) for e in exponents],
        "D": str(D),
        "Q2": [{"exponent": list(e), "coefficient": str(c)} for e, c in sorted(Q.items())],
        "N": [{"exponent": list(e), "numerator": str(f)} for e, f in sorted(N.items())],
        "free_equations": [{"exponent": list(e), "normalized_polynomial": str(f),
                            "divided_factor_powers": power} for e, f, power in zip(free, normalized, powers)],
        "identity": "All 19 ab-divisible coefficients of D*R-Q2*N vanish identically. The other 25 coefficients are the displayed normalized equations multiplied by the recorded powers of (1-z),(1-2z),(1-3z).",
    }
    output = HERE / "contact_generic_g2_numerators.json"
    output.write_text(json.dumps(witness, separators=(",", ":")) + "\n")
    receipt = {
        "status": "PASS", "coefficient_ring": "QQ[mu0,...,mu4,R0,...,R43]",
        "R_independent_coefficients": 44,
        "quartic_numerators": len(N), "zero_pivot_coefficients": len(pivots),
        "remaining_equations": len(free),
        "common_denominator": "D=(1-mu0*mu1)*(1-2*mu0*mu1)*(1-3*mu0*mu1)",
        "independent_method": "Build multiplication blocks from actual monomial coefficient lookup; compute sizes 5,3,1 determinants and adjugates by generic determinant algorithms; exact polynomial division; independently multiply Q2*N.",
        "denominator_polynomial_identity": "det(M_19)=(1-z)*(1-3z)*(1-2z)^3; D and det(M_19) have the same nonvanishing open.",
        "all_numerator_coefficients_integral": True,
        "maximum_numerator_terms": max(len(f) for f in N.values()),
        "total_numerator_terms": sum(len(f) for f in N.values()),
        "modular_builder_comparison": comparison,
        "witness_sha256": sha256(output.read_bytes()).hexdigest(),
        "audit_script_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "scope": "Exact characteristic-zero polynomial elimination proof by independent CAS. The normalized equations are equivalent to the original coefficient equations on D!=0. This is not a Lean proof, quotient-basis calculation, or trace evaluation.",
        "source_trace_proved": False, "full_certificate_proved": False,
        "seconds": time.monotonic()-started,
    }
    (HERE / "contact_generic_g2_audit.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2), flush=True)


if __name__ == "__main__":
    main()
