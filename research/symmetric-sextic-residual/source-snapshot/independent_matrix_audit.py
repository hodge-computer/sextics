#!/usr/bin/env python3
"""Independently audit the weighted multiplication matrices and Lean data.

Uses only the standard library. Does not import any upstream or local generator.
All polynomial coefficients are evaluated by a closed multinomial formula,
without polynomial multiplication or the upstream Ring implementation.

The integral monomial ring is
  Z[z0,z1,z2,z3,z4,u] / (z0^5,z1^5,z2^5,z3^5,z4^5,u^2),
with weights (1,1,1,1,1,2). The involution swaps z0/z1 and z2/z3.

For nonnegative a=(a0,...,a4), let S=a0-a1+a2-a3 and
T=a0+a1+a2+a3. With (c,n)=(1,10) when the u exponent is 0,
and (c,n)=(5,8) when it is 1, the coefficient of z^a u^e is

  [Q]  = c n! S / product(a_i!)       if sum(a_i)=n+1,
  [HQ] = c n! S (T-1)/product(a_i!)  if sum(a_i)=n+2.

Here Q=D*L^10+5*u*D*L^8, D=z0-z1+z2-z3,
L=z0+z1+z2+z3+z4, and H=z0+z1+z2+z3.
The first formula follows by summing the choice of the variable in D;
the second by also summing the choice of the variable in H. The numerator
T*S-S accounts for the choices in which both linear factors use the same
variable. Negative exponents, other u exponents, and other degrees give zero.
Since the quotient ideal is monomial, truncation removes out-of-range terms
and does not alter a coefficient at any surviving monomial.

Required inputs beside this script are weighted_matrices.json,
WeightedMatrixData.lean, and PackedRankData.lean. It can run from any working
directory and does not require the original repository or generators.

This script audits the semantic association computationally. It is not a Lean
proof that the concrete matrices represent maps of a geometric Jacobian ring,
and does not prove the geometric support theorem or HasCertificate.
"""

from ast import literal_eval
from functools import lru_cache
from hashlib import sha256
from itertools import product
from math import factorial, prod
from pathlib import Path
import json
import re


HERE = Path(__file__).resolve().parent
CAPS = (4, 4, 4, 4, 4, 1)
WEIGHTS = (1, 1, 1, 1, 1, 2)
PRIME = 101


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def sigma(a):
    return a[1], a[0], a[3], a[2], a[4], a[5]


def degree(a):
    return sum(x * w for x, w in zip(a, WEIGHTS))


@lru_cache(maxsize=None)
def monomials(d):
    return tuple(a for a in product(*(range(c + 1) for c in CAPS))
                 if degree(a) == d)


def orbit_basis(d, sign):
    """Canonical orbit representatives from an exhaustive set partition."""
    require(sign in (-1, 1), "Invalid eigenspace sign")
    available = set(monomials(d))
    unseen = set(available)
    pairs = []
    while unseen:
        a = min(unseen)
        b = sigma(a)
        require(b in available and sigma(b) == a, "Involution is not closed")
        unseen.remove(a)
        if b != a:
            require(a < b and b in unseen, "Orbit appears twice")
            unseen.remove(b)
            pairs.append([(a, 1), (b, sign)])
        elif sign == 1:
            pairs.append([(a, 1)])
    # Disjoint supports prove independence. Exhaustive orbit enumeration proves
    # that these vectors span the requested +/- eigenspace in characteristic 0.
    supports = [a for orbit in pairs for a, _ in orbit]
    require(len(supports) == len(set(supports)), "Basis supports overlap")
    for orbit in pairs:
        v = dict(orbit)
        require(all(v.get(sigma(a), 0) == sign * c for a, c in orbit),
                "Basis vector has incorrect sigma eigenvalue")
    return pairs


def json_basis(orbits):
    return [[[list(a), c] for a, c in orbit] for orbit in orbits]


@lru_cache(maxsize=None)
def coefficient(label, a):
    require(label in ("Q", "HQ"), "Unknown polynomial")
    if len(a) != 6 or any(x < 0 for x in a) or a[5] not in (0, 1):
        return 0
    c, n = (1, 10) if a[5] == 0 else (5, 8)
    if sum(a[:5]) != n + (1 if label == "Q" else 2):
        return 0
    signed_sum = a[0] - a[1] + a[2] - a[3]
    numerator = c * factorial(n) * signed_sum
    if label == "HQ":
        numerator *= sum(a[:4]) - 1
    denominator = prod(factorial(x) for x in a[:5])
    value, remainder = divmod(numerator, denominator)
    require(remainder == 0, "Multinomial coefficient unexpectedly nonintegral")
    return value


def product_coefficient(label, target, orbit):
    return sum(c * coefficient(label, tuple(x - y for x, y in zip(target, a)))
               for a, c in orbit)


def determinant_mod(matrix):
    """Unscaled triangular elimination; no dependency on the generator."""
    n = len(matrix)
    require(all(len(row) == n for row in matrix), "Nonsquare determinant")
    a = [[x % PRIME for x in row] for row in matrix]
    answer = 1
    for col in range(n):
        pivot = next((row for row in range(col, n) if a[row][col]), None)
        if pivot is None:
            return 0
        if pivot != col:
            a[col], a[pivot] = a[pivot], a[col]
            answer = -answer
        value = a[col][col]
        answer = answer * value % PRIME
        reciprocal = pow(value, PRIME - 2, PRIME)
        for row in range(col + 1, n):
            multiple = a[row][col] * reciprocal % PRIME
            for j in range(col, n):
                a[row][j] = (a[row][j] - multiple * a[col][j]) % PRIME
    return answer % PRIME


def verify_inverse(matrix, inverse):
    n = len(matrix)
    require(len(inverse) == n and all(len(row) == n for row in inverse),
            "Inverse shape mismatch")
    require(all(type(x) is int and 0 <= x < PRIME for row in inverse for x in row),
            "Inverse entries are not canonical residues")
    for side, left, right in (("M*B", matrix, inverse), ("B*M", inverse, matrix)):
        columns = tuple(zip(*right))
        for i, row in enumerate(left):
            for j, col in enumerate(columns):
                require(sum(x * y for x, y in zip(row, col)) % PRIME == int(i == j),
                        f"{side} differs from identity at ({i},{j})")


def lean_array_fragment(text, name):
    """Read a Lean array literal as text; never execute Lean or generator code."""
    match = re.search(r"^def " + re.escape(name) + r"\s*:[^\n]*?:=\s*#\[", text, re.M)
    require(match is not None, f"Missing literal array {name}")
    start = text.index("#[", match.start())
    depth = 0
    end = None
    for i in range(start, len(text)):
        if text[i] == "[":
            depth += 1
        elif text[i] == "]":
            depth -= 1
            if depth == 0:
                end = i + 1
                break
    require(end is not None, f"Unclosed array {name}")
    return text[start:end]


def lean_array(text, name):
    """Read an array of integer literals, used for the minor indices."""
    return literal_eval(lean_array_fragment(text, name).replace("#[", "["))


def named_nat_array(text, array_name, prefix, length):
    """Resolve a final data array through its named literal Nat constants."""
    matches = re.findall(r"^def ([A-Za-z][A-Za-z0-9_]*)\s*:\s*Nat\s*:=\s*([0-9]+)\s*$",
                         text, re.M)
    require(len(matches) == len({name for name, _ in matches}), "Repeated Nat definition")
    constants = {name: int(value) for name, value in matches}
    expected = [prefix + str(i) for i in range(length)]
    names = [s.strip() for s in lean_array_fragment(text, array_name)[2:-1].split(",")]
    require(names == expected, f"{array_name} has incorrect named-constant order")
    require({name for name in constants if re.fullmatch(re.escape(prefix) + r"[0-9]+", name)}
            == set(expected), f"{array_name} has missing or extra numbered constants")
    return [constants[name] for name in names]


def require_definition(text, name, expected):
    """Inspect the small decoder/selector definitions, ignoring whitespace only."""
    pattern = r"^def " + re.escape(name) + r"(?=\s|\{|\()"
    starts = list(re.finditer(pattern, text, re.M))
    require(len(starts) == 1, f"Missing or repeated definition {name}")
    start = starts[0].start()
    following = re.search(r"^(?:def|theorem|end|namespace)\b", text[starts[0].end():], re.M)
    end = starts[0].end() + following.start() if following else len(text)
    actual = text[start:end]
    require(re.sub(r"\s+", "", actual) == re.sub(r"\s+", "", expected),
            f"{name} differs from the audited definition")


def unpack(encoded, length, radix, offset=0):
    require(type(encoded) is int and encoded >= 0, "Packed row is not natural")
    out = []
    for _ in range(length):
        encoded, digit = divmod(encoded, radix)
        out.append(digit - offset)
    require(encoded == 0, "Packed row contains unaccounted high digits")
    return out


def selected(matrix, rows, cols):
    return [[matrix[i][j] for j in cols] for i in rows]


def digest_object(value):
    return sha256(json.dumps(value, separators=(",", ":")).encode()).hexdigest()


def main():
    paths = {
        "weighted_matrices": HERE / "weighted_matrices.json",
        "integer_lean": HERE / "WeightedMatrixData.lean",
        "modular_lean": HERE / "PackedRankData.lean",
        "independent_verifier": Path(__file__).resolve(),
    }
    raw = {name: path.read_bytes() for name, path in paths.items()}
    data = json.loads(raw["weighted_matrices"])
    upstream_path = HERE.parent / "sextics/scripts/verify-weighted-voisin.py"
    upstream_rechecked = upstream_path.is_file()
    if upstream_rechecked:
        upstream_hash = sha256(upstream_path.read_bytes()).hexdigest()
        require(data["upstream_sha256"] == upstream_hash, "Recorded upstream source hash mismatch")
    integer_text = raw["integer_lean"].decode()
    modular_text = raw["modular_lean"].decode()
    require_definition(integer_text, "integerRows", """
      def integerRows {m n : ℕ} (a : Array Nat) : Matrix (Fin m) (Fin n) ℤ :=
        fun i j => (((a[i.val]! / 4294967296^j.val) % 4294967296 : Nat) : ℤ) - 2147483648
    """)
    require_definition(modular_text, "digit", """
      def digit (a k : Nat) : Nat := (a / 128^k) % 128
    """)
    require_definition(modular_text, "dot", """
      def dot (n a b : Nat) : Nat :=
        ((List.range n).foldl (fun s k => s + digit a k * digit b k) 0) % 101
    """)
    require_definition(modular_text, "checkRow", """
      def checkRow (n a : Nat) (bs : Array Nat) (i : Nat) : Bool :=
        (List.range n).all fun j => dot n a bs[j]! == (if i == j then 1 else 0)
    """)

    basis_receipt = {}
    for d in (5, 16, 17):
        plus, minus = orbit_basis(d, 1), orbit_basis(d, -1)
        total = len(monomials(d))
        fixed = sum(sigma(a) == a for a in monomials(d))
        require(len(plus) + len(minus) == total and len(plus) - len(minus) == fixed,
                "Orbit basis dimension identity failed")
        basis_receipt[str(d)] = {
            "total_monomials": total, "fixed_monomials": fixed,
            "plus_dimension": len(plus), "minus_dimension": len(minus),
            "plus_basis_sha256": digest_object(json_basis(plus)),
            "minus_basis_sha256": digest_object(json_basis(minus)),
            "complete_disjoint_orbits_checked": True,
        }

    source = orbit_basis(5, 1)
    source_json = json_basis(source)
    maps = {}
    for label, target_degree in (("Q", 16), ("HQ", 17)):
        recorded = data[label]
        target = orbit_basis(target_degree, -1)
        representatives = [orbit[0][0] for orbit in target]
        require(recorded["source_orbits"] == source_json, f"{label} source orbit mismatch")
        require(recorded["source_basis"] == [term for orbit in source_json for term in orbit],
                f"{label} flattened source basis mismatch")
        require(recorded["target_representatives"] == [list(a) for a in representatives],
                f"{label} target representative mismatch")

        matrix = [[product_coefficient(label, a, orbit) for orbit in source]
                  for a in representatives]
        require(matrix == recorded["matrix"], f"{label} integral matrix mismatch")
        # Checking every target monomial confirms coefficients at representatives
        # suffice: products really are anti-invariant, including vanishing on all
        # fixed monomials. No monomial outside the target degree is possible.
        for a in monomials(target_degree):
            for orbit in source:
                require(product_coefficient(label, sigma(a), orbit)
                        == -product_coefficient(label, a, orbit),
                        f"{label} product is not anti-invariant")

        m, n = len(matrix), len(source)
        rows, cols = recorded["rows"], recorded["cols"]
        k = min(m, n)
        require(len(rows) == len(cols) == k, f"{label} minor not maximal")
        require(len(set(rows)) == k and all(0 <= x < m for x in rows),
                f"{label} invalid minor rows")
        require(len(set(cols)) == k and all(0 <= x < n for x in cols),
                f"{label} invalid minor columns")
        if label == "Q":
            require(cols == list(range(n)), "Q minor omits or permutes a source column")
        else:
            require(rows == list(range(m)), "HQ minor omits or permutes a target row")
        minor = selected(matrix, rows, cols)
        require(minor == recorded["minor"], f"{label} selected minor mismatch")
        inverse = recorded["inverse_mod101"]
        verify_inverse(minor, inverse)
        det = determinant_mod(minor)
        require(det != 0, f"{label} selected determinant vanishes")

        original = recorded["receipt"]
        require((original["source_dimension"], original["target_dimension"], original["rank"])
                == (n, m, k), f"{label} original rank dimensions mismatch")
        original_rows, original_cols = original["minor_rows_zero_based"], original["minor_columns_zero_based"]
        require(set(original_rows) == set(rows) and original_cols == cols,
                f"{label} receipt selects different minor")
        original_det = determinant_mod(selected(matrix, original_rows, original_cols))
        require(original_det == original["minor_determinant_mod_prime"],
                f"{label} original determinant receipt mismatch")

        packed_rows = named_nat_array(integer_text, label + "Rows", label + "IntegerRow", m)
        integer_matrix = [unpack(x, n, 2 ** 32, 2 ** 31) for x in packed_rows]
        require(integer_matrix == matrix, f"{label} final Lean integer matrix mismatch")
        packed_minor = named_nat_array(modular_text, label + "rows", label + "row", k)
        packed_inverse = named_nat_array(modular_text, label + "cols", label + "col", k)
        require([unpack(x, k, 128) for x in packed_minor]
                == [[x % PRIME for x in row] for row in minor],
                f"{label} final Lean modular minor rows mismatch")
        require([unpack(x, k, 128) for x in packed_inverse]
                == [list(col) for col in zip(*inverse)],
                f"{label} final Lean inverse columns mismatch")
        index_name, expected_indices = ("QRowIndices", rows) if label == "Q" else ("HQColumnIndices", cols)
        require(lean_array(integer_text, index_name) == expected_indices,
                f"{label} Lean minor selection index mismatch")
        require_definition(integer_text, label + "Matrix", f"""
          def {label}Matrix : Matrix (Fin {m}) (Fin {n}) ℤ := integerRows {label}Rows
        """)
        if label == "Q":
            require_definition(integer_text, "QSelectRows", f"""
              def QSelectRows (i : Fin {k}) : Fin {m} := QRowIndices[i.val]!
            """)
            require_definition(integer_text, "QMinor", f"""
              def QMinor : Matrix (Fin {k}) (Fin {k}) ℤ := QMatrix.submatrix QSelectRows id
            """)
        else:
            require_definition(integer_text, "HQSelectColumns", f"""
              def HQSelectColumns (i : Fin {k}) : Fin {n} := HQColumnIndices[i.val]!
            """)
            require_definition(integer_text, "HQMinor", f"""
              def HQMinor : Matrix (Fin {k}) (Fin {k}) ℤ := HQMatrix.submatrix id HQSelectColumns
            """)
        require_definition(integer_text, label + "Inverse", f"""
          def {label}Inverse : Matrix (Fin {k}) (Fin {k}) (ZMod 101) :=
            fun i j => (PackedCheck.digit PackedCheck.{label}cols[j.val]! i.val : ZMod 101)
        """)
        require(selected(integer_matrix, rows, cols) == minor,
                f"{label} final Lean submatrix differs from the reconstructed minor")

        maps[label] = {
            "matrix_shape": [m, n], "exact_entries_checked": m * n,
            "matrix_sha256": digest_object(matrix),
            "minor_shape": [k, k], "minor_sha256": digest_object(minor),
            "selected_minor_determinant_mod101": det,
            "original_receipt_minor_determinant_mod101": original_det,
            "source_orbits_match": True, "target_representatives_match": True,
            "full_products_anti_invariant": True, "integer_matrix_matches": True,
            "selected_minor_matches": True, "inverse_left_and_right_checked": True,
            "final_integer_lean_data_matches": True,
            "final_modular_minor_rows_match": True,
            "final_inverse_columns_and_orientation_match": True,
            "final_submatrix_definitions_and_indices_match": True,
            "named_constant_array_order_checked": True,
            "rank_over_Q_from_nonzero_maximal_minor": k,
        }

    receipt = {
        "status": "PASS",
        "method": "Closed multinomial coefficients; independent exhaustive sigma-orbit bases; exact integer arithmetic; no generator imports",
        "ring": "Z[z0,z1,z2,z3,z4,u]/(z0^5,z1^5,z2^5,z3^5,z4^5,u^2)",
        "caps": list(CAPS), "weights": list(WEIGHTS),
        "sigma": [1, 0, 3, 2, 4, 5],
        "polynomials": {
            "D": "z0-z1+z2-z3", "L": "z0+z1+z2+z3+z4",
            "H": "z0+z1+z2+z3", "Q": "D*L^10+5*u*D*L^8",
        },
        "coefficient_formulas": {
            "parameters": "For u exponent e=0 use (c,n)=(1,10), for e=1 use (c,n)=(5,8); S=a0-a1+a2-a3; T=a0+a1+a2+a3",
            "Q": "c*n!*S/product(a_i!) when sum(a_i)=n+1",
            "HQ": "c*n!*S*(T-1)/product(a_i!) when sum(a_i)=n+2",
        },
        "basis_degrees": basis_receipt, "maps": maps,
        "inputs_sha256": {name: sha256(content).hexdigest() for name, content in raw.items()},
        "recorded_upstream_sha256": data["upstream_sha256"],
        "optional_upstream_hash_rechecked": upstream_rechecked,
        "scope": "The semantic identification of the final Lean matrices with the polynomial multiplication maps in the stated monomial quotient is verified by this independent Python computation, not by formal Lean. The geometric Jacobian-quotient association, geometric support theorem, and HasCertificate are not proved in Lean by this audit. Lean rank certification of the concrete matrices is separate.",
    }
    output = HERE / "independent_matrix_audit.json"
    output.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "basis_dimensions": basis_receipt,
                      "maps": maps, "receipt": str(output)}, indent=2))


if __name__ == "__main__":
    main()
