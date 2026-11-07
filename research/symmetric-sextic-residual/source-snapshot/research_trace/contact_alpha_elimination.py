#!/usr/bin/env python3
"""Exact elimination of alpha on the bN-open of the actual contact algebra.

Emits an extended scalar DAG with 45 contact equations in 45 variables.  The
discarded bN=0 summand is explicitly retained as a separate obligation; no full
trace is identified with the open summand's trace without checking that part.
"""
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import copy
import json
import sys

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / "research_contact"
if not SOURCE.exists():
    SOURCE = HERE.parent / "proof_attempt4"
for dependency_directory in (HERE.parent / "research_workaround" / "python_deps",
                             HERE.parent / "proof_attempt3" / "python_deps"):
    if dependency_directory.exists():
        sys.path.insert(0, str(dependency_directory))
        break


class Nodes:
    def __init__(self, nodes):
        self.nodes = copy.deepcopy(nodes)
        self.memo = {(n["op"], tuple(n["data"]) if isinstance(n["data"], list) else n["data"]): i
                     for i, n in enumerate(nodes)}

    def make(self, op, data):
        key = (op, tuple(data) if isinstance(data, list) else data)
        if key not in self.memo:
            self.memo[key] = len(self.nodes)
            self.nodes.append({"op": op, "data": data})
        return self.memo[key]

    def const(self, x):
        x = Fraction(x)
        return self.make("rational", [x.numerator, x.denominator])

    def var(self, name):
        return self.make("variable", name)

    def add(self, *xs):
        return self.make("add", list(xs))

    def mul(self, *xs):
        return self.make("multiply", list(xs))

    def sub(self, x, y):
        return self.add(x, self.mul(self.const(-1), y))

    def pow(self, x, n):
        return self.make("power", [x, n])


def build():
    original = json.loads((SOURCE / "contact_forms_global_residue.json").read_text())
    base = json.loads((SOURCE / "contact_target_circuit.json").read_text())
    C = Nodes(original["scalar_nodes"])
    r, s = C.var("r"), C.var("s")
    r2, r3, s2, s3 = C.pow(r, 2), C.pow(r, 3), C.pow(s, 2), C.pow(s, 3)
    mu = [C.var(f"mu{i}") for i in range(5)]
    A = [C.var(f"A{i}") for i in range(8)]
    B = [C.var(f"B{i}") for i in range(8)]
    q0 = C.add(r, mu[0], C.mul(mu[1], r2))
    q2 = C.add(mu[2], C.mul(mu[3], s), C.mul(mu[4], s2))
    a0 = C.add(A[0], C.mul(A[1], r3))
    a2 = C.add(A[2], C.mul(A[3], s), C.mul(A[4], s2),
               C.mul(r, C.add(A[5], C.mul(A[6], s), C.mul(A[7], s2))))
    b0 = C.add(B[0], C.mul(B[1], s), C.mul(r2, C.add(B[2], C.mul(B[3], s))))
    b2 = C.add(B[4], C.mul(B[5], s), C.mul(B[6], s2), C.mul(B[7], s3))
    aN = C.sub(C.mul(q2, a0), C.mul(q0, a2))
    bN = C.sub(C.mul(q2, b0), C.mul(q0, b2))
    P = C.add(C.mul(q2, C.pow(aN, 2)), C.mul(q0, C.pow(bN, 2)))
    alpha = C.mul(C.const(-1), aN, C.make("inverse", bN))
    rho = [C.var(f"rho{i}") for i in range(5)]
    rhoX = C.add(rho[0], C.mul(rho[1], r2))
    rhoY = C.add(rho[2], C.mul(rho[3], s), C.mul(rho[4], s2))
    minus_q0 = C.mul(C.const(-1), q0)
    betaN = C.sub(C.mul(q0, rhoY), C.mul(q2, rhoX))
    # q2^3 G(-q0/q2, betaN/q2), with the monic cubic G fixed by the
    # protected target.  Its only contact parameters are rho and mu.
    G3_terms = []
    for term in base["polynomials"]["G"]:
        e = term["exponent"]
        assert (e[2] + e[3]) % 2 == 0
        k, ell = (e[2] + e[3]) // 2, e[4]
        assert k + ell <= 3
        G3_terms.append(C.mul(term["coefficient_node"], C.pow(r, e[1]), C.pow(s, e[3]),
                              C.pow(minus_q0, k), C.pow(betaN, ell), C.pow(q2, 3-k-ell)))
    G3 = C.add(*G3_terms)
    H_weights = []
    for e in original["contact_equation_monomial_order"]:
        assert (e[2] + e[3]) % 2 == 0
        k = (e[2] + e[3]) // 2
        H_weights.append(C.mul(C.pow(r, e[1]), C.pow(s, e[3]), C.pow(minus_q0, k), C.pow(q2, 3-k)))
    packet = {
        "schema": "symmetric-contact-alpha-elimination-v1",
        "coefficient_field": original["coefficient_field"],
        "scalar_nodes": C.nodes,
        "variable_order": original["contact_variable_order"],
        "equation_nodes": original["contact_equation_nodes"] + [P],
        "AB_free_equation_nodes": original["contact_equation_nodes"] + [G3],
        "coefficient_nodes": dict(zip(("q0", "q2", "a0", "a2", "b0", "b2", "aN", "bN", "P", "alpha_substitution", "G3", "betaN"),
                                      (q0, q2, a0, a2, b0, b2, aN, bN, P, alpha, G3, betaN))),
        "AB_free_identity": {
            "formula": "P-G3=sum_j H_weight_j*H_j",
            "H_weight_nodes": H_weights,
            "H_equation_nodes": original["contact_equation_nodes"],
            "G3_definition": "q2^3*G(-q0/q2,betaN/q2), expanded as a polynomial with no q2 division",
            "consequence": "(H_1,...,H_44,P)=(H_1,...,H_44,G3) as polynomial ideals. On H=0 the last Jacobian rows differ by a linear combination of the first 44 rows, so the 45x45 Jacobian determinants agree.",
        },
        "extra_open_node": bN,
        "original_localization": original["localization"],
        "original_localization_substitution": {"alpha": alpha},
        "original_incidence_J_evaluated_after_substitution": True,
        "original_J_from_eliminated_J": "J=Je/(q2*bN)",
        "eliminated_J_definition": "Je=det d(H_1,...,H_44,P)/d(contact parameters)",
        "eliminated_source_function": "q2*bN*f*Pi/Je; equals the original f*Pi/J",
        "exact_identities": [
            "q=q0+q2*alpha^2",
            "h=a0+a2*alpha^2+alpha*(b0+b2*alpha^2)",
            "aN=q2*a0-q0*a2; bN=q2*b0-q0*b2; P=q2*aN^2+q0*bN^2",
            "q2*h-(a2+alpha*b2)*q=aN+alpha*bN",
            "P=bN^2*q+q2*(aN-alpha*bN)*(aN+alpha*bN)",
            "q(-aN/bN)=P/bN^2",
            "h(-aN/bN)=(a2*b0-a0*b2)*P/bN^3",
            "Je=q2*bN*J on the incidence",
        ],
        "omitted_summand": {
            "presentation": "Original finite etale algebra modulo bN (which also forces aN=0)",
            "equation_node_to_append": bN,
            "aN_also_vanishes": True,
            "subcase_q2_zero": "q0=0; original h(alpha)=0 remains. The q equation becomes identically zero only after imposing q0=q2=0.",
            "subcase_q2_unit": "aN=bN=0, alpha^2=-q0/q2. Modulo q, h is identically zero; the original equations in the contact parameters must still be retained.",
            "trace_rule": "Tr_full(M)=Tr_bN-open(M)+Tr_bN-zero(M). Open and omitted degrees add. No claim that the omitted summand is zero.",
        },
        "source_trace_proved": False,
        "full_certificate_proved": False,
        "input_sha256": sha256((SOURCE / "contact_forms_global_residue.json").read_bytes()).hexdigest(),
    }
    return packet, base


def audit(packet, base):
    import sympy as sp
    cache = {}
    nodes = packet["scalar_nodes"]

    def val(i):
        if i in cache:
            return cache[i]
        op, d = nodes[i]["op"], nodes[i]["data"]
        if op == "rational": v = sp.Rational(*d)
        elif op == "variable": v = sp.Symbol(d)
        elif op == "add": v = sp.Add(*(val(j) for j in d))
        elif op == "multiply": v = sp.Mul(*(val(j) for j in d))
        elif op == "power": v = val(d[0]) ** d[1]
        elif op == "inverse": v = 1 / val(d)
        else: raise AssertionError(op)
        cache[i] = v
        return v

    c = {name: val(node) for name, node in packet["coefficient_nodes"].items()}
    al = sp.Symbol("alpha")
    q = c["q0"] + c["q2"] * al ** 2
    h = c["a0"] + c["a2"] * al ** 2 + al * (c["b0"] + c["b2"] * al ** 2)
    assert sp.expand(val(base["point_q_node"]) - q) == 0
    assert sp.expand(val(base["point_h_node"]) - h) == 0
    # Check the ring identities independently on six arbitrary coefficients.
    q0, q2, a0, a2, b0, b2 = sp.symbols("q0 q2 a0 a2 b0 b2")
    qg = q0 + q2 * al ** 2
    hg = a0 + a2 * al ** 2 + al * (b0 + b2 * al ** 2)
    an, bn = q2*a0-q0*a2, q2*b0-q0*b2
    pg = q2*an**2+q0*bn**2
    assert sp.expand(q2*hg-(a2+al*b2)*qg-an-al*bn) == 0
    assert sp.expand(pg-bn**2*qg-q2*(an-al*bn)*(an+al*bn)) == 0
    assert sp.cancel(qg.subs(al, -an/bn)-pg/bn**2) == 0
    assert sp.cancel(hg.subs(al, -an/bn)-(a2*b0-a0*b2)*pg/bn**3) == 0
    derivs = sp.symbols("dq0 dq2 da0 da2 db0 db2")
    variables = (q0, q2, a0, a2, b0, b2)
    K = lambda f: sum(sp.diff(f, v)*dv for v, dv in zip(variables, derivs))
    jac = K(qg)*sp.diff(hg, al)-sp.diff(qg, al)*K(hg)
    error = sp.expand(K(pg)-q2*bn*jac)
    reduced = error.subs(q0, -q2*al**2).subs(a0, -a2*al**2-al*(b0+b2*al**2))
    assert sp.expand(reduced) == 0
    # The 45 reduced equations have no alpha dependence.
    for i in packet["equation_nodes"]:
        assert al not in val(i).free_symbols
    identity = packet["AB_free_identity"]
    difference = c["P"] - c["G3"] - sum(val(w) * val(e) for w, e in
                       zip(identity["H_weight_nodes"], identity["H_equation_nodes"]))
    assert sp.cancel(sp.expand(difference)) == 0
    assert not any(str(v).startswith(("A", "B", "g2_")) for v in c["G3"].free_symbols)
    return {"actual_source_coefficient_binding": "PASS", "four_ring_identities": "PASS",
            "Jacobian_relation": "PASS", "equation_count": len(packet["equation_nodes"]),
            "variable_count": len(packet["variable_order"]), "bN_residual_retained": True,
            "AB_free_constraint_and_exact_ideal_witness": "PASS",
            "exact_coefficients": {k: str(c[k]) for k in ("q0", "q2", "a0", "a2", "b0", "b2")},
            "source_trace_proved": False}


def main():
    packet, base = build()
    receipt = audit(packet, base)
    target = HERE / "contact_alpha_elimination.json"
    target.write_text(json.dumps(packet, separators=(",", ":")) + "\n")
    receipt["output_sha256"] = sha256(target.read_bytes()).hexdigest()
    (HERE / "contact_alpha_elimination_receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
