#!/usr/bin/env python3
"""Exact character audit of the actual localized contact-source circuit.

This is a structural algebra audit, not sampling and not a trace evaluation.
Every scalar DAG operation is assigned its character under the two specified
involutions.  Determinant characters follow from checked row/column signs.
The script imports no circuit builder and uses only the Python standard library.
"""
from fractions import Fraction
from functools import cache
from hashlib import sha256
from itertools import product
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / "research_contact"
if not SOURCE.exists():
    SOURCE = HERE.parent / "proof_attempt4"


def load(name):
    return json.loads((SOURCE / name).read_text())


@cache
def mons(d):
    return sorted(e for e in product(range(d + 1), repeat=4) if sum(e) == d)


def ambient_character(e):
    return (-1) ** (e[2] + e[3])


def scalar_characters(nodes, negative_variables):
    """A set of possible characters for each DAG node; empty means zero.

    Additions take unions, so cancellations are never assumed.  A singleton
    is therefore an exact proof of the claimed parity by structural induction.
    """
    out = []
    for i, node in enumerate(nodes):
        op, data = node["op"], node["data"]
        if op == "rational":
            char = {1} if Fraction(*data) else set()
        elif op == "variable":
            char = {-1 if data in negative_variables else 1}
        elif op == "add":
            char = set().union(*(out[j] for j in data))
        elif op == "multiply":
            char = {1}
            for j in data:
                char = {a * b for a in char for b in out[j]}
        elif op == "power":
            j, n = data
            char = {a ** n for a in out[j]} if n else {1}
        elif op == "inverse":
            # Inverses in the source are of functions with a single character.
            assert len(out[data]) == 1, (i, node, out[data])
            char = out[data]
        else:
            raise AssertionError((i, op))
        out.append(char)
    return out


def product_sign(signs):
    out = 1
    for sign in signs:
        assert sign in (-1, 1)
        out *= sign
    return out


def main():
    global_packet = load("contact_forms_global_residue.json")
    forms = load("contact_forms_residue_system.json")
    base = load("contact_target_circuit.json")
    selected9 = load("contact_forms_nonzero_witness.json")["selected_ideal_columns"]
    selected10 = load("contact_forms_regularity_witness.json")["selected_columns"]
    nodes = global_packet["scalar_nodes"]
    assert len(global_packet["contact_variable_order"]) == 45
    assert len(global_packet["incidence_variable_order"]) == 46
    assert len(global_packet["contact_equation_nodes"]) == 44
    assert len(forms["target_pairs"]) == 9
    assert forms["socle_basis"] == [list(e) for e in mons(9)]
    assert base["parameter_order"] == (
        [f"rho{i}" for i in range(5)] + [f"mu{i}" for i in range(5)]
        + [f"A{i}" for i in range(8)] + [f"B{i}" for i in range(8)])
    # Exact chart normalizations: no ab term in Q1; coefficient of ab in Q2 is 1.
    q1 = {tuple(t["exponent"]): t["coefficient_node"] for t in base["polynomials"]["Q1"]}
    q2 = {tuple(t["exponent"]): t["coefficient_node"] for t in base["polynomials"]["Q2"]}
    assert (1, 1, 0, 0) not in q1
    assert nodes[q2[(1, 1, 0, 0)]] == {"op": "rational", "data": [1, 1]}
    # The source R is odd under (a,b,c,d)->(a,b,-c,-d).
    assert all(ambient_character(t["exponent"]) == -1
               for t in forms["source_after_u_elimination"])

    actions = {}
    for letter in ("A", "B"):
        negative = {f"{letter}{i}" for i in range(8)} | {"alpha"}
        chars = scalar_characters(nodes, negative)
        checks = 0

        def expect(node, character):
            nonlocal checks
            assert chars[node] <= {character}, (letter, node, chars[node], character)
            checks += 1

        # Under the parameter transformation, h'(x)=epsilon*h(S_y x).
        epsilon = -1 if letter == "A" else 1
        for node in global_packet["contact_equation_nodes"]:
            expect(node, 1)
        expect(base["point_q_node"], 1)
        expect(base["point_h_node"], epsilon)
        expect(base["point_beta_node"], 1)
        expect(base["localization_Delta_node"], 1)
        expect(global_packet["localization"]["factors"]["G_w_at_point_node"], 1)
        for t in forms["source_after_u_elimination"]:
            expect(t["coefficient_node"], 1)

        residue_form_names = ("Q2", "h", "g1bar", "g2")
        form_signs = (1, epsilon, 1, 1)
        for form_name, form_sign in zip(residue_form_names, form_signs):
            for term in forms["residue_forms"][form_name]:
                expect(term["coefficient_node"],
                       form_sign * ambient_character(term["exponent"]))

        # Each degree-nine constraint row changes by its generator/multiplier
        # sign followed by the common monomial-column diagonal matrix.
        row9signs = []
        for entry in forms["ideal_product_columns"]:
            sign = form_signs[entry["form_index"]] * ambient_character(entry["multiplier_exponent"])
            row9signs.append(sign)
            for i, node in entry["entries"]:
                expect(node, sign * ambient_character(forms["socle_basis"][i]))
        # The last row is det(d(Q2,h,g1bar,g2)/d(a,b,c,d)).  The ambient
        # involution has determinant +1, so its row factor is epsilon.
        jacobian = forms["normalization_jacobian_matrix"]
        for i, row in enumerate(jacobian):
            for j, polynomial in enumerate(row):
                variable_sign = -1 if j in (2, 3) else 1
                for term in polynomial:
                    expect(term["coefficient_node"], form_signs[i] * variable_sign
                           * ambient_character(term["exponent"]))
        delta9_sign = product_sign(row9signs[j] for j in selected9) * epsilon
        delta9_sign *= product_sign(ambient_character(e) for e in mons(9))
        # In T9*tau=96 e_last this gives tau'(e)=epsilon*chi(e)*tau(e).
        eta_signs = {}
        for component in forms["canonical_one_form"]["components"]:
            parameter = component["parameter"]
            parameter_parity = 1 if parameter.startswith("A") else -1
            eta_sign = -epsilon * parameter_parity
            for i, node in component["socle_coefficient_nodes"]:
                expect(node, 1)
                assert ambient_character(forms["socle_basis"][i]) == -parameter_parity
            eta_signs[parameter] = eta_sign
            tangent_sign = -1 if parameter in negative else 1
            assert tangent_sign * eta_sign == -1

        # The degree-ten selected minor uses the same generator/multiplier rule.
        column10signs = []
        for form_sign, degree in zip(form_signs, forms["residue_form_degrees"]):
            column10signs.extend(form_sign * ambient_character(e) for e in mons(10 - degree))
        assert len(column10signs) == 453
        D10_sign = product_sign(column10signs[j] for j in selected10)
        D10_sign *= product_sign(ambient_character(e) for e in mons(10))
        selected10frame = global_packet["determinant_frames"]["D10"]
        for col_idx, column in zip(selected10, selected10frame["sparse_columns"]):
            for row_idx, node in column:
                expect(node, column10signs[col_idx] * ambient_character(mons(10)[row_idx]))

        expected_partials = {"q_r": 1, "q_s": 1, "q_alpha": -1,
                             "h_r": epsilon, "h_s": epsilon, "h_alpha": -epsilon,
                             "beta_r": 1, "beta_s": 1, "beta_alpha": -1}
        for name, node in forms["point_partial_nodes"].items():
            expect(node, expected_partials[name])
        for name, node in forms["current_numerator_nodes"].items():
            expect(node, epsilon if name == "z" else -epsilon)
        for pair in forms["target_pairs"]:
            expect(pair["P_coefficient_node"], epsilon)
            expect(pair["target_coefficient_node"], 1)

        contact_variable_det = (-1) ** 8
        incidence_variable_det = -contact_variable_det
        J_sign = epsilon * incidence_variable_det
        density_sign = -1
        f_numerator_sign = density_sign * delta9_sign
        S_sign = J_sign * delta9_sign * D10_sign * -1
        T0_sign = -D10_sign
        # zeta transforms by S_sign because zeta*S=1.
        source_sign = S_sign * T0_sign * f_numerator_sign * epsilon
        assert source_sign == 1
        assert density_sign * epsilon * J_sign == 1
        actions[letter] = {
            "negative_variables": sorted(negative),
            "ambient_involution": "(a,b,c,d)->(a,b,-c,-d)",
            "h_form_multiplier_epsilon": epsilon,
            "contact_equation_character": 1,
            "point_h_character": epsilon,
            "J_character": J_sign,
            "delta9_character": delta9_sign,
            "D10_character": D10_sign,
            "density_f_character": density_sign,
            "f_numerator_character": f_numerator_sign,
            "S_and_zeta_character": S_sign,
            "T0_character": T0_sign,
            "P1_and_P2_coefficient_character": epsilon,
            "all_nine_actual_source_characters": [source_sign] * 9,
            "all_nine_target_characters": [1] * 9,
            "canonical_one_form_pullback_character": -1,
            "eta_coordinate_characters": eta_signs,
            "checked_nonzero_or_zero_coefficient_slots": checks,
        }

    receipt = {
        "schema": "symmetric-contact-exact-sign-audit-v1",
        "method": "Exact character propagation through every actual scalar DAG operation; exact selected matrix row/column transformations. No numeric evaluations.",
        "input_sha256": {name: sha256((SOURCE / name).read_bytes()).hexdigest() for name in (
            "contact_forms_global_residue.json", "contact_forms_residue_system.json",
            "contact_target_circuit.json", "contact_forms_nonzero_witness.json",
            "contact_forms_regularity_witness.json")},
        "actions": actions,
        "normalization_stable": True,
        "localization_stable_under_both_actions": True,
        "obvious_sign_group": "C2 x C2",
        "group_action_free_reason": "Each generator changes the unit alpha to -alpha. Their product fixes only A=B=0; there h=0 and the Jacobian normalization row of T9 is zero, contradicting delta9 being a unit.",
        "trace_consequence": "For B=A^(C2 x C2), rank_K(A)=4*rank_K(B) and Tr_A/K(M)=4*Tr_B/K(M) for each of the nine invariant source operands. Their normalized traces are equal. This does not evaluate those normalized traces.",
        "component_warning": "The symmetry group need not act transitively on all irreducible components. The full-algebra normalized trace is a degree-weighted average over component traces; a chosen component's trace is not identified by these sign symmetries.",
        "alpha_alone_is_not_an_incidence_action": True,
        "source_trace_proved": False,
        "full_certificate_proved": False,
        "lean_formalized": False,
        "result": "PASS: all nine source operands are invariant; the four-sheet sign group causes no cancellation and preserves every stated open.",
    }
    (HERE / "contact_sign_audit.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"result": receipt["result"],
                      "characters": {k: {j: v[j] for j in ("J_character", "delta9_character", "D10_character", "S_and_zeta_character", "P1_and_P2_coefficient_character")}
                                     for k, v in actions.items()},
                      "checked_slots": sum(a["checked_nonzero_or_zero_coefficient_slots"] for a in actions.values()),
                      "source_trace_proved": False}, indent=2))


if __name__ == "__main__":
    main()
