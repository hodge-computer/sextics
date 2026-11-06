import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.Ring

/-! Extracted from `benediamond`’s accepted two-ternary dense Hessian
construction. The application and its mathematical credit are linked in README.md. -/


/-! # Polynomial and rational vector fields in commuting algebraic coordinates -/

set_option autoImplicit false
noncomputable section

namespace HodgeTestbed.Conic

open scoped BigOperators

variable {ι k R : Type*} [Fintype ι] [CommRing k] [CommRing R] [Algebra k R]

/-- A field acts as the indicated linear combination of coordinate derivations. -/
def fieldAction (δ : ι → Derivation k R R) (v : ι → R) : Derivation k R R :=
  ∑ i, v i • δ i

@[simp] theorem fieldAction_apply (δ : ι → Derivation k R R) (v : ι → R) (f : R) :
    fieldAction δ v f = ∑ i, v i * δ i f := by
  have hh := congrFun (map_sum (Derivation.coeFnAddMonoidHom (R := k) (A := R) (M := R))
    (fun i => v i • δ i) Finset.univ) f
  simpa only [fieldAction, Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply,
    Derivation.smul_apply, smul_eq_mul] using hh

/-- Coordinate divergence. -/
def fieldDivergence (δ : ι → Derivation k R R) (v : ι → R) : R := ∑ i, δ i (v i)

/-- The actual coordinate formula for the Lie bracket. -/
def fieldBracket (δ : ι → Derivation k R R) (v w : ι → R) (i : ι) : R :=
  fieldAction δ v (w i) - fieldAction δ w (v i)

theorem fieldAction_add (δ : ι → Derivation k R R) (v w : ι → R) (f : R) :
    fieldAction δ (fun i => v i + w i) f = fieldAction δ v f + fieldAction δ w f := by
  simp only [fieldAction_apply, add_mul, Finset.sum_add_distrib]

theorem fieldAction_sub (δ : ι → Derivation k R R) (v w : ι → R) (f : R) :
    fieldAction δ (fun i => v i - w i) f = fieldAction δ v f - fieldAction δ w f := by
  simp only [fieldAction_apply, sub_mul, Finset.sum_sub_distrib]

theorem fieldAction_scale (δ : ι → Derivation k R R) (a : R) (v : ι → R) (f : R) :
    fieldAction δ (fun i => a * v i) f = a * fieldAction δ v f := by
  simp only [fieldAction_apply, Finset.mul_sum, mul_assoc]

theorem fieldDivergence_add (δ : ι → Derivation k R R) (v w : ι → R) :
    fieldDivergence δ (fun i => v i + w i) = fieldDivergence δ v + fieldDivergence δ w := by
  simp only [fieldDivergence, map_add, Finset.sum_add_distrib]

theorem fieldDivergence_sub (δ : ι → Derivation k R R) (v w : ι → R) :
    fieldDivergence δ (fun i => v i - w i) = fieldDivergence δ v - fieldDivergence δ w := by
  simp only [fieldDivergence, map_sub, Finset.sum_sub_distrib]

/-- The product rule includes the derivative of the scaling factor. -/
theorem fieldDivergence_scale (δ : ι → Derivation k R R) (a : R) (v : ι → R) :
    fieldDivergence δ (fun i => a * v i) =
      fieldAction δ v a + a * fieldDivergence δ v := by
  simp only [fieldDivergence, fieldAction_apply, Derivation.leibniz, smul_eq_mul,
    Finset.sum_add_distrib, Finset.mul_sum]
  ring

/-- Differentiate a field componentwise; mixed partials produce the derivative of divergence. -/
theorem divergence_action_components (δ : ι → Derivation k R R)
    (hcomm : ∀ i j, Function.Commute (δ i) (δ j)) (v w : ι → R) :
    fieldDivergence δ (fun i => fieldAction δ v (w i)) =
      (∑ i, ∑ j, δ i (v j) * δ j (w i)) + fieldAction δ v (fieldDivergence δ w) := by
  calc
    _ = ∑ i, ∑ j, (δ i (v j) * δ j (w i) + v j * δ i (δ j (w i))) := by
      simp only [fieldDivergence, fieldAction_apply, map_sum, Derivation.leibniz, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (∑ i, ∑ j, δ i (v j) * δ j (w i)) +
        ∑ i, ∑ j, v j * δ i (δ j (w i)) := by simp only [Finset.sum_add_distrib]
    _ = _ := by
      congr 1
      simp only [fieldAction_apply, fieldDivergence, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      rw [hcomm j i (w j)]

/-- The divergence of a Lie bracket is derived from commuting coordinate derivatives. -/
theorem fieldDivergence_bracket (δ : ι → Derivation k R R)
    (hcomm : ∀ i j, Function.Commute (δ i) (δ j)) (v w : ι → R) :
    fieldDivergence δ (fieldBracket δ v w) =
      fieldAction δ v (fieldDivergence δ w) - fieldAction δ w (fieldDivergence δ v) := by
  unfold fieldBracket
  rw [fieldDivergence_sub, divergence_action_components δ hcomm,
    divergence_action_components δ hcomm]
  have hcross : (∑ i, ∑ j, δ i (v j) * δ j (w i)) =
      ∑ i, ∑ j, δ i (w j) * δ j (v i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hcross]
  ring

/-- Expand two successive field actions by the product rule. -/
theorem action_action_components (δ : ι → Derivation k R R) (v w : ι → R) (f : R) :
    fieldAction δ v (fieldAction δ w f) =
      (∑ i, fieldAction δ v (w i) * δ i f) +
        ∑ i, w i * fieldAction δ v (δ i f) := by
  conv_lhs => arg 2; rw [fieldAction_apply]
  rw [map_sum]
  simp only [Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
  simp only [mul_comm, add_comm]

/-- The coordinate bracket acts as the commutator of derivations. -/
theorem fieldAction_bracket (δ : ι → Derivation k R R)
    (hcomm : ∀ i j, Function.Commute (δ i) (δ j)) (v w : ι → R) (f : R) :
    fieldAction δ (fieldBracket δ v w) f =
      fieldAction δ v (fieldAction δ w f) - fieldAction δ w (fieldAction δ v f) := by
  have hcross : (∑ i, w i * fieldAction δ v (δ i f)) =
      ∑ i, v i * fieldAction δ w (δ i f) := by
    simp only [fieldAction_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hcomm i j f]
    ring
  rw [action_action_components, action_action_components, ← hcross]
  simp only [fieldAction_apply, fieldBracket, sub_mul, Finset.sum_sub_distrib]
  ring

end HodgeTestbed.Conic
