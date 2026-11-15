import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Normalized trace and supported-class descent over a finite cover

The linear algebra of finite-cover transfer is written over Q, with its
geometric trace formula recorded explicitly as data:
  push (pull x) = degree • x,  degree > 0.
These two maps are *not* fabricated by this module. In the cycle-q2 route,
they must come from the actual finite etale cover and the corresponding
(co)homological functoriality. The results below formally deduce the
normalization, faithfulness, descent of projectors, and descent of support.

No Betti comparison, correspondence, or protected residue is assumed or
declared. This is a conditional algebraic component, not the final theorem.
-/

set_option autoImplicit false

noncomputable section

namespace CycleQ2FiniteTraceDescent

variable {V W : Type*}
variable [AddCommGroup V] [Module ℚ V]
variable [AddCommGroup W] [Module ℚ W]

/-- The exact push/pull identity of a finite cover, once its geometric maps
have been constructed. A positive natural degree prevents division by zero. -/
structure Transfer where
  degree : ℕ
  positive : 0 < degree
  pull : V →ₗ[ℚ] W
  push : W →ₗ[ℚ] V
  push_pull : ∀ v : V, push (pull v) = (degree : ℚ) • v

namespace Transfer

variable (T : Transfer (V := V) (W := W))

private theorem degree_ne_zero : (T.degree : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.ne_of_gt T.positive)

/-- The actual normalized trace (once pushforward is supplied). -/
def normalizedPush : W →ₗ[ℚ] V :=
  ((T.degree : ℚ)⁻¹) • T.push

/-- Dividing by the finite degree makes pushforward a left inverse to
pullback on *every* downstairs class. -/
theorem normalized_push_pull (v : V) : T.normalizedPush (T.pull v) = v := by
  change ((T.degree : ℚ)⁻¹) • T.push (T.pull v) = v
  rw [T.push_pull v, smul_smul, inv_mul_cancel₀ (degree_ne_zero T), one_smul]

theorem pull_injective : Function.Injective T.pull := by
  intro v w hvw
  have h := congrArg T.normalizedPush hvw
  simpa only [normalized_push_pull] using h

/-- Equality of two downstairs classes descends from equality on the
finite cover, without requiring the pullback map to be surjective. -/
theorem eq_of_pull_eq (v w : V) (h : T.pull v = T.pull w) : v = w :=
  T.pull_injective h

/-- A downstairs endomorphism is the identity if its pullback intertwines
with an upstairs endomorphism that fixes every pulled-back class. -/
theorem projector_identity_descends
    (P : Module.End ℚ V) (Q : Module.End ℚ W)
    (hcomm : ∀ v : V, T.pull (P v) = Q (T.pull v))
    (hfix : ∀ v : V, Q (T.pull v) = T.pull v) : P = 1 := by
  apply LinearMap.ext
  intro v
  apply T.pull_injective
  calc
    T.pull (P v) = Q (T.pull v) := hcomm v
    _ = T.pull v := hfix v

variable {B C : Type*}
variable [AddCommGroup B] [Module ℚ B]
variable [AddCommGroup C] [Module ℚ C]

/-- If restriction commutes with finite pushforward, vanishing of a
pulled-back class on the upstairs complement descends to the original
complement. This is the algebraic support descent required after averaging
a relative supported cycle. The restriction and trace maps remain actual
geometric inputs to be constructed. -/
theorem restriction_zero_of_cover_zero
    (rV : V →ₗ[ℚ] B) (rW : W →ₗ[ℚ] C)
    (trC : C →ₗ[ℚ] B)
    (hbase : ∀ w : W, rV (T.push w) = trC (rW w))
    (v : V) (hzero : rW (T.pull v) = 0) :
    rV v = 0 := by
  calc
    rV v = rV (T.normalizedPush (T.pull v)) := by
      rw [T.normalized_push_pull]
    _ = ((T.degree : ℚ)⁻¹) • rV (T.push (T.pull v)) := by
      change rV (((T.degree : ℚ)⁻¹) • T.push (T.pull v)) = _
      rw [map_smul]
    _ = ((T.degree : ℚ)⁻¹) • trC (rW (T.pull v)) := by
      rw [hbase (T.pull v)]
    _ = 0 := by rw [hzero, map_zero, smul_zero]

/-- The supported-image variant: a projector upstairs can witness
vanishing for the downstairs projected class via the genuine pullback. -/
theorem projector_restriction_zero_descends
    (rV : V →ₗ[ℚ] B) (rW : W →ₗ[ℚ] C)
    (trC : C →ₗ[ℚ] B)
    (hbase : ∀ w : W, rV (T.push w) = trC (rW w))
    (P : Module.End ℚ V) (Q : Module.End ℚ W)
    (hcomm : ∀ v : V, T.pull (P v) = Q (T.pull v))
    (v : V) (hsupport : rW (Q (T.pull v)) = 0) :
    rV (P v) = 0 := by
  apply restriction_zero_of_cover_zero T rV rW trC hbase
  rw [hcomm v]
  exact hsupport

end Transfer

end CycleQ2FiniteTraceDescent

end

#print axioms CycleQ2FiniteTraceDescent.Transfer.normalized_push_pull
#print axioms CycleQ2FiniteTraceDescent.Transfer.projector_identity_descends
#print axioms CycleQ2FiniteTraceDescent.Transfer.projector_restriction_zero_descends
