import HodgeComputer.Constructions.RationalFields.Calculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! # Ambient lift from a supplied tangential three-form

All derivatives and the physical volume density are retained before reduction modulo F.
No scalar primitive or vanishing divergence is assumed in the two ambient identities.
-/
set_option autoImplicit false
noncomputable section
namespace HodgeTestbed.EllipticAmbient
open scoped BigOperators
open HodgeTestbed.Conic

variable {ι R : Type*} [Fintype ι] [Field R] [Algebra ℚ R]

/-- Components along the base coordinates, for Γ = ι_B vol_base. -/
def baseField (h m : R) (B : ι → R) (i : ι) : R := -(h / m) * B i
/-- The normal component includes the complete tangential correction. -/
def normalField (δ : ι → Derivation ℚ R R) (F A h m : R) (B : ι → R) : R :=
  A / h + fieldAction δ B F / m
/-- Actual ambient directional action, with the normal coordinate last. -/
def ambientAction (δ : ι → Derivation ℚ R R) (η : Derivation ℚ R R)
    (v : ι → R) (vnormal f : R) : R := fieldAction δ v f + vnormal * η f
/-- Divergence with respect to density m times the ordered coordinate volume. -/
def volumeDivergence (δ : ι → Derivation ℚ R R) (η : Derivation ℚ R R)
    (m : R) (v : ι → R) (vnormal : R) : R :=
  (fieldDivergence δ (fun i => m * v i) + η (m * vnormal)) / m
/-- The actual tangent derivation ∂i - (∂i F / h) ∂normal. -/
def tangent (δ : ι → Derivation ℚ R R) (η : Derivation ℚ R R)
    (F h : R) (i : ι) : Derivation ℚ R R := δ i - (δ i F / h) • η
@[simp] theorem tangent_apply (δ : ι → Derivation ℚ R R) (η : Derivation ℚ R R)
    (F h : R) (i : ι) (f : R) :
    tangent δ η F h i f = δ i f - δ i F / h * η f := rfl

/-- Tangency is a consequence of the actual normal derivative, not an assumption. -/
theorem tangent_F (δ : ι → Derivation ℚ R R) (η : Derivation ℚ R R)
    (F h : R) (hh : h ≠ 0) (hF : η F = h) (i : ι) :
    tangent δ η F h i F = 0 := by simp [hF, hh]

/-- The supplied ambient lift always has the exact selected directional action. -/
theorem ambient_first (δ : ι → Derivation ℚ R R) (η : Derivation ℚ R R)
    (F A h m : R) (B : ι → R) (hh : h ≠ 0) (hm : m ≠ 0) (hF : η F = h) :
    ambientAction δ η (baseField h m B) (normalField δ F A h m B) F = A := by
  have hb : baseField h m B = fun i => (-(h / m)) * B i := rfl
  rw [ambientAction, hb, fieldAction_scale, normalField, hF]
  field_simp
  <;> ring

/-- Full divergence, including the normal derivative of the density and target.
Commutation cancels the mixed derivatives; no desired divergence is a premise. -/
theorem ambient_divergence (δ : ι → Derivation ℚ R R) (η : Derivation ℚ R R)
    (F A h m : R) (B : ι → R) (hh : h ≠ 0) (hm : m ≠ 0) (hF : η F = h)
    (hcomm : ∀ i, Function.Commute (δ i) η) :
    volumeDivergence δ η m (baseField h m B) (normalField δ F A h m B) =
      (h / m) * (η (m * A / h) / h - fieldDivergence (tangent δ η F h) B) := by
  have hv (i : ι) : m * baseField h m B i = -h * B i := by
    unfold baseField
    field_simp
  have hn : m * normalField δ F A h m B = m * A / h + fieldAction δ B F := by
    unfold normalField
    field_simp
    <;> ring
  have hmix (i : ι) : η (δ i F) = δ i h := (hcomm i F).symm.trans (congrArg (δ i) hF)
  rw [volumeDivergence, show (fun i => m * baseField h m B i) = (fun i => -h * B i) from funext hv, hn]
  simp only [fieldDivergence, fieldAction_apply, map_add, map_sum, Derivation.leibniz,
    map_neg, smul_eq_mul, tangent_apply, hmix, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.mul_sum]
  have hc : (∑ i, B i * -(δ i h)) + ∑ i, B i * δ i h = 0 := by
    rw [← Finset.sum_add_distrib]
    simp
  have ht : (∑ i, -h * δ i (B i)) + ∑ i, δ i F * η (B i) =
      -h * ((∑ i, δ i (B i)) - ∑ i, δ i F / h * η (B i)) := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
    <;> ring
  have hzero : (∑ i, B i * -(δ i h)) + (∑ i, -h * δ i (B i)) +
      (η (m * A / h) + ((∑ i, B i * δ i h) + ∑ i, δ i F * η (B i))) =
      η (m * A / h) - h * ((∑ i, δ i (B i)) - ∑ i, δ i F / h * η (B i)) := by
    linear_combination hc + ht
  rw [show (∑ i, -h * δ i (B i)) + (∑ i, B i * -(δ i h)) =
    (∑ i, B i * -(δ i h)) + (∑ i, -h * δ i (B i)) from add_comm _ _, hzero]
  field_simp
  <;> ring

end HodgeTestbed.EllipticAmbient
