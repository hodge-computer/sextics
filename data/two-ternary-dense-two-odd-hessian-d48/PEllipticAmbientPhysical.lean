import Proposal.PEllipticAmbientBaseEmbedding
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Actual physical coordinate derivatives and volume transfer

Physical order is (X1,X2,Y0,Y1,Y2), split order is (x,y,r,z,λ).
The vector pushforward and the inverse-coordinate derivatives are explicit.
-/
set_option autoImplicit false
noncomputable section
namespace HodgeTestbed.EllipticAmbient
open HodgeTestbed.FrozenChart HodgeTestbed.Conic
open scoped BigOperators

/-- The five physical affine coordinates in the split rational function field. -/
def physicalCoordinates : Fin 5 → K :=
  ![coord 0, lambda * coord 2, coord 1, lambda, lambda * coord 3]
/-- The inverse-coordinate formula for each physical partial derivative. -/
def physicalPartial : Fin 5 → Derivation ℚ K K :=
  ![basePartial 0, lambda⁻¹ • basePartial 2, basePartial 1,
    normalPartial - (coord 2 / lambda) • basePartial 2 - (coord 3 / lambda) • basePartial 3,
    lambda⁻¹ • basePartial 3]

theorem physicalPartial_coordinates (i j : Fin 5) :
    physicalPartial i (physicalCoordinates j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [physicalPartial, physicalCoordinates, Matrix.cons_val_succ, Matrix.cons_val_two, Fin.ext_iff, sub_apply,
      smul_apply, Derivation.leibniz, smul_eq_mul, lambda, partial_coord]
  all_goals try field_simp [coord_ne_zero]
  all_goals ring

/-- The actual ordered Jacobian determinant is positive λ². -/
theorem physical_jacobian :
    Matrix.det (fun i j : Fin 5 => rationalPartial j (physicalCoordinates i)) = density := by
  have he : (fun i j : Fin 5 => rationalPartial j (physicalCoordinates i)) =
      !![1, 0, 0, 0, 0; 0, 0, lambda, 0, coord 2; 0, 1, 0, 0, 0;
        0, 0, 0, 0, 1; 0, 0, 0, lambda, coord 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [physicalCoordinates, Matrix.cons_val_succ, Matrix.cons_val_two,
        lambda, Derivation.leibniz, smul_eq_mul, partial_coord, Fin.ext_iff]
  rw [he]
  rw [Matrix.det_succ_row_zero]
  norm_num [Fin.sum_univ_succ, Matrix.submatrix, Matrix.cons_val_succ, Matrix.cons_val_two, Fin.ext_iff]
  rw [Matrix.det_succ_row_zero]
  norm_num [Fin.sum_univ_succ, Matrix.submatrix, Matrix.cons_val_succ, Matrix.cons_val_two, Fin.ext_iff]
  change -(lambda * Matrix.det !![1, 0, 0; 0, 0, 1; 0, lambda, coord 3]) -
    coord 2 * Matrix.det !![1, 0, 0; 0, 0, 0; 0, 0, lambda] = density
  norm_num [Matrix.det_fin_three, Matrix.cons_val_succ, Matrix.cons_val_two, density]
  ring

/-- The physical coordinates determine every derivation on the whole rational field. -/
theorem physical_derivation_ext (D E : Derivation ℚ K K)
    (hc : ∀ j, D (physicalCoordinates j) = E (physicalCoordinates j)) : D = E := by
  have hx : D (coord 0) = E (coord 0) := hc 0
  have hy : D (coord 1) = E (coord 1) := hc 2
  have hl : D lambda = E lambda := hc 3
  have hr : D (lambda * coord 2) = E (lambda * coord 2) := hc 1
  have hz : D (lambda * coord 3) = E (lambda * coord 3) := hc 4
  simp only [Derivation.leibniz, smul_eq_mul, hl, add_left_inj] at hr hz
  have hr' : D (coord 2) = E (coord 2) := (mul_left_cancel₀ lambda_ne_zero) hr
  have hz' : D (coord 3) = E (coord 3) := (mul_left_cancel₀ lambda_ne_zero) hz
  apply rational_derivation_ext
  intro j
  fin_cases j
  · exact hx
  · exact hy
  · exact hr'
  · exact hz'
  · exact hl

/-- These explicit physical partial derivatives genuinely commute. -/
theorem physicalPartial_commute (i j : Fin 5) :
    Function.Commute (physicalPartial i) (physicalPartial j) := by
  have hh : ⁅physicalPartial i, physicalPartial j⁆ = 0 := by
    apply physical_derivation_ext
    intro k
    simp [Derivation.commutator_apply, physicalPartial_coordinates, apply_ite]
  intro f
  have hf := Derivation.congr_fun hh f
  simpa only [Derivation.commutator_apply, zero_apply, sub_eq_zero] using hf

/-- Actual physical polynomial substitution into the split chart. -/
def physicalSubstitution : Poly 5 →ₐ[ℚ] K := MvPolynomial.aeval physicalCoordinates

/-- The physical chain rule for every polynomial, proved by Leibniz induction. -/
theorem physicalPartial_substitution (i : Fin 5) (f : Poly 5) :
    physicalPartial i (physicalSubstitution f) = physicalSubstitution (MvPolynomial.pderiv i f) := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    rw [show physicalSubstitution (MvPolynomial.C c) = algebraMap ℚ K c from MvPolynomial.aeval_C _ c,
      MvPolynomial.pderiv_C, map_zero]
    exact Derivation.map_algebraMap _ c
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f j hf =>
    have hx : physicalSubstitution (MvPolynomial.X j) = physicalCoordinates j := MvPolynomial.aeval_X _ _
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hf, hx,
      physicalPartial_coordinates, MvPolynomial.pderiv_X, Pi.single_apply]
    by_cases hij : i = j
    · subst j; simp
    · simp [hij, Ne.symm hij]

/-- The explicit coordinate pushforward, with no omitted radial components. -/
def physicalField (v : Fin 4 → K) (vnormal : K) : Fin 5 → K :=
  ![v 0, lambda * v 2 + coord 2 * vnormal, v 1, vnormal,
    lambda * v 3 + coord 3 * vnormal]

/-- The actual physical derivatives applied to the pushed field give the split action. -/
theorem physical_action (v : Fin 4 → K) (vnormal f : K) :
    fieldAction physicalPartial (physicalField v vnormal) f =
      ambientAction basePartial normalPartial v vnormal f := by
  simp only [fieldAction_apply, ambientAction, Fin.sum_univ_succ]
  norm_num [physicalField, physicalPartial, Matrix.cons_val_succ, Matrix.cons_val_two, Fin.ext_iff, sub_apply,
    smul_apply, smul_eq_mul]
  field_simp [lambda_ne_zero]
  <;> ring

/-- Direct product-rule proof of the physical divergence and volume-density transfer. -/
theorem physical_divergence (v : Fin 4 → K) (vnormal : K) :
    fieldDivergence physicalPartial (physicalField v vnormal) =
      volumeDivergence basePartial normalPartial density v vnormal := by
  simp only [fieldDivergence, volumeDivergence, Fin.sum_univ_succ]
  norm_num [physicalField, physicalPartial, density, Matrix.cons_val_succ, Matrix.cons_val_two, Fin.ext_iff,
    sub_apply, smul_apply, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, base_lambda, normal_lambda, partial_coord]
  field_simp [lambda_ne_zero]
  <;> ring

/-- Complete physical identity derived from the full four-variable defect. -/
theorem physical_lift_full (B : Fin 4 → K4) :
    fieldAction physicalPartial (physicalField (liftBase (extendBase B))
      (liftNormal (extendBase B))) (splitSubstitution Frozen.F) = splitSubstitution Frozen.A ∧
    fieldDivergence physicalPartial (physicalField (liftBase (extendBase B))
      (liftNormal (extendBase B))) =
      6 * lambda * q * (1 / (18 * p * q) - L4 (extendBase B)) -
      splitF * (1 + 6 * q * dp (extendBase B)) / (3 * p * q * lambda ^ 5) := by
  constructor
  · rw [physical_action, frozen_F_split, frozen_A_split]
    exact lifted_first _
  · rw [physical_divergence]
    exact lifted_divergence_full _ (fun i => baseEmbedding_normal _)

end HodgeTestbed.EllipticAmbient
