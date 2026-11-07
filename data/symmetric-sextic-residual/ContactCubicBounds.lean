import Proposal.ContactCubicCheckStatement
import Proposal.ContactIntegerDerivative
import Proposal.ContactExactMatrixBridge
import Proposal.ContactCubicTargetBinding

/-!
# The actual finite contact certificate implies a regular target contact

This adapter turns the ten exact integer checks in each saved row into the
analytic hypotheses for the actual sparse polynomial system. The final
finite-check module supplies `RowCertificate` without additional assumptions.
-/

noncomputable section

namespace ContactCubicBounds

open ContactCubicData ContactExactArithmetic ContactPolynomialBounds Metric
open scoped BigOperators Matrix

set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false

def jacobian : Matrix (Fin 44) (Fin 44) ℂ :=
  fun i j => (jacobianNum i j : ℂ) / (centerDen : ℂ) ^ 2

abbrev inverseMatrix : Matrix (Fin 44) (Fin 44) ℂ := inverse

theorem centerDen_pos : 0 < centerDen := by norm_num [centerDen]
theorem inverseDen_pos : 0 < inverseDen := by norm_num [inverseDen]
theorem radius_pos : 0 < radius := by norm_num [radius]
theorem radius_le_quarter : radius ≤ (1 / 4 : ℝ) := by norm_num [radius]

theorem center_den_complex_ne : (centerDen : ℂ) ≠ 0 := by
  exact_mod_cast Nat.ne_of_gt centerDen_pos

theorem system_center_eq (hcert : ∀ i, RowCertificate i) (i : Fin 44) :
    system polynomials center i =
      (residualNum i : ℂ) / ((centerDen ^ 3 : ℕ) : ℂ) := by
  rcases hcert i with ⟨hdegree, heval, _, _, _, _, _, _, _, _⟩
  have h := evalScaled_cast 3 centerDen centerDen_pos (integerPolys i) hdegree centerNum
  rw [heval] at h
  change (residualNum i : ℂ) =
    (centerDen : ℂ) ^ 3 * poly (polynomials i) center at h
  change poly (polynomials i) center = _
  rw [Nat.cast_pow]
  apply (eq_div_iff (pow_ne_zero 3 center_den_complex_ne)).mpr
  simpa only [mul_comm] using h.symm

theorem jacobian_correct (hcert : ∀ i, RowCertificate i) (i j : Fin 44) :
    jacobian i j = polyDeriv (polynomials i) center (Pi.single j 1) := by
  rcases hcert i with ⟨hdegree, _, hj, _, _, _, _, _, _, _⟩
  have h := jacobianScaled_cast centerDen centerDen_pos (integerPolys i) hdegree centerNum j
  rw [hj j] at h
  change (jacobianNum i j : ℂ) =
    (centerDen : ℂ) ^ 2 * polyDeriv (polynomials i) center (Pi.single j 1) at h
  change (jacobianNum i j : ℂ) / (centerDen : ℂ) ^ 2 = _
  apply (div_eq_iff (pow_ne_zero 2 center_den_complex_ne)).mpr
  simpa only [mul_comm] using h

theorem coordinates_bound (hcert : ∀ i, RowCertificate i) (i : Fin 44) :
    complexMass (center i) + radius ≤ (100 : ℝ) := by
  rcases hcert i with ⟨_, _, _, _, _, hc, _, _, _, _⟩
  change complexMass ((centerNum i : ℂ) / (centerDen : ℂ)) + radius ≤ _
  rw [mass_scaled]
  have hD : (0 : ℝ) < (centerDen : ℝ) := by exact_mod_cast centerDen_pos
  have hm : (4 : ℝ) * (mass (centerNum i) : ℝ) ≤ 399 * (centerDen : ℝ) := by
    exact_mod_cast hc
  have hbound : (mass (centerNum i) : ℝ) / (centerDen : ℝ) ≤ (399 / 4 : ℝ) := by
    apply (div_le_iff₀ hD).mpr
    linarith
  calc
    _ ≤ (399 / 4 : ℝ) + 1 / 4 := add_le_add hbound radius_le_quarter
    _ = 100 := by norm_num

theorem hessian_bound (hcert : ∀ i, RowCertificate i) (i : Fin 44) :
    hessianMass (polynomials i) 100 ≤ (2 : ℝ) ^ 23 := by
  rcases hcert i with ⟨hdegree, _, _, _, _, _, _, _, _, hh⟩
  change hessianMass (complexPoly (integerPolys i)) (100 : ℝ) ≤ _
  have hcast := hessianMassInt_cast 100 (integerPolys i) hdegree
  norm_num only [Nat.cast_ofNat] at hcast
  rw [hcast]
  exact_mod_cast hh

theorem inverse_row_bound (hcert : ∀ i, RowCertificate i) (i : Fin 44) :
    (∑ j, complexMass (inverse i j)) ≤ (2 : ℝ) := by
  rcases hcert i with ⟨_, _, _, _, _, _, hB, _, _, _⟩
  change (∑ j, complexMass ((inverseNum i j : ℂ) / (inverseDen : ℂ))) ≤ _
  rw [rowMass_scaled]
  have hD : (0 : ℝ) < (inverseDen : ℝ) := by exact_mod_cast inverseDen_pos
  apply (div_le_iff₀ hD).mpr
  exact_mod_cast hB

theorem defect_entry (hcert : ∀ i, RowCertificate i) (i j : Fin 44) :
    ((1 : Matrix (Fin 44) (Fin 44) ℂ) - inverseMatrix * jacobian) i j =
      (defectNum i j : ℂ) / ((inverseDen * centerDen ^ 2 : ℕ) : ℂ) := by
  rcases hcert i with ⟨_, _, _, _, he, _, _, _, _, _⟩
  have h := defect_scaled inverseNum jacobianNum inverseDen (centerDen ^ 2)
    inverseDen_pos (pow_pos centerDen_pos 2) i j
  rw [he j] at h
  have hJ : jacobian = (fun a b =>
      (jacobianNum a b : ℂ) / ((centerDen ^ 2 : ℕ) : ℂ)) := by
    ext a b
    simp only [jacobian, Nat.cast_pow]
  have hB : inverseMatrix = (fun a b =>
      (inverseNum a b : ℂ) / (inverseDen : ℂ)) := rfl
  rw [hB, hJ]
  exact h

theorem defect_row_bound (hcert : ∀ i, RowCertificate i) (i : Fin 44) :
    (∑ j, complexMass (((1 : Matrix (Fin 44) (Fin 44) ℂ) - inverseMatrix * jacobian) i j)) ≤
      (1 / 4 : ℝ) := by
  rcases hcert i with ⟨_, _, _, _, _, _, _, _, hd, _⟩
  simp_rw [defect_entry hcert i]
  rw [rowMass_scaled]
  have hD : (0 : ℝ) < ((inverseDen * centerDen ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos inverseDen_pos (pow_pos centerDen_pos 2)
  apply (div_le_iff₀ hD).mpr
  calc
    (rowMass (defectNum i) : ℝ) ≤ (2 : ℝ) ^ 382 := by exact_mod_cast hd
    _ = (1 / 4 : ℝ) * ((inverseDen * centerDen ^ 2 : ℕ) : ℝ) := by
      norm_num [inverseDen, centerDen]

theorem residual_bound (hcert : ∀ i, RowCertificate i) (i : Fin 44) :
    complexMass ((inverse *ᵥ system polynomials center) i) ≤ radius / 2 := by
  rcases hcert i with ⟨_, _, _, hdot, _, _, _, hr, _, _⟩
  change complexMass (∑ j, inverse i j * system polynomials center j) ≤ _
  simp_rw [system_center_eq hcert]
  change complexMass (∑ j, ((inverseNum i j : ℂ) / (inverseDen : ℂ)) *
    ((residualNum j : ℂ) / ((centerDen ^ 3 : ℕ) : ℂ))) ≤ _
  rw [dot_scaled, hdot, mass_scaled]
  have hD : (0 : ℝ) < ((inverseDen * centerDen ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos inverseDen_pos (pow_pos centerDen_pos 3)
  apply (div_le_iff₀ hD).mpr
  calc
    (mass (newtonResidualNum i) : ℝ) ≤ (2 : ℝ) ^ 423 := by exact_mod_cast hr
    _ = radius / 2 * ((inverseDen * centerDen ^ 3 : ℕ) : ℝ) := by
      norm_num [radius, inverseDen, centerDen]

theorem smallness_bound : (1 / 4 : ℝ) + 2 * (2 : ℝ) ^ 23 * radius ≤ 1 / 2 := by
  norm_num [radius]

theorem exists_regular_zero (hcert : ∀ i, RowCertificate i) :
    ∃ x ∈ closedBall center radius, system polynomials x = 0 ∧
      Function.Bijective (systemDeriv polynomials x) := by
  exact exists_regular_zero_of_certificate polynomials center inverseMatrix jacobian
    radius 100 ((2 : ℝ)^23) 2 (1/4) radius_pos (by norm_num) (by positivity)
    (by norm_num) (by norm_num) (coordinates_bound hcert) (hessian_bound hcert)
    (inverse_row_bound hcert) (jacobian_correct hcert) (defect_row_bound hcert)
    (residual_bound hcert) smallness_bound

/-- The integer row certificates give an actual regular root and its actual
weighted target norm identity. No root-existence hypothesis is used. -/
theorem exists_regular_target_contact (hcert : ∀ i, RowCertificate i) :
    ∃ x ∈ closedBall center radius,
      (∀ i, poly (polynomials i) x = 0) ∧
      Function.Bijective (systemDeriv polynomials x) ∧
      WeightedFiberSmoothness.weightedG =
        ContactCubicTargetBinding.firstFactor x * ContactCubicTargetBinding.secondFactor x +
        ContactCubicTargetBinding.Q2 x * ContactCubicTargetBinding.quartic x +
        (ContactCubicTargetBinding.evenCubic x + ContactCubicTargetBinding.oddCubic x) *
          (ContactCubicTargetBinding.evenCubic x - ContactCubicTargetBinding.oddCubic x) := by
  obtain ⟨x, hx, hzero, hregular⟩ := exists_regular_zero hcert
  have hz : ∀ i, poly (polynomials i) x = 0 := fun i => congrFun hzero i
  exact ⟨x, hx, hz, hregular, ContactCubicTargetBinding.weightedG_contact_identity x hz⟩

#print axioms exists_regular_zero
#print axioms exists_regular_target_contact

end ContactCubicBounds
