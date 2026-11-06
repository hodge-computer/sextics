import HodgeComputer.Constructions.HoldoutCover.CurveFamily
import Proposal.PolynomialNormal

/- Source component: ConicNormal -/
section
/-!
The polynomial normal vector for the actual anchored holdout conic family.
Invertibility is that of the evaluated twelve coefficient equations; all
degree and constant-coefficient hypotheses are proved for this family.
-/

noncomputable section

namespace HoldoutConicIncidence

open Polynomial HoldoutConstruction
open scoped BigOperators

variable {R : Type*} [Field R]

/-- Positive-degree variations in precisely the twelve incidence variables. -/
def coordinateVariation (j : Index) : Fin 5 → Polynomial R :=
  Pi.single (coefficientCoordinate j) (Polynomial.X^coefficientDegree j)

/-- The constant normal direction on the endpoint chart `x₁=0`, `x₀≠0`. -/
def constantNormal (x : Fin 5 → R) : Fin 5 → Polynomial R :=
  Pi.single 0 (Polynomial.C ((6*x 0^5)⁻¹))

private theorem pairing_single (G : Fin 5 → Polynomial R)
    (i : Fin 5) (p : Polynomial R) :
    polynomialPairing G (Pi.single i p) = G i*p := by
  simp [polynomialPairing, Pi.single_apply]

theorem coordinateVariation_pairing (G : Fin 5 → Polynomial R) (j : Index) :
    polynomialPairing G (coordinateVariation j) =
      G (coefficientCoordinate j)*Polynomial.X^coefficientDegree j :=
  pairing_single G _ _

theorem coordinateVariation_constant (j : Index) (i : Fin 5) :
    (coordinateVariation (R := R) j i).coeff 0 = 0 := by
  by_cases hi : i = coefficientCoordinate j
  · simp [coordinateVariation, hi, Polynomial.coeff_X_pow,
      (ne_of_gt (coefficientDegree_pos j)).symm]
  · simp [coordinateVariation, hi]

theorem coordinateVariation_pairing_constant (G : Fin 5 → Polynomial R) (j : Index) :
    (polynomialPairing G (coordinateVariation j)).coeff 0 = 0 := by
  simp only [polynomialPairing, Polynomial.finsetSum_coeff, Polynomial.mul_coeff_zero,
    coordinateVariation_constant, mul_zero, Finset.sum_const_zero]

theorem gradient_zero_constant (alpha beta k : R) (x : Fin 5 → R)
    (v : Index → R) (hx : x 1 = 0) :
    (gradient (Polynomial.C alpha) (Polynomial.C beta) (valueCurve k x v) 0).coeff 0 =
      6*x 0^5 := by
  change Polynomial.constantCoeff
    (6*(valueCurve k x v 0)^5 + 3*Polynomial.C alpha*(valueCurve k x v 0)^2*
      valueCurve k x v 1*valueCurve k x v 4) = _
  simp only [map_add, map_mul, map_pow, map_ofNat]
  simp [Polynomial.constantCoeff_apply, hx]

theorem gradient_zero_degree_le (alpha beta k : R) (x : Fin 5 → R)
    (v : Index → R) :
    (gradient (Polynomial.C alpha) (Polynomial.C beta) (valueCurve k x v) 0).natDegree ≤ 12 := by
  have h := gradientVariation_degree_le alpha beta k x v (Sum.inl 0)
  change (gradient (Polynomial.C alpha) (Polynomial.C beta) (valueCurve k x v) 0 *
    Polynomial.X^2).natDegree ≤ 12 at h
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  have hz := Polynomial.coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt h (show 12 < n+2 by omega))
  simpa only [Polynomial.coeff_mul_X_pow] using hz

/-- The actual incidence Jacobian produces a polynomial normal vector,
with no formal-series approximation or unspecified degree condition. -/
theorem exists_polynomial_normal
    [CharZero R]
    (alpha beta k : R) (x : Fin 5 → R) (v : Index → R)
    (hx₁ : x 1 = 0) (hx₀ : x 0 ≠ 0)
    (hj : IsUnit (Matrix.det (fun i j : Index =>
      coeffEval v (MvPolynomial.pderiv j (equations alpha beta k x i))))) :
    ∃ psi : Fin 5 → Polynomial R,
      polynomialPairing
        (gradient (Polynomial.C alpha) (Polynomial.C beta) (valueCurve k x v)) psi = 1 ∧
      ∀ i, (psi i).coeff 0 = if i = 0 then (6*x 0^5)⁻¹ else 0 := by
  let G := gradient (Polynomial.C alpha) (Polynomial.C beta) (valueCurve k x v)
  let b := constantNormal x
  have hc : (6:R)*x 0^5 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 5 hx₀)
  have hconstant : (polynomialPairing G b).coeff 0 = 1 := by
    rw [show b = Pi.single (0 : Fin 5) (Polynomial.C ((6*x 0^5)⁻¹)) from rfl, pairing_single,
      Polynomial.coeff_mul_C]
    rw [gradient_zero_constant alpha beta k x v hx₁, mul_inv_cancel₀ hc]
  have hbaseBound : (polynomialPairing G b).natDegree ≤ 12 := by
    rw [show b = Pi.single (0 : Fin 5) (Polynomial.C ((6*x 0^5)⁻¹)) from rfl, pairing_single]
    exact (Polynomial.natDegree_mul_C_le _ _).trans (gradient_zero_degree_le alpha beta k x v)
  have hvariationBound (j : Index) :
      (polynomialPairing G (coordinateVariation j)).natDegree ≤ 12 := by
    rw [coordinateVariation_pairing]
    exact gradientVariation_degree_le alpha beta k x v j
  have hmatrix : positiveCoefficientMatrix equationDegree
      (fun j => polynomialPairing G (coordinateVariation j)) =
      fun i j : Index => coeffEval v (MvPolynomial.pderiv j (equations alpha beta k x i)) := by
    ext i j
    rw [positiveCoefficientMatrix, coordinateVariation_pairing]
    exact (equations_pderiv_eval alpha beta k x v i j).symm
  have hinvertible : IsUnit (positiveCoefficientMatrix equationDegree
      (fun j => polynomialPairing G (coordinateVariation j))).det := by
    rwa [hmatrix]
  obtain ⟨u, hu⟩ := polynomial_normal_from_coefficients G b coordinateVariation
    equationDegree 12 (fun n hn h12 => equationDegree_covers (n := n) hn h12) hconstant
    (coordinateVariation_pairing_constant G) hbaseBound hvariationBound hinvertible
  let psi : Fin 5 → Polynomial R :=
    fun i => b i + ∑ j, Polynomial.C (u j)*coordinateVariation j i
  refine ⟨psi, hu, ?_⟩
  intro i
  simp only [psi, Polynomial.coeff_add, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul, coordinateVariation_constant, mul_zero,
    Finset.sum_const_zero, add_zero]
  by_cases hi : i = 0 <;> simp [b, constantNormal, hi]

end HoldoutConicIncidence

#print axioms HoldoutConicIncidence.exists_polynomial_normal
end
end
