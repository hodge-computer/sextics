import Proposal.BundleConic
import HodgeComputer.Constructions.HoldoutCover.PolynomialNormal

/-!
The exact positive-coefficient Jacobian gives a polynomial normal along the
complementary diagonal conic.  This is the target-specific application of
fqlx's shared polynomial-normal construction.  No bound on the eventual
certificate denominator is imposed. Developed with ChatGPT assistance.
-/

noncomputable section

namespace HoldoutBundle
open Polynomial HoldoutConstruction
open scoped BigOperators

variable {R : Type*} [Field R]

def coordinateVariation (j : Fin 12) : Fin 5 → Polynomial R :=
  Pi.single (slotCoordinate j) (X ^ slotDegree j)

def constantNormal (k : Fin 4 → R) : Fin 5 → Polynomial R :=
  Pi.single 0 (C ((6 * k 0 ^ 5)⁻¹))

private theorem pairing_single (G : Fin 5 → Polynomial R)
    (i : Fin 5) (p : Polynomial R) :
    polynomialPairing G (Pi.single i p) = G i * p := by
  simp [polynomialPairing, Pi.single_apply]

theorem coordinateVariation_pairing (G : Fin 5 → Polynomial R) (j : Fin 12) :
    polynomialPairing G (coordinateVariation j) =
      G (slotCoordinate j) * X ^ slotDegree j :=
  pairing_single G _ _

theorem slotDegree_pos (j : Fin 12) : 0 < slotDegree j := by
  fin_cases j <;> simp [slotDegree]

theorem coordinateVariation_constant (j : Fin 12) (i : Fin 5) :
    (coordinateVariation (R := R) j i).coeff 0 = 0 := by
  by_cases hi : i = slotCoordinate j
  · simp [coordinateVariation, hi, Polynomial.coeff_X_pow,
      (ne_of_gt (slotDegree_pos j)).symm]
  · simp [coordinateVariation, hi]

theorem coordinateVariation_pairing_constant (G : Fin 5 → Polynomial R) (j : Fin 12) :
    (polynomialPairing G (coordinateVariation j)).coeff 0 = 0 := by
  simp only [polynomialPairing, Polynomial.finsetSum_coeff, Polynomial.mul_coeff_zero,
    coordinateVariation_constant, mul_zero, Finset.sum_const_zero]

theorem valueCurve_constant (k : Fin 4 → R) (v : Fin 12 → R) (i : Fin 5) :
    (valueCurve k v i).coeff 0 = ![k 0, 0, k 1, k 2, k 3] i := by
  fin_cases i <;> simp [valueCurve]

theorem gradient_zero_constant (a b : R) (k : Fin 4 → R) (v : Fin 12 → R) :
    (gradient (C a) (C b) (valueCurve k v) 0).coeff 0 = 6 * k 0 ^ 5 := by
  change Polynomial.constantCoeff
    (6 * (valueCurve k v 0)^5 + 3 * (valueCurve k v 0)^2 *
      valueCurve k v 1 * valueCurve k v 3) = _
  simp only [map_add, map_mul, map_pow, map_ofNat]
  simp [Polynomial.constantCoeff_apply, valueCurve_constant]

theorem gradient_zero_degree_le (a b : R) (k : Fin 4 → R) (v : Fin 12 → R) :
    (gradient (C a) (C b) (valueCurve k v) 0).natDegree ≤ 12 := by
  simp only [gradient, Matrix.cons_val_zero]
  unfold valueCurve
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  compute_degree <;> norm_num

theorem gradientVariation_degree_le (a b : R) (k : Fin 4 → R)
    (v : Fin 12 → R) (j : Fin 12) :
    (gradient (C a) (C b) (valueCurve k v) (slotCoordinate j) * X ^ slotDegree j).natDegree ≤ 12 := by
  fin_cases j <;> dsimp [slotCoordinate, slotDegree, gradient, valueCurve]
  all_goals compute_degree <;> norm_num

/-- The normal has an exact polynomial pairing of one and the required
endpoint value. All twelve coefficient directions are retained. -/
theorem exists_polynomial_normal [CharZero R]
    (a b : R) (k : Fin 4 → R) (v : Fin 12 → R) (hk : k 0 ≠ 0)
    (hj : IsUnit (Matrix.det (fun i j : Fin 12 =>
      MvPolynomial.eval₂Hom (RingHom.id R) v
        (MvPolynomial.pderiv j (equations a b k i))))) :
    ∃ psi : Fin 5 → Polynomial R,
      polynomialPairing (gradient (C a) (C b) (valueCurve k v)) psi = 1 ∧
      ∀ i, (psi i).coeff 0 = if i = 0 then (6 * k 0 ^ 5)⁻¹ else 0 := by
  let G := gradient (C a) (C b) (valueCurve k v)
  let base := constantNormal k
  have hc : (6 : R) * k 0 ^ 5 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 5 hk)
  have hconstant : (polynomialPairing G base).coeff 0 = 1 := by
    rw [show base = Pi.single (0 : Fin 5) (C ((6 * k 0 ^ 5)⁻¹)) from rfl,
      pairing_single, Polynomial.coeff_mul_C]
    rw [gradient_zero_constant, mul_inv_cancel₀ hc]
  have hbaseBound : (polynomialPairing G base).natDegree ≤ 12 := by
    rw [show base = Pi.single (0 : Fin 5) (C ((6 * k 0 ^ 5)⁻¹)) from rfl, pairing_single]
    exact (Polynomial.natDegree_mul_C_le _ _).trans (gradient_zero_degree_le a b k v)
  have hvariationBound (j : Fin 12) :
      (polynomialPairing G (coordinateVariation j)).natDegree ≤ 12 := by
    rw [coordinateVariation_pairing]
    exact gradientVariation_degree_le a b k v j
  have hmatrix : positiveCoefficientMatrix (fun i : Fin 12 => i.val + 1)
      (fun j => polynomialPairing G (coordinateVariation j)) =
      fun i j : Fin 12 => MvPolynomial.eval₂Hom (RingHom.id R) v
        (MvPolynomial.pderiv j (equations a b k i)) := by
    ext i j
    rw [positiveCoefficientMatrix, coordinateVariation_pairing, equations_pderiv_eval,
      curveEval_eq_valueCurve]
    rfl
  have hinvertible : IsUnit (positiveCoefficientMatrix (fun i : Fin 12 => i.val + 1)
      (fun j => polynomialPairing G (coordinateVariation j))).det := by
    rwa [hmatrix]
  obtain ⟨u, hu⟩ := polynomial_normal_from_coefficients G base coordinateVariation
    (fun i : Fin 12 => i.val + 1) 12
    (fun n hn hb => ⟨⟨n-1, by omega⟩, by change n-1+1=n; omega⟩)
    hconstant (coordinateVariation_pairing_constant G) hbaseBound hvariationBound hinvertible
  let psi : Fin 5 → Polynomial R :=
    fun i => base i + ∑ j, C (u j) * coordinateVariation j i
  refine ⟨psi, hu, ?_⟩
  intro i
  simp only [psi, Polynomial.coeff_add, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul, coordinateVariation_constant, mul_zero,
    Finset.sum_const_zero, add_zero]
  by_cases hi : i = 0 <;> simp [base, constantNormal, hi]

end HoldoutBundle

#print axioms HoldoutBundle.exists_polynomial_normal
