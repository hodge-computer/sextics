import Proposal.BundleFamily
import HodgeComputer.Constructions.HoldoutCover.FiniteDifferentials
import HodgeComputer.Constructions.HoldoutCover.EvaluationMatrix

/-! The commuting source derivatives and the full normal-and-tangent
determinant. Endpoint coefficient derivatives remain explicit until they
are constructed on the actual finite field. The time derivative and all
three endpoint directions preserve polynomial dependence on time. -/

noncomputable section

namespace HoldoutBundle.ConicFamily
open Polynomial HoldoutConstruction
open scoped BigOperators

variable {E : Type*} [Field E] [CharZero E]
variable {a b : E} {k : Fin 4 → E} (p : HoldoutBundle.ConicFamily a b k)
variable (D : Fin 3 → Derivation ℤ E E)

local instance : Algebra ℤ E := Ring.toIntAlgebra _
local instance : Algebra ℤ (CurveFunctionField E) := Ring.toIntAlgebra _

def polynomialDerivation : Fin 4 → Derivation ℤ (Polynomial E) (Polynomial E) :=
  Fin.cases timePolynomialDerivation (fun j => coefficientPolynomialDerivation (D j))

theorem polynomialDerivations_commute
    (hD : ∀ i j, Function.Commute (D i) (D j)) (i j : Fin 4) :
    Function.Commute (polynomialDerivation D i) (polynomialDerivation D j) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · intro f; rfl
    · exact time_coefficientPolynomialDerivation_commute _
  · refine Fin.cases ?_ (fun j => ?_) j
    · exact (time_coefficientPolynomialDerivation_commute _).symm
    · exact coefficientPolynomialDerivation_commute _ _ (hD i j)

def sourceDerivation (j : Fin 4) :
    Derivation ℤ (CurveFunctionField E) (CurveFunctionField E) :=
  extendRingDerivation (P := Polynomial E) (L := CurveFunctionField E)
    (polynomialDerivation D j)

theorem sourceDerivations_commute
    (hD : ∀ i j, Function.Commute (D i) (D j)) (i j : Fin 4) :
    Function.Commute (sourceDerivation D i) (sourceDerivation D j) :=
  extendRingDerivation_commute (L := CurveFunctionField E) _ _
    (polynomialDerivations_commute D hD i j)

@[simp] theorem sourceDerivation_polynomial (j : Fin 4) (f : Polynomial E) :
    sourceDerivation D j (algebraMap (Polynomial E) (CurveFunctionField E) f) =
      algebraMap (Polynomial E) (CurveFunctionField E) (polynomialDerivation D j f) :=
  extendRingDerivation_apply _ f

@[simp] theorem sourceDerivation_time_constant (r : E) :
    sourceDerivation D 0 (algebraMap E (CurveFunctionField E) r) = 0 :=
  curveTimeDerivation_coefficient r

@[simp] theorem sourceDerivation_time :
    sourceDerivation D 0 (curveTime (E := E)) = 1 :=
  curveTimeDerivation_time

theorem sourceDerivation_coefficient (j : Fin 3) (r : E) :
    sourceDerivation D j.succ (algebraMap E (CurveFunctionField E) r) =
      algebraMap E (CurveFunctionField E) (D j r) :=
  curveCoefficientDerivation_coefficient _ _

theorem sourceDerivation_eval_range (j : Fin 4) (x : CurveFunctionField E)
    (hx : x ∈ (Polynomial.eval₂RingHom (algebraMap E (CurveFunctionField E))
      (curveTime (E := E))).range) :
    sourceDerivation D j x ∈
      (Polynomial.eval₂RingHom (algebraMap E (CurveFunctionField E))
        (curveTime (E := E))).range := by
  rw [curvePolynomial_eval₂] at hx ⊢
  exact extendRingDerivation_mem_range _ x hx

theorem coefficient_polynomial (r : E) :
    algebraMap E (CurveFunctionField E) r ∈
      (Polynomial.eval₂RingHom (algebraMap E (CurveFunctionField E))
        (curveTime (E := E))).range := by
  rw [curvePolynomial_eval₂]
  exact ⟨C r, rfl⟩

theorem polynomial_image (f : Polynomial E) :
    algebraMap (Polynomial E) (CurveFunctionField E) f ∈
      (Polynomial.eval₂RingHom (algebraMap E (CurveFunctionField E))
        (curveTime (E := E))).range := by
  rw [curvePolynomial_eval₂]
  exact ⟨f, rfl⟩

def evaluationPolynomialMatrix : Matrix (Fin 5) (Fin 5) (Polynomial E) :=
  fun i => Fin.cases (p.normal i) (fun j => polynomialDerivation D j (p.curve i))

theorem evaluationPolynomialMatrix_det_constant
    (hDk : ∀ i j : Fin 3, D i (k j.succ) = if j = i then 1 else 0) :
    (p.evaluationPolynomialMatrix D).det.coeff 0 = (6 * k 0 ^ 5)⁻¹ := by
  have h := polynomial_evaluation_det_constant (p.evaluationPolynomialMatrix D)
    ((6 * k 0 ^ 5)⁻¹) 1
  rw [mul_one] at h
  apply h
  · intro i
    exact p.normal_constant i
  · change (timePolynomialDerivation (p.curve 1)).coeff 0 = 1
    rw [p.curve_time, timePolynomialDerivation_apply]
    simp
  · intro j
    change (coefficientPolynomialDerivation (D j) (p.curve 1)).coeff 0 = 0
    rw [p.curve_time, coefficientPolynomialDerivation_coeff]
    simp
  · intro i j
    change (coefficientPolynomialDerivation (D j) (p.curve i.succ.succ)).coeff 0 = _
    rw [coefficientPolynomialDerivation_coeff, p.curve_endpoint, hDk]

theorem evaluationPolynomialMatrix_det_ne_zero
    (hDk : ∀ i j : Fin 3, D i (k j.succ) = if j = i then 1 else 0) :
    (p.evaluationPolynomialMatrix D).det ≠ 0 := by
  intro hz
  have h := p.evaluationPolynomialMatrix_det_constant D hDk
  rw [hz, Polynomial.coeff_zero] at h
  exact (inv_ne_zero p.normal_endpoint_nonzero) h.symm

def evaluationMatrix : Matrix (Fin 5) (Fin 5) (CurveFunctionField E) :=
  (algebraMap (Polynomial E) (CurveFunctionField E)).mapMatrix (p.evaluationPolynomialMatrix D)

theorem evaluationMatrix_normal (i : Fin 5) :
    p.evaluationMatrix D i 0 =
      algebraMap (Polynomial E) (CurveFunctionField E) (p.normal i) := rfl

theorem evaluationMatrix_tangent (i : Fin 5) (j : Fin 4) :
    p.evaluationMatrix D i j.succ =
      sourceDerivation D j (algebraMap (Polynomial E) (CurveFunctionField E) (p.curve i)) :=
  (sourceDerivation_polynomial D j (p.curve i)).symm

theorem evaluationMatrix_det_ne_zero
    (hDk : ∀ i j : Fin 3, D i (k j.succ) = if j = i then 1 else 0) :
    (p.evaluationMatrix D).det ≠ 0 := by
  rw [evaluationMatrix, ← RingHom.map_det]
  simpa only [map_zero] using
    (IsFractionRing.injective (Polynomial E) (CurveFunctionField E)).ne
      (p.evaluationPolynomialMatrix_det_ne_zero D hDk)

theorem normal_field_pairing :
    (∑ j, algebraMap (Polynomial E) (CurveFunctionField E)
      (gradient (C a) (C b) p.curve j) *
      algebraMap (Polynomial E) (CurveFunctionField E) (p.normal j)) = 1 := by
  have h := congrArg (algebraMap (Polynomial E) (CurveFunctionField E)) p.normal_pairing
  simpa only [polynomialPairing, map_sum, map_mul, map_one] using h

end HoldoutBundle.ConicFamily

#print axioms HoldoutBundle.ConicFamily.sourceDerivations_commute
#print axioms HoldoutBundle.ConicFamily.evaluationMatrix_det_ne_zero
