import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import HodgeComputer.Constructions.HoldoutCover.ConicPolynomialFamily
import HodgeComputer.Constructions.HoldoutCover.EndpointDerivations
import HodgeComputer.Constructions.HoldoutCover.EvaluationMatrix
import HodgeComputer.Constructions.HoldoutCover.FiniteDifferentials

/- Source component: ConicSourceDerivations -/
section
/-!
The four commuting source derivatives of the holdout conic family.
The curve parameter is the first source coordinate. The other three
derivatives are the unique finite extensions of the actual endpoint
derivatives, acting coefficientwise on the polynomial curve.

The endpoint values prove that the normal-plus-tangent evaluation matrix
has constant determinant k/(6*a0^5), so its determinant is a nonzero
polynomial. This file uses the proved generic coefficient field and the
same twelve incidence equations used for the normal vector.
-/

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace HoldoutConicIncidence

open HoldoutConstruction Polynomial

local instance : Algebra ℤ FermatEndpointField := Ring.toIntAlgebra _
local instance (p : HoldoutConic.Seed) : Algebra ℤ (ConicCoefficientField p) :=
  Ring.toIntAlgebra _
local instance (p : HoldoutConic.Seed) :
    Algebra ℤ (CurveFunctionField (ConicCoefficientField p)) := Ring.toIntAlgebra _

/-- Extend the three actual endpoint derivatives through the finite
coefficient-field extension. -/
def conicEndpointDerivation (p : HoldoutConic.Seed) (j : Fin 3) :
    Derivation ℤ (ConicCoefficientField p) (ConicCoefficientField p) :=
  extendFiniteDerivation (L := ConicCoefficientField p)
    (endpointTangent (R := FermatBaseField) j)

theorem conicEndpointDerivation_apply (p : HoldoutConic.Seed) (j : Fin 3)
    (a : FermatEndpointField) :
    conicEndpointDerivation p j (algebraMap FermatEndpointField (ConicCoefficientField p) a) =
      algebraMap FermatEndpointField (ConicCoefficientField p)
        (endpointTangent (R := FermatBaseField) j a) :=
  extendFiniteDerivation_apply _ a

theorem conicEndpointDerivations_commute (p : HoldoutConic.Seed) (i j : Fin 3) :
    Function.Commute (conicEndpointDerivation p i) (conicEndpointDerivation p j) :=
  extendFiniteDerivation_commute _ _ (endpointTangents_commute i j)

@[simp] theorem conicEndpointDerivation_base (p : HoldoutConic.Seed) (j : Fin 3)
    (a : FermatBaseField) :
    conicEndpointDerivation p j (algebraMap FermatBaseField (ConicCoefficientField p) a) = 0 := by
  rw [IsScalarTower.algebraMap_apply FermatBaseField FermatEndpointField
    (ConicCoefficientField p), conicEndpointDerivation_apply,
    endpointTangent_algebraMap, map_zero]

theorem conicEndpoint_parameter (p : HoldoutConic.Seed) (j : Fin 3) :
    conicEndpoint p j.succ.succ = conicSourceMap p (endpointParameter j) := by
  fin_cases j <;> simp [conicEndpoint, fermatEndpoint]

@[simp] theorem conicEndpointDerivation_parameter (p : HoldoutConic.Seed) (i j : Fin 3) :
    conicEndpointDerivation p i (conicEndpoint p j.succ.succ) =
      if j = i then 1 else 0 := by
  rw [conicEndpoint_parameter, conicSourceMap_parameter,
    conicEndpointDerivation_apply, endpointTangent_parameter]
  split_ifs <;> simp

@[simp] theorem conicEndpointDerivation_middle (p : HoldoutConic.Seed) (j : Fin 3) :
    conicEndpointDerivation p j (conicEndpoint p 1) = 0 := by
  rw [conicEndpoint_one, map_zero]

@[simp] theorem conicEndpointDerivation_alpha (p : HoldoutConic.Seed) (j : Fin 3) :
    conicEndpointDerivation p j (conicAlpha p) = 0 := by
  rw [conicAlpha_base, conicEndpointDerivation_base]

@[simp] theorem conicEndpointDerivation_beta (p : HoldoutConic.Seed) (j : Fin 3) :
    conicEndpointDerivation p j (conicBeta p) = 0 := by
  rw [conicBeta_base, conicEndpointDerivation_base]

@[simp] theorem conicEndpointDerivation_k (p : HoldoutConic.Seed) (j : Fin 3) :
    conicEndpointDerivation p j (conicK p) = 0 := by
  rw [conicK_base, conicEndpointDerivation_base]

theorem conicEndpointDerivation_root (p : HoldoutConic.Seed) (j : Fin 3) :
    conicEndpointDerivation p j (conicEndpoint p 0) =
      algebraMap FermatEndpointField (ConicCoefficientField p)
        (-endpointResidueMap (integerPartial j.succ
          (endpointEquation (R := FermatBaseField))) /
          endpointResidueMap (integerPartial 0
            (endpointEquation (R := FermatBaseField)))) := by
  rw [conicSourceMap_root, conicEndpointDerivation_apply, endpointTangent_root]

/-- Source derivatives on the polynomial ring, in order t, X2, S, P. -/
def conicPolynomialDerivation (p : HoldoutConic.Seed) :
    Fin 4 → Derivation ℤ (Polynomial (ConicCoefficientField p))
      (Polynomial (ConicCoefficientField p)) :=
  Fin.cases timePolynomialDerivation
    (fun j => coefficientPolynomialDerivation (conicEndpointDerivation p j))

@[simp] theorem conicPolynomialDerivation_zero (p : HoldoutConic.Seed) :
    conicPolynomialDerivation p 0 = timePolynomialDerivation := rfl

@[simp] theorem conicPolynomialDerivation_succ (p : HoldoutConic.Seed) (j : Fin 3) :
    conicPolynomialDerivation p j.succ =
      coefficientPolynomialDerivation (conicEndpointDerivation p j) := rfl

theorem conicPolynomialDerivations_commute (p : HoldoutConic.Seed) (i j : Fin 4) :
    Function.Commute (conicPolynomialDerivation p i) (conicPolynomialDerivation p j) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · intro f; rfl
    · exact time_coefficientPolynomialDerivation_commute _
  · refine Fin.cases ?_ (fun j => ?_) j
    · exact (time_coefficientPolynomialDerivation_commute _).symm
    · exact coefficientPolynomialDerivation_commute _ _
        (conicEndpointDerivations_commute p i j)

/-- Source derivations on the fraction field of the polynomial family. -/
def conicSourceDerivation (p : HoldoutConic.Seed) (j : Fin 4) :
    Derivation ℤ (CurveFunctionField (ConicCoefficientField p))
      (CurveFunctionField (ConicCoefficientField p)) :=
  extendRingDerivation (P := Polynomial (ConicCoefficientField p))
    (L := CurveFunctionField (ConicCoefficientField p)) (conicPolynomialDerivation p j)

@[simp] theorem conicSourceDerivation_zero (p : HoldoutConic.Seed) :
    conicSourceDerivation p 0 = curveTimeDerivation := rfl

@[simp] theorem conicSourceDerivation_succ (p : HoldoutConic.Seed) (j : Fin 3) :
    conicSourceDerivation p j.succ =
      curveCoefficientDerivation (conicEndpointDerivation p j) := rfl

theorem conicSourceDerivations_commute (p : HoldoutConic.Seed) (i j : Fin 4) :
    Function.Commute (conicSourceDerivation p i) (conicSourceDerivation p j) :=
  extendRingDerivation_commute (L := CurveFunctionField (ConicCoefficientField p)) _ _
    (conicPolynomialDerivations_commute p i j)

@[simp] theorem conicSourceDerivation_polynomial (p : HoldoutConic.Seed) (j : Fin 4)
    (f : Polynomial (ConicCoefficientField p)) :
    conicSourceDerivation p j
      (algebraMap (Polynomial (ConicCoefficientField p))
        (CurveFunctionField (ConicCoefficientField p)) f) =
      algebraMap (Polynomial (ConicCoefficientField p))
        (CurveFunctionField (ConicCoefficientField p)) (conicPolynomialDerivation p j f) :=
  extendRingDerivation_apply _ f

@[simp] theorem conicSourceDerivation_time_constant (p : HoldoutConic.Seed)
    (a : ConicCoefficientField p) :
    conicSourceDerivation p 0
      (algebraMap (ConicCoefficientField p) (CurveFunctionField (ConicCoefficientField p)) a) = 0 :=
  curveTimeDerivation_coefficient a

@[simp] theorem conicSourceDerivation_time (p : HoldoutConic.Seed) (j : Fin 4) :
    conicSourceDerivation p j (curveTime (E := ConicCoefficientField p)) =
      if j = 0 then 1 else 0 := by
  refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp

@[simp] theorem conicSourceDerivation_base (p : HoldoutConic.Seed) (j : Fin 4)
    (a : FermatBaseField) :
    conicSourceDerivation p j
      (algebraMap (ConicCoefficientField p) (CurveFunctionField (ConicCoefficientField p))
        (algebraMap FermatBaseField (ConicCoefficientField p) a)) = 0 := by
  refine Fin.cases ?_ (fun j => ?_) j <;> simp

theorem conicSourceDerivation_polynomial_range (p : HoldoutConic.Seed) (j : Fin 4)
    (x : CurveFunctionField (ConicCoefficientField p))
    (hx : x ∈ (algebraMap (Polynomial (ConicCoefficientField p))
      (CurveFunctionField (ConicCoefficientField p))).range) :
    conicSourceDerivation p j x ∈
      (algebraMap (Polynomial (ConicCoefficientField p))
        (CurveFunctionField (ConicCoefficientField p))).range :=
  extendRingDerivation_mem_range _ x hx

theorem conicSourceDerivation_eval_range (p : HoldoutConic.Seed) (j : Fin 4)
    (x : CurveFunctionField (ConicCoefficientField p))
    (hx : x ∈ (Polynomial.eval₂RingHom
      (algebraMap (ConicCoefficientField p) (CurveFunctionField (ConicCoefficientField p)))
      (curveTime (E := ConicCoefficientField p))).range) :
    conicSourceDerivation p j x ∈ (Polynomial.eval₂RingHom
      (algebraMap (ConicCoefficientField p) (CurveFunctionField (ConicCoefficientField p)))
      (curveTime (E := ConicCoefficientField p))).range := by
  rw [curvePolynomial_eval₂] at hx ⊢
  exact conicSourceDerivation_polynomial_range p j x hx

theorem conicCoefficient_polynomial (p : HoldoutConic.Seed) (a : ConicCoefficientField p) :
    algebraMap (ConicCoefficientField p) (CurveFunctionField (ConicCoefficientField p)) a ∈
      (Polynomial.eval₂RingHom
        (algebraMap (ConicCoefficientField p) (CurveFunctionField (ConicCoefficientField p)))
        (curveTime (E := ConicCoefficientField p))).range := by
  rw [curvePolynomial_eval₂]
  exact ⟨Polynomial.C a, rfl⟩

theorem conicCurve_polynomial (p : HoldoutConic.Seed) (i : Fin 5) :
    algebraMap (Polynomial (ConicCoefficientField p))
      (CurveFunctionField (ConicCoefficientField p)) (conicCurve p i) ∈
      (Polynomial.eval₂RingHom
        (algebraMap (ConicCoefficientField p) (CurveFunctionField (ConicCoefficientField p)))
        (curveTime (E := ConicCoefficientField p))).range := by
  rw [curvePolynomial_eval₂]
  exact ⟨conicCurve p i, rfl⟩

theorem conicPolynomialDerivation_constant (p : HoldoutConic.Seed) (j : Fin 3)
    (i : Fin 5) :
    (conicPolynomialDerivation p j.succ (conicCurve p i)).coeff 0 =
      conicEndpointDerivation p j (conicEndpoint p i) := by
  rw [conicPolynomialDerivation_succ, coefficientPolynomialDerivation_coeff,
    conicCurve_constant]

theorem conicPolynomialDerivation_time_middle (p : HoldoutConic.Seed) :
    (conicPolynomialDerivation p 0 (conicCurve p 1)).coeff 0 = conicK p := by
  rw [conicPolynomialDerivation_zero, timePolynomialDerivation_apply, conicCurve_middle]
  simp

/-- The chosen polynomial normal vector supplied by the actual conic system. -/
def conicNormal (p : HoldoutConic.Seed) : Fin 5 → Polynomial (ConicCoefficientField p) :=
  Classical.choose (α := Fin 5 → Polynomial (ConicCoefficientField p))
    (conicCurve_exists_normal p)

theorem conicNormal_pairing (p : HoldoutConic.Seed) :
    polynomialPairing (gradient (C (conicAlpha p)) (C (conicBeta p)) (conicCurve p))
      (conicNormal p) = 1 :=
  (Classical.choose_spec (conicCurve_exists_normal p)).1

@[simp] theorem conicNormal_constant (p : HoldoutConic.Seed) (i : Fin 5) :
    (conicNormal p i).coeff 0 = if i = 0 then (6*conicEndpoint p 0^5)⁻¹ else 0 :=
  (Classical.choose_spec (conicCurve_exists_normal p)).2 i

def conicEvaluationPolynomialMatrix (p : HoldoutConic.Seed) :
    Matrix (Fin 5) (Fin 5) (Polynomial (ConicCoefficientField p)) :=
  fun i => Fin.cases (conicNormal p i)
    (fun j => conicPolynomialDerivation p j (conicCurve p i))

@[simp] theorem conicEvaluationPolynomialMatrix_normal (p : HoldoutConic.Seed) (i : Fin 5) :
    conicEvaluationPolynomialMatrix p i 0 = conicNormal p i := rfl

@[simp] theorem conicEvaluationPolynomialMatrix_tangent (p : HoldoutConic.Seed)
    (i : Fin 5) (j : Fin 4) :
    conicEvaluationPolynomialMatrix p i j.succ =
      conicPolynomialDerivation p j (conicCurve p i) := rfl

theorem conicEvaluationPolynomialMatrix_det_constant (p : HoldoutConic.Seed) :
    (Matrix.det (conicEvaluationPolynomialMatrix p)).coeff 0 =
      (6*conicEndpoint p 0^5)⁻¹*conicK p := by
  apply polynomial_evaluation_det_constant
  · intro i; exact conicNormal_constant p i
  · exact conicPolynomialDerivation_time_middle p
  · intro j
    rw [conicEvaluationPolynomialMatrix_tangent, conicPolynomialDerivation_constant,
      conicEndpointDerivation_middle]
  · intro i j
    rw [conicEvaluationPolynomialMatrix_tangent, conicPolynomialDerivation_constant,
      conicEndpointDerivation_parameter]

theorem conicEvaluationPolynomialMatrix_det_ne_zero (p : HoldoutConic.Seed) :
    Matrix.det (conicEvaluationPolynomialMatrix p) ≠ 0 := by
  intro hzero
  have h := conicEvaluationPolynomialMatrix_det_constant p
  rw [hzero, Polynomial.coeff_zero] at h
  have hg : (6*conicEndpoint p 0^5 : ConicCoefficientField p) ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero _ (conicEndpoint_zero_ne p))
  exact (mul_ne_zero (inv_ne_zero hg) (conicK_ne_zero p)) h.symm

def conicEvaluationMatrix (p : HoldoutConic.Seed) :
    Matrix (Fin 5) (Fin 5) (CurveFunctionField (ConicCoefficientField p)) :=
  (algebraMap (Polynomial (ConicCoefficientField p))
    (CurveFunctionField (ConicCoefficientField p))).mapMatrix (conicEvaluationPolynomialMatrix p)

@[simp] theorem conicEvaluationMatrix_normal (p : HoldoutConic.Seed) (i : Fin 5) :
    conicEvaluationMatrix p i 0 =
      algebraMap (Polynomial (ConicCoefficientField p))
        (CurveFunctionField (ConicCoefficientField p)) (conicNormal p i) := rfl

@[simp] theorem conicEvaluationMatrix_tangent (p : HoldoutConic.Seed)
    (i : Fin 5) (j : Fin 4) :
    conicEvaluationMatrix p i j.succ = conicSourceDerivation p j
      (algebraMap (Polynomial (ConicCoefficientField p))
        (CurveFunctionField (ConicCoefficientField p)) (conicCurve p i)) :=
  (conicSourceDerivation_polynomial p j (conicCurve p i)).symm

theorem conicEvaluationMatrix_det_ne_zero (p : HoldoutConic.Seed) :
    Matrix.det (conicEvaluationMatrix p) ≠ 0 := by
  have hmap : algebraMap (Polynomial (ConicCoefficientField p))
      (CurveFunctionField (ConicCoefficientField p))
      (Matrix.det (conicEvaluationPolynomialMatrix p)) =
      Matrix.det (conicEvaluationMatrix p) :=
    RingHom.map_det (R := Polynomial (ConicCoefficientField p))
      (S := CurveFunctionField (ConicCoefficientField p))
      (algebraMap (Polynomial (ConicCoefficientField p))
        (CurveFunctionField (ConicCoefficientField p))) (conicEvaluationPolynomialMatrix p)
  intro hzero
  apply conicEvaluationPolynomialMatrix_det_ne_zero p
  apply IsFractionRing.injective (Polynomial (ConicCoefficientField p))
    (CurveFunctionField (ConicCoefficientField p))
  simpa only [map_zero] using hmap.trans hzero

theorem conicEvaluationMatrix_det_isUnit (p : HoldoutConic.Seed) :
    IsUnit (Matrix.det (conicEvaluationMatrix p)) :=
  isUnit_iff_ne_zero.mpr (conicEvaluationMatrix_det_ne_zero p)

theorem conicEvaluationMatrix_mul_inverse (p : HoldoutConic.Seed) :
    conicEvaluationMatrix p * (conicEvaluationMatrix p)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (conicEvaluationMatrix_det_isUnit p)

theorem conicEvaluationMatrix_inverse_mul (p : HoldoutConic.Seed) :
    (conicEvaluationMatrix p)⁻¹ * conicEvaluationMatrix p = 1 :=
  Matrix.nonsing_inv_mul _ (conicEvaluationMatrix_det_isUnit p)

theorem conicEvaluationMatrix_polynomial (p : HoldoutConic.Seed) (i j : Fin 5) :
    conicEvaluationMatrix p i j ∈
      (Polynomial.eval₂RingHom
        (algebraMap (ConicCoefficientField p) (CurveFunctionField (ConicCoefficientField p)))
        (curveTime (E := ConicCoefficientField p))).range := by
  rw [curvePolynomial_eval₂]
  exact ⟨conicEvaluationPolynomialMatrix p i j, rfl⟩

theorem conicNormal_polynomial (p : HoldoutConic.Seed) (i : Fin 5) :
    algebraMap (Polynomial (ConicCoefficientField p))
      (CurveFunctionField (ConicCoefficientField p)) (conicNormal p i) ∈
      (Polynomial.eval₂RingHom
        (algebraMap (ConicCoefficientField p) (CurveFunctionField (ConicCoefficientField p)))
        (curveTime (E := ConicCoefficientField p))).range := by
  rw [curvePolynomial_eval₂]
  exact ⟨conicNormal p i, rfl⟩

theorem conicNormal_derivative_polynomial (p : HoldoutConic.Seed) (i : Fin 4) (j : Fin 5) :
    conicSourceDerivation p i
      (algebraMap (Polynomial (ConicCoefficientField p))
        (CurveFunctionField (ConicCoefficientField p)) (conicNormal p j)) ∈
      (Polynomial.eval₂RingHom
        (algebraMap (ConicCoefficientField p) (CurveFunctionField (ConicCoefficientField p)))
        (curveTime (E := ConicCoefficientField p))).range :=
  conicSourceDerivation_eval_range p i _ (conicNormal_polynomial p j)

theorem conicEvaluationMatrix_mixed (p : HoldoutConic.Seed) (i k : Fin 4) (j : Fin 5) :
    conicSourceDerivation p k (conicEvaluationMatrix p j i.succ) =
      conicSourceDerivation p i (conicEvaluationMatrix p j k.succ) := by
  rw [conicEvaluationMatrix_tangent, conicEvaluationMatrix_tangent]
  exact conicSourceDerivations_commute p k i _

end HoldoutConicIncidence

#print axioms HoldoutConicIncidence.conicSourceDerivations_commute
#print axioms HoldoutConicIncidence.conicEvaluationMatrix_det_ne_zero
#print axioms HoldoutConicIncidence.conicEvaluationMatrix_mixed
end
end
