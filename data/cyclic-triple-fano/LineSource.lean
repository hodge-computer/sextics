import Proposal.LineFamily
import HodgeComputer.Constructions.HoldoutCover.EvaluationMatrix

/-!
The five commuting source derivations, polynomial normal, and nonsingular
normal-plus-tangent matrix of the weighted-line family. The four endpoint
derivations are extended through the finite coefficient field; the fifth
is differentiation in the curve parameter. The constant determinant is
the transverse curve coefficient divided by the endpoint normal gradient.
-/

noncomputable section
namespace CyclicTriple
open Polynomial HoldoutConstruction

attribute [local irreducible] Endpoint.polynomial

theorem endpoint_evaluation_det_six {R : Type*} [CommRing R]
    (M : Matrix (Fin 6) (Fin 6) R) (g k : R)
    (hnormal : ∀ i : Fin 6, M i 0 = if i = 0 then g else 0)
    (htime : M 1 1 = k)
    (hmiddle : ∀ j : Fin 4, M 1 j.succ.succ = 0)
    (hendpoints : ∀ i j : Fin 4,
      M i.succ.succ j.succ.succ = if i = j then 1 else 0) :
    Matrix.det M = g*k := by
  have hc (i : Fin 5) : M i.succ 0 = 0 := by
    rw [hnormal, ite_eq_right (Fin.succ_ne_zero i)]
  rw [det_single_first_column M hc]
  have hr (j : Fin 4) : (M.submatrix Fin.succ Fin.succ) 0 j.succ = 0 :=
    hmiddle j
  rw [det_single_first_row (M.submatrix Fin.succ Fin.succ) hr]
  have hi : (M.submatrix Fin.succ Fin.succ).submatrix Fin.succ Fin.succ =
      (1 : Matrix (Fin 4) (Fin 4) R) := by
    ext i j
    exact hendpoints i j
  rw [hi, Matrix.det_one, mul_one]
  change M 0 0 * M 1 1 = g*k
  rw [hnormal, ite_eq_left rfl, htime]

namespace LineFamily

variable {c : ℂ} {E : Type*} [Field E]
variable [Algebra ℂ E] [Algebra (Endpoint.Field c) E]
variable [IsScalarTower ℂ (Endpoint.Field c) E]
variable [FiniteDimensional (Endpoint.Field c) E]

local instance : Algebra ℤ (Endpoint.Field c) := Ring.toIntAlgebra _
local instance : Algebra ℤ E := Ring.toIntAlgebra _
local instance : Algebra ℤ (CurveFunctionField E) := Ring.toIntAlgebra _

def endpointDerivation (c : ℂ) (E : Type*) [Field E]
    [Algebra (Endpoint.Field c) E] [FiniteDimensional (Endpoint.Field c) E]
    (j : Fin 4) : Derivation ℤ E E :=
  extendFiniteDerivation (L := E) (Endpoint.tangent c j)

theorem endpointDerivation_apply (j : Fin 4) (a : Endpoint.Field c) :
    endpointDerivation c E j (algebraMap (Endpoint.Field c) E a) =
      algebraMap (Endpoint.Field c) E (Endpoint.tangent c j a) :=
  extendFiniteDerivation_apply _ a

theorem endpointDerivations_commute (i j : Fin 4) :
    Function.Commute (endpointDerivation c E i) (endpointDerivation c E j) :=
  extendFiniteDerivation_commute _ _ (Endpoint.tangents_commute c i j)

@[simp] theorem endpointDerivation_base (j : Fin 4) (r : ℂ) :
    endpointDerivation c E j (algebraMap ℂ E r) = 0 := by
  rw [IsScalarTower.algebraMap_apply ℂ (Endpoint.Field c) E,
    endpointDerivation_apply, Endpoint.tangent_algebraMap, map_zero]

@[simp] theorem endpointDerivation_parameter (i j : Fin 4) :
    endpointDerivation c E i (familyEndpoint c E j.succ.succ) =
      if j = i then 1 else 0 := by
  rw [familyEndpoint_parameter, endpointDerivation_apply, Endpoint.tangent_parameter]
  split_ifs <;> simp

@[simp] theorem endpointDerivation_middle (j : Fin 4) :
    endpointDerivation c E j (familyEndpoint c E 1) = 0 := by
  rw [familyEndpoint_one, map_zero]

def polynomialDerivation (p : LineFamily c E) :
    Fin 5 → Derivation ℤ (Polynomial E) (Polynomial E) :=
  Fin.cases timePolynomialDerivation
    (fun j => coefficientPolynomialDerivation (endpointDerivation c E j))

@[simp] theorem polynomialDerivation_zero (p : LineFamily c E) :
    p.polynomialDerivation 0 = timePolynomialDerivation := rfl

@[simp] theorem polynomialDerivation_succ (p : LineFamily c E) (j : Fin 4) :
    p.polynomialDerivation j.succ =
      coefficientPolynomialDerivation (endpointDerivation c E j) := rfl

theorem polynomialDerivations_commute (p : LineFamily c E) (i j : Fin 5) :
    Function.Commute (p.polynomialDerivation i) (p.polynomialDerivation j) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · intro f; rfl
    · exact time_coefficientPolynomialDerivation_commute _
  · refine Fin.cases ?_ (fun j => ?_) j
    · exact (time_coefficientPolynomialDerivation_commute _).symm
    · exact coefficientPolynomialDerivation_commute _ _ (endpointDerivations_commute i j)

def sourceDerivation (p : LineFamily c E) (j : Fin 5) :
    Derivation ℤ (CurveFunctionField E) (CurveFunctionField E) :=
  extendRingDerivation (P := Polynomial E) (L := CurveFunctionField E)
    (p.polynomialDerivation j)

@[simp] theorem sourceDerivation_zero (p : LineFamily c E) :
    p.sourceDerivation 0 = curveTimeDerivation := rfl

@[simp] theorem sourceDerivation_succ (p : LineFamily c E) (j : Fin 4) :
    p.sourceDerivation j.succ = curveCoefficientDerivation (endpointDerivation c E j) := rfl

theorem sourceDerivations_commute (p : LineFamily c E) (i j : Fin 5) :
    Function.Commute (p.sourceDerivation i) (p.sourceDerivation j) :=
  extendRingDerivation_commute (L := CurveFunctionField E) _ _
    (p.polynomialDerivations_commute i j)

@[simp] theorem sourceDerivation_polynomial (p : LineFamily c E) (j : Fin 5)
    (f : Polynomial E) :
    p.sourceDerivation j (algebraMap (Polynomial E) (CurveFunctionField E) f) =
      algebraMap (Polynomial E) (CurveFunctionField E) (p.polynomialDerivation j f) :=
  extendRingDerivation_apply _ f

@[simp] theorem sourceDerivation_time_constant (p : LineFamily c E) (a : E) :
    p.sourceDerivation 0 (algebraMap E (CurveFunctionField E) a) = 0 :=
  curveTimeDerivation_coefficient a

@[simp] theorem sourceDerivation_time (p : LineFamily c E) (j : Fin 5) :
    p.sourceDerivation j (curveTime (E := E)) = if j = 0 then 1 else 0 := by
  refine Fin.cases ?_ (fun j => ?_) j <;> simp

@[simp] theorem sourceDerivation_base (p : LineFamily c E) (j : Fin 5) (a : ℂ) :
    p.sourceDerivation j (algebraMap E (CurveFunctionField E) (algebraMap ℂ E a)) = 0 := by
  refine Fin.cases ?_ (fun j => ?_) j <;> simp

theorem sourceDerivation_eval_range (p : LineFamily c E) (j : Fin 5)
    (x : CurveFunctionField E)
    (hx : x ∈ (Polynomial.eval₂RingHom (algebraMap E (CurveFunctionField E))
      (curveTime (E := E))).range) :
    p.sourceDerivation j x ∈
      (Polynomial.eval₂RingHom (algebraMap E (CurveFunctionField E))
        (curveTime (E := E))).range := by
  rw [curvePolynomial_eval₂] at hx ⊢
  exact extendRingDerivation_mem_range _ x hx

theorem coefficient_polynomial (a : E) :
    algebraMap E (CurveFunctionField E) a ∈
      (Polynomial.eval₂RingHom (algebraMap E (CurveFunctionField E))
        (curveTime (E := E))).range := by
  rw [curvePolynomial_eval₂]
  exact ⟨Polynomial.C a, rfl⟩

theorem curve_polynomial (p : LineFamily c E) (i : Fin 6) :
    algebraMap (Polynomial E) (CurveFunctionField E) (p.curve i) ∈
      (Polynomial.eval₂RingHom (algebraMap E (CurveFunctionField E))
        (curveTime (E := E))).range := by
  rw [curvePolynomial_eval₂]
  exact ⟨p.curve i, rfl⟩

theorem normal_polynomial (p : LineFamily c E) (i : Fin 6) :
    algebraMap (Polynomial E) (CurveFunctionField E) (p.normal i) ∈
      (Polynomial.eval₂RingHom (algebraMap E (CurveFunctionField E))
        (curveTime (E := E))).range := by
  rw [curvePolynomial_eval₂]
  exact ⟨p.normal i, rfl⟩

theorem polynomialDerivation_constant (p : LineFamily c E) (j : Fin 4) (i : Fin 6) :
    (p.polynomialDerivation j.succ (p.curve i)).coeff 0 =
      endpointDerivation c E j (familyEndpoint c E i) := by
  rw [polynomialDerivation_succ, coefficientPolynomialDerivation_coeff, curve_constant]

theorem polynomialDerivation_time_middle (p : LineFamily c E) :
    (p.polynomialDerivation 0 (p.curve 1)).coeff 0 = 1 := by
  rw [polynomialDerivation_zero, timePolynomialDerivation_apply, Polynomial.coeff_derivative]
  simpa using p.curve_one_linear

def evaluationPolynomialMatrix (p : LineFamily c E) :
    Matrix (Fin 6) (Fin 6) (Polynomial E) :=
  fun i => Fin.cases (p.normal i) (fun j => p.polynomialDerivation j (p.curve i))

@[simp] theorem evaluationPolynomialMatrix_normal (p : LineFamily c E) (i : Fin 6) :
    p.evaluationPolynomialMatrix i 0 = p.normal i := rfl

@[simp] theorem evaluationPolynomialMatrix_tangent (p : LineFamily c E)
    (i : Fin 6) (j : Fin 5) :
    p.evaluationPolynomialMatrix i j.succ = p.polynomialDerivation j (p.curve i) := rfl

theorem evaluationPolynomialMatrix_det_constant (p : LineFamily c E) :
    (Matrix.det p.evaluationPolynomialMatrix).coeff 0 =
      (gradient (algebraMap ℂ E c) (familyEndpoint c E) 0)⁻¹ * 1 := by
  rw [show (Matrix.det p.evaluationPolynomialMatrix).coeff 0 =
    Matrix.det (fun i j => (p.evaluationPolynomialMatrix i j).coeff 0) from
      (Polynomial.constantCoeff : Polynomial E →+* E).map_det p.evaluationPolynomialMatrix]
  apply endpoint_evaluation_det_six
  · intro i; exact p.normal_constant i
  · exact p.polynomialDerivation_time_middle
  · intro j
    rw [evaluationPolynomialMatrix_tangent, polynomialDerivation_constant,
      endpointDerivation_middle]
  · intro i j
    rw [evaluationPolynomialMatrix_tangent, polynomialDerivation_constant,
      endpointDerivation_parameter]

theorem evaluationPolynomialMatrix_det_ne_zero (p : LineFamily c E) :
    Matrix.det p.evaluationPolynomialMatrix ≠ 0 := by
  intro hz
  have h := p.evaluationPolynomialMatrix_det_constant
  rw [hz, Polynomial.coeff_zero] at h
  exact (mul_ne_zero (inv_ne_zero (familyEndpoint_normal c E)) one_ne_zero) h.symm

def evaluationMatrix (p : LineFamily c E) :
    Matrix (Fin 6) (Fin 6) (CurveFunctionField E) :=
  (algebraMap (Polynomial E) (CurveFunctionField E)).mapMatrix p.evaluationPolynomialMatrix

@[simp] theorem evaluationMatrix_normal (p : LineFamily c E) (i : Fin 6) :
    p.evaluationMatrix i 0 =
      algebraMap (Polynomial E) (CurveFunctionField E) (p.normal i) := rfl

@[simp] theorem evaluationMatrix_tangent (p : LineFamily c E) (i : Fin 6) (j : Fin 5) :
    p.evaluationMatrix i j.succ =
      p.sourceDerivation j (algebraMap (Polynomial E) (CurveFunctionField E) (p.curve i)) :=
  (p.sourceDerivation_polynomial j (p.curve i)).symm

theorem evaluationMatrix_det_ne_zero (p : LineFamily c E) :
    Matrix.det p.evaluationMatrix ≠ 0 := by
  have hmap : algebraMap (Polynomial E) (CurveFunctionField E)
      (Matrix.det p.evaluationPolynomialMatrix) = Matrix.det p.evaluationMatrix :=
    RingHom.map_det (algebraMap (Polynomial E) (CurveFunctionField E)) p.evaluationPolynomialMatrix
  intro hz
  apply p.evaluationPolynomialMatrix_det_ne_zero
  apply IsFractionRing.injective (Polynomial E) (CurveFunctionField E)
  simpa only [map_zero] using hmap.trans hz

theorem normal_field_pairing (p : LineFamily c E) :
    (∑ j, algebraMap (Polynomial E) (CurveFunctionField E)
      (gradient (Polynomial.C (algebraMap ℂ E c)) p.curve j) *
      algebraMap (Polynomial E) (CurveFunctionField E) (p.normal j)) = 1 := by
  have h := congrArg (algebraMap (Polynomial E) (CurveFunctionField E)) p.normal_pairing
  simpa only [polynomialPairing, map_sum, map_mul, map_one] using h

end LineFamily
end CyclicTriple

#print axioms CyclicTriple.LineFamily.sourceDerivations_commute
#print axioms CyclicTriple.LineFamily.evaluationMatrix_det_ne_zero
