import Proposal.GeometricGenericPencilOpen
import Proposal.GeometricGenericWeightedCoordinates
import Proposal.GeometricProtectedPencilParameter
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.RingTheory.LaurentSeries

/-!
# Principal opens at the weighted pencil's function-field point

The deformation parameter specializes to the Laurent indeterminate. The ratio
of weighted coordinates specializes to the constant Laurent series whose
coefficient is the original transcendental pencil parameter. Consequently the
actual pair is algebraically independent, and the weighted coefficient point
lies in every principal open containing its chosen endpoint.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2BivariateLaurentEvaluation
open Polynomial

variable {k K : Type} [Field k] [Field K] [Algebra k K]

/-- Exchange the two polynomial variables, evaluate the coefficient polynomials
at the given field element, and include the remaining polynomial in Laurent series. -/
def laurentEvaluation (a : K) : Polynomial (Polynomial k) →+* LaurentSeries K :=
  (algebraMap (Polynomial K) (LaurentSeries K)).comp
    ((Polynomial.mapRingHom (Polynomial.aeval (R := k) a).toRingHom).comp
      (Polynomial.Bivariate.swap (R := k)).toRingEquiv.toRingHom)

theorem laurentEvaluation_injective (a : K)
    (ha : Function.Injective (Polynomial.aeval (R := k) a)) :
    Function.Injective (laurentEvaluation (k := k) a) :=
  (Polynomial.algebraMap_hahnSeries_injective (Γ := ℤ) (R := K)).comp
    ((Polynomial.map_injective _ ha).comp (Polynomial.Bivariate.swap (R := k)).injective)

theorem laurentEvaluation_constant (a : K) (v : k) :
    laurentEvaluation a (C (C v)) = HahnSeries.single 0 (algebraMap k K v) := by
  change algebraMap (Polynomial K) (LaurentSeries K)
    ((Bivariate.swap (C (C v))).map (aeval a).toRingHom) = _
  simp only [Bivariate.swap_C_C, Polynomial.map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    aeval_C, Polynomial.algebraMap_hahnSeries_apply, Polynomial.coe_C, HahnSeries.ofPowerSeries_C]
  all_goals rfl

theorem laurentEvaluation_tau (a : K) :
    laurentEvaluation (k := k) a (C X) = HahnSeries.single 1 1 := by
  change algebraMap (Polynomial K) (LaurentSeries K)
    ((Bivariate.swap ((C X) : Polynomial (Polynomial k))).map (aeval a).toRingHom) = _
  simp only [Bivariate.swap_X, Polynomial.map_X, Polynomial.algebraMap_hahnSeries_apply,
    Polynomial.coe_X, HahnSeries.ofPowerSeries_X]

theorem laurentEvaluation_lambda (a : K) :
    laurentEvaluation (k := k) a X = HahnSeries.single 0 a := by
  change algebraMap (Polynomial K) (LaurentSeries K)
    ((Bivariate.swap (X : Polynomial (Polynomial k))).map (aeval a).toRingHom) = _
  simp only [Bivariate.swap_Y, Polynomial.map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    aeval_X, Polynomial.algebraMap_hahnSeries_apply, Polynomial.coe_C, HahnSeries.ofPowerSeries_C]
  all_goals rfl

/-- Generator values identify any two-parameter evaluation with this injection. -/
theorem eq_laurentEvaluation (a : K) (f : Polynomial (Polynomial k) →+* LaurentSeries K)
    (hc : ∀ v, f (C (C v)) = HahnSeries.single 0 (algebraMap k K v))
    (hτ : f (C X) = HahnSeries.single 1 1) (hl : f X = HahnSeries.single 0 a) :
    f = laurentEvaluation a := by
  apply Polynomial.ringHom_ext
  · intro p
    have eqC : f.comp (C : Polynomial k →+* Polynomial (Polynomial k)) =
        (laurentEvaluation (k := k) a).comp C :=
      Polynomial.ringHom_ext (fun v => (hc v).trans (laurentEvaluation_constant a v).symm)
        (hτ.trans (laurentEvaluation_tau a).symm)
    exact RingHom.congr_fun eqC p
  · exact hl.trans (laurentEvaluation_lambda a).symm

end CycleQ2BivariateLaurentEvaluation

namespace CycleQ2GenericWeightedOpen

open CycleQ2GenericPencilOpen CycleQ2GenericPencilLift
open CycleQ2GenericSpecialization (Direction RF parameter)

attribute [local instance] CycleQ2GenericSpecialization.coefficientAlgebra

/-- Evaluate the two parameters at their actual values in the generic function field. -/
def evaluation (d : Direction) : TwoParameterRing →+* RF :=
  Polynomial.eval₂RingHom (Polynomial.aeval (R := ℂ) (parameter d)).toRingHom
    CycleQ2GenericWeightedCoordinates.lambda

@[simp] theorem evaluation_constant (d : Direction) (a : ℂ) :
    evaluation d (constantParameters a) = algebraMap ℂ RF a := by
  simp [evaluation, constantParameters]

@[simp] theorem evaluation_comp_constants (d : Direction) :
    (evaluation d).comp constantParameters = algebraMap ℂ RF :=
  RingHom.ext (evaluation_constant d)

@[simp] theorem evaluation_tau (d : Direction) :
    evaluation d tau = parameter d := by simp [evaluation, tau]

@[simp] theorem evaluation_lambda (d : Direction) :
    evaluation d CycleQ2GenericPencilOpen.lambda = CycleQ2GenericWeightedCoordinates.lambda := by
  simp [evaluation, CycleQ2GenericPencilOpen.lambda]

/-- The Laurent specialization fixes the quotient of the fourth and first affine coordinates. -/
theorem specialize_lambda (d : Direction) :
    CycleQ2GenericSpecialization.specialize d CycleQ2GenericWeightedCoordinates.lambda =
      HahnSeries.single 0 CycleQ2AffineWeightedTransfer.parameter := by
  have h (j : Fin 4) : CycleQ2GenericSpecialization.specialize d
      (CycleQ2Bridge.polynomialMap 4 (MvPolynomial.X j.succ)) =
      HahnSeries.C (Γ := ℤ) (CycleQ2FormalSpecialization.fieldCoordinate j.succ) := by
    rw [CycleQ2GenericSpecialization.specialize_polynomial,
      CycleQ2GenericSpecialization.formalMap_X_succ, HahnSeries.ofPowerSeries_C]
  change CycleQ2GenericSpecialization.specialize d
    (CycleQ2Bridge.polynomialMap 4 (MvPolynomial.X (3 : Fin 4).succ) /
      CycleQ2Bridge.polynomialMap 4 (MvPolynomial.X (0 : Fin 4).succ)) = _
  rw [map_div₀, h, h, ← map_div₀]
  rfl

/-- The two-parameter evaluation specializes to the injective Laurent-series map. -/
theorem specialize_evaluation (d : Direction) :
    (CycleQ2GenericSpecialization.specialize d).toRingHom.comp (evaluation d) =
      CycleQ2BivariateLaurentEvaluation.laurentEvaluation (k := ℂ)
        CycleQ2AffineWeightedTransfer.parameter := by
  apply CycleQ2BivariateLaurentEvaluation.eq_laurentEvaluation
  · intro a
    change CycleQ2GenericSpecialization.specialize d (evaluation d (constantParameters a)) = _
    rw [evaluation_constant, AlgHom.commutes]
    rfl
  · change CycleQ2GenericSpecialization.specialize d (evaluation d tau) = _
    rw [evaluation_tau, CycleQ2GenericSpecialization.specialize_parameter]
  · change CycleQ2GenericSpecialization.specialize d
        (evaluation d CycleQ2GenericPencilOpen.lambda) = _
    rw [evaluation_lambda, specialize_lambda]

theorem evaluation_injective (d : Direction) : Function.Injective (evaluation d) := by
  intro p q h
  apply CycleQ2BivariateLaurentEvaluation.laurentEvaluation_injective _
    CycleQ2ProtectedPencilParameter.polynomialEvaluation_injective
  rw [← specialize_evaluation d]
  exact congrArg (CycleQ2GenericSpecialization.specialize d) h

/-- The coefficient vector of the universal deformation at the actual pair. -/
def coefficientPoint (d : Direction) (c : ParameterIndex → ℂ) (e : ParameterIndex) : RF :=
  evaluation d (universalCoefficient c e)

theorem parameterPullback_evaluation (d : Direction) (c : ParameterIndex → ℂ) (f : ParameterRing) :
    evaluation d (parameterPullback c f) =
      MvPolynomial.eval₂Hom (algebraMap ℂ RF) (coefficientPoint d c) f := by
  change evaluation d (MvPolynomial.eval₂Hom constantParameters (universalCoefficient c) f) = _
  rw [MvPolynomial.map_eval₂Hom, evaluation_comp_constants]
  rfl

/-- A nonzero two-parameter pullback stays nonzero at the actual function-field point. -/
theorem coefficientPoint_ne_zero (d : Direction) (c : ParameterIndex → ℂ) (f : ParameterRing)
    (h : parameterPullback c f ≠ 0) :
    MvPolynomial.eval₂Hom (algebraMap ℂ RF) (coefficientPoint d c) f ≠ 0 := by
  rw [← parameterPullback_evaluation]
  intro hz
  exact h (evaluation_injective d (hz.trans (map_zero (evaluation d)).symm))

/-- Every nonempty principal open admits an actual endpoint direction whose
weighted pencil's function-field point lies in that open. -/
theorem exists_direction_in_principal_open (f : ParameterRing) (hf : f ≠ 0) :
    ∃ (c : ParameterIndex → ℂ) (hc : endpointDifference c ≠ 0),
      MvPolynomial.eval c f ≠ 0 ∧
      MvPolynomial.eval₂Hom (algebraMap ℂ RF) (coefficientPoint (endpointDirection c hc) c) f ≠ 0 := by
  obtain ⟨c, hgood, hc⟩ := exists_endpoint_in_principal_open f hf
  exact ⟨c, hc, hgood, coefficientPoint_ne_zero _ c f (parameterPullback_ne_zero c f hgood)⟩

end CycleQ2GenericWeightedOpen
end

#print axioms CycleQ2GenericWeightedOpen.evaluation_injective
#print axioms CycleQ2GenericWeightedOpen.parameterPullback_evaluation
#print axioms CycleQ2GenericWeightedOpen.exists_direction_in_principal_open
