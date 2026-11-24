import Proposal.GeometricIncidenceTimeCurve
import Mathlib.RingTheory.Localization.BaseChange

/-!
# The actual time vector field over the generic sextic field

The generic parameter curve is the base change of the already constructed
étale incidence parameter algebra to the fraction field of the independent
sextic coefficients. This tensor product is a localization of that same
parameter algebra. Its regular complex time derivation therefore extends
through the actual formally étale localization.

Polynomial induction proves that the original derivation kills the sextic
coefficient ring. The localization denominator identity then proves that
the extended derivation kills the entire generic sextic field. We retain
the same function as a derivation over that field.

Finally, the original projective trace numerator maps to a unit in this
nontrivial generic parameter algebra. Consequently the derivatives of the
actual mapped cubic coefficients cannot all come from a scalar rescaling.
There is no supplied derivation, generic coefficient point, or
non-rescaling premise.

The geometric strategy is due to Ben
Diamond and the cited work of Claire Voisin. Prepared for fqlx with OpenAI
ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GenericTimeDerivation

open MvPolynomial Matrix
open CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceUniversalChart CycleQ2IncidenceTraceDirection
  CycleQ2IncidenceProjectiveTrace CycleQ2PolynomialProjectiveTrace
  CycleQ2IncidenceTraceFamily CycleQ2IncidenceTraceDerivative
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceTimeCurve
  CycleQ2SegreModularDetectorMatrixBinding
open scoped TensorProduct

attribute [local instance] CycleQ2IncidenceTimeCurve.timeParameterCommRing
  CycleQ2IncidenceTimeCurve.parameter_sexticModule
  CycleQ2IncidenceTimeCurve.genericSexticModule

local instance parameterComplexModule : Module ℂ ParameterAlgebra := Algebra.toModule
local instance sexticComplexModule : Module ℂ SexticRing := Algebra.toModule
local instance complexSexticSMul : SMul ℂ SexticRing := sexticComplexModule.toSMul
local instance sexticParameterSMul : SMul SexticRing ParameterAlgebra :=
  CycleQ2IncidenceTimeCurve.parameter_sexticModule.toSMul
local instance complexParameterSMul : SMul ℂ ParameterAlgebra := parameterComplexModule.toSMul
local instance genericTimeCommRing : CommRing GenericTimeAlgebra := inferInstance

/-! ## The actual scalar maps -/

private theorem sexticToTrace_C (c : ℂ) : sexticToTrace (C c) = C c :=
  MvPolynomial.rename_C _ _

@[simp] theorem sexticToParameter_C (c : ℂ) :
    sexticToParameter (C c) = algebraMap ℂ ParameterAlgebra c :=
  (congrArg (algebraMap TraceRing ParameterAlgebra) (sexticToTrace_C c)).trans
    (IsScalarTower.algebraMap_apply ℂ TraceRing ParameterAlgebra c).symm

/-- The inclusion of sextic coefficients preserves the original complex
scalar structure on the unchanged parameter algebra. -/
instance parameter_complex_sextic_tower :
    IsScalarTower ℂ SexticRing ParameterAlgebra :=
  IsScalarTower.of_algebraMap_eq (R := ℂ) (S := SexticRing) (A := ParameterAlgebra)
    (fun c => (sexticToParameter_C c).symm)

/-- This is exactly the ring map whose spectrum is
`genericTimeCurveToParameters`. -/
def parameterToGeneric : ParameterAlgebra →+* GenericTimeAlgebra :=
  (Algebra.TensorProduct.includeRight :
    ParameterAlgebra →ₐ[SexticRing] GenericTimeAlgebra).toRingHom

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local instance genericTimeFieldModule : Module GenericSexticField GenericTimeAlgebra :=
  Algebra.toModule

local instance genericTime_complex_parameter_tower :
    IsScalarTower ℂ ParameterAlgebra GenericTimeAlgebra := by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change (algebraMap ℂ GenericSexticField c) ⊗ₜ[SexticRing] (1 : ParameterAlgebra) =
    (1 : GenericSexticField) ⊗ₜ[SexticRing] (algebraMap ℂ ParameterAlgebra c)
  rw [IsScalarTower.algebraMap_apply ℂ SexticRing GenericSexticField,
    IsScalarTower.algebraMap_apply ℂ SexticRing ParameterAlgebra]
  exact Algebra.TensorProduct.algebraMap_apply'
    (R := SexticRing) (A := GenericSexticField) (B := ParameterAlgebra)
    (algebraMap ℂ SexticRing c)

local instance genericTime_sextic_field_tower :
    IsScalarTower SexticRing GenericSexticField GenericTimeAlgebra := by
  exact IsScalarTower.of_algebraMap_eq
    (R := SexticRing) (S := GenericSexticField) (A := GenericTimeAlgebra)
    (fun p => by
      simp only [Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply])

@[simp] theorem parameterToGeneric_complex (c : ℂ) :
    parameterToGeneric (algebraMap ℂ ParameterAlgebra c) =
      algebraMap ℂ GenericTimeAlgebra c :=
  (IsScalarTower.algebraMap_apply ℂ ParameterAlgebra GenericTimeAlgebra c).symm

@[simp] theorem parameterToGeneric_sextic (p : SexticRing) :
    parameterToGeneric (sexticToParameter p) =
      algebraMap SexticRing GenericTimeAlgebra p :=
  (Algebra.TensorProduct.includeRight :
    ParameterAlgebra →ₐ[SexticRing] GenericTimeAlgebra).commutes p

/-- Fraction-field base change is localization of the original parameter
algebra at the images of nonzero sextic polynomials. -/
local instance genericTime_localization :
    IsLocalization
      (Algebra.algebraMapSubmonoid ParameterAlgebra (nonZeroDivisors SexticRing))
      GenericTimeAlgebra := by
  infer_instance

local instance genericTime_formallyEtale :
    Algebra.FormallyEtale ParameterAlgebra GenericTimeAlgebra :=
  Algebra.FormallyEtale.of_isLocalization
    (Algebra.algebraMapSubmonoid ParameterAlgebra (nonZeroDivisors SexticRing))

/-! ## Extending the regular time derivation -/

/-- The original vector field kills every polynomial in the independent
sextic coefficients, not just their individual coordinates. -/
theorem timeDerivation_sextic (p : SexticRing) :
    CycleQ2IncidenceEtaleParameter.timeDerivation (sexticToParameter p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      rw [sexticToParameter_C, Derivation.map_algebraMap]
  | add p q hp hq =>
      simp only [map_add, hp, hq, add_zero]
  | mul_X p j hp =>
      simp only [map_mul, Derivation.leibniz, sexticToParameter_X,
        timeDerivation_sexticParameter, hp, smul_zero, add_zero]

/-- The complex derivation on the actual localization of the parameter
algebra. Its construction supplies all extension compatibility. -/
def complexTimeDerivation : Derivation ℂ GenericTimeAlgebra GenericTimeAlgebra :=
  CycleQ2EtaleDerivation.extend
    (S := GenericTimeAlgebra) CycleQ2IncidenceEtaleParameter.timeDerivation

@[simp] theorem complexTimeDerivation_parameter (a : ParameterAlgebra) :
    complexTimeDerivation (parameterToGeneric a) =
      parameterToGeneric (CycleQ2IncidenceEtaleParameter.timeDerivation a) :=
  CycleQ2EtaleDerivation.extend_algebraMap
    CycleQ2IncidenceEtaleParameter.timeDerivation a

theorem complexTimeDerivation_sextic (p : SexticRing) :
    complexTimeDerivation (algebraMap SexticRing GenericTimeAlgebra p) = 0 := by
  rw [← parameterToGeneric_sextic, complexTimeDerivation_parameter,
    timeDerivation_sextic, map_zero]

/-- Write a generic scalar as a fraction, differentiate the denominator
identity, and cancel the image of the denominator, which is a unit. -/
theorem complexTimeDerivation_genericField (a : GenericSexticField) :
    complexTimeDerivation (algebraMap GenericSexticField GenericTimeAlgebra a) = 0 := by
  obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors SexticRing) a
  have hidentity :
      algebraMap GenericSexticField GenericTimeAlgebra a *
        algebraMap SexticRing GenericTimeAlgebra (q : SexticRing) =
      algebraMap SexticRing GenericTimeAlgebra p := by
    have h := congrArg (algebraMap GenericSexticField GenericTimeAlgebra) hpq
    simpa only [map_mul,
      ← IsScalarTower.algebraMap_apply SexticRing GenericSexticField GenericTimeAlgebra]
      using h
  have hderivative := congrArg complexTimeDerivation hidentity
  simp only [Derivation.leibniz, complexTimeDerivation_sextic,
    smul_zero, zero_add, smul_eq_mul] at hderivative
  have hunit : IsUnit (algebraMap SexticRing GenericTimeAlgebra (q : SexticRing)) := by
    simpa only
      [← IsScalarTower.algebraMap_apply SexticRing GenericSexticField GenericTimeAlgebra]
      using (IsLocalization.map_units GenericSexticField q).map
        (algebraMap GenericSexticField GenericTimeAlgebra)
  apply hunit.mul_left_cancel
  simpa only [mul_zero, zero_add] using hderivative

/-- The same regular vector field, now correctly linear over the full
generic sextic field. -/
def genericTimeDerivation :
    Derivation GenericSexticField GenericTimeAlgebra GenericTimeAlgebra where
  toLinearMap :=
    { toFun := complexTimeDerivation
      map_add' := map_add complexTimeDerivation
      map_smul' := by
        intro a x
        simp only [RingHom.id_apply, Algebra.smul_def]
        rw [Derivation.leibniz, complexTimeDerivation_genericField,
          smul_zero, add_zero, smul_eq_mul] }
  map_one_eq_zero' := complexTimeDerivation.map_one_eq_zero
  leibniz' := complexTimeDerivation.leibniz

@[simp] theorem genericTimeDerivation_apply (a : GenericTimeAlgebra) :
    genericTimeDerivation a = complexTimeDerivation a := rfl

@[simp] theorem genericTimeDerivation_parameter (a : ParameterAlgebra) :
    genericTimeDerivation (parameterToGeneric a) =
      parameterToGeneric (CycleQ2IncidenceEtaleParameter.timeDerivation a) :=
  complexTimeDerivation_parameter a

/-- The retained external time coordinate on the actual generic curve. -/
def genericTimeParameter : GenericTimeAlgebra :=
  parameterToGeneric (algebraMap TraceRing ParameterAlgebra traceParameter)

theorem genericTimeDerivation_time : genericTimeDerivation genericTimeParameter = 1 := by
  rw [genericTimeParameter, genericTimeDerivation_parameter,
    timeDerivation_traceParameter, map_one]

theorem genericTimeDerivation_ne_zero : genericTimeDerivation ≠ 0 := by
  intro h
  have ht := genericTimeDerivation_time
  rw [h, Derivation.zero_apply] at ht
  exact zero_ne_one ht

/-! ## The unchanged incidence coefficients and their projective motion -/

/-- These are the original universal incidence coordinates after the
actual base-change map to the generic parameter curve. -/
def genericIncidencePoint (j : ParameterIndex) : GenericTimeAlgebra :=
  parameterToGeneric (incidencePoint j)

theorem genericIncidencePoint_sextic (j : FullInvariantIndex 6) :
    genericIncidencePoint (Sum.inr (Sum.inl j)) =
      algebraMap GenericSexticField GenericTimeAlgebra
        (algebraMap SexticRing GenericSexticField (X j)) := by
  rw [genericIncidencePoint, incidence_sextic_fixed,
    ← sexticToParameter_X, parameterToGeneric_sextic]
  exact IsScalarTower.algebraMap_apply
    SexticRing GenericSexticField GenericTimeAlgebra (X j)

theorem genericIncidencePoint_derivative (j : ParameterIndex) :
    genericTimeDerivation (genericIncidencePoint j) =
      parameterToGeneric (CycleQ2IncidenceEtaleParameter.timeDerivation (incidencePoint j)) :=
  genericTimeDerivation_parameter (incidencePoint j)

theorem genericIncidencePoint_sextic_derivative_zero (j : FullInvariantIndex 6) :
    genericTimeDerivation (genericIncidencePoint (Sum.inr (Sum.inl j))) = 0 := by
  rw [genericIncidencePoint_sextic, Derivation.map_algebraMap]

/-- The projective trace numerator was already protected on the original
regular parameter algebra. No fraction-field argument is used here. -/
theorem incidence_projectiveTraceNumerator_isUnit :
    IsUnit (incidencePoint (Sum.inl fullCubicLeadingIndex) *
      CycleQ2IncidenceEtaleParameter.timeDerivation
        ((algebraMap ℂ ParameterAlgebra ∘ traceWeights) ⬝ᵥ incidencePoint) -
      ((algebraMap ℂ ParameterAlgebra ∘ traceWeights) ⬝ᵥ incidencePoint) *
        CycleQ2IncidenceEtaleParameter.timeDerivation
          (incidencePoint (Sum.inl fullCubicLeadingIndex))) :=
  actual_derivative_projective_trace_isUnit
    CycleQ2IncidenceEtaleParameter.timeDerivation timeDerivation_traceParameter
    timeDerivation_sexticParameter splitting.P splitting.B sliceCoordinate
    incidence_isTracePoint.1 incidence_isTracePoint.2.1

def genericTraceValue : GenericTimeAlgebra :=
  (algebraMap ℂ GenericTimeAlgebra ∘ traceWeights) ⬝ᵥ genericIncidencePoint

theorem parameterToGeneric_traceValue :
    parameterToGeneric ((algebraMap ℂ ParameterAlgebra ∘ traceWeights) ⬝ᵥ incidencePoint) =
      genericTraceValue := by
  simp only [genericTraceValue, dotProduct, Function.comp_apply,
    map_sum, map_mul, parameterToGeneric_complex, genericIncidencePoint]

def genericProjectiveTraceNumerator : GenericTimeAlgebra :=
  genericIncidencePoint (Sum.inl fullCubicLeadingIndex) *
      genericTimeDerivation genericTraceValue -
    genericTraceValue *
      genericTimeDerivation (genericIncidencePoint (Sum.inl fullCubicLeadingIndex))

theorem genericProjectiveTraceNumerator_eq :
    genericProjectiveTraceNumerator =
      parameterToGeneric (incidencePoint (Sum.inl fullCubicLeadingIndex) *
        CycleQ2IncidenceEtaleParameter.timeDerivation
          ((algebraMap ℂ ParameterAlgebra ∘ traceWeights) ⬝ᵥ incidencePoint) -
        ((algebraMap ℂ ParameterAlgebra ∘ traceWeights) ⬝ᵥ incidencePoint) *
          CycleQ2IncidenceEtaleParameter.timeDerivation
            (incidencePoint (Sum.inl fullCubicLeadingIndex))) := by
  simp only [genericProjectiveTraceNumerator, ← parameterToGeneric_traceValue,
    genericIncidencePoint, genericTimeDerivation_parameter, map_sub, map_mul]

theorem genericProjectiveTraceNumerator_isUnit : IsUnit genericProjectiveTraceNumerator := by
  rw [genericProjectiveTraceNumerator_eq]
  exact incidence_projectiveTraceNumerator_isUnit.map parameterToGeneric

private theorem no_rescale_after_map {A B : Type*} [CommRing A] [CommRing B] [Nontrivial B]
    (φ : A →+* B) (x₀ x₁ x₈ dx₀ dx₁ dx₈ b c : A)
    (hu : IsUnit (x₀ * (b * dx₁ + c * dx₈) - (b * x₁ + c * x₈) * dx₀))
    (a : B) (h₀ : φ dx₀ = a * φ x₀) (h₁ : φ dx₁ = a * φ x₁)
    (h₈ : φ dx₈ = a * φ x₈) : False := by
  apply (hu.map φ).ne_zero
  simp only [map_sub, map_mul, map_add]
  rw [h₀, h₁, h₈]
  ring

private theorem source_sparse_numerator_isUnit :
    IsUnit (incidencePoint (Sum.inl fullCubicLeadingIndex) *
      (algebraMap ℂ ParameterAlgebra (Complex.I / 6) *
          CycleQ2IncidenceEtaleParameter.timeDerivation (incidencePoint (Sum.inl (cubicIndex 1))) +
        algebraMap ℂ ParameterAlgebra (-(1 + Complex.I) / 6) *
          CycleQ2IncidenceEtaleParameter.timeDerivation (incidencePoint (Sum.inl (cubicIndex 8)))) -
      (algebraMap ℂ ParameterAlgebra (Complex.I / 6) * incidencePoint (Sum.inl (cubicIndex 1)) +
        algebraMap ℂ ParameterAlgebra (-(1 + Complex.I) / 6) * incidencePoint (Sum.inl (cubicIndex 8))) *
        CycleQ2IncidenceEtaleParameter.timeDerivation (incidencePoint (Sum.inl fullCubicLeadingIndex))) := by
  have h := incidence_projectiveTraceNumerator_isUnit
  rw [derivation_linear_value] at h
  simpa only [mapped_traceWeights_formula] using h

private theorem mapped_cubic_not_rescaling :
    ¬ ∃ a : GenericTimeAlgebra, ∀ j : FullInvariantIndex 3,
      parameterToGeneric (CycleQ2IncidenceEtaleParameter.timeDerivation (incidencePoint (Sum.inl j))) =
        a * parameterToGeneric (incidencePoint (Sum.inl j)) := by
  rintro ⟨a, ha⟩
  exact no_rescale_after_map parameterToGeneric
    (incidencePoint (Sum.inl fullCubicLeadingIndex))
    (incidencePoint (Sum.inl (cubicIndex 1))) (incidencePoint (Sum.inl (cubicIndex 8)))
    (CycleQ2IncidenceEtaleParameter.timeDerivation (incidencePoint (Sum.inl fullCubicLeadingIndex)))
    (CycleQ2IncidenceEtaleParameter.timeDerivation (incidencePoint (Sum.inl (cubicIndex 1))))
    (CycleQ2IncidenceEtaleParameter.timeDerivation (incidencePoint (Sum.inl (cubicIndex 8))))
    (algebraMap ℂ ParameterAlgebra (Complex.I / 6))
    (algebraMap ℂ ParameterAlgebra (-(1 + Complex.I) / 6))
    source_sparse_numerator_isUnit a (ha _) (ha _) (ha _)

/-- The cubic retains projective motion over the
generic sextic field: no scalar in the actual parameter algebra accounts
for all of its coefficient derivatives. -/
theorem generic_cubic_derivative_not_rescaling :
    ¬ ∃ a : GenericTimeAlgebra, ∀ j : FullInvariantIndex 3,
      genericTimeDerivation (genericIncidencePoint (Sum.inl j)) =
        a * genericIncidencePoint (Sum.inl j) := by
  rintro ⟨a, ha⟩
  exact mapped_cubic_not_rescaling ⟨a, fun j =>
    (genericIncidencePoint_derivative (Sum.inl j)).symm.trans (ha j)⟩

end CycleQ2GenericTimeDerivation

#print axioms CycleQ2GenericTimeDerivation.complexTimeDerivation_genericField
#print axioms CycleQ2GenericTimeDerivation.genericTimeDerivation_time
#print axioms CycleQ2GenericTimeDerivation.genericProjectiveTraceNumerator_isUnit
#print axioms CycleQ2GenericTimeDerivation.generic_cubic_derivative_not_rescaling

end
