import Proposal.GeometricLiteralAbelJacobiNormal
import Proposal.GeometricLiteralAbelJacobiEquations
import Proposal.GeometricCartierDeformation
import Proposal.GeometricSquareZeroCoefficientDerivation

/-!
# Lifting the parameter tangent on a smooth closed curve chart

For a flat algebra over the dual numbers the epsilon ideal identifies with the
closed fibre. Formal smoothness of that fibre supplies a section of reduction.
The resulting coefficient derivation evaluates the original parameter to one
and induces the embedded normal functional on every defining equation.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2CurveParameterTangent

open scoped DualNumber
open CycleQ2DualNumberRegularQuotient CycleQ2LiteralAbelJacobiNormal
  CycleQ2GeometricSquareZeroSplittings CycleQ2GeometricSquareZeroCoefficientDerivation

variable {k : Type*} [Field k] (B : Type*) [CommRing B] [Algebra k[ε] B]
  [Algebra k B] [Module.Flat k[ε] B]

abbrev Fibre := B ⧸ epsilonIdeal (k := k) B

private def kernelEquiv : Fibre (k := k) B ≃ₗ[B] RingHom.ker (algebraMap B (Fibre (k := k) B)) :=
  (epsilonEquiv (k := k) B).trans (LinearEquiv.ofEq _ _ (by
    ext b
    exact Ideal.Quotient.eq_zero_iff_mem.symm))

omit [Algebra k B] in
private theorem kernelEquiv_one :
    epsilon (kernelEquiv (k := k) B) 1 = algebraMap k[ε] B ε := by
  change (algebraMap k[ε] B ε) * 1 = _
  exact mul_one _

variable [Algebra.FormallySmooth k (Fibre (k := k) B)]

/-- A parameter velocity with values on the true closed chart. -/
def velocity : Derivation k B (Fibre (k := k) B) :=
  coefficientDerivation (kernelEquiv (k := k) B)
    (smoothSplitting (K := k) (kernelEquiv (k := k) B) Ideal.Quotient.mk_surjective)
    (reduction_smoothSplitting (kernelEquiv (k := k) B) Ideal.Quotient.mk_surjective)

theorem velocity_epsilon : velocity (k := k) B (algebraMap k[ε] B ε) = 1 := by
  rw [← kernelEquiv_one, velocity, coefficientDerivation_epsilon_one]

theorem velocity_epsilon_mul (b : B) :
    velocity (k := k) B (algebraMap k[ε] B ε * b) = Ideal.Quotient.mk _ b := by
  rw [Derivation.leibniz, velocity_epsilon]
  simp only [Algebra.smul_def]
  change (Ideal.Quotient.mk _ (algebraMap k[ε] B ε)) * _ + (Ideal.Quotient.mk _ b) * 1 = _
  rw [quotient_epsilon_zero, zero_mul, zero_add, mul_one]

/-- The velocity evaluated on any ambient defining equation is the intrinsic
flat-family normal value. This holds for every formally smooth closed chart. -/
theorem velocity_equation (P : Type*) [CommRing P] [Algebra P B]
    (p : closedIdeal (k := k) B P) :
    velocity (k := k) B (algebraMap P B (p : P)) =
      normal (k := k) B P ((closedIdeal (k := k) B P).toCotangent p) := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp p.property
  rw [normal_on_lift B P p b hb, hb, velocity_epsilon_mul]

section Original

open CycleQ2IncidenceDehomogenizedChart CycleQ2FirstOrderChartReduction
  CycleQ2LiteralAbelJacobiEquations CycleQ2RelativeCurveChart
  CycleQ2IncidencePolynomialJacobianBinding

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower

variable (t : Fin 3 → ℂ) (i : Fin 4)

private abbrev Chart := FirstOrderCurveChart t i
private abbrev Seed := AffineCurveChart (seedPoint (57 : ℂ) Complex.I) t i
local instance chartRing : CommRing (Chart t i) := inferInstance
local instance seedRing : CommRing (Seed t i) := inferInstance
local instance fibreRing : CommRing (Fibre (k := ℂ) (Chart t i)) := inferInstance
local instance chartComplexAlgebra : Algebra ℂ (Chart t i) :=
  ((chartMap t i).comp MvPolynomial.C).toAlgebra

/-- Reduction respects the original complex coefficients of the section curve. -/
def chartFibreEquiv :
    (Fibre (k := ℂ) (Chart t i)) ≃ₐ[ℂ] Seed t i where
  __ := curveChartReductionEquiv t i
  commutes' c := chartMap_reduction t i (MvPolynomial.C c)

/-- On the actual smooth seed chart, the tangent to the flat family lifts
the unit parameter velocity and has the computed fixed-sextic and cubic values. -/
theorem exists_chart_velocity [Module.Flat ℂ[ε] (Chart t i)]
    [Algebra.FormallySmooth ℂ (Seed t i)] :
    ∃ v : Derivation ℂ (Chart t i) (Fibre (k := ℂ) (Chart t i)),
      v (algebraMap ℂ[ε] (Chart t i) ε) = 1 ∧
      v (chartMap t i (seedF i)) = 0 ∧
      curveChartReductionEquiv t i (v (chartMap t i (seedH i))) =
        -(seedChartMap t i (tangentL i)) := by
  let : Algebra.FormallySmooth ℂ (Fibre (k := ℂ) (Chart t i)) :=
    Algebra.FormallySmooth.of_equiv (chartFibreEquiv t i).symm
  refine ⟨velocity (k := ℂ) (Chart t i), velocity_epsilon _, ?_, ?_⟩
  · rw [chartMap_F, map_zero]
  · rw [chartMap_H, map_neg, velocity_epsilon_mul, map_neg, chartMap_reduction]

end Original

end CycleQ2CurveParameterTangent
end

#print axioms CycleQ2CurveParameterTangent.velocity_epsilon
#print axioms CycleQ2CurveParameterTangent.velocity_equation
#print axioms CycleQ2CurveParameterTangent.exists_chart_velocity
