import Proposal.GeometricLiteralAbelJacobiEvaluationAffine

/-!
# The normalized velocity of every original affine curve chart

The genuine flat first-order curve supplies a time tangent with
epsilon coefficient one. Both the sheaf evaluation and its explicit
Čech vertex corrections use this choice on the same central curve.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2LiteralAbelJacobiEvaluationChart

open CycleQ2LiteralAbelJacobiEvaluationAffine CycleQ2LiteralAbelJacobiMovingNormal
open scoped DualNumber

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  CycleQ2LiteralCylinderEvaluation.familyRing
  CycleQ2LiteralCylinderEvaluation.closedRing
  CycleQ2CurveParameterTangent.chartComplexAlgebra
  CycleQ2LiteralCylinderEvaluation.familyComplexSMul
  CycleQ2LiteralCylinderEvaluation.familyComplexModule
  CycleQ2LiteralCylinderEvaluation.reductionAlgebra
  CycleQ2LiteralCylinderEvaluation.familyReductionTower

variable (t : Fin 3 → ℂ) (i : Fin 4)

def normalizedVelocity (hi : AlgebraicIndependent ℚ t) : Derivation ℂ (B t i) (A t i) :=
  Classical.choose (exists_chart_evaluation t hi i)

theorem normalizedVelocity_epsilon (hi : AlgebraicIndependent ℚ t) :
    normalizedVelocity t i hi (algebraMap ℂ[ε] (B t i) ε) = 1 :=
  (Classical.choose_spec (exists_chart_evaluation t hi i)).1

end CycleQ2LiteralAbelJacobiEvaluationChart
end

#print axioms CycleQ2LiteralAbelJacobiEvaluationChart.normalizedVelocity_epsilon
