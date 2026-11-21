import Proposal.GeometricLiteralAbelJacobiEvaluationChart
import Proposal.GeometricLiteralAbelJacobiEvaluationSquareWedge

/-!
# The mixed evaluation formula on subopens of the projective curve germ

On each chart, the two coefficients multiplying the ordinary curve
differentials are the actual time derivatives of the original regular
functions. All coordinates are restricted through the Cartesian seed
chart.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace CycleQ2LiteralAbelJacobiEvaluationChartFormula

open CategoryTheory Opposite AlgebraicGeometry CycleQ2GeometricDifferentialSheaf
  CycleQ2LiteralAbelJacobiEvaluationAffine CycleQ2LiteralAbelJacobiEvaluationChart
  CycleQ2LiteralAbelJacobiEvaluationChartTransport CycleQ2LiteralAbelJacobiEvaluationWedge
  CycleQ2LiteralAbelJacobiEvaluationFiber CycleQ2LiteralAbelJacobiEvaluationGerm
  CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralCylinderEvaluation
  CycleQ2FirstOrderCurve CycleQ2FirstOrderCurveCharts CycleQ2FirstOrderCurveSeedFiber
  CycleQ2GeometricAffineDifferentialSheaf

attribute [local instance] CycleQ2LiteralAbelJacobiEvaluationChart.curveSectionModule
  CycleQ2LiteralAbelJacobiEvaluationChart.affineImageSectionModule
  CycleQ2LiteralCylinderEvaluation.familyRing CycleQ2LiteralCylinderEvaluation.closedRing
  CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  CycleQ2CurveParameterTangent.chartComplexAlgebra
  CycleQ2LiteralCylinderEvaluation.familyComplexSMul
  CycleQ2LiteralCylinderEvaluation.familyComplexModule
  CycleQ2LiteralCylinderEvaluation.reductionAlgebra
  CycleQ2LiteralCylinderEvaluation.familyReductionTower

variable (t : Fin 3 → ℂ) (i : Fin 4) (v : Derivation ℂ (B t i) (A t i))
  (W : (firstOrderCurve t).Opens)

/-- Computing in the seed chart gives the two normalized coefficients times the
corresponding differentials of the residual functions. -/
abbrev rawEvaluation_exact (a : Fin 2 → Γ(firstOrderCurve t,W)) :=
  (rawEvaluation_apply t i v W (exactWedge (firstOrderCurve t) (germCoefficient t) W a)).trans
    (CycleQ2LiteralAbelJacobiEvaluationSquareWedge.square_wedge (firstOrderChartToCurve t i) (seedChart t i)
      (seedCurveToFirstOrderCurve t) (seedChart_to_germ t i) (germCoefficient t) (germChart_compatible t i) v W a)

end CycleQ2LiteralAbelJacobiEvaluationChartFormula
end

#print axioms CycleQ2LiteralAbelJacobiEvaluationChartFormula.rawEvaluation_exact
