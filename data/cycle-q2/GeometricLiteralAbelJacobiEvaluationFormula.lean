import Proposal.GeometricLiteralAbelJacobiEvaluationChartFormula
import Proposal.GeometricLiteralAbelJacobiEvaluationVelocity

/-!
# The tangent evaluation of an exact wedge on the original seed curve

After computing on an affine chart, the one-form on the curve is the
alternating contraction by the time derivative on the actual section
rings. This formula holds on every subopen of that chart.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace CycleQ2LiteralAbelJacobiEvaluationFormula

open CategoryTheory Opposite AlgebraicGeometry CycleQ2GeometricDifferentialSheaf
  CycleQ2LiteralAbelJacobiEvaluationChart CycleQ2LiteralAbelJacobiEvaluationChartFormula
  CycleQ2LiteralAbelJacobiEvaluationVelocity CycleQ2LiteralAbelJacobiEvaluationWedge
  CycleQ2LiteralAbelJacobiEvaluationGerm CycleQ2LiteralAbelJacobiMovingNormal
  CycleQ2FirstOrderCurve CycleQ2FirstOrderCurveCharts CycleQ2FirstOrderCurveSeedFiber
  CycleQ2LiteralMovingResidueAdjunction.AffineFrame

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

private abbrev termOn (W : (firstOrderCurve t).Opens) (hW : W ≤ firstOrderCurveCoordinateOpen t i)
    (x y : Γ(firstOrderCurve t,W)) :=
  @SMul.smul _ _ (curveSectionModule t W).toSMul (onOpen t i v W hW x)
    ((universalDifferential (CycleQ2LiteralMovingResidueAdjunction.AffineFrame.Curve t).sheaf (curveCoefficient t)).d
      (X := op ((seedCurveToFirstOrderCurve t) ⁻¹ᵁ W)) ((seedCurveToFirstOrderCurve t).app W y))

theorem evaluation_exact (W : (firstOrderCurve t).Opens) (hW : W ≤ firstOrderCurveCoordinateOpen t i)
    (a : Fin 2 → Γ(firstOrderCurve t,W)) :
    (evaluationOn t i v).val.app (op (Over.mk (homOfLE hW))) (exactWedge _ (germCoefficient t) W a) =
      termOn t i v W hW (a 0) (a 1) - termOn t i v W hW (a 1) (a 0) := by
  apply toSeedCoordinates_injective t i W hW
  refine (evaluationOn_coordinates t i v W hW _).trans ((rawEvaluation_exact t i v W a).trans ?_)
  have term (x y : Γ(firstOrderCurve t,W)) :=
    (toSeedCoordinates_smul t i W (onOpen t i v W hW x)
      ((universalDifferential _ (curveCoefficient t)).d ((seedCurveToFirstOrderCurve t).app W y))).trans
      (congrArg₂ (@SMul.smul _ _ (affineImageSectionModule t i W).toSMul) (seedChart_app_onOpen t i v W hW x)
        (toSeedCoordinates_D t i W ((seedCurveToFirstOrderCurve t).app W y)))
  exact ((map_sub ((toSeedCoordinates t i).val.app (op W)).hom _ _).trans
    (congrArg₂ (· - ·) (term (a 0) (a 1)) (term (a 1) (a 0)))).symm

end CycleQ2LiteralAbelJacobiEvaluationFormula
end

#print axioms CycleQ2LiteralAbelJacobiEvaluationFormula.evaluation_exact
