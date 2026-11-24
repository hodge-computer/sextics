import Proposal.GeometricLiteralAbelJacobiQTimeChartLocal
import Proposal.GeometricLiteralAbelJacobiEvaluationGlobal

/-!
# The projective time evaluation on the original affine seed charts

For an arbitrary two-form of the time family, first restrict to an open
of the projective seed curve under a germ coordinate chart. Its affine
one-form is the evaluation of the directly restricted two-form on the
original affine first-order chart, at the normalized parameter velocity.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralAbelJacobiQTimeChart

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
  CycleQ2LiteralAbelJacobiQEvaluationTransport CycleQ2LiteralAbelJacobiEvaluationGlobal
  CycleQ2LiteralAbelJacobiEvaluationFiber CycleQ2LiteralAbelJacobiEvaluationGerm
  CycleQ2LiteralAbelJacobiEvaluationAffine CycleQ2LiteralAbelJacobiEvaluationChart
  CycleQ2LiteralAbelJacobiEvaluationChartTransport CycleQ2LiteralAbelJacobiEvaluationSeedForms
  CycleQ2LiteralAbelJacobiEvaluationRestriction CycleQ2LiteralAbelJacobiTimeCharts
  CycleQ2LiteralAbelJacobiTimeFamily CycleQ2LiteralAbelJacobiQPullback
  CycleQ2GeometricSchemeDifferentialMap CycleQ2GeometricAffineDifferentialSheaf
  CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralCylinderEvaluation
  CycleQ2FirstOrderCurve CycleQ2FirstOrderCurveCharts CycleQ2FirstOrderCurveSeedFiber
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceSeedFiberCover
  CycleQ2LiteralMovingResidueAdjunction.AffineFrame CycleQ2LiteralMovingResidueCurve

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  familyRing closedRing CycleQ2CurveParameterTangent.chartComplexAlgebra
  familyComplexSMul familyComplexModule reductionAlgebra familyReductionTower

variable (t : Fin 3 → ℂ) (ht : AlgebraicIndependent ℚ t) (i : Fin 4)

variable (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V) (U : (family V t).Opens)
  (O : (firstOrderCurve t).Opens) (hO : O ≤ (germToTime t V hV) ⁻¹ᵁ U)
  (hi : O ≤ firstOrderCurveCoordinateOpen t i) (W : (Curve t).Opens)
  (hW : W ≤ (seedCurveToFirstOrderCurve t) ⁻¹ᵁ O) (hWU : W ≤ (seedToTime t V hV) ⁻¹ᵁ U)

include hi in
/-- Evaluate first on the projective family and restrict to seed coordinates, or pull its
two-form to the first-order affine chart and contract there, then restrict the one-form. -/
theorem timeEvaluation_coordinates (x : (familyTwoForms V t).val.obj (op U)) :
    (seedFormsMap t i).val.app (op W)
      (onSubopen (curveDifferentials t) hWU ((timeEvaluation t ht V hV).val.app (op U) x)) =
    onSubopen (X := Spec (CommRingCat.of (A t i))) (affineDifferentialSheaf (A t i)) (withinTimeAffine t i V hV U O hO W hW)
      ((evaluation (normalizedVelocity t i ht)).val.app (op ((thickChart V t hV i) ⁻¹ᵁ U))
        ((toThickTwoForms V t hV i).val.app (op U) x)) := by
  have he := alongSquare_restrict (seedCurveToFirstOrderCurve t) (germToTime t V hV)
    (seedToTime t V hV) (seed_germ_to_time t V hV) (toGerm t V hV) (germEvaluation t ht) U O hO W hW hWU x
  refine (congrArg ((seedFormsMap t i).val.app (op W)) he).trans ?_
  refine (congrArg
    ((seedFormsMap t i).val.app (op W) ∘ onSubopen (curveDifferentials t) hW)
    (germEvaluation_on t ht i O hi
      (onSubopen (germTwoForms t) hO ((toGerm t V hV).val.app (op U) x)))).trans ?_
  exact localEvaluation_coordinates t i V hV U O hO hi W hW (normalizedVelocity t i ht) x

end CycleQ2LiteralAbelJacobiQTimeChart
end

#print axioms CycleQ2LiteralAbelJacobiQTimeChart.timeEvaluation_coordinates
