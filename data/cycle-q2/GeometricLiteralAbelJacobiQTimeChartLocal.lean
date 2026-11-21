import Proposal.GeometricLiteralAbelJacobiQEvaluationTransport
import Proposal.GeometricLiteralAbelJacobiEvaluationChart
import Proposal.GeometricLiteralAbelJacobiEvaluationGerm

/-!
# Tangent evaluation on each original first-order curve chart

For an arbitrary two-form of the time family, first restrict to an open
of the projective seed curve under a germ coordinate chart. Its affine
one-form is the evaluation of the directly restricted two-form on the
original affine first-order chart, at the same parameter velocity.

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
  CycleQ2LiteralAbelJacobiQEvaluationTransport
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

abbrev seedFormsMap := schemeDifferentialMap (seedChart t i) (affineCoefficient (A t i))
  (curveCoefficient t) (seedChart_coefficient t i)

theorem local_coordinates (v : Derivation ℂ (B t i) (A t i))
    (O : (firstOrderCurve t).Opens) (hi : O ≤ firstOrderCurveCoordinateOpen t i)
    (x : (germTwoForms t).val.obj (op O)) :
    (seedFormsMap t i).val.app (op ((seedCurveToFirstOrderCurve t) ⁻¹ᵁ O))
      ((evaluationOn t i v).val.app (op (Over.mk (homOfLE hi))) x) =
      (rawEvaluation t i v).val.app (op O) x := by
  have h := evaluationOn_coordinates t i v O hi x
  have e : toSeedCoordinates t i = (Scheme.Modules.pushforward (seedCurveToFirstOrderCurve t)).map (seedFormsMap t i) :=
    toSeedCoordinates_differentialMap t i
  change (toSeedCoordinates t i).val.app (op O) _ = _ at h
  rw [e] at h
  exact h

variable (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V) (U : (family V t).Opens)
  (O : (firstOrderCurve t).Opens) (hO : O ≤ (germToTime t V hV) ⁻¹ᵁ U)
  (hi : O ≤ firstOrderCurveCoordinateOpen t i) (W : (Curve t).Opens)
  (hW : W ≤ (seedCurveToFirstOrderCurve t) ⁻¹ᵁ O) (hWU : W ≤ (seedToTime t V hV) ⁻¹ᵁ U)

abbrev withinAffine : (seedChart t i) ⁻¹ᵁ W ≤ mapToChart t i ⁻¹ᵁ (firstOrderChartToCurve t i) ⁻¹ᵁ O :=
  ((seedChart t i).preimage_mono hW).trans (chart_preimage t i O).le

abbrev withinTimeAffine :
    (seedChart t i) ⁻¹ᵁ W ≤ mapToChart t i ⁻¹ᵁ (thickChart V t hV i) ⁻¹ᵁ U :=
  (withinAffine t i O W hW).trans
    ((mapToChart t i).preimage_mono ((firstOrderChartToCurve t i).preimage_mono hO))

private theorem thick_restrict (v : Derivation ℂ (B t i) (A t i))
    (x : (familyTwoForms V t).val.obj (op U)) :
    onSubopen (X := Spec (CommRingCat.of (A t i))) (affineDifferentialSheaf (A t i)) (withinAffine t i O W hW)
      ((evaluation v).val.app (op ((firstOrderChartToCurve t i) ⁻¹ᵁ O))
        ((germToChart t i).val.app (op O) (onSubopen (germTwoForms t) hO ((toGerm t V hV).val.app (op U) x)))) =
    onSubopen (X := Spec (CommRingCat.of (A t i))) (affineDifferentialSheaf (A t i)) (withinTimeAffine t i V hV U O hO W hW)
      ((evaluation v).val.app (op ((thickChart V t hV i) ⁻¹ᵁ U)) ((toThickTwoForms V t hV i).val.app (op U) x)) := by
  let z := (toGerm t V hV).val.app (op U) x
  let p : (Spec (CommRingCat.of (A t i))).Modules := affineDifferentialSheaf (A t i)
  let b : (Spec (CommRingCat.of (B t i))).Modules := thickTwoForms t i
  let hB := (firstOrderChartToCurve t i).preimage_mono hO
  let ω := (toThickTwoForms V t hV i).val.app (op U) x
  have hc := PresheafOfModules.naturality_apply (germToChart t i).val (homOfLE hO).op z
  have hω := hc.trans (congrArg (onSubopen b hB) (toChart_apply t V hV i U x).symm)
  have hv := congrArg ((evaluation v).val.app (op ((firstOrderChartToCurve t i) ⁻¹ᵁ O))) hω
  have he := hv.trans (evaluation_restrict v (homOfLE hB) ω)
  refine (congrArg (onSubopen p (withinAffine t i O W hW)) he).trans ?_
  exact onSubopen_trans p (withinAffine t i O W hW) ((mapToChart t i).preimage_mono hB) _

/-- Evaluate in the original weight-one chart and further restrict on the central curve. -/
theorem localEvaluation_coordinates (v : Derivation ℂ (B t i) (A t i))
    (x : (familyTwoForms V t).val.obj (op U)) :
    (seedFormsMap t i).val.app (op W)
      (onSubopen (curveDifferentials t) hW
        ((evaluationOn t i v).val.app (op (Over.mk (homOfLE hi)))
          (onSubopen (germTwoForms t) hO ((toGerm t V hV).val.app (op U) x)))) =
    onSubopen (X := Spec (CommRingCat.of (A t i))) (affineDifferentialSheaf (A t i)) (withinTimeAffine t i V hV U O hO W hW)
      ((evaluation v).val.app (op ((thickChart V t hV i) ⁻¹ᵁ U))
        ((toThickTwoForms V t hV i).val.app (op U) x)) := by
  let z := (toGerm t V hV).val.app (op U) x
  let y := onSubopen (germTwoForms t) hO z
  let p : (Spec (CommRingCat.of (A t i))).Modules := affineDifferentialSheaf (A t i)
  let hA := (seedChart t i).preimage_mono hW
  calc
    _ = onSubopen p hA ((seedFormsMap t i).val.app _
        ((evaluationOn t i v).val.app (op (Over.mk (homOfLE hi))) y)) :=
      PresheafOfModules.naturality_apply (seedFormsMap t i).val (homOfLE hW).op _
    _ = onSubopen p hA ((rawEvaluation t i v).val.app (op O) y) :=
      congrArg (onSubopen p hA) (local_coordinates t i v O hi y)
    _ = onSubopen p (withinAffine t i O W hW)
        ((evaluation v).val.app (op ((firstOrderChartToCurve t i) ⁻¹ᵁ O))
          ((germToChart t i).val.app (op O) y)) := by
      rw [rawEvaluation_apply]
      exact onSubopen_congr (seedChart_to_germ t i).symm p O _ _ hA _
    _ = _ := thick_restrict t i V hV U O hO W hW v x

end CycleQ2LiteralAbelJacobiQTimeChart
end

#print axioms CycleQ2LiteralAbelJacobiQTimeChart.localEvaluation_coordinates
