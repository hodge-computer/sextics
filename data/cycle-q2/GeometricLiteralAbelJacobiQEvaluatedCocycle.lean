import Proposal.GeometricLiteralAbelJacobiQTimeChart
import Proposal.GeometricLiteralAbelJacobiQPairForms
import Proposal.GeometricLiteralAbelJacobiEvaluationDerived

/-!
# The actual evaluated test cocycle on a central affine chart

On every common subopen of an increasing edge of the native cover the
evaluated test class restricts to the normalized parameter contraction
of the original time-family section on the affine curve chart.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralAbelJacobiQEvaluatedCocycle

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
  CycleQ2LiteralAbelJacobiQTimeChart CycleQ2LiteralAbelJacobiQPairForms CycleQ2LiteralAbelJacobiQEvaluationTransport
  CycleQ2LiteralAbelJacobiEvaluationGlobal CycleQ2LiteralAbelJacobiEvaluationDerived
  CycleQ2LiteralAbelJacobiEvaluationFiber CycleQ2LiteralAbelJacobiEvaluationGerm
  CycleQ2LiteralAbelJacobiEvaluationAffine CycleQ2LiteralAbelJacobiEvaluationChart
  CycleQ2LiteralAbelJacobiEvaluationRestriction CycleQ2LiteralAbelJacobiTimeCharts CycleQ2LiteralAbelJacobiTimeFamily
  CycleQ2LiteralAbelJacobiQPullback CycleQ2LiteralAbelJacobiQTest
  CycleQ2LiteralThreefoldHodgeCech CycleQ2LiteralAmbientCharts
  CycleQ2FiniteCechOrbitPullback CycleQ2FiniteInjectiveCech
  CycleQ2GeometricAffineDifferentialSheaf CycleQ2LiteralAbelJacobiMovingNormal
  CycleQ2LiteralCylinderEvaluation CycleQ2FirstOrderCurve CycleQ2FirstOrderCurveCharts CycleQ2FirstOrderCurveSeedFiber
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceSeedFiberCover
  CycleQ2LiteralMovingResidueAdjunction.AffineFrame CycleQ2LiteralMovingResidueCurve

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  familyRing closedRing CycleQ2CurveParameterTangent.chartComplexAlgebra
  familyComplexSMul familyComplexModule reductionAlgebra familyReductionTower

variable (t : Fin 3 → ℂ) (ht : AlgebraicIndependent ℚ t)
  (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V)
  (i j : Fin 4) (U : Threefold.Opens) (hi : U ≤ fixedOpen i) (hj : U ≤ fixedOpen j)
  (W : (Curve t).Opens) (hWU : W ≤ (seedToTime t V hV ≫ toThreefold V t) ⁻¹ᵁ U)

abbrev localValue :=
  edgeValue (curveForms t) (testCover t V hV) (evaluatedTest t ht V hV) i j W
    (fun _ hx => hi (hWU hx)) (fun _ hx => hj (hWU hx))

theorem localValue_eq :
    localValue t ht V hV i j U hi hj W hWU =
      onSubopen (curveDifferentials t) hWU
        ((timeEvaluation t ht V hV).val.app (op ((toThreefold V t) ⁻¹ᵁ U)) (testEdgeValue V t i j U hi hj)) :=
  edgeValue_pullOne (seedToTime t V hV).base (evaluationAdd t ht V hV)
    (cover (toThreefold V t).base fixedOpen) (testCocycle V t) i j hWU
    ((toThreefold V t).preimage_mono hi) ((toThreefold V t).preimage_mono hj)

abbrev commonGerm :=
  (germToTime t V hV) ⁻¹ᵁ (toThreefold V t) ⁻¹ᵁ U ⊓ firstOrderCurveCoordinateOpen t i

variable (hchart : W ≤ (seedChart t i).opensRange)

include hWU hchart in
theorem withinGerm : W ≤ (seedCurveToFirstOrderCurve t) ⁻¹ᵁ commonGerm t V hV i U := by
  change W ≤ (seedCurveToFirstOrderCurve t) ⁻¹ᵁ
    ((germToTime t V hV) ⁻¹ᵁ (toThreefold V t) ⁻¹ᵁ U ⊓ firstOrderCurveCoordinateOpen t i)
  rw [Scheme.Hom.preimage_inf, germ_preimage_coordinate t i, ← seedChart_opensRange t i]
  refine le_inf ?_ hchart
  exact hWU.trans (congrArg (fun q => q ⁻¹ᵁ ((toThreefold V t) ⁻¹ᵁ U)) (seed_germ_to_time t V hV)).ge

abbrev chartDomain := withinTimeAffine t i V hV ((toThreefold V t) ⁻¹ᵁ U) (commonGerm t V hV i U)
  inf_le_left W (withinGerm t V hV i U W hWU hchart)

theorem evaluatedTest_coordinates :
    (seedFormsMap t i).val.app (op W) (localValue t ht V hV i j U hi hj W hWU) =
      onSubopen (X := Spec (CommRingCat.of (A t i))) (affineDifferentialSheaf (A t i)) (chartDomain t V hV i U W hWU hchart)
        ((evaluation (normalizedVelocity t i ht)).val.app
          (op ((thickChart V t hV i) ⁻¹ᵁ (toThreefold V t) ⁻¹ᵁ U))
          ((toThickTwoForms V t hV i).val.app (op ((toThreefold V t) ⁻¹ᵁ U)) (testEdgeValue V t i j U hi hj))) := by
  refine (congrArg ((seedFormsMap t i).val.app (op W)) (localValue_eq t ht V hV i j U hi hj W hWU)).trans ?_
  exact timeEvaluation_coordinates t ht i V hV ((toThreefold V t) ⁻¹ᵁ U) (commonGerm t V hV i U)
    inf_le_left inf_le_right W (withinGerm t V hV i U W hWU hchart) hWU _

end CycleQ2LiteralAbelJacobiQEvaluatedCocycle
end

#print axioms CycleQ2LiteralAbelJacobiQEvaluatedCocycle.evaluatedTest_coordinates
