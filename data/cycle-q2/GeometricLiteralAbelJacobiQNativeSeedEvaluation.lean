import Proposal.GeometricLiteralAbelJacobiQOriginalEvaluation
import Proposal.GeometricLiteralAbelJacobiQEvaluatedCocycle
import Proposal.GeometricOpenDifferentialSections
import Proposal.GeometricCurveContractionRestriction

/-!
# The evaluated test edge is the native mixed differential on the projective seed

On each common seed open in its original affine chart, the genuine
one-cocycle representing tangent evaluation of the ambient test class
is obtained by contracting the native overlap two-form with the
normalized curve motion. The resulting one-form is realized on that
open of the projective curve.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralAbelJacobiQNativeSeedEvaluation

open CategoryTheory Opposite AlgebraicGeometry CycleQ2LiteralAbelJacobiQTimeChart
  CycleQ2LiteralAbelJacobiQPairSeed CycleQ2LiteralAbelJacobiQPairSeedSections
  CycleQ2LiteralAbelJacobiQThickSection CycleQ2LiteralAbelJacobiQEvaluatedCocycle
  CycleQ2LiteralAbelJacobiQEvaluationTransport CycleQ2LiteralAbelJacobiQPairCharts
  CycleQ2LiteralAbelJacobiEvaluationFiber CycleQ2LiteralAbelJacobiEvaluationChart
  CycleQ2LiteralAbelJacobiEvaluationSeedForms CycleQ2LiteralAbelJacobiEvaluationAffine
  CycleQ2LiteralAbelJacobiQPullback CycleQ2LiteralThreefoldHodgeCech CycleQ2LiteralAmbientCharts
  CycleQ2LiteralThreefoldTestEdges CycleQ2LiteralThreefoldResidueCoordinates
  CycleQ2LiteralThreefoldPairMotion CycleQ2CurvePairEvaluationLocalization CycleQ2CurvePairEvaluationSections
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralCylinderEvaluation CycleQ2LiteralAbelJacobiMovingNormal
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricAffineDifferentialSheaf CycleQ2GeometricSheafKaehlerMap
  CycleQ2LiteralMovingResidueAdjunction.AffineFrame CycleQ2LiteralMovingResidueCurve
  CycleQ2GeometricSectionDifferentials CycleQ2GeometricAffineOverlap
  CycleQ2LiteralThreefoldCurveTestSections
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceSeedFiberCover

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  familyRing closedRing threefoldRing CycleQ2CurveParameterTangent.chartComplexAlgebra
  familyComplexSMul familyComplexModule familyAlgebra familyComplexTower fixedAlgebra fixedTower
  reductionAlgebra fixedCurveTower familyReductionTower
  reductionPairAlgebra reductionPairTower baseAlgebra baseTower baseATower baseBTower
  ambientThickAlgebra ambientThickTower ambientClosedAlgebra ambientClosedTower ambientPairTower
attribute [local instance 2000] Algebra.toSMul Algebra.toModule
attribute [local instance] curveComplexOn

variable (t : Fin 3 → ℂ) (ht : AlgebraicIndependent ℚ t) (i : Fin 4) (k : Fin 3)

variable (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V)
  (j : Fin 4) (hij : i < j) (U : Threefold.Opens) (hi : U ≤ fixedOpen i) (hj : U ≤ fixedOpen j)
  (W : (Curve t).Opens) (hWU : W ≤ (seedToTime t V hV ≫ toThreefold V t) ⁻¹ᵁ U)
  (hchart : W ≤ (seedChart t i).opensRange)

include hWU hchart hj in
theorem withinNativePair : W ≤ (pairToSeed t i (slot i j hij)).opensRange := by
  rw [pairToSeed_range V t hV i (slot i j hij), succAbove_slot i j hij]
  exact le_inf hchart (hWU.trans ((seedToTime t V hV ≫ toThreefold V t).preimage_mono hj))

theorem evaluatedTest_native :
    localValue t ht V hV i j U hi hj W hWU =
      seedOne t i (slot i j hij) W (withinNativePair t i V hV j hij U hj W hWU hchart)
        (contractRestrict ((pairVelocity t ht i (slot i j hij)).compAlgebraMap (FixedOverlap i (slot i j hij)))
          (nativeEdge i (slot i j hij))) := by
  apply (CycleQ2OpenDifferentialSections.pull_bijective (seedChart t i) _ _ (seedChart_coefficient t i) W hchart).1
  refine (evaluatedTest_coordinates t ht V hV i j U hi hj W hWU hchart).trans ?_
  exact affine_native t ht i V hV j hij U hi hj W (withinNativePair t i V hV j hij U hj W hWU hchart)
    (chartDomain t V hV i U W hWU hchart)

/-- The same result in the project's ordinary-section-ring to sheaf notation. -/
theorem evaluatedTest_toSheaf :
    letI := sectionAlgebra (Curve t).sheaf (curveCoefficient t) W
    let k := slot i j hij
    let hpair := withinNativePair t i V hV j hij U hj W hWU hchart
    localValue t ht V hV i j U hi hj W hWU =
      toSheaf (Curve t).sheaf (curveCoefficient t) W
        (differentialMap (seedPointAlg t i k W hpair)
          (contractRestrict ((pairVelocity t ht i k).compAlgebraMap (FixedOverlap i k)) (nativeEdge i k))) :=
  (evaluatedTest_native t ht i V hV j hij U hi hj W hWU hchart).trans (seedOne_toSheaf t i _ W _ _)

theorem evaluatedTest_contract :
    let k := slot i j hij
    let hpair := withinNativePair t i V hV j hij U hj W hWU hchart
    letI := (overlapPointOnSeed t i k W hpair).toRingHom.toAlgebra
    letI : IsScalarTower ℂ (FixedOverlap i k) (CurveRingOn t W) := IsScalarTower.of_algHom (overlapPointOnSeed t i k W hpair)
    localValue t ht V hV i j U hi hj W hWU =
      toSheaf (Curve t).sheaf (curveCoefficient t) W
        (contractRestrict (overlapVelocityOnSeed t ht i k W hpair) (nativeEdge i k)) := by
  dsimp only
  let k := slot i j hij
  let hpair := withinNativePair t i V hV j hij U hj W hWU hchart
  letI := (overlapPointOnSeed t i k W hpair).toRingHom.toAlgebra
  letI : IsScalarTower ℂ (FixedOverlap i k) (CurveRingOn t W) := IsScalarTower.of_algHom (overlapPointOnSeed t i k W hpair)
  refine (evaluatedTest_toSheaf t ht i V hV j hij U hi hj W hWU hchart).trans ?_
  apply congrArg (toSheaf (Curve t).sheaf (curveCoefficient t) W)
  exact CycleQ2CurveContractionRestriction.contract_natural (seedPointAlg t i k W hpair) (fun _ => rfl)
    ((pairVelocity t ht i k).compAlgebraMap (FixedOverlap i k)) (overlapVelocityOnSeed t ht i k W hpair)
    (fun _ => rfl) (nativeEdge i k)

end CycleQ2LiteralAbelJacobiQNativeSeedEvaluation
end

#print axioms CycleQ2LiteralAbelJacobiQNativeSeedEvaluation.evaluatedTest_native
#print axioms CycleQ2LiteralAbelJacobiQNativeSeedEvaluation.evaluatedTest_toSheaf
#print axioms CycleQ2LiteralAbelJacobiQNativeSeedEvaluation.evaluatedTest_contract
