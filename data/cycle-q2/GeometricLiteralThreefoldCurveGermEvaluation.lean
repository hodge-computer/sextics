import Proposal.GeometricLiteralThreefoldCurveGermEdge
import Proposal.GeometricLiteralThreefoldCurveEvaluationRefinement
import Proposal.GeometricLiteralThreefoldPairOne
import Proposal.GeometricLiteralAbelJacobiQNativeSeedRefinement

/-!
# Evaluation of the actual pulled-back Hodge edge on a common germ open

The derived time evaluation on the original curve cover is the sheaf image
of the ordinary contraction on the common first-order section ring.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace CycleQ2LiteralThreefoldCurveGermEvaluation

open CategoryTheory AlgebraicGeometry TopologicalSpace
  CycleQ2LiteralThreefoldCurveGermEdge CycleQ2LiteralThreefoldGermCoordinates
  CycleQ2LiteralThreefoldCurveEvaluationRefinement CycleQ2LiteralThreefoldCurveTestSections
  CycleQ2LiteralThreefoldVertexMotion CycleQ2LiteralThreefoldVertexPointBinding
  CycleQ2LiteralThreefoldSurfaceTestLifts CycleQ2LiteralThreefoldResidueCoordinates CycleQ2LiteralThreefoldTestEdges
  CycleQ2LiteralThreefoldHodgeCech CycleQ2LiteralAmbientCharts CycleQ2LiteralThreefoldLiftTransition
  CycleQ2LiteralThreefoldPairOne CycleQ2LiteralAbelJacobiQNativeSeedEvaluation
  CycleQ2LiteralAbelJacobiQEvaluatedCocycle CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAbelJacobiMovingNormal
  CycleQ2LiteralCylinderEvaluation CycleQ2LiteralAbelJacobiEvaluationFiber CycleQ2LiteralAbelJacobiQPullback
  CycleQ2LiteralAbelJacobiEvaluationVelocity CycleQ2LiteralAbelJacobiEvaluationChart CycleQ2LiteralAbelJacobiEvaluationDerived
  CycleQ2LiteralAbelJacobiQPairCharts CycleQ2FirstOrderCurve CycleQ2FirstOrderCurveSeedFiber CycleQ2FirstOrderCurveCharts
  CycleQ2LiteralMovingResidueAdjunction.AffineFrame CycleQ2LiteralNativeGaugeSections CycleQ2LiteralProjectiveIntersections
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceSeedFiberCover CycleQ2SeedSectionSheafCurveBinding
  CycleQ2LiteralProjectiveIntersectionComplex CycleQ2LiteralMovingResidueCurve CycleQ2GeometricSectionDifferentials
  CycleQ2FiniteInjectiveCech CycleQ2FiniteCechDescent

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  familyRing closedRing threefoldRing CycleQ2CurveParameterTangent.chartComplexAlgebra
  familyAlgebra familyComplexTower fixedAlgebra fixedTower reductionAlgebra fixedCurveTower familyReductionTower
  curveComplexOn germAlgebra seedSectionAlgebra reductionOn
  CycleQ2LiteralAbelJacobiEvaluationFiberVelocity.sectionTower

variable (t : Fin 3 → ℂ) (ht : AlgebraicIndependent ℚ t) (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V)
  (s : Finset Vertex) (u v : Vertex) (hu : u ∈ s) (hv : v ∈ s) (huv : chartIndex u < chartIndex v)
  (G : (firstOrderCurve t).Opens) (huG : G ≤ firstOrderCurveCoordinateOpen t (chartIndex u))
  (hvG : G ≤ firstOrderCurveCoordinateOpen t (chartIndex v))
  (hW : seedOpen t G ≤ (curveToSurface t) ⁻¹ᵁ closedOpen s)

theorem evaluated_edge :
    edgeValue (curveForms t) (vertexOpen t) (nativeTest t V hV ht) u v (seedOpen t G)
      (withinVertex t s u hu (seedOpen t G) hW) (withinVertex t s v hv (seedOpen t G) hW) =
    (toSheaf (Curve t).sheaf (curveCoefficient t) (seedOpen t G)).toFun
      (testContraction t ht V hV u v G huG hvG (slot _ _ huv) (succAbove_slot _ _ huv)) := by
  let i := chartIndex u
  let j := chartIndex v
  let k := slot i j huv
  let h : i.succAbove k = j := succAbove_slot i j huv
  let d := overlapHom t V hV i k G huG (h.symm ▸ hvG)
  let f := (IsScalarTower.toAlgHom ℂ (GermRing t G) (SeedRing t G)).comp d
  letI := d.toRingHom.toAlgebra
  letI := IsScalarTower.of_algHom d
  letI := f.toRingHom.toAlgebra
  letI := IsScalarTower.of_algHom f
  letI : IsScalarTower (FixedOverlap i k) (GermRing t G) (SeedRing t G) := IsScalarTower.of_algebraMap_eq' rfl
  let v₀ := normalizedVelocity t i ht
  let ν := (onOpen t i v₀ G huG).compAlgebraMap (FixedOverlap i k)
  let W := seedOpen t G
  let huW := withinVertex t s u hu W hW
  let hp := CycleQ2LiteralAbelJacobiQNativeSeedRefinement.onPair V t hV s ⟨u,hu⟩ u v hu hv huv W hW
  refine (CycleQ2LiteralAbelJacobiQNativeSeedRefinement.nativeTest_seedOne V t hV s ⟨u,hu⟩ u v hu hv huv W hW ht).trans ?_
  exact pairOne_of_source t u k W huW hp
    (source_position t V hV s u v hu G huG hvG k h hW) v₀ (pairVelocity t ht i k)
    (pairVelocity_original t ht i k) ν (source_speed t ht V hV s u v hu G huG hvG k h hW) (nativeEdge i k)

end CycleQ2LiteralThreefoldCurveGermEvaluation
end

#print axioms CycleQ2LiteralThreefoldCurveGermEvaluation.evaluated_edge
