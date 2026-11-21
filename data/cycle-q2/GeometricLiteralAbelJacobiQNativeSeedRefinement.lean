import Proposal.GeometricLiteralAbelJacobiQNativeSeedEvaluation
import Proposal.GeometricLiteralAbelJacobiQPairSurface
import Proposal.GeometricLiteralThreefoldCurveEvaluationRefinement
import Proposal.GeometricLiteralThreefoldVertexPointBinding

/-!
# The evaluated class on the twelve original surface opens

Each increasing fixed-chart edge on a native surface intersection is the
regular one-form obtained from the original parameter velocity on that open
of the projective curve. The surface coordinates give its scalar action.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralAbelJacobiQNativeSeedRefinement

open CategoryTheory AlgebraicGeometry CycleQ2LiteralAbelJacobiQNativeSeedEvaluation
  CycleQ2LiteralAbelJacobiQPairSurface CycleQ2LiteralAbelJacobiQPairSeed
  CycleQ2LiteralAbelJacobiQEvaluatedCocycle CycleQ2LiteralThreefoldCurveEvaluationRefinement
  CycleQ2LiteralThreefoldVertexPointBinding CycleQ2LiteralThreefoldVertexMotion
  CycleQ2LiteralThreefoldCurveTestBinding CycleQ2LiteralThreefoldCurveTestSections
  CycleQ2LiteralThreefoldSurfaceTestLifts CycleQ2LiteralThreefoldHodgeCech CycleQ2LiteralAmbientCharts
  CycleQ2LiteralThreefoldResidueCoordinates CycleQ2LiteralThreefoldTestEdges
  CycleQ2LiteralAbelJacobiEvaluationFiber CycleQ2LiteralAbelJacobiEvaluationDerived
  CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralAbelJacobiContraction
  CycleQ2LiteralMovingResidueAdjunction.AffineFrame CycleQ2LiteralMovingResidueCurve
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionComplex
  CycleQ2LiteralCylinderEvaluation CycleQ2LiteralThreefoldPairMotion
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceSeedFiberCover CycleQ2SeedSectionSheafCurveBinding
  CycleQ2GeometricSectionDifferentials CycleQ2GeometricDifferentialSheaf CycleQ2FiniteCechDescent
  CycleQ2FiniteInjectiveCech

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra curveComplexOn closedComplexAlgebra
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

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ) (hV : seedBasePoint ∈ V)
  (s : Finset Vertex) (hs : s.Nonempty) (v w : Vertex) (hv : v ∈ s) (hw : w ∈ s)
  (hvw : chartIndex v < chartIndex w) (W : (Curve t).Opens) (hW : W ≤ (curveToSurface t) ⁻¹ᵁ closedOpen s)

private abbrev U := fixedOpen (chartIndex v) ⊓ fixedOpen (chartIndex w)

include hs hv hw hW in
private theorem within : W ≤ seedProjection V t hV ⁻¹ᵁ U v w := by
  change W ≤ (seedProjection V t hV) ⁻¹ᵁ (fixedOpen (chartIndex v) ⊓ fixedOpen (chartIndex w))
  rw [Scheme.Hom.preimage_inf]
  exact le_inf (native_within V t hV s hs v hv W hW) (native_within V t hV s hs w hw W hW)

include hv hW in
private theorem onChart : W ≤ (seedChart t (chartIndex v)).opensRange :=
  (withinVertex t s v hv W hW).trans ((vertexWithin t v).trans (seedChart_opensRange t (chartIndex v)).ge)

abbrev onPair : W ≤ (pairToSeed t (chartIndex v) (slot (chartIndex v) (chartIndex w) hvw)).opensRange :=
  withinNativePair t (chartIndex v) V hV (chartIndex w) hvw (U v w) inf_le_right W
    (within V t hV s hs v w hv hw W hW) (onChart t s v hv W hW)

/-- The normalized pair velocity acts at the actual native surface point. -/
theorem scalarPoint :
    let k := slot (chartIndex v) (chartIndex w) hvw
    overlapPointOnSeed t (chartIndex v) k W (onPair V t hV s hs v w hv hw hvw W hW) =
      (nativeToCurve t s hs W hW).comp (fixedOverlapPoint s v w hv hw k (succAbove_slot _ _ _)) := by
  apply AlgHom.ext
  intro x
  exact (surface_seed_coordinate V t hV s hs v w hv hw _ (succAbove_slot _ _ _) (U v w)
    (by simpa only [CycleQ2LiteralAbelJacobiQPairCharts.pairOpen, succAbove_slot] using (le_rfl : U v w ≤ U v w)) W hW
    (within V t hV s hs v w hv hw W hW) (onPair V t hV s hs v w hv hw hvw W hW) x).symm

/-- On the original twelve-open refinement, the evaluated edge is the ordinary
pair differential transported to the given projective curve open. -/
theorem nativeTest_seedOne (ht : AlgebraicIndependent ℚ t) :
    let i := chartIndex v
    let k := slot i (chartIndex w) hvw
    let hpair := onPair V t hV s hs v w hv hw hvw W hW
    edgeValue (curveForms t) (vertexOpen t) (nativeTest t V hV ht) v w W
        (withinVertex t s v hv W hW) (withinVertex t s w hw W hW) =
      CycleQ2LiteralAbelJacobiQPairSeedSections.seedOne t i k W hpair
        (contractRestrict ((pairVelocity t ht i k).compAlgebraMap (FixedOverlap i k)) (nativeEdge i k)) := by
  refine (nativeTest_edge t V hV ht v w W (withinVertex t s v hv W hW) (withinVertex t s w hw W hW)).trans ?_
  exact evaluatedTest_native t ht (chartIndex v) V hV (chartIndex w) hvw (U v w)
    inf_le_left inf_le_right W (within V t hV s hs v w hv hw W hW) (onChart t s v hv W hW)

theorem nativeTest_contract (ht : AlgebraicIndependent ℚ t) :
    let i := chartIndex v
    let k := slot i (chartIndex w) hvw
    let hpair := onPair V t hV s hs v w hv hw hvw W hW
    letI := (overlapPointOnSeed t i k W hpair).toRingHom.toAlgebra
    letI : IsScalarTower ℂ (FixedOverlap i k) (CurveRingOn t W) := IsScalarTower.of_algHom (overlapPointOnSeed t i k W hpair)
    edgeValue (curveForms t) (vertexOpen t) (nativeTest t V hV ht) v w W
        (withinVertex t s v hv W hW) (withinVertex t s w hw W hW) =
      toSheaf (Curve t).sheaf (curveCoefficient t) W
        (contractRestrict (overlapVelocityOnSeed t ht i k W hpair) (nativeEdge i k)) := by
  refine (nativeTest_edge t V hV ht v w W (withinVertex t s v hv W hW) (withinVertex t s w hw W hW)).trans ?_
  exact evaluatedTest_contract t ht (chartIndex v) V hV (chartIndex w) hvw (U v w)
    inf_le_left inf_le_right W (within V t hV s hs v w hv hw W hW) (onChart t s v hv W hW)

end CycleQ2LiteralAbelJacobiQNativeSeedRefinement
end

#print axioms CycleQ2LiteralAbelJacobiQNativeSeedRefinement.scalarPoint
#print axioms CycleQ2LiteralAbelJacobiQNativeSeedRefinement.nativeTest_seedOne
#print axioms CycleQ2LiteralAbelJacobiQNativeSeedRefinement.nativeTest_contract
