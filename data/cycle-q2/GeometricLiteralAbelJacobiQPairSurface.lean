import Proposal.GeometricLiteralAbelJacobiQPairSeed
import Proposal.GeometricLiteralAbelJacobiQPairSeedSections
import Proposal.GeometricLiteralAbelJacobiQAffineForms
import Proposal.GeometricLiteralThreefoldCurveTestBinding
import Proposal.GeometricLiteralThreefoldTestEdges

/-!
# The same overlap point on the surface and on the moving pair

On a common open of the original seed curve, pull the normalized surface
coordinates back to its literal affine pair. Every coordinate, including
the inverse weight-one ratio, then agrees with the reduction of the
moving cylinder point.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralAbelJacobiQPairSurface

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
  CycleQ2LiteralAbelJacobiQPairCharts CycleQ2LiteralAbelJacobiQPairSeed CycleQ2LiteralAbelJacobiQAffineForms
  CycleQ2LiteralAbelJacobiQPairSeedSections
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralCylinderEvaluation
  CycleQ2LiteralAbelJacobiEvaluationFiber CycleQ2LiteralAbelJacobiTimeCharts
  CycleQ2LiteralAbelJacobiQPullback CycleQ2LiteralThreefoldHodgeCech
  CycleQ2LiteralThreefoldOverlapAtlas CycleQ2LiteralThreefoldResidueCoordinates
  CycleQ2LiteralThreefoldResidueChartMaps CycleQ2LiteralThreefoldCurveTestBinding
  CycleQ2LiteralThreefoldCurveTestSections CycleQ2LiteralThreefoldSurfaceChartMap
  CycleQ2LiteralThreefoldSurfaceTestLifts CycleQ2LiteralMovingResidueAdjunction.AffineFrame
  CycleQ2SeedSectionSheafCurveBinding CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveIntersectionComplex CycleQ2IncidenceEtaleParameter
  CycleQ2IncidenceSeedFiberCover CycleQ2GeometricAffineDifferentialSheaf
  CycleQ2LiteralThreefoldTestEdges CycleQ2ExteriorSectionNaturality

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  familyRing closedRing threefoldRing CycleQ2CurveParameterTangent.chartComplexAlgebra
  familyAlgebra familyComplexTower fixedAlgebra fixedTower reductionAlgebra fixedCurveTower
  sourceFixedAlgebra sourceFixedTower closedComplexAlgebra curveComplexOn complexOn

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ) (hV : seedBasePoint ∈ V)

/-- On the same refined seed open the surface point and the literal cylinder
point determine exactly the same homomorphism on the full fixed overlap. -/
theorem surface_pair_coordinate (s : Finset Vertex) (hs : s.Nonempty) (v w : Vertex)
    (hv : v ∈ s) (hw : w ∈ s) (k : Fin 3) (h : (chartIndex v).succAbove k = chartIndex w)
    (U : Threefold.Opens) (hU : U ≤ pairOpen (chartIndex v) k)
    (W : (Curve t).Opens) (hW : W ≤ (curveToSurface t) ⁻¹ᵁ closedOpen s)
    (hWU : W ≤ seedProjection V t hV ⁻¹ᵁ U) (x : FixedOverlap (chartIndex v) k) :
    (pairToSeed t (chartIndex v) k).app W
        (nativeToCurve t s hs W hW (fixedOverlapPoint s v w hv hw k h x)) =
      algebraMap (APair t (chartIndex v) k)
        (AffineSections (APair t (chartIndex v) k) ((pairToSeed t (chartIndex v) k) ⁻¹ᵁ W))
        (pairMap (chartIndex v) k (toCurve t (chartIndex v)) x) := by
  let i := chartIndex v
  let j := pairToSeed t i k
  let g := seedProjection V t hV
  let y := overlapAlgebraMap i k U hU x
  rw [overlapPoint_curve V t hV s hs v w hv hw k h U hU W hW hWU]
  change j.app W (g.appLE U W hWU y) = _
  rw [j.app_eq_appLE]
  refine (ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE j g U W (j ⁻¹ᵁ W) hWU le_rfl) y).trans ?_
  exact chart_appLE (overlapIso i k).symm (pairMap i k (toCurve t i)).toRingHom (j ≫ g)
    (pairToSeed_over V t hV i k) U hU (j ⁻¹ᵁ W) _ x

variable (s : Finset Vertex) (hs : s.Nonempty) (v w : Vertex) (hv : v ∈ s) (hw : w ∈ s)
  (k : Fin 3) (h : (chartIndex v).succAbove k = chartIndex w) (U : Threefold.Opens)
  (hU : U ≤ pairOpen (chartIndex v) k) (W : (Curve t).Opens)
  (hW : W ≤ (curveToSurface t) ⁻¹ᵁ closedOpen s) (hWU : W ≤ seedProjection V t hV ⁻¹ᵁ U)

include hWU hU in
/-- Equality in the ring of regular functions of the projective seed open itself. -/
theorem surface_seed_coordinate (hpair : W ≤ (pairToSeed t (chartIndex v) k).opensRange)
    (x : FixedOverlap (chartIndex v) k) :
    nativeToCurve t s hs W hW (fixedOverlapPoint s v w hv hw k h x) =
      seedRingMap t (chartIndex v) k W hpair (pairMap (chartIndex v) k (toCurve t (chartIndex v)) x) := by
  let j := pairToSeed t (chartIndex v) k
  let : IsIso (j.app W) := Scheme.Hom.isIso_app j W hpair
  apply (asIso (j.app W)).commRingCatIsoToRingEquiv.injective
  exact (surface_pair_coordinate V t hV s hs v w hv hw k h U hU W hW hWU x).trans
    (seedRingMap_self t (chartIndex v) k W hpair _).symm

include hWU hU in
/-- Both ordinary fixed-overlap forms have the same pullback to the actual projective seed open. -/
theorem surface_seed_testEdge (hpair : W ≤ (pairToSeed t (chartIndex v) k).opensRange) :
    exteriorDifferentialMap (nativeToCurve t s hs W hW) 2
      (edgeAt (chartIndex v) k (fixedOverlapPoint s v w hv hw k h)) =
    exteriorDifferentialMap (seedPointAlg t (chartIndex v) k W hpair) 2
      (edgeAt (chartIndex v) k (pairMap (chartIndex v) k (toCurve t (chartIndex v)))) := by
  rw [edgeAt_map, edgeAt_map]
  apply congrArg (edgeAt (chartIndex v) k)
  exact AlgHom.ext (surface_seed_coordinate V t hV s hs v w hv hw k h U hU W hW hWU hpair)

end CycleQ2LiteralAbelJacobiQPairSurface
end

#print axioms CycleQ2LiteralAbelJacobiQPairSurface.surface_pair_coordinate
#print axioms CycleQ2LiteralAbelJacobiQPairSurface.surface_seed_coordinate
#print axioms CycleQ2LiteralAbelJacobiQPairSurface.surface_seed_testEdge
