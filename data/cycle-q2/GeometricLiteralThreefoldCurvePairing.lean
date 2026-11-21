import Proposal.GeometricLiteralThreefoldCurveSignedEdges
import Proposal.GeometricLiteralThreefoldCurveEvaluationRefinement
import Proposal.GeometricLiteralThreefoldCurveVertexCochain
import Proposal.GeometricFiniteCechOneAdditivity
import Proposal.GeometricAffineCechGauge
import Proposal.GeometricLiteralMovingCurveDifferentialNonzero

/-!
# Signed comparison on the central curve from its vertex corrections

The correction at each native vertex uses the genuine normalized
velocity. Checking the curve forms on the ordered weight charts identifies
the two derived classes, including their sign.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldCurvePairing

open CycleQ2GeometricSheafLocalIso CategoryTheory AlgebraicGeometry TopologicalSpace
  CycleQ2InjectiveCech CycleQ2FiniteInjectiveCech CycleQ2FiniteCechDescent CycleQ2FiniteCechHOne
  CycleQ2FiniteCechOneAdditivity CycleQ2LiteralThreefoldCurveEvaluationRefinement
  CycleQ2LiteralThreefoldCurveVertexCochain CycleQ2LiteralThreefoldCurveTestSections
  CycleQ2LiteralThreefoldCurveClassRepresentative CycleQ2LiteralThreefoldSurfaceTestLifts
  CycleQ2LiteralAbelJacobiEvaluationDerived CycleQ2LiteralAbelJacobiQPullbackDerived
  CycleQ2LiteralThreefoldTestClass CycleQ2LiteralMovingResidueCurve CycleQ2LiteralMovingCurveDifferentialNonzero
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceSeedFiberCover
  CycleQ2LiteralMovingResidueAdjunction.AffineFrame CycleQ2LiteralProjectiveIntersections

local instance (Z : Scheme.{0}) : HasExt.{1} (AbSheaf Z) := HasExt.standard _

variable (t : Fin 3 → ℂ) (ht : AlgebraicIndependent ℚ t)
  (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V)

theorem signed_class_of_native_edges
    (h : ∀ u v, chartIndex u ≤ chartIndex v → ∀ (W : (Curve t).Opens) (hu : W ≤ vertexOpen t u)
      (hv : W ≤ vertexOpen t v), IsAffineOpen W →
      edgeValue (curveForms t) (vertexOpen t) (nativeTest t V hV ht) u v W hu hv +
        res (curveForms t) hv (corrections t ht v) =
      res (curveForms t) hu (corrections t ht u) - edgeValue (curveForms t) (vertexOpen t) (beta t) u v W hu hv) :
    timeHodge t ht V hV (qHodge V t ambientTestClass) = -curveClass t := by
  let F := curveForms t
  let U := vertexOpen t
  let b := beta t
  let c := nativeTest t V hV ht
  let hb := beta_closed t
  let hc := nativeTest_closed t V hV ht
  have H (u v : Vertex) (huv : chartIndex u ≤ chartIndex v) :=
    CycleQ2AffineCechGauge.signed_edges_on_affines F U c b (corrections t ht) u v (h u v huv)
  have hz : cechOneClass U (vertexOpen_cover t) (c+b) ((oneCocycles U).add_mem hc hb) = 0 := by
    apply cechOneClass_eq_zero_of_primitive U (vertexOpen_cover t) _ _ (-corrections t ht)
    intro u v W hu hv
    change _ = res F (le_inf hu hv) (c u v + b u v)
    rw [map_add]
    change res F hv (-(corrections t ht v)) - res F hu (-(corrections t ht u)) =
      edgeValue F U c u v W hu hv + edgeValue F U b u v W hu hv
    rw [map_neg, map_neg]
    rcases le_total (chartIndex u) (chartIndex v) with huv | hvu
    · linear_combination (norm := abel) -(H u v huv W hu hv)
    · have h₁ := hc u v u W hu hv hu
      have h₂ := hb u v u W hu hv hu
      rw [oneCocycle_diagonal c hc u W hu] at h₁
      rw [oneCocycle_diagonal b hb u W hu] at h₂
      change 0 = edgeValue F U c u v W hu hv + edgeValue F U c v u W hv hu at h₁
      change 0 = edgeValue F U b u v W hu hv + edgeValue F U b v u W hv hu at h₂
      linear_combination (norm := abel) (H v u hvu W hv hu) + h₁ + h₂
  rw [cechOneClass_add U (vertexOpen_cover t) c b hc hb] at hz
  rw [evaluated_class_native, curveClass_eq_beta]
  exact eq_neg_of_add_eq_zero_left hz

/-- Time evaluation of the pulled-back fixed threefold class is the signed
moving cubic class in ordinary projective curve cohomology. -/
theorem signed_class : timeHodge t ht V hV (qHodge V t ambientTestClass) = -curveClass t :=
  signed_class_of_native_edges t ht V hV (fun u v huv W hu hv _ =>
    CycleQ2LiteralThreefoldCurveSignedEdges.signed_edges t ht V hV u v huv W hu hv)

/-- The comparison gives the actual signed complex trace computed by the
Cartier residue on the central curve. -/
theorem trace_of_signed_class (hreg : ∀ i, CycleQ2SeedSectionAffineInjective.ChartRegular t i)
    (hs : timeHodge t ht V hV (qHodge V t ambientTestClass) = -curveClass t) :
    differentialTrace t hreg (timeHodge t ht V hV (qHodge V t ambientTestClass)) =
      -differentialTrace t hreg (curveClass t) ∧
    differentialTrace t hreg (timeHodge t ht V hV (qHodge V t ambientTestClass)) ≠ 0 := by
  rw [hs, map_neg]
  exact ⟨rfl, neg_ne_zero.mpr (differentialTrace_curveClass_ne_zero t hreg)⟩

end CycleQ2LiteralThreefoldCurvePairing
end

#print axioms CycleQ2LiteralThreefoldCurvePairing.signed_class
