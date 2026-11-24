import Proposal.GeometricLiteralThreefoldVertexPoint
import Proposal.GeometricLiteralThreefoldSurfaceTestLifts
import Proposal.GeometricLiteralThreefoldCurveClassRepresentative
import Proposal.GeometricLiteralAbelJacobiEvaluationDerived
import Proposal.GeometricFiniteCechHOneRefinement

/-!
# The time-tested ambient class on the original twelve curve opens

Both derived classes are represented on exactly the twelve opens cut
out by the homogeneous surface cover on the original central curve.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldCurveEvaluationRefinement

open CategoryTheory AlgebraicGeometry TopologicalSpace
  CycleQ2LiteralThreefoldCurveTestSections CycleQ2LiteralThreefoldVertexMotion CycleQ2LiteralThreefoldVertexPoint
  CycleQ2LiteralThreefoldSurfaceTestLifts CycleQ2LiteralAbelJacobiEvaluationDerived
  CycleQ2LiteralAbelJacobiQPullbackDerived CycleQ2LiteralThreefoldTestClass
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceSeedFiberCover
  CycleQ2LiteralMovingResidueCurve CycleQ2LiteralNativeGaugeSections
  CycleQ2LiteralProjectiveIntersections CycleQ2SeedSectionSheafCurveBinding
  CycleQ2LiteralMovingResidueAdjunction.AffineFrame
  CycleQ2FiniteInjectiveCech CycleQ2FiniteCechDescent CycleQ2FiniteCechRefinement CycleQ2FiniteCechHOne
  CycleQ2InjectiveCech

local instance (Z : Scheme.{0}) : HasExt.{1} (AbSheaf Z) := HasExt.standard _

variable (t : Fin 3 → ℂ) (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V)

theorem vertex_le_test (v : Vertex) : vertexOpen t v ≤ testCover t V hV (chartIndex v) :=
  (vertexWithin t v).trans (seed_chart_within V t hV (chartIndex v))

variable (ht : AlgebraicIndependent ℚ t)

def nativeTest : One (curveForms t) (vertexOpen t) :=
  restrictOne (testCover t V hV) (vertexOpen t) chartIndex (vertex_le_test t V hV) (evaluatedTest t ht V hV)

theorem nativeTest_closed : IsOneCocycle (curveForms t) (vertexOpen t) (nativeTest t V hV ht) :=
  restrictOne_closed _ _ _ _ _ (evaluatedTest_closed t ht V hV)

theorem evaluated_class_native : timeHodge t ht V hV (qHodge V t ambientTestClass) =
    cechOneClass (vertexOpen t) (vertexOpen_cover t) (nativeTest t V hV ht) (nativeTest_closed t V hV ht) := by
  rw [testEvaluation_class]
  exact (cechOneClass_refinement (testCover t V hV) (vertexOpen t) chartIndex (vertex_le_test t V hV)
    (testCover_top t V hV) (vertexOpen_cover t) (evaluatedTest t ht V hV) (evaluatedTest_closed t ht V hV)).symm

theorem nativeTest_edge (u v : Vertex) (W : (Curve t).Opens) (hu : W ≤ vertexOpen t u)
    (hv : W ≤ vertexOpen t v) :
    edgeValue (curveForms t) (vertexOpen t) (nativeTest t V hV ht) u v W hu hv =
      edgeValue (curveForms t) (testCover t V hV) (evaluatedTest t ht V hV) (chartIndex u) (chartIndex v) W
        (hu.trans (vertex_le_test t V hV u)) (hv.trans (vertex_le_test t V hV v)) :=
  edgeValue_restrictOne _ _ _ _ _ _ _ _ _ _

end CycleQ2LiteralThreefoldCurveEvaluationRefinement
end

#print axioms CycleQ2LiteralThreefoldCurveEvaluationRefinement.evaluated_class_native
#print axioms CycleQ2LiteralThreefoldCurveEvaluationRefinement.nativeTest_edge
