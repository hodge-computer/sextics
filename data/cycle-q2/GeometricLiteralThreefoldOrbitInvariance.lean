import Proposal.GeometricLiteralThreefoldOrbitGauge
import Proposal.GeometricLiteralThreefoldOrbitHodgePullbackFixed
import Proposal.GeometricLiteralThreefoldOrbitLiftEdge

/-!
# The fixed threefold Hodge class under the cyclic action

The original affine splittings and the inverse-transformed splittings give two
representatives. Their differences on the four opens are explicit two-forms.
The resulting equality in derived cohomology applies to every complex cube
root of unity.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralThreefoldOrbitInvariance

open CategoryTheory CycleQ2LiteralThreefoldOrbitLift CycleQ2LiteralThreefoldOrbitGauge
  CycleQ2LiteralThreefoldOrbitHodgePullback CycleQ2LiteralThreefoldTestEdges
  CycleQ2LiteralThreefoldTestClass CycleQ2LiteralThreefoldHodgeCech
  CycleQ2LiteralAmbientCharts CycleQ2FiniteInjectiveCech CycleQ2GeometricSheafLocalIso

variable (z : ℂ) (hz : z ^ 3 = 1)

/-- The chart corrections are taken at the actual inverse-transformed splittings. -/
def chartCorrection : VertexForms :=
  vertexOfLift (actedCanonical z hz) (actedCanonical_liesOver z hz)

/-- On each overlap the pulled-back test two-form differs from the original
one by the restricted chart corrections. -/
theorem edge_comparison (i : Fin 4) (k : Fin 3) :
    NativeComparison (chartCorrection z hz) (transformedEdges z hz nativeEdge) i k :=
  nativeComparison_of_lifts (actedCanonical z hz) (actedCanonical_liesOver z hz)
    (transformedEdges z hz nativeEdge) i k (actedNormalized z hz i k (overlapAction z hz i k))
    (actedNormalized_normalizes z hz i k _ (overlapAction_source z hz i k))
    (actedNormalized_liesOver z hz i k _ (overlapAction_target z hz i k))
    (actedNormalized_value z hz i k _ (overlapAction_target z hz i k) _)

/-- The induced pullback on the actual algebraic H¹ of the exterior-square
cotangent sheaf fixes the class of the test deformation. -/
theorem ambientTestClass_fixed : fixedPull z hz ambientTestClass = ambientTestClass := by
  rw [hodgePull_testClass]
  exact class_eq_ambientTestClass _ _ (edge_comparison z hz) _ _
    (actedCocycle_ordered_pair z hz nativeEdge face)

/-- Changing the local lift on each chart gives another representative of
the same fixed class. -/
theorem hodgeClass_fixed_of_vertex_corrections (ω : NativeEdges) (hω)
    (v : VertexForms) (hv : ∀ i k, NativeComparison v ω i k) :
    fixedPull z hz (hodgeClass ω hω) = hodgeClass ω hω := by
  have he : hodgeClass ω hω = ambientTestClass := by
    apply class_eq_ambientTestClass v ω hv (hodgeCocycle ω hω).val
      (fun i j k W hi hj hk => ((hodgeCocycle ω hω).condition i j k W hi hj hk).symm)
    intro i j hij
    exact (res_self HodgeSheaf _ _).symm.trans
      (CycleQ2LiteralThreefoldOrbitCech.hodgeCocycle_edge_lt ω hω i j hij _ inf_le_left inf_le_right)
  rw [he, ambientTestClass_fixed]

end CycleQ2LiteralThreefoldOrbitInvariance
end

#print axioms CycleQ2LiteralThreefoldOrbitInvariance.edge_comparison
#print axioms CycleQ2LiteralThreefoldOrbitInvariance.ambientTestClass_fixed
#print axioms CycleQ2LiteralThreefoldOrbitInvariance.hodgeClass_fixed_of_vertex_corrections
