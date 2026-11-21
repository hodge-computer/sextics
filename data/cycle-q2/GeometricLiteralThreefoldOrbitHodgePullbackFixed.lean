import Proposal.GeometricLiteralThreefoldOrbitHodgePullback
import Proposal.GeometricLiteralThreefoldOrbitHodgePullbackCharts
import Proposal.GeometricLiteralThreefoldOrbitActionInclusion
import Proposal.GeometricLiteralThreefoldOrbitCech
import Proposal.GeometricLiteralThreefoldTestClass

/-!
# The literal cyclic action on the six threefold overlap forms

On each of the original four charts the automorphism fixes the open and scales
the coordinates by the cyclic action. Its actual derived pullback on H¹ acts
on each oriented edge by the induced differential on the native overlap ring.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralThreefoldOrbitHodgePullback
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
  CycleQ2GeometricAffineChartSections CycleQ2GeometricDifferentialSheaf
  CycleQ2GeometricSectionDifferentials CycleQ2ExteriorSectionNaturality CycleQ2ChartExteriorBinding
  CycleQ2LiteralThreefoldOrbitAction CycleQ2FiniteCechOrbitPullback CycleQ2GeometricSheafLocalIso
  CycleQ2GeometricProjectiveHOne CycleQ2LiteralThreefoldHodgeCech CycleQ2LiteralAmbientCharts
  CycleQ2LiteralThreefoldResidueCoordinates CycleQ2LiteralThreefoldResidueChartMaps
  CycleQ2LiteralThreefoldOverlapAtlas CycleQ2FiniteInjectiveCech CycleQ2LiteralThreefoldOrbitCech
  CycleQ2ChartSectionPullback

attribute [local instance] sourceFixedAlgebra sourceFixedTower CycleQ2LiteralThreefoldHodgeCech.complexOn

variable (z : ℂ) (hz : z^3 = 1)
private abbrev e := threefoldAction z hz
private abbrev hc := threefoldAction_overComplex z hz

theorem fixedStable (i : Fin 4) : fixedOpen i ≤ (e z hz).hom ⁻¹ᵁ fixedOpen i :=
  (fixedOpen_preimage z hz i).ge

theorem overlapAction_target (i : Fin 4) (k : Fin 3) (a : CycleQ2LiteralAbelJacobiContraction.T (i.succAbove k)) :
    overlapAction z hz i k (fixedTargetMap i k a) = fixedTargetMap i k (chartAction z hz (i.succAbove k) a) :=
  overlapAction_target_of_chart z hz i k (chartInclusion_equivariant z hz) a

theorem overlapAlgebraMap_action (i : Fin 4) (k : Fin 3) (O W : Threefold.Opens)
    (hO : O ≤ fixedOpen i ⊓ fixedOpen (i.succAbove k)) (hW : W ≤ fixedOpen i ⊓ fixedOpen (i.succAbove k))
    (hWO : W ≤ (e z hz).hom ⁻¹ᵁ O) (a : FixedOverlap i k) :
    (e z hz).hom.appLE O W hWO (overlapAlgebraMap i k O hO a) =
      overlapAlgebraMap i k W hW (overlapAction z hz i k a) :=
  chartSection_pullback (e z hz).hom (overlapIso i k).symm (overlapIso i k).symm
    (overlapAction z hz i k).toRingHom
    (inf_le_inf (fixedStable z hz i) (fixedStable z hz (i.succAbove k)))
    (overlapIso_equivariant_of_chart z hz i k (chartInclusion_equivariant z hz i)) O hO W hW hWO a

def transformedEdges (ω : NativeEdges) : NativeEdges := fun i k =>
  exteriorDifferentialMap (overlapAction z hz i k) 2 (ω i k)

theorem pull_overlapSection (i : Fin 4) (k : Fin 3) (O W : Threefold.Opens)
    (hO : O ≤ fixedOpen i ⊓ fixedOpen (i.succAbove k)) (hW : W ≤ fixedOpen i ⊓ fixedOpen (i.succAbove k))
    (hWO : W ≤ (e z hz).hom ⁻¹ᵁ O) (ω : NativeForms i k) :
    pullTo (F := HodgeSheaf) (G := HodgeSheaf) (e z hz).hom.base (hodgeAdd (e z hz) (hc z hz)) hWO
      (overlapSection i k O hO ω) = overlapSection i k W hW (exteriorDifferentialMap (overlapAction z hz i k) 2 ω) :=
  formsMap_sectionLift_restrict (e z hz).hom coefficients coefficients (compatible _ (hc z hz)) 2
    O (overlapAlgebraMap i k O hO).toRingHom (overlapAlgebraMap i k O hO).commutes W hWO
    (overlapAlgebraMap i k W hW).toRingHom (overlapAlgebraMap i k W hW).commutes (overlapAction z hz i k)
    (overlapAlgebraMap_action z hz i k O W hO hW hWO) ω

abbrev fixedPull := hodgePull (e z hz) (hc z hz)
abbrev fixedCocycle := actedCocycle (e z hz) (hc z hz) (fixedStable z hz)

/-- Pullback of the original ambient Hodge class on the fixed cover. -/
theorem hodgePull_testClass :
    fixedPull z hz CycleQ2LiteralThreefoldTestClass.ambientTestClass =
      CycleQ2FiniteCechHOne.cechOneClass fixedOpen fixedOpen_cover
        (fixedCocycle z hz CycleQ2LiteralThreefoldTestEdges.nativeEdge CycleQ2LiteralThreefoldTestClass.face)
        (actedCocycle_closed _ _ _ _ _) :=
  hodgePull_class (e z hz) (hc z hz) (fixedStable z hz)
    CycleQ2LiteralThreefoldTestEdges.nativeEdge CycleQ2LiteralThreefoldTestClass.face

theorem actedCocycle_edge_lt (ω : NativeEdges) (hω) (i j : Fin 4) (hij : i < j)
    (W : Threefold.Opens) (hi : W ≤ fixedOpen i) (hj : W ≤ fixedOpen j) :
    edgeValue HodgeSheaf fixedOpen (fixedCocycle z hz ω hω) i j W hi hj =
      edge (transformedEdges z hz ω) i j hij W (le_inf hi hj) := by
  rw [actedCocycle_edgeValue, hodgeCocycle_edge_lt ω hω i j hij]
  exact pull_overlapSection z hz i (slot i j hij) _ _ _ _ _ _

theorem actedCocycle_ordered_pair (ω : NativeEdges) (hω) (i j : Fin 4) (hij : i < j) :
    fixedCocycle z hz ω hω i j = edge (transformedEdges z hz ω) i j hij _ le_rfl := by
  have h := actedCocycle_edge_lt z hz ω hω i j hij _ inf_le_left inf_le_right
  exact (res_self HodgeSheaf _ _).symm.trans h

end CycleQ2LiteralThreefoldOrbitHodgePullback
end

#print axioms CycleQ2LiteralThreefoldOrbitHodgePullback.overlapAction_target
#print axioms CycleQ2LiteralThreefoldOrbitHodgePullback.pull_overlapSection
#print axioms CycleQ2LiteralThreefoldOrbitHodgePullback.hodgePull_testClass
#print axioms CycleQ2LiteralThreefoldOrbitHodgePullback.actedCocycle_ordered_pair
