import Proposal.GeometricLiteralMovingDivisorOrbitPullbackIdeal

/-!
# The literal three translated Cartier frames generate the orbit ideal

This comparison holds on every simultaneous matrix-pivot and translated
Cartier open. Each factor is the original curve ideal pulled back by the
corresponding projective automorphism of the given surface.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralMovingDivisorOrbitProduct

open CategoryTheory AlgebraicGeometry TopologicalSpace
  CycleQ2SeedProjectiveImageCocycle CycleQ2SeedSectionDivisorTransitions
  CycleQ2LinkageComponentAlgebra CycleQ2LiteralOrbitAction CycleQ2LiteralOrbitChern
  CycleQ2LiteralMovingDivisorOrbitPullback CycleQ2LiteralMovingDivisorOrbitFrames

abbrev action : Surface ⟶ Surface := (closedProjectiveAction complexRoot complexRoot_cube).hom

private theorem action_sq : action ≫ action =
    (closedProjectiveAction (complexRoot^2) (by rw [← pow_mul, Nat.mul_comm, pow_mul, complexRoot_cube, one_pow])).hom := by
  simpa only [pow_two] using
    closedProjectiveAction_hom_comp complexRoot complexRoot complexRoot_cube complexRoot_cube

theorem productGenerator_span {W : Surface.Opens} (f : FrameData W)
    (i : CycleQ2LiteralOrbitChern.Index)
    (hi : W ≤ commonCover (𝟙 Surface) action (action ≫ action) i) :
    Ideal.span {productGenerator (𝟙 Surface) action (action ≫ action) i W hi} =
      Ideal.span {pivotEquation f} := by
  have factor (z : ℂ) (hz : z^3 = 1) (j : Surface ⟶ Surface)
      (hj : (closedProjectiveAction z hz).hom = j) (v : CycleQ2LiteralProjectiveIntersections.Vertex)
      (hv : W ≤ j ⁻¹ᵁ CycleQ2LiteralNativeGaugeSections.cover v) :
      Ideal.span {edgeGenerator j v W hv} = translateIdeal f.chart W f.within z := by
    subst j
    exact edgeGenerator_span z hz f.chart W f.within v hv
  rw [pivotEquation_span_product, productGenerator, ← Ideal.span_singleton_mul_span_singleton,
    ← Ideal.span_singleton_mul_span_singleton]
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·)
    (factor 1 (one_pow 3) _ closedProjectiveAction_hom_one _ _)
    (factor complexRoot complexRoot_cube _ rfl _ _))
    (factor (complexRoot^2) _ _ action_sq.symm _ _)

end CycleQ2LiteralMovingDivisorOrbitProduct

end

#print axioms CycleQ2LiteralMovingDivisorOrbitProduct.productGenerator_span
