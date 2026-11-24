import Proposal.GeometricSeedSectionInvertible
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Gluing additive morphisms on affine opens with a moving Cartier frame

The affine opens carrying a unit-matrix pivot are a basis of the original
surface. Maps on these opens that commute with restriction for every pair
of frames extend uniquely to a sheaf morphism on the whole surface.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralMovingResidueBasis
open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
  CycleQ2SeedProjectiveImageCocycle CycleQ2SeedSectionDivisorTransitions CycleQ2SeedSectionInvertible

structure FramedAffine where
  carrier : Surface.Opens
  affine : IsAffineOpen carrier
  frame : FrameData carrier

theorem isBasis_framedAffine : Opens.IsBasis (Set.range FramedAffine.carrier) := by
  apply Opens.isBasis_iff_nbhd.mpr
  intro U x hx
  obtain ⟨i,p,hp⟩ := exists_pivotOpen_at x
  obtain ⟨W,hW,hxW,hWU⟩ := Opens.isBasis_iff_nbhd.mp Surface.isBasis_affineOpens
    (show x ∈ U ⊓ pivotOpen i p from ⟨hx,hp⟩)
  let A : FramedAffine := ⟨W,hW,(pivotFrameData i p).restrict (hWU.trans inf_le_right)⟩
  exact ⟨W,⟨A,rfl⟩,hxW,hWU.trans inf_le_left⟩

variable {F G : TopCat.Sheaf AddCommGrpCat.{0} (show TopCat from Surface)}
variable (a : (W : FramedAffine) → F.obj.obj (op W.carrier) →+ G.obj.obj (op W.carrier))
    (h : ∀ (W V : FramedAffine) (j : V.carrier ≤ W.carrier) (s : F.obj.obj (op W.carrier)),
      a V (F.obj.map (homOfLE j).op s) = G.obj.map (homOfLE j).op (a W s))

private def onBasis : (inducedFunctor FramedAffine.carrier).op ⋙ F.obj ⟶
    (inducedFunctor FramedAffine.carrier).op ⋙ G.obj where
  app W := AddCommGrpCat.ofHom (a W.unop)
  naturality W V j := by
    apply ConcreteCategory.hom_ext
    exact h W.unop V.unop j.unop.hom.le

/-- Extend the actual component maps to the entire surface. -/
def extend : F ⟶ G where
  hom := TopCat.Sheaf.restrictHomEquivHom F.obj G isBasis_framedAffine (onBasis a h)

theorem extend_apply (W : FramedAffine) (s : F.obj.obj (op W.carrier)) :
    (extend a h).hom.app (op W.carrier) s = a W s := by
  exact ConcreteCategory.congr_hom
    (TopCat.Sheaf.extend_hom_app (F := F.obj) (F' := G) isBasis_framedAffine (onBasis a h) W) s

theorem extend_unique (g : F ⟶ G)
    (hg : ∀ W s, g.hom.app (op W.carrier) s = a W s) : g = extend a h := by
  apply CategoryTheory.Sheaf.hom_ext
  apply TopCat.Sheaf.hom_ext _ G isBasis_framedAffine
  intro W
  apply ConcreteCategory.hom_ext
  intro s
  exact (hg W s).trans (extend_apply a h W s).symm

end CycleQ2LiteralMovingResidueBasis
end

#print axioms CycleQ2LiteralMovingResidueBasis.extend
#print axioms CycleQ2LiteralMovingResidueBasis.extend_unique
