import Proposal.GeometricSurfaceResidueFunctoriality
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Exact direct image of additive sheaves along a closed embedding

A local lift over a point on the closed subspace extends to an ambient
neighborhood with exactly the same inverse image. At points of the complement,
the direct-image sheaf has the zero section group on a neighborhood.
Consequently direct image preserves epimorphisms as well as finite limits.
Its inverse-image left adjoint preserves monomorphisms, so direct image also
preserves injective objects.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2ClosedEmbeddingSheafExact

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace Opposite
  CycleQ2ClosedSupportCohomology

variable {X Y : TopCat.{0}} (f : X ⟶ Y)
abbrev push := TopCat.Sheaf.pushforward AddCommGrpCat.{0} f

instance : (push f).Additive where

private theorem lift_on_preimage {F G : X.Sheaf AddCommGrpCat.{0}} (p : F ⟶ G)
    {U W : Opens Y} {V : Opens X} (hw : W ≤ U) (hv : V ≤ (Opens.map f).obj U)
    (he : (Opens.map f).obj W = V) (t : G.obj.obj (op ((Opens.map f).obj U)))
    (hs : ∃ s, p.hom.app (op V) s = G.obj.map (homOfLE hv).op t) :
    ∃ s, ((push f).map p).hom.app (op W) s = ((push f).obj G).obj.map (homOfLE hw).op t := by
  subst V
  exact hs

/-- Direct image across a closed embedding sends every sheaf epimorphism to an epimorphism. -/
theorem push_epi (hf : IsClosedEmbedding f) {F G : X.Sheaf AddCommGrpCat.{0}} (p : F ⟶ G)
    [Epi p] : Epi ((push f).map p) := by
  apply (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp
  apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
  intro U t y hy
  by_cases h : y ∈ Set.range f
  · obtain ⟨x,rfl⟩ := h
    have hp := (TopCat.Presheaf.isLocallySurjective_iff p.hom).mp
      ((TopCat.Sheaf.isLocallySurjective_iff_epi p).mpr inferInstance)
    obtain ⟨V,hV,hs,hx⟩ := hp ((Opens.map f).obj U) t x hy
    let W := U ⊓ extendedOpen f hf V
    have he : (Opens.map f).obj W = V := by
      change (Opens.map f).obj U ⊓ (Opens.map f).obj (extendedOpen f hf V) = V
      rw [preimage_extendedOpen,inf_eq_right.mpr hV]
    exact ⟨W, inf_le_left, lift_on_preimage f p inf_le_left hV he t hs,
      show x ∈ (Opens.map f).obj W from he.symm ▸ hx⟩
  · let W := U ⊓ extendedOpen f hf (⊥ : Opens X)
    have he : (Opens.map f).obj W = ⊥ := by
      change (Opens.map f).obj U ⊓ (Opens.map f).obj (extendedOpen f hf ⊥) = ⊥
      rw [preimage_extendedOpen, inf_bot_eq]
    have hsub := AddCommGrpCat.isZero_iff_subsingleton.mp (G.isTerminalOfEqEmpty he).isZero
    refine ⟨W,inf_le_left,⟨0,hsub.elim _ _⟩,hy,?_⟩
    exact fun ⟨x,_,hx⟩ => h ⟨x,hx⟩

theorem push_preservesFiniteColimits (hf : IsClosedEmbedding f) :
    PreservesFiniteColimits (push f) := by
  apply (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).mpr
  intro S hS
  have := hS.epi_g
  exact ⟨((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).mp
    (inferInstance : PreservesFiniteLimits (push f)) S hS).1, push_epi f hf S.g⟩

theorem push_preservesInjectiveObjects : (push f).PreservesInjectiveObjects := by
  let : PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{0} f) := by
    unfold TopCat.Sheaf.pullback
    exact Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat f)

end CycleQ2ClosedEmbeddingSheafExact
end

#print axioms CycleQ2ClosedEmbeddingSheafExact.push_preservesFiniteColimits
#print axioms CycleQ2ClosedEmbeddingSheafExact.push_preservesInjectiveObjects
