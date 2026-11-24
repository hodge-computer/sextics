import Proposal.GeometricSeedAffineReconstruction

/-!
# Global sections recover the prescribed affine comparison maps

The quasi-coherent comparison with a module model induces exactly the
specified global-section isomorphism followed by the canonical tilde unit.
Consequently, conjugating an associated-sheaf transition through two such
comparisons recovers the prescribed transition between their module models.

All global-section maps retain the native affine-ring module actions.
These generic identities do not assert compatibility between different
affine overlap charts or a triple-overlap cocycle.

Source-only draft: no Lean elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

namespace CycleQ2SeedAffineComparisonSections

open CategoryTheory AlgebraicGeometry
open CycleQ2SeedAffineReconstruction

variable {R : CommRingCat.{u}}

/-- The reconstructed comparison has the prescribed native global-section map. -/
theorem comparisonIso_map (M : (Spec R).Modules) [M.IsQuasicoherent]
    {E : ModuleCat R} (e : globalSections M ≅ E) :
    (moduleSpecΓFunctor (R := R)).map (comparisonIso M e).hom =
      e.hom ≫ (tilde.isoTop E).hom := by
  change (moduleSpecΓFunctor (R := R)).map
      (inv M.fromTildeΓ ≫ (tilde.functor R).map e.hom) = _
  rw [Functor.map_comp, map_inv_fromTildeΓ]
  exact tilde.toOpen_map_app e.hom ⊤

/-- The entire native global-section map of a conjugated sheaf transition
recovers its specified module transition through the two comparison maps. -/
theorem conjugatedTransition_map (M N : (Spec R).Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] {E F : ModuleCat R}
    (eM : globalSections M ≅ E) (eN : globalSections N ≅ F) (t : E ≅ F) :
    (moduleSpecΓFunctor (R := R)).map
        (comparisonIso M eM ≪≫ (tilde.functor R).mapIso t ≪≫
          (comparisonIso N eN).symm).hom ≫ eN.hom =
      eM.hom ≫ t.hom := by
  have hnat : (tilde.isoTop E).hom ≫
      (moduleSpecΓFunctor (R := R)).map ((tilde.functor R).map t.hom) =
        t.hom ≫ (tilde.isoTop F).hom :=
    tilde.toOpen_map_app t.hom ⊤
  apply (cancel_mono (tilde.isoTop F).hom).mp
  calc
    _ = (moduleSpecΓFunctor (R := R)).map
          (comparisonIso M eM ≪≫ (tilde.functor R).mapIso t ≪≫
            (comparisonIso N eN).symm).hom ≫
          (moduleSpecΓFunctor (R := R)).map (comparisonIso N eN).hom := by
      rw [Category.assoc, comparisonIso_map]
    _ = (moduleSpecΓFunctor (R := R)).map
          ((comparisonIso M eM).hom ≫ (tilde.functor R).map t.hom) := by
      rw [← Functor.map_comp]
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
        Iso.inv_hom_id, Category.comp_id, CategoryTheory.Functor.mapIso_hom]
    _ = (eM.hom ≫ (tilde.isoTop E).hom) ≫
          (moduleSpecΓFunctor (R := R)).map ((tilde.functor R).map t.hom) := by
      rw [Functor.map_comp, comparisonIso_map]
    _ = (eM.hom ≫ t.hom) ≫ (tilde.isoTop F).hom := by
      rw [Category.assoc, hnat, Category.assoc]

#print axioms comparisonIso_map
#print axioms conjugatedTransition_map

end CycleQ2SeedAffineComparisonSections
end
