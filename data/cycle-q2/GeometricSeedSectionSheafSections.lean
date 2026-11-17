import Proposal.GeometricSeedSectionSheaf

/-!
# Reading the twisted source in actual projective section rings

The maps here identify the sections of each pushed-forward structure
module with the original structure-sheaf sections on every subopen of
that patch.  The comparison uses the inverse of the actual open-immersion
section map, and is natural under all original restrictions.

This component does not replace any of the original ideal sheaves by a
free module.  It reads the already constructed global kernel source in
the ordinary projective section rings where its transition equations and
the section-functional balance are expressed.

-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedSectionSheafSections

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2SeedProjectiveImageCocycle CycleQ2SeedSectionSheaf

local instance patchSectionsCommRing (U V : Surface.Opens) :
    CommRing Γ(patchStructure U, V) :=
  inferInstanceAs (CommRing Γ(U.toScheme, U.ι ⁻¹ᵁ V))

private theorem patch_app_isIso (U V : Surface.Opens) (hV : V ≤ U) :
    IsIso (U.ι.app V) :=
  Scheme.Hom.isIso_app U.ι V (by simpa only [Scheme.Opens.opensRange_ι] using hV)

/-- The inverse of the original restriction to the open subscheme. -/
def patchSectionsEquiv (U V : Surface.Opens) (hV : V ≤ U) :
    Γ(patchStructure U, V) ≃+* Γ(Surface, V) :=
  letI := patch_app_isIso U V hV
  (asIso (U.ι.app V)).commRingCatIsoToRingEquiv.symm

@[simp] theorem patchSectionsEquiv_symm_apply (U V : Surface.Opens) (hV : V ≤ U)
    (a : Γ(Surface, V)) :
    (patchSectionsEquiv U V hV).symm a = U.ι.app V a := rfl

theorem patchSectionsEquiv_smul (U V : Surface.Opens) (hV : V ≤ U)
    (a : Γ(Surface, V)) (s : Γ(patchStructure U, V)) :
    patchSectionsEquiv U V hV (a • s) = a * patchSectionsEquiv U V hV s := by
  change patchSectionsEquiv U V hV
    ((show Γ(patchStructure U, V) from U.ι.app V a) * s) = _
  rw [map_mul]
  change patchSectionsEquiv U V hV ((patchSectionsEquiv U V hV).symm a) * _ = _
  rw [RingEquiv.apply_symm_apply]

/-- The actual normalization commutes with every smaller-open restriction. -/
theorem patchSectionsEquiv_restrict (U : Surface.Opens) {V W : Surface.Opens}
    (hWV : W ≤ V) (hV : V ≤ U) (s : Γ(patchStructure U, V)) :
    patchSectionsEquiv U W (hWV.trans hV)
        ((patchStructure U).presheaf.map (homOfLE hWV).op s) =
      Surface.presheaf.map (homOfLE hWV).op (patchSectionsEquiv U V hV s) := by
  apply (patchSectionsEquiv U W (hWV.trans hV)).symm.injective
  rw [RingEquiv.symm_apply_apply, patchSectionsEquiv_symm_apply]
  have h := ConcreteCategory.congr_hom
    (U.ι.naturality (homOfLE hWV).op) (patchSectionsEquiv U V hV s)
  change U.ι.app W
      (Surface.presheaf.map (homOfLE hWV).op (patchSectionsEquiv U V hV s)) =
    (patchStructure U).presheaf.map (homOfLE hWV).op
      ((patchSectionsEquiv U V hV).symm (patchSectionsEquiv U V hV s)) at h
  rw [RingEquiv.symm_apply_apply] at h
  exact h.symm

/-- Passing to a smaller patch does not change a section in the ambient
projective section ring. -/
theorem patchSectionsEquiv_patchRestriction {U V W : Surface.Opens}
    (hVU : V ≤ U) (hWV : W ≤ V) (s : Γ(patchStructure U, W)) :
    patchSectionsEquiv V W hWV ((patchStructureRestriction hVU).app W s) =
      patchSectionsEquiv U W (hWV.trans hVU) s := by
  obtain ⟨a, ha⟩ := (patchSectionsEquiv U W (hWV.trans hVU)).symm.surjective s
  subst s
  have h := congrArg
    (fun f : structureModule Surface ⟶ patchStructure V => f.app W a)
      (structureMap_patchRestriction hVU)
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h
  have h' :=
    (congrArg (fun z : Γ(patchStructure U, W) => (patchStructureRestriction hVU).app W z)
      (openStructureMap_app U.ι W a)).symm.trans
        (h.trans (openStructureMap_app V.ι W a))
  rw [patchSectionsEquiv_symm_apply U W (hWV.trans hVU), h']
  change patchSectionsEquiv V W hWV ((patchSectionsEquiv V W hWV).symm a) =
    patchSectionsEquiv U W (hWV.trans hVU)
      ((patchSectionsEquiv U W (hWV.trans hVU)).symm a)
  exact (RingEquiv.apply_symm_apply (patchSectionsEquiv V W hWV) a).trans
    (RingEquiv.apply_symm_apply (patchSectionsEquiv U W (hWV.trans hVU)) a).symm

section Morphism

variable {M : Surface.Modules} {U : Surface.Opens}

/-- Read a genuine morphism into a patch structure module as a natural
linear map into the original structure sheaf on each subopen. -/
def patchMap (f : M ⟶ patchStructure U) (V : Surface.Opens) (hV : V ≤ U) :
    Γ(M, V) →ₗ[Γ(Surface, V)] Γ(Surface, V) where
  toFun s := patchSectionsEquiv U V hV (f.app V s)
  map_add' s t := by rw [map_add, map_add]
  map_smul' a s := by
    rw [Scheme.Modules.Hom.app_smul, patchSectionsEquiv_smul] <;> rfl

theorem patchMap_restrict (f : M ⟶ patchStructure U) {V W : Surface.Opens}
    (hWV : W ≤ V) (hV : V ≤ U) (s : Γ(M, V)) :
    Surface.presheaf.map (homOfLE hWV).op (patchMap f V hV s) =
      patchMap f W (hWV.trans hV) (M.presheaf.map (homOfLE hWV).op s) := by
  change Surface.presheaf.map (homOfLE hWV).op
      (patchSectionsEquiv U V hV (f.app V s)) = _
  rw [← patchSectionsEquiv_restrict]
  have h := ConcreteCategory.congr_hom (f.mapPresheaf.naturality (homOfLE hWV).op) s
  exact congrArg (patchSectionsEquiv U W (hWV.trans hV)) h.symm

end Morphism

/-- The original ideal coordinate of a section of the fixed global source. -/
def sourceCoordinate (i : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i) :
    Γ(twistedIdeal, V) →ₗ[Γ(Surface, V)] Γ(Surface, V) :=
  patchMap (chartProjection i ≫ idealPatchInclusion i) V hi

/-- The original evaluation functional on that same source coordinate. -/
def evaluatedCoordinate (t : Fin 3 → ℂ) (i : Fin 3)
    (V : Surface.Opens) (hi : V ≤ Patch i) :
    Γ(twistedIdeal, V) →ₗ[Γ(Surface, V)] Γ(Surface, V) :=
  patchMap (localEvaluation t i) V hi

theorem sourceCoordinate_restrict (i : Fin 3) {V W : Surface.Opens}
    (hWV : W ≤ V) (hi : V ≤ Patch i) (s : Γ(twistedIdeal, V)) :
    Surface.presheaf.map (homOfLE hWV).op (sourceCoordinate i V hi s) =
      sourceCoordinate i W (hWV.trans hi)
        (twistedIdeal.presheaf.map (homOfLE hWV).op s) :=
  patchMap_restrict _ hWV hi s

theorem evaluatedCoordinate_restrict (t : Fin 3 → ℂ) (i : Fin 3)
    {V W : Surface.Opens} (hWV : W ≤ V) (hi : V ≤ Patch i)
    (s : Γ(twistedIdeal, V)) :
    Surface.presheaf.map (homOfLE hWV).op (evaluatedCoordinate t i V hi s) =
      evaluatedCoordinate t i W (hWV.trans hi)
        (twistedIdeal.presheaf.map (homOfLE hWV).op s) :=
  patchMap_restrict _ hWV hi s

end CycleQ2SeedSectionSheafSections

end

#print axioms CycleQ2SeedSectionSheafSections.patchSectionsEquiv_restrict
#print axioms CycleQ2SeedSectionSheafSections.patchSectionsEquiv_patchRestriction
#print axioms CycleQ2SeedSectionSheafSections.evaluatedCoordinate_restrict
