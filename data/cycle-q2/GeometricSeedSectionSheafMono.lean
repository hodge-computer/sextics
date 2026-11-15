import Proposal.GeometricSeedSectionSheafEvaluation

/-!
# The original chart ideals embed on every actual open

The maps below are the literal ideal inclusions already used to define
the fixed twisted source. Their injectivity is transported through the
original affine chart isomorphisms, then through the actual open-patch
pushforwards and section normalization. No affineness assumption on the
open set is required.

Source-only draft: no Lean elaboration or kernel replay was run.
Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedSectionSheafMono

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2SeedProjectiveImageChart CycleQ2SeedProjectiveImageCocycle
  CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2SeedSectionSheaf
  CycleQ2SeedSectionSheafSections CycleQ2SeedSectionSheafEvaluation

theorem affineInclusion_app_injective (i : Fin 3)
    (U : (Spec (CommRingCat.of (AffineRing i))).Opens) :
    Function.Injective ((affineInclusion i).app U) := by
  intro s t hst
  apply CycleQ2SeedImageSheafEmbedding.tilde_map_app_injective
    (ModuleCat.ofHom (OrbitIdeal i).subtype) Subtype.val_injective U
  apply iso_app_injective (tildeSelf (R := CommRingCat.of (AffineRing i))) U
  exact hst

theorem chartInclusion_app_injective (i : Fin 3)
    (U : (Patch i).toScheme.Opens) :
    Function.Injective ((chartInclusion i).app U) := by
  intro s t hst
  apply affineInclusion_app_injective i
    ((coordinateAffineChart 57 1 i.succ).hom ''ᵁ U)
  apply iso_app_injective
    (Scheme.Modules.restrictUnitIso (coordinateAffineChart 57 1 i.succ).hom) U
  exact hst

theorem idealPatchInclusion_app_injective (i : Fin 3) (V : Surface.Opens) :
    Function.Injective ((idealPatchInclusion i).app V) :=
  chartInclusion_app_injective i ((Patch i).ι ⁻¹ᵁ V)

instance chartInclusion_mono (i : Fin 3) : Mono (chartInclusion i) where
  right_cancellation {P} g h H := by
    apply Scheme.Modules.hom_ext
    intro U
    apply ConcreteCategory.hom_ext
    intro s
    apply chartInclusion_app_injective i U
    exact congrArg (fun f : P ⟶ structureModule (Patch i).toScheme => f.app U s) H

instance idealPatchInclusion_mono (i : Fin 3) : Mono (idealPatchInclusion i) where
  right_cancellation {P} g h H := by
    apply Scheme.Modules.hom_ext
    intro U
    apply ConcreteCategory.hom_ext
    intro s
    apply idealPatchInclusion_app_injective i U
    exact congrArg (fun f : P ⟶ patchStructure (Patch i) => f.app U s) H

/-- The original chart-ideal inclusion, read in the ambient section ring. -/
def idealCoordinate (i : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i) :
    Γ(idealPatch i, V) →ₗ[Γ(Surface, V)] Γ(Surface, V) :=
  patchMap (idealPatchInclusion i) V hi

theorem idealCoordinate_injective (i : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) : Function.Injective (idealCoordinate i V hi) :=
  (patchSectionsEquiv (Patch i) V hi).injective.comp
    (idealPatchInclusion_app_injective i V)

theorem idealCoordinate_restrict (i : Fin 3) {V W : Surface.Opens}
    (hWV : W ≤ V) (hi : V ≤ Patch i) (s : Γ(idealPatch i, V)) :
    Surface.presheaf.map (homOfLE hWV).op (idealCoordinate i V hi s) =
      idealCoordinate i W (hWV.trans hi)
        ((idealPatch i).presheaf.map (homOfLE hWV).op s) :=
  patchMap_restrict _ hWV hi s

end CycleQ2SeedSectionSheafMono

end

#print axioms CycleQ2SeedSectionSheafMono.chartInclusion_app_injective
#print axioms CycleQ2SeedSectionSheafMono.idealPatchInclusion_mono
#print axioms CycleQ2SeedSectionSheafMono.idealCoordinate_injective
