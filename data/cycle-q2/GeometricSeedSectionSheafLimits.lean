import Proposal.GeometricSeedSectionSheafGlobal
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Actual sections of the twisted kernel

Evaluation of an original scheme module preserves limits.  Applying that
fact to the independently defined product and kernel identifies its
sections with compatible families of original chart-ideal sections.
The construction uses the native categorical limits; it does not replace
the source by a chosen compatible-family model.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedSectionSheafLimits

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2SeedProjectiveImageCocycle CycleQ2SeedSectionSheaf

section ActualLimits

variable {X : Scheme.{0}}

def sectionFunctor (X : Scheme.{0}) (V : X.Opens) : X.Modules ⥤ Ab :=
  Scheme.Modules.toPresheaf X ⋙ (evaluation X.Opensᵒᵖ Ab).obj (op V)

instance (V : X.Opens) : PreservesLimits (sectionFunctor X V) := by
  dsimp only [sectionFunctor]
  haveI : PreservesLimits ((evaluation X.Opensᵒᵖ Ab).obj (op V)) :=
    evaluationPreservesLimits (op V)
  exact comp_preservesLimits (Scheme.Modules.toPresheaf X)
    ((evaluation X.Opensᵒᵖ Ab).obj (op V))

instance (V : X.Opens) : (sectionFunctor X V).Additive where
  map_add := by intros; rfl

def sectionFan {ι : Type} (M : ι → X.Modules) (V : X.Opens) :
    Fan (fun i => Γ(M i, V)) :=
  Fan.mk (AddCommGrpCat.of (∀ i, Γ(M i, V))) fun i =>
    AddCommGrpCat.ofHom
      { toFun := fun s => s i
        map_zero' := rfl
        map_add' := fun _ _ => rfl }

def sectionFanIsLimit {ι : Type} (M : ι → X.Modules) (V : X.Opens) :
    IsLimit (sectionFan M V) :=
  Fan.IsLimit.mk _
    (fun s => AddCommGrpCat.ofHom
      { toFun := fun x i => s.proj i x
        map_zero' := by funext i; exact map_zero (s.proj i).hom
        map_add' := by intro x y; funext i; exact map_add (s.proj i).hom x y })
    (by intro s i; rfl)
    (by
      intro s m hm
      apply AddCommGrpCat.ext
      intro x
      funext i
      exact ConcreteCategory.congr_hom (hm i) x)

/-- Sections of the native categorical product, with its actual projections. -/
def sectionProductEquiv {ι : Type} (M : ι → X.Modules) (V : X.Opens) :
    Γ(∏ᶜ M, V) ≃+ (∀ i, Γ(M i, V)) :=
  (IsLimit.conePointUniqueUpToIso
    (isLimitOfHasProductOfPreservesLimit (sectionFunctor X V) M)
    (sectionFanIsLimit M V)).addCommGroupIsoToAddEquiv

theorem sectionProductEquiv_apply {ι : Type} (M : ι → X.Modules) (V : X.Opens)
    (s : Γ(∏ᶜ M, V)) (i : ι) :
    sectionProductEquiv M V s i = (Pi.π M i).app V s := by
  exact ConcreteCategory.congr_hom
    (IsLimit.conePointUniqueUpToIso_hom_comp
      (isLimitOfHasProductOfPreservesLimit (sectionFunctor X V) M)
      (sectionFanIsLimit M V) (Discrete.mk i)) s

theorem sectionProductEquiv_symm_apply {ι : Type} (M : ι → X.Modules)
    (V : X.Opens) (s : ∀ i, Γ(M i, V)) (i : ι) :
    (Pi.π M i).app V ((sectionProductEquiv M V).symm s) = s i := by
  have h := congrFun ((sectionProductEquiv M V).apply_symm_apply s) i
  simpa only [sectionProductEquiv_apply] using h

/-- Sections of a native sheaf kernel are the kernel of the actual section map. -/
def sectionKernelEquiv {M N : X.Modules} (f : M ⟶ N) (V : X.Opens) :
    Γ(kernel f, V) ≃+ (f.app V).hom.ker :=
  ((PreservesKernel.iso (sectionFunctor X V) f) ≪≫
    AddCommGrpCat.kernelIsoKer ((sectionFunctor X V).map f)).addCommGroupIsoToAddEquiv

theorem sectionKernelEquiv_val {M N : X.Modules} (f : M ⟶ N) (V : X.Opens)
    (s : Γ(kernel f, V)) :
    (sectionKernelEquiv f V s).val = (kernel.ι f).app V s := by
  have h : (PreservesKernel.iso (sectionFunctor X V) f).hom ≫
      (AddCommGrpCat.kernelIsoKer ((sectionFunctor X V).map f)).hom ≫
        AddCommGrpCat.ofHom (AddSubgroup.subtype (((sectionFunctor X V).map f).hom.ker)) =
      (sectionFunctor X V).map (kernel.ι f) := by
    rw [AddCommGrpCat.kernelIsoKer_hom_comp_subtype,
      PreservesKernel.iso_hom, kernelComparison_comp_ι]
  exact ConcreteCategory.congr_hom h s

theorem sectionKernelEquiv_symm_val {M N : X.Modules} (f : M ⟶ N)
    (V : X.Opens) (s : (f.app V).hom.ker) :
    (kernel.ι f).app V ((sectionKernelEquiv f V).symm s) = s.val := by
  have h := sectionKernelEquiv_val f V ((sectionKernelEquiv f V).symm s)
  rw [AddEquiv.apply_symm_apply] at h
  exact h.symm

end ActualLimits

/-- Native compatibility in the actual pairwise pushforward modules. -/
def FamilyCompatible (V : Surface.Opens) (s : ∀ i, Γ(idealPatch i, V)) : Prop :=
  ∀ i j, (leftIdealToPair i j).app V (s i) =
    (pairTwist i j).app V ((rightIdealToPair i j).app V (s j))

def sourceFamily (V : Surface.Opens) :
    Γ(twistedIdeal, V) →+ (∀ i, Γ(idealPatch i, V)) where
  toFun s i := (chartProjection i).app V s
  map_zero' := by funext i; exact map_zero ((chartProjection i).app V).hom
  map_add' := by intro s t; funext i; exact map_add ((chartProjection i).app V).hom s t

theorem sourceFamily_compatible (V : Surface.Opens) (s : Γ(twistedIdeal, V)) :
    FamilyCompatible V (sourceFamily V s) := by
  intro i j
  exact congrArg (fun f => f.app V s) (chartProjection_compatibility i j)

/-- The original chart projections jointly detect a section of the actual kernel. -/
theorem sourceFamily_injective (V : Surface.Opens) :
    Function.Injective (sourceFamily V) := by
  intro s t hst
  apply (sectionKernelEquiv twistedDifference V).injective
  apply Subtype.ext
  rw [sectionKernelEquiv_val, sectionKernelEquiv_val]
  apply (sectionProductEquiv idealPatch V).injective
  funext i
  rw [sectionProductEquiv_apply, sectionProductEquiv_apply]
  exact congrFun hst i

theorem familyProduct_mem_kernel (V : Surface.Opens)
    (s : ∀ i, Γ(idealPatch i, V)) (hs : FamilyCompatible V s) :
    (sectionProductEquiv idealPatch V).symm s ∈ (twistedDifference.app V).hom.ker := by
  change twistedDifference.app V ((sectionProductEquiv idealPatch V).symm s) = 0
  apply (sectionProductEquiv
    (fun p : Fin 3 × Fin 3 => patchStructure (PairPatch p.1 p.2)) V).injective
  funext p
  rw [sectionProductEquiv_apply, map_zero]
  change (twistedDifference ≫ Pi.π
    (fun p : Fin 3 × Fin 3 => patchStructure (PairPatch p.1 p.2)) p).app V
      ((sectionProductEquiv idealPatch V).symm s) = 0
  rw [twistedDifference, Pi.lift_π]
  change (leftIdealToPair p.1 p.2).app V
      ((Pi.π idealPatch p.1).app V ((sectionProductEquiv idealPatch V).symm s)) -
    (pairTwist p.1 p.2).app V ((rightIdealToPair p.1 p.2).app V
      ((Pi.π idealPatch p.2).app V ((sectionProductEquiv idealPatch V).symm s))) = 0
  rw [sectionProductEquiv_symm_apply, sectionProductEquiv_symm_apply]
  exact sub_eq_zero.mpr (hs p.1 p.2)

/-- A compatible family gives a section of the original kernel itself. -/
def compatibleFamilySection (V : Surface.Opens)
    (s : ∀ i, Γ(idealPatch i, V)) (hs : FamilyCompatible V s) : Γ(twistedIdeal, V) :=
  (sectionKernelEquiv twistedDifference V).symm
    ⟨(sectionProductEquiv idealPatch V).symm s, familyProduct_mem_kernel V s hs⟩

theorem compatibleFamilySection_projection (V : Surface.Opens)
    (s : ∀ i, Γ(idealPatch i, V)) (hs : FamilyCompatible V s) (i : Fin 3) :
    (chartProjection i).app V (compatibleFamilySection V s hs) = s i := by
  change (Pi.π idealPatch i).app V ((kernel.ι twistedDifference).app V
    ((sectionKernelEquiv twistedDifference V).symm _)) = s i
  rw [sectionKernelEquiv_symm_val]
  exact sectionProductEquiv_symm_apply idealPatch V s i

end CycleQ2SeedSectionSheafLimits

end

#print axioms CycleQ2SeedSectionSheafLimits.sectionKernelEquiv
#print axioms CycleQ2SeedSectionSheafLimits.sourceFamily_injective
#print axioms CycleQ2SeedSectionSheafLimits.compatibleFamilySection_projection
