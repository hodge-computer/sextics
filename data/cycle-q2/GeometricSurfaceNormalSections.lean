import Proposal.GeometricIntrinsicNormal
import Proposal.GeometricSurfaceNormalCharts
import Proposal.GeometricSurfaceOverlap
import Proposal.GeometricSurfaceResidueSections

/-!
# Actual intrinsic normal sections and their projective transition

The local normal vector is transported through the actual affine chart
squares into Hom(I, j_* O_C). Its values on the two fixed equations are
proved on every subopen. Affine localization gives generator-based
uniqueness, so the minor frames agree and glue on each coordinate patch
of the actual curve at (57, 1). Gluing uses a cover of the curve preimage
and vanishing away from the closed curve.

The coefficient action is the actual j_* O_C action. The two coordinate
normal sections have the inverse-square transition, obtained from the
weight-two equation change and weight-four coefficient change. This file
does not assume an identification with the separate twisted normal line.
-/

section NormalSectionsAffineLocalHomExtPart

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricIntrinsicNormal
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf

section LocalEvaluation
variable {T : TopCat.{0}} (R : T.Sheaf CommRingCat.{0})
  (M N : SheafOfModules.{0} (ringSheaf R))

@[simp] theorem localLinearHomEvaluate_subopen {U V : Opens T} (h : V ⟶ U)
    (f : LocalLinearHom R M N U) (m : M.val.obj (op V)) :
    localLinearHomEvaluate R M N V (restrictLocalLinearHom R M N h.op f) m =
      f.val.app (op (Over.mk h)) m := by
  exact ConcreteCategory.congr_hom
    (presheafHom_map_app_op_mk_id
      (F := M.val.presheaf) (G := N.val.presheaf) h f.val) m

end LocalEvaluation

section Affine
variable {A : CommRingCat.{0}} (M N : (Spec A).Modules)

private theorem affineLocalLinearHom_basic (hM : IsLocalizing (modulesSpecToSheaf.obj M))
    (U : (Spec A).Opens) (f g : LocalLinearHom (Spec A).sheaf M N U)
    (hfg : ∀ m : M.val.obj (op ⊤),
      localLinearHomEvaluate (Spec A).sheaf M N U f
          (M.val.map (homOfLE (show U ≤ ⊤ from le_top)).op m) =
        localLinearHomEvaluate (Spec A).sheaf M N U g
          (M.val.map (homOfLE (show U ≤ ⊤ from le_top)).op m))
    (a : A) (ha : PrimeSpectrum.basicOpen a ≤ U)
    (m : M.val.obj (op (PrimeSpectrum.basicOpen a))) :
    localLinearHomEvaluate (Spec A).sheaf M N (PrimeSpectrum.basicOpen a)
        (restrictLocalLinearHom (Spec A).sheaf M N (homOfLE ha).op f) m =
      localLinearHomEvaluate (Spec A).sheaf M N (PrimeSpectrum.basicOpen a)
        (restrictLocalLinearHom (Spec A).sheaf M N (homOfLE ha).op g) m := by
  let F := localLinearHomEvaluate (Spec A).sheaf M N (PrimeSpectrum.basicOpen a)
    (restrictLocalLinearHom (Spec A).sheaf M N (homOfLE ha).op f)
  let G := localLinearHomEvaluate (Spec A).sheaf M N (PrimeSpectrum.basicOpen a)
    (restrictLocalLinearHom (Spec A).sheaf M N (homOfLE ha).op g)
  have hglob (m₀ : M.val.obj (op ⊤)) :
      F (M.val.map (homOfLE (show PrimeSpectrum.basicOpen a ≤ ⊤ from le_top)).op m₀) =
        G (M.val.map (homOfLE (show PrimeSpectrum.basicOpen a ≤ ⊤ from le_top)).op m₀) := by
    have hf := localLinearHomEvaluate_restrict (Spec A).sheaf M N (homOfLE ha) f
      (M.val.map (homOfLE (show U ≤ ⊤ from le_top)).op m₀)
    have hg := localLinearHomEvaluate_restrict (Spec A).sheaf M N (homOfLE ha) g
      (M.val.map (homOfLE (show U ≤ ⊤ from le_top)).op m₀)
    have hh := congrArg (N.val.map (homOfLE ha).op) (hfg m₀)
    have hf' : F (M.val.map
        (homOfLE (show PrimeSpectrum.basicOpen a ≤ ⊤ from le_top)).op m₀) =
        N.val.map (homOfLE ha).op
          (localLinearHomEvaluate (Spec A).sheaf M N U f
            (M.val.map (homOfLE (show U ≤ ⊤ from le_top)).op m₀)) := by
      exact (congrArg F (M.val.map_comp_apply
        (homOfLE (show U ≤ ⊤ from le_top)).op (homOfLE ha).op m₀)).trans hf
    have hg' : N.val.map (homOfLE ha).op
        (localLinearHomEvaluate (Spec A).sheaf M N U g
          (M.val.map (homOfLE (show U ≤ ⊤ from le_top)).op m₀)) =
        G (M.val.map (homOfLE (show PrimeSpectrum.basicOpen a ≤ ⊤ from le_top)).op m₀) := by
      exact hg.symm.trans (congrArg G (M.val.map_comp_apply
        (homOfLE (show U ≤ ⊤ from le_top)).op (homOfLE ha).op m₀)).symm
    exact hf'.trans (hh.trans hg')
  let hloc : IsLocalizedModule (Submonoid.powers a)
      ((modulesSpecToSheaf.obj M).obj.map
        (homOfLE (show PrimeSpectrum.basicOpen a ≤ ⊤ from le_top)).op).hom := hM a
  obtain ⟨⟨m₀, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers a)
    ((modulesSpecToSheaf.obj M).obj.map
      (homOfLE (show PrimeSpectrum.basicOpen a ≤ ⊤ from le_top)).op).hom m
  change (algebraMap A Γ(Spec A, PrimeSpectrum.basicOpen a) (s : A)) • m =
    M.val.map (homOfLE (show PrimeSpectrum.basicOpen a ≤ ⊤ from le_top)).op m₀ at hs
  apply (IsLocalization.map_units Γ(Spec A, PrimeSpectrum.basicOpen a) s).isSMulRegular
    (N.val.obj (op (PrimeSpectrum.basicOpen a)))
  change _ • F m = _ • G m
  calc
    _ = F ((algebraMap A Γ(Spec A, PrimeSpectrum.basicOpen a) (s : A)) • m) :=
      (F.map_smul _ _).symm
    _ = F (M.val.map (homOfLE (show PrimeSpectrum.basicOpen a ≤ ⊤ from le_top)).op m₀) :=
      congrArg F hs
    _ = G (M.val.map (homOfLE (show PrimeSpectrum.basicOpen a ≤ ⊤ from le_top)).op m₀) :=
      hglob m₀
    _ = G ((algebraMap A Γ(Spec A, PrimeSpectrum.basicOpen a) (s : A)) • m) :=
      congrArg G hs.symm
    _ = _ := G.map_smul _ _

/-- On every subopen of an affine scheme, a local morphism out of a
localizing module sheaf is determined by the restrictions of global sections.
No affineness of the subopen or local-freeness premise is imposed. -/
theorem affineLocalLinearHom_ext (hM : IsLocalizing (modulesSpecToSheaf.obj M))
    (U : (Spec A).Opens) (f g : LocalLinearHom (Spec A).sheaf M N U)
    (hfg : ∀ m : M.val.obj (op ⊤),
      localLinearHomEvaluate (Spec A).sheaf M N U f
          (M.val.map (homOfLE (show U ≤ ⊤ from le_top)).op m) =
        localLinearHomEvaluate (Spec A).sheaf M N U g
          (M.val.map (homOfLE (show U ≤ ⊤ from le_top)).op m)) : f = g := by
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.hom_ext
  intro m
  apply TopCat.Presheaf.IsSheaf.section_ext N.isSheaf
  intro x hx
  obtain ⟨_, ⟨_, ⟨a, rfl⟩, rfl⟩, hxa, haV⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hx V.unop.left.isOpen
  have haU : PrimeSpectrum.basicOpen a ≤ U := haV.trans V.unop.hom.le
  refine ⟨PrimeSpectrum.basicOpen a, haV, hxa, ?_⟩
  have he := affineLocalLinearHom_basic M N hM U f g hfg a haU
    (M.val.map (homOfLE haV).op m)
  rw [localLinearHomEvaluate_subopen, localLinearHomEvaluate_subopen] at he
  let t : Over.mk (homOfLE haU) ⟶ V.unop := Over.homMk (homOfLE haV)
  exact (ConcreteCategory.congr_hom (f.val.naturality t.op) m).symm.trans
    (he.trans (ConcreteCategory.congr_hom (g.val.naturality t.op) m))

local instance affineSectionModule (U : (Spec A).Opens) :
    Module A (M.val.obj (op U)) := inferInstanceAs (Module A Γ(M, U))

/-- Evaluation on restrictions of affine global sections retains its actual
linear structure over the affine coordinate ring. -/
def affineLocalLinearHomGlobalMap (U : (Spec A).Opens)
    (f : LocalLinearHom (Spec A).sheaf M N U) :
    M.val.obj (op ⊤) →ₗ[A] N.val.obj (op U) where
  toFun m := localLinearHomEvaluate (Spec A).sheaf M N U f
    (M.val.map (homOfLE (show U ≤ ⊤ from le_top)).op m)
  map_add' m n := by
    rw [map_add, map_add]
  map_smul' a m := by
    change localLinearHomEvaluate (Spec A).sheaf M N U f
      (M.val.map (homOfLE (show U ≤ ⊤ from le_top)).op
        ((algebraMap A Γ(Spec A, ⊤) a) • m)) =
      (algebraMap A Γ(Spec A, U) a) • _
    rw [M.val.map_smul, map_smul]
    rfl

/-- Any proved family of affine global generators determines a local
morphism on every subopen by its values on that family. -/
theorem affineLocalLinearHom_ext_generators
    (hM : IsLocalizing (modulesSpecToSheaf.obj M))
    {ι : Type} (s : ι → M.val.obj (op ⊤))
    (hs : Submodule.span A (Set.range s) = ⊤)
    (U : (Spec A).Opens) (f g : LocalLinearHom (Spec A).sheaf M N U)
    (hfg : ∀ a, localLinearHomEvaluate (Spec A).sheaf M N U f
        (M.val.map (homOfLE (show U ≤ ⊤ from le_top)).op (s a)) =
      localLinearHomEvaluate (Spec A).sheaf M N U g
        (M.val.map (homOfLE (show U ≤ ⊤ from le_top)).op (s a))) : f = g := by
  have h : affineLocalLinearHomGlobalMap M N U f = affineLocalLinearHomGlobalMap M N U g := by
    apply LinearMap.ext_on hs
    rintro m ⟨a, rfl⟩
    exact hfg a
  exact affineLocalLinearHom_ext M N hM U f g (fun m => LinearMap.congr_fun h m)

#print axioms affineLocalLinearHom_ext
#print axioms affineLocalLinearHom_ext_generators
end Affine
end CycleQ2GeometricIntrinsicNormal
end

end NormalSectionsAffineLocalHomExtPart

section NormalSectionsLocalHomOpenSubopenPart

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricIntrinsicNormal
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf

variable {X Y : Scheme.{0}} (i : X ⟶ Y) [IsOpenImmersion i]

/-- Taking images under an open immersion identifies all subopens of an open
with all subopens of its image. -/
instance openImageOver_isEquivalence (U : X.Opens) :
    (Over.post (X := U) i.opensFunctor).IsEquivalence where
  essSurj :=
    { mem_essImage W := by
        let V : Over U := Over.mk (homOfLE (show i ⁻¹ᵁ W.left ≤ U from by
          simpa only [i.preimage_image_eq U] using i.preimage_mono W.hom.le))
        refine ⟨V, ⟨Over.isoMk (eqToIso ?_)⟩⟩
        exact (i.image_preimage_eq_opensRange_inf W.left).trans
          (inf_eq_right.mpr (W.hom.le.trans (i.image_le_opensRange U))) }

variable (M N : Y.Modules)

/-- Restrict a local linear morphism to an arbitrary open in an open chart.
Its components are the same maps on the corresponding actual image opens. -/
def localLinearHomOpenImageMap (U : X.Opens) :
    LocalLinearHom Y.sheaf M N (i ''ᵁ U) →
      LocalLinearHom X.sheaf (M.restrict i) (N.restrict i) U := fun f =>
  ⟨Functor.whiskerLeft (Over.post (X := U) i.opensFunctor).op f.val, by
    intro V r m
    exact f.property ((Over.post (X := U) i.opensFunctor).obj V)
      ((i.appIso V.left).inv r) m⟩

theorem localLinearHomOpenImageMap_injective (U : X.Opens) :
    Function.Injective (localLinearHomOpenImageMap i M N U) := by
  intro f g h
  apply Subtype.ext
  exact ((Functor.whiskeringLeft _ _ AddCommGrpCat).obj
    (Over.post (X := U) i.opensFunctor).op).map_injective
      (congrArg Subtype.val h)

@[simp] theorem localLinearHomOpenImageMap_evaluate (U : X.Opens)
    (f : LocalLinearHom Y.sheaf M N (i ''ᵁ U))
    (m : M.val.obj (op (i ''ᵁ U))) :
    localLinearHomEvaluate X.sheaf (M.restrict i) (N.restrict i) U
        (localLinearHomOpenImageMap i M N U f) m =
      localLinearHomEvaluate Y.sheaf M N (i ''ᵁ U) f m := rfl

end CycleQ2GeometricIntrinsicNormal
end

noncomputable section
namespace CycleQ2GeometricIntrinsicNormal
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf

variable {A : CommRingCat.{0}} {Y : Scheme.{0}} (i : Spec A ⟶ Y)
  [IsOpenImmersion i] (M N : Y.Modules)

/-- An actual affine chart detects a local morphism on every subopen from its
values on the restrictions of all affine global source sections. -/
theorem localLinearHomOpenImage_ext
    (hM : IsLocalizing (modulesSpecToSheaf.obj (M.restrict i)))
    (U : (Spec A).Opens) (f g : LocalLinearHom Y.sheaf M N (i ''ᵁ U))
    (hfg : ∀ m : M.val.obj (op (i ''ᵁ ⊤)),
      localLinearHomEvaluate Y.sheaf M N (i ''ᵁ U) f
          (M.val.map (homOfLE (i.image_mono (show U ≤ ⊤ from le_top))).op m) =
        localLinearHomEvaluate Y.sheaf M N (i ''ᵁ U) g
          (M.val.map (homOfLE (i.image_mono (show U ≤ ⊤ from le_top))).op m)) : f = g := by
  apply localLinearHomOpenImageMap_injective i M N U
  apply affineLocalLinearHom_ext (M.restrict i) (N.restrict i) hM U
  intro m
  exact hfg m

#print axioms openImageOver_isEquivalence
#print axioms localLinearHomOpenImageMap_injective
#print axioms localLinearHomOpenImage_ext
end CycleQ2GeometricIntrinsicNormal
end

end NormalSectionsLocalHomOpenSubopenPart

section NormalSectionsNormalAffineSubopenExtPart

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricIntrinsicNormal
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf

section AffineKernel
variable {A B : CommRingCat.{0}} (φ : A ⟶ B)

local instance affineKernelGlobalModule :
    Module A ((kernelIdealSheaf (Spec.map φ)).val.obj (op ⊤)) :=
  inferInstanceAs (Module A Γ((show (Spec A).Modules from kernelIdealSheaf (Spec.map φ)), ⊤))

/-- Normalization of the actual global ideal sections is linear over the
original affine ring, with its canonical action through the affine scheme. -/
def affineKernelGlobalLinearEquiv :
    (kernelIdealSheaf (Spec.map φ)).val.obj (op ⊤) ≃ₗ[A] RingHom.ker φ.hom where
  __ := (kernelIdealSectionEquiv (Spec.map φ) ⊤).toEquiv.trans
    (affineKernelSectionSemilinearEquiv φ).toEquiv
  map_add' a b := by
    change affineKernelSectionSemilinearEquiv φ
      (kernelIdealSectionEquiv (Spec.map φ) ⊤ (a + b)) = _
    rw [map_add, map_add]
    rfl
  map_smul' a m := by
    change affineKernelSectionSemilinearEquiv φ
      (kernelIdealSectionEquiv (Spec.map φ) ⊤
        ((algebraMap A Γ(Spec A, ⊤) a) • m)) = _
    rw [(kernelIdealSectionEquiv (Spec.map φ) ⊤).map_smul,
      (affineKernelSectionSemilinearEquiv φ).map_smulₛₗ]
    change specTopRingEquiv A ((specTopRingEquiv A).symm a) • _ = a • _
    rw [RingEquiv.apply_symm_apply]
    rfl

@[simp] theorem affineKernelGlobalLinearEquiv_apply
    (m : (kernelIdealSheaf (Spec.map φ)).val.obj (op ⊤)) :
    affineKernelGlobalLinearEquiv φ m =
      affineKernelSectionSemilinearEquiv φ (kernelIdealSectionEquiv (Spec.map φ) ⊤ m) := rfl

end AffineKernel

section OpenChart
variable {A B : CommRingCat.{0}} (φ : A ⟶ B)
  {X Y : Scheme.{0}} (j : X ⟶ Y) (i : Spec A ⟶ Y) (k : Spec B ⟶ X)
  [IsOpenImmersion i] [IsOpenImmersion k]
  (H : IsPullback (Spec.map φ) k i j)

local instance restrictedKernelModule (V : (Spec A).Opens) :
    Module A ((kernelIdealSheaf j).val.obj (op (i ''ᵁ V))) :=
  inferInstanceAs (Module A Γ((show Y.Modules from kernelIdealSheaf j).restrict i, V))

/-- The actual coordinate ideal on the entire affine chart, normalized in
the original affine ring through the cartesian square. -/
def normalOpenGlobalIdealEquiv :
    (kernelIdealSheaf j).val.obj (op (i ''ᵁ ⊤)) ≃ₗ[A] RingHom.ker φ.hom :=
  (((affineEvaluation A ⊤).mapIso
    (kernelIdealOpenBaseChangeIso j i k (Spec.map φ) H)).toLinearEquiv).trans
      (affineKernelGlobalLinearEquiv φ)

@[simp] theorem normalOpenGlobalIdealEquiv_symm_kernel (a : RingHom.ker φ.hom) :
    kernelIdealSectionEquiv j (i ''ᵁ ⊤)
        ((normalOpenGlobalIdealEquiv φ j i k H).symm a) =
      normalOpenIdealPullback j i k (Spec.map φ) H ⊤
        ((affineKernelSectionSemilinearEquiv φ).symm a) := rfl

include H in
/-- The actual ideal remains localizing on the affine chart because it is
canonically the kernel ideal of the actual affine map. -/
theorem normalOpenIdeal_isLocalizing :
    IsLocalizing (modulesSpecToSheaf.obj
      ((show Y.Modules from kernelIdealSheaf j).restrict i)) :=
  isLocalizing_of_iso (modulesSpecToSheaf.mapIso
    (kernelIdealOpenBaseChangeIso j i k (Spec.map φ) H).symm)
      (affineIdeal_isLocalizing φ)

/-- On any subopen of an actual affine chart, values on the transported
affine ideal generators determine an intrinsic normal section. -/
theorem normalOpen_subopen_ext_of_generators
    {ι : Type} (s : ι → RingHom.ker φ.hom)
    (hs : Submodule.span A (Set.range s) = ⊤)
    (U : (Spec A).Opens)
    (f g : (normalDirectImageSheaf j).val.obj (op (i ''ᵁ U)))
    (hfg : ∀ a,
      normalSectionEvaluate j (i ''ᵁ U) f
          (kernelSectionRestrict j (homOfLE (i.image_mono (show U ≤ ⊤ from le_top)))
            (normalOpenIdealPullback j i k (Spec.map φ) H ⊤
              ((affineKernelSectionSemilinearEquiv φ).symm (s a)))) =
        normalSectionEvaluate j (i ''ᵁ U) g
          (kernelSectionRestrict j (homOfLE (i.image_mono (show U ≤ ⊤ from le_top)))
            (normalOpenIdealPullback j i k (Spec.map φ) H ⊤
              ((affineKernelSectionSemilinearEquiv φ).symm (s a))))) : f = g := by
  let M : Y.Modules := kernelIdealSheaf j
  let N : Y.Modules := imageStructureModule j
  let e := normalOpenGlobalIdealEquiv φ j i k H
  let F := localLinearHomOpenImageMap i M N U f
  let G := localLinearHomOpenImageMap i M N U g
  have hspan : Submodule.span A (Set.range (fun a => e.symm (s a))) = ⊤ := by
    have heq := (Submodule.map_span e.symm.toLinearMap (Set.range s)).symm
    rw [hs, Submodule.map_top, e.symm.range] at heq
    simpa only [← Set.range_comp, LinearEquiv.coe_coe, Function.comp_def] using heq
  apply localLinearHomOpenImageMap_injective i M N U
  apply affineLocalLinearHom_ext_generators (M.restrict i) (N.restrict i)
    (normalOpenIdeal_isLocalizing φ j i k H) (fun a => e.symm (s a)) hspan U F G
  intro a
  have he : (kernelIdealSheaf j).val.map
      (homOfLE (i.image_mono (show U ≤ ⊤ from le_top))).op (e.symm (s a)) =
    (kernelIdealSectionEquiv j (i ''ᵁ U)).symm
      (kernelSectionRestrict j (homOfLE (i.image_mono (show U ≤ ⊤ from le_top)))
        (normalOpenIdealPullback j i k (Spec.map φ) H ⊤
          ((affineKernelSectionSemilinearEquiv φ).symm (s a)))) := by
    apply (kernelIdealSectionEquiv j (i ''ᵁ U)).injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [kernelIdealSectionEquiv_restrict, kernelSectionRestrict_coe]
    rw [normalOpenGlobalIdealEquiv_symm_kernel]
  exact (congrArg (localLinearHomEvaluate Y.sheaf M N (i ''ᵁ U) f) he).trans
    ((hfg a).trans
      (congrArg (localLinearHomEvaluate Y.sheaf M N (i ''ᵁ U) g) he.symm))

/-- The same generator criterion on an arbitrary ambient open contained
in the affine chart range; the open itself need not be affine. -/
theorem normalOpen_ext_of_generators
    {ι : Type} (s : ι → RingHom.ker φ.hom)
    (hs : Submodule.span A (Set.range s) = ⊤)
    (V : Y.Opens) (hV : V ≤ i.opensRange)
    (f g : (normalDirectImageSheaf j).val.obj (op V))
    (hfg : ∀ a,
      normalSectionEvaluate j V f
          (kernelSectionRestrict j
            (homOfLE (hV.trans i.image_top_eq_opensRange.ge))
            (normalOpenIdealPullback j i k (Spec.map φ) H ⊤
              ((affineKernelSectionSemilinearEquiv φ).symm (s a)))) =
        normalSectionEvaluate j V g
          (kernelSectionRestrict j
            (homOfLE (hV.trans i.image_top_eq_opensRange.ge))
            (normalOpenIdealPullback j i k (Spec.map φ) H ⊤
              ((affineKernelSectionSemilinearEquiv φ).symm (s a))))) : f = g := by
  obtain ⟨U, rfl⟩ : ∃ U : (Spec A).Opens, i ''ᵁ U = V :=
    ⟨i ⁻¹ᵁ V, (i.image_preimage_eq_opensRange_inf V).trans (inf_eq_right.mpr hV)⟩
  exact normalOpen_subopen_ext_of_generators φ j i k H s hs U f g hfg

#print axioms affineKernelGlobalLinearEquiv
#print axioms normalOpenGlobalIdealEquiv
#print axioms normalOpen_subopen_ext_of_generators
#print axioms normalOpen_ext_of_generators
end OpenChart
end CycleQ2GeometricIntrinsicNormal
end

end NormalSectionsNormalAffineSubopenExtPart

section NormalSectionsNormalChartEvaluationBridgePart

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricNormalCharts
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricIntrinsicNormal CycleQ2GeometricAffineChartSections
  CycleQ2GeometricProjectiveChartModules

section ChartSection
variable {A : CommRingCat.{0}} {Y : Scheme.{0}}
  (W : Y.Opens) (e : W.toScheme ≅ Spec A) (i : Spec A ⟶ Y)
  [IsOpenImmersion i] (hi : e.inv ≫ W.ι = i)
  (hTop : i ''ᵁ ⊤ = W)

include hi

/-- The normalized inverse of the affine chart's actual section map is the
same polynomial section used by the differential chart constructions. -/
theorem chartSection_inverseApp (a : A) :
    Y.presheaf.map (eqToHom hTop.symm).op
        ((i.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv a)) =
      chartSection e (Over.mk (𝟙 W)) a := by
  subst i
  exact ConcreteCategory.congr_hom
    ((congrArg (fun f => (Scheme.ΓSpecIso A).inv ≫ f)
      (chartImmersion_appIso_inv W e)).trans (chartSection_top e).symm) a

/-- The same comparison in the restriction direction, avoiding a choice
of affine generators or a scalar normalization. -/
theorem chartSection_restrict_imageTop (a : A) :
    Y.presheaf.map (homOfLE hTop.le).op (chartSection e (Over.mk (𝟙 W)) a) =
      (i.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv a) := by
  let E := (Y.presheaf.mapIso (eqToIso hTop).op).commRingCatIsoToRingEquiv
  have h : E.symm ((i.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv a)) =
      chartSection e (Over.mk (𝟙 W)) a :=
    chartSection_inverseApp W e i hi hTop a
  exact (congrArg E h).symm.trans (E.apply_symm_apply _)

end ChartSection

section NormalEvaluation
variable {A B : CommRingCat.{0}} (φ : A ⟶ B)
  {X Y : Scheme.{0}} (j : X ⟶ Y) (i : Spec A ⟶ Y) (k : Spec B ⟶ X)
  [IsOpenImmersion i] [IsOpenImmersion k]
  (H : IsPullback (Spec.map φ) k i j)

include H

/-- A normalized value in the affine quotient is the literal evaluation
of the normal section, read through the actual chart square. -/
theorem normalOpenIdealValue_evaluate_imageTop
    (f : (normalDirectImageSheaf j).val.obj (op i.opensRange))
    (a : RingHom.ker φ.hom) (b : A)
    (hf : normalOpenIdealValue φ j i k H f a = φ b) :
    normalSectionEvaluate j (i ''ᵁ ⊤)
        ((normalDirectImageSheaf j).val.map
          (homOfLE (i.image_le_opensRange ⊤)).op f)
        (normalOpenIdealPullback j i k (Spec.map φ) H ⊤
          ((affineKernelSectionSemilinearEquiv φ).symm a)) =
      j.app (i ''ᵁ ⊤) ((i.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv b)) := by
  let E := baseChangeStructureSectionIso j i k (Spec.map φ) H ⊤
  apply E.commRingCatIsoToRingEquiv.injective
  apply (specTopRingEquiv B).injective
  change normalOpenIdealValue φ j i k H f a = _
  have he := ConcreteCategory.congr_hom
    (baseChangeStructureSectionIso_app j i k (Spec.map φ) H ⊤)
      ((Scheme.ΓSpecIso A).inv b)
  have hn : specTopRingEquiv B
      (E.hom (j.app (i ''ᵁ ⊤) ((i.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv b)))) = φ b :=
    (congrArg (specTopRingEquiv B) he).trans
      ((affineSectionMap_normalization φ ((Scheme.ΓSpecIso A).inv b)).trans
        (congrArg φ ((specTopRingEquiv A).apply_symm_apply b)))
  exact hf.trans hn.symm

/-- Exact normal evaluation on the original equation section of the chart,
with its coefficient interpreted by the same actual chart section map. -/
theorem normalOpenIdealValue_evaluate_chart
    (e : i.opensRange.toScheme ≅ Spec A)
    (hi : e.inv ≫ i.opensRange.ι = i)
    (f : (normalDirectImageSheaf j).val.obj (op i.opensRange))
    (a : RingHom.ker φ.hom) (t : RingHom.ker (j.app i.opensRange).hom)
    (ht : (t : Γ(Y, i.opensRange)) = chartSection e (Over.mk (𝟙 i.opensRange)) a)
    (b : A) (hf : normalOpenIdealValue φ j i k H f a = φ b) :
    normalSectionEvaluate j i.opensRange f t =
      j.app i.opensRange (chartSection e (Over.mk (𝟙 i.opensRange)) b) := by
  let hTop := i.image_top_eq_opensRange
  let E := (imageStructureModule j).val.presheaf.mapIso (eqToIso hTop).op
  apply E.addCommGroupIsoToAddEquiv.injective
  change (imageStructureModule j).val.map (homOfLE hTop.le).op
      (normalSectionEvaluate j i.opensRange f t) =
    (imageStructureModule j).val.map (homOfLE hTop.le).op
      (j.app i.opensRange (chartSection e (Over.mk (𝟙 i.opensRange)) b))
  rw [← normalSectionEvaluate_restrict]
  have ht' : kernelSectionRestrict j (homOfLE hTop.le) t =
      normalOpenIdealPullback j i k (Spec.map φ) H ⊤
        ((affineKernelSectionSemilinearEquiv φ).symm a) := by
    apply Subtype.ext
    rw [kernelSectionRestrict_coe, ht,
      chartSection_restrict_imageTop i.opensRange e i hi hTop,
      normalOpenIdealPullback_coe]
    rfl
  rw [ht']
  apply (normalOpenIdealValue_evaluate_imageTop φ j i k H f a b hf).trans
  have hn := ConcreteCategory.congr_hom
    (j.naturality (homOfLE hTop.le).op) (chartSection e (Over.mk (𝟙 i.opensRange)) b)
  exact (congrArg (j.app (i ''ᵁ ⊤))
    (chartSection_restrict_imageTop i.opensRange e i hi hTop b).symm).trans hn

/-- Every ambient subopen of an actual affine chart is governed by the
same original defining equations, interpreted as actual chart sections. -/
theorem normalOpen_ext_of_chart_generators
    (e : i.opensRange.toScheme ≅ Spec A)
    (hi : e.inv ≫ i.opensRange.ι = i)
    {ι : Type} (s : ι → RingHom.ker φ.hom)
    (hs : Submodule.span A (Set.range s) = ⊤)
    (t : ι → RingHom.ker (j.app i.opensRange).hom)
    (ht : ∀ a, (t a : Γ(Y, i.opensRange)) =
      chartSection e (Over.mk (𝟙 i.opensRange)) (s a))
    (V : Y.Opens) (hV : V ≤ i.opensRange)
    (f g : (normalDirectImageSheaf j).val.obj (op V))
    (hfg : ∀ a, normalSectionEvaluate j V f
        (kernelSectionRestrict j (homOfLE hV) (t a)) =
      normalSectionEvaluate j V g
        (kernelSectionRestrict j (homOfLE hV) (t a))) : f = g := by
  apply normalOpen_ext_of_generators φ j i k H s hs V hV f g
  intro a
  let hTop := i.image_top_eq_opensRange
  have ha : kernelSectionRestrict j (homOfLE hV) (t a) =
      kernelSectionRestrict j (homOfLE (hV.trans hTop.ge))
        (normalOpenIdealPullback j i k (Spec.map φ) H ⊤
          ((affineKernelSectionSemilinearEquiv φ).symm (s a))) := by
    apply Subtype.ext
    rw [kernelSectionRestrict_coe, kernelSectionRestrict_coe,
      normalOpenIdealPullback_coe]
    have hnorm : Y.presheaf.map (homOfLE hTop.le).op (t a) =
        (i.appIso ⊤).inv ((affineKernelSectionSemilinearEquiv φ).symm (s a)) := by
      rw [ht a]
      exact chartSection_restrict_imageTop i.opensRange e i hi hTop (s a)
    exact (ConcreteCategory.congr_hom
      (Y.presheaf.map_comp (homOfLE hTop.le).op
        (homOfLE (hV.trans hTop.ge)).op) (t a)).trans
      (congrArg (Y.presheaf.map (homOfLE (hV.trans hTop.ge)).op) hnorm)
  exact (congrArg (normalSectionEvaluate j V f) ha).symm.trans
    ((hfg a).trans (congrArg (normalSectionEvaluate j V g) ha))

#print axioms chartSection_inverseApp
#print axioms chartSection_restrict_imageTop
#print axioms normalOpenIdealValue_evaluate_imageTop
#print axioms normalOpenIdealValue_evaluate_chart
#print axioms normalOpen_ext_of_chart_generators
end NormalEvaluation
end CycleQ2GeometricNormalCharts
end

end NormalSectionsNormalChartEvaluationBridgePart

section NormalSectionsNormalVectorSubopenPart

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricCoordinateNormalSections
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry MvPolynomial
open CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSurfaceCurveCharts
open CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2GeometricLiteralSurface
open CycleQ2GeometricSurfaceJacobianCharts CycleQ2GeometricSurfaceOverlap
open CycleQ2GeometricAffineChartSections CycleQ2GeometricDifferentialChartTransport
open CycleQ2GeometricNormalCharts CycleQ2GeometricAffineCurveCharts
open CycleQ2GeometricSeedNormalIdeals
open CycleQ2CartierProjectiveCover

/-- A fixed polynomial on the actual first coordinate open. -/
def firstCoordinatePolynomial (r θ : ℂ) (p : SurfacePoly) :
    Γ(projectiveSurface r θ,coordinatePatch r θ 1) :=
  (firstSectionsEquiv r θ).symm (surfaceMap (firstEquations r θ) p)

def secondCoordinatePolynomial (r θ : ℂ) (p : SurfacePoly) :
    Γ(projectiveSurface r θ,coordinatePatch r θ 2) :=
  (secondSectionsEquiv r θ).symm (surfaceMap (secondEquations r θ) p)

theorem firstCoordinatePolynomial_mem_kernel_iff (r θ : ℂ) (p : SurfacePoly) :
    firstCoordinatePolynomial r θ p ∈
      RingHom.ker ((curveToSurface r θ).app (coordinatePatch r θ 1)).hom ↔
        polynomialToCurve (firstQuadric r) (firstCubic θ) p = 0 := by
  have hk := coordinateSectionMap_ker r θ (1 : Fin 4)
  change RingHom.ker (coordinateSectionMap r θ 1) =
    RingHom.ker ((curveToSurface r θ).app (coordinatePatch r θ 1)).hom at hk
  rw [← hk]
  change coordinateSectionMap r θ 1 (firstCoordinatePolynomial r θ p) = 0 ↔ _
  rw [← (CycleQ2GeometricAffineProjectiveCharts.firstSectionsEquiv r θ).map_eq_zero_iff,
    firstSectionsEquiv_curveMap]
  simp only [firstCoordinatePolynomial,RingEquiv.apply_symm_apply]
  rfl

theorem secondCoordinatePolynomial_mem_kernel_iff (r θ : ℂ) (p : SurfacePoly) :
    secondCoordinatePolynomial r θ p ∈
      RingHom.ker ((curveToSurface r θ).app (coordinatePatch r θ 2)).hom ↔
        polynomialToCurve (secondQuadric r) (secondCubic θ) p = 0 := by
  have hk := coordinateSectionMap_ker r θ (2 : Fin 4)
  change RingHom.ker (coordinateSectionMap r θ 2) =
    RingHom.ker ((curveToSurface r θ).app (coordinatePatch r θ 2)).hom at hk
  rw [← hk]
  change coordinateSectionMap r θ 2 (secondCoordinatePolynomial r θ p) = 0 ↔ _
  rw [← (CycleQ2GeometricAffineProjectiveCharts.secondSectionsEquiv r θ).map_eq_zero_iff,
    secondSectionsEquiv_curveMap]
  simp only [secondCoordinatePolynomial,RingEquiv.apply_symm_apply]
  rfl

/-- The original two equations, as sections of the actual coordinate
kernel ideal. They are fixed before choosing a Jacobian minor. -/
def firstCoordinateIdealEquation (r θ : ℂ) (a : Fin 2) :
    RingHom.ker ((curveToSurface r θ).app (coordinatePatch r θ 1)).hom :=
  ⟨firstCoordinatePolynomial r θ (normalPolynomial (firstQuadric r) a), by
    apply (firstCoordinatePolynomial_mem_kernel_iff r θ _).mpr
    fin_cases a
    · exact polynomialToCurve_quadric _ _
    · exact polynomialToCurve_normal _ _⟩

def secondCoordinateIdealEquation (r θ : ℂ) (a : Fin 2) :
    RingHom.ker ((curveToSurface r θ).app (coordinatePatch r θ 2)).hom :=
  ⟨secondCoordinatePolynomial r θ (normalPolynomial (secondQuadric r) a), by
    apply (secondCoordinatePolynomial_mem_kernel_iff r θ _).mpr
    fin_cases a
    · exact polynomialToCurve_quadric _ _
    · exact polynomialToCurve_normal _ _⟩

theorem firstNormal_polynomial_restriction (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : Over (firstNormalOpen r θ i j)) (p : SurfacePoly) :
    chartSection (firstNormalChart r θ i j) V
      (algebraMap SurfacePoly (FirstNormalRing r θ i j) p) =
    (projectiveSurface r θ).presheaf.map
      (V.hom ≫ homOfLE (firstNormalOpen_le r θ i j)).op
        (firstCoordinatePolynomial r θ p) := by
  change chartSection (firstNormalChart r θ i j) V
    (algebraMap (SurfaceChartRing (firstEquations r θ)) (Localization.Away (firstJacobian r θ i j))
      (surfaceMap (firstEquations r θ) p)) = _
  rw [firstNormal_chartSection,first_chartSection_subopen]
  rfl

theorem secondNormal_polynomial_restriction (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : Over (secondNormalOpen r θ i j)) (p : SurfacePoly) :
    chartSection (secondNormalChart r θ i j) V
      (algebraMap SurfacePoly (SecondNormalRing r θ i j) p) =
    (projectiveSurface r θ).presheaf.map
      (V.hom ≫ homOfLE (secondNormalOpen_le r θ i j)).op
        (secondCoordinatePolynomial r θ p) := by
  change chartSection (secondNormalChart r θ i j) V
    (algebraMap (SurfaceChartRing (secondEquations r θ)) (Localization.Away (secondJacobian r θ i j))
      (surfaceMap (secondEquations r θ) p)) = _
  rw [secondNormal_chartSection,second_chartSection_subopen]
  rfl

/-- The local ideal equation used to evaluate the intrinsic normal
section is the restriction of this same coordinate ideal equation. -/
theorem firstNormal_idealEquation_restriction (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : Over (firstNormalOpen r θ i j)) (a : Fin 2) :
    chartSection (firstNormalChart r θ i j) V (firstNormalIdealEquation r θ i j a) =
    (projectiveSurface r θ).presheaf.map
      (V.hom ≫ homOfLE (firstNormalOpen_le r θ i j)).op
        (firstCoordinateIdealEquation r θ a) :=
  firstNormal_polynomial_restriction r θ i j V (normalPolynomial (firstQuadric r) a)

theorem secondNormal_idealEquation_restriction (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : Over (secondNormalOpen r θ i j)) (a : Fin 2) :
    chartSection (secondNormalChart r θ i j) V (secondNormalIdealEquation r θ i j a) =
    (projectiveSurface r θ).presheaf.map
      (V.hom ≫ homOfLE (secondNormalOpen_le r θ i j)).op
        (secondCoordinateIdealEquation r θ a) :=
  secondNormal_polynomial_restriction r θ i j V (normalPolynomial (secondQuadric r) a)

#print axioms firstCoordinatePolynomial_mem_kernel_iff
#print axioms secondCoordinatePolynomial_mem_kernel_iff
#print axioms firstCoordinateIdealEquation
#print axioms secondCoordinateIdealEquation
#print axioms firstNormal_polynomial_restriction
#print axioms secondNormal_polynomial_restriction
#print axioms firstNormal_idealEquation_restriction
#print axioms secondNormal_idealEquation_restriction

end CycleQ2GeometricCoordinateNormalSections
end

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricIntrinsicNormal
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

variable {X Y : Scheme.{0}} (j : X ⟶ Y)

theorem kernelSectionRestrict_comp {U V W : Y.Opens} (h : V ⟶ U) (k : W ⟶ V)
    (a : RingHom.ker (j.app U).hom) :
    kernelSectionRestrict j k (kernelSectionRestrict j h a) =
      kernelSectionRestrict j (k ≫ h) a := by
  apply Subtype.ext
  rw [kernelSectionRestrict_coe, kernelSectionRestrict_coe, kernelSectionRestrict_coe]
  exact (ConcreteCategory.congr_hom (Y.presheaf.map_comp h.op k.op) a).symm

/-- A literal equation evaluation remains that same coefficient after
restriction to every subopen. -/
theorem normalSectionEvaluate_restrict_of_value {U V : Y.Opens} (h : V ⟶ U)
    (f : (normalDirectImageSheaf j).val.obj (op U))
    (a : RingHom.ker (j.app U).hom) (b : Γ(Y, U))
    (hf : normalSectionEvaluate j U f a = j.app U b) :
    normalSectionEvaluate j V ((normalDirectImageSheaf j).val.map h.op f)
        (kernelSectionRestrict j h a) = j.app V (Y.presheaf.map h.op b) := by
  rw [normalSectionEvaluate_restrict, hf]
  exact (ConcreteCategory.congr_hom (j.naturality h.op) b).symm

end CycleQ2GeometricIntrinsicNormal

namespace CycleQ2GeometricNormalCharts
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricIntrinsicNormal CycleQ2GeometricAffineChartSections
  CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricAffineCurveCharts

section Symbolic
variable (q h : AffinePoly) (g₁ g₂ k : SurfacePoly) (n : Fin 2) (t : Fin 3)
  {X Y : Scheme.{0}} (j : X ⟶ Y)
  (iS : Spec (CommRingCat.of (NormalSurfacePatch q h g₁ g₂ k n t)) ⟶ Y)
  (iC : Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k n t)) ⟶ X)
  [IsOpenImmersion iS] [IsOpenImmersion iC]
  (H : IsPullback (Spec.map (CommRingCat.ofHom (normalChartMap q h g₁ g₂ k n t).toRingHom))
    iC iS j)

theorem normalChartIdealEquation_span :
    Submodule.span (NormalSurfacePatch q h g₁ g₂ k n t)
      (Set.range (normalChartIdealEquation q h g₁ g₂ k n t)) = ⊤ :=
  (Submodule.span_range_subtype_eq_top_iff
    (RingHom.ker (normalChartMap q h g₁ g₂ k n t).toRingHom)
    (normalEquation_mem q h g₁ g₂ k n t)).mpr (normalEquations_span q h g₁ g₂ k n t)

/-- The normalized normal vector evaluates the actual two chart equations
to the actual polynomial coefficients G₂ and −G₁. -/
theorem normalChartVectorSection_evaluate_chart
    (e : iS.opensRange.toScheme ≅ Spec (CommRingCat.of (NormalSurfacePatch q h g₁ g₂ k n t)))
    (hi : e.inv ≫ iS.opensRange.ι = iS)
    (u : Fin 2 → RingHom.ker (j.app iS.opensRange).hom)
    (hu : ∀ a, (u a : Γ(Y, iS.opensRange)) =
      chartSection e (Over.mk (𝟙 iS.opensRange)) (normalChartIdealEquation q h g₁ g₂ k n t a))
    (a : Fin 2) :
    normalSectionEvaluate j iS.opensRange
        (normalChartVectorSection q h g₁ g₂ k n t j iS iC H) (u a) =
      j.app iS.opensRange (chartSection e (Over.mk (𝟙 iS.opensRange))
        (algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k n t) (![g₂, -g₁] a))) := by
  apply normalOpenIdealValue_evaluate_chart
    (CommRingCat.ofHom (normalChartMap q h g₁ g₂ k n t).toRingHom)
    j iS iC H e hi _ (normalChartIdealEquation q h g₁ g₂ k n t a) (u a) (hu a)
  apply (normalChartVectorSection_equation q h g₁ g₂ k n t j iS iC H a).trans
  change ![normalCoefficientMap q h g₁ g₂ k n t g₂,
      -normalCoefficientMap q h g₁ g₂ k n t g₁] a =
    algebraMap (NormalSurfacePatch q h g₁ g₂ k n t) (NormalCurvePatch q h g₁ g₂ k n t)
      (algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k n t) (![g₂, -g₁] a))
  rw [normalAlgebraMap_polynomial]
  fin_cases a
  · rfl
  · exact (map_neg (normalCoefficientMap q h g₁ g₂ k n t) g₁).symm

/-- The same intrinsic vector equation with any proved presentation of
the coefficient sections; polynomial chart comparison is composed before
specializing the literal surface coefficients. -/
theorem normalChartVectorSection_evaluate_coordinate
    (e : iS.opensRange.toScheme ≅ Spec (CommRingCat.of (NormalSurfacePatch q h g₁ g₂ k n t)))
    (hi : e.inv ≫ iS.opensRange.ι = iS)
    (u : Fin 2 → RingHom.ker (j.app iS.opensRange).hom)
    (hu : ∀ a, (u a : Γ(Y, iS.opensRange)) =
      chartSection e (Over.mk (𝟙 iS.opensRange)) (normalChartIdealEquation q h g₁ g₂ k n t a))
    (v : Fin 2 → Γ(Y, iS.opensRange))
    (hv : ∀ a, chartSection e (Over.mk (𝟙 iS.opensRange))
      (algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k n t) (![g₂, -g₁] a)) = v a)
    (a : Fin 2) :
    normalSectionEvaluate j iS.opensRange
        (normalChartVectorSection q h g₁ g₂ k n t j iS iC H) (u a) =
      j.app iS.opensRange (v a) :=
  (normalChartVectorSection_evaluate_chart q h g₁ g₂ k n t j iS iC H e hi u hu a).trans
    (congrArg (j.app iS.opensRange) (hv a))

/-- A presentation-independent wrapper keeps the actual named open and
normal section in the conclusion, while its identification with the
normalized vector is proved before any equation is evaluated. -/
theorem normalChartSection_evaluate_coordinate
    (U : Y.Opens) (hU : U = iS.opensRange)
    (e : U.toScheme ≅ Spec (CommRingCat.of (NormalSurfacePatch q h g₁ g₂ k n t)))
    (hi : e.inv ≫ U.ι = iS)
    (u : Fin 2 → RingHom.ker (j.app U).hom)
    (hu : ∀ a, (u a : Γ(Y, U)) =
      chartSection e (Over.mk (𝟙 U)) (normalChartIdealEquation q h g₁ g₂ k n t a))
    (v : Fin 2 → Γ(Y, U))
    (hv : ∀ a, chartSection e (Over.mk (𝟙 U))
      (algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k n t) (![g₂, -g₁] a)) = v a)
    (f : (normalDirectImageSheaf j).val.obj (op U))
    (hf : (hU ▸ f) = normalChartVectorSection q h g₁ g₂ k n t j iS iC H)
    (a : Fin 2) :
    normalSectionEvaluate j U f (u a) = j.app U (v a) := by
  subst U
  change f = normalChartVectorSection q h g₁ g₂ k n t j iS iC H at hf
  exact (congrArg (fun z => normalSectionEvaluate j iS.opensRange z (u a)) hf).trans
    (normalChartVectorSection_evaluate_coordinate q h g₁ g₂ k n t j iS iC H
      e hi u hu v hv a)

include H in
/-- The two original equations determine a normal section on every
subopen of the actual normal chart. -/
theorem normalChart_subopen_ext
    (e : iS.opensRange.toScheme ≅ Spec (CommRingCat.of (NormalSurfacePatch q h g₁ g₂ k n t)))
    (hi : e.inv ≫ iS.opensRange.ι = iS)
    (u : Fin 2 → RingHom.ker (j.app iS.opensRange).hom)
    (hu : ∀ a, (u a : Γ(Y, iS.opensRange)) =
      chartSection e (Over.mk (𝟙 iS.opensRange)) (normalChartIdealEquation q h g₁ g₂ k n t a))
    (V : Y.Opens) (hV : V ≤ iS.opensRange)
    (f g : (normalDirectImageSheaf j).val.obj (op V))
    (hfg : ∀ a, normalSectionEvaluate j V f
        (kernelSectionRestrict j (homOfLE hV) (u a)) =
      normalSectionEvaluate j V g
        (kernelSectionRestrict j (homOfLE hV) (u a))) : f = g :=
  normalOpen_ext_of_chart_generators
    (CommRingCat.ofHom (normalChartMap q h g₁ g₂ k n t).toRingHom)
    j iS iC H e hi (normalChartIdealEquation q h g₁ g₂ k n t)
    (normalChartIdealEquation_span q h g₁ g₂ k n t) u hu V hV f g hfg

end Symbolic

open CycleQ2SeedTrace CycleQ2SeedCechTheta CycleQ2NormalConnecting

open CycleQ2GeometricCoordinateNormalSections CycleQ2GeometricSurfaceJacobianCharts
  CycleQ2GeometricSurfacePrincipalCurveCharts CycleQ2GeometricSurfaceDehomogenizedCharts
  CycleQ2GeometricSurfaceOverlap CycleQ2GeometricLiteralSurface
  CycleQ2GeometricSeedNormalIdeals

/-- In each first-coordinate normal chart, the equation evaluated is the
restriction of the same fixed coordinate equation, independently of the minor. -/
theorem firstNormal_actualEquation_chartSection (r θ : ℂ) (i : Fin 2) (j : Fin 3) (a : Fin 2) :
    (kernelSectionRestrict (curveToSurface r θ)
      (homOfLE (firstNormalOpen_le r θ i j)) (firstCoordinateIdealEquation r θ a) :
        Γ(surface r θ, firstNormalOpen r θ i j)) =
      chartSection (firstNormalChart r θ i j) (Over.mk (𝟙 _))
        (firstNormalIdealEquation r θ i j a) := by
  exact (kernelSectionRestrict_coe (curveToSurface r θ)
    (homOfLE (firstNormalOpen_le r θ i j)) (firstCoordinateIdealEquation r θ a)).trans
      (firstNormal_idealEquation_restriction r θ i j (Over.mk (𝟙 _)) a).symm

/-- The first intrinsic normal frame has the literal coefficient values
on the actual coordinate equations in the actual surface section ring. -/
theorem firstNormalVectorSection_actualEquation (r θ : ℂ) (i : Fin 2) (j : Fin 3) (a : Fin 2) :
    normalSectionEvaluate (curveToSurface r θ) (firstNormalOpen r θ i j)
        (firstNormalVectorSection r θ i j)
        (kernelSectionRestrict (curveToSurface r θ)
          (homOfLE (firstNormalOpen_le r θ i j)) (firstCoordinateIdealEquation r θ a)) =
      (curveToSurface r θ).app (firstNormalOpen r θ i j)
        ((surface r θ).presheaf.map (homOfLE (firstNormalOpen_le r θ i j)).op
          (firstCoordinatePolynomial r θ
            (![firstSurfaceDehomogenize originalG2,
              -firstSurfaceDehomogenize (originalG1 r)] a))) := by
  exact normalChartSection_evaluate_coordinate
    (firstQuadric r) (firstCubic θ)
    (firstSurfaceDehomogenize (originalG1 r)) (firstSurfaceDehomogenize originalG2)
    (firstSurfaceDehomogenize (thetaK θ)) i j
    (curveToSurface r θ) (firstNormalSurfaceImmersion r θ i j)
    (firstNormalCurveImmersion r θ i j) (firstNormalCurve_isPullback r θ i j)
    (firstNormalOpen r θ i j) rfl (firstNormalChart r θ i j)
    (principalChart_inv_ι (firstAffineChart r θ) (firstJacobian r θ i j))
    (fun a => kernelSectionRestrict (curveToSurface r θ)
      (homOfLE (firstNormalOpen_le r θ i j)) (firstCoordinateIdealEquation r θ a))
    (firstNormal_actualEquation_chartSection r θ i j)
    (fun a => (surface r θ).presheaf.map (homOfLE (firstNormalOpen_le r θ i j)).op
      (firstCoordinatePolynomial r θ
        (![firstSurfaceDehomogenize originalG2, -firstSurfaceDehomogenize (originalG1 r)] a)))
    (fun a => firstNormal_polynomial_restriction r θ i j (Over.mk (𝟙 _))
      (![firstSurfaceDehomogenize originalG2, -firstSurfaceDehomogenize (originalG1 r)] a))
    (firstNormalVectorSection r θ i j) rfl a

#print axioms kernelSectionRestrict_comp
#print axioms normalSectionEvaluate_restrict_of_value
#print axioms normalChartVectorSection_evaluate_chart
#print axioms normalChart_subopen_ext
#print axioms firstNormalVectorSection_actualEquation
end CycleQ2GeometricNormalCharts
end

end NormalSectionsNormalVectorSubopenPart

section NormalSectionsNormalCoordinateGluingPreludePart

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricIntrinsicNormal
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

/-- Literal normal evaluation can be checked on any cover of the curve
preimage; a cover of the entire ambient open is not required. -/
theorem normalSectionEvaluate_eq_of_preimage_cover
    {X Y : Scheme.{0}} (j : X ⟶ Y) {ι : Type}
    (U : Y.Opens) (V : ι → Y.Opens) (hVU : ∀ t, V t ≤ U)
    (hcover : j ⁻¹ᵁ U ≤ ⨆ t, j ⁻¹ᵁ V t)
    (f : (normalDirectImageSheaf j).val.obj (op U))
    (a : RingHom.ker (j.app U).hom) (b : Γ(Y, U))
    (hs : ∀ t,
      normalSectionEvaluate j (V t)
          ((normalDirectImageSheaf j).val.map (homOfLE (hVU t)).op f)
          (kernelSectionRestrict j (homOfLE (hVU t)) a) =
        j.app (V t) (Y.presheaf.map (homOfLE (hVU t)).op b)) :
    normalSectionEvaluate j U f a = j.app U b := by
  apply TopCat.Presheaf.IsSheaf.section_ext X.sheaf.property
  intro x hx
  obtain ⟨t, ht⟩ := Opens.mem_iSup.mp (hcover hx)
  refine ⟨j ⁻¹ᵁ V t, j.preimage_mono (hVU t), ht, ?_⟩
  exact (normalSectionEvaluate_restrict j (homOfLE (hVU t)) f a).symm.trans
    ((hs t).trans (ConcreteCategory.congr_hom
      (j.naturality (homOfLE (hVU t)).op) b))

end CycleQ2GeometricIntrinsicNormal
end

noncomputable section
namespace CycleQ2GeometricNormalCharts
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricIntrinsicNormal CycleQ2GeometricAffineChartSections
  CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricAffineCurveCharts
  CycleQ2GeometricCoordinateNormalSections CycleQ2GeometricSurfaceJacobianCharts
  CycleQ2GeometricSurfacePrincipalCurveCharts CycleQ2GeometricSurfaceDehomogenizedCharts
  CycleQ2GeometricSurfaceOverlap CycleQ2GeometricLiteralSurface
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricSurfaceNormalCover
  CycleQ2GeometricSurfaceCurveCharts CycleQ2GeometricProjectiveCurve
  CycleQ2CartierProjectiveCover CycleQ2SeedTrace CycleQ2SeedCechTheta CycleQ2NormalConnecting

/-- In each second-coordinate normal chart, the equation evaluated is the
restriction of the same fixed coordinate equation, independently of the minor. -/
theorem secondNormal_actualEquation_chartSection (r θ : ℂ) (i : Fin 2) (j : Fin 3) (a : Fin 2) :
    (kernelSectionRestrict (curveToSurface r θ)
      (homOfLE (secondNormalOpen_le r θ i j)) (secondCoordinateIdealEquation r θ a) :
        Γ(surface r θ, secondNormalOpen r θ i j)) =
      chartSection (secondNormalChart r θ i j) (Over.mk (𝟙 _))
        (secondNormalIdealEquation r θ i j a) := by
  exact (kernelSectionRestrict_coe (curveToSurface r θ)
    (homOfLE (secondNormalOpen_le r θ i j)) (secondCoordinateIdealEquation r θ a)).trans
      (secondNormal_idealEquation_restriction r θ i j (Over.mk (𝟙 _)) a).symm

/-- The second intrinsic normal frame has the literal coefficient values
on the actual coordinate equations in the actual surface section ring. -/
theorem secondNormalVectorSection_actualEquation (r θ : ℂ) (i : Fin 2) (j : Fin 3) (a : Fin 2) :
    normalSectionEvaluate (curveToSurface r θ) (secondNormalOpen r θ i j)
        (secondNormalVectorSection r θ i j)
        (kernelSectionRestrict (curveToSurface r θ)
          (homOfLE (secondNormalOpen_le r θ i j)) (secondCoordinateIdealEquation r θ a)) =
      (curveToSurface r θ).app (secondNormalOpen r θ i j)
        ((surface r θ).presheaf.map (homOfLE (secondNormalOpen_le r θ i j)).op
          (secondCoordinatePolynomial r θ
            (![secondSurfaceDehomogenize originalG2,
              -secondSurfaceDehomogenize (originalG1 r)] a))) := by
  exact normalChartSection_evaluate_coordinate
    (secondQuadric r) (secondCubic θ)
    (secondSurfaceDehomogenize (originalG1 r)) (secondSurfaceDehomogenize originalG2)
    (secondSurfaceDehomogenize (thetaK θ)) i j
    (curveToSurface r θ) (secondNormalSurfaceImmersion r θ i j)
    (secondNormalCurveImmersion r θ i j) (secondNormalCurve_isPullback r θ i j)
    (secondNormalOpen r θ i j) rfl (secondNormalChart r θ i j)
    (principalChart_inv_ι (secondAffineChart r θ) (secondJacobian r θ i j))
    (fun a => kernelSectionRestrict (curveToSurface r θ)
      (homOfLE (secondNormalOpen_le r θ i j)) (secondCoordinateIdealEquation r θ a))
    (secondNormal_actualEquation_chartSection r θ i j)
    (fun a => (surface r θ).presheaf.map (homOfLE (secondNormalOpen_le r θ i j)).op
      (secondCoordinatePolynomial r θ
        (![secondSurfaceDehomogenize originalG2, -secondSurfaceDehomogenize (originalG1 r)] a)))
    (fun a => secondNormal_polynomial_restriction r θ i j (Over.mk (𝟙 _))
      (![secondSurfaceDehomogenize originalG2, -secondSurfaceDehomogenize (originalG1 r)] a))
    (secondNormalVectorSection r θ i j) rfl a


#print axioms CycleQ2GeometricIntrinsicNormal.normalSectionEvaluate_eq_of_preimage_cover
#print axioms secondNormalVectorSection_actualEquation
end CycleQ2GeometricNormalCharts
end

end NormalSectionsNormalCoordinateGluingPreludePart

section NormalSectionsNormalMinorRestrictionPart

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricIntrinsicNormal
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

/-- Coordinate-normalized evaluation restricts through any intermediate
open without changing its fixed equation or coefficient. -/
theorem normalSectionEvaluate_restrict_coordinate
    {X Y : Scheme.{0}} (j : X ⟶ Y) {W U V : Y.Opens}
    (h : U ⟶ W) (k : V ⟶ U) (l : V ⟶ W) (hl : l = k ≫ h)
    (f : (normalDirectImageSheaf j).val.obj (op U))
    (a : RingHom.ker (j.app W).hom) (b : Γ(Y, W))
    (hf : normalSectionEvaluate j U f (kernelSectionRestrict j h a) =
      j.app U (Y.presheaf.map h.op b)) :
    normalSectionEvaluate j V ((normalDirectImageSheaf j).val.map k.op f)
        (kernelSectionRestrict j l a) =
      j.app V (Y.presheaf.map l.op b) := by
  subst l
  have hv := normalSectionEvaluate_restrict_of_value j k f
    (kernelSectionRestrict j h a) (Y.presheaf.map h.op b) hf
  have he := kernelSectionRestrict_comp j h k a
  have hb := (ConcreteCategory.congr_hom (Y.presheaf.map_comp h.op k.op) b).symm
  exact (congrArg (normalSectionEvaluate j V
    ((normalDirectImageSheaf j).val.map k.op f)) he).symm.trans
      (hv.trans (congrArg (j.app V) hb))

end CycleQ2GeometricIntrinsicNormal
end

noncomputable section
namespace CycleQ2GeometricNormalCharts
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricIntrinsicNormal CycleQ2GeometricAffineChartSections
  CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricAffineCurveCharts
  CycleQ2GeometricCoordinateNormalSections CycleQ2GeometricSurfaceJacobianCharts
  CycleQ2GeometricSurfacePrincipalCurveCharts CycleQ2GeometricSurfaceDehomogenizedCharts
  CycleQ2GeometricSurfaceOverlap CycleQ2GeometricLiteralSurface
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricSurfaceNormalCover
  CycleQ2GeometricSurfaceCurveCharts CycleQ2GeometricProjectiveCurve
  CycleQ2CartierProjectiveCover CycleQ2SeedTrace CycleQ2SeedCechTheta CycleQ2NormalConnecting

/-- On every subopen, the first local frame evaluates the fixed coordinate
equations to the restrictions of the fixed coordinate coefficient sections. -/
theorem firstNormalVectorSection_restrict_actualEquation (r θ : ℂ)
    (i : Fin 2) (j : Fin 3) (V : (surface r θ).Opens)
    (hV : V ≤ firstNormalOpen r θ i j) (a : Fin 2) :
    normalSectionEvaluate (curveToSurface r θ) V
        ((normalDirectImageSheaf (curveToSurface r θ)).val.map (homOfLE hV).op
          (firstNormalVectorSection r θ i j))
        (kernelSectionRestrict (curveToSurface r θ)
          (homOfLE (hV.trans (firstNormalOpen_le r θ i j)))
          (firstCoordinateIdealEquation r θ a)) =
      (curveToSurface r θ).app V
        ((surface r θ).presheaf.map
          (homOfLE (hV.trans (firstNormalOpen_le r θ i j))).op
          (firstCoordinatePolynomial r θ
            (![firstSurfaceDehomogenize originalG2,
              -firstSurfaceDehomogenize (originalG1 r)] a))) := by
  exact normalSectionEvaluate_restrict_coordinate (curveToSurface r θ)
    (homOfLE (firstNormalOpen_le r θ i j)) (homOfLE hV)
    (homOfLE (hV.trans (firstNormalOpen_le r θ i j))) rfl
    (firstNormalVectorSection r θ i j) (firstCoordinateIdealEquation r θ a)
    (firstCoordinatePolynomial r θ
      (![firstSurfaceDehomogenize originalG2,
        -firstSurfaceDehomogenize (originalG1 r)] a))
    (firstNormalVectorSection_actualEquation r θ i j a)

/-- On every subopen, the second local frame evaluates the fixed coordinate
equations to the restrictions of the fixed coordinate coefficient sections. -/
theorem secondNormalVectorSection_restrict_actualEquation (r θ : ℂ)
    (i : Fin 2) (j : Fin 3) (V : (surface r θ).Opens)
    (hV : V ≤ secondNormalOpen r θ i j) (a : Fin 2) :
    normalSectionEvaluate (curveToSurface r θ) V
        ((normalDirectImageSheaf (curveToSurface r θ)).val.map (homOfLE hV).op
          (secondNormalVectorSection r θ i j))
        (kernelSectionRestrict (curveToSurface r θ)
          (homOfLE (hV.trans (secondNormalOpen_le r θ i j)))
          (secondCoordinateIdealEquation r θ a)) =
      (curveToSurface r θ).app V
        ((surface r θ).presheaf.map
          (homOfLE (hV.trans (secondNormalOpen_le r θ i j))).op
          (secondCoordinatePolynomial r θ
            (![secondSurfaceDehomogenize originalG2,
              -secondSurfaceDehomogenize (originalG1 r)] a))) := by
  exact normalSectionEvaluate_restrict_coordinate (curveToSurface r θ)
    (homOfLE (secondNormalOpen_le r θ i j)) (homOfLE hV)
    (homOfLE (hV.trans (secondNormalOpen_le r θ i j))) rfl
    (secondNormalVectorSection r θ i j) (secondCoordinateIdealEquation r θ a)
    (secondCoordinatePolynomial r θ
      (![secondSurfaceDehomogenize originalG2,
        -secondSurfaceDehomogenize (originalG1 r)] a))
    (secondNormalVectorSection_actualEquation r θ i j a)

#print axioms normalSectionEvaluate_restrict_coordinate
#print axioms firstNormalVectorSection_restrict_actualEquation
#print axioms secondNormalVectorSection_restrict_actualEquation
end CycleQ2GeometricNormalCharts
end

end NormalSectionsNormalMinorRestrictionPart

section NormalSectionsNormalTypedRestrictionPart

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricIntrinsicNormal
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

/-- Restriction of intrinsic normal sections with its target section type
exposed before any concrete affine normal frame is elaborated. -/
def normalSectionRestrict {X Y : Scheme.{0}} (j : X ⟶ Y)
    {U V : Y.Opens} (h : V ≤ U)
    (f : (normalDirectImageSheaf j).val.obj (op U)) :
    (normalDirectImageSheaf j).val.obj (op V) :=
  (normalDirectImageSheaf j).val.map (homOfLE h).op f

end CycleQ2GeometricIntrinsicNormal
end

noncomputable section
namespace CycleQ2GeometricIntrinsicNormal
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

/-- The restriction formula with an explicitly named restricted section.
The restriction identity is proved before its evaluation is specialized. -/
theorem normalSectionEvaluate_restrict_coordinate_as
    {X Y : Scheme.{0}} (j : X ⟶ Y) {W U V : Y.Opens}
    (h : U ⟶ W) (k : V ⟶ U) (l : V ⟶ W) (hl : l = k ≫ h)
    (f : (normalDirectImageSheaf j).val.obj (op U))
    (g : (normalDirectImageSheaf j).val.obj (op V))
    (hg : g = (normalDirectImageSheaf j).val.map k.op f)
    (a : RingHom.ker (j.app W).hom) (b : Γ(Y, W))
    (hf : normalSectionEvaluate j U f (kernelSectionRestrict j h a) =
      j.app U (Y.presheaf.map h.op b)) :
    normalSectionEvaluate j V g (kernelSectionRestrict j l a) =
      j.app V (Y.presheaf.map l.op b) :=
  (congrArg (fun z => normalSectionEvaluate j V z (kernelSectionRestrict j l a)) hg).trans
    (normalSectionEvaluate_restrict_coordinate j h k l hl f a b hf)

end CycleQ2GeometricIntrinsicNormal
end

noncomputable section
namespace CycleQ2GeometricNormalCharts
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricIntrinsicNormal CycleQ2GeometricAffineChartSections
  CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricAffineCurveCharts
  CycleQ2GeometricCoordinateNormalSections CycleQ2GeometricSurfaceJacobianCharts
  CycleQ2GeometricSurfacePrincipalCurveCharts CycleQ2GeometricSurfaceDehomogenizedCharts
  CycleQ2GeometricSurfaceOverlap CycleQ2GeometricLiteralSurface
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricSurfaceNormalCover
  CycleQ2GeometricSurfaceCurveCharts CycleQ2GeometricProjectiveCurve
  CycleQ2CartierProjectiveCover CycleQ2SeedTrace CycleQ2SeedCechTheta CycleQ2NormalConnecting

/-- On every subopen, the first local frame evaluates the fixed coordinate
equations to the restrictions of the fixed coordinate coefficient sections. -/
theorem firstNormalVectorSection_restrict_actualEquation_typed (r θ : ℂ)
    (i : Fin 2) (j : Fin 3) (V : (surface r θ).Opens)
    (hV : V ≤ firstNormalOpen r θ i j) (a : Fin 2) :
    normalSectionEvaluate (curveToSurface r θ) V
        (normalSectionRestrict (curveToSurface r θ) hV
          (firstNormalVectorSection r θ i j))
        (kernelSectionRestrict (curveToSurface r θ)
          (homOfLE (hV.trans (firstNormalOpen_le r θ i j)))
          (firstCoordinateIdealEquation r θ a)) =
      (curveToSurface r θ).app V
        ((surface r θ).presheaf.map
          (homOfLE (hV.trans (firstNormalOpen_le r θ i j))).op
          (firstCoordinatePolynomial r θ
            (![firstSurfaceDehomogenize originalG2,
              -firstSurfaceDehomogenize (originalG1 r)] a))) := by
  exact normalSectionEvaluate_restrict_coordinate_as (curveToSurface r θ)
    (homOfLE (firstNormalOpen_le r θ i j)) (homOfLE hV)
    (homOfLE (hV.trans (firstNormalOpen_le r θ i j))) rfl
    (firstNormalVectorSection r θ i j)
    (normalSectionRestrict (curveToSurface r θ) hV (firstNormalVectorSection r θ i j)) rfl
    (firstCoordinateIdealEquation r θ a)
    (firstCoordinatePolynomial r θ
      (![firstSurfaceDehomogenize originalG2,
        -firstSurfaceDehomogenize (originalG1 r)] a))
    (firstNormalVectorSection_actualEquation r θ i j a)

/-- On every subopen, the second local frame evaluates the fixed coordinate
equations to the restrictions of the fixed coordinate coefficient sections. -/
theorem secondNormalVectorSection_restrict_actualEquation_typed (r θ : ℂ)
    (i : Fin 2) (j : Fin 3) (V : (surface r θ).Opens)
    (hV : V ≤ secondNormalOpen r θ i j) (a : Fin 2) :
    normalSectionEvaluate (curveToSurface r θ) V
        (normalSectionRestrict (curveToSurface r θ) hV
          (secondNormalVectorSection r θ i j))
        (kernelSectionRestrict (curveToSurface r θ)
          (homOfLE (hV.trans (secondNormalOpen_le r θ i j)))
          (secondCoordinateIdealEquation r θ a)) =
      (curveToSurface r θ).app V
        ((surface r θ).presheaf.map
          (homOfLE (hV.trans (secondNormalOpen_le r θ i j))).op
          (secondCoordinatePolynomial r θ
            (![secondSurfaceDehomogenize originalG2,
              -secondSurfaceDehomogenize (originalG1 r)] a))) := by
  exact normalSectionEvaluate_restrict_coordinate_as (curveToSurface r θ)
    (homOfLE (secondNormalOpen_le r θ i j)) (homOfLE hV)
    (homOfLE (hV.trans (secondNormalOpen_le r θ i j))) rfl
    (secondNormalVectorSection r θ i j)
    (normalSectionRestrict (curveToSurface r θ) hV (secondNormalVectorSection r θ i j)) rfl
    (secondCoordinateIdealEquation r θ a)
    (secondCoordinatePolynomial r θ
      (![secondSurfaceDehomogenize originalG2,
        -secondSurfaceDehomogenize (originalG1 r)] a))
    (secondNormalVectorSection_actualEquation r θ i j a)

#print axioms normalSectionEvaluate_restrict_coordinate_as
#print axioms firstNormalVectorSection_restrict_actualEquation_typed
#print axioms secondNormalVectorSection_restrict_actualEquation_typed
end CycleQ2GeometricNormalCharts
end

end NormalSectionsNormalTypedRestrictionPart

section NormalSectionsNormalCoordinateExtPart

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricNormalCharts
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry MvPolynomial
  CycleQ2GeometricIntrinsicNormal CycleQ2GeometricAffineChartSections
  CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricAffineCurveCharts

theorem normalIndex_cases (a : Fin 2) : a = 0 ∨ a = 1 := by
  fin_cases a <;> simp

/-- The two coordinate equations in the kernel of the actual affine
surface-to-curve quotient, before any minor localization. -/
def coordinateChartIdealEquation (q h : AffinePoly) (g₁ g₂ k : SurfacePoly) (a : Fin 2) :
    RingHom.ker (surfaceToCurve q h g₁ g₂ k).toRingHom :=
  ⟨surfaceMap ![surfaceEquation q h g₁ g₂ k, includeCurve h] (normalPolynomial q a), by
    change polynomialToCurve q h (normalPolynomial q a) = 0
    rcases normalIndex_cases a with rfl | rfl
    · exact polynomialToCurve_quadric q h
    · exact polynomialToCurve_normal q h⟩

theorem coordinateChartIdealEquation_span (q h : AffinePoly) (g₁ g₂ k : SurfacePoly) :
    Submodule.span (SurfaceChartRing ![surfaceEquation q h g₁ g₂ k, includeCurve h])
      (Set.range (coordinateChartIdealEquation q h g₁ g₂ k)) = ⊤ := by
  apply (Submodule.span_range_subtype_eq_top_iff
    (RingHom.ker (surfaceToCurve q h g₁ g₂ k).toRingHom)
    (fun a => (coordinateChartIdealEquation q h g₁ g₂ k a).property)).mpr
  change Submodule.span _ (Set.range (fun a =>
    surfaceMap ![surfaceEquation q h g₁ g₂ k, includeCurve h] (normalPolynomial q a))) = _
  rw [surfaceToCurve_kernel]
  congr 1
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    rcases normalIndex_cases a with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (hx | hx)
    · exact ⟨0, hx.symm⟩
    · exact ⟨1, hx.symm⟩

/-- The fixed coordinate equations determine an intrinsic normal section
on every subopen of an actual affine surface-coordinate chart. -/
theorem coordinateChart_subopen_ext
    (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    {X Y : Scheme.{0}} (j : X ⟶ Y)
    (iS : Spec (CommRingCat.of
      (SurfaceChartRing ![surfaceEquation q h g₁ g₂ k, includeCurve h])) ⟶ Y)
    (iC : Spec (CommRingCat.of (ChartRing ![q,h])) ⟶ X)
    [IsOpenImmersion iS] [IsOpenImmersion iC]
    (H : IsPullback (Spec.map (CommRingCat.ofHom (surfaceToCurve q h g₁ g₂ k).toRingHom))
      iC iS j)
    (U : Y.Opens) (hU : U = iS.opensRange)
    (e : U.toScheme ≅ Spec (CommRingCat.of
      (SurfaceChartRing ![surfaceEquation q h g₁ g₂ k, includeCurve h])))
    (hi : e.inv ≫ U.ι = iS)
    (u : Fin 2 → RingHom.ker (j.app U).hom)
    (hu : ∀ a, (u a : Γ(Y, U)) =
      chartSection e (Over.mk (𝟙 U)) (coordinateChartIdealEquation q h g₁ g₂ k a))
    (V : Y.Opens) (hV : V ≤ U)
    (f g : (normalDirectImageSheaf j).val.obj (op V))
    (hfg : ∀ a, normalSectionEvaluate j V f
        (kernelSectionRestrict j (homOfLE hV) (u a)) =
      normalSectionEvaluate j V g
        (kernelSectionRestrict j (homOfLE hV) (u a))) : f = g := by
  subst U
  exact normalOpen_ext_of_chart_generators
    (CommRingCat.ofHom (surfaceToCurve q h g₁ g₂ k).toRingHom)
    j iS iC H e hi (coordinateChartIdealEquation q h g₁ g₂ k)
    (coordinateChartIdealEquation_span q h g₁ g₂ k) u hu V hV f g hfg

open CycleQ2GeometricCoordinateNormalSections CycleQ2GeometricSurfaceJacobianCharts
  CycleQ2GeometricSurfacePrincipalCurveCharts CycleQ2GeometricSurfaceDehomogenizedCharts
  CycleQ2GeometricSurfaceOverlap CycleQ2GeometricLiteralSurface
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricSurfaceNormalCover
  CycleQ2GeometricSurfaceCurveCharts CycleQ2GeometricProjectiveCurve
  CycleQ2CartierProjectiveCover CycleQ2SeedTrace CycleQ2SeedCechTheta CycleQ2NormalConnecting

theorem firstCoordinateNormal_subopen_ext (r θ : ℂ)
    (V : (surface r θ).Opens) (hV : V ≤ coordinatePatch r θ 1)
    (f g : (normalDirectImageSheaf (curveToSurface r θ)).val.obj (op V))
    (hfg : ∀ a, normalSectionEvaluate (curveToSurface r θ) V f
        (kernelSectionRestrict (curveToSurface r θ) (homOfLE hV)
          (firstCoordinateIdealEquation r θ a)) =
      normalSectionEvaluate (curveToSurface r θ) V g
        (kernelSectionRestrict (curveToSurface r θ) (homOfLE hV)
          (firstCoordinateIdealEquation r θ a))) : f = g := by
  exact coordinateChart_subopen_ext (firstQuadric r) (firstCubic θ)
    (firstSurfaceDehomogenize (originalG1 r)) (firstSurfaceDehomogenize originalG2)
    (firstSurfaceDehomogenize (thetaK θ))
    (curveToSurface r θ) (firstSurfaceImmersion r θ) (firstCurveImmersion r θ)
    (firstAffineChart_isPullback r θ) (coordinatePatch r θ 1)
    (firstSurfaceImmersion_range r θ).symm (firstAffineChart r θ) rfl
    (firstCoordinateIdealEquation r θ)
    (fun a => (RingHom.congr_fun (first_chartSection_top r θ)
      (surfaceMap (firstEquations r θ) (normalPolynomial (firstQuadric r) a))).symm)
    V hV f g hfg

theorem secondCoordinateNormal_subopen_ext (r θ : ℂ)
    (V : (surface r θ).Opens) (hV : V ≤ coordinatePatch r θ 2)
    (f g : (normalDirectImageSheaf (curveToSurface r θ)).val.obj (op V))
    (hfg : ∀ a, normalSectionEvaluate (curveToSurface r θ) V f
        (kernelSectionRestrict (curveToSurface r θ) (homOfLE hV)
          (secondCoordinateIdealEquation r θ a)) =
      normalSectionEvaluate (curveToSurface r θ) V g
        (kernelSectionRestrict (curveToSurface r θ) (homOfLE hV)
          (secondCoordinateIdealEquation r θ a))) : f = g := by
  exact coordinateChart_subopen_ext (secondQuadric r) (secondCubic θ)
    (secondSurfaceDehomogenize (originalG1 r)) (secondSurfaceDehomogenize originalG2)
    (secondSurfaceDehomogenize (thetaK θ))
    (curveToSurface r θ) (secondSurfaceImmersion r θ) (secondCurveImmersion r θ)
    (secondAffineChart_isPullback r θ) (coordinatePatch r θ 2)
    (secondSurfaceImmersion_range r θ).symm (secondAffineChart r θ) rfl
    (secondCoordinateIdealEquation r θ)
    (fun a => (RingHom.congr_fun (second_chartSection_top r θ)
      (surfaceMap (secondEquations r θ) (normalPolynomial (secondQuadric r) a))).symm)
    V hV f g hfg

#print axioms coordinateChartIdealEquation_span
#print axioms coordinateChart_subopen_ext
#print axioms firstCoordinateNormal_subopen_ext
#print axioms secondCoordinateNormal_subopen_ext
end CycleQ2GeometricNormalCharts
end

end NormalSectionsNormalCoordinateExtPart

section NormalSectionsNormalMinorCompatibilitySimplePart

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricNormalCharts
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricIntrinsicNormal CycleQ2GeometricAffineChartSections
  CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricAffineCurveCharts
  CycleQ2GeometricCoordinateNormalSections CycleQ2GeometricSurfaceJacobianCharts
  CycleQ2GeometricSurfacePrincipalCurveCharts CycleQ2GeometricSurfaceDehomogenizedCharts
  CycleQ2GeometricSurfaceOverlap CycleQ2GeometricLiteralSurface
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricSurfaceNormalCover
  CycleQ2GeometricSurfaceCurveCharts CycleQ2GeometricProjectiveCurve
  CycleQ2CartierProjectiveCover CycleQ2SeedTrace CycleQ2SeedCechTheta CycleQ2NormalConnecting

/-- The local frame evaluates a coordinate equation through any chosen
inclusion into the coordinate open; both frames can use this same arrow. -/
theorem firstNormalVectorSection_restrict_coordinateEquation (r θ : ℂ)
    (i : Fin 2) (j : Fin 3) (V : (surface r θ).Opens)
    (hV : V ≤ firstNormalOpen r θ i j) (hW : V ≤ coordinatePatch r θ 1) (a : Fin 2) :
    normalSectionEvaluate (curveToSurface r θ) V
        (normalSectionRestrict (curveToSurface r θ) hV (firstNormalVectorSection r θ i j))
        (kernelSectionRestrict (curveToSurface r θ) (homOfLE hW)
          (firstCoordinateIdealEquation r θ a)) =
      (curveToSurface r θ).app V
        ((surface r θ).presheaf.map (homOfLE hW).op
          (firstCoordinatePolynomial r θ
            (![firstSurfaceDehomogenize originalG2,-firstSurfaceDehomogenize (originalG1 r)] a))) := by
  exact normalSectionEvaluate_restrict_coordinate_as (curveToSurface r θ)
    (homOfLE (firstNormalOpen_le r θ i j)) (homOfLE hV) (homOfLE hW) (Subsingleton.elim _ _)
    (firstNormalVectorSection r θ i j)
    (normalSectionRestrict (curveToSurface r θ) hV (firstNormalVectorSection r θ i j)) rfl
    (firstCoordinateIdealEquation r θ a)
    (firstCoordinatePolynomial r θ
      (![firstSurfaceDehomogenize originalG2,-firstSurfaceDehomogenize (originalG1 r)] a))
    (firstNormalVectorSection_actualEquation r θ i j a)

/-- Two minor frames coincide on every actual common subopen. -/
theorem firstNormalVectorSection_compatible_on (r θ : ℂ)
    (i : Fin 2) (j : Fin 3) (i' : Fin 2) (j' : Fin 3)
    (V : (surface r θ).Opens) (h₁ : V ≤ firstNormalOpen r θ i j)
    (h₂ : V ≤ firstNormalOpen r θ i' j') :
    normalSectionRestrict (curveToSurface r θ) h₁ (firstNormalVectorSection r θ i j) =
      normalSectionRestrict (curveToSurface r θ) h₂ (firstNormalVectorSection r θ i' j') := by
  let hW : V ≤ coordinatePatch r θ 1 := h₁.trans (firstNormalOpen_le r θ i j)
  apply firstCoordinateNormal_subopen_ext r θ V hW
  intro a
  exact (firstNormalVectorSection_restrict_coordinateEquation r θ i j V h₁ hW a).trans
    (firstNormalVectorSection_restrict_coordinateEquation r θ i' j' V h₂ hW a).symm

/-- The minor frames agree on their actual intersection. -/
theorem firstNormalVectorSection_compatible (r θ : ℂ)
    (i : Fin 2) (j : Fin 3) (i' : Fin 2) (j' : Fin 3) :
    normalSectionRestrict (curveToSurface r θ)
        (show firstNormalOpen r θ i j ⊓ firstNormalOpen r θ i' j' ≤
          firstNormalOpen r θ i j from inf_le_left) (firstNormalVectorSection r θ i j) =
      normalSectionRestrict (curveToSurface r θ)
        (show firstNormalOpen r θ i j ⊓ firstNormalOpen r θ i' j' ≤
          firstNormalOpen r θ i' j' from inf_le_right) (firstNormalVectorSection r θ i' j') :=
  firstNormalVectorSection_compatible_on r θ i j i' j'
    (firstNormalOpen r θ i j ⊓ firstNormalOpen r θ i' j') inf_le_left inf_le_right

/-- The local frame evaluates a coordinate equation through any chosen
inclusion into the coordinate open; both frames can use this same arrow. -/
theorem secondNormalVectorSection_restrict_coordinateEquation (r θ : ℂ)
    (i : Fin 2) (j : Fin 3) (V : (surface r θ).Opens)
    (hV : V ≤ secondNormalOpen r θ i j) (hW : V ≤ coordinatePatch r θ 2) (a : Fin 2) :
    normalSectionEvaluate (curveToSurface r θ) V
        (normalSectionRestrict (curveToSurface r θ) hV (secondNormalVectorSection r θ i j))
        (kernelSectionRestrict (curveToSurface r θ) (homOfLE hW)
          (secondCoordinateIdealEquation r θ a)) =
      (curveToSurface r θ).app V
        ((surface r θ).presheaf.map (homOfLE hW).op
          (secondCoordinatePolynomial r θ
            (![secondSurfaceDehomogenize originalG2,-secondSurfaceDehomogenize (originalG1 r)] a))) := by
  exact normalSectionEvaluate_restrict_coordinate_as (curveToSurface r θ)
    (homOfLE (secondNormalOpen_le r θ i j)) (homOfLE hV) (homOfLE hW) (Subsingleton.elim _ _)
    (secondNormalVectorSection r θ i j)
    (normalSectionRestrict (curveToSurface r θ) hV (secondNormalVectorSection r θ i j)) rfl
    (secondCoordinateIdealEquation r θ a)
    (secondCoordinatePolynomial r θ
      (![secondSurfaceDehomogenize originalG2,-secondSurfaceDehomogenize (originalG1 r)] a))
    (secondNormalVectorSection_actualEquation r θ i j a)

/-- Two minor frames coincide on every actual common subopen. -/
theorem secondNormalVectorSection_compatible_on (r θ : ℂ)
    (i : Fin 2) (j : Fin 3) (i' : Fin 2) (j' : Fin 3)
    (V : (surface r θ).Opens) (h₁ : V ≤ secondNormalOpen r θ i j)
    (h₂ : V ≤ secondNormalOpen r θ i' j') :
    normalSectionRestrict (curveToSurface r θ) h₁ (secondNormalVectorSection r θ i j) =
      normalSectionRestrict (curveToSurface r θ) h₂ (secondNormalVectorSection r θ i' j') := by
  let hW : V ≤ coordinatePatch r θ 2 := h₁.trans (secondNormalOpen_le r θ i j)
  apply secondCoordinateNormal_subopen_ext r θ V hW
  intro a
  exact (secondNormalVectorSection_restrict_coordinateEquation r θ i j V h₁ hW a).trans
    (secondNormalVectorSection_restrict_coordinateEquation r θ i' j' V h₂ hW a).symm

/-- The minor frames agree on their actual intersection. -/
theorem secondNormalVectorSection_compatible (r θ : ℂ)
    (i : Fin 2) (j : Fin 3) (i' : Fin 2) (j' : Fin 3) :
    normalSectionRestrict (curveToSurface r θ)
        (show secondNormalOpen r θ i j ⊓ secondNormalOpen r θ i' j' ≤
          secondNormalOpen r θ i j from inf_le_left) (secondNormalVectorSection r θ i j) =
      normalSectionRestrict (curveToSurface r θ)
        (show secondNormalOpen r θ i j ⊓ secondNormalOpen r θ i' j' ≤
          secondNormalOpen r θ i' j' from inf_le_right) (secondNormalVectorSection r θ i' j') :=
  secondNormalVectorSection_compatible_on r θ i j i' j'
    (secondNormalOpen r θ i j ⊓ secondNormalOpen r θ i' j') inf_le_left inf_le_right

#print axioms firstNormalVectorSection_restrict_coordinateEquation
#print axioms secondNormalVectorSection_restrict_coordinateEquation
#print axioms firstNormalVectorSection_compatible_on
#print axioms secondNormalVectorSection_compatible_on
#print axioms firstNormalVectorSection_compatible
#print axioms secondNormalVectorSection_compatible
end CycleQ2GeometricNormalCharts
end

end NormalSectionsNormalMinorCompatibilitySimplePart

section NormalSectionsNormalCoordinateFinalGluingPart

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricIntrinsicNormal
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

/-- Support-aware gluing with restrictions retaining their explicit
normal-section target types. -/
theorem existsUnique_normalGluing_typed
    {X Y : Scheme.{0}} (j : X ⟶ Y) [IsClosedImmersion j] {ι : Type}
    (U : Y.Opens) (V : ι → Y.Opens) (hVU : ∀ t, V t ≤ U)
    (hcover : j ⁻¹ᵁ U ≤ ⨆ t, j ⁻¹ᵁ V t)
    (s : ∀ t, (normalDirectImageSheaf j).val.obj (op (V t)))
    (hs : ∀ a b,
      normalSectionRestrict j (show V a ⊓ V b ≤ V a from inf_le_left) (s a) =
      normalSectionRestrict j (show V a ⊓ V b ≤ V b from inf_le_right) (s b)) :
    ∃! f : (normalDirectImageSheaf j).val.obj (op U),
      ∀ t, normalSectionRestrict j (hVU t) f = s t :=
  existsUnique_normalGluing_of_preimage_cover j U V hVU hcover s hs

theorem normalSectionEvaluate_eq_of_preimage_cover_typed
    {X Y : Scheme.{0}} (j : X ⟶ Y) {ι : Type}
    (U : Y.Opens) (V : ι → Y.Opens) (hVU : ∀ t, V t ≤ U)
    (hcover : j ⁻¹ᵁ U ≤ ⨆ t, j ⁻¹ᵁ V t)
    (f : (normalDirectImageSheaf j).val.obj (op U))
    (a : RingHom.ker (j.app U).hom) (b : Γ(Y,U))
    (hs : ∀ t, normalSectionEvaluate j (V t) (normalSectionRestrict j (hVU t) f)
      (kernelSectionRestrict j (homOfLE (hVU t)) a) =
        j.app (V t) (Y.presheaf.map (homOfLE (hVU t)).op b)) :
    normalSectionEvaluate j U f a = j.app U b :=
  normalSectionEvaluate_eq_of_preimage_cover j U V hVU hcover f a b hs

end CycleQ2GeometricIntrinsicNormal
end

noncomputable section
namespace CycleQ2GeometricNormalCharts
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricIntrinsicNormal CycleQ2GeometricAffineChartSections
  CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricAffineCurveCharts

open CycleQ2GeometricCoordinateNormalSections CycleQ2GeometricSurfaceJacobianCharts
  CycleQ2GeometricSurfacePrincipalCurveCharts CycleQ2GeometricSurfaceDehomogenizedCharts
  CycleQ2GeometricSurfaceOverlap CycleQ2GeometricLiteralSurface
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricSurfaceNormalCover
  CycleQ2GeometricSurfaceCurveCharts CycleQ2GeometricProjectiveCurve
  CycleQ2CartierProjectiveCover CycleQ2SeedTrace CycleQ2SeedCechTheta CycleQ2NormalConnecting

theorem firstCoordinateNormal_preimage_cover :
    curveToSurface 57 1 ⁻¹ᵁ coordinatePatch 57 1 1 ≤
      ⨆ p : Fin 2 × Fin 3, curveToSurface 57 1 ⁻¹ᵁ firstNormalOpen 57 1 p.1 p.2 := by
  have hc : (⨆ p : Fin 2 × Fin 3, curveToSurface 57 1 ⁻¹ᵁ firstNormalOpen 57 1 p.1 p.2) =
      coordinateProjectivePatch 57 1 1 := by
    rw [iSup_prod]
    simp_rw [firstNormalOpen_preimage]
    exact first_normalOpen_cover
  rw [hc]
  exact (coordinateCurvePreimage 57 1 (1 : Fin 4)).le

/-- The six actual first-coordinate minor frames glue uniquely on the
surface coordinate open because their preimages cover the closed curve. -/
theorem firstCoordinateNormalVector_existsUnique :
    ∃! f : (normalDirectImageSheaf (curveToSurface 57 1)).val.obj
        (op (coordinatePatch 57 1 1)),
      ∀ p : Fin 2 × Fin 3,
        normalSectionRestrict (curveToSurface 57 1)
          (firstNormalOpen_le 57 1 p.1 p.2) f =
            firstNormalVectorSection 57 1 p.1 p.2 := by
  apply existsUnique_normalGluing_typed (curveToSurface 57 1)
    (coordinatePatch 57 1 1) (fun p : Fin 2 × Fin 3 => firstNormalOpen 57 1 p.1 p.2)
    (fun p => firstNormalOpen_le 57 1 p.1 p.2)
  · exact firstCoordinateNormal_preimage_cover
  · intro p q
    exact firstNormalVectorSection_compatible 57 1 p.1 p.2 q.1 q.2

/-- The actual first coordinate normal frame, with its literal polynomial
normalization fixed by every minor chart. -/
def firstCoordinateNormalVector :
    (normalDirectImageSheaf (curveToSurface 57 1)).val.obj (op (coordinatePatch 57 1 1)) :=
  firstCoordinateNormalVector_existsUnique.choose

@[simp] theorem firstCoordinateNormalVector_restrict (i : Fin 2) (j : Fin 3) :
    normalSectionRestrict (curveToSurface 57 1)
      (firstNormalOpen_le 57 1 i j) firstCoordinateNormalVector =
        firstNormalVectorSection 57 1 i j :=
  firstCoordinateNormalVector_existsUnique.choose_spec.1 (i,j)

theorem firstCoordinateNormalVector_unique
    (f : (normalDirectImageSheaf (curveToSurface 57 1)).val.obj (op (coordinatePatch 57 1 1)))
    (hf : ∀ p : Fin 2 × Fin 3,
      normalSectionRestrict (curveToSurface 57 1)
        (firstNormalOpen_le 57 1 p.1 p.2) f =
          firstNormalVectorSection 57 1 p.1 p.2) : f = firstCoordinateNormalVector :=
  firstCoordinateNormalVector_existsUnique.choose_spec.2 f hf

theorem secondCoordinateNormal_preimage_cover :
    curveToSurface 57 1 ⁻¹ᵁ coordinatePatch 57 1 2 ≤
      ⨆ p : Fin 2 × Fin 3, curveToSurface 57 1 ⁻¹ᵁ secondNormalOpen 57 1 p.1 p.2 := by
  have hc : (⨆ p : Fin 2 × Fin 3, curveToSurface 57 1 ⁻¹ᵁ secondNormalOpen 57 1 p.1 p.2) =
      coordinateProjectivePatch 57 1 2 := by
    rw [iSup_prod]
    simp_rw [secondNormalOpen_preimage]
    exact second_normalOpen_cover
  rw [hc]
  exact (coordinateCurvePreimage 57 1 (2 : Fin 4)).le

/-- The six actual second-coordinate minor frames glue uniquely on the
surface coordinate open because their preimages cover the closed curve. -/
theorem secondCoordinateNormalVector_existsUnique :
    ∃! f : (normalDirectImageSheaf (curveToSurface 57 1)).val.obj
        (op (coordinatePatch 57 1 2)),
      ∀ p : Fin 2 × Fin 3,
        normalSectionRestrict (curveToSurface 57 1)
          (secondNormalOpen_le 57 1 p.1 p.2) f =
            secondNormalVectorSection 57 1 p.1 p.2 := by
  apply existsUnique_normalGluing_typed (curveToSurface 57 1)
    (coordinatePatch 57 1 2) (fun p : Fin 2 × Fin 3 => secondNormalOpen 57 1 p.1 p.2)
    (fun p => secondNormalOpen_le 57 1 p.1 p.2)
  · exact secondCoordinateNormal_preimage_cover
  · intro p q
    exact secondNormalVectorSection_compatible 57 1 p.1 p.2 q.1 q.2

/-- The actual second coordinate normal frame, with its literal polynomial
normalization fixed by every minor chart. -/
def secondCoordinateNormalVector :
    (normalDirectImageSheaf (curveToSurface 57 1)).val.obj (op (coordinatePatch 57 1 2)) :=
  secondCoordinateNormalVector_existsUnique.choose

@[simp] theorem secondCoordinateNormalVector_restrict (i : Fin 2) (j : Fin 3) :
    normalSectionRestrict (curveToSurface 57 1)
      (secondNormalOpen_le 57 1 i j) secondCoordinateNormalVector =
        secondNormalVectorSection 57 1 i j :=
  secondCoordinateNormalVector_existsUnique.choose_spec.1 (i,j)

theorem secondCoordinateNormalVector_unique
    (f : (normalDirectImageSheaf (curveToSurface 57 1)).val.obj (op (coordinatePatch 57 1 2)))
    (hf : ∀ p : Fin 2 × Fin 3,
      normalSectionRestrict (curveToSurface 57 1)
        (secondNormalOpen_le 57 1 p.1 p.2) f =
          secondNormalVectorSection 57 1 p.1 p.2) : f = secondCoordinateNormalVector :=
  secondCoordinateNormalVector_existsUnique.choose_spec.2 f hf

/-- The glued first coordinate normal section retains the two original
polynomial coefficient values on the full coordinate open. -/
theorem firstCoordinateNormalVector_actualEquation (a : Fin 2) :
    normalSectionEvaluate (curveToSurface 57 1) (coordinatePatch 57 1 1)
        firstCoordinateNormalVector (firstCoordinateIdealEquation 57 1 a) =
      (curveToSurface 57 1).app (coordinatePatch 57 1 1)
        (firstCoordinatePolynomial 57 1
          (![firstSurfaceDehomogenize originalG2,
            -firstSurfaceDehomogenize (originalG1 57)] a)) := by
  apply normalSectionEvaluate_eq_of_preimage_cover_typed (curveToSurface 57 1)
    (coordinatePatch 57 1 1) (fun p : Fin 2 × Fin 3 => firstNormalOpen 57 1 p.1 p.2)
    (fun p => firstNormalOpen_le 57 1 p.1 p.2) firstCoordinateNormal_preimage_cover
  intro p
  rw [firstCoordinateNormalVector_restrict]
  exact firstNormalVectorSection_actualEquation 57 1 p.1 p.2 a

/-- The glued second coordinate normal section retains the two original
polynomial coefficient values on the full coordinate open. -/
theorem secondCoordinateNormalVector_actualEquation (a : Fin 2) :
    normalSectionEvaluate (curveToSurface 57 1) (coordinatePatch 57 1 2)
        secondCoordinateNormalVector (secondCoordinateIdealEquation 57 1 a) =
      (curveToSurface 57 1).app (coordinatePatch 57 1 2)
        (secondCoordinatePolynomial 57 1
          (![secondSurfaceDehomogenize originalG2,
            -secondSurfaceDehomogenize (originalG1 57)] a)) := by
  apply normalSectionEvaluate_eq_of_preimage_cover_typed (curveToSurface 57 1)
    (coordinatePatch 57 1 2) (fun p : Fin 2 × Fin 3 => secondNormalOpen 57 1 p.1 p.2)
    (fun p => secondNormalOpen_le 57 1 p.1 p.2) secondCoordinateNormal_preimage_cover
  intro p
  rw [secondCoordinateNormalVector_restrict]
  exact secondNormalVectorSection_actualEquation 57 1 p.1 p.2 a

#print axioms normalSectionEvaluate_eq_of_preimage_cover
#print axioms firstCoordinateNormalVector_actualEquation
#print axioms secondCoordinateNormalVector_actualEquation
#print axioms firstNormalVectorSection_compatible
#print axioms secondNormalVectorSection_compatible
#print axioms firstCoordinateNormalVector_existsUnique
#print axioms secondCoordinateNormalVector_existsUnique
#print axioms firstCoordinateNormalVector_restrict
#print axioms secondCoordinateNormalVector_restrict
end CycleQ2GeometricNormalCharts
end

end NormalSectionsNormalCoordinateFinalGluingPart

section NormalSectionsNormalImageScalarPart

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricIntrinsicNormal
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf

variable {X Y : Scheme.{0}} (j : X ⟶ Y)

/-- Multiply an intrinsic normal morphism by an arbitrary section of the
actual curve structure sheaf over the ambient open's preimage. -/
def normalImageScalar (U : Y.Opens) (r : Γ(X, j ⁻¹ᵁ U))
    (f : (normalDirectImageSheaf j).val.obj (op U)) :
    (normalDirectImageSheaf j).val.obj (op U) :=
  ⟨{ app V := AddCommGrpCat.ofHom
      { toFun m := X.presheaf.map ((Opens.map j.base).map V.unop.hom).op r *
          (show Γ(X, j ⁻¹ᵁ V.unop.left) from f.val.app V m)
        map_zero' := by
          rw [map_zero, mul_zero]
        map_add' m n := by
          rw [map_add, mul_add] }
     naturality {V W} h := by
       apply ConcreteCategory.hom_ext
       intro m
       change X.presheaf.map ((Opens.map j.base).map W.unop.hom).op r *
           (show Γ(X, j ⁻¹ᵁ W.unop.left) from
             f.val.app W ((kernelIdealSheaf j).val.map h.unop.left.op m)) =
         X.presheaf.map ((Opens.map j.base).map h.unop.left).op
           (X.presheaf.map ((Opens.map j.base).map V.unop.hom).op r *
             (show Γ(X, j ⁻¹ᵁ V.unop.left) from f.val.app V m))
       have hr : X.presheaf.map ((Opens.map j.base).map h.unop.left).op
           (X.presheaf.map ((Opens.map j.base).map V.unop.hom).op r) =
           X.presheaf.map ((Opens.map j.base).map W.unop.hom).op r :=
         (ConcreteCategory.congr_hom (X.presheaf.map_comp
           ((Opens.map j.base).map V.unop.hom).op
           ((Opens.map j.base).map h.unop.left).op) r).symm
       rw [map_mul, hr]
       exact congrArg (fun z : Γ(X, j ⁻¹ᵁ W.unop.left) =>
         X.presheaf.map ((Opens.map j.base).map W.unop.hom).op r * z)
           (ConcreteCategory.congr_hom (f.val.naturality h) m) }, by
    intro V a m
    change X.presheaf.map ((Opens.map j.base).map V.hom).op r *
        (show Γ(X, j ⁻¹ᵁ V.left) from f.val.app (op V) (a • m)) =
      j.app V.left a *
        (X.presheaf.map ((Opens.map j.base).map V.hom).op r *
          (show Γ(X, j ⁻¹ᵁ V.left) from f.val.app (op V) m))
    rw [f.property V a m]
    exact mul_left_comm _ _ _⟩

@[simp] theorem normalImageScalar_app (U : Y.Opens) (r : Γ(X, j ⁻¹ᵁ U))
    (f : (normalDirectImageSheaf j).val.obj (op U)) (V : Over U)
    (a : (kernelIdealSheaf j).val.obj (op V.left)) :
    (normalImageScalar j U r f).val.app (op V) a =
      X.presheaf.map ((Opens.map j.base).map V.hom).op r *
        (show Γ(X, j ⁻¹ᵁ V.left) from f.val.app (op V) a) := rfl

@[simp] theorem normalImageScalar_evaluate (U : Y.Opens) (r : Γ(X, j ⁻¹ᵁ U))
    (f : (normalDirectImageSheaf j).val.obj (op U))
    (a : RingHom.ker (j.app U).hom) :
    normalSectionEvaluate j U (normalImageScalar j U r f) a =
      r * (show Γ(X, j ⁻¹ᵁ U) from normalSectionEvaluate j U f a) := by
  change X.presheaf.map (𝟙 (op (j ⁻¹ᵁ U))) r *
    (show Γ(X, j ⁻¹ᵁ U) from normalSectionEvaluate j U f a) = _
  exact congrArg (fun s : Γ(X, j ⁻¹ᵁ U) =>
      s * (show Γ(X, j ⁻¹ᵁ U) from normalSectionEvaluate j U f a))
    (ConcreteCategory.congr_hom (X.presheaf.map_id (op (j ⁻¹ᵁ U))) r)

@[simp] theorem normalImageScalar_one (U : Y.Opens)
    (f : (normalDirectImageSheaf j).val.obj (op U)) : normalImageScalar j U 1 f = f := by
  apply localLinearHom_ext Y.sheaf (kernelIdealSheaf j) (imageStructureModule j)
  intro V a
  change X.presheaf.map ((Opens.map j.base).map V.hom).op 1 *
    (show Γ(X, j ⁻¹ᵁ V.left) from f.val.app (op V) a) = _
  rw [map_one, one_mul]

@[simp] theorem normalImageScalar_mul (U : Y.Opens) (r s : Γ(X, j ⁻¹ᵁ U))
    (f : (normalDirectImageSheaf j).val.obj (op U)) :
    normalImageScalar j U (r * s) f = normalImageScalar j U r (normalImageScalar j U s f) := by
  apply localLinearHom_ext Y.sheaf (kernelIdealSheaf j) (imageStructureModule j)
  intro V a
  change X.presheaf.map ((Opens.map j.base).map V.hom).op (r * s) *
      (show Γ(X, j ⁻¹ᵁ V.left) from f.val.app (op V) a) =
    X.presheaf.map ((Opens.map j.base).map V.hom).op r *
      (X.presheaf.map ((Opens.map j.base).map V.hom).op s *
        (show Γ(X, j ⁻¹ᵁ V.left) from f.val.app (op V) a))
  rw [map_mul, mul_assoc]

@[simp] theorem normalImageScalar_add (U : Y.Opens) (r s : Γ(X, j ⁻¹ᵁ U))
    (f : (normalDirectImageSheaf j).val.obj (op U)) :
    normalImageScalar j U (r + s) f = normalImageScalar j U r f + normalImageScalar j U s f := by
  apply localLinearHom_ext Y.sheaf (kernelIdealSheaf j) (imageStructureModule j)
  intro V a
  change X.presheaf.map ((Opens.map j.base).map V.hom).op (r + s) *
      (show Γ(X, j ⁻¹ᵁ V.left) from f.val.app (op V) a) =
    X.presheaf.map ((Opens.map j.base).map V.hom).op r *
        (show Γ(X, j ⁻¹ᵁ V.left) from f.val.app (op V) a) +
      X.presheaf.map ((Opens.map j.base).map V.hom).op s *
        (show Γ(X, j ⁻¹ᵁ V.left) from f.val.app (op V) a)
  rw [map_add, add_mul]

@[simp] theorem normalImageScalar_zero (U : Y.Opens)
    (f : (normalDirectImageSheaf j).val.obj (op U)) : normalImageScalar j U 0 f = 0 := by
  apply localLinearHom_ext Y.sheaf (kernelIdealSheaf j) (imageStructureModule j)
  intro V a
  change X.presheaf.map ((Opens.map j.base).map V.hom).op 0 *
    (show Γ(X, j ⁻¹ᵁ V.left) from f.val.app (op V) a) = 0
  rw [map_zero, zero_mul]

@[simp] theorem normalImageScalar_right_add (U : Y.Opens) (r : Γ(X, j ⁻¹ᵁ U))
    (f g : (normalDirectImageSheaf j).val.obj (op U)) :
    normalImageScalar j U r (f + g) = normalImageScalar j U r f + normalImageScalar j U r g := by
  apply localLinearHom_ext Y.sheaf (kernelIdealSheaf j) (imageStructureModule j)
  intro V a
  change X.presheaf.map ((Opens.map j.base).map V.hom).op r *
      ((show Γ(X, j ⁻¹ᵁ V.left) from f.val.app (op V) a) +
        (show Γ(X, j ⁻¹ᵁ V.left) from g.val.app (op V) a)) = _
  exact mul_add _ _ _

@[simp] theorem normalImageScalar_right_zero (U : Y.Opens) (r : Γ(X, j ⁻¹ᵁ U)) :
    normalImageScalar j U r 0 = 0 := by
  apply localLinearHom_ext Y.sheaf (kernelIdealSheaf j) (imageStructureModule j)
  intro V a
  change X.presheaf.map ((Opens.map j.base).map V.hom).op r * 0 = 0
  exact mul_zero _

/-- Intrinsic normal sections are naturally modules over the actual
curve-section ring, not only over the ambient section ring. -/
@[instance_reducible] def normalImageModule (U : Y.Opens) :
    Module Γ(X, j ⁻¹ᵁ U) ((normalDirectImageSheaf j).val.obj (op U)) where
  smul := normalImageScalar j U
  one_smul := normalImageScalar_one j U
  mul_smul := normalImageScalar_mul j U
  smul_zero := normalImageScalar_right_zero j U
  smul_add := normalImageScalar_right_add j U
  add_smul := normalImageScalar_add j U
  zero_smul := normalImageScalar_zero j U

/-- This curve-coefficient action commutes with restriction on every
ambient subopen. -/
theorem normalImageScalar_restrict {U V : Y.Opens} (h : V ⟶ U)
    (r : Γ(X, j ⁻¹ᵁ U)) (f : (normalDirectImageSheaf j).val.obj (op U)) :
    (normalDirectImageSheaf j).val.map h.op (normalImageScalar j U r f) =
      normalImageScalar j V (X.presheaf.map ((Opens.map j.base).map h).op r)
        ((normalDirectImageSheaf j).val.map h.op f) := by
  apply localLinearHom_ext Y.sheaf (kernelIdealSheaf j) (imageStructureModule j)
  intro W a
  change X.presheaf.map ((Opens.map j.base).map (W.hom ≫ h)).op r *
      (show Γ(X, j ⁻¹ᵁ W.left) from f.val.app (op ((Over.map h).obj W)) a) =
    X.presheaf.map ((Opens.map j.base).map W.hom).op
        (X.presheaf.map ((Opens.map j.base).map h).op r) *
      (show Γ(X, j ⁻¹ᵁ W.left) from f.val.app (op ((Over.map h).obj W)) a)
  exact congrArg (fun s : Γ(X, j ⁻¹ᵁ W.left) =>
      s * (show Γ(X, j ⁻¹ᵁ W.left) from f.val.app (op ((Over.map h).obj W)) a))
    (ConcreteCategory.congr_hom (X.presheaf.map_comp
      ((Opens.map j.base).map h).op ((Opens.map j.base).map W.hom).op) r)

/-- Restricting the curve-coefficient action through the actual scheme
section map recovers the existing ambient module action. -/
theorem normalImageScalar_app_eq_smul (U : Y.Opens) (r : Γ(Y, U))
    (f : (normalDirectImageSheaf j).val.obj (op U)) :
    normalImageScalar j U (j.app U r) f = r • f := by
  apply localLinearHom_ext Y.sheaf (kernelIdealSheaf j) (imageStructureModule j)
  intro V a
  change X.presheaf.map ((Opens.map j.base).map V.hom).op (j.app U r) *
      (show Γ(X, j ⁻¹ᵁ V.left) from f.val.app (op V) a) =
    j.app V.left (Y.presheaf.map V.hom.op r) *
      (show Γ(X, j ⁻¹ᵁ V.left) from f.val.app (op V) a)
  exact congrArg (fun s : Γ(X, j ⁻¹ᵁ V.left) =>
      s * (show Γ(X, j ⁻¹ᵁ V.left) from f.val.app (op V) a))
    (ConcreteCategory.congr_hom (j.naturality V.hom.op) r).symm

/-- Multiplication by an intrinsic normal section is a linear map from
the actual direct-image structure module. -/
def normalImageFrameLinearMap (U : Y.Opens)
    (f : (normalDirectImageSheaf j).val.obj (op U)) :
    (imageStructureModule j).val.obj (op U) →ₗ[Γ(Y, U)]
      (normalDirectImageSheaf j).val.obj (op U) where
  toFun r := normalImageScalar j U r f
  map_add' r s := normalImageScalar_add j U r s f
  map_smul' r a := by
    change normalImageScalar j U (j.app U r * (show Γ(X, j ⁻¹ᵁ U) from a)) f =
      r • normalImageScalar j U a f
    exact (normalImageScalar_mul j U (j.app U r) a f).trans
      (normalImageScalar_app_eq_smul j U r (normalImageScalar j U a f))

/-- The actual ideal of the immersion annihilates its normal sections. -/
theorem normal_ideal_smul_zero (U : Y.Opens) (a : RingHom.ker (j.app U).hom)
    (f : (normalDirectImageSheaf j).val.obj (op U)) : (a : Γ(Y, U)) • f = 0 := by
  rw [← normalImageScalar_app_eq_smul]
  change normalImageScalar j U ((j.app U).hom a) f = 0
  rw [a.property, normalImageScalar_zero]

#print axioms normalImageScalar
#print axioms normalImageScalar_evaluate
#print axioms normalImageModule
#print axioms normalImageScalar_restrict
#print axioms normalImageScalar_app_eq_smul
#print axioms normalImageFrameLinearMap
#print axioms normal_ideal_smul_zero
end CycleQ2GeometricIntrinsicNormal
end

end NormalSectionsNormalImageScalarPart

section NormalSectionsNormalCoordinateTransitionPart

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricIntrinsicNormal
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

/-- Restriction with both the restricted normal section and its
coefficient presentation supplied explicitly. -/
theorem normalSectionEvaluate_restrict_coefficient {X Y : Scheme.{0}} (j : X ⟶ Y)
    {U V : Y.Opens} (h : V ⟶ U)
    (f : (normalDirectImageSheaf j).val.obj (op U))
    (g : (normalDirectImageSheaf j).val.obj (op V))
    (hg : g = (normalDirectImageSheaf j).val.map h.op f)
    (a : RingHom.ker (j.app U).hom) (b : Γ(Y,U)) (c : Γ(Y,V))
    (hb : Y.presheaf.map h.op b = c)
    (hf : normalSectionEvaluate j U f a = j.app U b) :
    normalSectionEvaluate j V g (kernelSectionRestrict j h a) = j.app V c :=
  (congrArg (fun z => normalSectionEvaluate j V z (kernelSectionRestrict j h a)) hg).trans
    ((normalSectionEvaluate_restrict_of_value j h f a b hf).trans (congrArg (j.app V) hb))

/-- Evaluation is linear in the actual normal section, with ambient
scalars acting through the actual scheme section map. -/
theorem normalSectionEvaluate_smul {X Y : Scheme.{0}} (j : X ⟶ Y)
    (U : Y.Opens) (r : Γ(Y, U)) (f : (normalDirectImageSheaf j).val.obj (op U))
    (a : RingHom.ker (j.app U).hom) :
    normalSectionEvaluate j U (r • f) a =
      j.app U r * (show Γ(X, j ⁻¹ᵁ U) from normalSectionEvaluate j U f a) :=
  LinearMap.congr_fun ((normalSectionEvaluationLinearMap j U).map_smul r f) a

theorem normalSectionEvaluate_smul_ideal {X Y : Scheme.{0}} (j : X ⟶ Y)
    (U : Y.Opens) (r : Γ(Y, U)) (f : (normalDirectImageSheaf j).val.obj (op U))
    (a : RingHom.ker (j.app U).hom) :
    normalSectionEvaluate j U f (r • a) =
      j.app U r * (show Γ(X, j ⁻¹ᵁ U) from normalSectionEvaluate j U f a) :=
  (normalSectionEvaluate j U f).map_smul r a

/-- The inverse-square normal-frame factor follows from the weight-two
change of equations and weight-four change of their values. -/
theorem normalFrame_scaled_equations {X Y : Scheme.{0}} (j : X ⟶ Y)
    (U : Y.Opens) (t : Γ(Y, U))
    (q₁ q₂ : Fin 2 → RingHom.ker (j.app U).hom)
    (v₁ v₂ : Fin 2 → Γ(Y, U))
    (hq : ∀ a, q₂ a = (t ^ 2) • q₁ a)
    (hv : ∀ a, v₂ a = v₁ a * t ^ 4)
    (f₁ f₂ : (normalDirectImageSheaf j).val.obj (op U))
    (hf₁ : ∀ a, normalSectionEvaluate j U f₁ (q₁ a) = j.app U (v₁ a))
    (hf₂ : ∀ a, normalSectionEvaluate j U f₂ (q₂ a) = j.app U (v₂ a))
    (a : Fin 2) :
    normalSectionEvaluate j U ((t ^ 2) • f₁) (q₂ a) =
      normalSectionEvaluate j U f₂ (q₂ a) := by
  rw [hf₂ a, normalSectionEvaluate_smul, hq a, normalSectionEvaluate_smul_ideal,
    hf₁ a, hv a]
  simp only [map_mul, map_pow]
  ring

theorem normalFrame_scaled_of_ext {X Y : Scheme.{0}} (j : X ⟶ Y)
    (U : Y.Opens) (t : Γ(Y,U))
    (q₁ q₂ : Fin 2 → RingHom.ker (j.app U).hom)
    (v₁ v₂ : Fin 2 → Γ(Y,U))
    (hq : ∀ a, q₂ a = (t ^ 2) • q₁ a)
    (hv : ∀ a, v₂ a = v₁ a * t ^ 4)
    (f₁ f₂ : (normalDirectImageSheaf j).val.obj (op U))
    (hf₁ : ∀ a, normalSectionEvaluate j U f₁ (q₁ a) = j.app U (v₁ a))
    (hf₂ : ∀ a, normalSectionEvaluate j U f₂ (q₂ a) = j.app U (v₂ a))
    (hext : ∀ f g : (normalDirectImageSheaf j).val.obj (op U),
      (∀ a, normalSectionEvaluate j U f (q₂ a) = normalSectionEvaluate j U g (q₂ a)) → f = g) :
    f₂ = (t ^ 2) • f₁ :=
  hext f₂ ((t ^ 2) • f₁) (fun a =>
    (normalFrame_scaled_equations j U t q₁ q₂ v₁ v₂ hq hv f₁ f₂ hf₁ hf₂ a).symm)

end CycleQ2GeometricIntrinsicNormal
end

noncomputable section
namespace CycleQ2GeometricNormalCharts
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry MvPolynomial
  CycleQ2GeometricIntrinsicNormal CycleQ2GeometricAffineChartSections
  CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricAffineCurveCharts
  CycleQ2GeometricCoordinateNormalSections CycleQ2GeometricSurfaceJacobianCharts
  CycleQ2GeometricSurfacePrincipalCurveCharts CycleQ2GeometricSurfaceDehomogenizedCharts
  CycleQ2GeometricSurfaceOverlap CycleQ2GeometricLiteralSurface
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricSurfaceNormalCover
  CycleQ2GeometricSurfaceCurveCharts CycleQ2GeometricProjectiveCurve
  CycleQ2CartierProjectiveCover CycleQ2SeedTrace CycleQ2SeedCechTheta CycleQ2NormalConnecting
  CycleQ2CartierSurfaceGrading CycleQ2GeometricSurfaceCubicResidues

/-- The two literal weighted equations that define the curve. -/
def coordinateEquationPolynomial (r : ℂ) (a : Fin 2) : WeightedPoly :=
  ![originalF1 r, originalF2] a

def normalCoefficientPolynomial (r : ℂ) (a : Fin 2) : WeightedPoly :=
  ![originalG2, -originalG1 r] a

theorem coordinateEquationPolynomial_homogeneous (r : ℂ) (a : Fin 2) :
    (coordinateEquationPolynomial r a).IsWeightedHomogeneous CycleQ2CartierSurfaceGrading.weight 2 := by
  rcases normalIndex_cases a with rfl | rfl
  · exact originalF1_homogeneous r
  · exact originalF2_homogeneous

theorem normalCoefficientPolynomial_homogeneous (r : ℂ) (a : Fin 2) :
    (normalCoefficientPolynomial r a).IsWeightedHomogeneous CycleQ2CartierSurfaceGrading.weight 4 := by
  rcases normalIndex_cases a with rfl | rfl
  · exact originalG2_homogeneous
  · exact (originalG1_homogeneous r).neg

theorem firstCoordinatePolynomial_coefficient (r θ : ℂ)
    (V : (surface r θ).Opens) (hV : V ≤ coordinatePatch r θ 1) (p : WeightedPoly) :
    (surface r θ).presheaf.map (homOfLE hV).op
      (firstCoordinatePolynomial r θ (firstSurfaceDehomogenize p)) =
        firstCoefficientSection r θ V hV p :=
  (first_chartSection_subopen r θ (Over.mk (homOfLE hV))
    (surfaceMap (firstEquations r θ) (firstSurfaceDehomogenize p))).symm

theorem firstCoordinateIdealEquation_coefficient (r θ : ℂ)
    (V : (surface r θ).Opens) (hV : V ≤ coordinatePatch r θ 1) (a : Fin 2) :
    (kernelSectionRestrict (curveToSurface r θ) (homOfLE hV)
      (firstCoordinateIdealEquation r θ a) : Γ(surface r θ, V)) =
        firstCoefficientSection r θ V hV (coordinateEquationPolynomial r a) := by
  have he : normalPolynomial (firstQuadric r) a =
      firstSurfaceDehomogenize (coordinateEquationPolynomial r a) := by
    rcases normalIndex_cases a with rfl | rfl
    · exact (firstSurfaceDehomogenize_f1 r).symm
    · exact firstSurfaceDehomogenize_f2.symm
  exact (kernelSectionRestrict_coe (curveToSurface r θ) (homOfLE hV)
    (firstCoordinateIdealEquation r θ a)).trans
      ((congrArg (fun p => (surface r θ).presheaf.map (homOfLE hV).op
        (firstCoordinatePolynomial r θ p)) he).trans
          (firstCoordinatePolynomial_coefficient r θ V hV (coordinateEquationPolynomial r a)))

theorem secondCoordinatePolynomial_coefficient (r θ : ℂ)
    (V : (surface r θ).Opens) (hV : V ≤ coordinatePatch r θ 2) (p : WeightedPoly) :
    (surface r θ).presheaf.map (homOfLE hV).op
      (secondCoordinatePolynomial r θ (secondSurfaceDehomogenize p)) =
        secondCoefficientSection r θ V hV p :=
  (second_chartSection_subopen r θ (Over.mk (homOfLE hV))
    (surfaceMap (secondEquations r θ) (secondSurfaceDehomogenize p))).symm

theorem secondCoordinateIdealEquation_coefficient (r θ : ℂ)
    (V : (surface r θ).Opens) (hV : V ≤ coordinatePatch r θ 2) (a : Fin 2) :
    (kernelSectionRestrict (curveToSurface r θ) (homOfLE hV)
      (secondCoordinateIdealEquation r θ a) : Γ(surface r θ, V)) =
        secondCoefficientSection r θ V hV (coordinateEquationPolynomial r a) := by
  have he : normalPolynomial (secondQuadric r) a =
      secondSurfaceDehomogenize (coordinateEquationPolynomial r a) := by
    rcases normalIndex_cases a with rfl | rfl
    · exact (secondSurfaceDehomogenize_f1 r).symm
    · exact secondSurfaceDehomogenize_f2.symm
  exact (kernelSectionRestrict_coe (curveToSurface r θ) (homOfLE hV)
    (secondCoordinateIdealEquation r θ a)).trans
      ((congrArg (fun p => (surface r θ).presheaf.map (homOfLE hV).op
        (secondCoordinatePolynomial r θ p)) he).trans
          (secondCoordinatePolynomial_coefficient r θ V hV (coordinateEquationPolynomial r a)))

theorem coordinateIdealEquation_transition (r θ : ℂ)
    (V : (surface r θ).Opens) (hV : V ≤ overlapPatch r θ)
    (h₁ : V ≤ coordinatePatch r θ 1) (h₂ : V ≤ coordinatePatch r θ 2) (a : Fin 2) :
    kernelSectionRestrict (curveToSurface r θ) (homOfLE h₂)
        (secondCoordinateIdealEquation r θ a) =
      (overlapSectionMap r θ V hV (inverse (firstEquations r θ)) ^ 2) •
        kernelSectionRestrict (curveToSurface r θ) (homOfLE h₁)
          (firstCoordinateIdealEquation r θ a) := by
  apply Subtype.ext
  change (_ : Γ(surface r θ,V)) = _ * _
  rw [secondCoordinateIdealEquation_coefficient, firstCoordinateIdealEquation_coefficient]
  exact (homogeneousCoefficient_transition r θ V hV h₁ h₂ 2
    (coordinateEquationPolynomial r a) (coordinateEquationPolynomial_homogeneous r a)).trans
      (mul_comm _ _)

theorem firstCoordinateNormalVector_evaluate_coefficient
    (V : (surface 57 1).Opens) (hV : V ≤ coordinatePatch 57 1 1) (a : Fin 2) :
    normalSectionEvaluate (curveToSurface 57 1) V
      (normalSectionRestrict (curveToSurface 57 1) hV firstCoordinateNormalVector)
      (kernelSectionRestrict (curveToSurface 57 1) (homOfLE hV)
        (firstCoordinateIdealEquation 57 1 a)) =
      (curveToSurface 57 1).app V
        (firstCoefficientSection 57 1 V hV (normalCoefficientPolynomial 57 a)) := by
  have hp : (![firstSurfaceDehomogenize originalG2,
      -firstSurfaceDehomogenize (originalG1 57)] a) =
      firstSurfaceDehomogenize (normalCoefficientPolynomial 57 a) := by
    rcases normalIndex_cases a with rfl | rfl
    · rfl
    · exact (map_neg firstSurfaceDehomogenize (originalG1 57)).symm
  have hb := (congrArg (fun p => (surface 57 1).presheaf.map (homOfLE hV).op
    (firstCoordinatePolynomial 57 1 p)) hp).trans
      (firstCoordinatePolynomial_coefficient 57 1 V hV (normalCoefficientPolynomial 57 a))
  exact normalSectionEvaluate_restrict_coefficient (curveToSurface 57 1) (homOfLE hV)
    firstCoordinateNormalVector
    (normalSectionRestrict (curveToSurface 57 1) hV firstCoordinateNormalVector) rfl
    (firstCoordinateIdealEquation 57 1 a)
    (firstCoordinatePolynomial 57 1
      (![firstSurfaceDehomogenize originalG2,-firstSurfaceDehomogenize (originalG1 57)] a))
    (firstCoefficientSection 57 1 V hV (normalCoefficientPolynomial 57 a)) hb
    (firstCoordinateNormalVector_actualEquation a)

theorem secondCoordinateNormalVector_evaluate_coefficient
    (V : (surface 57 1).Opens) (hV : V ≤ coordinatePatch 57 1 2) (a : Fin 2) :
    normalSectionEvaluate (curveToSurface 57 1) V
      (normalSectionRestrict (curveToSurface 57 1) hV secondCoordinateNormalVector)
      (kernelSectionRestrict (curveToSurface 57 1) (homOfLE hV)
        (secondCoordinateIdealEquation 57 1 a)) =
      (curveToSurface 57 1).app V
        (secondCoefficientSection 57 1 V hV (normalCoefficientPolynomial 57 a)) := by
  have hp : (![secondSurfaceDehomogenize originalG2,
      -secondSurfaceDehomogenize (originalG1 57)] a) =
      secondSurfaceDehomogenize (normalCoefficientPolynomial 57 a) := by
    rcases normalIndex_cases a with rfl | rfl
    · rfl
    · exact (map_neg secondSurfaceDehomogenize (originalG1 57)).symm
  have hb := (congrArg (fun p => (surface 57 1).presheaf.map (homOfLE hV).op
    (secondCoordinatePolynomial 57 1 p)) hp).trans
      (secondCoordinatePolynomial_coefficient 57 1 V hV (normalCoefficientPolynomial 57 a))
  exact normalSectionEvaluate_restrict_coefficient (curveToSurface 57 1) (homOfLE hV)
    secondCoordinateNormalVector
    (normalSectionRestrict (curveToSurface 57 1) hV secondCoordinateNormalVector) rfl
    (secondCoordinateIdealEquation 57 1 a)
    (secondCoordinatePolynomial 57 1
      (![secondSurfaceDehomogenize originalG2,-secondSurfaceDehomogenize (originalG1 57)] a))
    (secondCoefficientSection 57 1 V hV (normalCoefficientPolynomial 57 a)) hb
    (secondCoordinateNormalVector_actualEquation a)

/-- The two actual coordinate normal frames have the required
inverse-square transition on every common subopen. -/
theorem coordinateNormalVector_transition
    (V : (surface 57 1).Opens) (hV : V ≤ overlapPatch 57 1) :
    normalSectionRestrict (curveToSurface 57 1)
        (hV.trans (overlap_le_second 57 1)) secondCoordinateNormalVector =
      (overlapSectionMap 57 1 V hV (inverse (firstEquations 57 1)) ^ 2) •
        normalSectionRestrict (curveToSurface 57 1)
          (hV.trans (overlap_le_first 57 1)) firstCoordinateNormalVector := by
  let h₁ := hV.trans (overlap_le_first 57 1)
  let h₂ := hV.trans (overlap_le_second 57 1)
  exact normalFrame_scaled_of_ext (curveToSurface 57 1) V
    (overlapSectionMap 57 1 V hV (inverse (firstEquations 57 1)))
    (fun a => kernelSectionRestrict (curveToSurface 57 1) (homOfLE h₁)
      (firstCoordinateIdealEquation 57 1 a))
    (fun a => kernelSectionRestrict (curveToSurface 57 1) (homOfLE h₂)
      (secondCoordinateIdealEquation 57 1 a))
    (fun a => firstCoefficientSection 57 1 V h₁ (normalCoefficientPolynomial 57 a))
    (fun a => secondCoefficientSection 57 1 V h₂ (normalCoefficientPolynomial 57 a))
    (coordinateIdealEquation_transition 57 1 V hV h₁ h₂)
    (fun a => homogeneousCoefficient_transition 57 1 V hV h₁ h₂ 4
      (normalCoefficientPolynomial 57 a) (normalCoefficientPolynomial_homogeneous 57 a))
    (normalSectionRestrict (curveToSurface 57 1) h₁ firstCoordinateNormalVector)
    (normalSectionRestrict (curveToSurface 57 1) h₂ secondCoordinateNormalVector)
    (firstCoordinateNormalVector_evaluate_coefficient V h₁)
    (secondCoordinateNormalVector_evaluate_coefficient V h₂)
    (secondCoordinateNormal_subopen_ext 57 1 V h₂)

#print axioms normalFrame_scaled_equations
#print axioms coordinateIdealEquation_transition
#print axioms firstCoordinateNormalVector_evaluate_coefficient
#print axioms secondCoordinateNormalVector_evaluate_coefficient
#print axioms coordinateNormalVector_transition
end CycleQ2GeometricNormalCharts
end

end NormalSectionsNormalCoordinateTransitionPart
