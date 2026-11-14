import Proposal.GeometricDifferentialSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.TensorProduct.Basic
import Proposal.GeometricLiteralSurface
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-!
# The actual kernel ideal sheaf of a scheme morphism

This construction uses the literal morphism of structure sheaves. Its
sections are identified with the kernel of the actual section-ring map,
including restriction compatibility. It provides the ideal-sheaf input
for an intrinsic normal sheaf; no normal-frame identification is assumed.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricIntrinsicNormal

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf

variable {X Y : Scheme.{0}} (j : X ⟶ Y)

/-- The actual scheme section maps bundled as a morphism of ring sheaves. -/
def schemeRingMap :
    ringSheaf Y.sheaf ⟶
      ((Opens.map j.base).sheafPushforwardContinuous RingCat.{0}
        (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj
          (ringSheaf X.sheaf) where
  hom :=
    { app U := RingCat.ofHom (j.app U.unop).hom
      naturality {U V} f := by
        ext a
        exact congrArg (fun g : Γ(Y, U.unop) ⟶ Γ(X, j ⁻¹ᵁ V.unop) => g a)
          (j.naturality f) }

/-- The direct image of the actual structure module of the source scheme. -/
def imageStructureModule : SheafOfModules.{0} (ringSheaf Y.sheaf) :=
  (SheafOfModules.pushforward (F := Opens.map j.base) (schemeRingMap j)).obj
    (SheafOfModules.unit (ringSheaf X.sheaf))

/-- The actual structure homomorphism as a map of module sheaves. -/
def schemeStructureMap :
    SheafOfModules.unit (ringSheaf Y.sheaf) ⟶ imageStructureModule j where
  val.app U := ModuleCat.homMk
    ((forget₂ RingCat AddCommGrpCat).map ((schemeRingMap j).hom.app U))
      (fun r ↦ by
        ext m
        exact (((schemeRingMap j).hom.app U).hom.map_mul r m).symm)
  val.naturality {U V} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact congrArg (fun g : Γ(Y, U.unop) ⟶ Γ(X, j ⁻¹ᵁ V.unop) => g a)
      (j.naturality f)

@[simp] theorem schemeStructureMap_app (U : Y.Opens) (a : Γ(Y, U)) :
    (schemeStructureMap j).val.app (op U) a = j.app U a := rfl

/-- The actual ideal subsheaf cut out by the scheme morphism. -/
def kernelIdealSheaf : SheafOfModules.{0} (ringSheaf Y.sheaf) :=
  kernel (schemeStructureMap j)

/-- Evaluation of the categorical kernel is the literal kernel ideal of
the corresponding ring map on sections. -/
def kernelIdealSectionIso (U : Y.Opens) :
    (kernelIdealSheaf j).val.obj (op U) ≅
      ModuleCat.of Γ(Y, U) (RingHom.ker (j.app U).hom) := by
  letI : (SheafOfModules.evaluation (ringSheaf Y.sheaf) (op U)).Additive := by
    dsimp [SheafOfModules.evaluation]
    infer_instance
  exact PreservesKernel.iso (SheafOfModules.evaluation (ringSheaf Y.sheaf) (op U))
      (schemeStructureMap j) ≪≫
    ModuleCat.kernelIsoKer ((schemeStructureMap j).val.app (op U))

def kernelIdealSectionEquiv (U : Y.Opens) :
    (kernelIdealSheaf j).val.obj (op U) ≃ₗ[Γ(Y, U)] RingHom.ker (j.app U).hom :=
  (kernelIdealSectionIso j U).toLinearEquiv

theorem kernelIdealSectionIso_hom_subtype (U : Y.Opens) :
    (kernelIdealSectionIso j U).hom ≫
      ModuleCat.ofHom (RingHom.ker (j.app U).hom).subtype =
      (kernel.ι (schemeStructureMap j)).val.app (op U) := by
  let : (SheafOfModules.evaluation (ringSheaf Y.sheaf) (op U)).Additive := by
    dsimp [SheafOfModules.evaluation]
    infer_instance
  change ((PreservesKernel.iso
      (SheafOfModules.evaluation (ringSheaf Y.sheaf) (op U))
      (schemeStructureMap j)).hom ≫
      (ModuleCat.kernelIsoKer ((schemeStructureMap j).val.app (op U))).hom) ≫ _ = _
  rw [Category.assoc]
  exact (congrArg
    (fun k => (PreservesKernel.iso
      (SheafOfModules.evaluation (ringSheaf Y.sheaf) (op U))
      (schemeStructureMap j)).hom ≫ k)
    (ModuleCat.kernelIsoKer_hom_ker_subtype ((schemeStructureMap j).val.app (op U)))).trans
    (kernelComparison_comp_ι (schemeStructureMap j)
      (SheafOfModules.evaluation (ringSheaf Y.sheaf) (op U)))

@[simp] theorem kernelIdealSectionEquiv_coe (U : Y.Opens)
    (a : (kernelIdealSheaf j).val.obj (op U)) :
    (kernelIdealSectionEquiv j U a : Γ(Y, U)) =
      (kernel.ι (schemeStructureMap j)).val.app (op U) a := by
  exact ConcreteCategory.congr_hom (kernelIdealSectionIso_hom_subtype j U) a

theorem kernelIdealSectionEquiv_restrict {U V : Y.Opens} (h : V ⟶ U)
    (a : (kernelIdealSheaf j).val.obj (op U)) :
    (kernelIdealSectionEquiv j V ((kernelIdealSheaf j).val.map h.op a) : Γ(Y, V)) =
      Y.presheaf.map h.op (kernelIdealSectionEquiv j U a) := by
  simp only [kernelIdealSectionEquiv_coe]
  exact PresheafOfModules.naturality_apply (kernel.ι (schemeStructureMap j)).val h.op a

#print axioms kernelIdealSectionIso

end CycleQ2GeometricIntrinsicNormal
end

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricIntrinsicNormal

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf

variable {T : TopCat.{0}} (R : T.Sheaf CommRingCat.{0})
  (M N : SheafOfModules.{0} (ringSheaf R))

local instance overModule (U : Opens T) (V : Over U) :
    Module ((ringSheaf R).obj.obj (op V.left))
      (((Over.forget U).op ⋙ N.val.presheaf).obj (op V)) := by
  change Module ((ringSheaf R).obj.obj (op V.left)) (N.val.obj (op V.left))
  infer_instance

/-- The subsheaf of local additive natural transformations which are linear
over every local section ring. -/
def linearHomSubfunctor : Subfunctor (presheafHom M.val.presheaf N.val.presheaf) where
  obj U := { f | ∀ (V : Over U.unop)
    (r : (ringSheaf R).obj.obj (op V.left)) (m : M.val.obj (op V.left)),
    f.app (op V) (r • m) = r • f.app (op V) m }
  map {U V} h f hf := by
    intro W r m
    exact hf ((Over.map h.unop).obj W) r m

theorem moduleUnderlying_isSheaf :
    Presieve.IsSheaf (Opens.grothendieckTopology T)
      (N.val.presheaf ⋙ forget AddCommGrpCat.{0}) :=
  (isSheaf_iff_isSheaf_of_type _ _).mp
    (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget AddCommGrpCat.{0}) N.isSheaf)

theorem linearHomSubfunctor_isSheaf :
    Presieve.IsSheaf (Opens.grothendieckTopology T)
      (linearHomSubfunctor R M N).toFunctor := by
  apply ((linearHomSubfunctor R M N).isSheaf_iff
    ((isSheaf_iff_isSheaf_of_type _ _).mp
      (Presheaf.IsSheaf.hom M.val.presheaf N.val.presheaf N.isSheaf))).mpr
  intro U f hf V r m
  let S := (linearHomSubfunctor R M N).sieveOfSection f
  apply ((moduleUnderlying_isSheaf R N) (S.pullback V.hom)
    ((Opens.grothendieckTopology T).pullback_stable V.hom hf)).isSeparatedFor.ext
  intro W h hh
  have hlin := hh (Over.mk (𝟙 W))
    ((ringSheaf R).obj.map h.op r) (M.val.map h.op m)
  have hnat (x : M.val.obj (op V.left)) :
      f.app (op (Over.mk (h ≫ V.hom))) (M.val.map h.op x) =
        N.val.map h.op (f.app (op V) x) :=
    ConcreteCategory.congr_hom
      (f.naturality (Over.homMk h : Over.mk (h ≫ V.hom) ⟶ V).op) x
  change N.val.map h.op (f.app (op V) (r • m)) =
    N.val.map h.op (r • f.app (op V) m)
  rw [← hnat, M.val.map_smul, N.val.map_smul, ← hnat]
  have e := presheafHom_map_app_op_mk_id
    (F := M.val.presheaf) (G := N.val.presheaf) (h ≫ V.hom) f
  exact (ConcreteCategory.congr_hom e _).symm.trans
    (hlin.trans (congrArg
      (fun z : N.val.obj (op W) => (ringSheaf R).obj.map h.op r • z)
      (ConcreteCategory.congr_hom e _)))

/-- Actual sheaf of local module morphisms, with no chosen affine frame. -/
def moduleHomTypeSheaf : T.Sheaf (Type 0) :=
  ⟨(linearHomSubfunctor R M N).toFunctor,
    (isSheaf_iff_isSheaf_of_type _ _).mpr (linearHomSubfunctor_isSheaf R M N)⟩

#print axioms linearHomSubfunctor_isSheaf

end CycleQ2GeometricIntrinsicNormal
end

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricIntrinsicNormal

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf

variable {T : TopCat.{0}} (R : T.Sheaf CommRingCat.{0})
  (M N : SheafOfModules.{0} (ringSheaf R))

local instance overHomRingModule (U : Opens T) (V : (Over U)ᵒᵖ) :
    Module ((ringSheaf R).obj.obj (op V.unop.left))
      (((Over.forget U).op ⋙ N.val.presheaf).obj V) := by
  change Module ((ringSheaf R).obj.obj (op V.unop.left)) (N.val.obj (op V.unop.left))
  infer_instance

local instance overHomCommModule (U : Opens T) (V : (Over U)ᵒᵖ) :
    Module (R.obj.obj (op V.unop.left))
      (((Over.forget U).op ⋙ N.val.presheaf).obj V) := by
  change Module (R.obj.obj (op V.unop.left)) (N.val.obj (op V.unop.left))
  infer_instance

local instance overHomRingModuleMk (U : Opens T) (V : Over U) :
    Module ((ringSheaf R).obj.obj (op V.left))
      (((Over.forget U).op ⋙ N.val.presheaf).obj (op V)) := by
  change Module ((ringSheaf R).obj.obj (op V.left)) (N.val.obj (op V.left))
  infer_instance

local instance overHomCommModuleMk (U : Opens T) (V : Over U) :
    Module (R.obj.obj (op V.left))
      (((Over.forget U).op ⋙ N.val.presheaf).obj (op V)) := by
  change Module (R.obj.obj (op V.left)) (N.val.obj (op V.left))
  infer_instance

local instance sectionCommRing (U : (Opens T)ᵒᵖ) :
    CommRing ((ringSheaf R).obj.obj U) :=
  inferInstanceAs (CommRing (R.obj.obj U))

local instance localAdditiveGroup (U : Opens T) :
    AddCommGroup ((presheafHom M.val.presheaf N.val.presheaf).obj (op U)) :=
  inferInstanceAs (AddCommGroup
    ((Over.forget U).op ⋙ M.val.presheaf ⟶ (Over.forget U).op ⋙ N.val.presheaf))

def localLinearHomAddSubgroup (U : Opens T) :
    AddSubgroup ((presheafHom M.val.presheaf N.val.presheaf).obj (op U)) where
  carrier := (linearHomSubfunctor R M N).obj (op U)
  zero_mem' := by
    intro V r m
    change (0 : N.val.obj (op V.left)) = r • 0
    exact (smul_zero r).symm
  add_mem' := by
    intro f g hf hg V r m
    change f.app (op V) (r • m) + g.app (op V) (r • m) =
      r • (f.app (op V) m + g.app (op V) m)
    rw [hf V r m, hg V r m, smul_add]
  neg_mem' := by
    intro f hf V r m
    change -(f.app (op V) (r • m)) = r • -(f.app (op V) m)
    rw [hf V r m, smul_neg]

abbrev LocalLinearHom (U : Opens T) := localLinearHomAddSubgroup R M N U

def scaleLocalAdditiveHom (U : Opens T) (r : R.obj.obj (op U))
    (f : (presheafHom M.val.presheaf N.val.presheaf).obj (op U)) :
    (presheafHom M.val.presheaf N.val.presheaf).obj (op U) where
  app V := AddCommGrpCat.ofHom
    { toFun := fun x => R.obj.map V.unop.hom.op r •
        (show N.val.obj (op V.unop.left) from f.app V x)
      map_zero' := by
        exact (congrArg (fun z : N.val.obj (op V.unop.left) =>
          R.obj.map V.unop.hom.op r • z) (f.app V).hom.map_zero).trans (smul_zero _)
      map_add' x y := by
        exact (congrArg (fun z : N.val.obj (op V.unop.left) =>
          R.obj.map V.unop.hom.op r • z) ((f.app V).hom.map_add x y)).trans
          (smul_add _ _ _) }
  naturality {V W} h := by
    apply ConcreteCategory.hom_ext
    intro x
    change R.obj.map W.unop.hom.op r •
      f.app W (M.val.map h.unop.left.op x) =
      N.val.map h.unop.left.op (R.obj.map V.unop.hom.op r • f.app V x)
    rw [N.val.map_smul]
    have hr : R.obj.map h.unop.left.op (R.obj.map V.unop.hom.op r) =
        R.obj.map W.unop.hom.op r := by
      change (R.obj.map V.unop.hom.op ≫ R.obj.map h.unop.left.op) r = _
      rw [← R.obj.map_comp, ← op_comp, Over.w h.unop]
    exact (congrArg (fun z : N.val.obj (op W.unop.left) =>
      R.obj.map W.unop.hom.op r • z)
      (ConcreteCategory.congr_hom (f.naturality h) x)).trans
        (congrArg (fun a : R.obj.obj (op W.unop.left) =>
          a • N.val.map h.unop.left.op (f.app V x)) hr.symm)

def scaleLocalLinearHom (U : Opens T) (r : R.obj.obj (op U))
    (f : LocalLinearHom R M N U) : LocalLinearHom R M N U :=
  ⟨scaleLocalAdditiveHom R M N U r f.val, by
    intro V a m
    change R.obj.map V.hom.op r • (f.val.app (op V) (a • m)) =
      a • (R.obj.map V.hom.op r • f.val.app (op V) m)
    rw [f.property V a m]
    change R.obj.map V.hom.op r • ((a : R.obj.obj (op V.left)) •
      (f.val.app (op V) m : N.val.obj (op V.left))) =
      (a : R.obj.obj (op V.left)) • (R.obj.map V.hom.op r •
        (f.val.app (op V) m : N.val.obj (op V.left)))
    exact @smul_comm (R.obj.obj (op V.left)) (R.obj.obj (op V.left))
      (N.val.obj (op V.left)) _ _ _ (R.obj.map V.hom.op r) a
        (f.val.app (op V) m)⟩

instance localLinearHomSMul (U : Opens T) :
    SMul (R.obj.obj (op U)) (LocalLinearHom R M N U) :=
  ⟨scaleLocalLinearHom R M N U⟩

@[simp] theorem localLinearHom_smul_app (U : Opens T)
    (r : R.obj.obj (op U)) (f : LocalLinearHom R M N U) (V : Over U)
    (m : M.val.obj (op V.left)) :
    (r • f).val.app (op V) m =
      R.obj.map V.hom.op r • f.val.app (op V) m := rfl

@[ext] theorem localLinearHom_ext {U : Opens T} {f g : LocalLinearHom R M N U}
    (h : ∀ (V : Over U) (m : M.val.obj (op V.left)),
      f.val.app (op V) m = g.val.app (op V) m) : f = g := by
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.hom_ext
  exact h V.unop

instance localLinearHomModule (U : Opens T) :
    Module (R.obj.obj (op U)) (LocalLinearHom R M N U) where
  one_smul f := by
    apply localLinearHom_ext
    intro V m
    change R.obj.map V.hom.op 1 • f.val.app (op V) m = _
    rw [map_one, one_smul]
  mul_smul r s f := by
    apply localLinearHom_ext
    intro V m
    change R.obj.map V.hom.op (r * s) • f.val.app (op V) m =
      R.obj.map V.hom.op r • (R.obj.map V.hom.op s • f.val.app (op V) m)
    rw [map_mul, mul_smul]
  smul_zero r := by
    apply localLinearHom_ext
    intro V m
    change R.obj.map V.hom.op r • (0 : N.val.obj (op V.left)) = 0
    exact smul_zero _
  smul_add r f g := by
    apply localLinearHom_ext
    intro V m
    change R.obj.map V.hom.op r • (f.val.app (op V) m + g.val.app (op V) m) =
      R.obj.map V.hom.op r • f.val.app (op V) m +
        R.obj.map V.hom.op r • g.val.app (op V) m
    exact smul_add _ _ _
  add_smul r s f := by
    apply localLinearHom_ext
    intro V m
    change R.obj.map V.hom.op (r + s) • f.val.app (op V) m =
      R.obj.map V.hom.op r • f.val.app (op V) m +
        R.obj.map V.hom.op s • f.val.app (op V) m
    rw [map_add, add_smul]
  zero_smul f := by
    apply localLinearHom_ext
    intro V m
    change R.obj.map V.hom.op 0 • f.val.app (op V) m = 0
    rw [map_zero, zero_smul]

end CycleQ2GeometricIntrinsicNormal
end

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricIntrinsicNormal

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf

section LocalHom

variable {T : TopCat.{0}} (R : T.Sheaf CommRingCat.{0})
  (M N : SheafOfModules.{0} (ringSheaf R))

def restrictLocalLinearHom {U V : (Opens T)ᵒᵖ} (h : U ⟶ V) :
    LocalLinearHom R M N U.unop →+ LocalLinearHom R M N V.unop where
  toFun f := ⟨(presheafHom M.val.presheaf N.val.presheaf).map h f.val,
    (linearHomSubfunctor R M N).map h f.property⟩
  map_zero' := by
    apply Subtype.ext
    rfl
  map_add' f g := by
    apply Subtype.ext
    rfl

def moduleHomAdditivePresheaf : T.Presheaf AddCommGrpCat.{0} where
  obj U := AddCommGrpCat.of (LocalLinearHom R M N U.unop)
  map h := AddCommGrpCat.ofHom (restrictLocalLinearHom R M N h)
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      ((presheafHom M.val.presheaf N.val.presheaf).map_id U) f.val
  map_comp h k := by
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      ((presheafHom M.val.presheaf N.val.presheaf).map_comp h k) f.val

local instance localLinearRingModule (U : (Opens T)ᵒᵖ) :
    Module ((ringSheaf R).obj.obj U) (LocalLinearHom R M N U.unop) := by
  change Module (R.obj.obj (op U.unop)) (LocalLinearHom R M N U.unop)
  infer_instance

local instance moduleHomObjModule (U : (Opens T)ᵒᵖ) :
    Module ((ringSheaf R).obj.obj U) ((moduleHomAdditivePresheaf R M N).obj U) := by
  change Module ((ringSheaf R).obj.obj U) (LocalLinearHom R M N U.unop)
  infer_instance

theorem restrictLocalLinearHom_smul {U V : (Opens T)ᵒᵖ} (h : U ⟶ V)
    (r : (ringSheaf R).obj.obj U) (f : LocalLinearHom R M N U.unop) :
    restrictLocalLinearHom R M N h (r • f) =
      (ringSheaf R).obj.map h r • restrictLocalLinearHom R M N h f := by
  apply localLinearHom_ext
  intro W m
  let n : N.val.obj (op W.left) := f.val.app (op ((Over.map h.unop).obj W)) m
  change R.obj.map (W.hom ≫ h.unop).op r • n =
    R.obj.map W.hom.op (R.obj.map h r) • n
  exact congrArg (fun a : R.obj.obj (op W.left) =>
    a • n)
    (ConcreteCategory.congr_hom (R.obj.map_comp h W.hom.op) r)

def moduleHomPresheaf : PresheafOfModules.{0} (ringSheaf R).obj :=
  PresheafOfModules.ofPresheaf (moduleHomAdditivePresheaf R M N)
    (fun {_ _} h r f => restrictLocalLinearHom_smul R M N h r f)

theorem moduleHomPresheaf_isSheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology T)
      (moduleHomPresheaf R M N).presheaf := by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget AddCommGrpCat.{0})
  change Presheaf.IsSheaf (Opens.grothendieckTopology T)
    (linearHomSubfunctor R M N).toFunctor
  exact (isSheaf_iff_isSheaf_of_type _ _).mpr (linearHomSubfunctor_isSheaf R M N)

/-- The intrinsic internal Hom module sheaf, defined by linear morphisms on
all subopens. No trivialization or local freeness enters the construction. -/
def moduleHomSheaf : SheafOfModules.{0} (ringSheaf R) :=
  ⟨moduleHomPresheaf R M N, moduleHomPresheaf_isSheaf R M N⟩

/-- Evaluation of a local morphism at the entire open. -/
def localLinearHomEvaluate (U : Opens T) (f : LocalLinearHom R M N U) :
    M.val.obj (op U) →ₗ[R.obj.obj (op U)] N.val.obj (op U) where
  toFun := f.val.app (op (Over.mk (𝟙 U)))
  map_add' a b := (f.val.app (op (Over.mk (𝟙 U)))).hom.map_add a b
  map_smul' r m := f.property (Over.mk (𝟙 U)) r m

end LocalHom

section Normal

variable {X Y : Scheme.{0}} (j : X ⟶ Y)

/-- The direct-image normal module sheaf intrinsic to the actual ideal of
the scheme morphism: Hom(I, j_* O_X). -/
def normalDirectImageSheaf : SheafOfModules.{0} (ringSheaf Y.sheaf) :=
  moduleHomSheaf Y.sheaf (kernelIdealSheaf j) (imageStructureModule j)

def normalSectionEvaluate (U : Y.Opens)
    (f : (normalDirectImageSheaf j).val.obj (op U)) :
    RingHom.ker (j.app U).hom →ₗ[Γ(Y, U)] (imageStructureModule j).val.obj (op U) :=
  (localLinearHomEvaluate Y.sheaf (kernelIdealSheaf j) (imageStructureModule j) U f).comp
    (kernelIdealSectionEquiv j U).symm.toLinearMap

end Normal

#print axioms moduleHomPresheaf_isSheaf
#print axioms normalSectionEvaluate

end CycleQ2GeometricIntrinsicNormal
end

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricIntrinsicNormal

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf

section LocalHom

variable {T : TopCat.{0}} (R : T.Sheaf CommRingCat.{0})
  (M N : SheafOfModules.{0} (ringSheaf R))

/-- Local linear natural transformations are exactly morphisms between the
restricted module sheaves. -/
def localLinearHomEquiv (U : Opens T) :
    LocalLinearHom R M N U ≃ (M.over U ⟶ N.over U) where
  toFun f := ⟨PresheafOfModules.homMk f.val (fun V r m => f.property V.unop r m)⟩
  invFun f :=
    ⟨(PresheafOfModules.toPresheaf ((ringSheaf R).over U).obj).map f.val,
      fun V r m => (f.val.app (op V)).hom.map_smul r m⟩
  left_inv f := by
    apply Subtype.ext
    rfl
  right_inv f := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    rfl

theorem localLinearHomEvaluate_restrict {U V : Opens T} (h : V ⟶ U)
    (f : LocalLinearHom R M N U) (m : M.val.obj (op U)) :
    localLinearHomEvaluate R M N V (restrictLocalLinearHom R M N h.op f)
      (M.val.map h.op m) =
    N.val.map h.op (localLinearHomEvaluate R M N U f m) := by
  have e := presheafHom_map_app_op_mk_id
    (F := M.val.presheaf) (G := N.val.presheaf) h f.val
  have hn := ConcreteCategory.congr_hom
    (f.val.naturality (Over.homMk h : Over.mk h ⟶ Over.mk (𝟙 U)).op) m
  exact (ConcreteCategory.congr_hom e _).trans hn

end LocalHom

section Normal

variable {X Y : Scheme.{0}} (j : X ⟶ Y)

/-- Restriction in the intrinsic ideal sheaf, expressed on the literal
kernel ideals of the maps of section rings. -/
def kernelSectionRestrict {U V : Y.Opens} (h : V ⟶ U)
    (a : RingHom.ker (j.app U).hom) : RingHom.ker (j.app V).hom :=
  kernelIdealSectionEquiv j V ((kernelIdealSheaf j).val.map h.op
    ((kernelIdealSectionEquiv j U).symm a))

@[simp] theorem kernelSectionRestrict_coe {U V : Y.Opens} (h : V ⟶ U)
    (a : RingHom.ker (j.app U).hom) :
    (kernelSectionRestrict j h a : Γ(Y, V)) = Y.presheaf.map h.op a := by
  change (kernelIdealSectionEquiv j V ((kernelIdealSheaf j).val.map h.op
    ((kernelIdealSectionEquiv j U).symm a)) : Γ(Y, V)) = _
  rw [kernelIdealSectionEquiv_restrict]
  exact congrArg (fun b : RingHom.ker (j.app U).hom => Y.presheaf.map h.op b)
    ((kernelIdealSectionEquiv j U).apply_symm_apply a)

/-- The canonical map on the actual conormal quotients induced by restriction
of the scheme's section rings. -/
def kernelCotangentRestriction {U V : Y.Opens} (h : V ⟶ U) :
    (RingHom.ker (j.app U).hom).Cotangent →ₗ[ℤ]
      (RingHom.ker (j.app V).hom).Cotangent :=
  Ideal.mapCotangent (RingHom.ker (j.app U).hom) (RingHom.ker (j.app V).hom)
    (Y.presheaf.map h.op).hom.toIntAlgHom (by
      intro a ha
      change Y.presheaf.map h.op a ∈ RingHom.ker (j.app V).hom
      exact (congrArg (fun b : Γ(Y, V) => b ∈ RingHom.ker (j.app V).hom)
        (kernelSectionRestrict_coe j h ⟨a, ha⟩)).mp
        (kernelSectionRestrict j h ⟨a, ha⟩).property)

@[simp] theorem kernelCotangentRestriction_toCotangent {U V : Y.Opens}
    (h : V ⟶ U) (a : RingHom.ker (j.app U).hom) :
    kernelCotangentRestriction j h ((RingHom.ker (j.app U).hom).toCotangent a) =
      (RingHom.ker (j.app V).hom).toCotangent (kernelSectionRestrict j h a) := by
  exact congrArg (RingHom.ker (j.app V).hom).toCotangent
    (Subtype.ext (kernelSectionRestrict_coe j h a).symm)

theorem normalSectionEvaluate_restrict {U V : Y.Opens} (h : V ⟶ U)
    (f : (normalDirectImageSheaf j).val.obj (op U))
    (a : RingHom.ker (j.app U).hom) :
    normalSectionEvaluate j V ((normalDirectImageSheaf j).val.map h.op f)
      (kernelSectionRestrict j h a) =
    (imageStructureModule j).val.map h.op (normalSectionEvaluate j U f a) := by
  have hn := localLinearHomEvaluate_restrict Y.sheaf (kernelIdealSheaf j)
    (imageStructureModule j) h f ((kernelIdealSectionEquiv j U).symm a)
  have he := (kernelIdealSectionEquiv j V).symm_apply_apply
    ((kernelIdealSheaf j).val.map h.op ((kernelIdealSectionEquiv j U).symm a))
  exact (congrArg
    (localLinearHomEvaluate Y.sheaf (kernelIdealSheaf j) (imageStructureModule j) V
      (restrictLocalLinearHom Y.sheaf (kernelIdealSheaf j) (imageStructureModule j) h.op f))
    he).trans hn

/-- An intrinsic normal functional annihilates products in the actual ideal.
Thus the construction is the dual conormal, rather than a free frame model. -/
theorem normalSectionEvaluate_product (U : Y.Opens)
    (f : (normalDirectImageSheaf j).val.obj (op U))
    (a b : RingHom.ker (j.app U).hom) :
    normalSectionEvaluate j U f (a * b) = 0 := by
  have h := (normalSectionEvaluate j U f).map_smul (a : Γ(Y, U)) b
  let n : Γ(X, j ⁻¹ᵁ U) := normalSectionEvaluate j U f b
  change normalSectionEvaluate j U f (a * b) =
    (j.app U (a : Γ(Y, U))) * n at h
  have ha : j.app U (a : Γ(Y, U)) = 0 := a.property
  exact h.trans ((congrArg (fun x : Γ(X, j ⁻¹ᵁ U) =>
    x * n) ha).trans (zero_mul _))

/-- Evaluation factors canonically through the actual quotient I/I². -/
def normalSectionCotangent (U : Y.Opens)
    (f : (normalDirectImageSheaf j).val.obj (op U)) :
    (RingHom.ker (j.app U).hom).Cotangent →ₗ[Γ(Y, U)]
      (imageStructureModule j).val.obj (op U) :=
  Ideal.Cotangent.lift (normalSectionEvaluate j U f)
    (normalSectionEvaluate_product j U f)

@[simp] theorem normalSectionCotangent_toCotangent (U : Y.Opens)
    (f : (normalDirectImageSheaf j).val.obj (op U))
    (a : RingHom.ker (j.app U).hom) :
    normalSectionCotangent j U f ((RingHom.ker (j.app U).hom).toCotangent a) =
      normalSectionEvaluate j U f a := rfl

theorem normalSectionCotangent_unique (U : Y.Opens)
    (f : (normalDirectImageSheaf j).val.obj (op U))
    (g : (RingHom.ker (j.app U).hom).Cotangent →ₗ[Γ(Y, U)]
      (imageStructureModule j).val.obj (op U))
    (hg : ∀ a, g ((RingHom.ker (j.app U).hom).toCotangent a) =
      normalSectionEvaluate j U f a) :
    g = normalSectionCotangent j U f := by
  apply LinearMap.ext
  intro a
  obtain ⟨b, rfl⟩ := (RingHom.ker (j.app U).hom).toCotangent_surjective a
  exact hg b

/-- The factorization through I/I² commutes with restriction on every open. -/
theorem normalSectionCotangent_restrict {U V : Y.Opens} (h : V ⟶ U)
    (f : (normalDirectImageSheaf j).val.obj (op U))
    (a : (RingHom.ker (j.app U).hom).Cotangent) :
    normalSectionCotangent j V ((normalDirectImageSheaf j).val.map h.op f)
      (kernelCotangentRestriction j h a) =
    (imageStructureModule j).val.map h.op (normalSectionCotangent j U f a) := by
  obtain ⟨b, rfl⟩ := (RingHom.ker (j.app U).hom).toCotangent_surjective a
  exact (congrArg
    (normalSectionCotangent j V ((normalDirectImageSheaf j).val.map h.op f))
    (kernelCotangentRestriction_toCotangent j h b)).trans
      (normalSectionEvaluate_restrict j h f b)

end Normal

def literalNormalDirectImageSheaf (r θ : ℂ) :
    SheafOfModules.{0}
      (ringSheaf (CycleQ2GeometricLiteralSurface.surface r θ).sheaf) :=
  normalDirectImageSheaf (CycleQ2GeometricLiteralSurface.curveToSurface r θ)

#print axioms normalSectionEvaluate_restrict
#print axioms normalSectionCotangent
#print axioms literalNormalDirectImageSheaf

end CycleQ2GeometricIntrinsicNormal
end


set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped TensorProduct
namespace CycleQ2GeometricIntrinsicNormal

section NormalFunctional
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable (I : Ideal A) (hI : ∀ a ∈ I, algebraMap A B a=0)

include hI in
theorem idealFunctional_product (φ : I →ₗ[A] B) (a b : I) : φ (a*b)=0 := by
  have h := φ.map_smul (a:A) b
  have hab : (a:A) • b=a*b := Subtype.ext rfl
  rw [hab,Algebra.smul_def,hI a a.property,zero_mul] at h
  exact h

/-- Every functional into the actual curve algebra kills I², so the
conormal quotient changes no such functional. -/
def idealCotangentHomEquiv : (I →ₗ[A] B) ≃ₗ[B] (I.Cotangent →ₗ[A] B) where
  toFun φ := Ideal.Cotangent.lift φ (idealFunctional_product I hI φ)
  invFun ψ := ψ.comp I.toCotangent
  left_inv φ := by
    ext a
    rfl
  right_inv ψ := by
    ext a
    obtain ⟨b,rfl⟩ := I.toCotangent_surjective a
    rfl
  map_add' φ ψ := by
    ext a
    obtain ⟨b,rfl⟩ := I.toCotangent_surjective a
    rfl
  map_smul' c φ := by
    ext a
    obtain ⟨b,rfl⟩ := I.toCotangent_surjective a
    rfl

@[simp] theorem idealCotangentHomEquiv_toCotangent (φ : I →ₗ[A] B) (a : I) :
    idealCotangentHomEquiv I hI φ (I.toCotangent a)=φ a := rfl

@[simp] theorem idealCotangentHomEquiv_symm_apply (φ : I.Cotangent →ₗ[A] B) (a : I) :
    (idealCotangentHomEquiv I hI).symm φ a=φ (I.toCotangent a) := rfl

/-- The algebraic ideal functional and the base-changed conormal dual
are canonically equivalent; both maps are fixed on actual ideal elements. -/
def normalFunctionalEquiv :
    (I →ₗ[A] B) ≃ₗ[B] (B ⊗[A] I.Cotangent →ₗ[B] B) :=
  (idealCotangentHomEquiv I hI).trans (LinearMap.liftBaseChangeEquiv B)

@[simp] theorem normalFunctionalEquiv_tmul (φ : I →ₗ[A] B) (b : B) (a : I) :
    normalFunctionalEquiv I hI φ (b ⊗ₜ[A] I.toCotangent a)=b*φ a := rfl

@[simp] theorem normalFunctionalEquiv_symm_apply
    (φ : B ⊗[A] I.Cotangent →ₗ[B] B) (a : I) :
    (normalFunctionalEquiv I hI).symm φ a=φ ((1:B) ⊗ₜ[A] I.toCotangent a) := rfl

theorem normalFunctionalEquiv_unique (φ : I →ₗ[A] B)
    (ψ : B ⊗[A] I.Cotangent →ₗ[B] B)
    (hψ : ∀ a : I, ψ ((1:B) ⊗ₜ[A] I.toCotangent a)=φ a) :
    ψ=normalFunctionalEquiv I hI φ := by
  apply (normalFunctionalEquiv I hI).symm.injective
  ext a
  change ψ ((1:B) ⊗ₜ[A] I.toCotangent a)=_
  rw [LinearEquiv.symm_apply_apply]
  exact hψ a

variable {C : Type*} [CommRing C] [Algebra A C]
variable (ρ : B →ₐ[A] C) (hC : ∀ a ∈ I, algebraMap A C a=0)

/-- Scalar extension carries the same functional values through the actual
coefficient map, including the normalization at 1 tensor [a]. -/
theorem normalFunctionalEquiv_coefficientMap (φ : I →ₗ[A] B) (c : C) (a : I) :
    normalFunctionalEquiv I hC (ρ.toLinearMap.comp φ) (c ⊗ₜ[A] I.toCotangent a)=
      c * ρ (normalFunctionalEquiv I hI φ ((1:B) ⊗ₜ[A] I.toCotangent a)) := by
  simp only [normalFunctionalEquiv_tmul,LinearMap.comp_apply,AlgHom.toLinearMap_apply,one_mul]

end NormalFunctional

#print axioms normalFunctionalEquiv
#print axioms normalFunctionalEquiv_coefficientMap
end CycleQ2GeometricIntrinsicNormal
end


set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricIntrinsicNormal
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

section Algebra

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
  (S : Submonoid A) [IsLocalization S B]
  {M N ML NL : Type} [AddCommGroup M] [AddCommGroup N]
  [AddCommGroup ML] [AddCommGroup NL]
  [Module A M] [Module A N] [Module A ML] [Module A NL]
  [Module B ML] [Module B NL] [IsScalarTower A B ML] [IsScalarTower A B NL]
  (a : M →ₗ[A] ML) (b : N →ₗ[A] NL)
  [IsLocalizedModule S a] [IsLocalizedModule S b]
  (f : M →ₗ[A] N) (g : ML →ₗ[A] NL) (h : g.comp a = b.comp f)

def kernelSquareMap : f.ker →ₗ[A] g.ker :=
  a.restrict (fun m hm => by
    change g (a m) = 0
    have he := LinearMap.congr_fun h m
    exact he.trans ((congrArg b (LinearMap.mem_ker.mp hm)).trans b.map_zero))

include B in
theorem kernelSquareMap_isLocalized : IsLocalizedModule S (kernelSquareMap a b f g h) := by
  have hg : g = IsLocalizedModule.map S a b f := by
    apply IsLocalizedModule.ext S a (IsLocalizedModule.map_units b)
    exact h.trans (IsLocalizedModule.map_comp S a b f).symm
  subst g
  exact LinearMap.toKerLocalized_isLocalizedModule B S a b f

end Algebra

section Tilde

variable (A : CommRingCat.{0})

def affineEvaluation (U : (Spec A).Opens) : (Spec A).Modules ⥤ ModuleCat A :=
  modulesSpecToSheaf ⋙ TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (op U)

instance affineEvaluation_additive (U : (Spec A).Opens) :
    (affineEvaluation A U).Additive where
  map_add := by intros; rfl

instance affineEvaluation_preservesFiniteLimits (U : (Spec A).Opens) :
    PreservesFiniteLimits (affineEvaluation A U) where
  preservesFiniteLimits J _ _ := by
    let : PreservesLimitsOfShape J
        (affineEvaluation A U ⋙ forget₂ (ModuleCat A) AddCommGrpCat) := by
      change PreservesLimitsOfShape J
        (SheafOfModules.evaluation (Spec A).ringCatSheaf (op U) ⋙
          forget₂ (ModuleCat Γ(Spec A, U)) AddCommGrpCat)
      infer_instance
    exact preservesLimitsOfShape_of_reflects_of_preserves (affineEvaluation A U)
      (forget₂ (ModuleCat A) AddCommGrpCat)

variable {A} {M N : (Spec A).Modules} (f : M ⟶ N)

def affineKernelSectionIso (U : (Spec A).Opens) :
    (affineEvaluation A U).obj (kernel f) ≅
      ModuleCat.of A ((affineEvaluation A U).map f).hom.ker :=
  PreservesKernel.iso (affineEvaluation A U) f ≪≫
    ModuleCat.kernelIsoKer ((affineEvaluation A U).map f)

def affineKernelSectionEquiv (U : (Spec A).Opens) :
    (affineEvaluation A U).obj (kernel f) ≃ₗ[A]
      ((affineEvaluation A U).map f).hom.ker :=
  (affineKernelSectionIso f U).toLinearEquiv

theorem affineKernelSectionEquiv_coe (U : (Spec A).Opens)
    (a : (affineEvaluation A U).obj (kernel f)) :
    (affineKernelSectionEquiv f U a : (affineEvaluation A U).obj M) =
      (affineEvaluation A U).map (kernel.ι f) a := by
  have h : (affineKernelSectionIso f U).hom ≫
      ModuleCat.ofHom ((affineEvaluation A U).map f).hom.ker.subtype =
        (affineEvaluation A U).map (kernel.ι f) := by
    change ((PreservesKernel.iso (affineEvaluation A U) f).hom ≫
      (ModuleCat.kernelIsoKer ((affineEvaluation A U).map f)).hom) ≫ _ = _
    rw [Category.assoc]
    exact (congrArg ((PreservesKernel.iso (affineEvaluation A U) f).hom ≫ ·)
      (ModuleCat.kernelIsoKer_hom_ker_subtype ((affineEvaluation A U).map f))).trans
      (kernelComparison_comp_ι f (affineEvaluation A U))
  exact ConcreteCategory.congr_hom h a

theorem affineKernelSectionEquiv_restrict {U V : (Spec A).Opens} (h : V ⟶ U)
    (a : (affineEvaluation A U).obj (kernel f)) :
    (affineKernelSectionEquiv f V
      ((modulesSpecToSheaf.obj (kernel f)).obj.map h.op a) :
        (affineEvaluation A V).obj M) =
      (modulesSpecToSheaf.obj M).obj.map h.op (affineKernelSectionEquiv f U a).val := by
  rw [affineKernelSectionEquiv_coe, affineKernelSectionEquiv_coe]
  exact ConcreteCategory.congr_hom
    ((modulesSpecToSheaf.map (kernel.ι f)).hom.naturality h.op) a

theorem kernel_isLocalizing
    (hM : IsLocalizing (modulesSpecToSheaf.obj M))
    (hN : IsLocalizing (modulesSpecToSheaf.obj N)) :
    IsLocalizing (modulesSpecToSheaf.obj (kernel f)) := by
  intro r
  let U : (Spec A).Opens := PrimeSpectrum.basicOpen r
  let a := ((modulesSpecToSheaf.obj M).obj.map U.leTop.op).hom
  let b := ((modulesSpecToSheaf.obj N).obj.map U.leTop.op).hom
  let k := ((modulesSpecToSheaf.obj (kernel f)).obj.map U.leTop.op).hom
  let f₀ := ((affineEvaluation A ⊤).map f).hom
  let f₁ := ((affineEvaluation A U).map f).hom
  let e₀ := affineKernelSectionEquiv f ⊤
  let e₁ := affineKernelSectionEquiv f U
  have h : f₁.comp a = b.comp f₀ :=
    congrArg ModuleCat.Hom.hom ((modulesSpecToSheaf.map f).hom.naturality U.leTop.op)
  let : IsLocalizedModule (Submonoid.powers r) a := hM r
  let : IsLocalizedModule (Submonoid.powers r) b := hN r
  let : Module Γ(Spec A, U) ((modulesSpecToSheaf.obj M).obj.obj (op U)) :=
    inferInstanceAs (Module Γ(Spec A, U) Γ(M, U))
  let : Module Γ(Spec A, U) ((modulesSpecToSheaf.obj N).obj.obj (op U)) :=
    inferInstanceAs (Module Γ(Spec A, U) Γ(N, U))
  let : IsScalarTower A Γ(Spec A, U) ((modulesSpecToSheaf.obj M).obj.obj (op U)) :=
    inferInstanceAs (IsScalarTower A Γ(Spec A, U) Γ(M, U))
  let : IsScalarTower A Γ(Spec A, U) ((modulesSpecToSheaf.obj N).obj.obj (op U)) :=
    inferInstanceAs (IsScalarTower A Γ(Spec A, U) Γ(N, U))
  have hk : IsLocalizedModule (Submonoid.powers r) (kernelSquareMap a b f₀ f₁ h) :=
    kernelSquareMap_isLocalized (B := Γ(Spec A, U)) (Submonoid.powers r) a b f₀ f₁ h
  have he : e₁.toLinearMap.comp k = (kernelSquareMap a b f₀ f₁ h).comp e₀.toLinearMap := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact affineKernelSectionEquiv_restrict f U.leTop x
  apply (IsLocalizedModule.comp_iff_of_bijective_left (Submonoid.powers r)
    e₁.toLinearMap e₁.bijective).mp
  change IsLocalizedModule (Submonoid.powers r) (e₁.toLinearMap.comp k)
  rw [he]
  exact (IsLocalizedModule.comp_iff_of_bijective_right (Submonoid.powers r)
    e₀.toLinearMap e₀.bijective).mpr hk

end Tilde
end CycleQ2GeometricIntrinsicNormal
end

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricIntrinsicNormal
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf

section GlobalHom

variable {T : TopCat.{0}} (R : T.Sheaf CommRingCat.{0})
  (M N : SheafOfModules.{0} (ringSheaf R))

def localLinearHomTopEquiv :
    LocalLinearHom R M N ⊤ ≃ (M ⟶ N) where
  toFun f :=
    ⟨PresheafOfModules.homMk
      { app U := f.val.app (op (Over.mk (homOfLE (show U.unop ≤ ⊤ from le_top))))
        naturality {U V} h := f.val.naturality
          (Over.homMk h.unop :
            Over.mk (homOfLE (show V.unop ≤ ⊤ from le_top)) ⟶
              Over.mk (homOfLE (show U.unop ≤ ⊤ from le_top))).op }
      (fun U r m => f.property (Over.mk (homOfLE le_top)) r m)⟩
  invFun f :=
    ⟨Functor.whiskerLeft (Over.forget (⊤ : Opens T)).op
      ((PresheafOfModules.toPresheaf (ringSheaf R).obj).map f.val),
      fun U r m => (f.val.app (op U.left)).hom.map_smul r m⟩
  left_inv f := by
    apply Subtype.ext
    rfl
  right_inv f := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    rfl

@[simp] theorem localLinearHomTopEquiv_app
    (f : LocalLinearHom R M N ⊤) (U : Opens T) (m : M.val.obj (op U)) :
    (localLinearHomTopEquiv R M N f).val.app (op U) m =
      f.val.app (op (Over.mk (homOfLE (show U ≤ ⊤ from le_top)))) m := rfl

end GlobalHom

section Affine

variable {A B : CommRingCat.{0}} (φ : A ⟶ B)

theorem imageStructureModule_eq_pushforward :
    imageStructureModule (Spec.map φ) =
      (Scheme.Modules.pushforward (Spec.map φ)).obj
        (SheafOfModules.unit (Spec B).ringCatSheaf) := rfl

theorem affineIdeal_isLocalizing :
    IsLocalizing (modulesSpecToSheaf.obj
      (show (Spec A).Modules from kernelIdealSheaf (Spec.map φ))) := by
  apply kernel_isLocalizing (f := schemeStructureMap (Spec.map φ))
  · exact (isIso_fromTildeΓ_iff_isLocalizing
      (SheafOfModules.unit (Spec A).ringCatSheaf)).mp inferInstance
  · have h := isIso_fromTildeΓ_pushforward φ (SheafOfModules.unit (Spec B).ringCatSheaf)
    exact (isIso_fromTildeΓ_iff_isLocalizing
      ((Scheme.Modules.pushforward (Spec.map φ)).obj
        (SheafOfModules.unit (Spec B).ringCatSheaf))).mp h

instance affineIdeal_fromTildeΓ_isIso :
    IsIso ((show (Spec A).Modules from kernelIdealSheaf (Spec.map φ)).fromTildeΓ) :=
  (isIso_fromTildeΓ_iff_isLocalizing _).mpr (affineIdeal_isLocalizing φ)

variable (M N : (Spec A).Modules) [IsIso M.fromTildeΓ]

/-- Every map of global modules extends uniquely from a quasicoherent affine
source. This equivalence is the tilde--Gamma adjunction, not a chosen extension. -/
def affineModuleHomEquiv :
    (M ⟶ N) ≃ ((affineEvaluation A ⊤).obj M ⟶ (affineEvaluation A ⊤).obj N) :=
  (Iso.homCongr (asIso M.fromTildeΓ).symm (Iso.refl N)).trans
    (tilde.adjunction.homEquiv _ _)

theorem affineModuleHomEquiv_apply (f : M ⟶ N) :
    affineModuleHomEquiv M N f = (affineEvaluation A ⊤).map f := by
  change tilde.adjunction.homEquiv _ _ (M.fromTildeΓ ≫ f ≫ 𝟙 N) = _
  rw [Category.comp_id, tilde.adjunction.homEquiv_naturality_right]
  have he : tilde.adjunction.homEquiv _ _ M.fromTildeΓ = 𝟙 _ :=
    (congrArg (tilde.adjunction.homEquiv _ _)
      (tilde.adjunction.homEquiv_symm_id M).symm).trans
      ((tilde.adjunction.homEquiv _ _).apply_symm_apply (𝟙 _))
  rw [he, Category.id_comp]
  rfl

end Affine

#print axioms affineIdeal_isLocalizing
#print axioms affineModuleHomEquiv
#print axioms affineModuleHomEquiv_apply

end CycleQ2GeometricIntrinsicNormal
end

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricIntrinsicNormal
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf

section ModuleHom

variable {A : CommRingCat.{0}} (M N : (Spec A).Modules) [IsIso M.fromTildeΓ]

local instance affineTopModule : Module A (M.val.obj (op ⊤)) :=
  inferInstanceAs (Module A Γ(M, ⊤))

local instance affineTopTower : IsScalarTower A Γ(Spec A, ⊤) (M.val.obj (op ⊤)) :=
  inferInstanceAs (IsScalarTower A Γ(Spec A, ⊤) Γ(M, ⊤))

local instance affineTopCompatible :
    LinearMap.CompatibleSMul (M.val.obj (op ⊤)) (N.val.obj (op ⊤)) A
      ((Spec A).ringCatSheaf.obj.obj (op ⊤)) :=
  inferInstanceAs (LinearMap.CompatibleSMul Γ(M, ⊤) Γ(N, ⊤) A Γ(Spec A, ⊤))

theorem affineModule_top_app_bijective :
    Function.Bijective (fun f : M ⟶ N => (f.val.app (op ⊤)).hom) := by
  constructor
  · intro f g h
    apply (affineModuleHomEquiv M N).injective
    rw [affineModuleHomEquiv_apply, affineModuleHomEquiv_apply]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun h x
  · intro f
    let g : (affineEvaluation A ⊤).obj M ⟶ (affineEvaluation A ⊤).obj N :=
      ModuleCat.ofHom (X := (affineEvaluation A ⊤).obj M)
        (Y := (affineEvaluation A ⊤).obj N) (f.restrictScalars A)
    let F := (affineModuleHomEquiv M N).symm g
    refine ⟨F, ?_⟩
    have h : (affineEvaluation A ⊤).map F = g :=
      (affineModuleHomEquiv_apply M N F).symm.trans
        ((affineModuleHomEquiv M N).apply_symm_apply g)
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom h x

/-- Evaluation at the whole affine scheme is an equivalence for a
quasicoherent source, retaining the full actual section-ring linearity. -/
def affineTopLinearMapEquiv :
    (M ⟶ N) ≃ (M.val.obj (op ⊤) →ₗ[Γ(Spec A, ⊤)] N.val.obj (op ⊤)) :=
  Equiv.ofBijective (fun f => (f.val.app (op ⊤)).hom)
    (affineModule_top_app_bijective M N)

@[simp] theorem affineTopLinearMapEquiv_apply (f : M ⟶ N) :
    affineTopLinearMapEquiv M N f = (f.val.app (op ⊤)).hom := rfl

end ModuleHom

section EvaluationLinearity

variable {X Y : Scheme.{0}} (j : X ⟶ Y)

def normalSectionEvaluationLinearMap (U : Y.Opens) :
    (normalDirectImageSheaf j).val.obj (op U) →ₗ[Γ(Y, U)]
      (RingHom.ker (j.app U).hom →ₗ[Γ(Y, U)] (imageStructureModule j).val.obj (op U)) where
  toFun := normalSectionEvaluate j U
  map_add' f g := by
    apply LinearMap.ext
    intro a
    rfl
  map_smul' r f := by
    apply LinearMap.ext
    intro a
    let v : (imageStructureModule j).val.obj (op U) := normalSectionEvaluate j U f a
    change Y.presheaf.map (𝟙 (op U)) r • v = r • v
    exact congrArg (fun s : Γ(Y, U) => s • v)
      (ConcreteCategory.congr_hom (Y.presheaf.map_id (op U)) r)

end EvaluationLinearity

section Normal

variable {A B : CommRingCat.{0}} (φ : A ⟶ B)

/-- Actual normal sheaf sections on an affine scheme are exactly the
algebraic functionals on the actual ideal of the section-ring map. -/
def affineNormalSectionEquiv :
    (normalDirectImageSheaf (Spec.map φ)).val.obj (op ⊤) ≃
      (RingHom.ker ((Spec.map φ).app ⊤).hom →ₗ[Γ(Spec A, ⊤)]
        (imageStructureModule (Spec.map φ)).val.obj (op ⊤)) :=
  (localLinearHomTopEquiv (Spec A).sheaf (kernelIdealSheaf (Spec.map φ))
      (imageStructureModule (Spec.map φ))).trans
    ((affineTopLinearMapEquiv
      (show (Spec A).Modules from kernelIdealSheaf (Spec.map φ))
      (show (Spec A).Modules from imageStructureModule (Spec.map φ))).trans
        ((kernelIdealSectionEquiv (Spec.map φ) ⊤).arrowCongr
          (LinearEquiv.refl Γ(Spec A, ⊤)
            ((imageStructureModule (Spec.map φ)).val.obj (op ⊤)))).toEquiv)

@[simp] theorem affineNormalSectionEquiv_apply
    (f : (normalDirectImageSheaf (Spec.map φ)).val.obj (op ⊤)) :
    affineNormalSectionEquiv φ f = normalSectionEvaluate (Spec.map φ) ⊤ f := rfl

theorem affineNormalSectionEvaluate_bijective :
    Function.Bijective (normalSectionEvaluate (Spec.map φ) ⊤) :=
  (affineNormalSectionEquiv φ).bijective

/-- The affine comparison also retains the actual O_Y(⊤)-module structure. -/
def affineNormalSectionLinearEquiv :
    (normalDirectImageSheaf (Spec.map φ)).val.obj (op ⊤) ≃ₗ[Γ(Spec A, ⊤)]
      (RingHom.ker ((Spec.map φ).app ⊤).hom →ₗ[Γ(Spec A, ⊤)]
        (imageStructureModule (Spec.map φ)).val.obj (op ⊤)) where
  __ := affineNormalSectionEquiv φ
  map_add' := (normalSectionEvaluationLinearMap (Spec.map φ) ⊤).map_add
  map_smul' r f := (normalSectionEvaluationLinearMap (Spec.map φ) ⊤).map_smul r f

/-- Every algebraic ideal functional extends uniquely to a section of the
actual intrinsic normal sheaf over the entire affine scheme. -/
theorem affineNormalSection_existsUnique
    (l : RingHom.ker ((Spec.map φ).app ⊤).hom →ₗ[Γ(Spec A, ⊤)]
      (imageStructureModule (Spec.map φ)).val.obj (op ⊤)) :
    ∃! f : (normalDirectImageSheaf (Spec.map φ)).val.obj (op ⊤),
      normalSectionEvaluate (Spec.map φ) ⊤ f = l :=
  (affineNormalSectionEvaluate_bijective φ).existsUnique l

end Normal

#print axioms affineModule_top_app_bijective
#print axioms affineNormalSectionEquiv
#print axioms affineNormalSectionLinearEquiv
#print axioms affineNormalSection_existsUnique

end CycleQ2GeometricIntrinsicNormal
end


set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricIntrinsicNormal
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf
open scoped TensorProduct

section SectionConormal

variable {X Y : Scheme.{0}} (j : X ⟶ Y)

/-- The algebra structure induced by the literal morphism on sections. -/
@[instance_reducible] def normalSectionAlgebra (U : Y.Opens) :
    Algebra Γ(Y, U) Γ(X, j ⁻¹ᵁ U) :=
  (j.app U).hom.toAlgebra

attribute [local instance] normalSectionAlgebra

/-- The actual conormal module, extended to the actual source section ring. -/
abbrev sectionConormal (U : Y.Opens) :=
  Γ(X, j ⁻¹ᵁ U) ⊗[Γ(Y, U)] (RingHom.ker (j.app U).hom).Cotangent

/-- An intrinsic normal section acts on the actual base-changed conormal
module, with no choice of a frame or normalization. -/
def normalSectionBaseChangeMap (U : Y.Opens) :
    (normalDirectImageSheaf j).val.obj (op U) →ₗ[Γ(Y, U)]
      (sectionConormal j U →ₗ[Γ(X, j ⁻¹ᵁ U)] Γ(X, j ⁻¹ᵁ U)) :=
  ((normalFunctionalEquiv (RingHom.ker (j.app U).hom)
    (fun _a ha => ha)).restrictScalars Γ(Y, U)).toLinearMap.comp
      (normalSectionEvaluationLinearMap j U)

@[simp] theorem normalSectionBaseChangeMap_tmul (U : Y.Opens)
    (f : (normalDirectImageSheaf j).val.obj (op U))
    (b : Γ(X, j ⁻¹ᵁ U)) (a : RingHom.ker (j.app U).hom) :
    normalSectionBaseChangeMap j U f
      (b ⊗ₜ[Γ(Y, U)] (RingHom.ker (j.app U).hom).toCotangent a) =
      b * (show Γ(X, j ⁻¹ᵁ U) from normalSectionEvaluate j U f a) := rfl

end SectionConormal

section AffineConormal

variable {A B : CommRingCat.{0}} (φ : A ⟶ B)

attribute [local instance] normalSectionAlgebra

/-- On an affine scheme, the intrinsic normal sections are canonically the
dual of the actual base-changed conormal module. -/
def affineNormalConormalEquiv :
    (normalDirectImageSheaf (Spec.map φ)).val.obj (op ⊤) ≃ₗ[Γ(Spec A, ⊤)]
      (sectionConormal (Spec.map φ) ⊤ →ₗ[Γ(Spec B, (Spec.map φ) ⁻¹ᵁ ⊤)]
        Γ(Spec B, (Spec.map φ) ⁻¹ᵁ ⊤)) :=
  (affineNormalSectionLinearEquiv φ).trans
    ((normalFunctionalEquiv (RingHom.ker ((Spec.map φ).app ⊤).hom)
      (fun _a ha => ha)).restrictScalars Γ(Spec A, ⊤))

@[simp] theorem affineNormalConormalEquiv_apply
    (f : (normalDirectImageSheaf (Spec.map φ)).val.obj (op ⊤)) :
    affineNormalConormalEquiv φ f = normalSectionBaseChangeMap (Spec.map φ) ⊤ f := rfl

@[simp] theorem affineNormalConormalEquiv_tmul
    (f : (normalDirectImageSheaf (Spec.map φ)).val.obj (op ⊤))
    (b : Γ(Spec B, (Spec.map φ) ⁻¹ᵁ ⊤))
    (a : RingHom.ker ((Spec.map φ).app ⊤).hom) :
    affineNormalConormalEquiv φ f
      (b ⊗ₜ[Γ(Spec A, ⊤)] (RingHom.ker ((Spec.map φ).app ⊤).hom).toCotangent a) =
      b * (show Γ(Spec B, (Spec.map φ) ⁻¹ᵁ ⊤) from
        normalSectionEvaluate (Spec.map φ) ⊤ f a) := rfl

@[simp] theorem affineNormalConormalEquiv_symm_evaluate
    (f : sectionConormal (Spec.map φ) ⊤ →ₗ[Γ(Spec B, (Spec.map φ) ⁻¹ᵁ ⊤)]
      Γ(Spec B, (Spec.map φ) ⁻¹ᵁ ⊤))
    (a : RingHom.ker ((Spec.map φ).app ⊤).hom) :
    normalSectionEvaluate (Spec.map φ) ⊤ ((affineNormalConormalEquiv φ).symm f) a =
      f ((1 : Γ(Spec B, (Spec.map φ) ⁻¹ᵁ ⊤)) ⊗ₜ[Γ(Spec A, ⊤)]
        (RingHom.ker ((Spec.map φ).app ⊤).hom).toCotangent a) := by
  have h := LinearMap.congr_fun
    ((affineNormalConormalEquiv φ).apply_symm_apply f)
    ((1 : Γ(Spec B, (Spec.map φ) ⁻¹ᵁ ⊤)) ⊗ₜ[Γ(Spec A, ⊤)]
      (RingHom.ker ((Spec.map φ).app ⊤).hom).toCotangent a)
  simpa only [affineNormalConormalEquiv_tmul, one_mul] using h

end AffineConormal

#print axioms normalSectionBaseChangeMap
#print axioms affineNormalConormalEquiv
#print axioms affineNormalConormalEquiv_symm_evaluate

end CycleQ2GeometricIntrinsicNormal
end


/-!
# Intrinsic normal sections on actual affine charts

Restriction and cartesian open base change transport the actual kernel ideal
and its normal functionals. The final equivalence uses the original affine
coordinate rings, and the generator formulas fix both coefficient maps.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricIntrinsicNormal
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf

variable {Y : Scheme.{0}} (M N : Y.Modules)

/-- Local linear Hom sections agree with actual morphisms of module sheaves
on the corresponding open subscheme. -/
def localLinearHomRestrictEquiv (U : Y.Opens) :
    LocalLinearHom Y.sheaf M N U ≃ (M.restrict U.ι ⟶ N.restrict U.ι) :=
  (localLinearHomEquiv Y.sheaf M N U).trans
    ((Scheme.Modules.overEquiv U).fullyFaithfulFunctor.homEquiv.trans
      (Iso.homCongr ((Scheme.Modules.overFunctorEquiv U).app M)
        ((Scheme.Modules.overFunctorEquiv U).app N)))

@[simp] theorem localLinearHomRestrictEquiv_app (U : Y.Opens)
    (f : LocalLinearHom Y.sheaf M N U) (V : U.toScheme.Opens)
    (x : M.val.obj (op (U.ι ''ᵁ V))) :
    (localLinearHomRestrictEquiv M N U f).val.app (op V) x =
      f.val.app (op (Over.mk (homOfLE (U.ι_image_le V)))) x := rfl

section MorphismRestriction

variable {X : Scheme.{0}} (j : X ⟶ Y)

instance restrictFunctor_preservesFiniteLimits (i : X ⟶ Y) [IsOpenImmersion i] :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor i) where
  preservesFiniteLimits J _ _ := by
    letI : PreservesLimitsOfShape J
        (Scheme.Modules.restrictFunctor i ⋙ Scheme.Modules.toPresheaf X) := by
      change PreservesLimitsOfShape J
        (Scheme.Modules.toPresheaf Y ⋙
          (Functor.whiskeringLeft _ _ AddCommGrpCat).obj i.opensFunctor.op)
      haveI : PreservesLimitsOfShape J (Scheme.Modules.toPresheaf Y) := by infer_instance
      haveI : PreservesLimitsOfShape J
          ((Functor.whiskeringLeft _ _ AddCommGrpCat).obj i.opensFunctor.op) := by
        infer_instance
      infer_instance
    exact preservesLimitsOfShape_of_reflects_of_preserves
      (Scheme.Modules.restrictFunctor i) (Scheme.Modules.toPresheaf X)

instance restrictFunctor_additive (i : X ⟶ Y) [IsOpenImmersion i] :
    (Scheme.Modules.restrictFunctor i).Additive where
  map_add := by intros; rfl

/-- Restricting the actual direct-image structure module to an open scheme
agrees with the direct-image structure module of the restricted morphism. -/
def imageStructureRestrictIso (U : Y.Opens) :
    (show Y.Modules from imageStructureModule j).restrict U.ι ≅
      (show U.toScheme.Modules from imageStructureModule (j ∣_ U)) := by
  refine (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun V => ?_) ?_)
  · let e := X.presheaf.mapIso (eqToIso (image_morphismRestrict_preimage j U V.unop)).op
    refine ModuleCat.isoMk
      ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).mapIso e) ?_
    intro r
    ext x
    let x' : Γ(X, j ⁻¹ᵁ (U.ι ''ᵁ V.unop)) := x
    let y : Γ(X, (j ⁻¹ᵁ U).ι ''ᵁ ((j ∣_ U) ⁻¹ᵁ V.unop)) :=
      (j ∣_ U).app V.unop r
    change y * e.hom x' =
      e.hom (j.app (U.ι ''ᵁ V.unop) ((U.ι.appIso V.unop).inv r) * x')
    have hr₀ : (U.ι.appIso V.unop).inv r = r := by
      rw [Scheme.Opens.ι_appIso]
      rfl
    rw [hr₀]
    rw [map_mul]
    have hr : y = e.hom (j.app (U.ι ''ᵁ V.unop) r) :=
      ConcreteCategory.congr_hom (morphismRestrict_app j U V.unop) r
    rw [hr]
  · intro V W h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change X.presheaf.map _ (X.presheaf.map _ x) =
      X.presheaf.map _ (X.presheaf.map _ x)
    let h₁ := (Opens.map j.base).map (U.ι.opensFunctor.map h.unop)
    let h₂ := (j ⁻¹ᵁ U).ι.opensFunctor.map ((Opens.map (j ∣_ U).base).map h.unop)
    have hn : X.presheaf.map h₁.op ≫
        X.presheaf.map (eqToHom (image_morphismRestrict_preimage j U W.unop)).op =
      X.presheaf.map (eqToHom (image_morphismRestrict_preimage j U V.unop)).op ≫
        X.presheaf.map h₂.op := by
      rw [← Functor.map_comp, ← Functor.map_comp]
      rfl
    exact ConcreteCategory.congr_hom hn x

theorem schemeStructureMap_restrict (U : Y.Opens) :
    (Scheme.Modules.restrictFunctor U.ι).map (schemeStructureMap j) ≫
      (imageStructureRestrictIso j U).hom =
    (Scheme.Modules.restrictUnitIso U.ι).hom ≫ schemeStructureMap (j ∣_ U) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change X.presheaf.map (eqToHom (image_morphismRestrict_preimage j U V.unop)).op
      (j.app (U.ι ''ᵁ V.unop) a) =
    (j ∣_ U).app V.unop ((U.ι.appIso V.unop).hom a)
  have ha : (U.ι.appIso V.unop).hom a = a := by
    rw [Scheme.Opens.ι_appIso]
    rfl
  rw [ha]
  exact (ConcreteCategory.congr_hom (morphismRestrict_app j U V.unop) a).symm

/-- The intrinsic kernel ideal restricts to the actual ideal sheaf of the
restricted scheme morphism. -/
def kernelIdealRestrictIso (U : Y.Opens) :
    (show Y.Modules from kernelIdealSheaf j).restrict U.ι ≅
      (show U.toScheme.Modules from kernelIdealSheaf (j ∣_ U)) :=
  PreservesKernel.iso (Scheme.Modules.restrictFunctor U.ι) (schemeStructureMap j) ≪≫
    kernel.mapIso _ (schemeStructureMap (j ∣_ U))
      (Scheme.Modules.restrictUnitIso U.ι) (imageStructureRestrictIso j U)
      (schemeStructureMap_restrict j U)

/-- Actual normal sections on an open set agree with global intrinsic
normal sections for the restricted immersion of schemes. -/
def normalSectionRestrictEquiv (U : Y.Opens) :
    (normalDirectImageSheaf j).val.obj (op U) ≃
      (normalDirectImageSheaf (j ∣_ U)).val.obj (op ⊤) :=
  (localLinearHomRestrictEquiv
      (show Y.Modules from kernelIdealSheaf j)
      (show Y.Modules from imageStructureModule j) U).trans
    ((Iso.homCongr (kernelIdealRestrictIso j U) (imageStructureRestrictIso j U)).trans
      (localLinearHomTopEquiv U.toScheme.sheaf (kernelIdealSheaf (j ∣_ U))
        (imageStructureModule (j ∣_ U))).symm)

end MorphismRestriction

#print axioms localLinearHomRestrictEquiv
#print axioms imageStructureRestrictIso
#print axioms kernelIdealRestrictIso
#print axioms normalSectionRestrictEquiv

end CycleQ2GeometricIntrinsicNormal
end

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricIntrinsicNormal
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf

section ModuleEquivalence

variable {X Y : Scheme.{0}}

/-- Restriction along a scheme isomorphism is an equivalence of actual
categories of structure-module sheaves. -/
def moduleRestrictEquivalence (e : X ≅ Y) : Y.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.restrictFunctor e.hom)
    (Scheme.Modules.restrictFunctor e.inv)
    (Scheme.Modules.restrictFunctorId.symm ≪≫
      (Scheme.Modules.restrictFunctorCongr e.inv_hom_id).symm ≪≫
        Scheme.Modules.restrictFunctorComp e.inv e.hom)
    ((Scheme.Modules.restrictFunctorComp e.hom e.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.hom_inv_id ≪≫
        Scheme.Modules.restrictFunctorId)

variable (i : X ⟶ Y) [IsOpenImmersion i] (M N : Y.Modules)

/-- Local linear maps on the range of an open immersion are exactly actual
module morphisms on its source scheme. -/
def localLinearHomOpenImmersionEquiv :
    LocalLinearHom Y.sheaf M N i.opensRange ≃ (M.restrict i ⟶ N.restrict i) := by
  let e := i.isoOpensRange
  let q : Scheme.Modules.restrictFunctor i.opensRange.ι ⋙
      Scheme.Modules.restrictFunctor e.hom ≅ Scheme.Modules.restrictFunctor i :=
    (Scheme.Modules.restrictFunctorComp e.hom i.opensRange.ι).symm ≪≫
      Scheme.Modules.restrictFunctorCongr i.isoOpensRange_hom_ι
  exact (localLinearHomRestrictEquiv M N i.opensRange).trans
    ((moduleRestrictEquivalence e).fullyFaithfulFunctor.homEquiv.trans
      (Iso.homCongr (q.app M) (q.app N)))

end ModuleEquivalence

section OpenBaseChange

variable {X Y X' Y' : Scheme.{0}}
  (j : X ⟶ Y) (i : Y' ⟶ Y) (k : X' ⟶ X) (j' : X' ⟶ Y')
  [IsOpenImmersion i] [IsOpenImmersion k]
  (H : IsPullback j' k i j)

/-- The actual section-ring isomorphism in an open cartesian square. -/
def baseChangeStructureSectionIso (V : Y'.Opens) :
    Γ(X, j ⁻¹ᵁ (i ''ᵁ V)) ≅ Γ(X', j' ⁻¹ᵁ V) := by
  have he := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H V
  have hW : j ⁻¹ᵁ (i ''ᵁ V) ≤ k.opensRange :=
    he.symm.le.trans (k.image_le_opensRange _)
  letI : IsIso (k.app (j ⁻¹ᵁ (i ''ᵁ V))) := k.isIso_app _ hW
  exact asIso (k.app (j ⁻¹ᵁ (i ''ᵁ V))) ≪≫
    X'.presheaf.mapIso (eqToIso
      (IsOpenImmersion.app_eq_invApp_app_of_comp_eq_aux j' i (k ≫ j) H.w.symm V)).op

@[simp] theorem baseChangeStructureSectionIso_hom (V : Y'.Opens) :
    (baseChangeStructureSectionIso j i k j' H V).hom =
      k.appLE (j ⁻¹ᵁ (i ''ᵁ V)) (j' ⁻¹ᵁ V)
        (IsOpenImmersion.app_eq_invApp_app_of_comp_eq_aux j' i (k ≫ j) H.w.symm V).le := rfl

/-- The cartesian comparison uses the literal morphism on section rings. -/
theorem baseChangeStructureSectionIso_app (V : Y'.Opens) :
    (i.appIso V).inv ≫ j.app (i ''ᵁ V) ≫
      (baseChangeStructureSectionIso j i k j' H V).hom = j'.app V := by
  change (i.appIso V).inv ≫ j.app (i ''ᵁ V) ≫ k.app (j ⁻¹ᵁ (i ''ᵁ V)) ≫
    X'.presheaf.map (eqToHom
      (IsOpenImmersion.app_eq_invApp_app_of_comp_eq_aux j' i (k ≫ j) H.w.symm V)).op =
    j'.app V
  simpa only [Scheme.Hom.comp_app, Category.assoc] using
      (IsOpenImmersion.app_eq_appIso_inv_app_of_comp_eq
        j' i (k ≫ j) H.w.symm V).symm

theorem baseChangeStructureSectionIso_naturality {V W : Y'.Opens} (h : V ⟶ W) :
    X.presheaf.map ((Opens.map j.base).map (i.opensFunctor.map h)).op ≫
      (baseChangeStructureSectionIso j i k j' H V).hom =
    (baseChangeStructureSectionIso j i k j' H W).hom ≫
      X'.presheaf.map ((Opens.map j'.base).map h).op := by
  simp only [baseChangeStructureSectionIso_hom, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

/-- Open base change for the actual direct image of the structure module. -/
def imageStructureOpenBaseChangeIso :
    (show Y.Modules from imageStructureModule j).restrict i ≅
      (show Y'.Modules from imageStructureModule j') := by
  refine (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun V => ?_) ?_)
  · let e := baseChangeStructureSectionIso j i k j' H V.unop
    refine ModuleCat.isoMk
      ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).mapIso e) ?_
    intro r
    ext x
    let x' : Γ(X, j ⁻¹ᵁ (i ''ᵁ V.unop)) := x
    let y : Γ(X', j' ⁻¹ᵁ V.unop) := j'.app V.unop r
    change y * e.hom x' =
      e.hom (j.app (i ''ᵁ V.unop) ((i.appIso V.unop).inv r) * x')
    rw [map_mul]
    have hr : e.hom (j.app (i ''ᵁ V.unop) ((i.appIso V.unop).inv r)) = y :=
      ConcreteCategory.congr_hom (baseChangeStructureSectionIso_app j i k j' H V.unop) r
    rw [hr]
  · intro V W h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom
      (baseChangeStructureSectionIso_naturality j i k j' H h.unop) x

theorem schemeStructureMap_openBaseChange :
    (Scheme.Modules.restrictFunctor i).map (schemeStructureMap j) ≫
      (imageStructureOpenBaseChangeIso j i k j' H).hom =
    (Scheme.Modules.restrictUnitIso i).hom ≫ schemeStructureMap j' := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (baseChangeStructureSectionIso j i k j' H V.unop).hom
      (j.app (i ''ᵁ V.unop) a) =
    j'.app V.unop ((i.appIso V.unop).hom a)
  have h := ConcreteCategory.congr_hom
    (baseChangeStructureSectionIso_app j i k j' H V.unop) ((i.appIso V.unop).hom a)
  have ha := ConcreteCategory.congr_hom (i.appIso V.unop).hom_inv_id a
  change (i.appIso V.unop).inv ((i.appIso V.unop).hom a) = a at ha
  simpa only [CommRingCat.comp_apply, ha] using h

/-- The actual ideal module respects open cartesian base change. -/
def kernelIdealOpenBaseChangeIso :
    (show Y.Modules from kernelIdealSheaf j).restrict i ≅
      (show Y'.Modules from kernelIdealSheaf j') :=
  PreservesKernel.iso (Scheme.Modules.restrictFunctor i) (schemeStructureMap j) ≪≫
    kernel.mapIso _ (schemeStructureMap j') (Scheme.Modules.restrictUnitIso i)
      (imageStructureOpenBaseChangeIso j i k j' H)
      (schemeStructureMap_openBaseChange j i k j' H)

/-- Intrinsic normal sections on a coordinate chart identify with the actual
normal sheaf of the induced affine morphism, through an open cartesian square. -/
def normalSectionOpenBaseChangeEquiv :
    (normalDirectImageSheaf j).val.obj (op i.opensRange) ≃
      (normalDirectImageSheaf j').val.obj (op ⊤) :=
  (localLinearHomOpenImmersionEquiv i
      (show Y.Modules from kernelIdealSheaf j)
      (show Y.Modules from imageStructureModule j)).trans
    ((Iso.homCongr (kernelIdealOpenBaseChangeIso j i k j' H)
      (imageStructureOpenBaseChangeIso j i k j' H)).trans
      (localLinearHomTopEquiv Y'.sheaf (kernelIdealSheaf j')
        (imageStructureModule j')).symm)

end OpenBaseChange

#print axioms moduleRestrictEquivalence
#print axioms localLinearHomOpenImmersionEquiv
#print axioms baseChangeStructureSectionIso
#print axioms imageStructureOpenBaseChangeIso
#print axioms kernelIdealOpenBaseChangeIso
#print axioms normalSectionOpenBaseChangeEquiv

end CycleQ2GeometricIntrinsicNormal
end

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricIntrinsicNormal
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf

variable {X Y : Scheme.{0}} (i : X ⟶ Y) [IsOpenImmersion i] (M N : Y.Modules)

/-- The cartesian chart comparison evaluates the same local linear map. -/
theorem localLinearHomOpenImmersionEquiv_app
    (f : LocalLinearHom Y.sheaf M N i.opensRange) (V : X.Opens)
    (x : M.val.obj (op (i ''ᵁ V))) :
    (localLinearHomOpenImmersionEquiv i M N f).val.app (op V) x =
      f.val.app (op (Over.mk (homOfLE (i.image_le_opensRange V)))) x := by
  let e := i.isoOpensRange
  have hc : i.opensRange.ι ''ᵁ (e.hom ''ᵁ V) = i ''ᵁ V := by
    simpa only [e, Scheme.Hom.isoOpensRange_hom_ι] using
      (Scheme.Hom.comp_image e.hom i.opensRange.ι V).symm
  let q : Scheme.Modules.restrictFunctor i.opensRange.ι ⋙
      Scheme.Modules.restrictFunctor e.hom ≅ Scheme.Modules.restrictFunctor i :=
    (Scheme.Modules.restrictFunctorComp e.hom i.opensRange.ι).symm ≪≫
      Scheme.Modules.restrictFunctorCongr i.isoOpensRange_hom_ι
  have hqh (P : Y.Modules) :
      (q.app P).hom.app V = P.presheaf.map (eqToHom hc.symm).op := by
    dsimp [q]
    change P.presheaf.map _ ≫ P.presheaf.map _ = P.presheaf.map (eqToHom hc.symm).op
    rw [← Functor.map_comp]
    rfl
  have hqi (P : Y.Modules) :
      (q.app P).inv.app V = P.presheaf.map (eqToHom hc).op := by
    dsimp [q]
    change P.presheaf.map _ ≫ P.presheaf.map _ = P.presheaf.map (eqToHom hc).op
    rw [← Functor.map_comp]
    rfl
  change (q.app N).hom.app V
    (((Scheme.Modules.restrictFunctor e.hom).map
      (localLinearHomRestrictEquiv M N i.opensRange f)).app V
      ((q.app M).inv.app V x)) = _
  rw [hqh, hqi]
  change N.val.map (eqToHom hc.symm).op
      (f.val.app (op (Over.mk (homOfLE (i.opensRange.ι_image_le (e.hom ''ᵁ V)))))
        (M.val.map (eqToHom hc).op x)) = _
  have hn := ConcreteCategory.congr_hom
    (f.val.naturality
      (Over.homMk (eqToHom hc) :
        Over.mk (homOfLE (i.opensRange.ι_image_le (e.hom ''ᵁ V))) ⟶
          Over.mk (homOfLE (i.image_le_opensRange V))).op) x
  change f.val.app (op (Over.mk (homOfLE (i.opensRange.ι_image_le (e.hom ''ᵁ V)))))
      (M.val.map (eqToHom hc).op x) =
    N.val.map (eqToHom hc).op
      (f.val.app (op (Over.mk (homOfLE (i.image_le_opensRange V)))) x) at hn
  have he : N.presheaf.map (eqToHom hc).op ≫
      N.presheaf.map (eqToHom hc.symm).op = 𝟙 _ := by
    rw [← Functor.map_comp]
    simp
  exact (congrArg (fun y => N.val.map (eqToHom hc.symm).op y) hn).trans
    (ConcreteCategory.congr_hom he
      (f.val.app (op (Over.mk (homOfLE (i.image_le_opensRange V)))) x))

#print axioms localLinearHomOpenImmersionEquiv_app
end CycleQ2GeometricIntrinsicNormal
end


set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricIntrinsicNormal
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf

variable {X Y X' Y' : Scheme.{0}}
  (j : X ⟶ Y) (i : Y' ⟶ Y) (k : X' ⟶ X) (j' : X' ⟶ Y')
  [IsOpenImmersion i] [IsOpenImmersion k]
  (H : IsPullback j' k i j)

/-- The kernel comparison has the expected actual inclusion into the
restricted structure sheaf. -/
theorem kernelIdealOpenBaseChangeIso_hom_ι :
    (kernelIdealOpenBaseChangeIso j i k j' H).hom ≫
      kernel.ι (schemeStructureMap j') =
    (Scheme.Modules.restrictFunctor i).map (kernel.ι (schemeStructureMap j)) ≫
      (Scheme.Modules.restrictUnitIso i).hom := by
  letI : (Scheme.Modules.restrictFunctor i).Additive := restrictFunctor_additive i
  letI : (Scheme.Modules.restrictFunctor i).PreservesZeroMorphisms := by infer_instance
  dsimp [kernelIdealOpenBaseChangeIso, kernel.mapIso]
  rw [Category.assoc, kernel.lift_ι, ← Category.assoc]
  exact congrArg (fun f => f ≫ (Scheme.Modules.restrictUnitIso i).hom)
    (kernelComparison_comp_ι (schemeStructureMap j) (Scheme.Modules.restrictFunctor i))

/-- On literal ideal sections, open base change is the actual coordinate
section-ring isomorphism. -/
theorem kernelIdealOpenBaseChangeIso_hom_section (V : Y'.Opens)
    (a : (kernelIdealSheaf j).val.obj (op (i ''ᵁ V))) :
    (kernelIdealSectionEquiv j' V
      ((kernelIdealOpenBaseChangeIso j i k j' H).hom.val.app (op V) a) : Γ(Y', V)) =
      (i.appIso V).hom (kernelIdealSectionEquiv j (i ''ᵁ V) a) := by
  rw [kernelIdealSectionEquiv_coe, kernelIdealSectionEquiv_coe]
  have h := congrArg (fun f => f.val.app (op V))
    (kernelIdealOpenBaseChangeIso_hom_ι j i k j' H)
  exact ConcreteCategory.congr_hom h a

/-- The inverse kernel comparison is normalized by the same actual ring
isomorphism; it therefore transports the given equation, not a chosen generator. -/
theorem kernelIdealOpenBaseChangeIso_inv_section (V : Y'.Opens)
    (a : (kernelIdealSheaf j').val.obj (op V)) :
    (kernelIdealSectionEquiv j (i ''ᵁ V)
      ((kernelIdealOpenBaseChangeIso j i k j' H).inv.val.app (op V) a) : Γ(Y, i ''ᵁ V)) =
      (i.appIso V).inv (kernelIdealSectionEquiv j' V a) := by
  have h := kernelIdealOpenBaseChangeIso_hom_section j i k j' H V
    ((kernelIdealOpenBaseChangeIso j i k j' H).inv.val.app (op V) a)
  have hi := ConcreteCategory.congr_hom
    (congrArg (fun f => f.val.app (op V))
      (kernelIdealOpenBaseChangeIso j i k j' H).inv_hom_id) a
  change (kernelIdealOpenBaseChangeIso j i k j' H).hom.val.app (op V)
    ((kernelIdealOpenBaseChangeIso j i k j' H).inv.val.app (op V) a) = a at hi
  rw [hi] at h
  apply (i.appIso V).commRingCatIsoToRingEquiv.injective
  exact h.symm.trans
    (ConcreteCategory.congr_hom (i.appIso V).inv_hom_id
      (kernelIdealSectionEquiv j' V a)).symm

/-- Pull a literal local ideal element back to the actual ambient section
ideal through the open cartesian square. -/
def normalOpenIdealPullback (V : Y'.Opens)
    (a : RingHom.ker (j'.app V).hom) : RingHom.ker (j.app (i ''ᵁ V)).hom :=
  kernelIdealSectionEquiv j (i ''ᵁ V)
    ((kernelIdealOpenBaseChangeIso j i k j' H).inv.val.app (op V)
      ((kernelIdealSectionEquiv j' V).symm a))

@[simp] theorem normalOpenIdealPullback_coe (V : Y'.Opens)
    (a : RingHom.ker (j'.app V).hom) :
    (normalOpenIdealPullback j i k j' H V a : Γ(Y, i ''ᵁ V)) =
      (i.appIso V).inv a := by
  simpa only [normalOpenIdealPullback, LinearEquiv.apply_symm_apply] using
    kernelIdealOpenBaseChangeIso_inv_section j i k j' H V
      ((kernelIdealSectionEquiv j' V).symm a)

#print axioms kernelIdealOpenBaseChangeIso_hom_section
#print axioms kernelIdealOpenBaseChangeIso_inv_section
#print axioms normalOpenIdealPullback_coe
end CycleQ2GeometricIntrinsicNormal
end


set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricIntrinsicNormal
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf

variable {X Y X' Y' : Scheme.{0}}
  (j : X ⟶ Y) (i : Y' ⟶ Y) (k : X' ⟶ X) (j' : X' ⟶ Y')
  [IsOpenImmersion i] [IsOpenImmersion k]
  (H : IsPullback j' k i j)

/-- The intrinsic chart comparison evaluates the original local ideal
functional, through the actual coordinate maps on both schemes. -/
theorem normalSectionOpenBaseChangeEquiv_evaluate
    (f : (normalDirectImageSheaf j).val.obj (op i.opensRange))
    (a : RingHom.ker (j'.app ⊤).hom) :
    normalSectionEvaluate j' ⊤ (normalSectionOpenBaseChangeEquiv j i k j' H f) a =
      (baseChangeStructureSectionIso j i k j' H ⊤).hom
        (normalSectionEvaluate j (i ''ᵁ ⊤)
          ((normalDirectImageSheaf j).val.map
            (homOfLE (i.image_le_opensRange ⊤)).op f)
          (normalOpenIdealPullback j i k j' H ⊤ a)) := by
  let K := kernelIdealOpenBaseChangeIso j i k j' H
  let x : (kernelIdealSheaf j).val.obj (op (i ''ᵁ ⊤)) :=
    K.inv.val.app (op ⊤) ((kernelIdealSectionEquiv j' ⊤).symm a)
  let F := localLinearHomOpenImmersionEquiv i
    (show Y.Modules from kernelIdealSheaf j)
    (show Y.Modules from imageStructureModule j) f
  let e := baseChangeStructureSectionIso j i k j' H ⊤
  calc
    _ = e.hom (f.val.app (op (Over.mk (homOfLE (i.image_le_opensRange ⊤)))) x) := by
      change e.hom (F.val.app (op ⊤) x) = _
      exact congrArg e.hom (localLinearHomOpenImmersionEquiv_app i
        (show Y.Modules from kernelIdealSheaf j)
        (show Y.Modules from imageStructureModule j) f ⊤ x)
    _ = _ := by
      apply congrArg e.hom
      change f.val.app (op (Over.mk (homOfLE (i.image_le_opensRange ⊤)))) x =
        localLinearHomEvaluate Y.sheaf (kernelIdealSheaf j) (imageStructureModule j)
          (i ''ᵁ ⊤)
          ((normalDirectImageSheaf j).val.map
            (homOfLE (i.image_le_opensRange ⊤)).op f)
          ((kernelIdealSectionEquiv j (i ''ᵁ ⊤)).symm
            (kernelIdealSectionEquiv j (i ''ᵁ ⊤) x))
      rw [LinearEquiv.symm_apply_apply]
      have h := presheafHom_map_app_op_mk_id
        (F := (kernelIdealSheaf j).val.presheaf)
        (G := (imageStructureModule j).val.presheaf)
        (homOfLE (i.image_le_opensRange ⊤)) f.val
      exact (ConcreteCategory.congr_hom h x).symm

#print axioms normalSectionOpenBaseChangeEquiv_evaluate
end CycleQ2GeometricIntrinsicNormal
end

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricIntrinsicNormal
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf
open scoped TensorProduct

variable {A B : CommRingCat.{0}} (φ : A ⟶ B)

/-- The canonical global-section ring equivalence for an affine scheme. -/
abbrev specTopRingEquiv (A : CommRingCat.{0}) : Γ(Spec A, ⊤) ≃+* A :=
  (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv

instance specTopRingHomInvPair (A : CommRingCat.{0}) :
    RingHomInvPair (specTopRingEquiv A).toRingHom (specTopRingEquiv A).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (specTopRingEquiv A)

instance specTopRingHomInvPair_symm (A : CommRingCat.{0}) :
    RingHomInvPair (specTopRingEquiv A).symm.toRingHom (specTopRingEquiv A).toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (specTopRingEquiv A)

@[simp] theorem affineSectionMap_normalization (a : Γ(Spec A, ⊤)) :
    specTopRingEquiv B ((Spec.map φ).app ⊤ a) = φ (specTopRingEquiv A a) :=
  ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality φ) a

/-- The actual ideal of the affine section-ring map is the original kernel,
with the canonical semilinearity induced by Γ(Spec A) ≃ A. -/
def affineKernelSectionSemilinearEquiv :
    RingHom.ker ((Spec.map φ).app ⊤).hom ≃ₛₗ[(specTopRingEquiv A).toRingHom]
      RingHom.ker φ.hom where
  toFun a := ⟨specTopRingEquiv A a, by
    change φ (specTopRingEquiv A a) = 0
    rw [← affineSectionMap_normalization]
    exact (congrArg (specTopRingEquiv B) a.property).trans (map_zero _)⟩
  invFun a := ⟨(specTopRingEquiv A).symm a, by
    change (Spec.map φ).app ⊤ ((specTopRingEquiv A).symm a) = 0
    apply (specTopRingEquiv B).injective
    rw [affineSectionMap_normalization, (specTopRingEquiv A).apply_symm_apply, map_zero]
    exact a.property⟩
  left_inv a := Subtype.ext ((specTopRingEquiv A).symm_apply_apply a)
  right_inv a := Subtype.ext ((specTopRingEquiv A).apply_symm_apply a)
  map_add' a b := Subtype.ext
    (map_add (specTopRingEquiv A) (a : Γ(Spec A, ⊤)) (b : Γ(Spec A, ⊤)))
  map_smul' r a := Subtype.ext
    (map_mul (specTopRingEquiv A) r (a : Γ(Spec A, ⊤)))

@[simp] theorem affineKernelSectionSemilinearEquiv_coe
    (a : RingHom.ker ((Spec.map φ).app ⊤).hom) :
    (affineKernelSectionSemilinearEquiv φ a : A) = specTopRingEquiv A a := rfl

@[simp] theorem affineKernelSectionSemilinearEquiv_symm_coe
    (a : RingHom.ker φ.hom) :
    ((affineKernelSectionSemilinearEquiv φ).symm a : Γ(Spec A, ⊤)) =
      (specTopRingEquiv A).symm a := rfl

/-- The coefficient module of the actual affine normal sheaf is the original
curve algebra, under the canonical global-section equivalence. -/
def affineImageSectionSemilinearEquiv :
    letI : Algebra A B := φ.hom.toAlgebra
    (imageStructureModule (Spec.map φ)).val.obj (op ⊤) ≃ₛₗ[(specTopRingEquiv A).toRingHom] B := by
  letI : Algebra A B := φ.hom.toAlgebra
  refine
    { __ := (specTopRingEquiv B).toAddEquiv
      map_smul' := ?_ }
  intro r b
  let b' : Γ(Spec B, ⊤) := b
  let s : Γ(Spec B, ⊤) := (Spec.map φ).app ⊤ r
  change specTopRingEquiv B (s * b') =
    φ (specTopRingEquiv A r) * specTopRingEquiv B b'
  have hs : specTopRingEquiv B s = φ (specTopRingEquiv A r) :=
    affineSectionMap_normalization φ r
  rw [map_mul, hs]

/-- Affine normal sections are functionals on the original algebraic ideal,
with no chosen functional or frame. -/
def affineNormalAlgebraEquiv :
    letI : Algebra A B := φ.hom.toAlgebra
    (normalDirectImageSheaf (Spec.map φ)).val.obj (op ⊤) ≃ₛₗ[(specTopRingEquiv A).toRingHom]
      (RingHom.ker φ.hom →ₗ[A] B) := by
  letI : Algebra A B := φ.hom.toAlgebra
  exact (affineNormalSectionLinearEquiv φ).trans
    ((affineKernelSectionSemilinearEquiv φ).arrowCongr
      (affineImageSectionSemilinearEquiv φ))

@[simp] theorem affineNormalAlgebraEquiv_apply
    (f : (normalDirectImageSheaf (Spec.map φ)).val.obj (op ⊤)) (a : RingHom.ker φ.hom) :
    letI : Algebra A B := φ.hom.toAlgebra
    affineNormalAlgebraEquiv φ f a =
      specTopRingEquiv B (normalSectionEvaluate (Spec.map φ) ⊤ f
        ((affineKernelSectionSemilinearEquiv φ).symm a)) := rfl

/-- The actual affine intrinsic normal sections identify with the dual of
B ⊗[A] (ker φ)/(ker φ)² over the original coordinate algebras. -/
def affineNormalAlgebraConormalEquiv :
    letI : Algebra A B := φ.hom.toAlgebra
    (normalDirectImageSheaf (Spec.map φ)).val.obj (op ⊤) ≃ₛₗ[(specTopRingEquiv A).toRingHom]
      (B ⊗[A] (RingHom.ker φ.hom).Cotangent →ₗ[B] B) := by
  letI : Algebra A B := φ.hom.toAlgebra
  exact (affineNormalAlgebraEquiv φ).trans
    ((normalFunctionalEquiv (RingHom.ker φ.hom) (fun _ ha => ha)).restrictScalars A)

@[simp] theorem affineNormalAlgebraConormalEquiv_tmul
    (f : (normalDirectImageSheaf (Spec.map φ)).val.obj (op ⊤)) (b : B)
    (a : RingHom.ker φ.hom) :
    letI : Algebra A B := φ.hom.toAlgebra
    affineNormalAlgebraConormalEquiv φ f
      (b ⊗ₜ[A] (RingHom.ker φ.hom).toCotangent a) =
        b * specTopRingEquiv B (normalSectionEvaluate (Spec.map φ) ⊤ f
          ((affineKernelSectionSemilinearEquiv φ).symm a)) := rfl

@[simp] theorem affineNormalAlgebraConormalEquiv_symm_evaluate
    (a : RingHom.ker φ.hom) :
    letI : Algebra A B := φ.hom.toAlgebra
    ∀ g : B ⊗[A] (RingHom.ker φ.hom).Cotangent →ₗ[B] B,
      specTopRingEquiv B (normalSectionEvaluate (Spec.map φ) ⊤
        ((affineNormalAlgebraConormalEquiv φ).symm g)
        ((affineKernelSectionSemilinearEquiv φ).symm a)) =
      g ((1 : B) ⊗ₜ[A] (RingHom.ker φ.hom).toCotangent a) := by
  letI : Algebra A B := φ.hom.toAlgebra
  intro g
  have h := LinearMap.congr_fun
    ((affineNormalAlgebraConormalEquiv φ).apply_symm_apply g)
    ((1 : B) ⊗ₜ[A] (RingHom.ker φ.hom).toCotangent a)
  simpa only [affineNormalAlgebraConormalEquiv_tmul, one_mul] using h

#print axioms affineKernelSectionSemilinearEquiv
#print axioms affineImageSectionSemilinearEquiv
#print axioms affineNormalAlgebraEquiv
#print axioms affineNormalAlgebraConormalEquiv
#print axioms affineNormalAlgebraConormalEquiv_symm_evaluate

end CycleQ2GeometricIntrinsicNormal
end

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricIntrinsicNormal
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf
open scoped TensorProduct

variable {X Y : Scheme.{0}} {A B : CommRingCat.{0}} (φ : A ⟶ B)
  (j : X ⟶ Y) (i : Spec A ⟶ Y) (k : Spec B ⟶ X)
  [IsOpenImmersion i] [IsOpenImmersion k]
  (H : IsPullback (Spec.map φ) k i j)

/-- On an actual affine cartesian chart, intrinsic normal sections are the
dual of the algebraic conormal module in the original coordinate rings. -/
def normalOpenAlgebraConormalEquiv :
    letI : Algebra A B := φ.hom.toAlgebra
    (normalDirectImageSheaf j).val.obj (op i.opensRange) ≃
      (B ⊗[A] (RingHom.ker φ.hom).Cotangent →ₗ[B] B) := by
  letI : Algebra A B := φ.hom.toAlgebra
  exact (normalSectionOpenBaseChangeEquiv j i k (Spec.map φ) H).trans
    (affineNormalAlgebraConormalEquiv φ).toEquiv

/-- The transported ideal element is exactly the section represented by the
original coordinate-ring element through the actual affine chart. -/
@[simp] theorem normalOpenAlgebraIdeal_coe (a : RingHom.ker φ.hom) :
    (normalOpenIdealPullback j i k (Spec.map φ) H ⊤
      ((affineKernelSectionSemilinearEquiv φ).symm a) : Γ(Y, i ''ᵁ ⊤)) =
      (i.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv a) := by
  rw [normalOpenIdealPullback_coe]
  rfl

/-- The normal comparison is fixed on every actual ideal element and every
coefficient; it carries the same functional used by the local adjunction. -/
@[simp] theorem normalOpenAlgebraConormalEquiv_tmul
    (f : (normalDirectImageSheaf j).val.obj (op i.opensRange)) (b : B)
    (a : RingHom.ker φ.hom) :
    letI : Algebra A B := φ.hom.toAlgebra
    normalOpenAlgebraConormalEquiv φ j i k H f
      (b ⊗ₜ[A] (RingHom.ker φ.hom).toCotangent a) =
    b * specTopRingEquiv B
      ((baseChangeStructureSectionIso j i k (Spec.map φ) H ⊤).hom
        (normalSectionEvaluate j (i ''ᵁ ⊤)
          ((normalDirectImageSheaf j).val.map
            (homOfLE (i.image_le_opensRange ⊤)).op f)
          (normalOpenIdealPullback j i k (Spec.map φ) H ⊤
            ((affineKernelSectionSemilinearEquiv φ).symm a)))) := by
  letI : Algebra A B := φ.hom.toAlgebra
  change affineNormalAlgebraConormalEquiv φ
      (normalSectionOpenBaseChangeEquiv j i k (Spec.map φ) H f)
      (b ⊗ₜ[A] (RingHom.ker φ.hom).toCotangent a) = _
  rw [affineNormalAlgebraConormalEquiv_tmul]
  exact congrArg (fun z : Γ(Spec B, ⊤) => b * specTopRingEquiv B z)
    (normalSectionOpenBaseChangeEquiv_evaluate j i k (Spec.map φ) H f
      ((affineKernelSectionSemilinearEquiv φ).symm a))

#print axioms normalOpenAlgebraConormalEquiv
#print axioms normalOpenAlgebraConormalEquiv_tmul
end CycleQ2GeometricIntrinsicNormal
end
