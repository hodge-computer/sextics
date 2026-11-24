import Proposal.GeometricAffineCohomology
import Proposal.GeometricCartierDerivedClass

/-!
# The degree-zero source under a homeomorphism

The free abelian sheaf on the top open represents global sections. Its
universal section gives a canonical map to the direct image of the same
representing sheaf. Full faithfulness and essential surjectivity of the
direct image along a homeomorphism make this map an isomorphism.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2AutomorphismGlobalSections

open CategoryTheory CategoryTheory.Abelian TopologicalSpace Opposite
  CycleQ2InjectiveCech CycleQ2CechTwoToDerived CycleQ2GeometricSheafCohomologyRestriction

variable {X Y : TopCat.{0}}

def pushFunctor (h : X ≅ Y) : AbSheaf X ⥤ AbSheaf Y :=
  (Opens.map h.hom).sheafPushforwardContinuous AddCommGrpCat
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

def pushEquiv (h : X ≅ Y) : AbSheaf X ≌ AbSheaf Y := by
  let e := (Opens.mapMapIso h).symm
  letI : e.functor.IsContinuous (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) :=
    inferInstanceAs ((Opens.map h.inv).IsContinuous _ _)
  letI : e.inverse.IsContinuous (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) :=
    inferInstanceAs ((Opens.map h.hom).IsContinuous _ _)
  exact continuousSheafEquiv _ _ e

@[simp] theorem pushEquiv_functor (h : X ≅ Y) : (pushEquiv h).functor = pushFunctor h := rfl

instance (h : X ≅ Y) : (pushFunctor h).IsEquivalence :=
  inferInstanceAs (pushEquiv h).functor.IsEquivalence

instance (h : X ≅ Y) : (pushFunctor h).Additive where

def sourceMap (h : X ≅ Y) : freeOpen (⊤ : Opens Y) ⟶ (pushFunctor h).obj (freeOpen (⊤ : Opens X)) :=
  (freeOpenSections _ ⊤).symm (freeOpenSections (freeOpen (⊤ : Opens X)) ⊤ (𝟙 _))

theorem sourceMap_sectionHom (h : X ≅ Y) (F : AbSheaf X) (s : Sections F ⊤) :
    sourceMap h ≫ (pushFunctor h).map ((freeOpenSections F ⊤).symm s) =
      (freeOpenSections ((pushFunctor h).obj F) ⊤).symm s := by
  apply (freeOpenSections ((pushFunctor h).obj F) ⊤).injective
  rw [AddEquiv.apply_symm_apply, ← freeOpenSections_postcomp, sourceMap, AddEquiv.apply_symm_apply]
  change app ((freeOpenSections F ⊤).symm s) ⊤
    (freeOpenSections (freeOpen (⊤ : Opens X)) ⊤ (𝟙 _)) = s
  rw [freeOpenSections_postcomp, Category.id_comp, AddEquiv.apply_symm_apply]

private theorem precomp_bijective_push (h : X ≅ Y) (F : AbSheaf X) :
    Function.Bijective (fun v : (pushFunctor h).obj (freeOpen (⊤ : Opens X)) ⟶
      (pushFunctor h).obj F => sourceMap h ≫ v) := by
  let e := (pushFunctor h).asEquivalence.fullyFaithfulFunctor.homEquiv (X := freeOpen (⊤ : Opens X))
    (Y := F)
  let k := (freeOpenSections F ⊤).toEquiv.trans (freeOpenSections ((pushFunctor h).obj F) ⊤).symm.toEquiv
  suffices H : (fun v : _ ⟶ _ => sourceMap h ≫ v) ∘ e = k by
    exact ((EquivLike.bijective e).of_comp_iff _).mp (H ▸ k.bijective)
  funext v
  change sourceMap h ≫ (pushFunctor h).map v =
    (freeOpenSections ((pushFunctor h).obj F) ⊤).symm (freeOpenSections F ⊤ v)
  simpa only [AddEquiv.symm_apply_apply] using
    sourceMap_sectionHom h F (freeOpenSections F ⊤ v)

private theorem precomp_bijective_iso {C : Type*} [Category C] {A B Z Z' : C}
    (u : A ⟶ B) (i : Z ≅ Z') (H : Function.Bijective (fun v : B ⟶ Z => u ≫ v)) :
    Function.Bijective (fun v : B ⟶ Z' => u ≫ v) := by
  constructor
  · intro v w hvw
    apply (cancel_mono i.inv).mp
    apply H.injective
    simpa only [← Category.assoc] using congrArg (fun k => k ≫ i.inv) hvw
  · intro w
    obtain ⟨v,hv⟩ := H.surjective (w ≫ i.inv)
    change u ≫ v = w ≫ i.inv at hv
    refine ⟨v ≫ i.hom, ?_⟩
    change u ≫ v ≫ i.hom = w
    rw [← Category.assoc,hv,Category.assoc,Iso.inv_hom_id,Category.comp_id]

instance (h : X ≅ Y) : IsIso (sourceMap h) := by
  apply isIso_of_coyoneda_map_bijective
  intro F
  exact precomp_bijective_iso _ ((pushFunctor h).objObjPreimageIso F)
    (precomp_bijective_push h _)

def sourceIso (h : X ≅ Y) : freeOpen (⊤ : Opens Y) ≅ (pushFunctor h).obj (freeOpen (⊤ : Opens X)) :=
  asIso (sourceMap h)

local instance (Z : TopCat.{0}) : HasExt.{1} (AbSheaf Z) := HasExt.standard _

theorem sourceIso_sectionExtZero (h : X ≅ Y) (F : AbSheaf X) (s : Sections F ⊤) :
    (Ext.mk₀ (sourceIso h).hom).comp ((sectionExtZero ⊤ s).mapExactFunctor (pushFunctor h)) rfl =
      sectionExtZero (F := (pushFunctor h).obj F) ⊤ s := by
  rw [sectionExtZero, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
  exact congrArg Ext.mk₀ (sourceMap_sectionHom h F s)

end CycleQ2AutomorphismGlobalSections
end

#print axioms CycleQ2AutomorphismGlobalSections.sourceIso_sectionExtZero
