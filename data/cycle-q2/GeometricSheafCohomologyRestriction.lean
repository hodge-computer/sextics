import Proposal.GeometricSheafHZero
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB

/-!
# Actual restriction of first sheaf cohomology

Restriction to the over-site of an open induces an injective map from
ambient-site first cohomology on that open. The proof uses the exact
restriction functor, additive Yoneda, and actual injective presentations.
It does not assume affine acyclicity or a comparison of derived groups.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricSheafCohomologyRestriction

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
  CycleQ2GeometricConeCech.HZero

section ExactFunctor
universe u u' v v' w w'
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasExt.{w} C] [HasExt.{w'} D] [EnoughInjectives C]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- Exact restriction detects degree-one extensions when it preserves
all morphisms out of their fixed source. No preservation of injective
objects by the restriction functor is needed. -/
theorem mapExtOne_injective_of_hom_bijective (X : C)
    (hX : ∀ Y : C, Function.Bijective (fun f : X ⟶ Y => G.map f)) (Y : C) :
    Function.Injective (G.mapExtAddHom X Y 1) := by
  rw [← AddMonoidHom.ker_eq_bot_iff, AddSubgroup.eq_bot_iff_forall]
  intro x hx
  change x.mapExactFunctor G = 0 at hx
  let I : InjectivePresentation Y := Classical.arbitrary _
  let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
  have : Injective S.X₂ := I.injective
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ X hS x
    (Ext.eq_zero_of_injective _) (n₀ := 0) rfl
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).surjective z
  have hf : (Ext.mk₀ (G.map f)).comp (hS.map G).extClass rfl = 0 := by
    have hh := congrArg (fun t => t.mapExactFunctor G) hz
    simpa only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
      Ext.mapExactFunctor_extClass, hx] using hh
  obtain ⟨t, ht⟩ := Ext.covariant_sequence_exact₃ (G.obj X) (hS.map G)
    (Ext.mk₀ (G.map f)) rfl hf
  obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective _ _).surjective t
  change (Ext.mk₀ g).comp (Ext.mk₀ (G.map S.g)) (zero_add 0) =
    Ext.mk₀ (G.map f) at ht
  obtain ⟨g₀, hg₀⟩ := (hX S.X₂).surjective g
  have hgf : g₀ ≫ S.g = f := by
    apply (hX S.X₃).injective
    apply (Ext.mk₀_bijective _ _).injective
    simpa only [Ext.mk₀_comp_mk₀, Functor.map_comp, hg₀] using ht
  rw [← hz, ← hgf, ← Ext.mk₀_comp_mk₀_assoc]
  simp
end ExactFunctor

section Sheaves
variable {C : Type} [Category.{0} C] [Quiver.IsThin C]
  (J : GrothendieckTopology C) (U : C)

local instance overIsThin : Quiver.IsThin (Over U) :=
  fun _ _ => ⟨fun _ _ => Over.OverMorphism.ext (Subsingleton.elim _ _)⟩

abbrev freeAbelianSheaf :=
  (presheafToSheaf J AddCommGrpCat.{0}).obj (yoneda.obj U ⋙ AddCommGrpCat.free)

abbrev restrictionFunctor : Sheaf J AddCommGrpCat.{0} ⥤ Sheaf (J.over U) AddCommGrpCat.{0} :=
  J.overPullback AddCommGrpCat U

local instance : (restrictionFunctor J U).IsLeftAdjoint :=
  ((Over.forget U).sheafAdjunctionCocontinuous AddCommGrpCat (J.over U) J).isLeftAdjoint

local instance : (restrictionFunctor J U).IsRightAdjoint :=
  ((Over.forget U).sheafAdjunctionContinuous AddCommGrpCat (J.over U) J).isRightAdjoint

local instance : (restrictionFunctor J U).Additive where

/-- A thin site's representable at U restricts to the representable at
the terminal object of its actual over-site. -/
def overYonedaIso :
    (Over.forget U).op ⋙ yoneda.obj U ≅ yoneda.obj (Over.mk (𝟙 U)) :=
  NatIso.ofComponents (fun V => Equiv.toIso
    { toFun := fun f => Over.homMk f (Subsingleton.elim _ _)
      invFun := fun f => f.left
      left_inv := fun _ => rfl
      right_inv := fun _ => by apply Over.OverMorphism.ext; rfl })
    (fun _ => by ext; rfl)

/-- The preceding comparison on free abelian presheaves. -/
def overFreePresheafIso :
    (Over.forget U).op ⋙ (yoneda.obj U ⋙ AddCommGrpCat.free) ≅
      yoneda.obj (Over.mk (𝟙 U)) ⋙ AddCommGrpCat.free :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (overYonedaIso U) AddCommGrpCat.free

/-- The actual restricted free abelian sheaf, using compatibility of
restriction and sheafification for the over-forget functor. -/
def overFreeSheafIso :
    (restrictionFunctor J U).obj (freeAbelianSheaf J U) ≅
      freeAbelianSheaf (J.over U) (Over.mk (𝟙 U)) :=
  (((Over.forget U).pushforwardContinuousSheafificationCompatibility
    AddCommGrpCat (J.over U) J).app (yoneda.obj U ⋙ AddCommGrpCat.free)).symm ≪≫
      (presheafToSheaf (J.over U) AddCommGrpCat).mapIso (overFreePresheafIso U)

/-- Evaluation on the free generator is additive Yoneda after actual
sheafification. -/
def freeSheafSections (F : Sheaf J AddCommGrpCat.{0}) :
    (freeAbelianSheaf J U ⟶ F) ≃+ F.obj.obj (op U) :=
  ((sheafificationAdjunction J AddCommGrpCat).homAddEquiv _ F).trans
    (freeYonedaSections F.obj U)

theorem overFreeSheafIso_inv_unit :
    toSheafify (J.over U) (yoneda.obj (Over.mk (𝟙 U)) ⋙ AddCommGrpCat.free) ≫
        (overFreeSheafIso J U).inv.hom =
      (overFreePresheafIso U).inv ≫
        Functor.whiskerLeft (Over.forget U).op
          (toSheafify J (yoneda.obj U ⋙ AddCommGrpCat.free)) := by
  change toSheafify (J.over U) _ ≫
      (sheafifyMap (J.over U) (overFreePresheafIso U).inv ≫
        (((Over.forget U).pushforwardContinuousSheafificationCompatibility
          AddCommGrpCat (J.over U) J).app _).hom.hom) = _
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc]
  exact congrArg (fun f => (overFreePresheafIso U).inv ≫ f)
    ((Over.forget U).toSheafify_pullbackSheafificationCompatibility
      AddCommGrpCat (J.over U) J (yoneda.obj U ⋙ AddCommGrpCat.free))

/-- The canonical free generator is preserved by the actual sheaf comparison. -/
theorem overFreeSheafIso_generator :
    (overFreeSheafIso J U).inv.hom.app (op (Over.mk (𝟙 U)))
      ((toSheafify (J.over U)
        (yoneda.obj (Over.mk (𝟙 U)) ⋙ AddCommGrpCat.free)).app
          (op (Over.mk (𝟙 U))) (FreeAbelianGroup.of (𝟙 (Over.mk (𝟙 U))))) =
      (toSheafify J (yoneda.obj U ⋙ AddCommGrpCat.free)).app (op U)
        (FreeAbelianGroup.of (𝟙 U)) := by
  have hh := congrArg (fun f => f.app (op (Over.mk (𝟙 U)))
      (FreeAbelianGroup.of (𝟙 (Over.mk (𝟙 U)))))
    (overFreeSheafIso_inv_unit J U)
  have hraw : (overFreePresheafIso U).inv.app (op (Over.mk (𝟙 U)))
      (FreeAbelianGroup.of (𝟙 (Over.mk (𝟙 U)))) = FreeAbelianGroup.of (𝟙 U) := by
    change FreeAbelianGroup.map (fun f : Over.mk (𝟙 U) ⟶ Over.mk (𝟙 U) => f.left)
      (FreeAbelianGroup.of (𝟙 (Over.mk (𝟙 U)))) = _
    exact FreeAbelianGroup.map_of_apply _
  exact hh.trans (congrArg
    ((toSheafify J (yoneda.obj U ⋙ AddCommGrpCat.free)).app (op U)) hraw)

/-- The restriction of a map from the free sheaf evaluates to exactly the
same section on U. -/
theorem freeSheafSections_restriction (F : Sheaf J AddCommGrpCat.{0})
    (f : freeAbelianSheaf J U ⟶ F) :
    freeSheafSections (J.over U) (Over.mk (𝟙 U)) (F.over U)
      ((overFreeSheafIso J U).inv ≫ (restrictionFunctor J U).map f) =
        freeSheafSections J U F f := by
  change f.hom.app (op U)
    ((overFreeSheafIso J U).inv.hom.app (op (Over.mk (𝟙 U)))
      ((toSheafify (J.over U)
        (yoneda.obj (Over.mk (𝟙 U)) ⋙ AddCommGrpCat.free)).app
          (op (Over.mk (𝟙 U))) (FreeAbelianGroup.of (𝟙 (Over.mk (𝟙 U)))))) = _
  rw [overFreeSheafIso_generator]
  rfl

/-- Restriction is fully faithful on all morphisms out of this actual
free abelian sheaf. -/
theorem restriction_hom_bijective (F : Sheaf J AddCommGrpCat.{0}) :
    Function.Bijective (fun f : freeAbelianSheaf J U ⟶ F =>
      (restrictionFunctor J U).map f) := by
  constructor
  · intro f g hfg
    apply (freeSheafSections J U F).injective
    exact (freeSheafSections_restriction J U F f).symm.trans
      ((congrArg (fun k => freeSheafSections (J.over U) (Over.mk (𝟙 U))
        (F.over U) ((overFreeSheafIso J U).inv ≫ k)) hfg).trans
          (freeSheafSections_restriction J U F g))
  · intro g
    obtain ⟨f, hf⟩ := (freeSheafSections J U F).surjective
      (freeSheafSections (J.over U) (Over.mk (𝟙 U)) (F.over U)
        ((overFreeSheafIso J U).inv ≫ g))
    refine ⟨f, ?_⟩
    apply (cancel_epi (overFreeSheafIso J U).inv).mp
    apply (freeSheafSections (J.over U) (Over.mk (𝟙 U)) (F.over U)).injective
    exact (freeSheafSections_restriction J U F f).trans hf

/-- At a terminal object, the free abelian representable presheaf is
literally the constant integer presheaf up to this explicit isomorphism. -/
def terminalFreePresheafIso (T : C) (hT : IsTerminal T) :
    yoneda.obj T ⋙ AddCommGrpCat.free ≅
      (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{0} ℤ)) :=
  NatIso.ofComponents (fun V => by
    letI : Unique (V.unop ⟶ T) :=
      { default := hT.from V.unop, uniq := fun _ => hT.hom_ext _ _ }
    exact ((FreeAbelianGroup.uniqueEquiv (V.unop ⟶ T)).trans
      AddEquiv.ulift.symm).toAddCommGrpIso)
    (by
      intro V W f
      apply AddCommGrpCat.hom_ext
      apply FreeAbelianGroup.lift_ext
      intro g
      simp [Functor.comp_map, AddCommGrpCat.free_map, FreeAbelianGroup.uniqueEquiv])

/-- The actual free sheaf at a terminal object is the constant integer sheaf. -/
def terminalFreeSheafIso (T : C) (hT : IsTerminal T) :
    freeAbelianSheaf J T ≅
      (constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of (ULift.{0} ℤ)) :=
  (presheafToSheaf J AddCommGrpCat).mapIso (terminalFreePresheafIso T hT)

local instance sheafHasExt : HasExt.{1} (Sheaf J AddCommGrpCat.{0}) := HasExt.standard _

/-- The ambient-site cohomology at a terminal object is the ordinary
cohomology of that same additive sheaf, in every degree. -/
def terminalCohomologyEquiv (F : Sheaf J AddCommGrpCat.{0})
    (T : C) (hT : IsTerminal T) (n : ℕ) : F.H' n T ≃+ F.H n :=
  (((extFunctor n).mapIso (terminalFreeSheafIso J T hT).op).app F).addCommGroupIsoToAddEquiv.symm

/-- The restricted free source of H′ is the actual constant integer
sheaf on the over-site. -/
def restrictionSourceIso :
    (restrictionFunctor J U).obj (freeAbelianSheaf J U) ≅
      (constantSheaf (J.over U) AddCommGrpCat).obj (AddCommGrpCat.of (ULift.{0} ℤ)) :=
  overFreeSheafIso J U ≪≫ terminalFreeSheafIso (J.over U) (Over.mk (𝟙 U)) Over.mkIdTerminal

/-- The actual degree-one restriction map, induced by the exact
restriction functor and the constructed source isomorphism. -/
def restrictionHOne (F : Sheaf J AddCommGrpCat.{0}) : F.H' 1 U →+ (F.over U).H 1 :=
  ((((extFunctor 1).mapIso (restrictionSourceIso J U).op).app (F.over U)).addCommGroupIsoToAddEquiv).symm.toAddMonoidHom.comp
      ((restrictionFunctor J U).mapExtAddHom (freeAbelianSheaf J U) F 1)

/-- Vanishing after restriction detects vanishing of the original
ambient-site degree-one class. This applies to the actual opens site. -/
theorem restrictionHOne_injective (F : Sheaf J AddCommGrpCat.{0}) :
    Function.Injective (restrictionHOne J U F) :=
  ((((extFunctor 1).mapIso (restrictionSourceIso J U).op).app (F.over U)).addCommGroupIsoToAddEquiv).symm.injective.comp
      (mapExtOne_injective_of_hom_bijective (restrictionFunctor J U)
        (freeAbelianSheaf J U) (restriction_hom_bijective J U) F)

theorem restrictionHOne_eq_zero_iff (F : Sheaf J AddCommGrpCat.{0}) (x : F.H' 1 U) :
    restrictionHOne J U F x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    apply restrictionHOne_injective J U F
    simpa only [map_zero] using hx
  · rintro rfl
    exact map_zero _

/-- Actual over-site vanishing implies ambient-site vanishing on the open. -/
theorem ambientHOne_subsingleton (F : Sheaf J AddCommGrpCat.{0})
    [Subsingleton ((F.over U).H 1)] : Subsingleton (F.H' 1 U) :=
  Function.Injective.subsingleton (restrictionHOne_injective J U F)

end Sheaves

section SiteEquivalence
variable {C D : Type} [Category.{0} C] [Category.{0} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (e : C ≌ D)
  [e.functor.IsContinuous J K] [e.inverse.IsContinuous K J]

/-- The actual equivalence of additive sheaves associated to a site
category equivalence whose two directions are continuous. -/
def continuousSheafEquiv : Sheaf J AddCommGrpCat.{0} ≌ Sheaf K AddCommGrpCat.{0} where
  functor := e.inverse.sheafPushforwardContinuous AddCommGrpCat K J
  inverse := e.functor.sheafPushforwardContinuous AddCommGrpCat J K
  unitIso := NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _ (Functor.isoWhiskerRight e.op.unitIso F.obj))
    (by
      intro F G f
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext V
      exact (f.hom.naturality (e.op.unitIso.hom.app V)).symm)
  counitIso := NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _ (Functor.isoWhiskerRight e.op.counitIso F.obj))
    (by
      intro F G f
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext V
      exact (f.hom.naturality (e.op.counitIso.hom.app V)).symm)
  functor_unitIso_comp F := by
    ext
    simp [← Functor.map_comp, ← op_comp]
    rfl

local instance : (continuousSheafEquiv J K e).functor.Additive where

/-- Constant additive sheaves transport along this actual equivalence.
The construction uses their adjunction with terminal evaluation. -/
def constantSheafEquiv (T : D) (hT : IsTerminal T) :
    constantSheaf J AddCommGrpCat ≅
      constantSheaf K AddCommGrpCat ⋙ (continuousSheafEquiv J K e).inverse :=
  (constantSheafAdj J AddCommGrpCat (hT.isTerminalObj e.inverse T)).leftAdjointUniq
    ((constantSheafAdj K AddCommGrpCat hT).comp
      (continuousSheafEquiv J K e).symm.toAdjunction)

/-- The integer source of actual sheaf cohomology is preserved. -/
def constantSourceIso (T : D) (hT : IsTerminal T) :
    (continuousSheafEquiv J K e).functor.obj
        ((constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of (ULift.{0} ℤ))) ≅
      (constantSheaf K AddCommGrpCat).obj (AddCommGrpCat.of (ULift.{0} ℤ)) :=
  (continuousSheafEquiv J K e).functor.mapIso
    ((constantSheafEquiv J K e T hT).app _) ≪≫
      (continuousSheafEquiv J K e).counitIso.app _

local instance sourceHasExt : HasExt.{1} (Sheaf J AddCommGrpCat.{0}) := HasExt.standard _
local instance targetHasExt : HasExt.{1} (Sheaf K AddCommGrpCat.{0}) := HasExt.standard _

/-- Transport of actual first sheaf cohomology along equivalent sites. -/
def siteEquivalenceHOne (T : D) (hT : IsTerminal T) (F : Sheaf J AddCommGrpCat.{0}) :
    F.H 1 →+ ((continuousSheafEquiv J K e).functor.obj F).H 1 :=
  ((((extFunctor 1).mapIso (constantSourceIso J K e T hT).op).app
    ((continuousSheafEquiv J K e).functor.obj F)).addCommGroupIsoToAddEquiv).symm.toAddMonoidHom.comp
      ((continuousSheafEquiv J K e).functor.mapExtAddHom _ F 1)

/-- The map is injective; full faithfulness supplies all degree-zero lifts. -/
theorem siteEquivalenceHOne_injective
    (T : D) (hT : IsTerminal T) (F : Sheaf J AddCommGrpCat.{0}) :
    Function.Injective (siteEquivalenceHOne J K e T hT F) :=
  ((((extFunctor 1).mapIso (constantSourceIso J K e T hT).op).app
    ((continuousSheafEquiv J K e).functor.obj F)).addCommGroupIsoToAddEquiv).symm.injective.comp
      (mapExtOne_injective_of_hom_bijective (continuousSheafEquiv J K e).functor _
        (fun _ => ⟨(continuousSheafEquiv J K e).functor.map_injective,
          (continuousSheafEquiv J K e).functor.map_surjective⟩) F)

/-- First cohomology vanishing transfers through a genuine site equivalence
and an actual isomorphism of the transported sheaves. -/
theorem hOne_subsingleton_of_continuousEquivalence
    (T : D) (hT : IsTerminal T) (F : Sheaf J AddCommGrpCat.{0})
    (G : Sheaf K AddCommGrpCat.{0})
    (i : F ≅ (e.functor.sheafPushforwardContinuous AddCommGrpCat J K).obj G)
    [Subsingleton (G.H 1)] : Subsingleton (F.H 1) := by
  let j : (continuousSheafEquiv J K e).functor.obj F ≅ G :=
    (continuousSheafEquiv J K e).functor.mapIso i ≪≫
      (continuousSheafEquiv J K e).counitIso.app G
  let : Subsingleton ((Sheaf.functorH K 1).obj G) :=
    inferInstanceAs (Subsingleton (G.H 1))
  exact Function.Injective.subsingleton
    ((((Sheaf.functorH K 1).mapIso j).addCommGroupIsoToAddEquiv).injective.comp
      (siteEquivalenceHOne_injective J K e T hT F))

end SiteEquivalence

section ChartVanishing
variable {C D : Type} [Category.{0} C] [Category.{0} D] [Quiver.IsThin C]
  (J : GrothendieckTopology C) (U : C) (K : GrothendieckTopology D)
  (e : Over U ≌ D)
  [e.functor.IsContinuous (J.over U) K]
  [e.inverse.IsContinuous K (J.over U)]

local instance chartSourceHasExt : HasExt.{1} (Sheaf J AddCommGrpCat.{0}) := HasExt.standard _
local instance chartTargetHasExt : HasExt.{1} (Sheaf K AddCommGrpCat.{0}) := HasExt.standard _
local instance chartOverHasExt : HasExt.{1} (Sheaf (J.over U) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- Actual affine-chart vanishing gives vanishing of the ambient H′ group.
All transports here are constructed from the sites and the given sheaf
isomorphism; no derived restriction comparison is assumed. -/
theorem ambientHOne_subsingleton_of_chart
    (T : D) (hT : IsTerminal T) (F : Sheaf J AddCommGrpCat.{0})
    (G : Sheaf K AddCommGrpCat.{0})
    (i : F.over U ≅
      (e.functor.sheafPushforwardContinuous AddCommGrpCat (J.over U) K).obj G)
    [Subsingleton (G.H 1)] : Subsingleton (F.H' 1 U) := by
  let : Subsingleton ((F.over U).H 1) :=
    hOne_subsingleton_of_continuousEquivalence (J.over U) K e T hT (F.over U) G i
  exact ambientHOne_subsingleton J U F

end ChartVanishing
end CycleQ2GeometricSheafCohomologyRestriction
end
