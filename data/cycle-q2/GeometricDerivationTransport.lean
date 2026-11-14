import Proposal.GeometricDifferentialSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# Derivations transported through an equivalence of ringed sites

This supplies the change of section rings needed for actual affine charts.
The inverse transport detects equality of derivations with values in any
sheaf of modules; derivations into the structure module transport directly.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricDerivationTransport

open CategoryTheory Opposite

variable {C D : Type} [Category.{0} C] [Category.{0} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (S : Sheaf J CommRingCat.{0}) (R : Sheaf K CommRingCat.{0})
  (E : C ≌ D) [E.inverse.IsContinuous K J]
  (α : S.obj ≅ E.functor.op ⋙ R.obj)

abbrev ringSheaf {B : Type} [Category.{0} B] {L : GrothendieckTopology B}
    (T : Sheaf L CommRingCat.{0}) : Sheaf L RingCat.{0} :=
  (sheafCompose L (forget₂ CommRingCat RingCat)).obj T

/-- The inverse chart section isomorphism, with the counit restriction
needed to align the actual open objects. -/
def inverseRingIso : R.obj ≅ E.inverse.op ⋙ S.obj :=
  (Functor.leftUnitor R.obj).symm ≪≫
    Functor.isoWhiskerRight (NatIso.op E.counitIso) R.obj ≪≫
      Functor.associator E.inverse.op E.functor.op R.obj ≪≫
        Functor.isoWhiskerLeft E.inverse.op α.symm

omit [E.inverse.IsContinuous K J] in
theorem inverseRingIso_apply (V : Dᵒᵖ) (a : R.obj.obj V) :
    (inverseRingIso S R E α).hom.app V a =
      (α.app (E.inverse.op.obj V)).inv (R.obj.map (E.counit.app V.unop).op a) := rfl

omit [E.inverse.IsContinuous K J] in
theorem inverseRingIso_unit (V : Cᵒᵖ) (a : S.obj.obj V) :
    S.obj.map (E.unit.app V.unop).op
        ((inverseRingIso S R E α).hom.app (E.functor.op.obj V) ((α.app V).hom a)) = a := by
  apply (α.app V).commRingCatIsoToRingEquiv.injective
  have hn (b : S.obj.obj (E.inverse.op.obj (E.functor.op.obj V))) :
      (α.app V).hom (S.obj.map (E.unit.app V.unop).op b) =
        R.obj.map (E.functor.map (E.unit.app V.unop)).op
          ((α.app (E.inverse.op.obj (E.functor.op.obj V))).hom b) :=
    congrArg (fun f => f b) (α.hom.naturality (E.unit.app V.unop).op)
  change (α.app V).hom (S.obj.map (E.unit.app V.unop).op _) = (α.app V).hom a
  rw [hn, inverseRingIso_apply, Iso.inv_hom_id_apply]
  change (R.obj.map (E.counit.app (E.functor.obj V.unop)).op ≫
    R.obj.map (E.functor.map (E.unit.app V.unop)).op) ((α.app V).hom a) = _
  rw [← R.obj.map_comp, ← op_comp]
  have hid : R.obj.map (𝟙 (E.functor.op.obj V)) ((α.app V).hom a) = (α.app V).hom a :=
    congrArg (fun f : R.obj.obj (E.functor.op.obj V) ⟶ R.obj.obj (E.functor.op.obj V) =>
      f ((α.app V).hom a)) (R.obj.map_id (E.functor.op.obj V))
  exact (congrArg (fun f => R.obj.map f.op ((α.app V).hom a))
    (E.functor_unitIso_comp V.unop)).trans hid

def inverseRingSheafMap :
    ringSheaf R ⟶
      (E.inverse.sheafPushforwardContinuous RingCat.{0} K J).obj (ringSheaf S) where
  hom := Functor.whiskerRight (inverseRingIso S R E α).hom (forget₂ CommRingCat RingCat)

def inverseModule (M : SheafOfModules.{0} (ringSheaf S)) :
    SheafOfModules.{0} (ringSheaf R) :=
  (SheafOfModules.pushforward (inverseRingSheafMap S R E α)).obj M

variable
  (cS : (Functor.const Cᵒᵖ).obj (CommRingCat.of ℂ) ⟶ S.obj)
  (cR : (Functor.const Dᵒᵖ).obj (CommRingCat.of ℂ) ⟶ R.obj)
  (hc : ∀ (V : Cᵒᵖ) (c : ℂ), (α.app V).hom (cS.app V c) =
    cR.app (E.functor.op.obj V) c)

omit [E.inverse.IsContinuous K J] in
include hc in
theorem inverseRingIso_coefficient (V : Dᵒᵖ) (c : ℂ) :
    (inverseRingIso S R E α).hom.app V (cR.app V c) =
      cS.app (E.inverse.op.obj V) c := by
  rw [inverseRingIso_apply]
  have hn : R.obj.map (E.counit.app V.unop).op (cR.app V c) =
      cR.app (E.functor.op.obj (E.inverse.op.obj V)) c :=
    (congrArg (fun f => f c) (cR.naturality (E.counit.app V.unop).op)).symm
  rw [hn, ← hc, Iso.hom_inv_id_apply]

abbrev DerivationOn {B : Type} [Category.{0} B] {L : GrothendieckTopology B}
    (T : Sheaf L CommRingCat.{0})
    (cT : (Functor.const Bᵒᵖ).obj (CommRingCat.of ℂ) ⟶ T.obj)
    (M : SheafOfModules.{0} (ringSheaf T)) :=
  PresheafOfModules.Derivation' (R := T.obj) M.val cT

/-- Transport an arbitrary module-valued derivation to the affine site. -/
def inverseDerivation (M : SheafOfModules.{0} (ringSheaf S))
    (d : DerivationOn S cS M) : DerivationOn R cR (inverseModule S R E α M) where
  d {V} := (d.d (X := E.inverse.op.obj V)).comp
    ((inverseRingIso S R E α).hom.app V).hom.toAddMonoidHom
  d_mul {V} a b := by
    change d.d ((inverseRingIso S R E α).hom.app V (a * b)) =
      (inverseRingIso S R E α).hom.app V a •
          d.d ((inverseRingIso S R E α).hom.app V b) +
        (inverseRingIso S R E α).hom.app V b •
          d.d ((inverseRingIso S R E α).hom.app V a)
    rw [map_mul, d.d_mul]
  d_map {V W} f a := by
    change d.d ((inverseRingIso S R E α).hom.app W (R.obj.map f a)) =
      M.val.map (E.inverse.op.map f)
        (d.d ((inverseRingIso S R E α).hom.app V a))
    exact (congrArg (d.d (X := E.inverse.op.obj W))
      (congrArg (fun k => k a) ((inverseRingIso S R E α).hom.naturality f))).trans
        (d.d_map (E.inverse.op.map f) ((inverseRingIso S R E α).hom.app V a))
  d_app {V} c := by
    change d.d ((inverseRingIso S R E α).hom.app V (cR.app V c)) = 0
    exact (congrArg (d.d (X := E.inverse.op.obj V))
      (inverseRingIso_coefficient S R E α cS cR hc V c)).trans (d.d_app c)

/-- Equality of derivations can be checked after moving to the affine
site; no faithfulness or uniqueness hypothesis is supplied. -/
theorem inverseDerivation_injective (M : SheafOfModules.{0} (ringSheaf S)) :
    Function.Injective (inverseDerivation S R E α cS cR hc M) := by
  intro d e h
  ext V a
  have h' := congrArg (M.val.map (E.unit.app V.unop).op)
    (PresheafOfModules.Derivation.congr_d h ((α.app V).hom a))
  change M.val.map (E.unit.app V.unop).op
      (d.d ((inverseRingIso S R E α).hom.app (E.functor.op.obj V) ((α.app V).hom a))) =
    M.val.map (E.unit.app V.unop).op
      (e.d ((inverseRingIso S R E α).hom.app (E.functor.op.obj V) ((α.app V).hom a))) at h'
  calc
    _ = M.val.map (E.unit.app V.unop).op
        (d.d ((inverseRingIso S R E α).hom.app (E.functor.op.obj V) ((α.app V).hom a))) :=
      (congrArg (d.d (X := V)) (inverseRingIso_unit S R E α V a)).symm.trans
        (d.d_map (E.unit.app V.unop).op _)
    _ = _ := h'
    _ = _ := (e.d_map (E.unit.app V.unop).op _).symm.trans
      (congrArg (e.d (X := V)) (inverseRingIso_unit S R E α V a))

/-- The coefficient derivation on regular affine sections transports
to a genuine derivation of the structure module on the chart. -/
def structureDerivation
    (d : DerivationOn R cR (SheafOfModules.unit (ringSheaf R))) :
    DerivationOn S cS (SheafOfModules.unit (ringSheaf S)) where
  d {V} := ((α.app V).inv.hom.toAddMonoidHom.comp
    (d.d (X := E.functor.op.obj V))).comp (α.app V).hom.hom.toAddMonoidHom
  d_mul {V} a b := by
    let dV : R.obj.obj (E.functor.op.obj V) →+ R.obj.obj (E.functor.op.obj V) :=
      d.d (X := E.functor.op.obj V)
    let a' : R.obj.obj (E.functor.op.obj V) := (α.app V).hom a
    let b' : R.obj.obj (E.functor.op.obj V) := (α.app V).hom b
    have hd : dV (a' * b') = a' * dV b' + b' * dV a' := d.d_mul _ _
    have hab : (α.app V).hom (a * b) = a' * b' := map_mul _ _ _
    change (α.app V).inv (dV ((α.app V).hom (a * b))) =
      a * (α.app V).inv (dV ((α.app V).hom b)) +
        b * (α.app V).inv (dV ((α.app V).hom a))
    rw [hab, hd]
    rw [map_add, map_mul, map_mul, Iso.hom_inv_id_apply, Iso.hom_inv_id_apply]
  d_map {V W} f a := by
    apply (α.app W).commRingCatIsoToRingEquiv.injective
    have hn (b : S.obj.obj V) :
        (α.app W).hom (S.obj.map f b) =
          R.obj.map (E.functor.op.map f) ((α.app V).hom b) :=
      congrArg (fun k => k b) (α.hom.naturality f)
    change (α.app W).hom ((α.app W).inv (d.d ((α.app W).hom (S.obj.map f a)))) =
      (α.app W).hom (S.obj.map f ((α.app V).inv (d.d ((α.app V).hom a))))
    rw [Iso.inv_hom_id_apply, hn, d.d_map, hn, Iso.inv_hom_id_apply]
    rfl
  d_app {V} c := by
    change (α.app V).inv (d.d ((α.app V).hom (cS.app V c))) = 0
    rw [hc, d.d_app, map_zero]

end CycleQ2GeometricDerivationTransport
end
