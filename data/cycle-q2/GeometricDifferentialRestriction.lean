import Proposal.GeometricDifferentialSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Topology.Sheaves.Over

/-!
# Universal differentials on an actual open restriction

Restriction to the over-site of an open retains the universal property of
the constructed differential sheaf. The lift is obtained from the actual
restriction/direct-image adjunction and the global universal differential.
This is the local universal property needed to compare affine differential
frames with the differential sheaf on the whole projective curve.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricDifferentialRestriction

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
  CycleQ2GeometricDifferentialSheaf

variable {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
  (c : ℂ →+* R.obj.obj (op ⊤)) (U : Opens X)

def overCoefficient :
    (Over.forget U).op ⋙ constantComplex X ⟶ (Over.forget U).op ⋙ R.obj :=
  Functor.whiskerLeft (Over.forget U).op (coefficientMap R c)

abbrev OverModule := SheafOfModules.{0} ((ringSheaf R).over U)

abbrev OverDerivation (M : OverModule R U) :=
  PresheafOfModules.Derivation' (R := (Over.forget U).op ⋙ R.obj)
    M.val (overCoefficient R c U)

def restrictDerivation (M : SheafOfModules.{0} (ringSheaf R))
    (d : M.val.Derivation' (coefficientMap R c)) :
    OverDerivation R c U (M.over U) where
  d {V} := d.d (X := (Over.forget U).op.obj V)
  d_mul a b := d.d_mul a b
  d_map f x := d.d_map ((Over.forget U).op.map f) x
  d_app a := d.d_app a

def restrictedUniversal :
    OverDerivation R c U ((differentialSheaf R c).over U) :=
  restrictDerivation R c U (differentialSheaf R c) (universalDifferential R c)

abbrev directImage (M : OverModule R U) : SheafOfModules.{0} (ringSheaf R) :=
  (SheafOfModules.pushforward (SheafOfModules.pushforwardOver
    (R := ringSheaf R) U)).obj M

/-- Restrict a section to its intersection with the open and apply the
given derivation there. The target is the actual direct image module. -/
def directImageDerivation (M : OverModule R U) (d : OverDerivation R c U M) :
    (directImage R U M).val.Derivation' (coefficientMap R c) where
  d {V} := (d.d (X := op ((Over.star U).obj V.unop))).comp
    (R.obj.map (prod.snd : U ⨯ V.unop ⟶ V.unop).op).hom.toAddMonoidHom
  d_mul {V} a b := by
    change d.d (X := op ((Over.star U).obj V.unop))
      (R.obj.map (prod.snd : U ⨯ V.unop ⟶ V.unop).op (a * b)) = _
    rw [map_mul, d.d_mul]
    rfl
  d_map {V W} f x := by
    change d.d (X := op ((Over.star U).obj W.unop))
      (R.obj.map (prod.snd : U ⨯ W.unop ⟶ W.unop).op (R.obj.map f x)) =
      M.val.map ((Over.star U).map f.unop).op
        (d.d (X := op ((Over.star U).obj V.unop))
          (R.obj.map (prod.snd : U ⨯ V.unop ⟶ V.unop).op x))
    have hnat := d.d_map ((Over.star U).map f.unop).op
      (R.obj.map (prod.snd : U ⨯ V.unop ⟶ V.unop).op x)
    change d.d (X := op ((Over.star U).obj W.unop))
      (R.obj.map ((Over.star U).map f.unop).left.op
        (R.obj.map (prod.snd : U ⨯ V.unop ⟶ V.unop).op x)) = _ at hnat
    apply Eq.trans ?_ hnat
    apply congrArg (d.d (X := op ((Over.star U).obj W.unop)))
    change (R.obj.map f ≫ R.obj.map prod.snd.op) x =
      (R.obj.map prod.snd.op ≫ R.obj.map
        ((Over.star U).map f.unop).left.op) x
    rw [← R.obj.map_comp, ← R.obj.map_comp]
    congr 2
  d_app {V} a := by
    change d.d (X := op ((Over.star U).obj V.unop))
      (R.obj.map (prod.snd : U ⨯ V.unop ⟶ V.unop).op
        (coefficientOn R c V.unop a)) = 0
    have h := d.d_app (X := op ((Over.star U).obj V.unop)) a
    change d.d (X := op ((Over.star U).obj V.unop))
      (coefficientOn R c (U ⨯ V.unop) a) = 0 at h
    have hc : R.obj.map (prod.snd : U ⨯ V.unop ⟶ V.unop).op
        (coefficientOn R c V.unop a) =
        coefficientOn R c (U ⨯ V.unop) a := by
      unfold coefficientOn
      change (R.obj.map (homOfLE le_top).op ≫ R.obj.map prod.snd.op) (c a) =
        R.obj.map (homOfLE le_top).op (c a)
      rw [← R.obj.map_comp]
      congr 2
    rw [hc]
    exact h

/-- The lift to the genuine restricted differential sheaf, using the
existing restriction/direct-image adjunction. -/
def restrictedLift (M : OverModule R U) (d : OverDerivation R c U M) :
    (differentialSheaf R c).over U ⟶ M :=
  ((SheafOfModules.overPushforwardOverAdj (R := ringSheaf R) U).homEquiv
    (differentialSheaf R c) M).symm
      (differentialLift R c (directImage R U M) (directImageDerivation R c U M d))

theorem restrictedLift_fac (M : OverModule R U) (d : OverDerivation R c U M) :
    (restrictedUniversal R c U).postcomp (restrictedLift R c U M d).val = d := by
  ext V x
  change ((restrictedLift R c U M d).val.app V)
    ((universalDifferential R c).d (X := op V.unop.left) x) = d.d x
  rw [restrictedLift, Adjunction.homEquiv_counit]
  change M.val.map ((Over.forgetAdjStar U).unit.app V.unop).op
    ((differentialLift R c (directImage R U M) (directImageDerivation R c U M d)).val.app
      (op V.unop.left) ((universalDifferential R c).d x)) = d.d x
  have hfac := PresheafOfModules.Derivation.congr_d
    (differentialLift_fac R c (directImage R U M) (directImageDerivation R c U M d)) x
  change (differentialLift R c (directImage R U M)
      (directImageDerivation R c U M d)).val.app (op V.unop.left)
        ((universalDifferential R c).d x) =
      d.d (X := op ((Over.star U).obj V.unop.left))
        (R.obj.map (prod.snd : U ⨯ V.unop.left ⟶ V.unop.left).op x) at hfac
  have hnat := d.d_map ((Over.forgetAdjStar U).unit.app V.unop).op
    (R.obj.map (prod.snd : U ⨯ V.unop.left ⟶ V.unop.left).op x)
  change d.d (X := V)
    (R.obj.map ((Over.forgetAdjStar U).unit.app V.unop).left.op
      (R.obj.map (prod.snd : U ⨯ V.unop.left ⟶ V.unop.left).op x)) = _ at hnat
  apply (congrArg (M.val.map ((Over.forgetAdjStar U).unit.app V.unop).op) hfac).trans
  apply hnat.symm.trans
  have hx : R.obj.map ((Over.forgetAdjStar U).unit.app V.unop).left.op
      (R.obj.map prod.snd.op x) = x := by
    change (R.obj.map prod.snd.op ≫
      R.obj.map ((Over.forgetAdjStar U).unit.app V.unop).left.op) x = x
    rw [← R.obj.map_comp, ← op_comp, Over.forgetAdjStar_unit_app_left,
      prod.lift_snd]
    exact congrArg
      (fun f : R.obj.obj (op V.unop.left) ⟶ R.obj.obj (op V.unop.left) => f x)
      (R.obj.map_id (op V.unop.left))
  exact congrArg (d.d (X := V)) hx

theorem restrictedLift_unique (M : OverModule R U)
    (f g : (differentialSheaf R c).over U ⟶ M)
    (h : (restrictedUniversal R c U).postcomp f.val =
      (restrictedUniversal R c U).postcomp g.val) : f = g := by
  apply ((SheafOfModules.overPushforwardOverAdj (R := ringSheaf R) U).homEquiv
    (differentialSheaf R c) M).injective
  apply differentialLift_unique R c (directImage R U M)
  ext V x
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change f.val.app (op ((Over.star U).obj V.unop))
      ((differentialSheaf R c).val.map prod.snd.op ((universalDifferential R c).d x)) =
    g.val.app (op ((Over.star U).obj V.unop))
      ((differentialSheaf R c).val.map prod.snd.op ((universalDifferential R c).d x))
  have hnat := (universalDifferential R c).d_map
    (prod.snd : U ⨯ V.unop ⟶ V.unop).op x
  have hlocal := PresheafOfModules.Derivation.congr_d
    (X := op ((Over.star U).obj V.unop)) h
    (R.obj.map (prod.snd : U ⨯ V.unop ⟶ V.unop).op x)
  change f.val.app (op ((Over.star U).obj V.unop))
      ((universalDifferential R c).d
        (R.obj.map (prod.snd : U ⨯ V.unop ⟶ V.unop).op x)) =
    g.val.app (op ((Over.star U).obj V.unop))
      ((universalDifferential R c).d
        (R.obj.map (prod.snd : U ⨯ V.unop ⟶ V.unop).op x)) at hlocal
  exact (congrArg (f.val.app (op ((Over.star U).obj V.unop))) hnat).symm.trans
    (hlocal.trans (congrArg (g.val.app (op ((Over.star U).obj V.unop))) hnat))

/-- The actual restricted differential is universal for natural complex
derivations on all subopens of U. -/
def restrictedHomEquiv (M : OverModule R U) :
    ((differentialSheaf R c).over U ⟶ M) ≃ OverDerivation R c U M where
  toFun f := (restrictedUniversal R c U).postcomp f.val
  invFun := restrictedLift R c U M
  left_inv f := restrictedLift_unique R c U M _ f (restrictedLift_fac R c U M _)
  right_inv := restrictedLift_fac R c U M

#print axioms restrictedLift_fac
#print axioms restrictedLift_unique
#print axioms restrictedHomEquiv

end CycleQ2GeometricDifferentialRestriction
end
