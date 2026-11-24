import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Actual scheme pullback of an affine tilde module

The genuine global sections of affine scheme-module pushforward are
restriction of scalars through the original ring homomorphism. Taking
the mates of this natural isomorphism identifies the genuine scheme
pullback of a tilde module with the tilde of its actual tensor product.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricAffineModulePullback

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

variable {B C : CommRingCat.{0}} (ρ : B ⟶ C)

def pushforwardGlobalIso :
    Scheme.Modules.pushforward (Spec.map ρ) ⋙ moduleSpecΓFunctor (R := B) ≅
      moduleSpecΓFunctor (R := C) ⋙ ModuleCat.restrictScalars ρ.hom := by
  refine NatIso.ofComponents (fun M => ?_) ?_
  · refine LinearEquiv.toModuleIso
      (X₁ := (moduleSpecΓFunctor (R := B)).obj
        ((Scheme.Modules.pushforward (Spec.map ρ)).obj M))
      (X₂ := (ModuleCat.restrictScalars ρ.hom).obj ((moduleSpecΓFunctor (R := C)).obj M))
      { toFun := fun m => m
        invFun := fun m => m
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun b m => ?_ }
    change (Spec.map ρ).appTop ((Scheme.ΓSpecIso B).inv b) • (show Γ(M, ⊤) from m) =
      (Scheme.ΓSpecIso C).inv (ρ b) • (show Γ(M, ⊤) from m)
    exact congrArg (fun c : Γ(Spec C, ⊤) => c • (show Γ(M, ⊤) from m))
      (congrArg (fun f => f b) (Scheme.ΓSpecIso_inv_naturality ρ)).symm
  · intro M N f
    ext m
    rfl

def pullbackTildeIso :
    tilde.functor B ⋙ Scheme.Modules.pullback (Spec.map ρ) ≅
      ModuleCat.extendScalars ρ.hom ⋙ tilde.functor C :=
  ((conjugateIsoEquiv
    ((tilde.adjunction (R := B)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ρ)))
    ((ModuleCat.extendRestrictScalarsAdj ρ.hom).comp (tilde.adjunction (R := C)))).symm
      (pushforwardGlobalIso ρ)).symm

/-- The isomorphism respects the units of the genuine scheme pullback
and tensor-product adjunctions, fixing its original-element normalization. -/
theorem pullbackTilde_unit (M : ModuleCat B) :
    ((ModuleCat.extendRestrictScalarsAdj ρ.hom).comp (tilde.adjunction (R := C))).unit.app M ≫
        (pushforwardGlobalIso ρ).inv.app
          ((tilde.functor C).obj ((ModuleCat.extendScalars ρ.hom).obj M)) =
      ((tilde.adjunction (R := B)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ρ))).unit.app M ≫
        (Scheme.Modules.pushforward (Spec.map ρ) ⋙ moduleSpecΓFunctor (R := B)).map
          ((pullbackTildeIso ρ).hom.app M) :=
  unit_conjugateEquiv_symm
    ((ModuleCat.extendRestrictScalarsAdj ρ.hom).comp (tilde.adjunction (R := C)))
    ((tilde.adjunction (R := B)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ρ)))
    (pushforwardGlobalIso ρ).inv M

/-- On an original global module element, the actual pullback unit is
carried to the literal tensor-product unit and the original tilde map. -/
theorem pullbackTilde_unit_apply (M : ModuleCat B) (m : M) :
    ((pullbackTildeIso ρ).hom.app M).val.app (op ⊤)
        (((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ρ)).unit.app
          (tilde (R := B) M)).val.app (op ⊤) (tilde.toOpen (R := B) M ⊤ m)) =
      tilde.toOpen (R := C) ((ModuleCat.extendScalars ρ.hom).obj M) ⊤
        ((ModuleCat.extendRestrictScalarsAdj ρ.hom).unit.app M m) := by
  have h := congrArg (fun f => f m) (pullbackTilde_unit ρ M)
  exact h.symm

end CycleQ2GeometricAffineModulePullback

end

#print axioms CycleQ2GeometricAffineModulePullback.pushforwardGlobalIso
#print axioms CycleQ2GeometricAffineModulePullback.pullbackTildeIso
#print axioms CycleQ2GeometricAffineModulePullback.pullbackTilde_unit
#print axioms CycleQ2GeometricAffineModulePullback.pullbackTilde_unit_apply
