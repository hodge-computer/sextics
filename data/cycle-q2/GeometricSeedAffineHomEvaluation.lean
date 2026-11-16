import Proposal.GeometricIntrinsicNormal
import Proposal.GeometricSeedProjectiveImageChart

/-!
# Native affine evaluation of the actual orbit-ideal internal Hom

The existing internal-Hom sheaf consists of linear natural transformations
on all subopens. At the whole affine scheme, the tilde--Gamma adjunction
identifies these with linear maps from the original module to the native
global sections of the target. This comparison is linear for the native
affine scalar actions and retains evaluation on every original element.

For the actual chart orbit ideal, normalization by `ΓSpecIso` identifies
the global sections of its genuine internal Hom into the structure module
with the existing `OrbitDual`. No condition is imposed on an arbitrary
target, and no identification with the original single curve is used.
The localization assertion on proper basic opens remains a separate step.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedAffineHomEvaluation

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricIntrinsicNormal
open CycleQ2SeedProjectiveImageChart

attribute [local instance] CycleQ2GeometricIntrinsicNormal.overHomCommModuleMk
  CycleQ2GeometricIntrinsicNormal.localLinearRingModule
  CycleQ2GeometricIntrinsicNormal.moduleHomObjModule

section Evaluation

variable {T : TopCat.{0}} (R : T.Sheaf CommRingCat.{0})
  (M N : SheafOfModules.{0} (ringSheaf R)) (U : Opens T)

/-- Evaluation is linear over the actual ring of the open. -/
def localHomEvaluationLinearMap :
    LocalLinearHom R M N U →ₗ[R.obj.obj (op U)]
      (M.val.obj (op U) →ₗ[R.obj.obj (op U)] N.val.obj (op U)) where
  toFun := localLinearHomEvaluate R M N U
  map_add' f g := by
    apply LinearMap.ext
    intro x
    rfl
  map_smul' r f := by
    apply LinearMap.ext
    intro x
    let v : N.val.obj (op U) := localLinearHomEvaluate R M N U f x
    change R.obj.map (𝟙 (op U)) r • v = r • v
    exact congrArg (fun a : R.obj.obj (op U) => a • v)
      (ConcreteCategory.congr_hom (R.obj.map_id (op U)) r)

end Evaluation

section Affine

variable {A : CommRingCat.{0}} (P : ModuleCat.{0} A) (N : (Spec A).Modules)

/-- This is the genuine internal Hom, with a tilde source and arbitrary
target; its sections retain all subopen components. -/
def affineHomSheaf : (Spec A).Modules :=
  moduleHomSheaf (Spec A).sheaf (tilde P) N

/-- At the whole affine scheme, the actual local-Hom sections are exactly
the maps supplied by the tilde--Gamma adjunction. -/
def topHomEquivType :
    Γ(affineHomSheaf P N, ⊤) ≃ (P →ₗ[A] Γ(N, ⊤)) :=
  (localLinearHomTopEquiv (Spec A).sheaf (tilde P) N).trans
    (((tilde.adjunction (R := A)).homEquiv P N).trans ModuleCat.homEquiv)

theorem topHomEquivType_apply (H : Γ(affineHomSheaf P N, ⊤)) (x : P) :
    topHomEquivType P N H x =
      localLinearHomEvaluate (Spec A).sheaf (tilde P) N ⊤ H
        ((tilde.toOpen P ⊤).hom x) := rfl

/-- The adjunction comparison preserves the native affine scalar action,
including its `ΓSpecIso` coefficient map. -/
def topHomEquiv :
    (moduleSpecΓFunctor (R := A)).obj (affineHomSheaf P N) ≃ₗ[A]
      (P →ₗ[A] (moduleSpecΓFunctor (R := A)).obj N) where
  __ := topHomEquivType P N
  map_add' H K := by
    apply LinearMap.ext
    intro x
    rfl
  map_smul' r H := by
    apply LinearMap.ext
    intro x
    change topHomEquivType P N (r • H) x = r • topHomEquivType P N H x
    rw [topHomEquivType_apply, topHomEquivType_apply]
    rw [Scheme.Modules.smul_Spec_def (M := affineHomSheaf P N),
      Scheme.Modules.smul_Spec_def (M := N)]
    exact LinearMap.congr_fun
      ((localHomEvaluationLinearMap (Spec A).sheaf (tilde P) N ⊤).map_smul
        ((Spec A).presheaf.map (⊤ : (Spec A).Opens).leTop.op
          ((Scheme.ΓSpecIso A).inv r)) H)
      ((tilde.toOpen P ⊤).hom x)

theorem topHomEquiv_apply
    (H : (moduleSpecΓFunctor (R := A)).obj (affineHomSheaf P N)) (x : P) :
    topHomEquiv P N H x =
      localLinearHomEvaluate (Spec A).sheaf (tilde P) N ⊤ H
        ((tilde.toOpen P ⊤).hom x) := rfl

theorem topHomEquiv_symm_evaluate
    (φ : P →ₗ[A] (moduleSpecΓFunctor (R := A)).obj N) (x : P) :
    localLinearHomEvaluate (Spec A).sheaf (tilde P) N ⊤
        ((topHomEquiv P N).symm φ) ((tilde.toOpen P ⊤).hom x) = φ x :=
  LinearMap.congr_fun ((topHomEquiv P N).apply_symm_apply φ) x

end Affine

/-- The actual structure-module sheaf. -/
abbrev structureModule (A : CommRingCat.{0}) : (Spec A).Modules :=
  SheafOfModules.unit (Spec A).ringCatSheaf

/-- Normalize the native global sections of the structure module by the
canonical ring isomorphism, preserving the native `A`-action. -/
def structureTopEquiv (A : CommRingCat.{0}) :
    (moduleSpecΓFunctor (R := A)).obj (structureModule A) ≃ₗ[A] A where
  toFun := (Scheme.ΓSpecIso A).hom
  invFun := (Scheme.ΓSpecIso A).inv
  left_inv := fun s => Iso.hom_inv_id_apply (Scheme.ΓSpecIso A) s
  right_inv := fun a => Iso.inv_hom_id_apply (Scheme.ΓSpecIso A) a
  map_add' := fun s t => map_add (Scheme.ΓSpecIso A).hom.hom s t
  map_smul' r s := by
    rw [Scheme.Modules.smul_Spec_def]
    have hi : (⊤ : (Spec A).Opens).leTop.op =
        𝟙 (op (⊤ : (Spec A).Opens)) := Subsingleton.elim _ _
    change (Scheme.ΓSpecIso A).hom
        ((Spec A).presheaf.map (⊤ : (Spec A).Opens).leTop.op
          ((Scheme.ΓSpecIso A).inv r) * (show Γ(Spec A, ⊤) from s)) =
      r * (Scheme.ΓSpecIso A).hom (show Γ(Spec A, ⊤) from s)
    rw [hi, CategoryTheory.Functor.map_id]
    change (Scheme.ΓSpecIso A).hom
        ((Scheme.ΓSpecIso A).inv r * (show Γ(Spec A, ⊤) from s)) =
      r * (Scheme.ΓSpecIso A).hom (show Γ(Spec A, ⊤) from s)
    rw [map_mul, Iso.inv_hom_id_apply]

/-- The genuine internal Hom of the actual three-component orbit ideal. -/
def orbitHomSheaf (i : Fin 3) : (Spec (CommRingCat.of (AffineRing i))).Modules :=
  affineHomSheaf (ModuleCat.of (AffineRing i) (OrbitIdeal i))
    (structureModule (CommRingCat.of (AffineRing i)))

/-- Native global sections of the actual internal Hom recover exactly the
existing algebraic orbit dual, with no additional chart hypotheses. -/
def orbitHomTopEquiv (i : Fin 3) :
    (moduleSpecΓFunctor (R := CommRingCat.of (AffineRing i))).obj (orbitHomSheaf i)
      ≃ₗ[AffineRing i] OrbitDual i :=
  let e : (moduleSpecΓFunctor (R := CommRingCat.of (AffineRing i))).obj (orbitHomSheaf i)
      ≃ₗ[AffineRing i] (OrbitIdeal i →ₗ[AffineRing i]
        (moduleSpecΓFunctor (R := CommRingCat.of (AffineRing i))).obj
          (structureModule (CommRingCat.of (AffineRing i)))) :=
    topHomEquiv (A := CommRingCat.of (AffineRing i)) (ModuleCat.of (AffineRing i) (OrbitIdeal i))
      (structureModule (CommRingCat.of (AffineRing i)))
  let k : (moduleSpecΓFunctor (R := CommRingCat.of (AffineRing i))).obj
      (structureModule (CommRingCat.of (AffineRing i))) ≃ₗ[AffineRing i] AffineRing i :=
    structureTopEquiv (CommRingCat.of (AffineRing i))
  let f : (OrbitIdeal i →ₗ[AffineRing i]
      (moduleSpecΓFunctor (R := CommRingCat.of (AffineRing i))).obj
        (structureModule (CommRingCat.of (AffineRing i)))) ≃ₗ[AffineRing i] OrbitDual i :=
    (LinearEquiv.refl (AffineRing i) (OrbitIdeal i)).arrowCongr k
  e.trans f

/-- The actual tilde image of an original ideal element in the native section carrier. -/
def orbitElementSection (i : Fin 3) (x : OrbitIdeal i) :
    (tilde (R := CommRingCat.of (AffineRing i)) (ModuleCat.of (AffineRing i) (OrbitIdeal i))).val.obj (op ⊤) :=
  (tilde.toOpen (R := CommRingCat.of (AffineRing i)) (ModuleCat.of (AffineRing i) (OrbitIdeal i)) ⊤).hom
    (show ModuleCat.of (AffineRing i) (OrbitIdeal i) from x)

theorem orbitHomTopEquiv_evaluate (i : Fin 3)
    (H : (moduleSpecΓFunctor (R := CommRingCat.of (AffineRing i))).obj (orbitHomSheaf i))
    (x : OrbitIdeal i) :
    orbitHomTopEquiv i H x =
      (Scheme.ΓSpecIso (CommRingCat.of (AffineRing i))).hom
        (localLinearHomEvaluate (Spec (CommRingCat.of (AffineRing i))).sheaf
          (tilde (R := CommRingCat.of (AffineRing i)) (ModuleCat.of (AffineRing i) (OrbitIdeal i)))
          (structureModule (CommRingCat.of (AffineRing i))) ⊤ H
          (orbitElementSection i x)) := rfl

/-- Every original orbit functional has a unique actual local-sheaf
morphism on the full affine chart, retaining its original evaluations. -/
theorem orbitHomTopEquiv_symm_evaluate (i : Fin 3) (φ : OrbitDual i) (x : OrbitIdeal i) :
    localLinearHomEvaluate (Spec (CommRingCat.of (AffineRing i))).sheaf
        (tilde (R := CommRingCat.of (AffineRing i)) (ModuleCat.of (AffineRing i) (OrbitIdeal i)))
        (structureModule (CommRingCat.of (AffineRing i))) ⊤
        ((orbitHomTopEquiv i).symm φ)
        (orbitElementSection i x) =
      (Scheme.ΓSpecIso (CommRingCat.of (AffineRing i))).inv (φ x) := by
  have hx := LinearMap.congr_fun ((orbitHomTopEquiv i).apply_symm_apply φ) x
  have h := congrArg (fun a : AffineRing i =>
    (Scheme.ΓSpecIso (CommRingCat.of (AffineRing i))).inv a) hx
  simpa only [orbitHomTopEquiv_evaluate, Iso.hom_inv_id_apply] using h

#print axioms localHomEvaluationLinearMap
#print axioms topHomEquiv
#print axioms structureTopEquiv
#print axioms orbitHomTopEquiv
#print axioms orbitHomTopEquiv_symm_evaluate

end CycleQ2SeedAffineHomEvaluation
end
