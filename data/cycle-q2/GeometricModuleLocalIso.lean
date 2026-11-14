import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Proposal.GeometricSheafLocalIso

/-!
# Gluing actual local isomorphisms of sheaves of modules

Compatible natural linear equivalences on all subopens of two covering opens
produce an isomorphism in the actual category of sheaves of modules. The
underlying section maps are the unique additive sheaf gluings constructed in
`GeometricSheafLocalIso`; their scalar compatibility is proved by restriction
to the two opens. Both inverse identities follow from the local inverses.

This is a gluing theorem for supplied local module isomorphisms. It does not
assert or assume a global cotangent or canonical-sheaf identification.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
universe u

namespace CycleQ2GeometricModuleLocalIso

open CategoryTheory Opposite TopologicalSpace

variable {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}

/-- The actual underlying additive sheaf of a sheaf of modules. -/
abbrev addSheaf (M : SheafOfModules.{u} R) : CycleQ2GeometricSheafLocalIso.AddSheaf X :=
  (SheafOfModules.toSheaf R).obj M

local instance additiveSectionModule (M : SheafOfModules.{u} R) (O : Opens X) :
    Module (R.obj.obj (op O)) ((addSheaf M).obj.obj (op O)) :=
  (M.val.obj (op O)).isModule

/-- Restrictions of the underlying additive sheaf are semilinear over the
restriction homomorphisms of the given ring sheaf. -/
theorem res_smul (M : SheafOfModules.{u} R) {O P : Opens X} (hPO : P ≤ O)
    (a : R.obj.obj (op O)) (s : M.val.obj (op O)) :
    CycleQ2GeometricSheafLocalIso.res (addSheaf M) hPO (a • s) =
      R.obj.map (homOfLE hPO).op a • CycleQ2GeometricSheafLocalIso.res (addSheaf M) hPO s :=
  M.val.map_smul (homOfLE hPO).op a s

/-- A natural family of linear equivalences on all subopens of a patch. -/
structure PatchIso (M N : SheafOfModules.{u} R) (U : Opens X) where
  app (O : Opens X) (hO : O ≤ U) :
    M.val.obj (op O) ≃ₗ[R.obj.obj (op O)] N.val.obj (op O)
  naturality {O P : Opens X} (hPO : P ≤ O) (hO : O ≤ U)
      (s : M.val.obj (op O)) :
    N.val.map (homOfLE hPO).op (app O hO s) =
      app P (hPO.trans hO) (M.val.map (homOfLE hPO).op s)

namespace PatchIso

variable {M N : SheafOfModules.{u} R} {U V : Opens X}

/-- Forget scalar compatibility, retaining the same actual local maps. -/
def toAdditive (e : PatchIso M N U) :
    CycleQ2GeometricSheafLocalIso.PatchIso (addSheaf M) (addSheaf N) U where
  app O hO := (e.app O hO).toAddEquiv
  naturality hPO hO s := e.naturality hPO hO s

/-- The natural local linear inverses. -/
def symm (e : PatchIso M N U) : PatchIso N M U where
  app O hO := (e.app O hO).symm
  naturality hPO hO s := by
    apply (e.app _ (hPO.trans hO)).injective
    rw [LinearEquiv.apply_symm_apply]
    have h := e.naturality hPO hO ((e.app _ hO).symm s)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

@[simp] theorem symm_toAdditive (e : PatchIso M N U) :
    e.symm.toAdditive = e.toAdditive.symm := rfl

/-- Agreement of the two maps on every common subopen. -/
def Compatible (eU : PatchIso M N U) (eV : PatchIso M N V) : Prop :=
  ∀ (O : Opens X) (hU : O ≤ U) (hV : O ≤ V) (s : M.val.obj (op O)),
    eU.app O hU s = eV.app O hV s

theorem Compatible.toAdditive {eU : PatchIso M N U} {eV : PatchIso M N V}
    (h : eU.Compatible eV) : eU.toAdditive.Compatible eV.toAdditive := h

theorem Compatible.symm {eU : PatchIso M N U} {eV : PatchIso M N V}
    (h : eU.Compatible eV) : eU.symm.Compatible eV.symm :=
  CycleQ2GeometricSheafLocalIso.PatchIso.Compatible.symm h.toAdditive

end PatchIso

section Gluing

variable (M N : SheafOfModules.{u} R) (U V : Opens X) (hcover : U ⊔ V = ⊤)
  (eU : PatchIso M N U) (eV : PatchIso M N V) (hc : eU.Compatible eV)

/-- The section map is the genuine unique sheaf gluing. -/
def mapSection (O : Opens X) (s : M.val.obj (op O)) : N.val.obj (op O) :=
  CycleQ2GeometricSheafLocalIso.mapSection (addSheaf M) (addSheaf N) U V hcover
    eU.toAdditive eV.toAdditive hc.toAdditive O s

/-- Scalar compatibility is checked on the actual covering restrictions. -/
theorem mapSection_smul (O : Opens X) (a : R.obj.obj (op O))
    (s : M.val.obj (op O)) :
    mapSection M N U V hcover eU eV hc O (a • s) =
      a • mapSection M N U V hcover eU eV hc O s := by
  have hcov : O ≤ (O ⊓ U) ⊔ (O ⊓ V) := by
    rw [← inf_sup_left, hcover, inf_top_eq]
  apply (addSheaf N).eq_of_locally_eq₂
    (homOfLE (show O ⊓ U ≤ O from inf_le_left))
    (homOfLE (show O ⊓ V ≤ O from inf_le_left)) hcov
  · change CycleQ2GeometricSheafLocalIso.res (addSheaf N) (show O ⊓ U ≤ O from inf_le_left)
      (CycleQ2GeometricSheafLocalIso.mapSection (addSheaf M) (addSheaf N) U V hcover
        eU.toAdditive eV.toAdditive hc.toAdditive O (a • s)) =
      CycleQ2GeometricSheafLocalIso.res (addSheaf N) inf_le_left
        (a • CycleQ2GeometricSheafLocalIso.mapSection (addSheaf M) (addSheaf N) U V hcover
          eU.toAdditive eV.toAdditive hc.toAdditive O s)
    rw [CycleQ2GeometricSheafLocalIso.mapSection_restrictU, res_smul, res_smul,
      CycleQ2GeometricSheafLocalIso.mapSection_restrictU]
    exact (eU.app (O ⊓ U) inf_le_right).map_smul _ _
  · change CycleQ2GeometricSheafLocalIso.res (addSheaf N) (show O ⊓ V ≤ O from inf_le_left)
      (CycleQ2GeometricSheafLocalIso.mapSection (addSheaf M) (addSheaf N) U V hcover
        eU.toAdditive eV.toAdditive hc.toAdditive O (a • s)) =
      CycleQ2GeometricSheafLocalIso.res (addSheaf N) inf_le_left
        (a • CycleQ2GeometricSheafLocalIso.mapSection (addSheaf M) (addSheaf N) U V hcover
          eU.toAdditive eV.toAdditive hc.toAdditive O s)
    rw [CycleQ2GeometricSheafLocalIso.mapSection_restrictV, res_smul, res_smul,
      CycleQ2GeometricSheafLocalIso.mapSection_restrictV]
    exact (eV.app (O ⊓ V) inf_le_right).map_smul _ _

/-- The glued additive sheaf morphism with its proved module compatibility. -/
def glueHom : M ⟶ N where
  val := PresheafOfModules.homMk
    (CycleQ2GeometricSheafLocalIso.glueHom (addSheaf M) (addSheaf N) U V hcover
      eU.toAdditive eV.toAdditive hc.toAdditive).hom
    (fun O a s => mapSection_smul M N U V hcover eU eV hc O.unop a s)

@[simp] theorem glueHom_app (O : Opens X) (s : M.val.obj (op O)) :
    (glueHom M N U V hcover eU eV hc).val.app (op O) s =
      mapSection M N U V hcover eU eV hc O s := rfl

/-- Forgetting the module structure gives exactly the earlier additive gluing. -/
theorem toSheaf_glueHom :
    (SheafOfModules.toSheaf R).map (glueHom M N U V hcover eU eV hc) =
      CycleQ2GeometricSheafLocalIso.glueHom (addSheaf M) (addSheaf N) U V hcover
        eU.toAdditive eV.toAdditive hc.toAdditive := by
  rfl

/-- The compatible local module isomorphisms glue to a genuine global
isomorphism of sheaves of modules. -/
def glueIso : M ≅ N where
  hom := glueHom M N U V hcover eU eV hc
  inv := glueHom N M U V hcover eU.symm eV.symm hc.symm
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro O
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact CycleQ2GeometricSheafLocalIso.mapSection_symm_apply (addSheaf M) (addSheaf N) U V hcover
      eU.toAdditive eV.toAdditive hc.toAdditive O.unop s
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro O
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact CycleQ2GeometricSheafLocalIso.mapSection_apply_symm (addSheaf M) (addSheaf N) U V hcover
      eU.toAdditive eV.toAdditive hc.toAdditive O.unop s

@[simp] theorem glueIso_hom_app (O : Opens X) (s : M.val.obj (op O)) :
    (glueIso M N U V hcover eU eV hc).hom.val.app (op O) s =
      mapSection M N U V hcover eU eV hc O s := rfl

@[simp] theorem glueIso_hom_app_of_leU (O : Opens X) (hO : O ≤ U)
    (s : M.val.obj (op O)) :
    (glueIso M N U V hcover eU eV hc).hom.val.app (op O) s = eU.app O hO s :=
  CycleQ2GeometricSheafLocalIso.mapSection_of_leU (addSheaf M) (addSheaf N) U V hcover
    eU.toAdditive eV.toAdditive hc.toAdditive O hO s

@[simp] theorem glueIso_hom_app_of_leV (O : Opens X) (hO : O ≤ V)
    (s : M.val.obj (op O)) :
    (glueIso M N U V hcover eU eV hc).hom.val.app (op O) s = eV.app O hO s :=
  CycleQ2GeometricSheafLocalIso.mapSection_of_leV (addSheaf M) (addSheaf N) U V hcover
    eU.toAdditive eV.toAdditive hc.toAdditive O hO s

@[simp] theorem glueIso_inv_app_of_leU (O : Opens X) (hO : O ≤ U)
    (s : N.val.obj (op O)) :
    (glueIso M N U V hcover eU eV hc).inv.val.app (op O) s = (eU.app O hO).symm s :=
  CycleQ2GeometricSheafLocalIso.mapSection_of_leU (addSheaf N) (addSheaf M) U V hcover
    eU.toAdditive.symm eV.toAdditive.symm hc.toAdditive.symm O hO s

@[simp] theorem glueIso_inv_app_of_leV (O : Opens X) (hO : O ≤ V)
    (s : N.val.obj (op O)) :
    (glueIso M N U V hcover eU eV hc).inv.val.app (op O) s = (eV.app O hO).symm s :=
  CycleQ2GeometricSheafLocalIso.mapSection_of_leV (addSheaf N) (addSheaf M) U V hcover
    eU.toAdditive.symm eV.toAdditive.symm hc.toAdditive.symm O hO s

/-- The forward module isomorphism has the prescribed restriction on every
subopen of the first patch, even for a section on a larger open. -/
theorem glueIso_hom_restrict_toU {O P : Opens X} (hPO : P ≤ O) (hPU : P ≤ U)
    (s : M.val.obj (op O)) :
    N.val.map (homOfLE hPO).op ((glueIso M N U V hcover eU eV hc).hom.val.app (op O) s) =
      eU.app P hPU (M.val.map (homOfLE hPO).op s) :=
  CycleQ2GeometricSheafLocalIso.mapSection_restrict_toU (addSheaf M) (addSheaf N) U V hcover
    eU.toAdditive eV.toAdditive hc.toAdditive hPO hPU s

theorem glueIso_hom_restrict_toV {O P : Opens X} (hPO : P ≤ O) (hPV : P ≤ V)
    (s : M.val.obj (op O)) :
    N.val.map (homOfLE hPO).op ((glueIso M N U V hcover eU eV hc).hom.val.app (op O) s) =
      eV.app P hPV (M.val.map (homOfLE hPO).op s) :=
  CycleQ2GeometricSheafLocalIso.mapSection_restrict_toV (addSheaf M) (addSheaf N) U V hcover
    eU.toAdditive eV.toAdditive hc.toAdditive hPO hPV s

#print axioms mapSection_smul
#print axioms glueIso
#print axioms glueIso_hom_app_of_leU
#print axioms glueIso_inv_app_of_leV
#print axioms glueIso_hom_restrict_toU

end Gluing
end CycleQ2GeometricModuleLocalIso
end
