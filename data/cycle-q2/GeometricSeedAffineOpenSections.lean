import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Native sections on an affine open inside a chart

For an affine open `V ≤ U` of an ambient scheme `X`, the canonical map
`Spec Γ(X,V) → U` identifies native global sections of a restricted
module sheaf with its sections on the inverse image of `V` in `U`.

The comparison is linear over the actual ring `Γ(X,V)`. Its source uses
the native affine-module action from `moduleSpecΓFunctor`; its target
uses restriction along `U.ι.app V`. The equality of these scalar maps
is proved from the normalization of `IsAffineOpen.fromSpec`.

Source-only draft: no Lean elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

namespace CycleQ2SeedAffineOpenSections

open CategoryTheory Opposite AlgebraicGeometry

variable {X : Scheme.{u}} {U V : X.Opens}

/-- The canonical affine-open map into the containing chart. -/
def overlapMap (hV : IsAffineOpen V) (h : V ≤ U) :
    Spec Γ(X, V) ⟶ U.toScheme :=
  hV.isoSpec.inv ≫ X.homOfLE h

instance overlapMap_isOpenImmersion (hV : IsAffineOpen V) (h : V ≤ U) :
    IsOpenImmersion (overlapMap hV h) := by
  unfold overlapMap
  infer_instance

theorem overlapMap_comp_ι (hV : IsAffineOpen V) (h : V ≤ U) :
    overlapMap hV h ≫ U.ι = hV.fromSpec := by
  rw [overlapMap, Category.assoc, Scheme.homOfLE_ι]
  rfl

theorem overlapMap_image_top (hV : IsAffineOpen V) (h : V ≤ U) :
    overlapMap hV h ''ᵁ ⊤ = U.ι ⁻¹ᵁ V := by
  rw [Scheme.Hom.image_top_eq_opensRange, overlapMap,
    Scheme.Hom.opensRange_comp_of_isIso, Scheme.opensRange_homOfLE]

theorem overlapMap_preimage (hV : IsAffineOpen V) (h : V ≤ U) :
    overlapMap hV h ⁻¹ᵁ (U.ι ⁻¹ᵁ V) = ⊤ := by
  rw [← overlapMap_image_top hV h, Scheme.Hom.preimage_image_eq]

private theorem fromSpec_appLE_self (hV : IsAffineOpen V)
    (e : ⊤ ≤ hV.fromSpec ⁻¹ᵁ V) :
    hV.fromSpec.appLE V ⊤ e = (Scheme.ΓSpecIso Γ(X, V)).inv := by
  rw [Scheme.Hom.appLE, hV.fromSpec_app_self, Category.assoc,
    ← Functor.map_comp]
  have hi : (eqToHom hV.fromSpec_preimage_self).op ≫ (homOfLE e).op =
      𝟙 (op (⊤ : (Spec Γ(X, V)).Opens)) := Subsingleton.elim _ _
  rw [hi, Functor.map_id, Category.comp_id]

/-- Pulling an ambient section to the affine source has the canonical
`ΓSpecIso` normalization, including the open-equality transport. -/
theorem overlapMap_appLE (hV : IsAffineOpen V) (h : V ≤ U) :
    U.ι.app V ≫ (overlapMap hV h).appLE (U.ι ⁻¹ᵁ V) ⊤
        (overlapMap_preimage hV h).ge =
      (Scheme.ΓSpecIso Γ(X, V)).inv := by
  rw [← Scheme.Hom.comp_appLE, overlapMap_comp_ι hV h]
  exact fromSpec_appLE_self hV _

/-- The coefficient map for restricted native affine sections is exactly
the actual ambient restriction map. -/
theorem overlapMap_coefficient (hV : IsAffineOpen V) (h : V ≤ U) :
    (Scheme.ΓSpecIso Γ(X, V)).inv ≫ ((overlapMap hV h).appIso ⊤).inv ≫
        U.toScheme.presheaf.map (eqToHom (overlapMap_image_top hV h).symm).op =
      U.ι.app V := by
  let δ := U.toScheme.presheaf.mapIso
    (eqToIso (overlapMap_image_top hV h).symm).op
  change (Scheme.ΓSpecIso Γ(X, V)).inv ≫
      ((overlapMap hV h).appIso ⊤).inv ≫ δ.hom = U.ι.app V
  have hc : (Scheme.ΓSpecIso Γ(X, V)).inv ≫
        ((overlapMap hV h).appIso ⊤).inv = U.ι.app V ≫ δ.inv := by
    change (Scheme.ΓSpecIso Γ(X, V)).inv ≫
        ((overlapMap hV h).appIso ⊤).inv =
      U.ι.app V ≫ U.toScheme.presheaf.map
        (eqToHom (overlapMap_image_top hV h)).op
    rw [← overlapMap_appLE hV h, Category.assoc, Scheme.Hom.appLE_appIso_inv]
    apply congrArg (fun i : op (U.ι ⁻¹ᵁ V) ⟶ op (overlapMap hV h ''ᵁ ⊤) =>
      U.ι.app V ≫ U.toScheme.presheaf.map i)
    exact Subsingleton.elim _ _
  rw [← Category.assoc, hc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The original module sheaf restricted to the canonical affine source. -/
abbrev affineRestriction (hV : IsAffineOpen V) (h : V ≤ U)
    (M : U.toScheme.Modules) :=
  M.restrict (overlapMap hV h)

/-- The additive comparison includes the identification of the image open. -/
def topSectionIso (hV : IsAffineOpen V) (h : V ≤ U) (M : U.toScheme.Modules) :
    Γ(affineRestriction hV h M, ⊤) ≅ Γ(M, U.ι ⁻¹ᵁ V) :=
  M.restrictAppIso (overlapMap hV h) ⊤ ≪≫
    M.presheaf.mapIso (eqToIso (overlapMap_image_top hV h).symm).op

theorem topSectionIso_smul (hV : IsAffineOpen V) (h : V ≤ U)
    (M : U.toScheme.Modules) (b : Γ(X, V))
    (s : Γ(affineRestriction hV h M, ⊤)) :
    (topSectionIso hV h M).hom (b • s) =
      U.ι.app V b • (topSectionIso hV h M).hom s := by
  rw [Scheme.Modules.smul_Spec_def]
  have hi : (⊤ : (Spec Γ(X, V)).Opens).leTop.op =
      𝟙 (op (⊤ : (Spec Γ(X, V)).Opens)) := Subsingleton.elim _ _
  rw [hi, Functor.map_id]
  change M.presheaf.map (eqToHom (overlapMap_image_top hV h).symm).op
      ((M.restrictAppIso (overlapMap hV h) ⊤).hom
        ((Scheme.ΓSpecIso Γ(X, V)).inv b • s)) =
    U.ι.app V b • M.presheaf.map
      (eqToHom (overlapMap_image_top hV h).symm).op
        ((M.restrictAppIso (overlapMap hV h) ⊤).hom s)
  rw [Scheme.Modules.smul_restrictAppIso_hom_apply, M.map_smul]
  have hb := congrArg (fun k : Γ(X, V) ⟶ Γ(U.toScheme, U.ι ⁻¹ᵁ V) => k b)
    (overlapMap_coefficient hV h)
  exact congrArg (fun a => a • M.presheaf.map
    (eqToHom (overlapMap_image_top hV h).symm).op
      ((M.restrictAppIso (overlapMap hV h) ⊤).hom s)) hb

theorem topSectionIso_naturality (hV : IsAffineOpen V) (h : V ≤ U)
    {M N : U.toScheme.Modules} (φ : M ⟶ N) :
    ((Scheme.Modules.restrictFunctor (overlapMap hV h)).map φ).app ⊤ ≫
        (topSectionIso hV h N).hom =
      (topSectionIso hV h M).hom ≫ φ.app (U.ι ⁻¹ᵁ V) := by
  change φ.app (overlapMap hV h ''ᵁ ⊤) ≫
      N.presheaf.map (eqToHom (overlapMap_image_top hV h).symm).op =
    M.presheaf.map (eqToHom (overlapMap_image_top hV h).symm).op ≫
      φ.app (U.ι ⁻¹ᵁ V)
  exact (φ.mapPresheaf.naturality
    (eqToHom (overlapMap_image_top hV h).symm).op).symm

/-- The target action is restriction from the actual ambient section ring.
It is installed locally, leaving the native affine action unchanged. -/
def ambientSectionModule (h : V ≤ U) (M : U.toScheme.Modules) :
    Module Γ(X, V) Γ(M, U.ι ⁻¹ᵁ V) :=
  Module.compHom _ (U.ι.app V).hom

/-- Native affine global sections are identified linearly with the actual
sections on the open inside the chart. -/
def topSectionEquiv (hV : IsAffineOpen V) (h : V ≤ U) (M : U.toScheme.Modules) :
    letI := ambientSectionModule h M
    (moduleSpecΓFunctor (R := Γ(X, V))).obj (affineRestriction hV h M)
      ≃ₗ[Γ(X, V)] Γ(M, U.ι ⁻¹ᵁ V) := by
  letI := ambientSectionModule h M
  refine
    { toFun := (topSectionIso hV h M).hom
      invFun := (topSectionIso hV h M).inv
      left_inv := fun s => Iso.hom_inv_id_apply (topSectionIso hV h M) s
      right_inv := fun s => Iso.inv_hom_id_apply (topSectionIso hV h M) s
      map_add' := fun s t => map_add (topSectionIso hV h M).hom.hom s t
      map_smul' := ?_ }
  intro b s
  change (topSectionIso hV h M).hom (b • s) =
    U.ι.app V b • (topSectionIso hV h M).hom s
  exact topSectionIso_smul hV h M b s

theorem topSectionEquiv_apply (hV : IsAffineOpen V) (h : V ≤ U)
    (M : U.toScheme.Modules)
    (s : (moduleSpecΓFunctor (R := Γ(X, V))).obj (affineRestriction hV h M)) :
    topSectionEquiv hV h M s = (topSectionIso hV h M).hom s := rfl

/-- Naturality uses the global-section map of the restricted original
sheaf morphism; it introduces no replacement module maps. -/
theorem topSectionEquiv_naturality (hV : IsAffineOpen V) (h : V ≤ U)
    {M N : U.toScheme.Modules} (φ : M ⟶ N)
    (s : (moduleSpecΓFunctor (R := Γ(X, V))).obj (affineRestriction hV h M)) :
    topSectionEquiv hV h N
        (((moduleSpecΓFunctor (R := Γ(X, V))).map
          ((Scheme.Modules.restrictFunctor (overlapMap hV h)).map φ)).hom s) =
      φ.app (U.ι ⁻¹ᵁ V) (topSectionEquiv hV h M s) := by
  change (topSectionIso hV h N).hom
      (((Scheme.Modules.restrictFunctor (overlapMap hV h)).map φ).app ⊤ s) =
    φ.app (U.ι ⁻¹ᵁ V) ((topSectionIso hV h M).hom s)
  exact congrArg (fun k : Γ(affineRestriction hV h M, ⊤) ⟶
    Γ(N, U.ι ⁻¹ᵁ V) => k s) (topSectionIso_naturality hV h φ)

#print axioms overlapMap_image_top
#print axioms overlapMap_appLE
#print axioms overlapMap_coefficient
#print axioms topSectionIso_smul
#print axioms topSectionEquiv
#print axioms topSectionEquiv_naturality

end CycleQ2SeedAffineOpenSections
end
