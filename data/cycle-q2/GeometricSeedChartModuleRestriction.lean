import Proposal.GeometricSeedChartSectionScalars

/-!
# Restricting native module sections through the actual chart isomorphism

Restriction along a scheme isomorphism first gives an additive section
isomorphism on its image open. Transport to the inverse-preimage open
has scalar map equal to the actual inverse chart map on sections.
The equality of those coefficient maps is proved explicitly.

For an affine chart of an ambient scheme, the resulting comparison is
linear over the actual ambient section ring. On the projective side its
action is the ordinary restriction through the chart inclusion. On the
affine side it is the action through the existing chartSectionIso.
The comparison is natural in the original module-sheaf morphism.

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

namespace CycleQ2SeedChartModuleRestriction

open CategoryTheory Opposite AlgebraicGeometry
open CycleQ2GeometricAffineChartSections CycleQ2SeedChartSectionScalars

section SchemeIso

variable {X Y : Scheme.{u}} (e : X ≅ Y) (W : X.Opens)

/-- The inverse coefficient map used by restriction is the actual inverse
scheme morphism, after the canonical identification of the two opens. -/
theorem inverse_chart_app :
    (e.hom.appIso W).inv ≫
      Y.presheaf.map (eqToHom (Scheme.Hom.inv_preimage e W)).op =
        e.inv.app W := by
  simpa only [Scheme.Hom.id_app, Category.id_comp, Category.comp_id] using
    (IsOpenImmersion.app_eq_appIso_inv_app_of_comp_eq
      e.inv e.hom (𝟙 Y) e.inv_hom_id.symm W).symm

def restrictionSectionIso (M : Y.Modules) :
    Γ(M.restrict e.hom, W) ≅ Γ(M, e.inv ⁻¹ᵁ W) :=
  M.restrictAppIso e.hom W ≪≫
    M.presheaf.mapIso (eqToIso (Scheme.Hom.inv_preimage e W)).op

/-- Scalar compatibility includes the open-equality transport; the two
inverse section maps are compared by inverse_chart_app. -/
theorem restrictionSectionIso_smul (M : Y.Modules) (r : Γ(X, W))
    (s : Γ(M.restrict e.hom, W)) :
    (restrictionSectionIso e W M).hom (r • s) =
      e.inv.app W r • (restrictionSectionIso e W M).hom s := by
  change M.presheaf.map (eqToHom (Scheme.Hom.inv_preimage e W)).op
      ((M.restrictAppIso e.hom W).hom (r • s)) =
    e.inv.app W r • M.presheaf.map (eqToHom (Scheme.Hom.inv_preimage e W)).op
      ((M.restrictAppIso e.hom W).hom s)
  rw [Scheme.Modules.smul_restrictAppIso_hom_apply, M.map_smul]
  have hr := congrArg (fun k : Γ(X, W) ⟶ Γ(Y, e.inv ⁻¹ᵁ W) => k r)
    (inverse_chart_app e W)
  exact congrArg (fun a => a • M.presheaf.map
    (eqToHom (Scheme.Hom.inv_preimage e W)).op
      ((M.restrictAppIso e.hom W).hom s)) hr

/-- The section comparison uses the restricted original morphism. -/
theorem restrictionSectionIso_naturality {M N : Y.Modules} (φ : M ⟶ N) :
    ((Scheme.Modules.restrictFunctor e.hom).map φ).app W ≫
        (restrictionSectionIso e W N).hom =
      (restrictionSectionIso e W M).hom ≫ φ.app (e.inv ⁻¹ᵁ W) := by
  change φ.app (e.hom ''ᵁ W) ≫
      N.presheaf.map (eqToHom (Scheme.Hom.inv_preimage e W)).op =
    M.presheaf.map (eqToHom (Scheme.Hom.inv_preimage e W)).op ≫
      φ.app (e.inv ⁻¹ᵁ W)
  exact (φ.mapPresheaf.naturality
    (eqToHom (Scheme.Hom.inv_preimage e W)).op).symm

end SchemeIso

section AffineChart

variable {X : Scheme.{0}} {U : X.Opens} {A : Type} [CommRing A]
variable (e : U.toScheme ≅ Spec (CommRingCat.of A)) (V : Over U)
variable (M : (Spec (CommRingCat.of A)).Modules)

/-- The ambient section ring acts by the actual open-immersion restriction. -/
def chartRestrictedModule :
    Module Γ(X, V.left) Γ(M.restrict e.hom, U.ι ⁻¹ᵁ V.left) :=
  Module.compHom _ (U.ι.app V.left).hom

/-- Native restricted sections and native affine sections are identified
linearly over the actual ambient section ring, with the two stated actions. -/
def chartRestrictionEquiv :
    letI := chartRestrictedModule e V M
    letI := chartSectionsModule e V M
    Γ(M.restrict e.hom, U.ι ⁻¹ᵁ V.left) ≃ₗ[Γ(X, V.left)]
      Γ(M, (chartOpensEquiv e).functor.obj V) := by
  letI := chartRestrictedModule e V M
  letI := chartSectionsModule e V M
  refine
    { toFun := (restrictionSectionIso e (U.ι ⁻¹ᵁ V.left) M).hom
      invFun := (restrictionSectionIso e (U.ι ⁻¹ᵁ V.left) M).inv
      left_inv := fun s => Iso.hom_inv_id_apply
        (restrictionSectionIso e (U.ι ⁻¹ᵁ V.left) M) s
      right_inv := fun s => Iso.inv_hom_id_apply
        (restrictionSectionIso e (U.ι ⁻¹ᵁ V.left) M) s
      map_add' := fun s t => map_add
        (restrictionSectionIso e (U.ι ⁻¹ᵁ V.left) M).hom.hom s t
      map_smul' := ?_ }
  intro b s
  change (restrictionSectionIso e (U.ι ⁻¹ᵁ V.left) M).hom
      (U.ι.app V.left b • s) =
    e.inv.app (U.ι ⁻¹ᵁ V.left) (U.ι.app V.left b) •
      (restrictionSectionIso e (U.ι ⁻¹ᵁ V.left) M).hom s
  exact restrictionSectionIso_smul e (U.ι ⁻¹ᵁ V.left) M (U.ι.app V.left b) s

theorem chartRestrictionEquiv_naturality
    {M N : (Spec (CommRingCat.of A)).Modules} (φ : M ⟶ N)
    (s : Γ(M.restrict e.hom, U.ι ⁻¹ᵁ V.left)) :
    chartRestrictionEquiv e V N
        (((Scheme.Modules.restrictFunctor e.hom).map φ).app (U.ι ⁻¹ᵁ V.left) s) =
      φ.app ((chartOpensEquiv e).functor.obj V) (chartRestrictionEquiv e V M s) :=
  congrArg (fun k : Γ(M.restrict e.hom, U.ι ⁻¹ᵁ V.left) ⟶
    Γ(N, (chartOpensEquiv e).functor.obj V) => k s)
      (restrictionSectionIso_naturality e (U.ι ⁻¹ᵁ V.left) φ)

end AffineChart

#print axioms inverse_chart_app
#print axioms restrictionSectionIso_smul
#print axioms restrictionSectionIso_naturality
#print axioms chartRestrictionEquiv
#print axioms chartRestrictionEquiv_naturality

end CycleQ2SeedChartModuleRestriction
end
