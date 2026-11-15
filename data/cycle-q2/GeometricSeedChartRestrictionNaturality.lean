import Proposal.GeometricSeedChartModuleRestriction

/-!
# Chart section comparisons commute with restriction to subopens

The native module-section comparison through a scheme isomorphism commutes
with every open restriction. For an affine chart this is the restriction
square on the existing over-site, using its actual chart-open functor.

The coefficient comparison is natural under the same restrictions. Both
native module actions therefore give semilinear restriction maps over the
actual ambient structure-sheaf restriction. No localization or additional
geometric hypothesis is needed for these results.

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

namespace CycleQ2SeedChartRestrictionNaturality

open CategoryTheory Opposite AlgebraicGeometry
open CycleQ2GeometricAffineChartSections CycleQ2SeedChartSectionScalars
  CycleQ2SeedChartModuleRestriction

/-- The actual inverse-chart section comparison commutes with open restrictions. -/
theorem restrictionSectionIso_restriction
    {X Y : Scheme.{u}} (e : X ≅ Y) (M : Y.Modules)
    {W₁ W₂ : X.Opens} (a : W₁ ⟶ W₂) :
    (M.restrict e.hom).presheaf.map a.op ≫
        (restrictionSectionIso e W₁ M).hom =
      (restrictionSectionIso e W₂ M).hom ≫
        M.presheaf.map
          ((TopologicalSpace.Opens.map e.inv.base).map a).op := by
  change
    (M.restrict e.hom).presheaf.map a.op ≫
        ((M.restrictAppIso e.hom W₁).hom ≫
          M.presheaf.map
            (eqToHom (Scheme.Hom.inv_preimage e W₁)).op) =
      ((M.restrictAppIso e.hom W₂).hom ≫
        M.presheaf.map
          (eqToHom (Scheme.Hom.inv_preimage e W₂)).op) ≫
        M.presheaf.map
          ((TopologicalSpace.Opens.map e.inv.base).map a).op
  rw [← Category.assoc, Scheme.Modules.map_restrictAppIso_hom]
  simp only [Category.assoc]
  congr 1
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg M.presheaf.map (Subsingleton.elim _ _)

section AffineChart

variable {X : Scheme.{0}} {U : X.Opens} {A : Type} [CommRing A]
variable (e : U.toScheme ≅ Spec (CommRingCat.of A))
variable (M : (Spec (CommRingCat.of A)).Modules)

/-- The existing ambient-ring-linear comparison uses the native restriction
maps on both sides of every over-site morphism. -/
theorem chartRestrictionEquiv_restriction {V W : Over U} (f : V ⟶ W)
    (s : Γ(M.restrict e.hom, U.ι ⁻¹ᵁ W.left)) :
    chartRestrictionEquiv e V M
        ((M.restrict e.hom).presheaf.map
          ((TopologicalSpace.Opens.map U.ι.base).map f.left).op s) =
      M.presheaf.map ((chartOpensEquiv e).functor.map f).op
        (chartRestrictionEquiv e W M s) := by
  exact congrArg
    (fun k : Γ(M.restrict e.hom, U.ι ⁻¹ᵁ W.left) ⟶
      Γ(M, (chartOpensEquiv e).functor.obj V) => k s)
    (restrictionSectionIso_restriction e M
      ((TopologicalSpace.Opens.map U.ι.base).map f.left))

/-- The actual chart coefficient maps commute with the ambient restriction. -/
theorem chartSectionIso_restriction {V W : Over U} (f : V ⟶ W)
    (b : Γ(X, W.left)) :
    (chartSectionIso e V).hom (X.presheaf.map f.left.op b) =
      (Spec (CommRingCat.of A)).presheaf.map
        ((chartOpensEquiv e).functor.map f).op
        ((chartSectionIso e W).hom b) := by
  exact congrArg
    (fun k : Γ(X, W.left) ⟶
      Γ(Spec (CommRingCat.of A), (chartOpensEquiv e).functor.obj V) => k b)
    ((chartSectionsIso e).hom.naturality f.op)

/-- Native affine restrictions are semilinear for the proved ambient-ring action. -/
theorem chartSections_restriction_smul {V W : Over U} (f : V ⟶ W)
    (b : Γ(X, W.left)) (s : Γ(M, (chartOpensEquiv e).functor.obj W)) :
    letI := chartSectionsModule e V M
    letI := chartSectionsModule e W M
    M.presheaf.map ((chartOpensEquiv e).functor.map f).op (b • s) =
      X.presheaf.map f.left.op b •
        M.presheaf.map ((chartOpensEquiv e).functor.map f).op s := by
  letI := chartSectionsModule e V M
  letI := chartSectionsModule e W M
  change M.presheaf.map ((chartOpensEquiv e).functor.map f).op
      ((chartSectionIso e W).hom b • s) =
    (chartSectionIso e V).hom (X.presheaf.map f.left.op b) •
      M.presheaf.map ((chartOpensEquiv e).functor.map f).op s
  rw [M.map_smul]
  exact congrArg
    (fun a => a • M.presheaf.map ((chartOpensEquiv e).functor.map f).op s)
    (chartSectionIso_restriction e f b).symm

/-- Native restricted-chart sections are semilinear for the same ambient restriction. -/
theorem chartRestricted_restriction_smul {V W : Over U} (f : V ⟶ W)
    (b : Γ(X, W.left)) (s : Γ(M.restrict e.hom, U.ι ⁻¹ᵁ W.left)) :
    letI := chartRestrictedModule e V M
    letI := chartRestrictedModule e W M
    (M.restrict e.hom).presheaf.map
        ((TopologicalSpace.Opens.map U.ι.base).map f.left).op (b • s) =
      X.presheaf.map f.left.op b •
        (M.restrict e.hom).presheaf.map
          ((TopologicalSpace.Opens.map U.ι.base).map f.left).op s := by
  letI := chartRestrictedModule e V M
  letI := chartRestrictedModule e W M
  change (M.restrict e.hom).presheaf.map
      ((TopologicalSpace.Opens.map U.ι.base).map f.left).op
      (U.ι.app W.left b • s) =
    U.ι.app V.left (X.presheaf.map f.left.op b) •
      (M.restrict e.hom).presheaf.map
        ((TopologicalSpace.Opens.map U.ι.base).map f.left).op s
  rw [(M.restrict e.hom).map_smul]
  have hb := congrArg
    (fun k : Γ(X, W.left) ⟶ Γ(U.toScheme, U.ι ⁻¹ᵁ V.left) => k b)
    (U.ι.naturality f.left.op)
  exact congrArg
    (fun a => a • (M.restrict e.hom).presheaf.map
      ((TopologicalSpace.Opens.map U.ι.base).map f.left).op s)
    hb.symm

end AffineChart

#print axioms restrictionSectionIso_restriction
#print axioms chartRestrictionEquiv_restriction
#print axioms chartSectionIso_restriction
#print axioms chartSections_restriction_smul
#print axioms chartRestricted_restriction_smul

end CycleQ2SeedChartRestrictionNaturality
end
