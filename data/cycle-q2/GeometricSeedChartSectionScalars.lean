import Proposal.GeometricAffineChartSections
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# The actual chart coefficient map and native section scalar actions

The existing chart section-ring isomorphism respects the original affine
coefficient ring when the projective-side algebra is defined by the exact
`chartSection` map. Its algebra compatibility is the inverse-isomorphism
cancellation already built into that map.

Native sections of an arbitrary module sheaf on the affine spectrum retain
their native affine-ring action. Pulling their section-ring action back
through the chart isomorphism supplies an action of the actual projective
section ring, and the two actions form a scalar tower. All extra structures
are explicit definitions or local bindings, not competing global instances.

Source-only draft: no Lean elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the remaining certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedChartSectionScalars

open CategoryTheory Opposite AlgebraicGeometry
open CycleQ2GeometricAffineChartSections

variable {X : Scheme.{0}} {U : X.Opens} {A : Type} [CommRing A]
variable (e : U.toScheme ≅ Spec (CommRingCat.of A)) (V : Over U)

/-- The coefficient algebra uses the existing chart section map exactly. -/
def chartSectionAlgebra : Algebra A Γ(X, V.left) :=
  (chartSection e V).toAlgebra

/-- The actual section-ring isomorphism is an algebra equivalence over A. -/
def chartSectionAlgEquiv :
    letI := chartSectionAlgebra e V
    Γ(X, V.left) ≃ₐ[A]
      Γ(Spec (CommRingCat.of A), (chartOpensEquiv e).functor.obj V) := by
  letI := chartSectionAlgebra e V
  refine { (chartSectionIso e V).commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro a
  change (chartSectionIso e V).hom
      ((chartSectionIso e V).inv
        (algebraMap A Γ(Spec (CommRingCat.of A), (chartOpensEquiv e).functor.obj V) a)) = _
  exact Iso.inv_hom_id_apply (chartSectionIso e V) _

theorem chartSectionAlgEquiv_apply (b : Γ(X, V.left)) :
    letI := chartSectionAlgebra e V
    chartSectionAlgEquiv e V b = (chartSectionIso e V).hom b := rfl

variable (M : (Spec (CommRingCat.of A)).Modules)

/-- Pull back the intrinsic native section-ring action along the actual
chart section-ring map. The existing native A-action is not replaced. -/
def chartSectionsModule :
    Module Γ(X, V.left) Γ(M, (chartOpensEquiv e).functor.obj V) :=
  Module.compHom _ (chartSectionIso e V).hom.hom

theorem chartSections_smul (b : Γ(X, V.left))
    (s : Γ(M, (chartOpensEquiv e).functor.obj V)) :
    letI := chartSectionsModule e V M
    b • s = (chartSectionIso e V).hom b • s := rfl

/-- Restricting the projective-section action along the actual affine
coefficient map recovers the native affine-ring action on sheaf sections. -/
theorem chartSections_algebraMap_smul (a : A)
    (s : Γ(M, (chartOpensEquiv e).functor.obj V)) :
    letI := chartSectionAlgebra e V
    letI := chartSectionsModule e V M
    algebraMap A Γ(X, V.left) a • s = a • s := by
  letI := chartSectionAlgebra e V
  letI := chartSectionsModule e V M
  change chartSectionAlgEquiv e V (algebraMap A Γ(X, V.left) a) • s = a • s
  rw [(chartSectionAlgEquiv e V).commutes]
  exact IsScalarTower.algebraMap_smul
    Γ(Spec (CommRingCat.of A), (chartOpensEquiv e).functor.obj V) a s

/-- The actual chart coefficients and native sheaf-section scalars are compatible. -/
theorem chartSections_isScalarTower :
    letI := chartSectionAlgebra e V
    letI := chartSectionsModule e V M
    IsScalarTower A Γ(X, V.left) Γ(M, (chartOpensEquiv e).functor.obj V) := by
  letI := chartSectionAlgebra e V
  letI := chartSectionsModule e V M
  apply IsScalarTower.of_algebraMap_smul
  intro a s
  exact chartSections_algebraMap_smul e V M a s

#print axioms chartSectionAlgEquiv
#print axioms chartSections_algebraMap_smul
#print axioms chartSections_isScalarTower

end CycleQ2SeedChartSectionScalars
end
