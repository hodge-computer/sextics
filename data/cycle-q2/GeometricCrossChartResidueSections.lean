import Proposal.GeometricSurfaceResidueSections

/-!
# Transport of actual residue sections from a coordinate determinant

Status: source-only proof draft; verification is deferred at the user's request.
The two forms below are the original normalized determinant residues in the
actual differential sheaf. A proved differential expansion and its mixed
Jacobian determinant give their transition on an arbitrary common subopen.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2CrossChartResidueSections

open CategoryTheory Opposite AlgebraicGeometry Module
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricAffineChartSections
  CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSurfaceExteriorSections
  CycleQ2GeometricSurfaceResidueSections CycleQ2GeometricExteriorSheaf

variable {X : Scheme.{0}} {U₁ U₂ : X.Opens}
  (f : X ⟶ Spec (CommRingCat.of ℂ))
  (v₁ v₂ : Fin 2 → SurfacePoly) (n₁ t₁ n₂ t₂ : SurfacePoly)
  (e₁ : U₁.toScheme ≅ Spec (CommRingCat.of (AdjunctionPatch v₁ n₁ t₁)))
  (e₂ : U₂.toScheme ≅ Spec (CommRingCat.of (AdjunctionPatch v₂ n₂ t₂)))
  (he₁ : e₁.inv ≫ U₁.ι ≫ f =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (AdjunctionPatch v₁ n₁ t₁))))
  (he₂ : e₂.inv ≫ U₂.ι ≫ f =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (AdjunctionPatch v₂ n₂ t₂))))
  (V : X.Opens) (hV₁ : V ≤ U₁) (hV₂ : V ≤ U₂)
  (pulled : SurfacePoly → Fin 4 → Γ(X,V)) (factor : Γ(X,V))
  (hD : ∀ p : SurfacePoly,
    polynomialDifferentialSection_common f v₂ n₂ t₂ e₂ (Over.mk (homOfLE hV₂)) p =
      chartAmbientDifferential f v₁ n₁ t₁ e₁ (Over.mk (homOfLE hV₁)) (pulled p))
  (hdet : ∀ p q : SurfacePoly,
    Matrix.det ![chartEquationGradient v₁ n₁ t₁ e₁ (Over.mk (homOfLE hV₁)) 0,
      chartEquationGradient v₁ n₁ t₁ e₁ (Over.mk (homOfLE hV₁)) 1,
      pulled p, pulled q] =
    factor * chartSurfaceSectionMap v₂ n₂ t₂ e₂ (Over.mk (homOfLE hV₂))
      (augmentedJacobian v₂ p q))

/-- The actual normalized residue transition follows from the actual
coordinate differential expansion and its mixed determinant. -/
theorem residueSection_transition :
    chartResidueSection_common f v₂ n₂ t₂ e₂ he₂ (Over.mk (homOfLE hV₂)) =
      factor • chartResidueSection_common f v₁ n₁ t₁ e₁ he₁
        (Over.mk (homOfLE hV₁)) := by
  let E := chartResidueCoordinate_common f v₁ n₁ t₁ e₁ he₁
    (Over.mk (homOfLE hV₁))
  let J : Γ(X,V) := chartSurfaceSectionMap v₂ n₂ t₂ e₂
    (Over.mk (homOfLE hV₂)) (augmentedJacobian v₂ n₂ t₂)
  have hJ : IsUnit J :=
    (IsLocalization.Away.algebraMap_isUnit (S := AdjunctionPatch v₂ n₂ t₂)
      (augmentedJacobian v₂ n₂ t₂)).map (chartSection e₂ (Over.mk (homOfLE hV₂)))
  have hp : E
      (J • chartResidueSection_common f v₂ n₂ t₂ e₂ he₂
        (Over.mk (homOfLE hV₂))) = factor * J := by
    rw [chartJacobian_smul_residue_common, hD n₂, hD t₂]
    exact (chartResidueCoordinate_ambient_pair f v₁ n₁ t₁ e₁ he₁
      (Over.mk (homOfLE hV₁)) (pulled n₂) (pulled t₂)).trans (hdet n₂ t₂)
  apply E.injective
  have hnorm : E (chartResidueSection_common f v₁ n₁ t₁ e₁ he₁
      (Over.mk (homOfLE hV₁))) = 1 :=
    chartResidueSection_common_normalization f v₁ n₁ t₁ e₁ he₁ _
  rw [map_smul, hnorm, smul_eq_mul, mul_one]
  apply hJ.mul_left_cancel
  exact (map_smul E J _).symm.trans (hp.trans (mul_comm factor J))

/-- Passing through the canonical exterior-sheaf unit preserves the same
transition and the same actual coefficient. -/
theorem residueSheafSection_transition :
    chartResidueSheafSection f v₂ n₂ t₂ e₂ he₂ (Over.mk (homOfLE hV₂)) =
      factor • chartResidueSheafSection f v₁ n₁ t₁ e₁ he₁
        (Over.mk (homOfLE hV₁)) := by
  have h := congrArg
    (exteriorSection X.sheaf (differentialSheaf X.sheaf (schemeCoefficient f)).val 2 V)
    (residueSection_transition f v₁ v₂ n₁ t₁ n₂ t₂ e₁ e₂ he₁ he₂
      V hV₁ hV₂ pulled factor hD hdet)
  simpa only [map_smul, chartResidueSheafSection, chartResidueSection_common] using h

#print axioms residueSection_transition
#print axioms residueSheafSection_transition

end CycleQ2CrossChartResidueSections

end
