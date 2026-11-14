import Proposal.GeometricAffineChartSections
import Proposal.GeometricProjectiveAffineCoefficients

/-!
# The literal coordinate sections of the actual projective affine charts

The coordinate maps obtained by transporting the actual structure sheaf
through the affine chart schemes agree with the existing literal quotient
coordinate maps. These identities bind the affine differential frames to
the explicit projective residue forms.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricProjectiveChartSections

open CategoryTheory AlgebraicGeometry CycleQ2GeometricProjectiveCurve
  CycleQ2GeometricProjectiveAffine CycleQ2GeometricProjectiveAffineCoefficients
  CycleQ2GeometricAffineChartSections

private theorem basicOpen_sectionMap (r θ : ℂ) (j : Fin 4)
    {B : Type} [CommRing B] (q : ProjectiveCoordinateRing r θ j ≃+* B) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
        (Proj.basicOpenToSpec (curveGrade r θ) (coordinateDen r θ j) ≫
          Spec.map (CommRingCat.ofHom q.symm.toRingHom)).appTop ≫
        (Proj.basicOpen (curveGrade r θ) (coordinateDen r θ j)).topIso.hom =
      CommRingCat.ofHom q.symm.toRingHom ≫
        (Proj.basicOpenIsoAway (curveGrade r θ) (coordinateDen r θ j)
          (coordinate_mem_grade r θ j) (by decide)).hom := by
  rw [Scheme.Hom.comp_appTop, Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality_assoc]
  dsimp only [Scheme.Hom.appTop]
  rw [Proj.basicOpenToSpec_app_top]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id,
    Proj.basicOpenIsoAway_hom]

/-- The first actual affine chart coordinate map is exactly the inverse of
the literal first coordinate-section equivalence. -/
theorem first_chartSection_top (r θ : ℂ) :
    chartSection (firstCoordinateChartIso r θ)
        (Over.mk (𝟙 (coordinateProjectivePatch r θ 1))) =
      (firstCoordinateSectionsEquiv r θ).symm.toRingHom := by
  have hcat : CommRingCat.ofHom (chartSection (firstCoordinateChartIso r θ)
        (Over.mk (𝟙 (coordinateProjectivePatch r θ 1)))) =
      CommRingCat.ofHom (firstCoordinateSectionsEquiv r θ).symm.toRingHom := by
    rw [chartSection_top]
    exact basicOpen_sectionMap r θ 1 (firstCoordinateEquiv r θ).toRingEquiv
  exact congrArg CommRingCat.Hom.hom hcat

/-- The second actual affine chart coordinate map is exactly the inverse
of the literal second coordinate-section equivalence. -/
theorem second_chartSection_top (r θ : ℂ) :
    chartSection (secondCoordinateChartIso r θ)
        (Over.mk (𝟙 (coordinateProjectivePatch r θ 2))) =
      (secondCoordinateSectionsEquiv r θ).symm.toRingHom := by
  have hcat : CommRingCat.ofHom (chartSection (secondCoordinateChartIso r θ)
        (Over.mk (𝟙 (coordinateProjectivePatch r θ 2)))) =
      CommRingCat.ofHom (secondCoordinateSectionsEquiv r θ).symm.toRingHom := by
    rw [chartSection_top]
    exact basicOpen_sectionMap r θ 2 (secondCoordinateEquiv r θ).toRingEquiv
  exact congrArg CommRingCat.Hom.hom hcat

end CycleQ2GeometricProjectiveChartSections

end
