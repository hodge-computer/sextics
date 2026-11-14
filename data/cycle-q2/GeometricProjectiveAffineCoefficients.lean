import Proposal.GeometricProjectiveAffine
import Proposal.GeometricProjectiveCoefficients

/-!
# Complex coefficients in the actual affine polynomial charts

The proved coordinate presentations respect the global complex coefficients
used to define the differential sheaf. Both the section-ring formulas and
the structure morphisms of the actual chart schemes are identified.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricProjectiveAffineCoefficients

open CategoryTheory AlgebraicGeometry CycleQ2GeometricProjectiveCurve
  CycleQ2GeometricProjectiveAffine CycleQ2GeometricProjectiveCoefficients
  CycleQ2GeometricDifferentialSheaf

def coordinateSectionsEquiv (r θ : ℂ) (j : Fin 4) :
    Γ(projectiveCurve r θ, coordinateProjectivePatch r θ j) ≃+*
      AffineCoordinateRing r θ j :=
  (Proj.basicOpenIsoAway (curveGrade r θ) (coordinateDen r θ j)
    (coordinate_mem_grade r θ j) (by decide)).symm.commRingCatIsoToRingEquiv.trans
      (coordinateEquiv r θ j).toRingEquiv

def firstCoordinateSectionsEquiv (r θ : ℂ) :
    Γ(projectiveCurve r θ, coordinateProjectivePatch r θ 1) ≃+* FirstChartRing r θ :=
  (Proj.basicOpenIsoAway (curveGrade r θ) (coordinateDen r θ 1)
    (coordinate_mem_grade r θ 1) (by decide)).symm.commRingCatIsoToRingEquiv.trans
      (firstCoordinateEquiv r θ).toRingEquiv

def secondCoordinateSectionsEquiv (r θ : ℂ) :
    Γ(projectiveCurve r θ, coordinateProjectivePatch r θ 2) ≃+* SecondChartRing r θ :=
  (Proj.basicOpenIsoAway (curveGrade r θ) (coordinateDen r θ 2)
    (coordinate_mem_grade r θ 2) (by decide)).symm.commRingCatIsoToRingEquiv.trans
      (secondCoordinateEquiv r θ).toRingEquiv

theorem coordinateSectionsEquiv_coefficient (r θ : ℂ) (j : Fin 4) (c : ℂ) :
    coordinateSectionsEquiv r θ j
        (coefficientOn (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
          (coordinateProjectivePatch r θ j) c) =
      algebraMap ℂ (AffineCoordinateRing r θ j) c := by
  change coordinateEquiv r θ j
    ((Proj.basicOpenIsoAway (curveGrade r θ) (coordinateDen r θ j)
      (coordinate_mem_grade r θ j) (by decide)).inv _) = _
  rw [coefficientOn_coordinatePatch]
  exact (coordinateEquiv r θ j).commutes c

theorem firstCoordinateSectionsEquiv_coefficient (r θ : ℂ) (c : ℂ) :
    firstCoordinateSectionsEquiv r θ
        (coefficientOn (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
          (coordinateProjectivePatch r θ 1) c) =
      algebraMap ℂ (FirstChartRing r θ) c := by
  change firstCoordinateEquiv r θ
    ((Proj.basicOpenIsoAway (curveGrade r θ) (coordinateDen r θ 1)
      (coordinate_mem_grade r θ 1) (by decide)).inv _) = _
  rw [coefficientOn_coordinatePatch]
  exact (firstCoordinateEquiv r θ).commutes c

theorem secondCoordinateSectionsEquiv_coefficient (r θ : ℂ) (c : ℂ) :
    secondCoordinateSectionsEquiv r θ
        (coefficientOn (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
          (coordinateProjectivePatch r θ 2) c) =
      algebraMap ℂ (SecondChartRing r θ) c := by
  change secondCoordinateEquiv r θ
    ((Proj.basicOpenIsoAway (curveGrade r θ) (coordinateDen r θ 2)
      (coordinate_mem_grade r θ 2) (by decide)).inv _) = _
  rw [coefficientOn_coordinatePatch]
  exact (secondCoordinateEquiv r θ).commutes c

/-- The actual coordinate chart is an affine chart over the complex field,
for precisely the structure map used to define projective differentials. -/
theorem coordinateChartIso_overComplex (r θ : ℂ) (j : Fin 4) :
    (coordinateChartIso r θ j).inv ≫ (coordinateProjectivePatch r θ j).ι ≫
        projectiveToComplex r θ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (AffineCoordinateRing r θ j))) := by
  change (Spec.map (CommRingCat.ofHom (coordinateEquiv r θ j).toRingHom) ≫
      (Proj.basicOpenIsoSpec (curveGrade r θ) (coordinateDen r θ j)
        (coordinate_mem_grade r θ j) (by decide)).inv) ≫
      (Proj.basicOpen (curveGrade r θ) (coordinateDen r θ j)).ι ≫
        projectiveToComplex r θ = _
  rw [Category.assoc, Proj.basicOpenIsoSpec_inv_ι_assoc,
    awayι_projectiveToComplex, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact (coordinateEquiv r θ j).commutes c

theorem firstCoordinateChartIso_overComplex (r θ : ℂ) :
    (firstCoordinateChartIso r θ).inv ≫ (coordinateProjectivePatch r θ 1).ι ≫
        projectiveToComplex r θ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (FirstChartRing r θ))) := by
  change (Spec.map (CommRingCat.ofHom (firstCoordinateEquiv r θ).toRingHom) ≫
      (Proj.basicOpenIsoSpec (curveGrade r θ) (coordinateDen r θ 1)
        (coordinate_mem_grade r θ 1) (by decide)).inv) ≫
      (Proj.basicOpen (curveGrade r θ) (coordinateDen r θ 1)).ι ≫
        projectiveToComplex r θ = _
  rw [Category.assoc, Proj.basicOpenIsoSpec_inv_ι_assoc,
    awayι_projectiveToComplex, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact (firstCoordinateEquiv r θ).commutes c

theorem secondCoordinateChartIso_overComplex (r θ : ℂ) :
    (secondCoordinateChartIso r θ).inv ≫ (coordinateProjectivePatch r θ 2).ι ≫
        projectiveToComplex r θ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (SecondChartRing r θ))) := by
  change (Spec.map (CommRingCat.ofHom (secondCoordinateEquiv r θ).toRingHom) ≫
      (Proj.basicOpenIsoSpec (curveGrade r θ) (coordinateDen r θ 2)
        (coordinate_mem_grade r θ 2) (by decide)).inv) ≫
      (Proj.basicOpen (curveGrade r θ) (coordinateDen r θ 2)).ι ≫
        projectiveToComplex r θ = _
  rw [Category.assoc, Proj.basicOpenIsoSpec_inv_ι_assoc,
    awayι_projectiveToComplex, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact (secondCoordinateEquiv r θ).commutes c

end CycleQ2GeometricProjectiveAffineCoefficients

end
