import Proposal.GeometricSeedImageLocalization
import Proposal.GeometricSeedProjectiveImageCocycle

/-!
# The seed linkage comparison on actual projective intersections

The pair ring is the existing homogeneous degree-zero ring of the actual
projective intersection. The established coordinate restriction theorem
identifies it as a localization of either homogeneous affine chart.
Transporting the proved chart linkage regularity through this localization
and the actual section isomorphism supplies factor data on the intersection.

The resulting image-dual comparisons commute with each original chart
map on original image and ideal elements. No regularity premise is supplied
by a caller. Comparing the two intersection isomorphisms with the degree-four
twist, and identifying their module models with the restricted dual sheaves,
are separate steps.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the remaining certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedProjectiveImageRestriction

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open CycleQ2SeedTrace CycleQ2CartierSurfaceGrading CycleQ2CartierProjectiveCover
  CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2GeometricSurfaceOverlap
  CycleQ2SurfaceCoordinateSections CycleQ2SeedProjectiveImageChart
  CycleQ2SeedProjectiveImageTwist CycleQ2SeedProjectiveImageCocycle
  CycleQ2SeedImageLocalization CycleQ2SegreFactorSequence
  CycleQ2GeometricSeedNormalIdeals

abbrev OverlapRing (i j : Fin 3) := PairRing 57 1 i.succ j.succ
abbrev OverlapOpen (i j : Fin 3) := pairOpen 57 1 i.succ j.succ

def sectionsEquiv (i j : Fin 3) : OverlapRing i j ≃+* Γ(Surface, OverlapOpen i j) :=
  (pairSectionsIso 57 1 i.succ j.succ).commRingCatIsoToRingEquiv

def coefficient (i j : Fin 3) (x : SurfaceRing 57 1)
    (hx : x = coordinateDen 57 1 i.succ * coordinateDen 57 1 j.succ) :
    AffineRing i →+* HomogeneousLocalization.Away (surfaceGrade 57 1) x :=
  (coordinateRestriction 57 1 i.succ j.succ x hx).comp
    (coordinateChartEquiv 57 1 i.succ).symm.toRingHom

/-- This is regularity on the actual projective overlap, obtained from
the original chart regularity and the proved localization description. -/
theorem coefficient_linkage_regular (i j : Fin 3) (x : SurfaceRing 57 1)
    (hx : x = coordinateDen 57 1 i.succ * coordinateDen 57 1 j.succ) :
    Function.Injective (fun z : HomogeneousLocalization.Away (surfaceGrade 57 1) x =>
      coefficient i j x hx (chartFactorData i).linkage * z) := by
  letI := (coordinateRestriction 57 1 i.succ j.succ x hx).toAlgebra
  letI := coordinateRestriction_isLocalization 57 1 i.succ j.succ x hx
  have hreg : Function.Injective (fun z : CoordinateRing 57 1 i.succ =>
      (coordinateChartEquiv 57 1 i.succ).symm (chartFactorData i).linkage * z) := by
    intro a b hab
    apply (coordinateChartEquiv 57 1 i.succ).injective
    apply (chartFactorData i).regular
    have h := congrArg (coordinateChartEquiv 57 1 i.succ) hab
    simpa only [map_mul, RingEquiv.apply_symm_apply] using h
  exact localization_regular
    (Submonoid.powers (coordinateRatio 57 1 i.succ j.succ.castSucc))
    (HomogeneousLocalization.Away (surfaceGrade 57 1) x)
    ((coordinateChartEquiv 57 1 i.succ).symm (chartFactorData i).linkage) hreg

def leftCoefficient (i j : Fin 3) : AffineRing i →+* OverlapRing i j :=
  coefficient i j (pairDen 57 1 i.succ j.succ) rfl

def rightCoefficient (i j : Fin 3) : AffineRing j →+* OverlapRing i j :=
  coefficient j i (pairDen 57 1 i.succ j.succ) (mul_comm _ _)

theorem pairSection_top (i j : Fin 3) (a : OverlapRing i j) :
    pairSection 57 1 i.succ j.succ (OverlapOpen i j) le_rfl a = sectionsEquiv i j a := by
  change (Surface.presheaf.map (𝟙 (op (OverlapOpen i j))))
      ((pairSectionsIso 57 1 i.succ j.succ).hom a) = _
  simp only [CategoryTheory.Functor.map_id]
  rfl

/-- The left coefficient map is the actual structure-sheaf restriction. -/
theorem leftCoefficient_toSections (i j : Fin 3) (a : AffineRing i) :
    sectionsEquiv i j (leftCoefficient i j a) =
      chartSectionMap i (OverlapOpen i j) (pair_le_left 57 1 i.succ j.succ) a := by
  have h := pairSection_left 57 1 i.succ j.succ (OverlapOpen i j) le_rfl
    ((coordinateChartEquiv 57 1 i.succ).symm a)
  rw [pairSection_top] at h
  change sectionsEquiv i j (leftCoefficient i j a) =
    CycleQ2GeometricAffineChartSections.chartSection (coordinateAffineChart 57 1 i.succ)
      (Over.mk (homOfLE (pair_le_left 57 1 i.succ j.succ))) a
  rw [CycleQ2SurfaceCoordinateSections.coordinate_chartSection_subopen]
  exact h

/-- The right coefficient map is the actual structure-sheaf restriction. -/
theorem rightCoefficient_toSections (i j : Fin 3) (a : AffineRing j) :
    sectionsEquiv i j (rightCoefficient i j a) =
      chartSectionMap j (OverlapOpen i j) (pair_le_right 57 1 i.succ j.succ) a := by
  have h := pairSection_right 57 1 i.succ j.succ (OverlapOpen i j) le_rfl
    ((coordinateChartEquiv 57 1 j.succ).symm a)
  rw [pairSection_top] at h
  change sectionsEquiv i j (rightCoefficient i j a) =
    CycleQ2GeometricAffineChartSections.chartSection (coordinateAffineChart 57 1 j.succ)
      (Over.mk (homOfLE (pair_le_right 57 1 i.succ j.succ))) a
  rw [CycleQ2SurfaceCoordinateSections.coordinate_chartSection_subopen]
  exact h

theorem leftSection_linkage_regular (i j : Fin 3) :
    Function.Injective (fun z : Γ(Surface, OverlapOpen i j) =>
      chartSectionMap i (OverlapOpen i j) (pair_le_left 57 1 i.succ j.succ)
        (chartFactorData i).linkage * z) := by
  intro a b hab
  apply (sectionsEquiv i j).symm.injective
  apply coefficient_linkage_regular i j (pairDen 57 1 i.succ j.succ) rfl
  simp only [← leftCoefficient_toSections] at hab
  have h := congrArg (sectionsEquiv i j).symm hab
  simp only [map_mul, RingEquiv.symm_apply_apply] at h
  exact h

theorem rightSection_linkage_regular (i j : Fin 3) :
    Function.Injective (fun z : Γ(Surface, OverlapOpen i j) =>
      chartSectionMap j (OverlapOpen i j) (pair_le_right 57 1 i.succ j.succ)
        (chartFactorData j).linkage * z) := by
  intro a b hab
  apply (sectionsEquiv i j).symm.injective
  apply coefficient_linkage_regular j i (pairDen 57 1 i.succ j.succ) (mul_comm _ _)
  simp only [← rightCoefficient_toSections] at hab
  have h := congrArg (sectionsEquiv i j).symm hab
  simp only [map_mul, RingEquiv.symm_apply_apply] at h
  exact h

def leftData (i j : Fin 3) : FactorData Γ(Surface, OverlapOpen i j) :=
  mapFactorData (chartFactorData i)
    (chartSectionMap i (OverlapOpen i j) (pair_le_left 57 1 i.succ j.succ))
    (leftSection_linkage_regular i j)

def rightData (i j : Fin 3) : FactorData Γ(Surface, OverlapOpen i j) :=
  mapFactorData (chartFactorData j)
    (chartSectionMap j (OverlapOpen i j) (pair_le_right 57 1 i.succ j.succ))
    (rightSection_linkage_regular i j)

theorem leftData_matrix (i j : Fin 3) :
    (leftData i j).matrix =
      sectionMatrix i (OverlapOpen i j) (pair_le_left 57 1 i.succ j.succ) := rfl

theorem rightData_matrix (i j : Fin 3) :
    (rightData i j).matrix =
      sectionMatrix j (OverlapOpen i j) (pair_le_right 57 1 i.succ j.succ) := rfl

theorem leftData_left (i j : Fin 3) :
    (leftData i j).left =
      sectionLeft i (OverlapOpen i j) (pair_le_left 57 1 i.succ j.succ) := rfl

theorem rightData_left (i j : Fin 3) :
    (rightData i j).left =
      sectionLeft j (OverlapOpen i j) (pair_le_right 57 1 i.succ j.succ) := rfl

def leftImageRestriction (i j : Fin 3) :
    ImageModule i →ₛₗ[chartSectionMap i (OverlapOpen i j)
      (pair_le_left 57 1 i.succ j.succ)] Regrading.Image (leftData i j) :=
  imageBaseChange (chartFactorData i) _ (leftSection_linkage_regular i j)

def rightImageRestriction (i j : Fin 3) :
    ImageModule j →ₛₗ[chartSectionMap j (OverlapOpen i j)
      (pair_le_right 57 1 i.succ j.succ)] Regrading.Image (rightData i j) :=
  imageBaseChange (chartFactorData j) _ (rightSection_linkage_regular i j)

theorem left_imageDual_restriction (i j : Fin 3) (z : ImageModule i) (x : OrbitIdeal i) :
    Regrading.imageDual (leftData i j) (leftImageRestriction i j z)
        (mappedLeft (chartFactorData i) _ (leftSection_linkage_regular i j) x) =
      chartSectionMap i (OverlapOpen i j) (pair_le_left 57 1 i.succ j.succ)
        (imageDualEquiv i z x) :=
  imageDual_baseChange (chartFactorData i) _ (leftSection_linkage_regular i j) z x

theorem right_imageDual_restriction (i j : Fin 3) (z : ImageModule j) (x : OrbitIdeal j) :
    Regrading.imageDual (rightData i j) (rightImageRestriction i j z)
        (mappedLeft (chartFactorData j) _ (rightSection_linkage_regular i j) x) =
      chartSectionMap j (OverlapOpen i j) (pair_le_right 57 1 i.succ j.succ)
        (imageDualEquiv j z x) :=
  imageDual_baseChange (chartFactorData j) _ (rightSection_linkage_regular i j) z x

#print axioms coefficient_linkage_regular
#print axioms leftCoefficient_toSections
#print axioms rightCoefficient_toSections
#print axioms leftSection_linkage_regular
#print axioms rightSection_linkage_regular
#print axioms left_imageDual_restriction
#print axioms right_imageDual_restriction

end CycleQ2SeedProjectiveImageRestriction
end
