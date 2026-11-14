import Proposal.GeometricCoordinateH2
import Proposal.GeometricSurfaceCoordinateSections

/-!
# Actual projective sections in the original coordinate localizations

These maps retain the original homogeneous localization, its actual
structure-sheaf section isomorphism, and its canonical injection into the
ordinary localization. No Laurent range or extension hypothesis is used.
Their naturality and homogeneous numerator identity are sufficient to map
canonical two-form boundaries to the original coordinate Čech boundaries.

Status: source-only proof draft. Verification is deferred at the user's request.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SurfaceSectionCoefficients

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open CycleQ2SeedTrace CycleQ2GeometricSeedNormalIdeals
open CycleQ2GeometricSurfaceCoordinates CycleQ2CartierSurfaceGrading CycleQ2CartierProjectiveCover
open CycleQ2ProjectiveCoordinateCohomology CycleQ2ProjectiveCoordinateH2
open CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2SurfaceCoordinateSections

/-- The literal section isomorphism followed by the canonical homogeneous
localization inclusion. -/
def sectionCoefficient (r θ : ℂ) (s : Finset (Fin 3)) (hs : s.Nonempty) :
    Γ(projectiveSurface r θ, coordinateIntersection r θ s) →+* CoordinateLocal r θ s :=
  (algebraMap (HomogeneousCoordinateLocal r θ s) (CoordinateLocal r θ s)).comp
    (coordinateSections r θ s hs).symm.toRingHom

@[simp] theorem sectionCoefficient_sections (r θ : ℂ) (s : Finset (Fin 3))
    (hs : s.Nonempty) (q : HomogeneousCoordinateLocal r θ s) :
    sectionCoefficient r θ s hs (coordinateSections r θ s hs q) = q.val := by
  change ((coordinateSections r θ s hs).symm (coordinateSections r θ s hs q)).val = _
  rw [RingEquiv.symm_apply_apply]

/-- Both maps are the original restrictions, not a newly chosen transport. -/
theorem sectionCoefficient_restrict (r θ : ℂ) {s t : Finset (Fin 3)}
    (hs : s.Nonempty) (ht : t.Nonempty) (hst : s ⊆ t)
    (a : Γ(projectiveSurface r θ, coordinateIntersection r θ s)) :
    sectionCoefficient r θ t ht
        ((projectiveSurface r θ).presheaf.map
          (homOfLE (coordinateIntersection_mono r θ hst)).op a) =
      CycleQ2GeometricSurfaceCoordinates.coordinateRestriction r θ hst
        (sectionCoefficient r θ s hs a) := by
  obtain ⟨q,rfl⟩ := (coordinateSections r θ s hs).surjective a
  rw [coordinateSections_restrict, sectionCoefficient_sections,
    sectionCoefficient_sections, coordinateHomogeneousRestriction_val]

/-- The same map on an identified open, for the original pair/triple
Mayer--Vietoris conventions. -/
def sectionCoefficientAt (r θ : ℂ) (s : Finset (Fin 3)) (hs : s.Nonempty)
    (O : (projectiveSurface r θ).Opens) (hO : O = coordinateIntersection r θ s) :
    Γ(projectiveSurface r θ,O) →+* CoordinateLocal r θ s :=
  (algebraMap (HomogeneousCoordinateLocal r θ s) (CoordinateLocal r θ s)).comp
    (sectionsAt r θ s hs O hO).symm.toRingHom

@[simp] theorem sectionCoefficientAt_sectionsAt (r θ : ℂ) (s : Finset (Fin 3))
    (hs : s.Nonempty) (O : (projectiveSurface r θ).Opens)
    (hO : O = coordinateIntersection r θ s) (q : HomogeneousCoordinateLocal r θ s) :
    sectionCoefficientAt r θ s hs O hO (sectionsAt r θ s hs O hO q) = q.val := by
  change ((sectionsAt r θ s hs O hO).symm (sectionsAt r θ s hs O hO q)).val = _
  rw [RingEquiv.symm_apply_apply]

theorem sectionCoefficientAt_restrict (r θ : ℂ) {s t : Finset (Fin 3)}
    (hs : s.Nonempty) (ht : t.Nonempty) (hst : s ⊆ t)
    (O P : (projectiveSurface r θ).Opens)
    (hO : O = coordinateIntersection r θ s) (hP : P = coordinateIntersection r θ t)
    (hPO : P ≤ O) (a : Γ(projectiveSurface r θ,O)) :
    sectionCoefficientAt r θ t ht P hP
        ((projectiveSurface r θ).presheaf.map (homOfLE hPO).op a) =
      CycleQ2GeometricSurfaceCoordinates.coordinateRestriction r θ hst
        (sectionCoefficientAt r θ s hs O hO a) := by
  obtain ⟨q,rfl⟩ := (sectionsAt r θ s hs O hO).surjective a
  rw [sectionsAt_restrict r θ hs ht hst O P hO hP hPO,
    sectionCoefficientAt_sectionsAt, sectionCoefficientAt_sectionsAt,
    coordinateHomogeneousRestriction_val]

def chartIndex (i : Fin 3) : Fin 4 := i.succ

theorem coordinateElement_eq (r θ : ℂ) (i : Fin 3) :
    coordinateElement r θ i =
      surfaceQuotient r θ (X (chartIndex i).castSucc) := by
  fin_cases i <;> rfl

theorem coordinateOpen_eq (r θ : ℂ) (i : Fin 3) :
    CycleQ2ProjectiveCoordinateCohomology.coordinateOpen r θ i =
      coordinatePatch r θ (chartIndex i).castSucc := by
  rw [CycleQ2ProjectiveCoordinateCohomology.coordinateOpen, coordinateElement_eq]
  rfl

theorem coordinateProduct_factor_at (r θ : ℂ) {s : Finset (Fin 3)}
    (i : Fin 3) (hi : i ∈ s) :
    coordinateProduct r θ s =
      surfaceQuotient r θ (X (chartIndex i).castSucc) * coordinateProduct r θ (s.erase i) := by
  rw [← coordinateElement_eq]
  exact (Finset.mul_prod_erase s (coordinateElement r θ) hi).symm

/-- Every coordinate intersection lies in every one of its coordinate
charts, with the actual factorization of the original denominator. -/
theorem intersection_le_chart (r θ : ℂ) {s : Finset (Fin 3)}
    (i : Fin 3) (hi : i ∈ s) :
    coordinateIntersection r θ s ≤ coordinatePatch r θ (chartIndex i).castSucc :=
  Proj.basicOpen_mono (surfaceGrade r θ)
    (surfaceQuotient r θ (X (chartIndex i).castSucc)) (coordinateProduct r θ s)
    ⟨coordinateProduct r θ (s.erase i), coordinateProduct_factor_at r θ i hi⟩

/-- The actual homogeneous restriction from Xi to the intersection. -/
def chartHomogeneousRestriction (r θ : ℂ) {s : Finset (Fin 3)}
    (i : Fin 3) (hi : i ∈ s) :
    CoordinateRing r θ (chartIndex i) →+* HomogeneousCoordinateLocal r θ s :=
  HomogeneousLocalization.awayMap (surfaceGrade r θ)
    (coordinateProduct_mem_grade r θ (s.erase i)) (coordinateProduct_factor_at r θ i hi)

def chartOrdinaryRestriction (r θ : ℂ) {s : Finset (Fin 3)}
    (i : Fin 3) (hi : i ∈ s) :
    CoordinateLocalization r θ (chartIndex i) →+* CoordinateLocal r θ s :=
  Localization.awayLift (algebraMap (SurfaceRing r θ) (CoordinateLocal r θ s))
    (surfaceQuotient r θ (X (chartIndex i).castSucc))
    (isUnit_of_dvd_unit (map_dvd _ ⟨_, coordinateProduct_factor_at r θ i hi⟩)
      (IsLocalization.Away.algebraMap_isUnit (coordinateProduct r θ s)))

@[simp] theorem chartOrdinaryRestriction_base (r θ : ℂ) {s : Finset (Fin 3)}
    (i : Fin 3) (hi : i ∈ s) (a : SurfaceRing r θ) :
    chartOrdinaryRestriction r θ i hi
        (algebraMap (SurfaceRing r θ) (CoordinateLocalization r θ (chartIndex i)) a) =
      algebraMap (SurfaceRing r θ) (CoordinateLocal r θ s) a :=
  IsLocalization.Away.lift_eq _ _ a

theorem chartHomogeneousRestriction_val (r θ : ℂ) {s : Finset (Fin 3)}
    (i : Fin 3) (hi : i ∈ s) (q : CoordinateRing r θ (chartIndex i)) :
    (chartHomogeneousRestriction r θ i hi q).val = chartOrdinaryRestriction r θ i hi q.val :=
  HomogeneousLocalization.val_awayMap _ _ _ _

/-- The restriction from the homogeneous ring is the actual sheaf
restriction on every coordinate intersection. -/
theorem chartHomogeneousRestriction_sections (r θ : ℂ) {s : Finset (Fin 3)}
    (hs : s.Nonempty) (i : Fin 3) (hi : i ∈ s)
    (q : CoordinateRing r θ (chartIndex i)) :
    coordinateSections r θ s hs (chartHomogeneousRestriction r θ i hi q) =
      (projectiveSurface r θ).presheaf.map (homOfLE (intersection_le_chart r θ i hi)).op
        ((Proj.basicOpenIsoAway (surfaceGrade r θ)
          (surfaceQuotient r θ (X (chartIndex i).castSucc))
          (coordinate_mem_grade r θ (chartIndex i)) (by decide)).hom q) := by
  have h := congrArg (fun f => f q)
    (Proj.awayMap_awayToSection (surfaceGrade r θ)
      (coordinateProduct_mem_grade r θ (s.erase i))
      (coordinateProduct_factor_at r θ i hi))
  exact h

theorem sectionCoefficient_coordinatePolynomial (r θ : ℂ) {s : Finset (Fin 3)}
    (hs : s.Nonempty) (i : Fin 3) (hi : i ∈ s) (n : ℕ)
    (p : WeightedPoly) (hp : p.IsWeightedHomogeneous weight n) :
    sectionCoefficient r θ s hs
        (coordinatePolynomialSection r θ (chartIndex i) (coordinateIntersection r θ s)
          (intersection_le_chart r θ i hi) p) =
      (chartHomogeneousRestriction r θ i hi
        (homogeneousFraction r θ (chartIndex i) n p hp)).val := by
  rw [coordinatePolynomialSection_fraction r θ (chartIndex i)
    (coordinateIntersection r θ s) (intersection_le_chart r θ i hi) n p hp,
    ← chartHomogeneousRestriction_sections r θ hs i hi,
    sectionCoefficient_sections]

/-- Clearing the actual Xi denominator gives the original polynomial in
the original cone coordinate localization. The numerator is not changed. -/
theorem sectionCoefficient_homogeneous (r θ : ℂ) {s : Finset (Fin 3)}
    (hs : s.Nonempty) (i : Fin 3) (hi : i ∈ s) (n : ℕ)
    (p : WeightedPoly) (hp : p.IsWeightedHomogeneous weight n) :
    sectionCoefficient r θ s hs
        (coordinatePolynomialSection r θ (chartIndex i) (coordinateIntersection r θ s)
          (intersection_le_chart r θ i hi) p) *
      algebraMap (SurfaceRing r θ) (CoordinateLocal r θ s) ((coordinateElement r θ i)^n) =
      algebraMap (SurfaceRing r θ) (CoordinateLocal r θ s) (surfaceQuotient r θ p) := by
  rw [sectionCoefficient_coordinatePolynomial r θ hs i hi n p hp,
    chartHomogeneousRestriction_val]
  have hfrac : (homogeneousFraction r θ (chartIndex i) n p hp).val *
      algebraMap (SurfaceRing r θ) (CoordinateLocalization r θ (chartIndex i))
        ((surfaceQuotient r θ (X (chartIndex i).castSucc))^n) =
      algebraMap (SurfaceRing r θ) (CoordinateLocalization r θ (chartIndex i))
        (surfaceQuotient r θ p) := by
    rw [homogeneousFraction, HomogeneousLocalization.Away.val_mk,
      Localization.mk_eq_mk']
    exact IsLocalization.mk'_spec _ _ _
  have h := congrArg (chartOrdinaryRestriction r θ i hi) hfrac
  rw [map_mul, chartOrdinaryRestriction_base, chartOrdinaryRestriction_base] at h
  simpa only [coordinateElement_eq] using h

/-- The denominator stays a unit on this actual cone localization. -/
theorem coordinateElement_isUnit (r θ : ℂ) {s : Finset (Fin 3)}
    (i : Fin 3) (hi : i ∈ s) :
    IsUnit (algebraMap (SurfaceRing r θ) (CoordinateLocal r θ s) (coordinateElement r θ i)) := by
  rw [coordinateElement_eq]
  exact isUnit_of_dvd_unit (map_dvd _ ⟨_, coordinateProduct_factor_at r θ i hi⟩)
    (IsLocalization.Away.algebraMap_isUnit (coordinateProduct r θ s))

#print axioms sectionCoefficient_restrict
#print axioms sectionCoefficientAt_restrict
#print axioms sectionCoefficient_homogeneous

end CycleQ2SurfaceSectionCoefficients

end
