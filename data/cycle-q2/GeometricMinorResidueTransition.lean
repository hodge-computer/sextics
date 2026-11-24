import Proposal.GeometricProjectiveResidueTransition

/-!
# Residue transition on the actual minor intersections

The ring is the localization of the actual projective X1*X2 overlap at
the product of the chosen signed minors from the two affine charts.
Both minors are proved to be units in this ring. The transition identity
is transported by Mathlib's actual map on Kähler differentials.

Thus the final identity has no hypothesis that a minor is already a unit
on the entire projective overlap. It applies on each real minor
intersection, including empty intersections, without a smoothness or
covering assumption.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2GeometricMinorResidueTransition

open CycleQ2GeometricCofactorResidue
open CycleQ2GeometricProjectiveResidueTransition

def firstMinor (r θ : ℂ) (k : Fin 3) : CoordinateOverlapRing r θ :=
  cofactor (firstGradientRows r θ 0) (firstGradientRows r θ 1) k

def secondMinor (r θ : ℂ) (l : Fin 3) : CoordinateOverlapRing r θ :=
  cofactor (secondGradientRows r θ 0) (secondGradientRows r θ 1) l

/-- The differential identity before any minor is inverted. -/
theorem differential_balance (r θ : ℂ) (k l : Fin 3) :
    firstMinor r θ k •
        KaehlerDifferential.D ℂ (CoordinateOverlapRing r θ) (secondCoordinates r θ l) =
      (-(overlapUnit r θ : CoordinateOverlapRing r θ) * secondMinor r θ l) •
        KaehlerDifferential.D ℂ (CoordinateOverlapRing r θ) (firstCoordinates r θ k) := by
  have h := congrArg (firstDifferential r θ)
    (scaled_reconstruction (firstGradientRows r θ 0) (firstGradientRows r θ 1)
      (overlapCoordinatePull r θ (coordinateVector l)) k)
  simp only [map_smul, firstDifferential_toResidue, coefficient_change_on_overlap,
    coefficient_coordinateVector, firstCoordinateDifferentials_coordinateVector] at h
  have hd := LinearMap.congr_fun (coordinateDifferentials_change r θ) (coordinateVector l)
  rw [LinearMap.comp_apply, secondCoordinateDifferentials_coordinateVector] at hd
  rw [hd] at h
  exact h

/-- The genuine intersection of the two selected Jacobian-minor opens
inside the actual homogeneous coordinate overlap. -/
abbrev MinorOverlapRing (r θ : ℂ) (k l : Fin 3) :=
  Localization.Away (firstMinor r θ k * secondMinor r θ l)

theorem firstMinor_isUnit (r θ : ℂ) (k l : Fin 3) :
    IsUnit (algebraMap (CoordinateOverlapRing r θ) (MinorOverlapRing r θ k l)
      (firstMinor r θ k)) := by
  apply isUnit_of_dvd_unit (map_dvd
    (algebraMap (CoordinateOverlapRing r θ) (MinorOverlapRing r θ k l))
    ⟨secondMinor r θ l, rfl⟩)
  exact IsLocalization.Away.algebraMap_isUnit (firstMinor r θ k * secondMinor r θ l)

theorem secondMinor_isUnit (r θ : ℂ) (k l : Fin 3) :
    IsUnit (algebraMap (CoordinateOverlapRing r θ) (MinorOverlapRing r θ k l)
      (secondMinor r θ l)) := by
  apply isUnit_of_dvd_unit (map_dvd
    (algebraMap (CoordinateOverlapRing r θ) (MinorOverlapRing r θ k l))
    ⟨firstMinor r θ k, mul_comm _ _⟩)
  exact IsLocalization.Away.algebraMap_isUnit (firstMinor r θ k * secondMinor r θ l)

def firstMinorUnit (r θ : ℂ) (k l : Fin 3) : (MinorOverlapRing r θ k l)ˣ :=
  (firstMinor_isUnit r θ k l).unit

def secondMinorUnit (r θ : ℂ) (k l : Fin 3) : (MinorOverlapRing r θ k l)ˣ :=
  (secondMinor_isUnit r θ k l).unit

@[simp] theorem firstMinorUnit_val (r θ : ℂ) (k l : Fin 3) :
    (firstMinorUnit r θ k l : MinorOverlapRing r θ k l) =
      algebraMap (CoordinateOverlapRing r θ) (MinorOverlapRing r θ k l)
        (firstMinor r θ k) :=
  (firstMinor_isUnit r θ k l).unit_spec

@[simp] theorem secondMinorUnit_val (r θ : ℂ) (k l : Fin 3) :
    (secondMinorUnit r θ k l : MinorOverlapRing r θ k l) =
      algebraMap (CoordinateOverlapRing r θ) (MinorOverlapRing r θ k l)
        (secondMinor r θ l) :=
  (secondMinor_isUnit r θ k l).unit_spec

def firstLocalizedCoordinates (r θ : ℂ) (k l j : Fin 3) : MinorOverlapRing r θ k l :=
  algebraMap (CoordinateOverlapRing r θ) (MinorOverlapRing r θ k l) (firstCoordinates r θ j)

def secondLocalizedCoordinates (r θ : ℂ) (k l j : Fin 3) : MinorOverlapRing r θ k l :=
  algebraMap (CoordinateOverlapRing r θ) (MinorOverlapRing r θ k l) (secondCoordinates r θ j)

/-- Transport along the actual localization map on Kähler differentials. -/
theorem localized_differential_balance (r θ : ℂ) (k l : Fin 3) :
    (firstMinorUnit r θ k l : MinorOverlapRing r θ k l) •
        KaehlerDifferential.D ℂ _ (secondLocalizedCoordinates r θ k l l) =
      (-(algebraMap (CoordinateOverlapRing r θ) (MinorOverlapRing r θ k l))
          (overlapUnit r θ : CoordinateOverlapRing r θ) *
        (secondMinorUnit r θ k l : MinorOverlapRing r θ k l)) •
          KaehlerDifferential.D ℂ _ (firstLocalizedCoordinates r θ k l k) := by
  have h := congrArg
    (KaehlerDifferential.map ℂ ℂ (CoordinateOverlapRing r θ) (MinorOverlapRing r θ k l))
    (differential_balance r θ k l)
  simp only [map_smul, KaehlerDifferential.map_D] at h
  simpa only [firstMinorUnit_val, secondMinorUnit_val, firstLocalizedCoordinates,
    secondLocalizedCoordinates, ← map_neg, ← map_mul, algebraMap_smul] using h

/-- The first chart has the negative projective deletion orientation. -/
def firstOrientedResidue (r θ : ℂ) (k l : Fin 3) :
    KaehlerDifferential ℂ (MinorOverlapRing r θ k l) :=
  -((↑((firstMinorUnit r θ k l)⁻¹) : MinorOverlapRing r θ k l) •
    KaehlerDifferential.D ℂ _ (firstLocalizedCoordinates r θ k l k))

/-- The second chart has the positive projective deletion orientation. -/
def secondOrientedResidue (r θ : ℂ) (k l : Fin 3) :
    KaehlerDifferential ℂ (MinorOverlapRing r θ k l) :=
  (↑((secondMinorUnit r θ k l)⁻¹) : MinorOverlapRing r θ k l) •
    KaehlerDifferential.D ℂ _ (secondLocalizedCoordinates r θ k l l)

/-- The actual oriented differential transition on every minor intersection.
Both inverses are constructed from the localization; there are no unit,
smoothness, exactness, or supplied comparison hypotheses. -/
theorem oriented_residue_transition (r θ : ℂ) (k l : Fin 3) :
    secondOrientedResidue r θ k l =
      algebraMap (CoordinateOverlapRing r θ) (MinorOverlapRing r θ k l)
          (overlapUnit r θ : CoordinateOverlapRing r θ) •
        firstOrientedResidue r θ k l := by
  let u := firstMinorUnit r θ k l
  let v := secondMinorUnit r θ k l
  let b : MinorOverlapRing r θ k l :=
    algebraMap (CoordinateOverlapRing r θ) (MinorOverlapRing r θ k l)
      (overlapUnit r θ : CoordinateOverlapRing r θ)
  have h := localized_differential_balance r θ k l
  change (u : MinorOverlapRing r θ k l) •
      KaehlerDifferential.D ℂ _ (secondLocalizedCoordinates r θ k l l) =
    (-b * (v : MinorOverlapRing r θ k l)) •
      KaehlerDifferential.D ℂ _ (firstLocalizedCoordinates r θ k l k) at h
  have hscaled := congrArg
    (fun z : KaehlerDifferential ℂ (MinorOverlapRing r θ k l) =>
      ((↑(v⁻¹) : MinorOverlapRing r θ k l) *
        (↑(u⁻¹) : MinorOverlapRing r θ k l)) • z) h
  have hleft :
      ((↑(v⁻¹) : MinorOverlapRing r θ k l) *
        (↑(u⁻¹) : MinorOverlapRing r θ k l)) * (u : MinorOverlapRing r θ k l) =
      (↑(v⁻¹) : MinorOverlapRing r θ k l) := by
    rw [mul_assoc, u.inv_mul, mul_one]
  have hright :
      ((↑(v⁻¹) : MinorOverlapRing r θ k l) *
        (↑(u⁻¹) : MinorOverlapRing r θ k l)) * (-b * (v : MinorOverlapRing r θ k l)) =
      b * -(↑(u⁻¹) : MinorOverlapRing r θ k l) := by
    calc
      _ = ((↑(v⁻¹) : MinorOverlapRing r θ k l) * (v : MinorOverlapRing r θ k l)) *
          (b * -(↑(u⁻¹) : MinorOverlapRing r θ k l)) := by ring
      _ = _ := by rw [v.inv_mul, one_mul]
  change (↑(v⁻¹) : MinorOverlapRing r θ k l) •
      KaehlerDifferential.D ℂ _ (secondLocalizedCoordinates r θ k l l) =
    b • (-((↑(u⁻¹) : MinorOverlapRing r θ k l) •
      KaehlerDifferential.D ℂ _ (firstLocalizedCoordinates r θ k l k)))
  simp only [smul_smul, hleft, hright] at hscaled
  simpa only [smul_smul, mul_neg, neg_smul, smul_neg] using hscaled

end CycleQ2GeometricMinorResidueTransition

end
