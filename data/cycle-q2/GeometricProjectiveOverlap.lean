import Proposal.GeometricProjectiveAffineCoefficients
import Proposal.GeometricAffineOverlap

/-!
# The actual projective coordinate overlap and its affine substitutions

The homogeneous localization at x1*x2 is identified with the two literal
affine quotients localized at their middle coordinates. Their comparison
is the already checked substitution used for the differential transition.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

noncomputable section

namespace CycleQ2GeometricProjectiveOverlap

open MvPolynomial CategoryTheory AlgebraicGeometry
  CycleQ2NormalConnecting CycleQ2GeometricProjectiveCurve
  CycleQ2GeometricAffineCurveCharts CycleQ2GeometricProjectiveAffine
  CycleQ2GeometricProjectiveAffineCoefficients

theorem firstCoordinateEquiv_ratio (r θ : ℂ) (k : Fin 4) :
    firstCoordinateEquiv r θ (coordinateRatio r θ 1 k) =
      firstChartMap r θ (firstDehomogenize (X k)) := by
  change Ideal.quotientEquivAlgOfEq ℂ
    (congrArg chartIdeal (coordinateEquations_one r θ)) (toChart r θ 1 _) = _
  rw [toChart_coordinateRatio]
  change Ideal.quotientEquivAlgOfEq ℂ (congrArg chartIdeal (coordinateEquations_one r θ))
    (Ideal.Quotient.mk _ (dehomogenize 1 (X k))) = _
  rw [Ideal.quotientEquivAlgOfEq_mk, dehomogenize_one]
  rfl

theorem secondCoordinateEquiv_ratio (r θ : ℂ) (k : Fin 4) :
    secondCoordinateEquiv r θ (coordinateRatio r θ 2 k) =
      secondChartMap r θ (secondDehomogenize (X k)) := by
  change Ideal.quotientEquivAlgOfEq ℂ
    (congrArg chartIdeal (coordinateEquations_two r θ)) (toChart r θ 2 _) = _
  rw [toChart_coordinateRatio]
  change Ideal.quotientEquivAlgOfEq ℂ (congrArg chartIdeal (coordinateEquations_two r θ))
    (Ideal.Quotient.mk _ (dehomogenize 2 (X k))) = _
  rw [Ideal.quotientEquivAlgOfEq_mk, dehomogenize_two]
  rfl

def coordinateRestriction (r θ : ℂ) (j k : Fin 4) (x : CurveRing r θ)
    (hx : x = coordinateDen r θ j * coordinateDen r θ k) :
    ProjectiveCoordinateRing r θ j →+* HomogeneousLocalization.Away (curveGrade r θ) x :=
  HomogeneousLocalization.awayMap (curveGrade r θ) (coordinate_mem_grade r θ k) hx

theorem coordinateLocalizationElement_eq (r θ : ℂ) (j k : Fin 4) :
    HomogeneousLocalization.Away.isLocalizationElem
      (coordinate_mem_grade r θ j) (coordinate_mem_grade r θ k) =
      coordinateRatio r θ j k := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.isLocalizationElem,
    HomogeneousLocalization.Away.val_mk, pow_one]
  rfl

theorem coordinateRestriction_isLocalization (r θ : ℂ) (j k : Fin 4)
    (x : CurveRing r θ) (hx : x = coordinateDen r θ j * coordinateDen r θ k) :
    letI := (coordinateRestriction r θ j k x hx).toAlgebra
    IsLocalization.Away (coordinateRatio r θ j k)
      (HomogeneousLocalization.Away (curveGrade r θ) x) := by
  let := (coordinateRestriction r θ j k x hx).toAlgebra
  rw [← coordinateLocalizationElement_eq]
  exact HomogeneousLocalization.Away.isLocalization_mul
    (coordinate_mem_grade r θ j) (coordinate_mem_grade r θ k) hx (by decide)

/-- Localizing the proved coordinate presentation gives the actual
homogeneous overlap presentation. -/
def localizedCoordinateRingEquiv {B : Type*} [CommRing B] [Algebra ℂ B]
    (r θ : ℂ) (j k : Fin 4) (x : CurveRing r θ)
    (hx : x = coordinateDen r θ j * coordinateDen r θ k)
    (e : ProjectiveCoordinateRing r θ j ≃ₐ[ℂ] B)
    (z : B) (he : e (coordinateRatio r θ j k) = z) :
    HomogeneousLocalization.Away (curveGrade r θ) x ≃+* Localization.Away z := by
  letI := (coordinateRestriction r θ j k x hx).toAlgebra
  letI := coordinateRestriction_isLocalization r θ j k x hx
  exact IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (coordinateRatio r θ j k)) (T := Submonoid.powers z)
    _ _ e.toRingEquiv (by
    rw [Submonoid.map_powers]
    exact congrArg Submonoid.powers he)

theorem localizedCoordinateRingEquiv_restriction {B : Type*} [CommRing B] [Algebra ℂ B]
    (r θ : ℂ) (j k : Fin 4) (x : CurveRing r θ)
    (hx : x = coordinateDen r θ j * coordinateDen r θ k)
    (e : ProjectiveCoordinateRing r θ j ≃ₐ[ℂ] B)
    (z : B) (he : e (coordinateRatio r θ j k) = z)
    (a : ProjectiveCoordinateRing r θ j) :
    localizedCoordinateRingEquiv r θ j k x hx e z he
        (coordinateRestriction r θ j k x hx a) =
      algebraMap B (Localization.Away z) (e a) := by
  let := (coordinateRestriction r θ j k x hx).toAlgebra
  let := coordinateRestriction_isLocalization r θ j k x hx
  exact IsLocalization.ringEquivOfRingEquiv_eq
    (S := HomogeneousLocalization.Away (curveGrade r θ) x)
    (Q := Localization.Away z) (M := Submonoid.powers (coordinateRatio r θ j k))
    (T := Submonoid.powers z) (j := e.toRingEquiv) (by
      rw [Submonoid.map_powers]
      exact congrArg Submonoid.powers he) a

theorem localizedCoordinateRingEquiv_constant {B : Type*} [CommRing B] [Algebra ℂ B]
    (r θ : ℂ) (j k : Fin 4) (x : CurveRing r θ)
    (hx : x = coordinateDen r θ j * coordinateDen r θ k)
    (e : ProjectiveCoordinateRing r θ j ≃ₐ[ℂ] B)
    (z : B) (he : e (coordinateRatio r θ j k) = z) (c : ℂ) :
    localizedCoordinateRingEquiv r θ j k x hx e z he
        (HomogeneousLocalization.fromZeroRingHom (curveGrade r θ) (Submonoid.powers x)
          (algebraMap ℂ (curveGrade r θ 0) c)) =
      algebraMap ℂ (Localization.Away z) c := by
  rw [← HomogeneousLocalization.awayMap_fromZeroRingHom (curveGrade r θ)
    (coordinate_mem_grade r θ k) hx]
  change localizedCoordinateRingEquiv r θ j k x hx e z he
      (coordinateRestriction r θ j k x hx
        (algebraMap ℂ (ProjectiveCoordinateRing r θ j) c)) = _
  rw [localizedCoordinateRingEquiv_restriction, e.commutes]
  exact (IsScalarTower.algebraMap_apply ℂ B (Localization.Away z) c).symm

abbrev coordinateOverlapDen (r θ : ℂ) : CurveRing r θ :=
  coordinateDen r θ 1 * coordinateDen r θ 2

abbrev ProjectiveCoordinateOverlapRing (r θ : ℂ) :=
  HomogeneousLocalization.Away (curveGrade r θ) (coordinateOverlapDen r θ)

instance coordinateOverlapAlgebra (r θ : ℂ) : Algebra ℂ (ProjectiveCoordinateOverlapRing r θ) :=
  ((HomogeneousLocalization.fromZeroRingHom (curveGrade r θ)
    (Submonoid.powers (coordinateOverlapDen r θ))).comp
      (algebraMap ℂ (curveGrade r θ 0))).toAlgebra

def firstCoordinateRestriction (r θ : ℂ) :
    ProjectiveCoordinateRing r θ 1 →+* ProjectiveCoordinateOverlapRing r θ :=
  coordinateRestriction r θ 1 2 (coordinateOverlapDen r θ) rfl

def secondCoordinateRestriction (r θ : ℂ) :
    ProjectiveCoordinateRing r θ 2 →+* ProjectiveCoordinateOverlapRing r θ :=
  coordinateRestriction r θ 2 1 (coordinateOverlapDen r θ) (mul_comm _ _)

open CycleQ2GeometricAffineOverlap

private theorem first_middle_image (r θ : ℂ) :
    firstCoordinateEquiv r θ (coordinateRatio r θ 1 2) = middle (firstEquations r θ) := by
  rw [firstCoordinateEquiv_ratio]
  simp only [firstDehomogenize, aeval_X, Matrix.cons_val_two]
  rfl

private theorem second_middle_image (r θ : ℂ) :
    secondCoordinateEquiv r θ (coordinateRatio r θ 2 1) = middle (secondEquations r θ) := by
  rw [secondCoordinateEquiv_ratio]
  simp only [secondDehomogenize, aeval_X, Matrix.cons_val_one]
  rfl

def firstOverlapEquiv (r θ : ℂ) :
    ProjectiveCoordinateOverlapRing r θ ≃ₐ[ℂ] FirstOverlap r θ where
  __ := localizedCoordinateRingEquiv r θ 1 2 (coordinateOverlapDen r θ) rfl
    (firstCoordinateEquiv r θ) (middle (firstEquations r θ)) (first_middle_image r θ)
  commutes' := localizedCoordinateRingEquiv_constant r θ 1 2 (coordinateOverlapDen r θ) rfl
    (firstCoordinateEquiv r θ) (middle (firstEquations r θ)) (first_middle_image r θ)

def secondOverlapEquiv (r θ : ℂ) :
    ProjectiveCoordinateOverlapRing r θ ≃ₐ[ℂ] SecondOverlap r θ where
  __ := localizedCoordinateRingEquiv r θ 2 1 (coordinateOverlapDen r θ) (mul_comm _ _)
    (secondCoordinateEquiv r θ) (middle (secondEquations r θ)) (second_middle_image r θ)
  commutes' := localizedCoordinateRingEquiv_constant r θ 2 1 (coordinateOverlapDen r θ)
    (mul_comm _ _) (secondCoordinateEquiv r θ)
    (middle (secondEquations r θ)) (second_middle_image r θ)

theorem firstOverlapEquiv_restriction (r θ : ℂ) (a : ProjectiveCoordinateRing r θ 1) :
    firstOverlapEquiv r θ (firstCoordinateRestriction r θ a) =
      algebraMap (FirstChartRing r θ) (FirstOverlap r θ) (firstCoordinateEquiv r θ a) :=
  localizedCoordinateRingEquiv_restriction r θ 1 2 _ rfl _ _ (first_middle_image r θ) a

theorem secondOverlapEquiv_restriction (r θ : ℂ) (a : ProjectiveCoordinateRing r θ 2) :
    secondOverlapEquiv r θ (secondCoordinateRestriction r θ a) =
      algebraMap (SecondChartRing r θ) (SecondOverlap r θ) (secondCoordinateEquiv r θ a) :=
  localizedCoordinateRingEquiv_restriction r θ 2 1 _ (mul_comm _ _) _ _
    (second_middle_image r θ) a

theorem coordinateRatio_eq_awayMk (r θ : ℂ) (j k : Fin 4) :
    coordinateRatio r θ j k = HomogeneousLocalization.Away.mk (curveGrade r θ)
      (coordinate_mem_grade r θ j) 1 (coordinateDen r θ k)
      (by simpa using coordinate_mem_grade r θ k) := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.val_mk, pow_one]
  rfl

theorem coordinateRestriction_ratio_val (r θ : ℂ) (j k m : Fin 4)
    (x : CurveRing r θ) (hx : x = coordinateDen r θ j * coordinateDen r θ k) :
    (coordinateRestriction r θ j k x hx (coordinateRatio r θ j m)).val =
      Localization.mk (coordinateDen r θ m * coordinateDen r θ k)
        ⟨x, Submonoid.mem_powers x⟩ := by
  rw [coordinateRatio_eq_awayMk]
  change (HomogeneousLocalization.awayMap (curveGrade r θ)
    (coordinate_mem_grade r θ k) hx _).val = _
  rw [HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.Away.val_mk]
  simp only [pow_one]

/-- The coordinate substitutions hold in the actual homogeneous overlap. -/
theorem ratio_change_identity (r θ : ℂ) (k : Fin 4) :
    secondCoordinateRestriction r θ (coordinateRatio r θ 2 k) *
        firstCoordinateRestriction r θ (coordinateRatio r θ 1 2) =
      firstCoordinateRestriction r θ (coordinateRatio r θ 1 k) := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul]
  simp only [firstCoordinateRestriction, secondCoordinateRestriction,
    coordinateRestriction_ratio_val]
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Submonoid.coe_mul, one_mul,
    coordinateOverlapDen]
  ring

theorem firstOverlapEquiv_ratio (r θ : ℂ) (k : Fin 4) :
    firstOverlapEquiv r θ (firstCoordinateRestriction r θ (coordinateRatio r θ 1 k)) =
      polynomialMap (firstEquations r θ) (firstDehomogenize (X k)) := by
  rw [firstOverlapEquiv_restriction, firstCoordinateEquiv_ratio]
  rfl

theorem secondOverlapEquiv_ratio (r θ : ℂ) (k : Fin 4) :
    secondOverlapEquiv r θ (secondCoordinateRestriction r θ (coordinateRatio r θ 2 k)) =
      polynomialMap (secondEquations r θ) (secondDehomogenize (X k)) := by
  rw [secondOverlapEquiv_restriction, secondCoordinateEquiv_ratio]
  rfl

theorem firstOverlapEquiv_secondRatio (r θ : ℂ) (k : Fin 4) :
    firstOverlapEquiv r θ (secondCoordinateRestriction r θ (coordinateRatio r θ 2 k)) =
      polynomialMap (firstEquations r θ) (firstDehomogenize (X k)) *
        inverse (firstEquations r θ) := by
  have hb : firstOverlapEquiv r θ
      (firstCoordinateRestriction r θ (coordinateRatio r θ 1 2)) =
      coordinate (firstEquations r θ) 1 := by
    rw [firstOverlapEquiv_ratio]
    simp only [firstDehomogenize, aeval_X, Matrix.cons_val_two]
    rfl
  have h := congrArg (firstOverlapEquiv r θ) (ratio_change_identity r θ k)
  rw [map_mul, hb, firstOverlapEquiv_ratio] at h
  calc
    _ = (firstOverlapEquiv r θ
        (secondCoordinateRestriction r θ (coordinateRatio r θ 2 k)) *
          coordinate (firstEquations r θ) 1) * inverse (firstEquations r θ) := by
      rw [mul_assoc, coordinate_mul_inverse, mul_one]
    _ = _ := congrArg (fun z => z * inverse (firstEquations r θ)) h

theorem secondOverlapEquiv_inv_coordinate (r θ : ℂ) (i : Fin 3) :
    (secondOverlapEquiv r θ).symm (coordinate (secondEquations r θ) i) =
      secondCoordinateRestriction r θ (coordinateRatio r θ 2 ((2 : Fin 4).succAbove i)) := by
  apply (secondOverlapEquiv r θ).injective
  rw [AlgEquiv.apply_symm_apply, secondOverlapEquiv_ratio,
    ← dehomogenize_two, dehomogenize_succAbove]
  rfl

theorem overlapEquiv_comparison (r θ : ℂ) :
    (firstOverlapEquiv r θ).toAlgHom.comp (secondOverlapEquiv r θ).symm.toAlgHom =
      (overlapEquiv r θ).toAlgHom := by
  apply coordinate_algHom_ext (secondEquations r θ)
  intro i
  change firstOverlapEquiv r θ
    ((secondOverlapEquiv r θ).symm (coordinate (secondEquations r θ) i)) =
      overlapEquiv r θ (coordinate (secondEquations r θ) i)
  rw [secondOverlapEquiv_inv_coordinate, firstOverlapEquiv_secondRatio]
  fin_cases i
  · change polynomialMap (firstEquations r θ) (firstDehomogenize (X 0)) *
      inverse (firstEquations r θ) = overlapEquiv r θ (coordinate (secondEquations r θ) 0)
    rw [overlapEquiv_coordinate0]
    simp [firstDehomogenize, coordinate]
  · change polynomialMap (firstEquations r θ) (firstDehomogenize (X 1)) *
      inverse (firstEquations r θ) = overlapEquiv r θ (coordinate (secondEquations r θ) 1)
    rw [overlapEquiv_coordinate1]
    simp [firstDehomogenize]
  · change polynomialMap (firstEquations r θ) (firstDehomogenize (X 3)) *
      inverse (firstEquations r θ) = overlapEquiv r θ (coordinate (secondEquations r θ) 2)
    rw [overlapEquiv_coordinate2]
    simp [firstDehomogenize, coordinate]

/-- The established affine substitution is exactly the comparison of the
two presentations of the same projective overlap ring. -/
theorem overlapEquiv_compatibility (r θ : ℂ) (a : ProjectiveCoordinateOverlapRing r θ) :
    firstOverlapEquiv r θ a = overlapEquiv r θ (secondOverlapEquiv r θ a) := by
  have h := AlgHom.congr_fun (overlapEquiv_comparison r θ) (secondOverlapEquiv r θ a)
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] using h

/-! ## Structure-sheaf restrictions and actual affine scheme maps -/

def coordinateOverlapPatch (r θ : ℂ) : (projectiveCurve r θ).Opens :=
  Proj.basicOpen (curveGrade r θ) (coordinateOverlapDen r θ)

theorem coordinateOverlapPatch_eq (r θ : ℂ) :
    coordinateOverlapPatch r θ =
      coordinateProjectivePatch r θ 1 ⊓ coordinateProjectivePatch r θ 2 :=
  Proj.basicOpen_mul _ _ _

theorem coordinateOverlap_le_first (r θ : ℂ) :
    coordinateOverlapPatch r θ ≤ coordinateProjectivePatch r θ 1 :=
  Proj.basicOpen_mono (curveGrade r θ) _ _ ⟨_, rfl⟩

theorem coordinateOverlap_le_second (r θ : ℂ) :
    coordinateOverlapPatch r θ ≤ coordinateProjectivePatch r θ 2 :=
  Proj.basicOpen_mono (curveGrade r θ) _ _ ⟨_, mul_comm _ _⟩

theorem coordinateOverlapDen_mem_grade (r θ : ℂ) :
    coordinateOverlapDen r θ ∈ curveGrade r θ 2 :=
  SetLike.mul_mem_graded (coordinate_mem_grade r θ 1) (coordinate_mem_grade r θ 2)

def coordinateOverlapSectionsIso (r θ : ℂ) :
    CommRingCat.of (ProjectiveCoordinateOverlapRing r θ) ≅
      Γ(projectiveCurve r θ, coordinateOverlapPatch r θ) :=
  Proj.basicOpenIsoAway (curveGrade r θ) (coordinateOverlapDen r θ)
    (coordinateOverlapDen_mem_grade r θ) (by decide)

def firstOverlapSectionsEquiv (r θ : ℂ) :
    Γ(projectiveCurve r θ, coordinateOverlapPatch r θ) ≃+* FirstOverlap r θ :=
  (coordinateOverlapSectionsIso r θ).symm.commRingCatIsoToRingEquiv.trans
    (firstOverlapEquiv r θ).toRingEquiv

def secondOverlapSectionsEquiv (r θ : ℂ) :
    Γ(projectiveCurve r θ, coordinateOverlapPatch r θ) ≃+* SecondOverlap r θ :=
  (coordinateOverlapSectionsIso r θ).symm.commRingCatIsoToRingEquiv.trans
    (secondOverlapEquiv r θ).toRingEquiv

theorem firstCoordinateRestriction_is_sheaf_restriction (r θ : ℂ)
    (a : ProjectiveCoordinateRing r θ 1) :
    (projectiveCurve r θ).presheaf.map (homOfLE (coordinateOverlap_le_first r θ)).op
        ((Proj.basicOpenIsoAway (curveGrade r θ) (coordinateDen r θ 1)
          (coordinate_mem_grade r θ 1) (by decide)).hom a) =
      (coordinateOverlapSectionsIso r θ).hom (firstCoordinateRestriction r θ a) := by
  exact congrArg (fun k => k a)
    (Proj.awayMap_awayToSection (curveGrade r θ) (coordinate_mem_grade r θ 2) rfl).symm

theorem secondCoordinateRestriction_is_sheaf_restriction (r θ : ℂ)
    (a : ProjectiveCoordinateRing r θ 2) :
    (projectiveCurve r θ).presheaf.map (homOfLE (coordinateOverlap_le_second r θ)).op
        ((Proj.basicOpenIsoAway (curveGrade r θ) (coordinateDen r θ 2)
          (coordinate_mem_grade r θ 2) (by decide)).hom a) =
      (coordinateOverlapSectionsIso r θ).hom (secondCoordinateRestriction r θ a) := by
  exact congrArg (fun k => k a)
    (Proj.awayMap_awayToSection (curveGrade r θ)
      (coordinate_mem_grade r θ 1) (mul_comm _ _)).symm

theorem firstOverlapSectionsEquiv_restriction (r θ : ℂ)
    (s : Γ(projectiveCurve r θ, coordinateProjectivePatch r θ 1)) :
    firstOverlapSectionsEquiv r θ
        ((projectiveCurve r θ).presheaf.map (homOfLE (coordinateOverlap_le_first r θ)).op s) =
      algebraMap (FirstChartRing r θ) (FirstOverlap r θ) (firstCoordinateSectionsEquiv r θ s) := by
  have h := firstCoordinateRestriction_is_sheaf_restriction r θ
    ((Proj.basicOpenIsoAway (curveGrade r θ) (coordinateDen r θ 1)
      (coordinate_mem_grade r θ 1) (by decide)).inv s)
  rw [Iso.inv_hom_id_apply] at h
  change firstOverlapEquiv r θ ((coordinateOverlapSectionsIso r θ).inv _) = _
  rw [h, Iso.hom_inv_id_apply, firstOverlapEquiv_restriction]
  rfl

theorem secondOverlapSectionsEquiv_restriction (r θ : ℂ)
    (s : Γ(projectiveCurve r θ, coordinateProjectivePatch r θ 2)) :
    secondOverlapSectionsEquiv r θ
        ((projectiveCurve r θ).presheaf.map (homOfLE (coordinateOverlap_le_second r θ)).op s) =
      algebraMap (SecondChartRing r θ) (SecondOverlap r θ) (secondCoordinateSectionsEquiv r θ s) := by
  have h := secondCoordinateRestriction_is_sheaf_restriction r θ
    ((Proj.basicOpenIsoAway (curveGrade r θ) (coordinateDen r θ 2)
      (coordinate_mem_grade r θ 2) (by decide)).inv s)
  rw [Iso.inv_hom_id_apply] at h
  change secondOverlapEquiv r θ ((coordinateOverlapSectionsIso r θ).inv _) = _
  rw [h, Iso.hom_inv_id_apply, secondOverlapEquiv_restriction]
  rfl

theorem overlapSectionsEquiv_compatibility (r θ : ℂ)
    (s : Γ(projectiveCurve r θ, coordinateOverlapPatch r θ)) :
    firstOverlapSectionsEquiv r θ s = overlapEquiv r θ (secondOverlapSectionsEquiv r θ s) :=
  overlapEquiv_compatibility r θ _

open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricProjectiveCoefficients

theorem firstOverlapSectionsEquiv_coefficient (r θ c : ℂ) :
    firstOverlapSectionsEquiv r θ
        (coefficientOn (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
          (coordinateOverlapPatch r θ) c) =
      algebraMap ℂ (FirstOverlap r θ) c := by
  exact (congrArg (firstOverlapEquiv r θ)
    (coefficientOn_basicOpen r θ (coordinateOverlapDen r θ)
      (coordinateOverlapDen_mem_grade r θ) (by decide) c)).trans
        ((firstOverlapEquiv r θ).commutes c)

theorem secondOverlapSectionsEquiv_coefficient (r θ c : ℂ) :
    secondOverlapSectionsEquiv r θ
        (coefficientOn (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
          (coordinateOverlapPatch r θ) c) =
      algebraMap ℂ (SecondOverlap r θ) c := by
  exact (congrArg (secondOverlapEquiv r θ)
    (coefficientOn_basicOpen r θ (coordinateOverlapDen r θ)
      (coordinateOverlapDen_mem_grade r θ) (by decide) c)).trans
        ((secondOverlapEquiv r θ).commutes c)

theorem denominatorOverlap_le_coordinateOverlap (r θ : ℂ) :
    overlapProjectivePatch r θ ≤ coordinateOverlapPatch r θ := by
  rw [overlapProjectivePatch_eq, coordinateOverlapPatch_eq]
  exact inf_le_inf (firstProjectivePatch_le_firstCoordinate r θ)
    (secondProjectivePatch_le_secondCoordinate r θ)

def firstOverlapChartIso (r θ : ℂ) :
    (coordinateOverlapPatch r θ).toScheme ≅ Spec (CommRingCat.of (FirstOverlap r θ)) :=
  Proj.basicOpenIsoSpec (curveGrade r θ) (coordinateOverlapDen r θ)
      (coordinateOverlapDen_mem_grade r θ) (by decide) ≪≫
    Scheme.Spec.mapIso (firstOverlapEquiv r θ).toRingEquiv.toCommRingCatIso.symm.op

def secondOverlapChartIso (r θ : ℂ) :
    (coordinateOverlapPatch r θ).toScheme ≅ Spec (CommRingCat.of (SecondOverlap r θ)) :=
  Proj.basicOpenIsoSpec (curveGrade r θ) (coordinateOverlapDen r θ)
      (coordinateOverlapDen_mem_grade r θ) (by decide) ≪≫
    Scheme.Spec.mapIso (secondOverlapEquiv r θ).toRingEquiv.toCommRingCatIso.symm.op

/-- The coordinate transition on the actual overlap scheme is induced by
the literal affine substitution already used for the cofactor forms. -/
theorem overlapChartIso_transition (r θ : ℂ) :
    (firstOverlapChartIso r θ).inv ≫ (secondOverlapChartIso r θ).hom =
      Spec.map (CommRingCat.ofHom (overlapEquiv r θ).toRingHom) := by
  change (Spec.map (CommRingCat.ofHom (firstOverlapEquiv r θ).toRingHom) ≫
      (Proj.basicOpenIsoSpec (curveGrade r θ) (coordinateOverlapDen r θ)
        (coordinateOverlapDen_mem_grade r θ) (by decide)).inv) ≫
    ((Proj.basicOpenIsoSpec (curveGrade r θ) (coordinateOverlapDen r θ)
      (coordinateOverlapDen_mem_grade r θ) (by decide)).hom ≫
        Spec.map (CommRingCat.ofHom (secondOverlapEquiv r θ).symm.toRingHom)) = _
  rw [Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact AlgHom.congr_fun (overlapEquiv_comparison r θ) a

theorem firstOverlapEquiv_symm_base (r θ : ℂ) (a : FirstChartRing r θ) :
    (firstOverlapEquiv r θ).symm (algebraMap (FirstChartRing r θ) (FirstOverlap r θ) a) =
      firstCoordinateRestriction r θ ((firstCoordinateEquiv r θ).symm a) := by
  apply (firstOverlapEquiv r θ).injective
  rw [AlgEquiv.apply_symm_apply, firstOverlapEquiv_restriction, AlgEquiv.apply_symm_apply]

theorem secondOverlapEquiv_symm_base (r θ : ℂ) (a : SecondChartRing r θ) :
    (secondOverlapEquiv r θ).symm (algebraMap (SecondChartRing r θ) (SecondOverlap r θ) a) =
      secondCoordinateRestriction r θ ((secondCoordinateEquiv r θ).symm a) := by
  apply (secondOverlapEquiv r θ).injective
  rw [AlgEquiv.apply_symm_apply, secondOverlapEquiv_restriction, AlgEquiv.apply_symm_apply]

/-- The first affine localization map is the actual restriction from its
coordinate chart to the projective coordinate overlap. -/
theorem firstOverlapChartIso_restriction (r θ : ℂ) :
    (firstOverlapChartIso r θ).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap (FirstChartRing r θ) (FirstOverlap r θ))) =
      (projectiveCurve r θ).homOfLE (coordinateOverlap_le_first r θ) ≫
        (firstCoordinateChartIso r θ).hom := by
  have he : CommRingCat.ofHom (algebraMap (FirstChartRing r θ) (FirstOverlap r θ)) ≫
      CommRingCat.ofHom (firstOverlapEquiv r θ).symm.toRingHom =
      CommRingCat.ofHom (firstCoordinateEquiv r θ).symm.toRingHom ≫
        CommRingCat.ofHom (firstCoordinateRestriction r θ) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact firstOverlapEquiv_symm_base r θ a
  change (Proj.basicOpenToSpec (curveGrade r θ) (coordinateOverlapDen r θ) ≫
      Spec.map (CommRingCat.ofHom (firstOverlapEquiv r θ).symm.toRingHom)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (FirstChartRing r θ) (FirstOverlap r θ))) =
    (Proj (curveGrade r θ)).homOfLE
      (Proj.basicOpen_mono (curveGrade r θ) (coordinateDen r θ 1)
        (coordinateOverlapDen r θ) ⟨_, rfl⟩) ≫
      (Proj.basicOpenToSpec (curveGrade r θ) (coordinateDen r θ 1) ≫
        Spec.map (CommRingCat.ofHom (firstCoordinateEquiv r θ).symm.toRingHom))
  rw [Category.assoc, ← Spec.map_comp, he, Spec.map_comp, ← Category.assoc]
  exact congrArg (fun f => f ≫
    Spec.map (CommRingCat.ofHom (firstCoordinateEquiv r θ).symm.toRingHom))
      (Proj.basicOpenToSpec_SpecMap_awayMap (curveGrade r θ)
        (coordinate_mem_grade r θ 2) rfl)

/-- The second affine localization map is the actual restriction from its
coordinate chart to the projective coordinate overlap. -/
theorem secondOverlapChartIso_restriction (r θ : ℂ) :
    (secondOverlapChartIso r θ).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap (SecondChartRing r θ) (SecondOverlap r θ))) =
      (projectiveCurve r θ).homOfLE (coordinateOverlap_le_second r θ) ≫
        (secondCoordinateChartIso r θ).hom := by
  have he : CommRingCat.ofHom (algebraMap (SecondChartRing r θ) (SecondOverlap r θ)) ≫
      CommRingCat.ofHom (secondOverlapEquiv r θ).symm.toRingHom =
      CommRingCat.ofHom (secondCoordinateEquiv r θ).symm.toRingHom ≫
        CommRingCat.ofHom (secondCoordinateRestriction r θ) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact secondOverlapEquiv_symm_base r θ a
  change (Proj.basicOpenToSpec (curveGrade r θ) (coordinateOverlapDen r θ) ≫
      Spec.map (CommRingCat.ofHom (secondOverlapEquiv r θ).symm.toRingHom)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (SecondChartRing r θ) (SecondOverlap r θ))) =
    (Proj (curveGrade r θ)).homOfLE
      (Proj.basicOpen_mono (curveGrade r θ) (coordinateDen r θ 2)
        (coordinateOverlapDen r θ) ⟨_, mul_comm _ _⟩) ≫
      (Proj.basicOpenToSpec (curveGrade r θ) (coordinateDen r θ 2) ≫
        Spec.map (CommRingCat.ofHom (secondCoordinateEquiv r θ).symm.toRingHom))
  rw [Category.assoc, ← Spec.map_comp, he, Spec.map_comp, ← Category.assoc]
  exact congrArg (fun f => f ≫
    Spec.map (CommRingCat.ofHom (secondCoordinateEquiv r θ).symm.toRingHom))
      (Proj.basicOpenToSpec_SpecMap_awayMap (curveGrade r θ)
        (coordinate_mem_grade r θ 1) (mul_comm _ _))

end CycleQ2GeometricProjectiveOverlap

end
