import Proposal.GeometricSurfaceDifferentialCharts

section SurfaceOverlapPart

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricSurfaceOverlap

open MvPolynomial CategoryTheory AlgebraicGeometry
open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2ConormalJacobian
open CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
open CycleQ2CartierSurfaceGrading CycleQ2CartierProjectiveCover
open CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSurfaceDehomogenizedCharts
open CycleQ2GeometricSurfaceCoefficients

abbrev coordinateDen (r θ : ℂ) (i : Fin 4) : SurfaceRing r θ :=
  surfaceQuotient r θ (X i.castSucc)

def coordinateRestriction (r θ : ℂ) (j k : Fin 4) (x : SurfaceRing r θ)
    (hx : x = coordinateDen r θ j * coordinateDen r θ k) :
    CoordinateRing r θ j →+* HomogeneousLocalization.Away (surfaceGrade r θ) x :=
  HomogeneousLocalization.awayMap (surfaceGrade r θ) (coordinate_mem_grade r θ k) hx

theorem coordinateLocalizationElement_eq (r θ : ℂ) (j k : Fin 4) :
    HomogeneousLocalization.Away.isLocalizationElem
      (coordinate_mem_grade r θ j) (coordinate_mem_grade r θ k) =
      coordinateRatio r θ j k.castSucc := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.isLocalizationElem, coordinateRatio,
    homogeneousFraction, weight_castSucc, HomogeneousLocalization.Away.val_mk, pow_one]

theorem coordinateRestriction_isLocalization (r θ : ℂ) (j k : Fin 4)
    (x : SurfaceRing r θ) (hx : x = coordinateDen r θ j * coordinateDen r θ k) :
    letI := (coordinateRestriction r θ j k x hx).toAlgebra
    IsLocalization.Away (coordinateRatio r θ j k.castSucc)
      (HomogeneousLocalization.Away (surfaceGrade r θ) x) := by
  let := (coordinateRestriction r θ j k x hx).toAlgebra
  rw [← coordinateLocalizationElement_eq]
  exact HomogeneousLocalization.Away.isLocalization_mul
    (coordinate_mem_grade r θ j) (coordinate_mem_grade r θ k) hx (by decide)

/-- The actual surface homogeneous overlap is the localization of the proved affine chart. -/
def localizedCoordinateRingEquiv {B : Type*} [CommRing B] [Algebra ℂ B]
    (r θ : ℂ) (j k : Fin 4) (x : SurfaceRing r θ)
    (hx : x = coordinateDen r θ j * coordinateDen r θ k)
    (e : CoordinateRing r θ j ≃ₐ[ℂ] B)
    (z : B) (he : e (coordinateRatio r θ j k.castSucc) = z) :
    HomogeneousLocalization.Away (surfaceGrade r θ) x ≃+* Localization.Away z := by
  letI := (coordinateRestriction r θ j k x hx).toAlgebra
  letI := coordinateRestriction_isLocalization r θ j k x hx
  exact IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (coordinateRatio r θ j k.castSucc)) (T := Submonoid.powers z)
    _ _ e.toRingEquiv (by
      rw [Submonoid.map_powers]
      exact congrArg Submonoid.powers he)

theorem localizedCoordinateRingEquiv_restriction {B : Type*} [CommRing B] [Algebra ℂ B]
    (r θ : ℂ) (j k : Fin 4) (x : SurfaceRing r θ)
    (hx : x = coordinateDen r θ j * coordinateDen r θ k)
    (e : CoordinateRing r θ j ≃ₐ[ℂ] B)
    (z : B) (he : e (coordinateRatio r θ j k.castSucc) = z)
    (a : CoordinateRing r θ j) :
    localizedCoordinateRingEquiv r θ j k x hx e z he
        (coordinateRestriction r θ j k x hx a) =
      algebraMap B (Localization.Away z) (e a) := by
  let := (coordinateRestriction r θ j k x hx).toAlgebra
  let := coordinateRestriction_isLocalization r θ j k x hx
  exact IsLocalization.ringEquivOfRingEquiv_eq
    (S := HomogeneousLocalization.Away (surfaceGrade r θ) x)
    (Q := Localization.Away z) (M := Submonoid.powers (coordinateRatio r θ j k.castSucc))
    (T := Submonoid.powers z) (j := e.toRingEquiv) (by
      rw [Submonoid.map_powers]
      exact congrArg Submonoid.powers he) a

theorem localizedCoordinateRingEquiv_constant {B : Type*} [CommRing B] [Algebra ℂ B]
    (r θ : ℂ) (j k : Fin 4) (x : SurfaceRing r θ)
    (hx : x = coordinateDen r θ j * coordinateDen r θ k)
    (e : CoordinateRing r θ j ≃ₐ[ℂ] B)
    (z : B) (he : e (coordinateRatio r θ j k.castSucc) = z) (c : ℂ) :
    localizedCoordinateRingEquiv r θ j k x hx e z he
        (HomogeneousLocalization.fromZeroRingHom (surfaceGrade r θ) (Submonoid.powers x)
          (algebraMap ℂ (surfaceGrade r θ 0) c)) =
      algebraMap ℂ (Localization.Away z) c := by
  rw [← HomogeneousLocalization.awayMap_fromZeroRingHom (surfaceGrade r θ)
    (coordinate_mem_grade r θ k) hx]
  change localizedCoordinateRingEquiv r θ j k x hx e z he
      (coordinateRestriction r θ j k x hx
        (algebraMap ℂ (CoordinateRing r θ j) c)) = _
  rw [localizedCoordinateRingEquiv_restriction, e.commutes]
  exact (IsScalarTower.algebraMap_apply ℂ B (Localization.Away z) c).symm

abbrev overlapDen (r θ : ℂ) : SurfaceRing r θ :=
  coordinateDen r θ 1 * coordinateDen r θ 2

abbrev ProjectiveOverlapRing (r θ : ℂ) :=
  HomogeneousLocalization.Away (surfaceGrade r θ) (overlapDen r θ)

instance overlapAlgebra (r θ : ℂ) : Algebra ℂ (ProjectiveOverlapRing r θ) :=
  ((HomogeneousLocalization.fromZeroRingHom (surfaceGrade r θ)
    (Submonoid.powers (overlapDen r θ))).comp
      (algebraMap ℂ (surfaceGrade r θ 0))).toAlgebra

def firstRestriction (r θ : ℂ) : CoordinateRing r θ 1 →+* ProjectiveOverlapRing r θ :=
  coordinateRestriction r θ 1 2 (overlapDen r θ) rfl

def secondRestriction (r θ : ℂ) : CoordinateRing r θ 2 →+* ProjectiveOverlapRing r θ :=
  coordinateRestriction r θ 2 1 (overlapDen r θ) (mul_comm _ _)

def middle (v : Fin 2 → SurfacePoly) : SurfaceChartRing v :=
  Ideal.Quotient.mk (surfaceChartIdeal v) (X (some 1))

abbrev CoordinateOverlap (v : Fin 2 → SurfacePoly) := Localization.Away (middle v)
abbrev FirstOverlap (r θ : ℂ) := CoordinateOverlap (firstEquations r θ)
abbrev SecondOverlap (r θ : ℂ) := CoordinateOverlap (secondEquations r θ)

def polynomialMap (v : Fin 2 → SurfacePoly) : SurfacePoly →ₐ[ℂ] CoordinateOverlap v :=
  (IsScalarTower.toAlgHom ℂ (SurfaceChartRing v) (CoordinateOverlap v)).comp
    (Ideal.Quotient.mkₐ ℂ (surfaceChartIdeal v))

def coordinate (v : Fin 2 → SurfacePoly) (j : Option (Fin 3)) : CoordinateOverlap v :=
  polynomialMap v (X j)

def inverse (v : Fin 2 → SurfacePoly) : CoordinateOverlap v :=
  IsLocalization.Away.invSelf (middle v)

theorem coordinate_mul_inverse (v : Fin 2 → SurfacePoly) :
    coordinate v (some 1) * inverse v = 1 :=
  IsLocalization.Away.mul_invSelf (middle v)

private theorem first_middle_image (r θ : ℂ) :
    firstChartAlgEquiv r θ (coordinateRatio r θ 1 (2 : Fin 4).castSucc) =
      middle (firstEquations r θ) := by
  change firstChartEquiv r θ (homogeneousFraction r θ 1 1 (X 2) _) = _
  rw [firstChartEquiv_homogeneousFraction]
  simp only [firstSurfaceDehomogenize, aeval_X, Matrix.cons_val_two]
  rfl

private theorem second_middle_image (r θ : ℂ) :
    secondChartAlgEquiv r θ (coordinateRatio r θ 2 (1 : Fin 4).castSucc) =
      middle (secondEquations r θ) := by
  change secondChartEquiv r θ (homogeneousFraction r θ 2 1 (X 1) _) = _
  rw [secondChartEquiv_homogeneousFraction]
  simp only [secondSurfaceDehomogenize, aeval_X, Matrix.cons_val_one]
  rfl

def firstOverlapEquiv (r θ : ℂ) : ProjectiveOverlapRing r θ ≃ₐ[ℂ] FirstOverlap r θ where
  __ := localizedCoordinateRingEquiv r θ 1 2 (overlapDen r θ) rfl
    (firstChartAlgEquiv r θ) (middle (firstEquations r θ)) (first_middle_image r θ)
  commutes' := localizedCoordinateRingEquiv_constant r θ 1 2 (overlapDen r θ) rfl
    (firstChartAlgEquiv r θ) (middle (firstEquations r θ)) (first_middle_image r θ)

def secondOverlapEquiv (r θ : ℂ) : ProjectiveOverlapRing r θ ≃ₐ[ℂ] SecondOverlap r θ where
  __ := localizedCoordinateRingEquiv r θ 2 1 (overlapDen r θ) (mul_comm _ _)
    (secondChartAlgEquiv r θ) (middle (secondEquations r θ)) (second_middle_image r θ)
  commutes' := localizedCoordinateRingEquiv_constant r θ 2 1 (overlapDen r θ)
    (mul_comm _ _) (secondChartAlgEquiv r θ)
    (middle (secondEquations r θ)) (second_middle_image r θ)

theorem firstOverlapEquiv_restriction (r θ : ℂ) (a : CoordinateRing r θ 1) :
    firstOverlapEquiv r θ (firstRestriction r θ a) =
      algebraMap (SurfaceChartRing (firstEquations r θ)) (FirstOverlap r θ)
        (firstChartEquiv r θ a) :=
  localizedCoordinateRingEquiv_restriction r θ 1 2 _ rfl _ _ (first_middle_image r θ) a

theorem secondOverlapEquiv_restriction (r θ : ℂ) (a : CoordinateRing r θ 2) :
    secondOverlapEquiv r θ (secondRestriction r θ a) =
      algebraMap (SurfaceChartRing (secondEquations r θ)) (SecondOverlap r θ)
        (secondChartEquiv r θ a) :=
  localizedCoordinateRingEquiv_restriction r θ 2 1 _ (mul_comm _ _) _ _
    (second_middle_image r θ) a

theorem restriction_homogeneousFraction_val (r θ : ℂ) (j k : Fin 4)
    (x : SurfaceRing r θ) (hx : x = coordinateDen r θ j * coordinateDen r θ k)
    (n : ℕ) (p : WeightedPoly) (hp : p.IsWeightedHomogeneous weight n) :
    (coordinateRestriction r θ j k x hx (homogeneousFraction r θ j n p hp)).val =
      Localization.mk (surfaceQuotient r θ p * coordinateDen r θ k ^ n)
        ⟨x ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers x) n⟩ := by
  change (HomogeneousLocalization.awayMap (surfaceGrade r θ)
    (coordinate_mem_grade r θ k) hx
    (HomogeneousLocalization.Away.mk (surfaceGrade r θ) (coordinate_mem_grade r θ j)
      n (surfaceQuotient r θ p) _)).val = _
  rw [HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.Away.val_mk]

theorem homogeneousFraction_change (r θ : ℂ) (n : ℕ) (p : WeightedPoly)
    (hp : p.IsWeightedHomogeneous weight n) :
    secondRestriction r θ (homogeneousFraction r θ 2 n p hp) *
        firstRestriction r θ (coordinateRatio r θ 1 (2 : Fin 4).castSucc) ^ n =
      firstRestriction r θ (homogeneousFraction r θ 1 n p hp) := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow]
  simp only [firstRestriction, secondRestriction, coordinateRatio,
    restriction_homogeneousFraction_val, weight_castSucc]
  rw [Localization.mk_pow, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Submonoid.coe_mul, SubmonoidClass.coe_pow, one_mul,
    overlapDen, mul_pow, pow_one]
  ring

theorem firstOverlapEquiv_fraction (r θ : ℂ) (n : ℕ) (p : WeightedPoly)
    (hp : p.IsWeightedHomogeneous weight n) :
    firstOverlapEquiv r θ (firstRestriction r θ (homogeneousFraction r θ 1 n p hp)) =
      polynomialMap (firstEquations r θ) (firstSurfaceDehomogenize p) := by
  rw [firstOverlapEquiv_restriction, firstChartEquiv_homogeneousFraction]
  rfl

theorem secondOverlapEquiv_fraction (r θ : ℂ) (n : ℕ) (p : WeightedPoly)
    (hp : p.IsWeightedHomogeneous weight n) :
    secondOverlapEquiv r θ (secondRestriction r θ (homogeneousFraction r θ 2 n p hp)) =
      polynomialMap (secondEquations r θ) (secondSurfaceDehomogenize p) := by
  rw [secondOverlapEquiv_restriction, secondChartEquiv_homogeneousFraction]
  rfl

theorem firstOverlapEquiv_secondFraction (r θ : ℂ) (n : ℕ) (p : WeightedPoly)
    (hp : p.IsWeightedHomogeneous weight n) :
    firstOverlapEquiv r θ (secondRestriction r θ (homogeneousFraction r θ 2 n p hp)) =
      polynomialMap (firstEquations r θ) (firstSurfaceDehomogenize p) *
        inverse (firstEquations r θ) ^ n := by
  have hb : firstOverlapEquiv r θ
      (firstRestriction r θ (coordinateRatio r θ 1 (2 : Fin 4).castSucc)) =
      coordinate (firstEquations r θ) (some 1) := by
    change firstOverlapEquiv r θ (firstRestriction r θ
      (homogeneousFraction r θ 1 1 (X 2) _)) = _
    rw [firstOverlapEquiv_fraction]
    simp only [firstSurfaceDehomogenize, aeval_X, Matrix.cons_val_two]
    rfl
  have h := congrArg (firstOverlapEquiv r θ) (homogeneousFraction_change r θ n p hp)
  rw [map_mul, map_pow, hb, firstOverlapEquiv_fraction] at h
  have hi : coordinate (firstEquations r θ) (some 1) ^ n *
      inverse (firstEquations r θ) ^ n = 1 := by
    rw [← mul_pow, coordinate_mul_inverse, one_pow]
  calc
    _ = (firstOverlapEquiv r θ (secondRestriction r θ (homogeneousFraction r θ 2 n p hp)) *
        coordinate (firstEquations r θ) (some 1) ^ n) * inverse (firstEquations r θ) ^ n := by
      rw [mul_assoc, hi, mul_one]
    _ = _ := congrArg (fun z => z * inverse (firstEquations r θ) ^ n) h

/-- Comparison of the two actual presentations of the same weighted projective overlap. -/
def overlapEquiv (r θ : ℂ) : SecondOverlap r θ ≃ₐ[ℂ] FirstOverlap r θ :=
  (secondOverlapEquiv r θ).symm.trans (firstOverlapEquiv r θ)

theorem overlapEquiv_dehomogenize (r θ : ℂ) (n : ℕ) (p : WeightedPoly)
    (hp : p.IsWeightedHomogeneous weight n) :
    overlapEquiv r θ (polynomialMap (secondEquations r θ) (secondSurfaceDehomogenize p)) =
      polynomialMap (firstEquations r θ) (firstSurfaceDehomogenize p) *
        inverse (firstEquations r θ) ^ n := by
  rw [← secondOverlapEquiv_fraction r θ n p hp]
  change firstOverlapEquiv r θ ((secondOverlapEquiv r θ).symm
    (secondOverlapEquiv r θ (secondRestriction r θ (homogeneousFraction r θ 2 n p hp)))) = _
  rw [AlgEquiv.symm_apply_apply]
  exact firstOverlapEquiv_secondFraction r θ n p hp

theorem overlapEquiv_coordinate0 (r θ : ℂ) :
    overlapEquiv r θ (coordinate (secondEquations r θ) (some 0)) =
      coordinate (firstEquations r θ) (some 0) * inverse (firstEquations r θ) := by
  have h := overlapEquiv_dehomogenize r θ 1 (X 0) (by
    simpa [CycleQ2CartierSurfaceGrading.weight] using isWeightedHomogeneous_X ℂ weight (0 : Fin 5))
  simpa [firstSurfaceDehomogenize, secondSurfaceDehomogenize, coordinate] using h

theorem overlapEquiv_coordinate1 (r θ : ℂ) :
    overlapEquiv r θ (coordinate (secondEquations r θ) (some 1)) =
      inverse (firstEquations r θ) := by
  have h := overlapEquiv_dehomogenize r θ 1 (X 1) (by
    simpa [CycleQ2CartierSurfaceGrading.weight] using isWeightedHomogeneous_X ℂ weight (1 : Fin 5))
  simpa [firstSurfaceDehomogenize, secondSurfaceDehomogenize, coordinate] using h

theorem overlapEquiv_coordinate2 (r θ : ℂ) :
    overlapEquiv r θ (coordinate (secondEquations r θ) (some 2)) =
      coordinate (firstEquations r θ) (some 2) * inverse (firstEquations r θ) := by
  have h := overlapEquiv_dehomogenize r θ 1 (X 3) (by
    simpa [CycleQ2CartierSurfaceGrading.weight] using isWeightedHomogeneous_X ℂ weight (3 : Fin 5))
  simpa [firstSurfaceDehomogenize, secondSurfaceDehomogenize, coordinate] using h

/-- The normal coordinate is the actual weight-two homogeneous fraction f₂/Xi². -/
theorem overlapEquiv_normalCoordinate (r θ : ℂ) :
    overlapEquiv r θ (coordinate (secondEquations r θ) none) =
      coordinate (firstEquations r θ) none * inverse (firstEquations r θ) ^ 2 := by
  have h := overlapEquiv_dehomogenize r θ 2 originalF2 originalF2_homogeneous
  simpa only [firstSurfaceDehomogenize_f2, secondSurfaceDehomogenize_f2, coordinate] using h

def middleUnit (v : Fin 2 → SurfacePoly) : (CoordinateOverlap v)ˣ :=
  Units.mkOfMulEqOne (coordinate v (some 1)) (inverse v) (coordinate_mul_inverse v)

theorem differential_inverse (v : Fin 2 → SurfacePoly) :
    KaehlerDifferential.D ℂ (CoordinateOverlap v) (inverse v) =
      -(inverse v ^ 2) • KaehlerDifferential.D ℂ (CoordinateOverlap v) (coordinate v (some 1)) :=
  CycleQ2GeometricResidueFrames.derivation_unit_inverse
    (KaehlerDifferential.D ℂ (CoordinateOverlap v)) (middleUnit v)

def overlapDifferentialEquiv (r θ : ℂ) :
    KaehlerDifferential ℂ (SecondOverlap r θ) ≃ₗ[ℂ] KaehlerDifferential ℂ (FirstOverlap r θ) :=
  CycleQ2GeometricAffineOverlap.differentialEquiv (overlapEquiv r θ)

theorem overlapDifferential_coordinate0 (r θ : ℂ) :
    overlapDifferentialEquiv r θ
      (KaehlerDifferential.D ℂ (SecondOverlap r θ) (coordinate (secondEquations r θ) (some 0))) =
      inverse (firstEquations r θ) •
        KaehlerDifferential.D ℂ (FirstOverlap r θ) (coordinate (firstEquations r θ) (some 0)) -
      (coordinate (firstEquations r θ) (some 0) * inverse (firstEquations r θ) ^ 2) •
        KaehlerDifferential.D ℂ (FirstOverlap r θ) (coordinate (firstEquations r θ) (some 1)) := by
  rw [overlapDifferentialEquiv, CycleQ2GeometricAffineOverlap.differentialEquiv_D,
    overlapEquiv_coordinate0, Derivation.leibniz, differential_inverse]
  rw [smul_smul, mul_neg, neg_smul, sub_eq_add_neg]
  exact add_comm _ _

theorem overlapDifferential_coordinate1 (r θ : ℂ) :
    overlapDifferentialEquiv r θ
      (KaehlerDifferential.D ℂ (SecondOverlap r θ) (coordinate (secondEquations r θ) (some 1))) =
      -(inverse (firstEquations r θ) ^ 2) •
        KaehlerDifferential.D ℂ (FirstOverlap r θ) (coordinate (firstEquations r θ) (some 1)) := by
  rw [overlapDifferentialEquiv, CycleQ2GeometricAffineOverlap.differentialEquiv_D,
    overlapEquiv_coordinate1, differential_inverse]

theorem overlapDifferential_coordinate2 (r θ : ℂ) :
    overlapDifferentialEquiv r θ
      (KaehlerDifferential.D ℂ (SecondOverlap r θ) (coordinate (secondEquations r θ) (some 2))) =
      inverse (firstEquations r θ) •
        KaehlerDifferential.D ℂ (FirstOverlap r θ) (coordinate (firstEquations r θ) (some 2)) -
      (coordinate (firstEquations r θ) (some 2) * inverse (firstEquations r θ) ^ 2) •
        KaehlerDifferential.D ℂ (FirstOverlap r θ) (coordinate (firstEquations r θ) (some 1)) := by
  rw [overlapDifferentialEquiv, CycleQ2GeometricAffineOverlap.differentialEquiv_D,
    overlapEquiv_coordinate2, Derivation.leibniz, differential_inverse]
  rw [smul_smul, mul_neg, neg_smul, sub_eq_add_neg]
  exact add_comm _ _

private theorem derivation_mul_square {R M : Type*} [CommRing R] [Algebra ℂ R]
    [AddCommGroup M] [Module ℂ M] [Module R M] [IsScalarTower ℂ R M]
    (D : Derivation ℂ R M) (z b t : R) (ht : D t = -(t ^ 2) • D b) :
    D (z * t ^ 2) = t ^ 2 • D z - (2 * z * t ^ 3) • D b := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, ht]
  simp only [Nat.reduceSub, pow_one, smul_smul, smul_neg, neg_smul]
  module

/-- The derivative of the actual weight-two normal coordinate retains its denominator term. -/
theorem overlapDifferential_normalCoordinate (r θ : ℂ) :
    overlapDifferentialEquiv r θ
      (KaehlerDifferential.D ℂ (SecondOverlap r θ) (coordinate (secondEquations r θ) none)) =
      inverse (firstEquations r θ) ^ 2 •
        KaehlerDifferential.D ℂ (FirstOverlap r θ) (coordinate (firstEquations r θ) none) -
      (2 * coordinate (firstEquations r θ) none * inverse (firstEquations r θ) ^ 3) •
        KaehlerDifferential.D ℂ (FirstOverlap r θ) (coordinate (firstEquations r θ) (some 1)) := by
  rw [overlapDifferentialEquiv, CycleQ2GeometricAffineOverlap.differentialEquiv_D,
    overlapEquiv_normalCoordinate]
  exact derivation_mul_square (KaehlerDifferential.D ℂ (FirstOverlap r θ))
    (coordinate (firstEquations r θ) none) (coordinate (firstEquations r θ) (some 1))
    (inverse (firstEquations r θ)) (differential_inverse (firstEquations r θ))

def overlapPatch (r θ : ℂ) : (projectiveSurface r θ).Opens :=
  Proj.basicOpen (surfaceGrade r θ) (overlapDen r θ)

theorem overlapPatch_eq (r θ : ℂ) :
    overlapPatch r θ = coordinatePatch r θ 1 ⊓ coordinatePatch r θ 2 :=
  Proj.basicOpen_mul _ _ _

theorem overlap_le_first (r θ : ℂ) : overlapPatch r θ ≤ coordinatePatch r θ 1 :=
  Proj.basicOpen_mono (surfaceGrade r θ) _ _ ⟨_, rfl⟩

theorem overlap_le_second (r θ : ℂ) : overlapPatch r θ ≤ coordinatePatch r θ 2 :=
  Proj.basicOpen_mono (surfaceGrade r θ) _ _ ⟨_, mul_comm _ _⟩

theorem overlapDen_mem_grade (r θ : ℂ) : overlapDen r θ ∈ surfaceGrade r θ 2 :=
  SetLike.mul_mem_graded (coordinate_mem_grade r θ 1) (coordinate_mem_grade r θ 2)

def overlapSectionsIso (r θ : ℂ) :
    CommRingCat.of (ProjectiveOverlapRing r θ) ≅ Γ(projectiveSurface r θ, overlapPatch r θ) :=
  Proj.basicOpenIsoAway (surfaceGrade r θ) (overlapDen r θ)
    (overlapDen_mem_grade r θ) (by decide)

def firstOverlapSectionsEquiv (r θ : ℂ) :
    Γ(projectiveSurface r θ, overlapPatch r θ) ≃+* FirstOverlap r θ :=
  (overlapSectionsIso r θ).symm.commRingCatIsoToRingEquiv.trans
    (firstOverlapEquiv r θ).toRingEquiv

def secondOverlapSectionsEquiv (r θ : ℂ) :
    Γ(projectiveSurface r θ, overlapPatch r θ) ≃+* SecondOverlap r θ :=
  (overlapSectionsIso r θ).symm.commRingCatIsoToRingEquiv.trans
    (secondOverlapEquiv r θ).toRingEquiv

theorem firstRestriction_is_sheaf_restriction (r θ : ℂ) (a : CoordinateRing r θ 1) :
    (projectiveSurface r θ).presheaf.map (homOfLE (overlap_le_first r θ)).op
        ((Proj.basicOpenIsoAway (surfaceGrade r θ) (coordinateDen r θ 1)
          (coordinate_mem_grade r θ 1) (by decide)).hom a) =
      (overlapSectionsIso r θ).hom (firstRestriction r θ a) := by
  exact congrArg (fun k => k a)
    (Proj.awayMap_awayToSection (surfaceGrade r θ) (coordinate_mem_grade r θ 2) rfl).symm

theorem secondRestriction_is_sheaf_restriction (r θ : ℂ) (a : CoordinateRing r θ 2) :
    (projectiveSurface r θ).presheaf.map (homOfLE (overlap_le_second r θ)).op
        ((Proj.basicOpenIsoAway (surfaceGrade r θ) (coordinateDen r θ 2)
          (coordinate_mem_grade r θ 2) (by decide)).hom a) =
      (overlapSectionsIso r θ).hom (secondRestriction r θ a) := by
  exact congrArg (fun k => k a)
    (Proj.awayMap_awayToSection (surfaceGrade r θ)
      (coordinate_mem_grade r θ 1) (mul_comm _ _)).symm

theorem firstOverlapSectionsEquiv_restriction (r θ : ℂ)
    (s : Γ(projectiveSurface r θ, coordinatePatch r θ 1)) :
    firstOverlapSectionsEquiv r θ
        ((projectiveSurface r θ).presheaf.map (homOfLE (overlap_le_first r θ)).op s) =
      algebraMap (SurfaceChartRing (firstEquations r θ)) (FirstOverlap r θ)
        (firstSectionsEquiv r θ s) := by
  have h := firstRestriction_is_sheaf_restriction r θ
    ((Proj.basicOpenIsoAway (surfaceGrade r θ) (coordinateDen r θ 1)
      (coordinate_mem_grade r θ 1) (by decide)).inv s)
  rw [Iso.inv_hom_id_apply] at h
  change firstOverlapEquiv r θ ((overlapSectionsIso r θ).inv _) = _
  rw [h, Iso.hom_inv_id_apply, firstOverlapEquiv_restriction]
  rfl

theorem secondOverlapSectionsEquiv_restriction (r θ : ℂ)
    (s : Γ(projectiveSurface r θ, coordinatePatch r θ 2)) :
    secondOverlapSectionsEquiv r θ
        ((projectiveSurface r θ).presheaf.map (homOfLE (overlap_le_second r θ)).op s) =
      algebraMap (SurfaceChartRing (secondEquations r θ)) (SecondOverlap r θ)
        (secondSectionsEquiv r θ s) := by
  have h := secondRestriction_is_sheaf_restriction r θ
    ((Proj.basicOpenIsoAway (surfaceGrade r θ) (coordinateDen r θ 2)
      (coordinate_mem_grade r θ 2) (by decide)).inv s)
  rw [Iso.inv_hom_id_apply] at h
  change secondOverlapEquiv r θ ((overlapSectionsIso r θ).inv _) = _
  rw [h, Iso.hom_inv_id_apply, secondOverlapEquiv_restriction]
  rfl

/-- The same equivalence compares the actual structure-sheaf restrictions. -/
theorem overlapSectionsEquiv_compatibility (r θ : ℂ)
    (s : Γ(projectiveSurface r θ, overlapPatch r θ)) :
    firstOverlapSectionsEquiv r θ s = overlapEquiv r θ (secondOverlapSectionsEquiv r θ s) := by
  change firstOverlapEquiv r θ ((overlapSectionsIso r θ).inv s) =
    firstOverlapEquiv r θ ((secondOverlapEquiv r θ).symm
      (secondOverlapEquiv r θ ((overlapSectionsIso r θ).inv s)))
  rw [AlgEquiv.symm_apply_apply]

#print axioms homogeneousFraction_change
#print axioms overlapDifferential_normalCoordinate
#print axioms overlapSectionsEquiv_compatibility

end CycleQ2GeometricSurfaceOverlap

end
end SurfaceOverlapPart

section SurfaceWeightedChangePart

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricSurfaceWeightedChange

open MvPolynomial
open CycleQ2SeedTrace CycleQ2NormalConnecting
open CycleQ2ConormalJacobian CycleQ2CartierSurfaceGrading CycleQ2GeometricSurfaceAdjunction
open CycleQ2GeometricSurfaceDehomogenizedCharts

section Evaluation

variable {R : Type*} [CommRing R] [Algebra ℂ R]

def surfaceEvaluate (z a b c : R) : SurfacePoly →ₐ[ℂ] R :=
  aeval (fun j => match j with | none => z | some k => ![a,b,c] k)

theorem derivation_aeval (D : Derivation ℂ R R) (x : Option (Fin 3) → R) (p : SurfacePoly) :
    D (aeval x p) = ∑ j : Option (Fin 3), aeval x (pderiv j p) * D (x j) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p i hp =>
      simp only [map_mul, aeval_X, Derivation.leibniz, pderiv_X, Pi.single_apply,
        smul_eq_mul, map_add, apply_ite, map_one, map_zero]
      rw [hp]
      simp [mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_left_comm, mul_comm]

theorem firstEvaluate_dehomogenize (z a b c : R) (p : WeightedPoly) :
    surfaceEvaluate z a b c (firstSurfaceDehomogenize p) =
      aeval ![a, 1, b, c, z - b ^ 2] p := by
  have h : (surfaceEvaluate z a b c).comp firstSurfaceDehomogenize =
      aeval ![a, 1, b, c, z - b ^ 2] := by
    apply MvPolynomial.algHom_ext
    intro j
    fin_cases j <;> simp [surfaceEvaluate, firstSurfaceDehomogenize]
  exact AlgHom.congr_fun h p

theorem secondEvaluate_dehomogenize (z a b c : R) (p : WeightedPoly) :
    surfaceEvaluate z a b c (secondSurfaceDehomogenize p) =
      aeval ![a, b, 1, c, z - 1] p := by
  have h : (surfaceEvaluate z a b c).comp secondSurfaceDehomogenize =
      aeval ![a, b, 1, c, z - 1] := by
    apply MvPolynomial.algHom_ext
    intro j
    fin_cases j <;> simp [surfaceEvaluate, secondSurfaceDehomogenize]
  exact AlgHom.congr_fun h p

/-- The literal weighted coordinate substitution, before imposing either surface equation. -/
theorem dehomogenize_scaling (z a b c t : R) (ht : b * t = 1)
    (p : WeightedPoly) (n : ℕ) (hp : p.IsWeightedHomogeneous weight n) :
    surfaceEvaluate (z * t ^ 2) (a * t) t (c * t) (secondSurfaceDehomogenize p) =
      t ^ n * surfaceEvaluate z a b c (firstSurfaceDehomogenize p) := by
  rw [firstEvaluate_dehomogenize, secondEvaluate_dehomogenize]
  have hv : (![a*t,t,1,c*t,z*t^2-1] : Fin 5 → R) =
      fun j => t ^ weight j * (![a,1,b,c,z-b^2] : Fin 5 → R) j := by
    funext j
    fin_cases j
    · simp [weight, mul_comm]
    · simp [weight]
    · simpa [weight, mul_comm] using ht.symm
    · simp [weight, mul_comm]
    · change z * t ^ 2 - 1 = t ^ 2 * (z - b ^ 2)
      linear_combination (b * t + 1) * ht
  rw [hv]
  exact weighted_homogeneous_eval_scale (algebraMap ℂ R)
    ![a,1,b,c,z-b^2] t p n hp

end Evaluation

section Determinant

variable {R : Type*} [CommRing R]

/-- Rows and columns both use the actual ambient order (z,a,b,c). -/
def coordinateJacobian (z a c t : R) : Matrix (Fin 4) (Fin 4) R :=
  !![t^2, 0, -2*z*t^3, 0;
     0, t, -a*t^2, 0;
     0, 0, -t^2, 0;
     0, 0, -c*t^2, t]

private theorem succAbove_four (i : Fin 4) (j : Fin 3) :
    i.succAbove j = (!![(1 : Fin 4), 2, 3; 0, 2, 3; 0, 1, 3; 0, 1, 2] i j) := by
  fin_cases i <;> fin_cases j <;> rfl

theorem coordinateJacobian_det (z a c t : R) :
    (coordinateJacobian z a c t).det = -t ^ 6 := by
  simp [coordinateJacobian, Matrix.det_succ_row_zero,
    Matrix.submatrix_apply, Fin.sum_univ_succ, succAbove_four]
  ring

end Determinant

abbrev AmbientOverlap := Localization.Away (X (some (1 : Fin 3)) : SurfacePoly)

def ambientCoordinate (j : Option (Fin 3)) : AmbientOverlap :=
  algebraMap SurfacePoly AmbientOverlap (X j)

def ambientInverse : AmbientOverlap :=
  IsLocalization.Away.invSelf (X (some (1 : Fin 3)) : SurfacePoly)

theorem ambient_coordinate_mul_inverse : ambientCoordinate (some 1) * ambientInverse = 1 :=
  IsLocalization.Away.mul_invSelf (X (some (1 : Fin 3)) : SurfacePoly)

def ambientMiddleUnit : AmbientOverlapˣ :=
  Units.mkOfMulEqOne (ambientCoordinate (some 1)) ambientInverse ambient_coordinate_mul_inverse

def ambientPartial (j : Option (Fin 3)) : Derivation ℂ AmbientOverlap AmbientOverlap :=
  CycleQ2GeometricFunctionalDifferentials.localizedDerivation
    (Submonoid.powers (X (some (1 : Fin 3)) : SurfacePoly)) AmbientOverlap
    ((KaehlerDifferential.mvPolynomialBasis ℂ (Option (Fin 3))).coord j)

theorem ambientPartial_base (j : Option (Fin 3)) (p : SurfacePoly) :
    ambientPartial j (algebraMap SurfacePoly AmbientOverlap p) =
      algebraMap SurfacePoly AmbientOverlap (pderiv j p) := by
  change CycleQ2GeometricFunctionalDifferentials.localizedDerivation
    (Submonoid.powers (X (some (1 : Fin 3)) : SurfacePoly)) AmbientOverlap
    ((KaehlerDifferential.mvPolynomialBasis ℂ (Option (Fin 3))).coord j)
      (algebraMap SurfacePoly AmbientOverlap p) = _
  rw [CycleQ2GeometricFunctionalDifferentials.localizedDerivation_algebraMap]
  simp only [Module.Basis.coord_apply, KaehlerDifferential.mvPolynomialBasis_repr_apply]

theorem ambientPartial_coordinate (j k : Option (Fin 3)) :
    ambientPartial j (ambientCoordinate k) = if k = j then 1 else 0 := by
  rw [ambientCoordinate, ambientPartial_base]
  by_cases h : k = j <;> simp [pderiv_X, h]

theorem ambientPartial_inverse (j : Option (Fin 3)) :
    ambientPartial j ambientInverse =
      -(ambientInverse ^ 2) * ambientPartial j (ambientCoordinate (some 1)) := by
  exact CycleQ2GeometricResidueFrames.derivation_unit_inverse (ambientPartial j) ambientMiddleUnit

theorem ambient_firstEvaluate (p : SurfacePoly) :
    surfaceEvaluate (ambientCoordinate none) (ambientCoordinate (some 0))
        (ambientCoordinate (some 1)) (ambientCoordinate (some 2)) p =
      algebraMap SurfacePoly AmbientOverlap p := by
  have h : surfaceEvaluate (ambientCoordinate none) (ambientCoordinate (some 0))
      (ambientCoordinate (some 1)) (ambientCoordinate (some 2)) =
      IsScalarTower.toAlgHom ℂ SurfacePoly AmbientOverlap := by
    apply MvPolynomial.algHom_ext
    intro j
    cases j with
    | none => simp only [surfaceEvaluate, aeval_X]; rfl
    | some j => fin_cases j <;> simp only [surfaceEvaluate, aeval_X] <;> rfl
  exact AlgHom.congr_fun h p

def ambientChangeCoordinate : Option (Fin 3) → AmbientOverlap :=
  fun j => match j with
    | none => ambientCoordinate none * ambientInverse ^ 2
    | some k => ![ambientCoordinate (some 0) * ambientInverse,
        ambientInverse, ambientCoordinate (some 2) * ambientInverse] k

def ambientChangeEvaluate : SurfacePoly →ₐ[ℂ] AmbientOverlap := aeval ambientChangeCoordinate

theorem ambient_dehomogenize_scaling (p : WeightedPoly) (n : ℕ)
    (hp : p.IsWeightedHomogeneous weight n) :
    ambientChangeEvaluate (secondSurfaceDehomogenize p) =
      ambientInverse ^ n * algebraMap SurfacePoly AmbientOverlap (firstSurfaceDehomogenize p) := by
  have h := dehomogenize_scaling (ambientCoordinate none) (ambientCoordinate (some 0))
    (ambientCoordinate (some 1)) (ambientCoordinate (some 2)) ambientInverse
    ambient_coordinate_mul_inverse p n hp
  rw [ambient_firstEvaluate] at h
  exact h

def ambientJacobian : Matrix (Option (Fin 3)) (Option (Fin 3)) AmbientOverlap :=
  fun j k => ambientPartial k (ambientChangeCoordinate j)

/-- Differentiate the literal scaling before imposing the defining equations.
The final summand is the derivative of the denominator factor. -/
theorem ambient_gradient_change (p : WeightedPoly) (n : ℕ)
    (hp : p.IsWeightedHomogeneous weight n) (i : Option (Fin 3)) :
    (∑ j : Option (Fin 3), ambientChangeEvaluate (pderiv j (secondSurfaceDehomogenize p)) *
      ambientJacobian j i) =
      ambientInverse ^ n *
          algebraMap SurfacePoly AmbientOverlap (pderiv i (firstSurfaceDehomogenize p)) +
        algebraMap SurfacePoly AmbientOverlap (firstSurfaceDehomogenize p) *
          (n • ambientInverse ^ (n - 1) * ambientPartial i ambientInverse) := by
  have h := congrArg (ambientPartial i) (ambient_dehomogenize_scaling p n hp)
  change ambientPartial i (aeval ambientChangeCoordinate (secondSurfaceDehomogenize p)) = _ at h
  rw [derivation_aeval, Derivation.leibniz, ambientPartial_base, Derivation.leibniz_pow] at h
  simpa only [ambientChangeEvaluate, ambientJacobian, smul_eq_mul, nsmul_eq_mul, mul_assoc] using h

private theorem derivative_mul_square {R : Type*} [CommRing R] [Algebra ℂ R]
    (D : Derivation ℂ R R) (z b t : R) (ht : D t = -(t ^ 2) * D b) :
    D (z * t ^ 2) = t ^ 2 * D z - (2 * z * t ^ 3) * D b := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, ht]
  simp only [Nat.reduceSub, pow_one, smul_eq_mul, nsmul_eq_mul]
  ring

private theorem derivative_mul_linear {R : Type*} [CommRing R] [Algebra ℂ R]
    (D : Derivation ℂ R R) (a b t : R) (ht : D t = -(t ^ 2) * D b) :
    D (a * t) = t * D a - (a * t ^ 2) * D b := by
  rw [Derivation.leibniz, ht]
  simp only [smul_eq_mul]
  ring

theorem ambientJacobian_none (j : Option (Fin 3)) :
    ambientJacobian none j = ambientInverse ^ 2 * (if none = j then 1 else 0) -
      (2 * ambientCoordinate none * ambientInverse ^ 3) * (if some 1 = j then 1 else 0) := by
  change ambientPartial j (ambientCoordinate none * ambientInverse ^ 2) = _
  rw [derivative_mul_square (ambientPartial j) _ _ _ (ambientPartial_inverse j),
    ambientPartial_coordinate, ambientPartial_coordinate]

theorem ambientJacobian_some0 (j : Option (Fin 3)) :
    ambientJacobian (some 0) j = ambientInverse * (if some 0 = j then 1 else 0) -
      (ambientCoordinate (some 0) * ambientInverse ^ 2) * (if some 1 = j then 1 else 0) := by
  change ambientPartial j (ambientCoordinate (some 0) * ambientInverse) = _
  rw [derivative_mul_linear (ambientPartial j) _ _ _ (ambientPartial_inverse j),
    ambientPartial_coordinate, ambientPartial_coordinate]

theorem ambientJacobian_some1 (j : Option (Fin 3)) :
    ambientJacobian (some 1) j = -(ambientInverse ^ 2) * (if some 1 = j then 1 else 0) := by
  change ambientPartial j ambientInverse = _
  rw [ambientPartial_inverse, ambientPartial_coordinate]

theorem ambientJacobian_some2 (j : Option (Fin 3)) :
    ambientJacobian (some 2) j = ambientInverse * (if some 2 = j then 1 else 0) -
      (ambientCoordinate (some 2) * ambientInverse ^ 2) * (if some 1 = j then 1 else 0) := by
  change ambientPartial j (ambientCoordinate (some 2) * ambientInverse) = _
  rw [derivative_mul_linear (ambientPartial j) _ _ _ (ambientPartial_inverse j),
    ambientPartial_coordinate, ambientPartial_coordinate]

private theorem coordinateIndex (i : Fin 4) :
    _root_.finSuccEquiv 3 i = (![none, some 0, some 1, some 2] : Fin 4 → Option (Fin 3)) i := by
  fin_cases i <;> rfl

theorem ambientJacobian_fin :
    (fun i j : Fin 4 => ambientJacobian (_root_.finSuccEquiv 3 i) (_root_.finSuccEquiv 3 j)) =
      coordinateJacobian (ambientCoordinate none) (ambientCoordinate (some 0))
        (ambientCoordinate (some 2)) ambientInverse := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coordinateIndex, ambientJacobian_none, ambientJacobian_some0, ambientJacobian_some1,
      ambientJacobian_some2, coordinateJacobian]

/-- This is the determinant of the actual ambient coordinate derivations. -/
theorem ambientJacobian_det : ambientJacobian.det = -ambientInverse ^ 6 := by
  rw [← Matrix.det_reindex_self (_root_.finSuccEquiv 3).symm]
  change Matrix.det (fun i j : Fin 4 => ambientJacobian (_root_.finSuccEquiv 3 i) (_root_.finSuccEquiv 3 j)) = _
  rw [ambientJacobian_fin, coordinateJacobian_det]

#print axioms dehomogenize_scaling
#print axioms coordinateJacobian_det
#print axioms ambient_dehomogenize_scaling
#print axioms ambient_gradient_change
#print axioms ambientJacobian_det

end CycleQ2GeometricSurfaceWeightedChange

end
end SurfaceWeightedChangePart

section SurfaceDeterminantNaturalityPart

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricSurfaceDeterminantNaturality

open Module
open CycleQ2GeometricSurfaceAdjunction
open scoped TensorProduct

section QuotientDeterminant

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
  (b : Basis (Fin 2 ⊕ Fin 2) R M) (g : M →ₗ[R] N)
  (hg : Function.Surjective g)
  (hk : LinearMap.ker g = Submodule.span R (Set.range (fun j => b (Sum.inl j))))

theorem quotientBasis_coord_map (x : M) (i : Fin 2) :
    (quotientBasis b g hg hk).repr (g x) i = b.repr x (Sum.inr i) := by
  have hz (j : Fin 2) : g (b (Sum.inl j)) = 0 := by
    apply LinearMap.mem_ker.mp
    rw [hk]
    exact Submodule.subset_span ⟨j, rfl⟩
  have hm : ((quotientBasis b g hg hk).coord i).comp g = b.coord (Sum.inr i) := by
    apply b.ext
    intro j
    rcases j with j | j
    · simp only [LinearMap.comp_apply, hz, map_zero, Basis.coord_apply, Basis.repr_self,
        Finsupp.single_apply, Sum.inl_ne_inr, ite_false]
    · change (quotientBasis b g hg hk).coord i (g (b (Sum.inr j))) = _
      rw [← quotientBasis_apply b g hg hk]
      simp only [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, Sum.inr.injEq]
  exact LinearMap.congr_fun hm x

/-- The determinant on the quotient is the ambient determinant with its two kernel columns fixed. -/
theorem quotientBasis_determinant_pair (x y : M) :
    determinantEquiv (quotientBasis b g hg hk)
      (exteriorPower.ιMulti R 2 ![g x, g y]) =
      (b.toMatrix (Sum.elim (fun j => b (Sum.inl j)) ![x,y])).det := by
  rw [determinantEquiv_pair, quotientBasis_coord_map, quotientBasis_coord_map,
    quotientBasis_coord_map, quotientBasis_coord_map]
  have hm : b.toMatrix (Sum.elim (fun j => b (Sum.inl j)) ![x,y]) =
      Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) R)
        (fun i j => b.repr (![x,y] j) (Sum.inl i)) 0
        (fun i j => b.repr (![x,y] j) (Sum.inr i)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Basis.toMatrix_apply, Basis.repr_self, Finsupp.single_apply, Matrix.one_apply, eq_comm]
  rw [hm, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

end QuotientDeterminant

def ambientPolynomialFamily (v : Fin 2 → SurfacePoly) (n t p q : SurfacePoly) :
    AmbientIndex → LocalAmbientDifferentials v n t :=
  fun j => (1 : AdjunctionPatch v n t) ⊗ₜ[SurfaceChartRing v] augmentedFamily v p q j

theorem ambientPolynomialFamily_matrix (v : Fin 2 → SurfacePoly) (n t p q : SurfacePoly) :
    (localAmbientBasis v n t).toMatrix (ambientPolynomialFamily v n t p q) =
      ((ambientBasis v).toMatrix (augmentedFamily v p q)).map
        (algebraMap (SurfaceChartRing v) (AdjunctionPatch v n t)) := by
  ext i j
  simp [Basis.toMatrix, localAmbientBasis, ambientPolynomialFamily,
    Basis.baseChange_repr_tmul, Algebra.smul_def]

theorem ambientPolynomialFamily_determinant (v : Fin 2 → SurfacePoly) (n t p q : SurfacePoly) :
    ((localAmbientBasis v n t).toMatrix (ambientPolynomialFamily v n t p q)).det =
      algebraMap (SurfaceChartRing v) (AdjunctionPatch v n t) (augmentedJacobian v p q) := by
  rw [ambientPolynomialFamily_matrix]
  exact (RingHom.map_det _ _).symm

theorem compactAugmentedBasis_determinant (v : Fin 2 → SurfacePoly) (n t : SurfacePoly) :
    ((localAmbientBasis v n t).toMatrix (compactAugmentedBasis v n t)).det =
      algebraMap (SurfaceChartRing v) (AdjunctionPatch v n t) (augmentedJacobian v n t) := by
  have h : (compactAugmentedBasis v n t : AmbientIndex → LocalAmbientDifferentials v n t) =
      ambientPolynomialFamily v n t n t := by
    funext j
    exact compactAugmentedBasis_apply v n t j
  rw [h]
  exact ambientPolynomialFamily_determinant v n t n t

/-- On every actual Jacobian patch, the residue functional evaluates every genuine pair
of polynomial differentials by its actual augmented Jacobian. -/
theorem localSurfaceDeterminantEquiv_pair (v : Fin 2 → SurfacePoly) (n t p q : SurfacePoly) :
    localSurfaceDeterminantEquiv v n t
      (exteriorPower.ιMulti (AdjunctionPatch v n t) 2
        ![KaehlerDifferential.D ℂ (AdjunctionPatch v n t)
            (algebraMap SurfacePoly (AdjunctionPatch v n t) p),
          KaehlerDifferential.D ℂ (AdjunctionPatch v n t)
            (algebraMap SurfacePoly (AdjunctionPatch v n t) q)]) =
      algebraMap (SurfaceChartRing v) (AdjunctionPatch v n t) (augmentedJacobian v p q) := by
  let b := compactAugmentedBasis v n t
  let g := localToKaehler v n t
  let xp : LocalAmbientDifferentials v n t :=
    (1 : AdjunctionPatch v n t) ⊗ₜ[SurfaceChartRing v] ambientDifferential v p
  let xq : LocalAmbientDifferentials v n t :=
    (1 : AdjunctionPatch v n t) ⊗ₜ[SurfaceChartRing v] ambientDifferential v q
  have hp : g xp = KaehlerDifferential.D ℂ (AdjunctionPatch v n t)
      (algebraMap SurfacePoly (AdjunctionPatch v n t) p) := localToKaehler_polynomial v n t p
  have hq : g xq = KaehlerDifferential.D ℂ (AdjunctionPatch v n t)
      (algebraMap SurfacePoly (AdjunctionPatch v n t) q) := localToKaehler_polynomial v n t q
  have hf : Sum.elim (fun j => b (Sum.inl j)) ![xp,xq] =
      ambientPolynomialFamily v n t p q := by
    funext j
    rcases j with j | j
    · simp only [b, Sum.elim_inl, compactAugmentedBasis_apply, localAugmentedFamily,
        ambientPolynomialFamily, augmentedFamily]
    · fin_cases j <;> rfl
  have hc := quotientBasis_determinant_pair b g (localToKaehler_surjective v n t)
    (localToKaehler_kernel_compact v n t) xp xq
  rw [hf] at hc
  change determinantEquiv (localSurfaceKaehlerBasis v n t)
    (exteriorPower.ιMulti (AdjunctionPatch v n t) 2 ![g xp, g xq]) =
      ((compactAugmentedBasis v n t).toMatrix (ambientPolynomialFamily v n t p q)).det at hc
  change ((↑((IsLocalization.Away.algebraMap_isUnit
    (S := AdjunctionPatch v n t) (augmentedJacobian v n t)).unit) : AdjunctionPatch v n t) *
    determinantEquiv (localSurfaceKaehlerBasis v n t)
      (exteriorPower.ιMulti (AdjunctionPatch v n t) 2 ![_,_])) = _
  rw [IsUnit.unit_spec, ← hp, ← hq, hc]
  rw [← compactAugmentedBasis_determinant v n t, ← Matrix.det_mul,
    Basis.toMatrix_mul_toMatrix]
  exact ambientPolynomialFamily_determinant v n t p q

/-- The same normalization holds on all ambient cotangent vectors, including linear
combinations coming from differentiated localized coordinate substitutions. -/
theorem localSurfaceDeterminantEquiv_ambient_pair (v : Fin 2 → SurfacePoly) (n t : SurfacePoly)
    (x y : LocalAmbientDifferentials v n t) :
    localSurfaceDeterminantEquiv v n t
      (exteriorPower.ιMulti (AdjunctionPatch v n t) 2
        ![localToKaehler v n t x, localToKaehler v n t y]) =
      ((localAmbientBasis v n t).toMatrix
        (Sum.elim (fun j => compactAugmentedBasis v n t (Sum.inl j)) ![x,y])).det := by
  have hc := quotientBasis_determinant_pair (compactAugmentedBasis v n t)
    (localToKaehler v n t) (localToKaehler_surjective v n t)
    (localToKaehler_kernel_compact v n t) x y
  change determinantEquiv (localSurfaceKaehlerBasis v n t)
    (exteriorPower.ιMulti (AdjunctionPatch v n t) 2
      ![localToKaehler v n t x, localToKaehler v n t y]) = _ at hc
  change ((↑((IsLocalization.Away.algebraMap_isUnit
    (S := AdjunctionPatch v n t) (augmentedJacobian v n t)).unit) : AdjunctionPatch v n t) *
    determinantEquiv (localSurfaceKaehlerBasis v n t)
      (exteriorPower.ιMulti (AdjunctionPatch v n t) 2 ![_,_])) = _
  rw [IsUnit.unit_spec, hc, ← compactAugmentedBasis_determinant v n t,
    ← Matrix.det_mul, Basis.toMatrix_mul_toMatrix]

#print axioms localSurfaceDeterminantEquiv_pair
#print axioms localSurfaceDeterminantEquiv_ambient_pair

end CycleQ2GeometricSurfaceDeterminantNaturality

end
end SurfaceDeterminantNaturalityPart

section PrincipalChartSectionsPart

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricPrincipalChartSections

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricAffineChartSections CycleQ2GeometricDifferentialChartTransport
open CycleQ2GeometricSurfaceJacobianCharts

variable {X : Scheme.{0}} {U W : X.Opens} {A B : Type} [CommRing A] [CommRing B]
  (e : U.toScheme ≅ Spec (CommRingCat.of A))
  (eW : W.toScheme ≅ Spec (CommRingCat.of B))

private theorem homOfLE_topIso (hWU : W ≤ U) :
    (X.homOfLE hWU).appTop ≫ W.topIso.hom =
      U.topIso.hom ≫ X.presheaf.map (homOfLE hWU).op := by
  simp only [Scheme.homOfLE_appTop, Scheme.Opens.topIso_hom, ← Functor.map_comp]
  exact congrArg X.presheaf.map (Subsingleton.elim _ _)

/-- An actual map of affine charts determines the same map on every
actual ring of sections on a subopen. -/
theorem chartSection_compatible (hWU : W ≤ U) (φ : A →+* B)
    (hc : eW.inv ≫ W.ι = Spec.map (CommRingCat.ofHom φ) ≫ e.inv ≫ U.ι)
    (V : Over W) (a : A) :
    chartSection eW V (φ a) =
      chartSection e (Over.mk (V.hom ≫ homOfLE hWU)) a := by
  have h₁ : eW.inv ≫ X.homOfLE hWU = Spec.map (CommRingCat.ofHom φ) ≫ e.inv := by
    apply (cancel_mono U.ι).mp
    simpa only [Category.assoc, Scheme.homOfLE_ι] using hc
  have h₂ : X.homOfLE hWU ≫ e.hom = eW.hom ≫ Spec.map (CommRingCat.ofHom φ) := by
    have h := congrArg (fun k => eW.hom ≫ k ≫ e.hom) h₁
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] using h
  have happ := congrArg (fun k => k.appTop) h₂
  simp only [Scheme.Hom.comp_appTop] at happ
  have hcat : CommRingCat.ofHom φ ≫ CommRingCat.ofHom (chartSection eW (chartTop W)) =
      CommRingCat.ofHom (chartSection e (chartTop U)) ≫
        X.presheaf.map (homOfLE hWU).op := by
    dsimp only [chartTop]
    rw [chartSection_top, chartSection_top]
    calc
      _ = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
          ((Spec.map (CommRingCat.ofHom φ)).appTop ≫ eW.hom.appTop) ≫ W.topIso.hom := by
        rw [Scheme.ΓSpecIso_inv_naturality_assoc]
        simp only [Category.assoc]
      _ = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
          (e.hom.appTop ≫ (X.homOfLE hWU).appTop) ≫ W.topIso.hom := by rw [← happ]
      _ = _ := by
        simp only [Category.assoc]
        rw [homOfLE_topIso]
  have htop : chartSection eW (chartTop W) (φ a) =
      chartSection e (Over.mk (homOfLE hWU)) a := by
    have hc' := congrArg (fun k => k a) hcat
    have hn := chartSection_naturality e
      (toChartTop (Over.mk (homOfLE hWU))) a
    exact hc'.trans hn
  have hW := chartSection_naturality eW (toChartTop V) (φ a)
  have hU := chartSection_naturality e
    (Over.homMk V.hom (show V.hom ≫ homOfLE hWU = V.hom ≫ homOfLE hWU from rfl) :
      Over.mk (V.hom ≫ homOfLE hWU) ⟶ Over.mk (homOfLE hWU)) a
  calc
    _ = X.presheaf.map V.hom.op (chartSection eW (chartTop W) (φ a)) := hW.symm
    _ = X.presheaf.map V.hom.op (chartSection e (Over.mk (homOfLE hWU)) a) := congrArg _ htop
    _ = _ := hU

variable [Algebra ℂ A]

/-- The genuine principal chart lies inside its original affine chart. -/
theorem principalOpen_le (a : A) : principalOpen e a ≤ U := by
  have h₁ : (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))) ≫
      e.inv ≫ U.ι).opensRange ≤ (e.inv ≫ U.ι).opensRange := by
    rw [Scheme.Hom.opensRange_comp]
    exact (e.inv ≫ U.ι).image_le_opensRange _
  have h₂ : (e.inv ≫ U.ι).opensRange ≤ U := by
    rw [Scheme.Hom.opensRange_comp]
    simpa only [Scheme.Opens.opensRange_ι] using U.ι.image_le_opensRange e.inv.opensRange
  exact h₁.trans h₂

/-- The principal-localization coordinate map is the actual restriction
of the original chart coordinate map on every subopen. -/
theorem principal_chartSection (s : A) (V : Over (principalOpen e s)) (a : A) :
    chartSection (principalChart e s) V (algebraMap A (Localization.Away s) a) =
      chartSection e (Over.mk (V.hom ≫ homOfLE (principalOpen_le e s))) a :=
  chartSection_compatible e (principalChart e s) (principalOpen_le e s)
    (algebraMap A (Localization.Away s)) (principalChart_inv_ι e s) V a

#print axioms chartSection_compatible
#print axioms principal_chartSection

end CycleQ2GeometricPrincipalChartSections
end

end PrincipalChartSectionsPart

section SurfaceResidueTransitionTailPart
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2GeometricSurfaceResidueTransition

open MvPolynomial
open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2ConormalJacobian
open CycleQ2CartierSurfaceGrading CycleQ2GeometricSurfaceAdjunction
open CycleQ2GeometricSurfaceDehomogenizedCharts
open CycleQ2GeometricSurfaceOverlap CycleQ2GeometricSurfaceWeightedChange

/-- The actual polynomial quotient induces the map from the ambient coordinate overlap. -/
def ambientToSurface (r θ : ℂ) : AmbientOverlap →ₐ[ℂ] FirstOverlap r θ :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (X (some (1 : Fin 3)) : SurfacePoly))
    (f := polynomialMap (firstEquations r θ)) (by
      rintro ⟨_, n, rfl⟩
      rw [map_pow]
      exact ((middleUnit (firstEquations r θ)).isUnit).pow n)

theorem ambientToSurface_base (r θ : ℂ) (p : SurfacePoly) :
    ambientToSurface r θ (algebraMap SurfacePoly AmbientOverlap p) =
      polynomialMap (firstEquations r θ) p := by
  change IsLocalization.lift _ (algebraMap SurfacePoly AmbientOverlap p) = _
  rw [IsLocalization.lift_eq]
  rfl

theorem ambientToSurface_coordinate (r θ : ℂ) (j : Option (Fin 3)) :
    ambientToSurface r θ (ambientCoordinate j) = coordinate (firstEquations r θ) j :=
  ambientToSurface_base r θ (X j)

theorem ambientToSurface_inverse (r θ : ℂ) :
    ambientToSurface r θ ambientInverse = inverse (firstEquations r θ) := by
  have h := congrArg (ambientToSurface r θ) ambient_coordinate_mul_inverse
  rw [map_mul, ambientToSurface_coordinate, map_one] at h
  apply ((middleUnit (firstEquations r θ)).isUnit).mul_left_cancel
  change coordinate (firstEquations r θ) (some 1) * ambientToSurface r θ ambientInverse =
    coordinate (firstEquations r θ) (some 1) * inverse (firstEquations r θ)
  rw [coordinate_mul_inverse]
  exact h

/-- The ambient substitution becomes exactly the already proved projective overlap map. -/
theorem ambientToSurface_changeEvaluate (r θ : ℂ) (p : SurfacePoly) :
    ambientToSurface r θ (ambientChangeEvaluate p) =
      overlapEquiv r θ (polynomialMap (secondEquations r θ) p) := by
  have h : (ambientToSurface r θ).comp ambientChangeEvaluate =
      (overlapEquiv r θ).toAlgHom.comp (polynomialMap (secondEquations r θ)) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, ambientChangeEvaluate, aeval_X, AlgEquiv.coe_toAlgHom]
    cases j with
    | none =>
      simp only [ambientChangeCoordinate, map_mul, map_pow,
        ambientToSurface_coordinate, ambientToSurface_inverse]
      exact (overlapEquiv_normalCoordinate r θ).symm
    | some j =>
      fin_cases j <;>
        simp only [ambientChangeCoordinate, Matrix.cons_val_zero', Matrix.cons_val_succ',
          map_mul, ambientToSurface_coordinate, ambientToSurface_inverse]
      · exact (overlapEquiv_coordinate0 r θ).symm
      · exact (overlapEquiv_coordinate1 r θ).symm
      · exact (overlapEquiv_coordinate2 r θ).symm
  exact AlgHom.congr_fun h p

def surfaceJacobian (r θ : ℂ) : Matrix (Option (Fin 3)) (Option (Fin 3)) (FirstOverlap r θ) :=
  ambientJacobian.map (ambientToSurface r θ)

theorem surfaceJacobian_det (r θ : ℂ) :
    (surfaceJacobian r θ).det = -(inverse (firstEquations r θ) ^ 6) := by
  change ((ambientToSurface r θ).toRingHom.mapMatrix ambientJacobian).det = _
  rw [← RingHom.map_det, ambientJacobian_det, map_neg, map_pow]
  exact congrArg (fun z : FirstOverlap r θ => -(z^6)) (ambientToSurface_inverse r θ)

/-- The denominator derivative disappears only after its actual polynomial factor vanishes. -/
theorem surface_gradient_change (r θ : ℂ) (p : WeightedPoly) (n : ℕ)
    (hp : p.IsWeightedHomogeneous weight n)
    (hz : polynomialMap (firstEquations r θ) (firstSurfaceDehomogenize p) = 0)
    (i : Option (Fin 3)) :
    (∑ j : Option (Fin 3),
      overlapEquiv r θ (polynomialMap (secondEquations r θ) (pderiv j (secondSurfaceDehomogenize p))) *
        surfaceJacobian r θ j i) =
      inverse (firstEquations r θ) ^ n *
        polynomialMap (firstEquations r θ) (pderiv i (firstSurfaceDehomogenize p)) := by
  have h := congrArg (ambientToSurface r θ) (ambient_gradient_change p n hp i)
  simp only [map_sum, map_add, map_mul, map_pow, ambientToSurface_changeEvaluate,
    ambientToSurface_base, ambientToSurface_inverse, hz, zero_mul, add_zero] at h
  exact h

theorem polynomialMap_relation (v : Fin 2 → SurfacePoly) (j : Fin 2) :
    polynomialMap v (v j) = 0 := by
  change algebraMap (SurfaceChartRing v) (CoordinateOverlap v)
    (Ideal.Quotient.mk (surfaceChartIdeal v) (v j)) = 0
  have hj : v j ∈ surfaceChartIdeal v := Ideal.subset_span ⟨j, rfl⟩
  have hq : Ideal.Quotient.mk (surfaceChartIdeal v) (v j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hj
  rw [hq, map_zero]

theorem firstEquation_gradient_change (r θ : ℂ) (i : Option (Fin 3)) :
    (∑ j : Option (Fin 3),
      overlapEquiv r θ (polynomialMap (secondEquations r θ) (pderiv j (secondEquations r θ 0))) *
        surfaceJacobian r θ j i) =
      inverse (firstEquations r θ) ^ 6 *
        polynomialMap (firstEquations r θ) (pderiv i (firstEquations r θ 0)) := by
  have hf : firstSurfaceDehomogenize (actualSeedEquation r θ) = firstEquations r θ 0 := by
    simp only [firstEquations, Matrix.cons_val_zero]
    exact firstSurfaceDehomogenize_equation r θ
  have hs : secondSurfaceDehomogenize (actualSeedEquation r θ) = secondEquations r θ 0 := by
    simp only [secondEquations, Matrix.cons_val_zero]
    exact secondSurfaceDehomogenize_equation r θ
  have hz : polynomialMap (firstEquations r θ)
      (firstSurfaceDehomogenize (actualSeedEquation r θ)) = 0 := by
    rw [hf]
    exact polynomialMap_relation (firstEquations r θ) 0
  have h := surface_gradient_change r θ (actualSeedEquation r θ) 6
    (actualSeedEquation_homogeneous r θ) hz i
  rw [hf, hs] at h
  exact h

theorem secondEquation_gradient_change (r θ : ℂ) (i : Option (Fin 3)) :
    (∑ j : Option (Fin 3),
      overlapEquiv r θ (polynomialMap (secondEquations r θ) (pderiv j (secondEquations r θ 1))) *
        surfaceJacobian r θ j i) =
      inverse (firstEquations r θ) ^ 3 *
        polynomialMap (firstEquations r θ) (pderiv i (firstEquations r θ 1)) := by
  have hf : firstSurfaceDehomogenize (thetaH θ) = firstEquations r θ 1 := by
    simp only [firstEquations, Matrix.cons_val_one, Matrix.cons_val_zero]
    exact firstSurfaceDehomogenize_h θ
  have hs : secondSurfaceDehomogenize (thetaH θ) = secondEquations r θ 1 := by
    simp only [secondEquations, Matrix.cons_val_one, Matrix.cons_val_zero]
    exact secondSurfaceDehomogenize_h θ
  have hz : polynomialMap (firstEquations r θ) (firstSurfaceDehomogenize (thetaH θ)) = 0 := by
    rw [hf]
    exact polynomialMap_relation (firstEquations r θ) 1
  have h := surface_gradient_change r θ (thetaH θ) 3 (thetaH_homogeneous θ) hz i
  rw [hf, hs] at h
  exact h

#print axioms surfaceJacobian_det
#print axioms firstEquation_gradient_change
#print axioms secondEquation_gradient_change

end CycleQ2GeometricSurfaceResidueTransition

end
end SurfaceResidueTransitionTailPart

section SurfaceJacobianDeterminantTailPart
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2GeometricSurfaceResidueTransition

open MvPolynomial
open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2ConormalJacobian
open CycleQ2CartierSurfaceGrading CycleQ2GeometricSurfaceAdjunction
open CycleQ2GeometricSurfaceDehomogenizedCharts
open CycleQ2GeometricSurfaceOverlap CycleQ2GeometricSurfaceWeightedChange

def secondGradientMatrix (r θ : ℂ) (p q : SurfacePoly) : Matrix (Fin 4) (Fin 4) (FirstOverlap r θ) :=
  fun i j => overlapEquiv r θ
    (polynomialMap (secondEquations r θ)
      (pderiv (_root_.finSuccEquiv 3 j) (augmentedPolynomialRows (secondEquations r θ) p q i)))

theorem secondGradientMatrix_det (r θ : ℂ) (p q : SurfacePoly) :
    (secondGradientMatrix r θ p q).det =
      overlapEquiv r θ
        (algebraMap (SurfaceChartRing (secondEquations r θ)) (SecondOverlap r θ)
          (augmentedJacobian (secondEquations r θ) p q)) := by
  symm
  rw [augmentedJacobian_polynomial]
  change (overlapEquiv r θ).toRingHom
    ((algebraMap (SurfaceChartRing (secondEquations r θ)) (SecondOverlap r θ))
      (Matrix.det _)) = _
  rw [RingHom.map_det, RingHom.map_det]
  rfl

def surfaceJacobianFin (r θ : ℂ) : Matrix (Fin 4) (Fin 4) (FirstOverlap r θ) :=
  fun i j => surfaceJacobian r θ (_root_.finSuccEquiv 3 i) (_root_.finSuccEquiv 3 j)

theorem surfaceJacobianFin_det (r θ : ℂ) :
    (surfaceJacobianFin r θ).det = -(inverse (firstEquations r θ) ^ 6) := by
  change (Matrix.reindex (_root_.finSuccEquiv 3).symm (_root_.finSuccEquiv 3).symm
    (surfaceJacobian r θ)).det = _
  rw [Matrix.det_reindex_self, surfaceJacobian_det]

def pulledGradient (r θ : ℂ) (p : SurfacePoly) (j : Fin 4) : FirstOverlap r θ :=
  ∑ k : Fin 4,
    overlapEquiv r θ (polynomialMap (secondEquations r θ) (pderiv (_root_.finSuccEquiv 3 k) p)) *
      surfaceJacobianFin r θ k j

theorem pulledGradient_firstEquation (r θ : ℂ) (j : Fin 4) :
    pulledGradient r θ (secondEquations r θ 0) j =
      inverse (firstEquations r θ) ^ 6 *
        polynomialMap (firstEquations r θ) (pderiv (_root_.finSuccEquiv 3 j) (firstEquations r θ 0)) := by
  change (∑ k : Fin 4,
    (fun k : Option (Fin 3) =>
      overlapEquiv r θ (polynomialMap (secondEquations r θ) (pderiv k (secondEquations r θ 0))) *
        surfaceJacobian r θ k (_root_.finSuccEquiv 3 j)) (_root_.finSuccEquiv 3 k)) = _
  exact (Equiv.sum_comp (_root_.finSuccEquiv 3) _).trans
    (firstEquation_gradient_change r θ (_root_.finSuccEquiv 3 j))

theorem pulledGradient_secondEquation (r θ : ℂ) (j : Fin 4) :
    pulledGradient r θ (secondEquations r θ 1) j =
      inverse (firstEquations r θ) ^ 3 *
        polynomialMap (firstEquations r θ) (pderiv (_root_.finSuccEquiv 3 j) (firstEquations r θ 1)) := by
  change (∑ k : Fin 4,
    (fun k : Option (Fin 3) =>
      overlapEquiv r θ (polynomialMap (secondEquations r θ) (pderiv k (secondEquations r θ 1))) *
        surfaceJacobian r θ k (_root_.finSuccEquiv 3 j)) (_root_.finSuccEquiv 3 k)) = _
  exact (Equiv.sum_comp (_root_.finSuccEquiv 3) _).trans
    (secondEquation_gradient_change r θ (_root_.finSuccEquiv 3 j))

def mixedGradientMatrix (r θ : ℂ) (p q : SurfacePoly) : Matrix (Fin 4) (Fin 4) (FirstOverlap r θ) :=
  ![(fun j => polynomialMap (firstEquations r θ)
        (pderiv (_root_.finSuccEquiv 3 j) (firstEquations r θ 0))),
    (fun j => polynomialMap (firstEquations r θ)
        (pderiv (_root_.finSuccEquiv 3 j) (firstEquations r θ 1))),
    pulledGradient r θ p, pulledGradient r θ q]

theorem gradientMatrix_mul (r θ : ℂ) (p q : SurfacePoly) :
    secondGradientMatrix r θ p q * surfaceJacobianFin r θ =
      Matrix.diagonal ![inverse (firstEquations r θ)^6, inverse (firstEquations r θ)^3, 1, 1] *
        mixedGradientMatrix r θ p q := by
  ext i j
  rw [Matrix.diagonal_mul]
  simp only [Matrix.mul_apply, secondGradientMatrix,
    augmentedPolynomialRows, mixedGradientMatrix]
  fin_cases i <;> simp only [Matrix.cons_val_zero', Matrix.cons_val_succ']
  · exact pulledGradient_firstEquation r θ j
  · exact pulledGradient_secondEquation r θ j
  · simp only [one_mul]
    rfl
  · simp only [one_mul]
    rfl

private theorem weightedDiagonal_det {R : Type*} [CommRing R] (t : R) :
    (Matrix.diagonal (![t^6,t^3,1,1] : Fin 4 → R)).det = t^9 := by
  simp [Matrix.det_diagonal, Fin.prod_univ_succ]
  ring

theorem actualJacobian_determinant_balance (r θ : ℂ) (p q : SurfacePoly) :
    overlapEquiv r θ
        (algebraMap (SurfaceChartRing (secondEquations r θ)) (SecondOverlap r θ)
          (augmentedJacobian (secondEquations r θ) p q)) *
        -(inverse (firstEquations r θ)^6) =
      inverse (firstEquations r θ)^9 * (mixedGradientMatrix r θ p q).det := by
  have h := congrArg Matrix.det (gradientMatrix_mul r θ p q)
  rw [Matrix.det_mul, secondGradientMatrix_det, surfaceJacobianFin_det,
    Matrix.det_mul, weightedDiagonal_det] at h
  exact h

private theorem cancel_weighted_determinant {R : Type*} [CommRing R]
    (a d b t : R) (ht : b * t = 1) (h : a * -(t^6) = t^9 * d) :
    d = -(b^3) * a := by
  have hu : IsUnit t := isUnit_iff_exists_inv.mpr ⟨b, by rw [mul_comm]; exact ht⟩
  apply (hu.pow 9).mul_left_cancel
  have h3 : b^3 * t^3 = 1 := by rw [← mul_pow, ht, one_pow]
  calc
    t^9 * d = a * -(t^6) := h.symm
    _ = -(a * t^6 * (b^3 * t^3)) := by rw [h3, mul_one]; ring
    _ = t^9 * (-(b^3) * a) := by ring

/-- The sign and cubic factor are derived from the literal ambient and conormal Jacobians. -/
theorem mixedJacobian_transition (r θ : ℂ) (p q : SurfacePoly) :
    (mixedGradientMatrix r θ p q).det =
      -(coordinate (firstEquations r θ) (some 1)^3) *
        overlapEquiv r θ
          (algebraMap (SurfaceChartRing (secondEquations r θ)) (SecondOverlap r θ)
            (augmentedJacobian (secondEquations r θ) p q)) :=
  cancel_weighted_determinant _ _ _ _ (coordinate_mul_inverse (firstEquations r θ))
    (actualJacobian_determinant_balance r θ p q)

private theorem cubic_weight_balance {R : Type*} [CommRing R]
    (a b t : R) (ht : b * t = 1) : (a * t^3) * -(b^3) = -a := by
  have h3 : b^3 * t^3 = 1 := by rw [← mul_pow, ht, one_pow]
  calc
    (a * t^3) * -(b^3) = -a * (b^3 * t^3) := by ring
    _ = -a := by rw [h3, mul_one]

/-- A fixed homogeneous cubic cancels the weight but retains the raw residue minus sign.
The projective coordinate orientation is therefore necessary for descent. -/
theorem rawCubic_transition_scalar (r θ : ℂ) (p : WeightedPoly)
    (hp : p.IsWeightedHomogeneous weight 3) :
    overlapEquiv r θ (polynomialMap (secondEquations r θ) (secondSurfaceDehomogenize p)) *
        -(coordinate (firstEquations r θ) (some 1)^3) =
      -polynomialMap (firstEquations r θ) (firstSurfaceDehomogenize p) := by
  rw [overlapEquiv_dehomogenize r θ 3 p hp]
  exact cubic_weight_balance _ _ _ (coordinate_mul_inverse (firstEquations r θ))

#print axioms mixedJacobian_transition
#print axioms rawCubic_transition_scalar

end CycleQ2GeometricSurfaceResidueTransition

end
end SurfaceJacobianDeterminantTailPart

section SurfaceChartSectionBindingTailPart
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2GeometricSurfaceOverlap

open CategoryTheory Opposite AlgebraicGeometry
open CycleQ2GeometricAffineChartSections CycleQ2GeometricDifferentialChartTransport
open CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2GeometricSurfaceAdjunction
open CycleQ2CartierSurfaceGrading CycleQ2CartierProjectiveCover

private theorem basicOpen_sectionMap (r θ : ℂ) (j : Fin 4)
    {B : Type} [CommRing B] (q : CoordinateRing r θ j ≃+* B) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
        (Proj.basicOpenToSpec (surfaceGrade r θ) (coordinateDen r θ j) ≫
          Spec.map (CommRingCat.ofHom q.symm.toRingHom)).appTop ≫
        (Proj.basicOpen (surfaceGrade r θ) (coordinateDen r θ j)).topIso.hom =
      CommRingCat.ofHom q.symm.toRingHom ≫
        (Proj.basicOpenIsoAway (surfaceGrade r θ) (coordinateDen r θ j)
          (coordinate_mem_grade r θ j) (by decide)).hom := by
  rw [Scheme.Hom.comp_appTop, Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality_assoc]
  dsimp only [Scheme.Hom.appTop]
  rw [Proj.basicOpenToSpec_app_top]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id,
    Proj.basicOpenIsoAway_hom]

theorem first_chartSection_top (r θ : ℂ) :
    chartSection (firstAffineChart r θ) (Over.mk (𝟙 (coordinatePatch r θ 1))) =
      (firstSectionsEquiv r θ).symm.toRingHom := by
  have hcat : CommRingCat.ofHom (chartSection (firstAffineChart r θ)
        (Over.mk (𝟙 (coordinatePatch r θ 1)))) =
      CommRingCat.ofHom (firstSectionsEquiv r θ).symm.toRingHom := by
    rw [chartSection_top]
    exact basicOpen_sectionMap r θ 1 (firstChartEquiv r θ)
  exact congrArg CommRingCat.Hom.hom hcat

theorem second_chartSection_top (r θ : ℂ) :
    chartSection (secondAffineChart r θ) (Over.mk (𝟙 (coordinatePatch r θ 2))) =
      (secondSectionsEquiv r θ).symm.toRingHom := by
  have hcat : CommRingCat.ofHom (chartSection (secondAffineChart r θ)
        (Over.mk (𝟙 (coordinatePatch r θ 2)))) =
      CommRingCat.ofHom (secondSectionsEquiv r θ).symm.toRingHom := by
    rw [chartSection_top]
    exact basicOpen_sectionMap r θ 2 (secondChartEquiv r θ)
  exact congrArg CommRingCat.Hom.hom hcat

theorem first_chartSection_subopen (r θ : ℂ) (V : Over (coordinatePatch r θ 1))
    (a : SurfaceChartRing (firstEquations r θ)) :
    chartSection (firstAffineChart r θ) V a =
      (projectiveSurface r θ).presheaf.map V.hom.op ((firstSectionsEquiv r θ).symm a) := by
  calc
    _ = (projectiveSurface r θ).presheaf.map V.hom.op
        (chartSection (firstAffineChart r θ) (chartTop (coordinatePatch r θ 1)) a) :=
      (chartSection_naturality (firstAffineChart r θ) (toChartTop V) a).symm
    _ = _ := by
      rw [show chartSection (firstAffineChart r θ) (chartTop (coordinatePatch r θ 1)) =
        (firstSectionsEquiv r θ).symm.toRingHom from first_chartSection_top r θ]
      rfl

theorem second_chartSection_subopen (r θ : ℂ) (V : Over (coordinatePatch r θ 2))
    (a : SurfaceChartRing (secondEquations r θ)) :
    chartSection (secondAffineChart r θ) V a =
      (projectiveSurface r θ).presheaf.map V.hom.op ((secondSectionsEquiv r θ).symm a) := by
  calc
    _ = (projectiveSurface r θ).presheaf.map V.hom.op
        (chartSection (secondAffineChart r θ) (chartTop (coordinatePatch r θ 2)) a) :=
      (chartSection_naturality (secondAffineChart r θ) (toChartTop V) a).symm
    _ = _ := by
      rw [show chartSection (secondAffineChart r θ) (chartTop (coordinatePatch r θ 2)) =
        (secondSectionsEquiv r θ).symm.toRingHom from second_chartSection_top r θ]
      rfl

/-- Evaluation of the literal overlap ring in actual sections on an actual subopen. -/
def overlapSectionMap (r θ : ℂ) (V : (projectiveSurface r θ).Opens) (hV : V ≤ overlapPatch r θ) :
    FirstOverlap r θ →+* Γ(projectiveSurface r θ, V) :=
  ((projectiveSurface r θ).presheaf.map (homOfLE hV).op).hom.comp
    (firstOverlapSectionsEquiv r θ).symm.toRingHom

theorem overlapSectionMap_first (r θ : ℂ) (V : (projectiveSurface r θ).Opens)
    (hV : V ≤ overlapPatch r θ) (a : SurfaceChartRing (firstEquations r θ)) :
    overlapSectionMap r θ V hV
        (algebraMap (SurfaceChartRing (firstEquations r θ)) (FirstOverlap r θ) a) =
      chartSection (firstAffineChart r θ) (Over.mk (homOfLE (hV.trans (overlap_le_first r θ)))) a := by
  have h := firstOverlapSectionsEquiv_restriction r θ ((firstSectionsEquiv r θ).symm a)
  rw [RingEquiv.apply_symm_apply] at h
  have h' := congrArg (firstOverlapSectionsEquiv r θ).symm h
  rw [RingEquiv.symm_apply_apply] at h'
  rw [first_chartSection_subopen]
  change (projectiveSurface r θ).presheaf.map (homOfLE hV).op
      ((firstOverlapSectionsEquiv r θ).symm _) = _
  rw [← h']
  change ((projectiveSurface r θ).presheaf.map (homOfLE (overlap_le_first r θ)).op ≫
    (projectiveSurface r θ).presheaf.map (homOfLE hV).op) ((firstSectionsEquiv r θ).symm a) = _
  rw [← (projectiveSurface r θ).presheaf.map_comp]
  rfl

theorem overlapSectionMap_second (r θ : ℂ) (V : (projectiveSurface r θ).Opens)
    (hV : V ≤ overlapPatch r θ) (a : SurfaceChartRing (secondEquations r θ)) :
    overlapSectionMap r θ V hV
        (overlapEquiv r θ (algebraMap (SurfaceChartRing (secondEquations r θ)) (SecondOverlap r θ) a)) =
      chartSection (secondAffineChart r θ) (Over.mk (homOfLE (hV.trans (overlap_le_second r θ)))) a := by
  have h := secondOverlapSectionsEquiv_restriction r θ ((secondSectionsEquiv r θ).symm a)
  rw [RingEquiv.apply_symm_apply] at h
  have h' := congrArg (fun x => (firstOverlapSectionsEquiv r θ).symm (overlapEquiv r θ x)) h
  rw [← overlapSectionsEquiv_compatibility, RingEquiv.symm_apply_apply] at h'
  rw [second_chartSection_subopen]
  change (projectiveSurface r θ).presheaf.map (homOfLE hV).op
      ((firstOverlapSectionsEquiv r θ).symm _) = _
  rw [← h']
  change ((projectiveSurface r θ).presheaf.map (homOfLE (overlap_le_second r θ)).op ≫
    (projectiveSurface r θ).presheaf.map (homOfLE hV).op) ((secondSectionsEquiv r θ).symm a) = _
  rw [← (projectiveSurface r θ).presheaf.map_comp]
  rfl

#print axioms first_chartSection_top
#print axioms overlapSectionMap_second

end CycleQ2GeometricSurfaceOverlap

end
end SurfaceChartSectionBindingTailPart

section PrincipalChartSectionSpecializationsPart
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2GeometricSurfaceOverlap

open CategoryTheory Opposite AlgebraicGeometry
open CycleQ2GeometricAffineChartSections CycleQ2GeometricSurfaceJacobianCharts
open CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2GeometricSurfaceAdjunction
open CycleQ2GeometricPrincipalChartSections CycleQ2CartierProjectiveCover

/-- The first actual Jacobian chart is contained in its coordinate chart. -/
theorem firstNormalOpen_le (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    firstNormalOpen r θ i j ≤ coordinatePatch r θ 1 :=
  principalOpen_le (firstAffineChart r θ) (firstJacobian r θ i j)

/-- The second actual Jacobian chart is contained in its coordinate chart. -/
theorem secondNormalOpen_le (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    secondNormalOpen r θ i j ≤ coordinatePatch r θ 2 :=
  principalOpen_le (secondAffineChart r θ) (secondJacobian r θ i j)

/-- First Jacobian localization and first projective coordinate map agree
on their actual section values on every subopen. -/
theorem firstNormal_chartSection (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : Over (firstNormalOpen r θ i j)) (a : SurfaceChartRing (firstEquations r θ)) :
    chartSection (firstNormalChart r θ i j) V
        (algebraMap (SurfaceChartRing (firstEquations r θ))
          (Localization.Away (firstJacobian r θ i j)) a) =
      chartSection (firstAffineChart r θ)
        (Over.mk (V.hom ≫ homOfLE (firstNormalOpen_le r θ i j))) a :=
  principal_chartSection (firstAffineChart r θ) (firstJacobian r θ i j) V a

/-- Second Jacobian localization and second projective coordinate map agree
on their actual section values on every subopen. -/
theorem secondNormal_chartSection (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : Over (secondNormalOpen r θ i j)) (a : SurfaceChartRing (secondEquations r θ)) :
    chartSection (secondNormalChart r θ i j) V
        (algebraMap (SurfaceChartRing (secondEquations r θ))
          (Localization.Away (secondJacobian r θ i j)) a) =
      chartSection (secondAffineChart r θ)
        (Over.mk (V.hom ≫ homOfLE (secondNormalOpen_le r θ i j))) a :=
  principal_chartSection (secondAffineChart r θ) (secondJacobian r θ i j) V a

#print axioms firstNormal_chartSection
#print axioms secondNormal_chartSection

end CycleQ2GeometricSurfaceOverlap

end
end PrincipalChartSectionSpecializationsPart
