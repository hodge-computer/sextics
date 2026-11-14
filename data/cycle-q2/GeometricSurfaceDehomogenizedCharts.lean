import Proposal.GeometricCartierCechNonboundary
import Proposal.GeometricSurfaceAdjunction

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2GeometricSurfaceDehomogenizedCharts

open MvPolynomial
open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2ConormalJacobian
open CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
open CycleQ2CartierSurfaceGrading CycleQ2GeometricSurfaceAdjunction

@[simp] theorem weight_castSucc (i : Fin 4) : weight i.castSucc = 1 := by
  fin_cases i <;> rfl

@[simp] theorem weight_last : weight (Fin.last 4) = 2 := rfl

/-- The weight-one coordinates after setting Xi = 1. -/
def linearCoordinate (i : Fin 4) : Fin 4 → SurfacePoly :=
  Fin.insertNth i 1 (fun j : Fin 3 => X (some j))

@[simp] theorem linearCoordinate_self (i : Fin 4) : linearCoordinate i i = 1 := by
  simp [linearCoordinate]

@[simp] theorem linearCoordinate_succAbove (i : Fin 4) (j : Fin 3) :
    linearCoordinate i (i.succAbove j) = X (some j) := by
  simp [linearCoordinate]

/-- The fourth affine variable is the genuine normal equation z = f₂/Xi². -/
def dehomogenize (i : Fin 4) : WeightedPoly →ₐ[ℂ] SurfacePoly :=
  aeval (Fin.lastCases (X none - linearCoordinate i 2 ^ 2) (linearCoordinate i))

@[simp] theorem dehomogenize_castSucc (i j : Fin 4) :
    dehomogenize i (X j.castSucc) = linearCoordinate i j := by
  simp [dehomogenize]

@[simp] theorem dehomogenize_last (i : Fin 4) :
    dehomogenize i (X (Fin.last 4)) = X none - linearCoordinate i 2 ^ 2 := by
  simp only [dehomogenize, aeval_X, Fin.lastCases_last]

@[simp] theorem dehomogenize_self (i : Fin 4) : dehomogenize i (X i.castSucc) = 1 := by
  simp

@[simp] theorem dehomogenize_succAbove (i : Fin 4) (j : Fin 3) :
    dehomogenize i (X (i.succAbove j).castSucc) = X (some j) := by
  simp

@[simp] theorem dehomogenize_f2 (i : Fin 4) : dehomogenize i originalF2 = X none := by
  change dehomogenize i (X (Fin.last 4) + X (2 : Fin 4).castSucc ^ 2) = _
  rw [map_add, map_pow, dehomogenize_last, dehomogenize_castSucc, sub_add_cancel]

def dehomogenizedEquations (r θ : ℂ) (i : Fin 4) : Fin 2 → SurfacePoly :=
  ![dehomogenize i (actualSeedEquation r θ), dehomogenize i (thetaH θ)]

abbrev DehomogenizedRing (r θ : ℂ) (i : Fin 4) :=
  SurfaceChartRing (dehomogenizedEquations r θ i)

abbrev CoordinateRing (r θ : ℂ) (i : Fin 4) :=
  HomogeneousLocalization.Away (surfaceGrade r θ) (surfaceQuotient r θ (X i.castSucc))

abbrev CoordinateLocalization (r θ : ℂ) (i : Fin 4) :=
  Localization.Away (surfaceQuotient r θ (X i.castSucc))

def dehomogenizedMap (r θ : ℂ) (i : Fin 4) :
    SurfacePoly →+* DehomogenizedRing r θ i :=
  Ideal.Quotient.mk (surfaceChartIdeal (dehomogenizedEquations r θ i))

theorem dehomogenizedMap_equation (r θ : ℂ) (i : Fin 4) (j : Fin 2) :
    dehomogenizedMap r θ i (dehomogenizedEquations r θ i j) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)

theorem surfaceIdeal_le_dehomogenization_kernel (r θ : ℂ) (i : Fin 4) :
    surfaceIdeal r θ ≤
      RingHom.ker ((dehomogenizedMap r θ i).comp (dehomogenize i).toRingHom) := by
  apply Ideal.span_le.mpr
  rintro p ⟨j, rfl⟩
  fin_cases j
  · exact dehomogenizedMap_equation r θ i 0
  · exact dehomogenizedMap_equation r θ i 1

def surfaceToDehomogenized (r θ : ℂ) (i : Fin 4) :
    SurfaceRing r θ →+* DehomogenizedRing r θ i :=
  Ideal.Quotient.lift (surfaceIdeal r θ)
    ((dehomogenizedMap r θ i).comp (dehomogenize i).toRingHom)
    (fun _ hp => surfaceIdeal_le_dehomogenization_kernel r θ i hp)

@[simp] theorem surfaceToDehomogenized_surfaceQuotient (r θ : ℂ) (i : Fin 4)
    (p : WeightedPoly) :
    surfaceToDehomogenized r θ i (surfaceQuotient r θ p) =
      dehomogenizedMap r θ i (dehomogenize i p) := rfl

@[simp] theorem surfaceToDehomogenized_self (r θ : ℂ) (i : Fin 4) :
    surfaceToDehomogenized r θ i (surfaceQuotient r θ (X i.castSucc)) = 1 := by simp

def localizationToDehomogenized (r θ : ℂ) (i : Fin 4) :
    CoordinateLocalization r θ i →+* DehomogenizedRing r θ i :=
  Localization.awayLift (surfaceToDehomogenized r θ i) (surfaceQuotient r θ (X i.castSucc))
    (isUnit_iff_exists_inv.mpr ⟨1, by simp⟩)

def toDehomogenized (r θ : ℂ) (i : Fin 4) :
    CoordinateRing r θ i →+* DehomogenizedRing r θ i :=
  (localizationToDehomogenized r θ i).comp
    (algebraMap (CoordinateRing r θ i) (CoordinateLocalization r θ i))

theorem coordinate_mem_grade (r θ : ℂ) (i : Fin 4) :
    surfaceQuotient r θ (X i.castSucc) ∈ surfaceGrade r θ 1 := by
  apply surfaceQuotient_mem_grade
  change (X i.castSucc : WeightedPoly).IsWeightedHomogeneous weight 1
  simpa only [weight_castSucc] using isWeightedHomogeneous_X ℂ weight i.castSucc

def homogeneousFraction (r θ : ℂ) (i : Fin 4) (n : ℕ) (p : WeightedPoly)
    (hp : p.IsWeightedHomogeneous weight n) : CoordinateRing r θ i :=
  HomogeneousLocalization.Away.mk (surfaceGrade r θ) (coordinate_mem_grade r θ i)
    n (surfaceQuotient r θ p) (by simpa using surfaceQuotient_mem_grade r θ hp)

theorem homogeneousFraction_val (r θ : ℂ) (i : Fin 4) (n : ℕ) (p : WeightedPoly)
    (hp : p.IsWeightedHomogeneous weight n) :
    (homogeneousFraction r θ i n p hp).val =
      algebraMap (SurfaceRing r θ) (CoordinateLocalization r θ i) (surfaceQuotient r θ p) *
        IsLocalization.Away.invSelf (surfaceQuotient r θ (X i.castSucc)) ^ n := by
  rw [homogeneousFraction, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
  simp only [map_pow]
  rw [mul_assoc, mul_comm (IsLocalization.Away.invSelf (surfaceQuotient r θ (X i.castSucc)) ^ n),
    ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]

@[simp] theorem toDehomogenized_homogeneousFraction (r θ : ℂ) (i : Fin 4)
    (n : ℕ) (p : WeightedPoly) (hp : p.IsWeightedHomogeneous weight n) :
    toDehomogenized r θ i (homogeneousFraction r θ i n p hp) =
      dehomogenizedMap r θ i (dehomogenize i p) := by
  change localizationToDehomogenized r θ i
    (Localization.mk (surfaceQuotient r θ p)
      ⟨surfaceQuotient r θ (X i.castSucc) ^ n, n, rfl⟩) = _
  simpa only [localizationToDehomogenized, one_pow, mul_one,
    surfaceToDehomogenized_surfaceQuotient] using
      (Localization.awayLift_mk (surfaceToDehomogenized r θ i)
        (surfaceQuotient r θ (X i.castSucc)) (surfaceQuotient r θ p) 1 (by simp) n)

def constants (r θ : ℂ) (i : Fin 4) : ℂ →+* CoordinateRing r θ i where
  toFun c := homogeneousFraction r θ i 0 (C c) (isWeightedHomogeneous_C weight c)
  map_zero' := by
    apply HomogeneousLocalization.val_injective
    simp only [homogeneousFraction_val, map_zero, pow_zero, zero_mul,
      HomogeneousLocalization.val_zero]
  map_one' := by
    apply HomogeneousLocalization.val_injective
    simp only [homogeneousFraction_val, map_one, pow_zero, one_mul,
      HomogeneousLocalization.val_one]
  map_add' c d := by
    apply HomogeneousLocalization.val_injective
    simp only [homogeneousFraction_val, map_add, pow_zero, mul_one,
      HomogeneousLocalization.val_add]
  map_mul' c d := by
    apply HomogeneousLocalization.val_injective
    simp only [homogeneousFraction_val, map_mul, pow_zero, mul_one,
      HomogeneousLocalization.val_mul]

@[simp] theorem constants_val (r θ : ℂ) (i : Fin 4) (c : ℂ) :
    (constants r θ i c).val =
      algebraMap (SurfaceRing r θ) (CoordinateLocalization r θ i) (surfaceQuotient r θ (C c)) := by
  change (homogeneousFraction r θ i 0 (C c) (isWeightedHomogeneous_C weight c)).val = _
  simp only [homogeneousFraction_val, pow_zero, mul_one]

def coordinateRatio (r θ : ℂ) (i : Fin 4) (j : Fin 5) : CoordinateRing r θ i :=
  homogeneousFraction r θ i (weight j) (X j) (isWeightedHomogeneous_X ℂ weight j)

@[simp] theorem coordinateRatio_val (r θ : ℂ) (i : Fin 4) (j : Fin 5) :
    (coordinateRatio r θ i j).val =
      algebraMap (SurfaceRing r θ) (CoordinateLocalization r θ i) (surfaceQuotient r θ (X j)) *
        IsLocalization.Away.invSelf (surfaceQuotient r θ (X i.castSucc)) ^ weight j :=
  homogeneousFraction_val r θ i (weight j) (X j) (isWeightedHomogeneous_X ℂ weight j)

@[simp] theorem coordinateRatio_self (r θ : ℂ) (i : Fin 4) :
    coordinateRatio r θ i i.castSucc = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [coordinateRatio_val, weight_castSucc, pow_one,
    IsLocalization.Away.mul_invSelf, HomogeneousLocalization.val_one]

theorem weighted_homogeneous_eval_scale {S : Type*} [CommRing S] (f : ℂ →+* S)
    (x : Fin 5 → S) (c : S) (p : WeightedPoly) (n : ℕ)
    (hp : p.IsWeightedHomogeneous weight n) :
    eval₂Hom f (fun j => c ^ weight j * x j) p = c ^ n * eval₂Hom f x p := by
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => simp only [map_add, ihp, ihq, mul_add]
  | monomial d a hd =>
      have hdegree : (∑ j ∈ d.support, weight j * d j) = n := by
        simpa [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, Nat.mul_comm] using hd
      simp only [eval₂Hom_monomial, Finsupp.prod, mul_pow, ← pow_mul,
        Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdegree]
      ring

@[simp] theorem toDehomogenized_constants (r θ : ℂ) (i : Fin 4) (c : ℂ) :
    toDehomogenized r θ i (constants r θ i c) = dehomogenizedMap r θ i (C c) := by
  change toDehomogenized r θ i
    (homogeneousFraction r θ i 0 (C c) (isWeightedHomogeneous_C weight c)) = _
  rw [toDehomogenized_homogeneousFraction]
  simp [dehomogenize]

@[simp] theorem toDehomogenized_coordinateRatio (r θ : ℂ) (i : Fin 4) (j : Fin 5) :
    toDehomogenized r θ i (coordinateRatio r θ i j) =
      dehomogenizedMap r θ i (dehomogenize i (X j)) :=
  toDehomogenized_homogeneousFraction r θ i (weight j) (X j)
    (isWeightedHomogeneous_X ℂ weight j)

/-- Evaluate the shifted normal variable at the literal f₂/Xi². -/
def affineEvaluate (r θ : ℂ) (i : Fin 4) : SurfacePoly →+* CoordinateRing r θ i :=
  eval₂Hom (constants r θ i) (fun j => match j with
    | none => coordinateRatio r θ i (Fin.last 4) + coordinateRatio r θ i (2 : Fin 4).castSucc ^ 2
    | some j => coordinateRatio r θ i (i.succAbove j).castSucc)

def projectiveEvaluate (r θ : ℂ) (i : Fin 4) : WeightedPoly →+* CoordinateRing r θ i :=
  eval₂Hom (constants r θ i) (coordinateRatio r θ i)

@[simp] theorem affineEvaluate_linearCoordinate (r θ : ℂ) (i j : Fin 4) :
    affineEvaluate r θ i (linearCoordinate i j) = coordinateRatio r θ i j.castSucc := by
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · simp
  · simp [affineEvaluate]

theorem affineEvaluate_comp_dehomogenize (r θ : ℂ) (i : Fin 4) :
    (affineEvaluate r θ i).comp (dehomogenize i).toRingHom = projectiveEvaluate r θ i := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [affineEvaluate, projectiveEvaluate, dehomogenize]
  · intro j
    induction j using Fin.lastCases with
    | last =>
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
      rw [dehomogenize_last, map_sub, map_pow, affineEvaluate_linearCoordinate]
      simp only [affineEvaluate, projectiveEvaluate, eval₂Hom_X', add_sub_cancel_right]
    | cast j => simp [projectiveEvaluate]

@[simp] theorem affineEvaluate_dehomogenize (r θ : ℂ) (i : Fin 4) (p : WeightedPoly) :
    affineEvaluate r θ i (dehomogenize i p) = projectiveEvaluate r θ i p :=
  RingHom.congr_fun (affineEvaluate_comp_dehomogenize r θ i) p

theorem projectiveEvaluate_homogeneousFraction (r θ : ℂ) (i : Fin 4)
    (n : ℕ) (p : WeightedPoly) (hp : p.IsWeightedHomogeneous weight n) :
    projectiveEvaluate r θ i p = homogeneousFraction r θ i n p hp := by
  let F : WeightedPoly →+* CoordinateLocalization r θ i :=
    (algebraMap (SurfaceRing r θ) (CoordinateLocalization r θ i)).comp (surfaceQuotient r θ)
  have heval : eval₂Hom (F.comp C) (fun j => F (X j)) = F := by
    apply MvPolynomial.ringHom_ext <;> intro x <;> simp
  have hcomp :
      (algebraMap (CoordinateRing r θ i) (CoordinateLocalization r θ i)).comp
          (projectiveEvaluate r θ i) =
        eval₂Hom (F.comp C) (fun j =>
          IsLocalization.Away.invSelf (surfaceQuotient r θ (X i.castSucc)) ^ weight j * F (X j)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, projectiveEvaluate, eval₂Hom_C,
        HomogeneousLocalization.algebraMap_apply, constants_val]
      rfl
    · intro j
      simp only [RingHom.comp_apply, projectiveEvaluate, eval₂Hom_X',
        HomogeneousLocalization.algebraMap_apply, coordinateRatio_val]
      exact mul_comm _ _
  apply HomogeneousLocalization.val_injective
  change ((algebraMap (CoordinateRing r θ i) (CoordinateLocalization r θ i)).comp
    (projectiveEvaluate r θ i)) p = _
  rw [hcomp, weighted_homogeneous_eval_scale (F.comp C) (fun j => F (X j))
    (IsLocalization.Away.invSelf (surfaceQuotient r θ (X i.castSucc))) p n hp,
    heval, homogeneousFraction_val]
  exact mul_comm _ _

theorem projectiveEvaluate_zero_of_surfaceQuotient_zero (r θ : ℂ) (i : Fin 4)
    (n : ℕ) (p : WeightedPoly) (hp : p.IsWeightedHomogeneous weight n)
    (hz : surfaceQuotient r θ p = 0) : projectiveEvaluate r θ i p = 0 := by
  rw [projectiveEvaluate_homogeneousFraction r θ i n p hp]
  apply HomogeneousLocalization.val_injective
  simp only [homogeneousFraction_val, hz, map_zero, zero_mul,
    HomogeneousLocalization.val_zero]

theorem surfaceQuotient_equation (r θ : ℂ) (j : Fin 2) :
    surfaceQuotient r θ (surfaceEquations r θ j) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)

theorem affineEvaluate_equation (r θ : ℂ) (i : Fin 4) (j : Fin 2) :
    affineEvaluate r θ i (dehomogenizedEquations r θ i j) = 0 := by
  fin_cases j
  · change affineEvaluate r θ i (dehomogenize i (actualSeedEquation r θ)) = 0
    rw [affineEvaluate_dehomogenize]
    exact projectiveEvaluate_zero_of_surfaceQuotient_zero r θ i 6 (actualSeedEquation r θ)
      (actualSeedEquation_homogeneous r θ) (surfaceQuotient_equation r θ 0)
  · change affineEvaluate r θ i (dehomogenize i (thetaH θ)) = 0
    rw [affineEvaluate_dehomogenize]
    exact projectiveEvaluate_zero_of_surfaceQuotient_zero r θ i 3 (thetaH θ)
      (thetaH_homogeneous θ) (surfaceQuotient_equation r θ 1)

theorem dehomogenizedIdeal_le_affineEvaluate_kernel (r θ : ℂ) (i : Fin 4) :
    surfaceChartIdeal (dehomogenizedEquations r θ i) ≤ RingHom.ker (affineEvaluate r θ i) := by
  apply Ideal.span_le.mpr
  rintro p ⟨j, rfl⟩
  exact affineEvaluate_equation r θ i j

def fromDehomogenized (r θ : ℂ) (i : Fin 4) :
    DehomogenizedRing r θ i →+* CoordinateRing r θ i :=
  Ideal.Quotient.lift (surfaceChartIdeal (dehomogenizedEquations r θ i))
    (affineEvaluate r θ i) (fun _ hp => dehomogenizedIdeal_le_affineEvaluate_kernel r θ i hp)

@[simp] theorem fromDehomogenized_mk (r θ : ℂ) (i : Fin 4) (p : SurfacePoly) :
    fromDehomogenized r θ i (dehomogenizedMap r θ i p) = affineEvaluate r θ i p := rfl

theorem toDehomogenized_affineEvaluate (r θ : ℂ) (i : Fin 4) :
    (toDehomogenized r θ i).comp (affineEvaluate r θ i) = dehomogenizedMap r θ i := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [affineEvaluate]
  · intro j
    cases j with
    | none =>
      simp only [RingHom.comp_apply, affineEvaluate, eval₂Hom_X']
      rw [map_add, map_pow, toDehomogenized_coordinateRatio, toDehomogenized_coordinateRatio,
        dehomogenize_last, dehomogenize_castSucc, map_sub, map_pow, sub_add_cancel]
    | some j => simp [affineEvaluate]

theorem toDehomogenized_fromDehomogenized (r θ : ℂ) (i : Fin 4)
    (z : DehomogenizedRing r θ i) :
    toDehomogenized r θ i (fromDehomogenized r θ i z) = z := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact RingHom.congr_fun (toDehomogenized_affineEvaluate r θ i) p

theorem fromDehomogenized_toDehomogenized (r θ : ℂ) (i : Fin 4)
    (z : CoordinateRing r θ i) :
    fromDehomogenized r θ i (toDehomogenized r θ i z) = z := by
  obtain ⟨n, a, ha, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (surfaceGrade r θ) (coordinate_mem_grade r θ i) z
  obtain ⟨p, hp, rfl⟩ := ha
  have hp' : p.IsWeightedHomogeneous weight n := by simpa using hp
  change fromDehomogenized r θ i
      (toDehomogenized r θ i (homogeneousFraction r θ i n p hp')) =
    homogeneousFraction r θ i n p hp'
  rw [toDehomogenized_homogeneousFraction, fromDehomogenized_mk,
    affineEvaluate_dehomogenize, projectiveEvaluate_homogeneousFraction r θ i n p hp']

/-- The actual weighted projective surface chart is its shifted affine equation ring. -/
def coordinateChartEquiv (r θ : ℂ) (i : Fin 4) :
    CoordinateRing r θ i ≃+* DehomogenizedRing r θ i where
  toFun := toDehomogenized r θ i
  invFun := fromDehomogenized r θ i
  left_inv := fromDehomogenized_toDehomogenized r θ i
  right_inv := toDehomogenized_fromDehomogenized r θ i
  map_mul' := map_mul (toDehomogenized r θ i)
  map_add' := map_add (toDehomogenized r θ i)

@[simp] theorem coordinateChartEquiv_homogeneousFraction (r θ : ℂ) (i : Fin 4)
    (n : ℕ) (p : WeightedPoly) (hp : p.IsWeightedHomogeneous weight n) :
    coordinateChartEquiv r θ i (homogeneousFraction r θ i n p hp) =
      dehomogenizedMap r θ i (dehomogenize i p) :=
  toDehomogenized_homogeneousFraction r θ i n p hp

@[simp] theorem coordinateChartEquiv_constants (r θ : ℂ) (i : Fin 4) (c : ℂ) :
    coordinateChartEquiv r θ i (constants r θ i c) = dehomogenizedMap r θ i (C c) :=
  toDehomogenized_constants r θ i c

@[simp] theorem coordinateChartEquiv_coordinateRatio (r θ : ℂ) (i : Fin 4) (j : Fin 3) :
    coordinateChartEquiv r θ i (coordinateRatio r θ i (i.succAbove j).castSucc) =
      dehomogenizedMap r θ i (X (some j)) := by
  change toDehomogenized r θ i (coordinateRatio r θ i (i.succAbove j).castSucc) = _
  rw [toDehomogenized_coordinateRatio, dehomogenize_succAbove]

@[simp] theorem coordinateChartEquiv_normalRatio (r θ : ℂ) (i : Fin 4) :
    coordinateChartEquiv r θ i (homogeneousFraction r θ i 2 originalF2 originalF2_homogeneous) =
      dehomogenizedMap r θ i (X none) := by
  exact (coordinateChartEquiv_homogeneousFraction r θ i 2 originalF2
    originalF2_homogeneous).trans (congrArg (dehomogenizedMap r θ i) (dehomogenize_f2 i))

theorem dehomogenize_one : dehomogenize 1 = firstSurfaceDehomogenize := by
  apply MvPolynomial.algHom_ext
  intro j
  induction j using Fin.lastCases with
  | last => rw [dehomogenize_last]; simp [firstSurfaceDehomogenize, linearCoordinate, Fin.insertNth, Fin.succAboveCases]
  | cast j =>
      rw [dehomogenize_castSucc]
      fin_cases j <;> simp [firstSurfaceDehomogenize, linearCoordinate, Fin.insertNth, Fin.succAboveCases]

theorem dehomogenize_two : dehomogenize 2 = secondSurfaceDehomogenize := by
  apply MvPolynomial.algHom_ext
  intro j
  induction j using Fin.lastCases with
  | last => rw [dehomogenize_last]; simp [secondSurfaceDehomogenize, linearCoordinate, Fin.insertNth, Fin.succAboveCases]
  | cast j =>
      rw [dehomogenize_castSucc]
      fin_cases j <;> simp [secondSurfaceDehomogenize, linearCoordinate, Fin.insertNth, Fin.succAboveCases]

open CycleQ2GeometricAffineCurveCharts

def firstEquations (r θ : ℂ) : Fin 2 → SurfacePoly :=
  ![surfaceEquation (firstQuadric r) (firstCubic θ)
      (firstSurfaceDehomogenize (originalG1 r)) (firstSurfaceDehomogenize originalG2)
      (firstSurfaceDehomogenize (thetaK θ)), includeCurve (firstCubic θ)]

def secondEquations (r θ : ℂ) : Fin 2 → SurfacePoly :=
  ![surfaceEquation (secondQuadric r) (secondCubic θ)
      (secondSurfaceDehomogenize (originalG1 r)) (secondSurfaceDehomogenize originalG2)
      (secondSurfaceDehomogenize (thetaK θ)), includeCurve (secondCubic θ)]

theorem dehomogenizedEquations_one (r θ : ℂ) :
    dehomogenizedEquations r θ 1 = firstEquations r θ := by
  simp only [dehomogenizedEquations, firstEquations, dehomogenize_one,
    firstSurfaceDehomogenize_equation, firstSurfaceDehomogenize_h]

theorem dehomogenizedEquations_two (r θ : ℂ) :
    dehomogenizedEquations r θ 2 = secondEquations r θ := by
  simp only [dehomogenizedEquations, secondEquations, dehomogenize_two,
    secondSurfaceDehomogenize_equation, secondSurfaceDehomogenize_h]

/-- The actual first weighted projective chart, with the precise local adjunction equations. -/
def firstChartEquiv (r θ : ℂ) :
    CoordinateRing r θ 1 ≃+* SurfaceChartRing (firstEquations r θ) :=
  (coordinateChartEquiv r θ 1).trans
    (Ideal.quotientEquivAlgOfEq ℂ
      (congrArg surfaceChartIdeal (dehomogenizedEquations_one r θ))).toRingEquiv

/-- The actual second weighted projective chart, with the precise local adjunction equations. -/
def secondChartEquiv (r θ : ℂ) :
    CoordinateRing r θ 2 ≃+* SurfaceChartRing (secondEquations r θ) :=
  (coordinateChartEquiv r θ 2).trans
    (Ideal.quotientEquivAlgOfEq ℂ
      (congrArg surfaceChartIdeal (dehomogenizedEquations_two r θ))).toRingEquiv

@[simp] theorem firstChartEquiv_homogeneousFraction (r θ : ℂ)
    (n : ℕ) (p : WeightedPoly) (hp : p.IsWeightedHomogeneous weight n) :
    firstChartEquiv r θ (homogeneousFraction r θ 1 n p hp) =
      Ideal.Quotient.mk (surfaceChartIdeal (firstEquations r θ))
        (firstSurfaceDehomogenize p) := by
  change Ideal.quotientEquivAlgOfEq ℂ (congrArg surfaceChartIdeal (dehomogenizedEquations_one r θ))
    (coordinateChartEquiv r θ 1 (homogeneousFraction r θ 1 n p hp)) = _
  rw [coordinateChartEquiv_homogeneousFraction]
  change Ideal.Quotient.mk (surfaceChartIdeal (firstEquations r θ)) (dehomogenize 1 p) = _
  rw [dehomogenize_one]

@[simp] theorem secondChartEquiv_homogeneousFraction (r θ : ℂ)
    (n : ℕ) (p : WeightedPoly) (hp : p.IsWeightedHomogeneous weight n) :
    secondChartEquiv r θ (homogeneousFraction r θ 2 n p hp) =
      Ideal.Quotient.mk (surfaceChartIdeal (secondEquations r θ))
        (secondSurfaceDehomogenize p) := by
  change Ideal.quotientEquivAlgOfEq ℂ (congrArg surfaceChartIdeal (dehomogenizedEquations_two r θ))
    (coordinateChartEquiv r θ 2 (homogeneousFraction r θ 2 n p hp)) = _
  rw [coordinateChartEquiv_homogeneousFraction]
  change Ideal.Quotient.mk (surfaceChartIdeal (secondEquations r θ)) (dehomogenize 2 p) = _
  rw [dehomogenize_two]

@[simp] theorem firstChartEquiv_normalRatio (r θ : ℂ) :
    firstChartEquiv r θ (homogeneousFraction r θ 1 2 originalF2 originalF2_homogeneous) =
      Ideal.Quotient.mk (surfaceChartIdeal (firstEquations r θ)) (X none) := by
  exact (firstChartEquiv_homogeneousFraction r θ 2 originalF2 originalF2_homogeneous).trans
    (congrArg (Ideal.Quotient.mk (surfaceChartIdeal (firstEquations r θ)))
      firstSurfaceDehomogenize_f2)

@[simp] theorem secondChartEquiv_normalRatio (r θ : ℂ) :
    secondChartEquiv r θ (homogeneousFraction r θ 2 2 originalF2 originalF2_homogeneous) =
      Ideal.Quotient.mk (surfaceChartIdeal (secondEquations r θ)) (X none) := by
  exact (secondChartEquiv_homogeneousFraction r θ 2 originalF2 originalF2_homogeneous).trans
    (congrArg (Ideal.Quotient.mk (surfaceChartIdeal (secondEquations r θ)))
      secondSurfaceDehomogenize_f2)

#print axioms firstChartEquiv
#print axioms secondChartEquiv


open CategoryTheory AlgebraicGeometry CycleQ2CartierProjectiveCover

/-- The dehomogenized equation ring is an actual affine chart of the projective surface. -/
def coordinateAffineChart (r θ : ℂ) (i : Fin 4) :
    (coordinatePatch r θ i.castSucc).toScheme ≅
      Spec (CommRingCat.of (DehomogenizedRing r θ i)) :=
  Proj.basicOpenIsoSpec (surfaceGrade r θ) (surfaceQuotient r θ (X i.castSucc))
      (coordinate_mem_grade r θ i) (by decide) ≪≫
    Scheme.Spec.mapIso (coordinateChartEquiv r θ i).toCommRingCatIso.symm.op

def firstAffineChart (r θ : ℂ) :
    (coordinatePatch r θ 1).toScheme ≅
      Spec (CommRingCat.of (SurfaceChartRing (firstEquations r θ))) :=
  Proj.basicOpenIsoSpec (surfaceGrade r θ) (surfaceQuotient r θ (X (1 : Fin 4).castSucc))
      (coordinate_mem_grade r θ 1) (by decide) ≪≫
    Scheme.Spec.mapIso (firstChartEquiv r θ).toCommRingCatIso.symm.op

def secondAffineChart (r θ : ℂ) :
    (coordinatePatch r θ 2).toScheme ≅
      Spec (CommRingCat.of (SurfaceChartRing (secondEquations r θ))) :=
  Proj.basicOpenIsoSpec (surfaceGrade r θ) (surfaceQuotient r θ (X (2 : Fin 4).castSucc))
      (coordinate_mem_grade r θ 2) (by decide) ≪≫
    Scheme.Spec.mapIso (secondChartEquiv r θ).toCommRingCatIso.symm.op

/-- The corresponding actual structure-sheaf sections carry the same equation presentation. -/
def coordinateSectionsEquiv (r θ : ℂ) (i : Fin 4) :
    Γ(projectiveSurface r θ, coordinatePatch r θ i.castSucc) ≃+*
      DehomogenizedRing r θ i :=
  (Proj.basicOpenIsoAway (surfaceGrade r θ) (surfaceQuotient r θ (X i.castSucc))
    (coordinate_mem_grade r θ i) (by decide)).commRingCatIsoToRingEquiv.symm.trans
      (coordinateChartEquiv r θ i)

def firstSectionsEquiv (r θ : ℂ) :
    Γ(projectiveSurface r θ, coordinatePatch r θ 1) ≃+* SurfaceChartRing (firstEquations r θ) :=
  (Proj.basicOpenIsoAway (surfaceGrade r θ) (surfaceQuotient r θ (X (1 : Fin 4).castSucc))
    (coordinate_mem_grade r θ 1) (by decide)).commRingCatIsoToRingEquiv.symm.trans
      (firstChartEquiv r θ)

def secondSectionsEquiv (r θ : ℂ) :
    Γ(projectiveSurface r θ, coordinatePatch r θ 2) ≃+* SurfaceChartRing (secondEquations r θ) :=
  (Proj.basicOpenIsoAway (surfaceGrade r θ) (surfaceQuotient r θ (X (2 : Fin 4).castSucc))
    (coordinate_mem_grade r θ 2) (by decide)).commRingCatIsoToRingEquiv.symm.trans
      (secondChartEquiv r θ)

#print axioms coordinateAffineChart
#print axioms firstAffineChart
#print axioms secondAffineChart
#print axioms coordinateSectionsEquiv


#print axioms coordinateChartEquiv

end CycleQ2GeometricSurfaceDehomogenizedCharts
