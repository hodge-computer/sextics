import Proposal.GeometricDegreeOneCech
import Proposal.GeometricAffineCurveCharts
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Coordinate charts of the actual projective curve

Dehomogenization sets a chosen projective coordinate to one. The inverse
chart map sends each remaining affine coordinate to its homogeneous ratio.
All rings below use the existing curve quotient and its existing grading.
The scalar map into the degree-zero homogeneous localization is constructed
from literal constant fractions; no unrelated complex-algebra structure is
assumed on that localization.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricDehomogenizedCharts

open MvPolynomial
open CycleQ2SeedTrace CycleQ2SeedCechTheta CycleQ2NormalConnecting
open CycleQ2GeometricProjectiveCurve CycleQ2GeometricAffineCurveCharts

/-- Set coordinate i to one and retain the other coordinates in their order. -/
def dehomogenize (i : Fin 4) : Poly →ₐ[ℂ] AffinePoly :=
  aeval (Fin.insertNth i 1 (fun j : Fin 3 => X j))

@[simp] theorem dehomogenize_self (i : Fin 4) : dehomogenize i (X i) = 1 := by
  simp [dehomogenize]

@[simp] theorem dehomogenize_succAbove (i : Fin 4) (j : Fin 3) :
    dehomogenize i (X (i.succAbove j)) = X j := by
  simp [dehomogenize]

def dehomogenizedEquations (r θ : ℂ) (i : Fin 4) : Fin 2 → AffinePoly :=
  ![dehomogenize i (relation r 0), dehomogenize i (curveH θ)]

abbrev DehomogenizedRing (r θ : ℂ) (i : Fin 4) :=
  ChartRing (dehomogenizedEquations r θ i)

abbrev CoordinateRing (r θ : ℂ) (i : Fin 4) :=
  HomogeneousLocalization.Away (curveGrade r θ) (curveMap r θ (X i))

abbrev CoordinateLocalization (r θ : ℂ) (i : Fin 4) :=
  Localization.Away (curveMap r θ (X i))

def dehomogenizedMap (r θ : ℂ) (i : Fin 4) :
    AffinePoly →+* DehomogenizedRing r θ i :=
  Ideal.Quotient.mk (chartIdeal (dehomogenizedEquations r θ i))

theorem dehomogenizedMap_equation (r θ : ℂ) (i : Fin 4) (j : Fin 2) :
    dehomogenizedMap r θ i (dehomogenizedEquations r θ i j) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)

theorem curveIdeal_le_dehomogenization_kernel (r θ : ℂ) (i : Fin 4) :
    curveIdeal r θ ≤
      RingHom.ker ((dehomogenizedMap r θ i).comp (dehomogenize i).toRingHom) := by
  apply Ideal.span_le.mpr
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with hp | hp
  · rw [hp]
    exact dehomogenizedMap_equation r θ i 0
  · rw [hp]
    exact dehomogenizedMap_equation r θ i 1

/-- The actual curve-quotient map induced by substitution Xi = 1. -/
def curveToDehomogenized (r θ : ℂ) (i : Fin 4) :
    CurveRing r θ →+* DehomogenizedRing r θ i :=
  Ideal.Quotient.lift (curveIdeal r θ)
    ((dehomogenizedMap r θ i).comp (dehomogenize i).toRingHom)
    (fun _ hp => curveIdeal_le_dehomogenization_kernel r θ i hp)

@[simp] theorem curveToDehomogenized_curveMap (r θ : ℂ) (i : Fin 4) (p : Poly) :
    curveToDehomogenized r θ i (curveMap r θ p) =
      dehomogenizedMap r θ i (dehomogenize i p) := rfl

@[simp] theorem curveToDehomogenized_self (r θ : ℂ) (i : Fin 4) :
    curveToDehomogenized r θ i (curveMap r θ (X i)) = 1 := by simp

def localizationToDehomogenized (r θ : ℂ) (i : Fin 4) :
    CoordinateLocalization r θ i →+* DehomogenizedRing r θ i :=
  Localization.awayLift (curveToDehomogenized r θ i) (curveMap r θ (X i))
    (isUnit_iff_exists_inv.mpr ⟨1, by simp⟩)

def toDehomogenized (r θ : ℂ) (i : Fin 4) :
    CoordinateRing r θ i →+* DehomogenizedRing r θ i :=
  (localizationToDehomogenized r θ i).comp
    (algebraMap (CoordinateRing r θ i) (CoordinateLocalization r θ i))

/-- A degree-zero fraction with a specified homogeneous polynomial numerator. -/
def homogeneousFraction (r θ : ℂ) (i : Fin 4) (n : ℕ) (p : Poly)
    (hp : p.IsHomogeneous n) : CoordinateRing r θ i :=
  HomogeneousLocalization.Away.mk (curveGrade r θ) (coordinate_mem_grade r θ i)
    n (curveMap r θ p) (by simpa using curveMap_mem_grade r θ hp)

theorem homogeneousFraction_val (r θ : ℂ) (i : Fin 4) (n : ℕ) (p : Poly)
    (hp : p.IsHomogeneous n) :
    (homogeneousFraction r θ i n p hp).val =
      algebraMap (CurveRing r θ) (CoordinateLocalization r θ i) (curveMap r θ p) *
        IsLocalization.Away.invSelf (curveMap r θ (X i)) ^ n := by
  rw [homogeneousFraction, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
  simp only [map_pow]
  rw [mul_assoc, mul_comm (IsLocalization.Away.invSelf (curveMap r θ (X i)) ^ n),
    ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]

@[simp] theorem toDehomogenized_homogeneousFraction (r θ : ℂ) (i : Fin 4)
    (n : ℕ) (p : Poly) (hp : p.IsHomogeneous n) :
    toDehomogenized r θ i (homogeneousFraction r θ i n p hp) =
      dehomogenizedMap r θ i (dehomogenize i p) := by
  change localizationToDehomogenized r θ i
    (Localization.mk (curveMap r θ p) ⟨curveMap r θ (X i) ^ n, n, rfl⟩) = _
  simpa only [localizationToDehomogenized, one_pow, mul_one,
    curveToDehomogenized_curveMap] using
      (Localization.awayLift_mk (curveToDehomogenized r θ i) (curveMap r θ (X i))
        (curveMap r θ p) 1 (by simp) n)

/-- The canonical complex constants, represented by degree-zero fractions. -/
def constants (r θ : ℂ) (i : Fin 4) : ℂ →+* CoordinateRing r θ i where
  toFun c := homogeneousFraction r θ i 0 (C c) (isHomogeneous_C _ c)
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
      algebraMap (CurveRing r θ) (CoordinateLocalization r θ i) (curveMap r θ (C c)) := by
  change (homogeneousFraction r θ i 0 (C c) (isHomogeneous_C _ c)).val = _
  simp only [homogeneousFraction_val, pow_zero, mul_one]

def coordinateRatio (r θ : ℂ) (i j : Fin 4) : CoordinateRing r θ i :=
  homogeneousFraction r θ i 1 (X j) (isHomogeneous_X ℂ j)

@[simp] theorem coordinateRatio_val (r θ : ℂ) (i j : Fin 4) :
    (coordinateRatio r θ i j).val =
      algebraMap (CurveRing r θ) (CoordinateLocalization r θ i) (curveMap r θ (X j)) *
        IsLocalization.Away.invSelf (curveMap r θ (X i)) := by
  simp only [coordinateRatio, homogeneousFraction_val, pow_one]

@[simp] theorem coordinateRatio_self (r θ : ℂ) (i : Fin 4) :
    coordinateRatio r θ i i = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [coordinateRatio_val, IsLocalization.Away.mul_invSelf, HomogeneousLocalization.val_one]

/-- Evaluation of a homogeneous polynomial after uniformly rescaling its variables. -/
theorem homogeneous_eval_scale {S : Type*} [CommRing S] (f : ℂ →+* S)
    (x : Fin 4 → S) (c : S) (p : Poly) (n : ℕ) (hp : p.IsHomogeneous n) :
    eval₂Hom f (fun j => c * x j) p = c ^ n * eval₂Hom f x p := by
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => simp only [map_add, ihp, ihq, mul_add]
  | monomial d a hd =>
      have hdegree : (∑ j ∈ d.support, d j) = n := by
        simpa [Finsupp.weight_apply, Finsupp.sum] using hd
      simp only [eval₂Hom_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum, hdegree]
      ring

@[simp] theorem toDehomogenized_constants (r θ : ℂ) (i : Fin 4) (c : ℂ) :
    toDehomogenized r θ i (constants r θ i c) = dehomogenizedMap r θ i (C c) := by
  change toDehomogenized r θ i
    (homogeneousFraction r θ i 0 (C c) (isHomogeneous_C _ c)) = _
  rw [toDehomogenized_homogeneousFraction]
  simp [dehomogenize]

@[simp] theorem toDehomogenized_coordinateRatio (r θ : ℂ) (i j : Fin 4) :
    toDehomogenized r θ i (coordinateRatio r θ i j) =
      dehomogenizedMap r θ i (dehomogenize i (X j)) :=
  toDehomogenized_homogeneousFraction r θ i 1 (X j) (isHomogeneous_X ℂ j)

/-- Evaluate affine coordinates at the actual ratios Xj/Xi. -/
def affineEvaluate (r θ : ℂ) (i : Fin 4) :
    AffinePoly →+* CoordinateRing r θ i :=
  eval₂Hom (constants r θ i) (fun j => coordinateRatio r θ i (i.succAbove j))

def projectiveEvaluate (r θ : ℂ) (i : Fin 4) :
    Poly →+* CoordinateRing r θ i :=
  eval₂Hom (constants r θ i) (coordinateRatio r θ i)

theorem affineEvaluate_comp_dehomogenize (r θ : ℂ) (i : Fin 4) :
    (affineEvaluate r θ i).comp (dehomogenize i).toRingHom = projectiveEvaluate r θ i := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [affineEvaluate, projectiveEvaluate, dehomogenize]
  · intro j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · simp [affineEvaluate, projectiveEvaluate]
    · simp [affineEvaluate, projectiveEvaluate]

@[simp] theorem affineEvaluate_dehomogenize (r θ : ℂ) (i : Fin 4) (p : Poly) :
    affineEvaluate r θ i (dehomogenize i p) = projectiveEvaluate r θ i p :=
  RingHom.congr_fun (affineEvaluate_comp_dehomogenize r θ i) p

/-- The inverse chart formula holds for every homogeneous numerator. -/
theorem projectiveEvaluate_homogeneousFraction (r θ : ℂ) (i : Fin 4)
    (n : ℕ) (p : Poly) (hp : p.IsHomogeneous n) :
    projectiveEvaluate r θ i p = homogeneousFraction r θ i n p hp := by
  let F : Poly →+* CoordinateLocalization r θ i :=
    (algebraMap (CurveRing r θ) (CoordinateLocalization r θ i)).comp (curveMap r θ)
  have heval : eval₂Hom (F.comp C) (fun j => F (X j)) = F := by
    apply MvPolynomial.ringHom_ext <;> intro x <;> simp
  have hcomp :
      (algebraMap (CoordinateRing r θ i) (CoordinateLocalization r θ i)).comp
          (projectiveEvaluate r θ i) =
        eval₂Hom (F.comp C) (fun j =>
          IsLocalization.Away.invSelf (curveMap r θ (X i)) * F (X j)) := by
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
  rw [hcomp, homogeneous_eval_scale (F.comp C) (fun j => F (X j))
    (IsLocalization.Away.invSelf (curveMap r θ (X i))) p n hp,
    heval, homogeneousFraction_val]
  exact mul_comm _ _

theorem projectiveEvaluate_zero_of_curveMap_zero (r θ : ℂ) (i : Fin 4)
    (n : ℕ) (p : Poly) (hp : p.IsHomogeneous n) (hz : curveMap r θ p = 0) :
    projectiveEvaluate r θ i p = 0 := by
  rw [projectiveEvaluate_homogeneousFraction r θ i n p hp]
  apply HomogeneousLocalization.val_injective
  simp only [homogeneousFraction_val, hz, map_zero, zero_mul,
    HomogeneousLocalization.val_zero]

theorem affineEvaluate_equation (r θ : ℂ) (i : Fin 4) (j : Fin 2) :
    affineEvaluate r θ i (dehomogenizedEquations r θ i j) = 0 := by
  fin_cases j
  · change affineEvaluate r θ i (dehomogenize i (relation r 0)) = 0
    rw [affineEvaluate_dehomogenize]
    exact projectiveEvaluate_zero_of_curveMap_zero r θ i 2 (relation r 0)
      (relation_zero_homogeneous r) (curveMap_f1 r θ)
  · change affineEvaluate r θ i (dehomogenize i (curveH θ)) = 0
    rw [affineEvaluate_dehomogenize]
    exact projectiveEvaluate_zero_of_curveMap_zero r θ i 3 (curveH θ)
      (sparse_curveH_homogeneous θ) (curveMap_h r θ)

theorem dehomogenizedIdeal_le_affineEvaluate_kernel (r θ : ℂ) (i : Fin 4) :
    chartIdeal (dehomogenizedEquations r θ i) ≤ RingHom.ker (affineEvaluate r θ i) := by
  apply Ideal.span_le.mpr
  rintro p ⟨j, rfl⟩
  exact affineEvaluate_equation r θ i j

/-- The inverse map descends through precisely the two dehomogenized equations. -/
def fromDehomogenized (r θ : ℂ) (i : Fin 4) :
    DehomogenizedRing r θ i →+* CoordinateRing r θ i :=
  Ideal.Quotient.lift (chartIdeal (dehomogenizedEquations r θ i))
    (affineEvaluate r θ i) (fun _ hp => dehomogenizedIdeal_le_affineEvaluate_kernel r θ i hp)

@[simp] theorem fromDehomogenized_mk (r θ : ℂ) (i : Fin 4) (p : AffinePoly) :
    fromDehomogenized r θ i (dehomogenizedMap r θ i p) = affineEvaluate r θ i p := rfl

theorem toDehomogenized_affineEvaluate (r θ : ℂ) (i : Fin 4) :
    (toDehomogenized r θ i).comp (affineEvaluate r θ i) = dehomogenizedMap r θ i := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [affineEvaluate]
  · intro j
    simp [affineEvaluate]

theorem toDehomogenized_fromDehomogenized (r θ : ℂ) (i : Fin 4)
    (z : DehomogenizedRing r θ i) :
    toDehomogenized r θ i (fromDehomogenized r θ i z) = z := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact RingHom.congr_fun (toDehomogenized_affineEvaluate r θ i) p

theorem fromDehomogenized_toDehomogenized (r θ : ℂ) (i : Fin 4)
    (z : CoordinateRing r θ i) :
    fromDehomogenized r θ i (toDehomogenized r θ i z) = z := by
  obtain ⟨n, a, ha, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (curveGrade r θ) (coordinate_mem_grade r θ i) z
  obtain ⟨p, hp, rfl⟩ := ha
  have hp' : p.IsHomogeneous n := by simpa using hp
  change fromDehomogenized r θ i
      (toDehomogenized r θ i (homogeneousFraction r θ i n p hp')) =
    homogeneousFraction r θ i n p hp'
  rw [toDehomogenized_homogeneousFraction, fromDehomogenized_mk,
    affineEvaluate_dehomogenize, projectiveEvaluate_homogeneousFraction r θ i n p hp']

/-- The actual degree-zero coordinate localization is its dehomogenized equation ring. -/
def coordinateChartEquiv (r θ : ℂ) (i : Fin 4) :
    CoordinateRing r θ i ≃+* DehomogenizedRing r θ i where
  toFun := toDehomogenized r θ i
  invFun := fromDehomogenized r θ i
  left_inv := fromDehomogenized_toDehomogenized r θ i
  right_inv := toDehomogenized_fromDehomogenized r θ i
  map_mul' := map_mul (toDehomogenized r θ i)
  map_add' := map_add (toDehomogenized r θ i)

@[simp] theorem coordinateChartEquiv_constants (r θ : ℂ) (i : Fin 4) (c : ℂ) :
    coordinateChartEquiv r θ i (constants r θ i c) = dehomogenizedMap r θ i (C c) :=
  toDehomogenized_constants r θ i c

@[simp] theorem coordinateChartEquiv_coordinateRatio (r θ : ℂ) (i : Fin 4) (j : Fin 3) :
    coordinateChartEquiv r θ i (coordinateRatio r θ i (i.succAbove j)) =
      dehomogenizedMap r θ i (X j) := by
  change toDehomogenized r θ i (coordinateRatio r θ i (i.succAbove j)) = _
  rw [toDehomogenized_coordinateRatio, dehomogenize_succAbove]

theorem dehomogenize_one : dehomogenize 1 = firstDehomogenize := by
  change aeval (Fin.insertNth (1 : Fin 4) 1 (fun j : Fin 3 => X j)) =
    aeval ![X 0, 1, X 1, X 2]
  congr 1
  apply Fin.insertNth_eq_iff.mpr
  constructor
  · rfl
  · funext j
    fin_cases j <;> rfl

theorem dehomogenize_two : dehomogenize 2 = secondDehomogenize := by
  change aeval (Fin.insertNth (2 : Fin 4) 1 (fun j : Fin 3 => X j)) =
    aeval ![X 0, X 1, 1, X 2]
  congr 1
  apply Fin.insertNth_eq_iff.mpr
  constructor
  · rfl
  · funext j
    fin_cases j <;> rfl

theorem dehomogenizedEquations_one (r θ : ℂ) :
    dehomogenizedEquations r θ 1 = ![firstQuadric r, firstCubic θ] := by
  funext j
  fin_cases j <;> simp [dehomogenizedEquations, dehomogenize_one,
    firstDehomogenize_quadric, firstDehomogenize_cubic]

theorem dehomogenizedEquations_two (r θ : ℂ) :
    dehomogenizedEquations r θ 2 = ![secondQuadric r, secondCubic θ] := by
  funext j
  fin_cases j <;> simp [dehomogenizedEquations, dehomogenize_two,
    secondDehomogenize_quadric, secondDehomogenize_cubic]

/-- The first coordinate chart uses exactly the existing first affine equations. -/
def firstChartEquiv (r θ : ℂ) :
    CoordinateRing r θ 1 ≃+* ChartRing ![firstQuadric r, firstCubic θ] :=
  (coordinateChartEquiv r θ 1).trans
    (Ideal.quotientEquivAlgOfEq ℂ
      (congrArg chartIdeal (dehomogenizedEquations_one r θ))).toRingEquiv

/-- The second coordinate chart uses exactly the existing second affine equations. -/
def secondChartEquiv (r θ : ℂ) :
    CoordinateRing r θ 2 ≃+* ChartRing ![secondQuadric r, secondCubic θ] :=
  (coordinateChartEquiv r θ 2).trans
    (Ideal.quotientEquivAlgOfEq ℂ
      (congrArg chartIdeal (dehomogenizedEquations_two r θ))).toRingEquiv

@[simp] theorem firstChartEquiv_coordinateRatio (r θ : ℂ) (j : Fin 3) :
    firstChartEquiv r θ (coordinateRatio r θ 1 ((1 : Fin 4).succAbove j)) =
      Ideal.Quotient.mk (chartIdeal ![firstQuadric r, firstCubic θ]) (X j) := by
  change Ideal.quotientEquivAlgOfEq ℂ (congrArg chartIdeal (dehomogenizedEquations_one r θ))
    (coordinateChartEquiv r θ 1 (coordinateRatio r θ 1 ((1 : Fin 4).succAbove j))) = _
  rw [coordinateChartEquiv_coordinateRatio]
  rfl

@[simp] theorem secondChartEquiv_coordinateRatio (r θ : ℂ) (j : Fin 3) :
    secondChartEquiv r θ (coordinateRatio r θ 2 ((2 : Fin 4).succAbove j)) =
      Ideal.Quotient.mk (chartIdeal ![secondQuadric r, secondCubic θ]) (X j) := by
  change Ideal.quotientEquivAlgOfEq ℂ (congrArg chartIdeal (dehomogenizedEquations_two r θ))
    (coordinateChartEquiv r θ 2 (coordinateRatio r θ 2 ((2 : Fin 4).succAbove j))) = _
  rw [coordinateChartEquiv_coordinateRatio]
  rfl

@[simp] theorem firstChartEquiv_constants (r θ : ℂ) (c : ℂ) :
    firstChartEquiv r θ (constants r θ 1 c) =
      algebraMap ℂ (ChartRing ![firstQuadric r, firstCubic θ]) c := by
  change Ideal.quotientEquivAlgOfEq ℂ (congrArg chartIdeal (dehomogenizedEquations_one r θ))
    (coordinateChartEquiv r θ 1 (constants r θ 1 c)) = _
  rw [coordinateChartEquiv_constants]
  rfl

@[simp] theorem secondChartEquiv_constants (r θ : ℂ) (c : ℂ) :
    secondChartEquiv r θ (constants r θ 2 c) =
      algebraMap ℂ (ChartRing ![secondQuadric r, secondCubic θ]) c := by
  change Ideal.quotientEquivAlgOfEq ℂ (congrArg chartIdeal (dehomogenizedEquations_two r θ))
    (coordinateChartEquiv r θ 2 (constants r θ 2 c)) = _
  rw [coordinateChartEquiv_constants]
  rfl

@[simp] theorem firstChartEquiv_symm_variable (r θ : ℂ) (j : Fin 3) :
    (firstChartEquiv r θ).symm
        (Ideal.Quotient.mk (chartIdeal ![firstQuadric r, firstCubic θ]) (X j)) =
      coordinateRatio r θ 1 ((1 : Fin 4).succAbove j) := by
  apply (firstChartEquiv r θ).injective
  rw [RingEquiv.apply_symm_apply, firstChartEquiv_coordinateRatio]

@[simp] theorem secondChartEquiv_symm_variable (r θ : ℂ) (j : Fin 3) :
    (secondChartEquiv r θ).symm
        (Ideal.Quotient.mk (chartIdeal ![secondQuadric r, secondCubic θ]) (X j)) =
      coordinateRatio r θ 2 ((2 : Fin 4).succAbove j) := by
  apply (secondChartEquiv r θ).injective
  rw [RingEquiv.apply_symm_apply, secondChartEquiv_coordinateRatio]

end CycleQ2GeometricDehomogenizedCharts

end
