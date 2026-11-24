import Proposal.GeometricProjectiveCurve
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# The actual relative incidence surface on its weight-one charts

Status: source-only proof draft. No elaboration or kernel replay was run.

For every coefficient algebra S and every incidence parameter y, the actual
degree-zero homogeneous localization of PointSurface y is identified with
the quotient by its two shifted dehomogenized equations. The normal affine
coordinate is (X4 + X2^2)/Xi^2. The forward and inverse maps are explicit;
their inverse laws use the existing quotient grading and homogeneity of
the original equations.

The final affine scheme isomorphism respects the existing surfaceToBase
morphism. No smoothness, flatness, or fiber-identification hypothesis is
assumed, and no such geometric property is asserted in this component.

The homogeneous-fraction construction adapts
GeometricSurfaceDehomogenizedCharts. The geometric strategy is due to
Ben Diamond and the collaborators cited in solution.md. Prepared for
fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2IncidenceDehomogenizedChart

open MvPolynomial
open CycleQ2IncidenceNormalForm CycleQ2IncidenceUniversalChart CycleQ2IncidenceImageLine
  CycleQ2GeometricIncidenceProj

variable {S : Type} [CommRing S] [Algebra ℂ S]

abbrev ChartPolynomial (S : Type) [CommRing S] :=
  MvPolynomial (Option (Fin 3)) S

def chartIdeal (v : Fin 2 → ChartPolynomial S) : Ideal (ChartPolynomial S) :=
  Ideal.span (Set.range v)

abbrev ChartRing (v : Fin 2 → ChartPolynomial S) :=
  ChartPolynomial S ⧸ chartIdeal v

def equations (y : ParameterIndex → S) : Fin 2 → MvPolynomial (Fin 5) S :=
  ![pointEquationF y, pointEquationH y]

def surfaceQuotient (y : ParameterIndex → S) :
    MvPolynomial (Fin 5) S →+* PointSurface y :=
  Ideal.Quotient.mk (pointEquations y)

theorem surfaceQuotient_mem_grade (y : ParameterIndex → S) {n : ℕ}
    {p : MvPolynomial (Fin 5) S} (hp : p.IsWeightedHomogeneous geometricWeight n) :
    surfaceQuotient y p ∈ surfaceGrade y n :=
  ⟨p, hp, rfl⟩

@[simp] theorem weight_castSucc (i : Fin 4) : geometricWeight i.castSucc = 1 := by
  fin_cases i <;> rfl

@[simp] theorem weight_last : geometricWeight (Fin.last 4) = 2 := rfl

/-- The weight-one coordinates after setting Xi = 1. -/
def linearCoordinate (i : Fin 4) : Fin 4 → ChartPolynomial S :=
  Fin.insertNth i 1 (fun j : Fin 3 => X (some j))

@[simp] theorem linearCoordinate_self (i : Fin 4) : linearCoordinate (S := S) i i = 1 := by
  simp [linearCoordinate]

@[simp] theorem linearCoordinate_succAbove (i : Fin 4) (j : Fin 3) :
    linearCoordinate (S := S) i (i.succAbove j) = X (some j) := by
  simp [linearCoordinate]

/-- The fourth affine variable is the genuine normal equation z = f₂/Xi². -/
def dehomogenize (i : Fin 4) : MvPolynomial (Fin 5) S →ₐ[S] ChartPolynomial S :=
  aeval (Fin.lastCases (X none - linearCoordinate i 2 ^ 2) (linearCoordinate i))

@[simp] theorem dehomogenize_castSucc (i j : Fin 4) :
    dehomogenize (S := S) i (X j.castSucc) = linearCoordinate i j := by
  simp [dehomogenize]

@[simp] theorem dehomogenize_last (i : Fin 4) :
    dehomogenize (S := S) i (X (Fin.last 4)) = X none - linearCoordinate i 2 ^ 2 := by
  simp only [dehomogenize, aeval_X, Fin.lastCases_last]

@[simp] theorem dehomogenize_self (i : Fin 4) : dehomogenize (S := S) i (X i.castSucc) = 1 := by
  simp

@[simp] theorem dehomogenize_succAbove (i : Fin 4) (j : Fin 3) :
    dehomogenize (S := S) i (X (i.succAbove j).castSucc) = X (some j) := by
  simp

@[simp] theorem dehomogenize_normal (i : Fin 4) :
    dehomogenize (S := S) i (X (Fin.last 4) + X (2 : Fin 4).castSucc ^ 2) = X none := by
  rw [map_add, map_pow, dehomogenize_last, dehomogenize_castSucc, sub_add_cancel]

def dehomogenizedEquations (y : ParameterIndex → S) (i : Fin 4) : Fin 2 → ChartPolynomial S :=
  ![dehomogenize i (pointEquationF y), dehomogenize i (pointEquationH y)]

abbrev DehomogenizedRing (y : ParameterIndex → S) (i : Fin 4) :=
  ChartRing (dehomogenizedEquations y i)

abbrev CoordinateRing (y : ParameterIndex → S) (i : Fin 4) :=
  HomogeneousLocalization.Away (surfaceGrade y) (surfaceQuotient y (X i.castSucc))

abbrev CoordinateLocalization (y : ParameterIndex → S) (i : Fin 4) :=
  Localization.Away (surfaceQuotient y (X i.castSucc))

def dehomogenizedMap (y : ParameterIndex → S) (i : Fin 4) :
    ChartPolynomial S →+* DehomogenizedRing y i :=
  Ideal.Quotient.mk (chartIdeal (dehomogenizedEquations y i))

theorem dehomogenizedMap_equation (y : ParameterIndex → S) (i : Fin 4) (j : Fin 2) :
    dehomogenizedMap y i (dehomogenizedEquations y i j) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)

theorem surfaceIdeal_le_dehomogenization_kernel (y : ParameterIndex → S) (i : Fin 4) :
    pointEquations y ≤
      RingHom.ker ((dehomogenizedMap y i).comp (dehomogenize i).toRingHom) := by
  apply Ideal.span_le.mpr
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · exact dehomogenizedMap_equation y i 1
  · exact dehomogenizedMap_equation y i 0

def surfaceToDehomogenized (y : ParameterIndex → S) (i : Fin 4) :
    PointSurface y →+* DehomogenizedRing y i :=
  Ideal.Quotient.lift (pointEquations y)
    ((dehomogenizedMap y i).comp (dehomogenize i).toRingHom)
    (fun _ hp => surfaceIdeal_le_dehomogenization_kernel y i hp)

@[simp] theorem surfaceToDehomogenized_surfaceQuotient (y : ParameterIndex → S) (i : Fin 4)
    (p : MvPolynomial (Fin 5) S) :
    surfaceToDehomogenized y i (surfaceQuotient y p) =
      dehomogenizedMap y i (dehomogenize i p) := rfl

@[simp] theorem surfaceToDehomogenized_self (y : ParameterIndex → S) (i : Fin 4) :
    surfaceToDehomogenized y i (surfaceQuotient y (X i.castSucc)) = 1 := by simp

def localizationToDehomogenized (y : ParameterIndex → S) (i : Fin 4) :
    CoordinateLocalization y i →+* DehomogenizedRing y i :=
  Localization.awayLift (surfaceToDehomogenized y i) (surfaceQuotient y (X i.castSucc))
    (isUnit_iff_exists_inv.mpr ⟨1, by simp⟩)

def toDehomogenized (y : ParameterIndex → S) (i : Fin 4) :
    CoordinateRing y i →+* DehomogenizedRing y i :=
  (localizationToDehomogenized y i).comp
    (algebraMap (CoordinateRing y i) (CoordinateLocalization y i))

theorem coordinate_mem_grade (y : ParameterIndex → S) (i : Fin 4) :
    surfaceQuotient y (X i.castSucc) ∈ surfaceGrade y 1 := by
  apply surfaceQuotient_mem_grade
  change (X i.castSucc : MvPolynomial (Fin 5) S).IsWeightedHomogeneous geometricWeight 1
  simpa only [weight_castSucc] using isWeightedHomogeneous_X S geometricWeight i.castSucc

def homogeneousFraction (y : ParameterIndex → S) (i : Fin 4) (n : ℕ) (p : MvPolynomial (Fin 5) S)
    (hp : p.IsWeightedHomogeneous geometricWeight n) : CoordinateRing y i :=
  HomogeneousLocalization.Away.mk (surfaceGrade y) (coordinate_mem_grade y i)
    n (surfaceQuotient y p) (by simpa using surfaceQuotient_mem_grade y hp)

theorem homogeneousFraction_val (y : ParameterIndex → S) (i : Fin 4) (n : ℕ) (p : MvPolynomial (Fin 5) S)
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    (homogeneousFraction y i n p hp).val =
      algebraMap (PointSurface y) (CoordinateLocalization y i) (surfaceQuotient y p) *
        IsLocalization.Away.invSelf (surfaceQuotient y (X i.castSucc)) ^ n := by
  rw [homogeneousFraction, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
  simp only [map_pow]
  rw [mul_assoc, mul_comm (IsLocalization.Away.invSelf (surfaceQuotient y (X i.castSucc)) ^ n),
    ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]

@[simp] theorem toDehomogenized_homogeneousFraction (y : ParameterIndex → S) (i : Fin 4)
    (n : ℕ) (p : MvPolynomial (Fin 5) S) (hp : p.IsWeightedHomogeneous geometricWeight n) :
    toDehomogenized y i (homogeneousFraction y i n p hp) =
      dehomogenizedMap y i (dehomogenize i p) := by
  change localizationToDehomogenized y i
    (Localization.mk (surfaceQuotient y p)
      ⟨surfaceQuotient y (X i.castSucc) ^ n, n, rfl⟩) = _
  simpa only [localizationToDehomogenized, one_pow, mul_one,
    surfaceToDehomogenized_surfaceQuotient] using
      (Localization.awayLift_mk (surfaceToDehomogenized y i)
        (surfaceQuotient y (X i.castSucc)) (surfaceQuotient y p) 1 (by simp) n)

def constants (y : ParameterIndex → S) (i : Fin 4) : S →+* CoordinateRing y i where
  toFun c := homogeneousFraction y i 0 (C c) (isWeightedHomogeneous_C geometricWeight c)
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

@[simp] theorem constants_val (y : ParameterIndex → S) (i : Fin 4) (c : S) :
    (constants y i c).val =
      algebraMap (PointSurface y) (CoordinateLocalization y i) (surfaceQuotient y (C c)) := by
  change (homogeneousFraction y i 0 (C c) (isWeightedHomogeneous_C geometricWeight c)).val = _
  simp only [homogeneousFraction_val, pow_zero, mul_one]

def coordinateRatio (y : ParameterIndex → S) (i : Fin 4) (j : Fin 5) : CoordinateRing y i :=
  homogeneousFraction y i (geometricWeight j) (X j) (isWeightedHomogeneous_X S geometricWeight j)

@[simp] theorem coordinateRatio_val (y : ParameterIndex → S) (i : Fin 4) (j : Fin 5) :
    (coordinateRatio y i j).val =
      algebraMap (PointSurface y) (CoordinateLocalization y i) (surfaceQuotient y (X j)) *
        IsLocalization.Away.invSelf (surfaceQuotient y (X i.castSucc)) ^ geometricWeight j :=
  homogeneousFraction_val y i (geometricWeight j) (X j) (isWeightedHomogeneous_X S geometricWeight j)

@[simp] theorem coordinateRatio_self (y : ParameterIndex → S) (i : Fin 4) :
    coordinateRatio y i i.castSucc = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [coordinateRatio_val, weight_castSucc, pow_one,
    IsLocalization.Away.mul_invSelf, HomogeneousLocalization.val_one]

theorem weighted_homogeneous_eval_scale {T : Type*} [CommRing T] (f : S →+* T)
    (x : Fin 5 → T) (c : T) (p : MvPolynomial (Fin 5) S) (n : ℕ)
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    eval₂Hom f (fun j => c ^ geometricWeight j * x j) p = c ^ n * eval₂Hom f x p := by
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => simp only [map_add, ihp, ihq, mul_add]
  | monomial d a hd =>
      have hdegree : (∑ j ∈ d.support, geometricWeight j * d j) = n := by
        simpa [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, Nat.mul_comm] using hd
      simp only [eval₂Hom_monomial, Finsupp.prod, mul_pow, ← pow_mul,
        Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdegree]
      ring

@[simp] theorem toDehomogenized_constants (y : ParameterIndex → S) (i : Fin 4) (c : S) :
    toDehomogenized y i (constants y i c) = dehomogenizedMap y i (C c) := by
  change toDehomogenized y i
    (homogeneousFraction y i 0 (C c) (isWeightedHomogeneous_C geometricWeight c)) = _
  rw [toDehomogenized_homogeneousFraction]
  simp [dehomogenize]

@[simp] theorem toDehomogenized_coordinateRatio (y : ParameterIndex → S) (i : Fin 4) (j : Fin 5) :
    toDehomogenized y i (coordinateRatio y i j) =
      dehomogenizedMap y i (dehomogenize i (X j)) :=
  toDehomogenized_homogeneousFraction y i (geometricWeight j) (X j)
    (isWeightedHomogeneous_X S geometricWeight j)

/-- Evaluate the shifted normal variable at the original (X4 + X2^2)/Xi^2. -/
def affineEvaluate (y : ParameterIndex → S) (i : Fin 4) : ChartPolynomial S →+* CoordinateRing y i :=
  eval₂Hom (constants y i) (fun j => match j with
    | none => coordinateRatio y i (Fin.last 4) + coordinateRatio y i (2 : Fin 4).castSucc ^ 2
    | some j => coordinateRatio y i (i.succAbove j).castSucc)

def projectiveEvaluate (y : ParameterIndex → S) (i : Fin 4) : MvPolynomial (Fin 5) S →+* CoordinateRing y i :=
  eval₂Hom (constants y i) (coordinateRatio y i)

@[simp] theorem affineEvaluate_linearCoordinate (y : ParameterIndex → S) (i j : Fin 4) :
    affineEvaluate y i (linearCoordinate i j) = coordinateRatio y i j.castSucc := by
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · simp
  · simp [affineEvaluate]

theorem affineEvaluate_comp_dehomogenize (y : ParameterIndex → S) (i : Fin 4) :
    (affineEvaluate y i).comp (dehomogenize i).toRingHom = projectiveEvaluate y i := by
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

@[simp] theorem affineEvaluate_dehomogenize (y : ParameterIndex → S) (i : Fin 4) (p : MvPolynomial (Fin 5) S) :
    affineEvaluate y i (dehomogenize i p) = projectiveEvaluate y i p :=
  RingHom.congr_fun (affineEvaluate_comp_dehomogenize y i) p

theorem projectiveEvaluate_homogeneousFraction (y : ParameterIndex → S) (i : Fin 4)
    (n : ℕ) (p : MvPolynomial (Fin 5) S) (hp : p.IsWeightedHomogeneous geometricWeight n) :
    projectiveEvaluate y i p = homogeneousFraction y i n p hp := by
  let F : MvPolynomial (Fin 5) S →+* CoordinateLocalization y i :=
    (algebraMap (PointSurface y) (CoordinateLocalization y i)).comp (surfaceQuotient y)
  have heval : eval₂Hom (F.comp C) (fun j => F (X j)) = F := by
    apply MvPolynomial.ringHom_ext <;> intro x <;> simp
  have hcomp :
      (algebraMap (CoordinateRing y i) (CoordinateLocalization y i)).comp
          (projectiveEvaluate y i) =
        eval₂Hom (F.comp C) (fun j =>
          IsLocalization.Away.invSelf (surfaceQuotient y (X i.castSucc)) ^ geometricWeight j * F (X j)) := by
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
  change ((algebraMap (CoordinateRing y i) (CoordinateLocalization y i)).comp
    (projectiveEvaluate y i)) p = _
  rw [hcomp, weighted_homogeneous_eval_scale (F.comp C) (fun j => F (X j))
    (IsLocalization.Away.invSelf (surfaceQuotient y (X i.castSucc))) p n hp,
    heval, homogeneousFraction_val]
  exact mul_comm _ _

theorem projectiveEvaluate_zero_of_surfaceQuotient_zero (y : ParameterIndex → S) (i : Fin 4)
    (n : ℕ) (p : MvPolynomial (Fin 5) S) (hp : p.IsWeightedHomogeneous geometricWeight n)
    (hz : surfaceQuotient y p = 0) : projectiveEvaluate y i p = 0 := by
  rw [projectiveEvaluate_homogeneousFraction y i n p hp]
  apply HomogeneousLocalization.val_injective
  simp only [homogeneousFraction_val, hz, map_zero, zero_mul,
    HomogeneousLocalization.val_zero]

theorem surfaceQuotient_equation (y : ParameterIndex → S) (j : Fin 2) :
    surfaceQuotient y (equations y j) = 0 := by
  change Ideal.Quotient.mk
      (Ideal.span {pointEquationH y, pointEquationF y}) (equations y j) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.subset_span
  fin_cases j <;> simp [equations]

theorem affineEvaluate_equation (y : ParameterIndex → S) (i : Fin 4) (j : Fin 2) :
    affineEvaluate y i (dehomogenizedEquations y i j) = 0 := by
  fin_cases j
  · change affineEvaluate y i (dehomogenize i (pointEquationF y)) = 0
    rw [affineEvaluate_dehomogenize]
    exact projectiveEvaluate_zero_of_surfaceQuotient_zero y i 6 (pointEquationF y)
      (pointEquationF_homogeneous y) (surfaceQuotient_equation y 0)
  · change affineEvaluate y i (dehomogenize i (pointEquationH y)) = 0
    rw [affineEvaluate_dehomogenize]
    exact projectiveEvaluate_zero_of_surfaceQuotient_zero y i 3 (pointEquationH y)
      (pointEquationH_homogeneous y) (surfaceQuotient_equation y 1)

theorem dehomogenizedIdeal_le_affineEvaluate_kernel (y : ParameterIndex → S) (i : Fin 4) :
    chartIdeal (dehomogenizedEquations y i) ≤ RingHom.ker (affineEvaluate y i) := by
  apply Ideal.span_le.mpr
  rintro p ⟨j, rfl⟩
  exact affineEvaluate_equation y i j

def fromDehomogenized (y : ParameterIndex → S) (i : Fin 4) :
    DehomogenizedRing y i →+* CoordinateRing y i :=
  Ideal.Quotient.lift (chartIdeal (dehomogenizedEquations y i))
    (affineEvaluate y i) (fun _ hp => dehomogenizedIdeal_le_affineEvaluate_kernel y i hp)

@[simp] theorem fromDehomogenized_mk (y : ParameterIndex → S) (i : Fin 4) (p : ChartPolynomial S) :
    fromDehomogenized y i (dehomogenizedMap y i p) = affineEvaluate y i p := rfl

theorem toDehomogenized_affineEvaluate (y : ParameterIndex → S) (i : Fin 4) :
    (toDehomogenized y i).comp (affineEvaluate y i) = dehomogenizedMap y i := by
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

theorem toDehomogenized_fromDehomogenized (y : ParameterIndex → S) (i : Fin 4)
    (z : DehomogenizedRing y i) :
    toDehomogenized y i (fromDehomogenized y i z) = z := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact RingHom.congr_fun (toDehomogenized_affineEvaluate y i) p

theorem fromDehomogenized_toDehomogenized (y : ParameterIndex → S) (i : Fin 4)
    (z : CoordinateRing y i) :
    fromDehomogenized y i (toDehomogenized y i z) = z := by
  obtain ⟨n, a, ha, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (surfaceGrade y) (coordinate_mem_grade y i) z
  obtain ⟨p, hp, rfl⟩ := ha
  have hp' : p.IsWeightedHomogeneous geometricWeight n := by simpa using hp
  change fromDehomogenized y i
      (toDehomogenized y i (homogeneousFraction y i n p hp')) =
    homogeneousFraction y i n p hp'
  rw [toDehomogenized_homogeneousFraction, fromDehomogenized_mk,
    affineEvaluate_dehomogenize, projectiveEvaluate_homogeneousFraction y i n p hp']

/-- The actual weighted projective surface chart is its shifted affine equation ring. -/
def coordinateChartEquiv (y : ParameterIndex → S) (i : Fin 4) :
    CoordinateRing y i ≃+* DehomogenizedRing y i where
  toFun := toDehomogenized y i
  invFun := fromDehomogenized y i
  left_inv := fromDehomogenized_toDehomogenized y i
  right_inv := toDehomogenized_fromDehomogenized y i
  map_mul' := map_mul (toDehomogenized y i)
  map_add' := map_add (toDehomogenized y i)

@[simp] theorem coordinateChartEquiv_homogeneousFraction (y : ParameterIndex → S) (i : Fin 4)
    (n : ℕ) (p : MvPolynomial (Fin 5) S) (hp : p.IsWeightedHomogeneous geometricWeight n) :
    coordinateChartEquiv y i (homogeneousFraction y i n p hp) =
      dehomogenizedMap y i (dehomogenize i p) :=
  toDehomogenized_homogeneousFraction y i n p hp

/-! ## Coefficients and the actual scheme chart over S -/

/-- The existing structure morphism supplies the coefficients in this chart. -/
def basicOpenCoefficient (y : ParameterIndex → S) (i : Fin 4) :
    S →+* CoordinateRing y i :=
  (HomogeneousLocalization.fromZeroRingHom (surfaceGrade y)
    (Submonoid.powers (surfaceQuotient y (X i.castSucc)))).comp (surfaceCoefficient y)

theorem basicOpenCoefficient_coordinate (y : ParameterIndex → S) (i : Fin 4) (c : S) :
    basicOpenCoefficient y i c = constants y i c := by
  apply HomogeneousLocalization.val_injective
  rw [constants_val]
  change Localization.mk (algebraMap S (PointSurface y) c) 1 = _
  rw [Localization.mk_one_eq_algebraMap]
  rfl

instance coordinateAlgebra (y : ParameterIndex → S) (i : Fin 4) :
    Algebra S (CoordinateRing y i) :=
  (basicOpenCoefficient y i).toAlgebra

@[simp] theorem coordinate_algebraMap (y : ParameterIndex → S) (i : Fin 4) (c : S) :
    algebraMap S (CoordinateRing y i) c = constants y i c :=
  basicOpenCoefficient_coordinate y i c

/-- The actual degree-zero chart, with its canonical S-coefficients, is
the quotient by the two original shifted dehomogenized equations. -/
def familyCoordinateChartEquiv (y : ParameterIndex → S) (i : Fin 4) :
    CoordinateRing y i ≃ₐ[S] DehomogenizedRing y i where
  __ := coordinateChartEquiv y i
  commutes' c := by
    change coordinateChartEquiv y i (algebraMap S (CoordinateRing y i) c) =
      dehomogenizedMap y i (C c)
    rw [coordinate_algebraMap]
    exact toDehomogenized_constants y i c

@[simp] theorem familyCoordinateChartEquiv_homogeneousFraction
    (y : ParameterIndex → S) (i : Fin 4) (n : ℕ)
    (p : MvPolynomial (Fin 5) S) (hp : p.IsWeightedHomogeneous geometricWeight n) :
    familyCoordinateChartEquiv y i (homogeneousFraction y i n p hp) =
      dehomogenizedMap y i (dehomogenize i p) :=
  toDehomogenized_homogeneousFraction y i n p hp

@[simp] theorem familyCoordinateChartEquiv_symm_mk
    (y : ParameterIndex → S) (i : Fin 4) (p : ChartPolynomial S) :
    (familyCoordinateChartEquiv y i).symm (dehomogenizedMap y i p) =
      affineEvaluate y i p := rfl

@[simp] theorem familyCoordinateChartEquiv_linearCoordinate
    (y : ParameterIndex → S) (i : Fin 4) (j : Fin 3) :
    familyCoordinateChartEquiv y i (coordinateRatio y i (i.succAbove j).castSucc) =
      dehomogenizedMap y i (X (some j)) := by
  change toDehomogenized y i (coordinateRatio y i (i.succAbove j).castSucc) = _
  rw [toDehomogenized_coordinateRatio, dehomogenize_succAbove]

@[simp] theorem familyCoordinateChartEquiv_normal
    (y : ParameterIndex → S) (i : Fin 4) :
    familyCoordinateChartEquiv y i
      (coordinateRatio y i (Fin.last 4) + coordinateRatio y i (2 : Fin 4).castSucc ^ 2) =
      dehomogenizedMap y i (X none) := by
  change toDehomogenized y i
    (coordinateRatio y i (Fin.last 4) + coordinateRatio y i (2 : Fin 4).castSucc ^ 2) = _
  rw [map_add, map_pow, toDehomogenized_coordinateRatio, toDehomogenized_coordinateRatio,
    dehomogenize_last, dehomogenize_castSucc, map_sub, map_pow, sub_add_cancel]

open CategoryTheory AlgebraicGeometry

def familyCoordinatePatch (y : ParameterIndex → S) (i : Fin 4) :
    (surface y).Opens :=
  Proj.basicOpen (surfaceGrade y) (surfaceQuotient y (X i.castSucc))

/-- An affine chart of the existing relative projective incidence surface. -/
def familyCoordinateAffineChart (y : ParameterIndex → S) (i : Fin 4) :
    (familyCoordinatePatch y i).toScheme ≅
      Spec (CommRingCat.of (DehomogenizedRing y i)) :=
  Proj.basicOpenIsoSpec (surfaceGrade y) (surfaceQuotient y (X i.castSucc))
      (coordinate_mem_grade y i) (by decide) ≪≫
    Scheme.Spec.mapIso (coordinateChartEquiv y i).toCommRingCatIso.symm.op

theorem awayι_surfaceToBase (y : ParameterIndex → S) (i : Fin 4) :
    Proj.awayι (surfaceGrade y) (surfaceQuotient y (X i.castSucc))
        (coordinate_mem_grade y i) (by decide) ≫ surfaceToBase y =
      Spec.map (CommRingCat.ofHom (basicOpenCoefficient y i)) := by
  rw [surfaceToBase, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  rfl

/-- The chart identification respects the original parameter-base morphism. -/
theorem familyCoordinateAffineChart_overBase (y : ParameterIndex → S) (i : Fin 4) :
    (familyCoordinateAffineChart y i).inv ≫
        (familyCoordinatePatch y i).ι ≫ surfaceToBase y =
      Spec.map (CommRingCat.ofHom (algebraMap S (DehomogenizedRing y i))) := by
  change (Spec.map (CommRingCat.ofHom (coordinateChartEquiv y i).toRingHom) ≫
      (Proj.basicOpenIsoSpec (surfaceGrade y) (surfaceQuotient y (X i.castSucc))
        (coordinate_mem_grade y i) (by decide)).inv) ≫
      (Proj.basicOpen (surfaceGrade y) (surfaceQuotient y (X i.castSucc))).ι ≫
        surfaceToBase y = _
  rw [Category.assoc, Proj.basicOpenIsoSpec_inv_ι_assoc,
    awayι_surfaceToBase, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact (familyCoordinateChartEquiv y i).commutes c

end CycleQ2IncidenceDehomogenizedChart

end

#print axioms CycleQ2IncidenceDehomogenizedChart.familyCoordinateChartEquiv
#print axioms CycleQ2IncidenceDehomogenizedChart.familyCoordinateChartEquiv_normal
#print axioms CycleQ2IncidenceDehomogenizedChart.familyCoordinateAffineChart_overBase

