import Proposal.GeometricSeedFermatProj
import Proposal.GeometricSmoothRetract

/-!
# Smooth degree-zero charts of the actual zero-cubic seed

The degree-zero homogeneous localization on a weight-one coordinate is
an explicit complex-algebra retract of the corresponding localization
of the cone. Normalization sends each variable to its weighted ratio,
and sends the inverted coordinate to one. Weighted homogeneity proves
that this map kills the original equation and is the identity on every
homogeneous fraction of degree zero.

The cone localization is already smooth when `r ^ 3 = 2`. Smoothness
therefore descends to the actual homogeneous-localization chart. Its
complex algebra structure is the native map through degree zero used
by `Proj.toSpecZero`, so no change of coefficients is implicit.

Prepared for `fqlx` with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CycleQ2SeedFermatChartRetract

open MvPolynomial CycleQ2GeometricSeedSmooth CycleQ2SeedFermatCone
open CycleQ2GeometricIncidenceProj CycleQ2SeedFermatProj

/-- The native degree-zero chart of the existing one-equation cone ring. -/
abbrev ChartRing (r : ℂ) (i : Fin 4) :=
  HomogeneousLocalization.Away (coneGrade r) (coordinateClass r i.castSucc)

/-- The coefficient map occurring in the actual Proj structure morphism. -/
def chartCoefficient (r : ℂ) (i : Fin 4) : ℂ →+* ChartRing r i :=
  (HomogeneousLocalization.fromZeroRingHom (coneGrade r)
    (Submonoid.powers (coordinateClass r i.castSucc))).comp (coefficient r)

instance chartAlgebra (r : ℂ) (i : Fin 4) : Algebra ℂ (ChartRing r i) :=
  (chartCoefficient r i).toAlgebra

@[simp] theorem chart_algebraMap (r : ℂ) (i : Fin 4) (c : ℂ) :
    algebraMap ℂ (ChartRing r i) c = chartCoefficient r i c := rfl

@[simp] theorem chartCoefficient_val (r : ℂ) (i : Fin 4) (c : ℂ) :
    (chartCoefficient r i c).val =
      algebraMap (ConeRing r) (CoordinateRing r i.castSucc) (coneQuotient r (C c)) := by
  change Localization.mk ((coefficient r c : coneGrade r 0) : ConeRing r) 1 = _
  rw [coefficient_coe, Localization.mk_one_eq_algebraMap]

def homogeneousFraction (r : ℂ) (i : Fin 4) (n : ℕ) (p : SeedPolynomial)
    (hp : p.IsWeightedHomogeneous geometricWeight n) : ChartRing r i :=
  HomogeneousLocalization.Away.mk (coneGrade r) (coordinate_mem_grade r i)
    n (coneQuotient r p) (by simpa using coneQuotient_mem_grade r hp)

theorem homogeneousFraction_val (r : ℂ) (i : Fin 4) (n : ℕ)
    (p : SeedPolynomial) (hp : p.IsWeightedHomogeneous geometricWeight n) :
    (homogeneousFraction r i n p hp).val =
      algebraMap (ConeRing r) (CoordinateRing r i.castSucc) (coneQuotient r p) *
        IsLocalization.Away.invSelf (coordinateClass r i.castSucc) ^ n := by
  rw [homogeneousFraction, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
  simp only [map_pow]
  rw [mul_assoc,
    mul_comm (IsLocalization.Away.invSelf (coordinateClass r i.castSucc) ^ n),
    ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]

def coordinateRatio (r : ℂ) (i : Fin 4) (j : Fin 5) : ChartRing r i :=
  homogeneousFraction r i (geometricWeight j) (X j)
    (isWeightedHomogeneous_X ℂ geometricWeight j)

@[simp] theorem coordinateRatio_val (r : ℂ) (i : Fin 4) (j : Fin 5) :
    (coordinateRatio r i j).val =
      algebraMap (ConeRing r) (CoordinateRing r i.castSucc) (coneQuotient r (X j)) *
        IsLocalization.Away.invSelf (coordinateClass r i.castSucc) ^ geometricWeight j :=
  homogeneousFraction_val r i (geometricWeight j) (X j)
    (isWeightedHomogeneous_X ℂ geometricWeight j)

@[simp] theorem coordinateRatio_self (r : ℂ) (i : Fin 4) :
    coordinateRatio r i i.castSucc = 1 := by
  have hw : geometricWeight i.castSucc = 1 := by fin_cases i <;> rfl
  apply HomogeneousLocalization.val_injective
  rw [coordinateRatio_val, hw, pow_one]
  exact (IsLocalization.Away.mul_invSelf (coordinateClass r i.castSucc)).trans
    (HomogeneousLocalization.val_one.symm)

private theorem weighted_eval_scale {S : Type*} [CommRing S] (f : ℂ →+* S)
    (x : Fin 5 → S) (c : S) (p : SeedPolynomial) (n : ℕ)
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    eval₂Hom f (fun j => c ^ geometricWeight j * x j) p =
      c ^ n * eval₂Hom f x p := by
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => simp only [map_add, ihp, ihq, mul_add]
  | monomial d a hd =>
      have hdegree : (∑ j ∈ d.support, geometricWeight j * d j) = n := by
        simpa [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, Nat.mul_comm] using hd
      simp only [eval₂Hom_monomial, Finsupp.prod, mul_pow, ← pow_mul,
        Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdegree]
      ring

/-- Evaluation at the normalized weighted coordinates. -/
def projectiveEvaluate (r : ℂ) (i : Fin 4) : SeedPolynomial →+* ChartRing r i :=
  eval₂Hom (chartCoefficient r i) (coordinateRatio r i)

theorem projectiveEvaluate_homogeneousFraction (r : ℂ) (i : Fin 4)
    (n : ℕ) (p : SeedPolynomial) (hp : p.IsWeightedHomogeneous geometricWeight n) :
    projectiveEvaluate r i p = homogeneousFraction r i n p hp := by
  let F : SeedPolynomial →+* CoordinateRing r i.castSucc :=
    (algebraMap (ConeRing r) (CoordinateRing r i.castSucc)).comp (coneQuotient r)
  have heval : eval₂Hom (F.comp C) (fun j => F (X j)) = F := by
    apply MvPolynomial.ringHom_ext <;> intro x <;> simp
  have hcomp :
      (algebraMap (ChartRing r i) (CoordinateRing r i.castSucc)).comp
          (projectiveEvaluate r i) =
        eval₂Hom (F.comp C) (fun j =>
          IsLocalization.Away.invSelf (coordinateClass r i.castSucc) ^
            geometricWeight j * F (X j)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, projectiveEvaluate, eval₂Hom_C,
        HomogeneousLocalization.algebraMap_apply, chartCoefficient_val]
      rfl
    · intro j
      simp only [RingHom.comp_apply, projectiveEvaluate, eval₂Hom_X',
        HomogeneousLocalization.algebraMap_apply, coordinateRatio_val]
      exact mul_comm _ _
  apply HomogeneousLocalization.val_injective
  change ((algebraMap (ChartRing r i) (CoordinateRing r i.castSucc)).comp
    (projectiveEvaluate r i)) p = _
  rw [hcomp, weighted_eval_scale (F.comp C) (fun j => F (X j))
    (IsLocalization.Away.invSelf (coordinateClass r i.castSucc)) p n hp,
    heval, homogeneousFraction_val]
  exact mul_comm _ _

theorem projectiveEvaluate_seedFamily (r : ℂ) (i : Fin 4) :
    projectiveEvaluate r i (seedFamily r 0) = 0 := by
  rw [projectiveEvaluate_homogeneousFraction r i 6 (seedFamily r 0)
    (seedEquation_homogeneous r)]
  apply HomogeneousLocalization.val_injective
  simp only [homogeneousFraction_val, coneEquation, map_zero, zero_mul,
    HomogeneousLocalization.val_zero]

theorem coneIdeal_le_evaluate_kernel (r : ℂ) (i : Fin 4) :
    Ideal.span {seedFamily r 0} ≤ RingHom.ker (projectiveEvaluate r i) := by
  apply Ideal.span_le.mpr
  intro p hp
  rcases Set.mem_singleton_iff.mp hp with rfl
  exact projectiveEvaluate_seedFamily r i

/-- Normalization factors through the original one-equation cone quotient. -/
def coneNormalization (r : ℂ) (i : Fin 4) : ConeRing r →+* ChartRing r i :=
  Ideal.Quotient.lift (Ideal.span {seedFamily r 0}) (projectiveEvaluate r i)
    (fun _ hp => coneIdeal_le_evaluate_kernel r i hp)

@[simp] theorem coneNormalization_coneQuotient (r : ℂ) (i : Fin 4)
    (p : SeedPolynomial) :
    coneNormalization r i (coneQuotient r p) = projectiveEvaluate r i p := rfl

@[simp] theorem coneNormalization_self (r : ℂ) (i : Fin 4) :
    coneNormalization r i (coordinateClass r i.castSucc) = 1 := by
  change projectiveEvaluate r i (X i.castSucc) = 1
  simp only [projectiveEvaluate, eval₂Hom_X', coordinateRatio_self]

def coneNormalizationAlgHom (r : ℂ) (i : Fin 4) :
    ConeRing r →ₐ[ℂ] ChartRing r i where
  toRingHom := coneNormalization r i
  commutes' c := by
    change projectiveEvaluate r i (C c) = chartCoefficient r i c
    simp only [projectiveEvaluate, eval₂Hom_C]

/-- The full cone localization maps to its degree-zero chart by setting
the chosen weight-one coordinate to one. -/
def chartRetraction (r : ℂ) (i : Fin 4) :
    CoordinateRing r i.castSucc →ₐ[ℂ] ChartRing r i :=
  IsLocalization.Away.liftAlgHom (S := CoordinateRing r i.castSucc)
    (f := coneNormalizationAlgHom r i) (coordinateClass r i.castSucc) (by
      change IsUnit (coneNormalization r i (coordinateClass r i.castSucc))
      rw [coneNormalization_self]
      exact isUnit_one)

@[simp] theorem chartRetraction_algebraMap (r : ℂ) (i : Fin 4) (a : ConeRing r) :
    chartRetraction r i (algebraMap (ConeRing r) (CoordinateRing r i.castSucc) a) =
      coneNormalization r i a := by
  dsimp only [chartRetraction]
  have hunit : IsUnit (coneNormalization r i (coordinateClass r i.castSucc)) := by
    rw [coneNormalization_self]
    exact isUnit_one
  exact IsLocalization.Away.lift_eq (coordinateClass r i.castSucc) hunit a

@[simp] theorem chartRetraction_invSelf (r : ℂ) (i : Fin 4) :
    chartRetraction r i (IsLocalization.Away.invSelf (coordinateClass r i.castSucc)) = 1 := by
  have h := congrArg (chartRetraction r i)
    (IsLocalization.Away.mul_invSelf (S := CoordinateRing r i.castSucc)
      (coordinateClass r i.castSucc))
  simpa only [map_mul, map_one, chartRetraction_algebraMap,
    coneNormalization_self, one_mul] using h

/-- The native inclusion of degree-zero fractions preserves the exact
complex coefficient action used by the projective structure morphism. -/
def chartInclusion (r : ℂ) (i : Fin 4) :
    ChartRing r i →ₐ[ℂ] CoordinateRing r i.castSucc where
  toRingHom := algebraMap (ChartRing r i) (CoordinateRing r i.castSucc)
  commutes' c := by
    change (chartCoefficient r i c).val = algebraMap ℂ (CoordinateRing r i.castSucc) c
    rw [chartCoefficient_val]
    exact (IsScalarTower.algebraMap_apply ℂ (ConeRing r) (CoordinateRing r i.castSucc) c).symm

theorem chartRetraction_homogeneousFraction (r : ℂ) (i : Fin 4)
    (n : ℕ) (p : SeedPolynomial) (hp : p.IsWeightedHomogeneous geometricWeight n) :
    chartRetraction r i (chartInclusion r i (homogeneousFraction r i n p hp)) =
      homogeneousFraction r i n p hp := by
  change chartRetraction r i ((homogeneousFraction r i n p hp).val) = _
  rw [homogeneousFraction_val, map_mul, map_pow, chartRetraction_algebraMap,
    chartRetraction_invSelf, one_pow, mul_one, coneNormalization_coneQuotient,
    projectiveEvaluate_homogeneousFraction r i n p hp]

/-- Normalization is a left inverse of the native chart inclusion. -/
theorem chartRetraction_comp_chartInclusion (r : ℂ) (i : Fin 4) :
    (chartRetraction r i).comp (chartInclusion r i) = AlgHom.id ℂ (ChartRing r i) := by
  apply AlgHom.ext
  intro z
  obtain ⟨n, a, ha, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (coneGrade r) (coordinate_mem_grade r i) z
  obtain ⟨p, hp, rfl⟩ := ha
  have hp' : p.IsWeightedHomogeneous geometricWeight n := by simpa using hp
  change chartRetraction r i (chartInclusion r i (homogeneousFraction r i n p hp')) =
    homogeneousFraction r i n p hp'
  exact chartRetraction_homogeneousFraction r i n p hp'

/-- Every weight-one chart of the actual zero-cubic weighted Proj is
smooth over its native complex coefficient map when `r ^ 3 = 2`. -/
theorem chartRing_smooth (r : ℂ) (hr : r ^ 3 = 2) (i : Fin 4) :
    Algebra.Smooth ℂ (ChartRing r i) := by
  letI := coordinateRing_smooth r hr i.castSucc
  exact CycleQ2GeometricSmoothRetract.smooth_of_retract
    (chartInclusion r i) (chartRetraction r i) (chartRetraction_comp_chartInclusion r i)

end CycleQ2SeedFermatChartRetract

end

#print axioms CycleQ2SeedFermatChartRetract.projectiveEvaluate_seedFamily
#print axioms CycleQ2SeedFermatChartRetract.chartRetraction_comp_chartInclusion
#print axioms CycleQ2SeedFermatChartRetract.chartRing_smooth
