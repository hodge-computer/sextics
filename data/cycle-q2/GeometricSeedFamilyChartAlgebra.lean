import Proposal.GeometricSeedProjectiveFamily

/-!
# Native homogeneous-localization charts of the full cubic family

The chart ring is the native degree-zero localization of the original
universal cone quotient. Its parameter-algebra structure is the one used
by `Proj.toSpecZero`. Weighted normalization evaluates each original
coordinate at its corresponding homogeneous ratio and kills the actual
degree-six family equation.

These constructions use homogeneity alone. They assume neither a smooth
fiber nor a smooth total family. Source-only draft: no Lean elaboration,
compilation, or kernel replay was run. Prepared for `fqlx` with OpenAI
ChatGPT assistance, following Ben Diamond's geometric seed construction.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedFamilyChart

open MvPolynomial CycleQ2SeedCubicFamily CycleQ2SeedProjectiveFamily
open CycleQ2GeometricIncidenceProj

/-- The full cone localization at one of the four weight-one coordinates. -/
abbrev CoordinateRing (r : ℂ) (i : Fin 4) :=
  Localization.Away (familyCoordinate r i.castSucc)

/-- The native degree-zero homogeneous localization for the same coordinate. -/
abbrev ChartRing (r : ℂ) (i : Fin 4) :=
  HomogeneousLocalization.Away (familyGrade r) (familyCoordinate r i.castSucc)

theorem coordinate_mem_grade (r : ℂ) (i : Fin 4) :
    familyCoordinate r i.castSucc ∈ familyGrade r 1 := by
  simpa only [CycleQ2SeedFermatProj.geometricWeight_castSucc] using
    familyCoordinate_mem_grade r i.castSucc

def chartCoefficient (r : ℂ) (i : Fin 4) : ParameterRing →+* ChartRing r i :=
  (HomogeneousLocalization.fromZeroRingHom (familyGrade r)
    (Submonoid.powers (familyCoordinate r i.castSucc))).comp (parameterCoefficient r)

instance chartAlgebra (r : ℂ) (i : Fin 4) : Algebra ParameterRing (ChartRing r i) :=
  (chartCoefficient r i).toAlgebra

@[simp] theorem chart_algebraMap (r : ℂ) (i : Fin 4) (c : ParameterRing) :
    algebraMap ParameterRing (ChartRing r i) c = chartCoefficient r i c := rfl

@[simp] theorem chartCoefficient_val (r : ℂ) (i : Fin 4) (c : ParameterRing) :
    (chartCoefficient r i c).val =
      algebraMap (FamilyRing r) (CoordinateRing r i) (familyQuotient r (C c)) := by
  change Localization.mk ((parameterCoefficient r c : familyGrade r 0) : FamilyRing r) 1 = _
  rw [parameterCoefficient_coe, Localization.mk_one_eq_algebraMap]

def homogeneousFraction (r : ℂ) (i : Fin 4) (n : ℕ) (p : FamilyPolynomial)
    (hp : p.IsWeightedHomogeneous geometricWeight n) : ChartRing r i :=
  HomogeneousLocalization.Away.mk (familyGrade r) (coordinate_mem_grade r i)
    n (familyQuotient r p) (by simpa using familyQuotient_mem_grade r hp)

theorem homogeneousFraction_val (r : ℂ) (i : Fin 4) (n : ℕ)
    (p : FamilyPolynomial) (hp : p.IsWeightedHomogeneous geometricWeight n) :
    (homogeneousFraction r i n p hp).val =
      algebraMap (FamilyRing r) (CoordinateRing r i) (familyQuotient r p) *
        IsLocalization.Away.invSelf (familyCoordinate r i.castSucc) ^ n := by
  rw [homogeneousFraction, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
  simp only [map_pow]
  rw [mul_assoc,
    mul_comm (IsLocalization.Away.invSelf (familyCoordinate r i.castSucc) ^ n),
    ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]

def coordinateRatio (r : ℂ) (i : Fin 4) (j : Fin 5) : ChartRing r i :=
  homogeneousFraction r i (geometricWeight j) (X j)
    (isWeightedHomogeneous_X ParameterRing geometricWeight j)

@[simp] theorem coordinateRatio_val (r : ℂ) (i : Fin 4) (j : Fin 5) :
    (coordinateRatio r i j).val =
      algebraMap (FamilyRing r) (CoordinateRing r i) (familyQuotient r (X j)) *
        IsLocalization.Away.invSelf (familyCoordinate r i.castSucc) ^ geometricWeight j :=
  homogeneousFraction_val r i (geometricWeight j) (X j)
    (isWeightedHomogeneous_X ParameterRing geometricWeight j)

@[simp] theorem coordinateRatio_self (r : ℂ) (i : Fin 4) :
    coordinateRatio r i i.castSucc = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [coordinateRatio_val, CycleQ2SeedFermatProj.geometricWeight_castSucc, pow_one]
  exact (IsLocalization.Away.mul_invSelf (familyCoordinate r i.castSucc)).trans
    HomogeneousLocalization.val_one.symm

private theorem weighted_eval_scale {S : Type*} [CommRing S]
    (f : ParameterRing →+* S) (x : Fin 5 → S) (c : S) (p : FamilyPolynomial) (n : ℕ)
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

def projectiveEvaluate (r : ℂ) (i : Fin 4) : FamilyPolynomial →+* ChartRing r i :=
  eval₂Hom (chartCoefficient r i) (coordinateRatio r i)

theorem projectiveEvaluate_homogeneousFraction (r : ℂ) (i : Fin 4)
    (n : ℕ) (p : FamilyPolynomial) (hp : p.IsWeightedHomogeneous geometricWeight n) :
    projectiveEvaluate r i p = homogeneousFraction r i n p hp := by
  let F : FamilyPolynomial →+* CoordinateRing r i :=
    (algebraMap (FamilyRing r) (CoordinateRing r i)).comp (familyQuotient r)
  have heval : eval₂Hom (F.comp C) (fun j => F (X j)) = F := by
    apply MvPolynomial.ringHom_ext <;> intro x <;> simp
  have hcomp :
      (algebraMap (ChartRing r i) (CoordinateRing r i)).comp (projectiveEvaluate r i) =
        eval₂Hom (F.comp C) (fun j =>
          IsLocalization.Away.invSelf (familyCoordinate r i.castSucc) ^
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
  change ((algebraMap (ChartRing r i) (CoordinateRing r i)).comp
    (projectiveEvaluate r i)) p = _
  rw [hcomp, weighted_eval_scale (F.comp C) (fun j => F (X j))
    (IsLocalization.Away.invSelf (familyCoordinate r i.castSucc)) p n hp,
    heval, homogeneousFraction_val]
  exact mul_comm _ _

theorem projectiveEvaluate_familyEquation (r : ℂ) (i : Fin 4) :
    projectiveEvaluate r i (familyEquation r) = 0 := by
  rw [projectiveEvaluate_homogeneousFraction r i 6 (familyEquation r)
    (familyEquation_homogeneous r)]
  apply HomogeneousLocalization.val_injective
  simp only [homogeneousFraction_val, familyEquation_zero, map_zero, zero_mul,
    HomogeneousLocalization.val_zero]

/-- The native inclusion preserves the original parameter coefficients. -/
def chartInclusion (r : ℂ) (i : Fin 4) :
    ChartRing r i →ₐ[ParameterRing] CoordinateRing r i where
  toRingHom := algebraMap (ChartRing r i) (CoordinateRing r i)
  commutes' c := by
    change (chartCoefficient r i c).val = algebraMap ParameterRing (CoordinateRing r i) c
    rw [chartCoefficient_val]
    exact (IsScalarTower.algebraMap_apply ParameterRing (FamilyRing r)
      (CoordinateRing r i) c).symm

end CycleQ2SeedFamilyChart

end

#print axioms CycleQ2SeedFamilyChart.projectiveEvaluate_homogeneousFraction
#print axioms CycleQ2SeedFamilyChart.projectiveEvaluate_familyEquation
