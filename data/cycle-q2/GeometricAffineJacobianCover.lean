import Proposal.GeometricSeedCurveGradientArithmetic
import Proposal.GeometricAdjunctionOverlap
import Proposal.GeometricKaehlerResidue
import Mathlib.RingTheory.Ideal.Operations

/-!
# The actual affine Jacobian opens cover the literal seed

For the seed `(r, θ) = (57, 1)`, the two affine complete intersections
have unit Jacobian-minor ideals. The proof specializes the existing exact
homogeneous gradient certificates at `x1 = 1` and `x2 = 1`. Euler's identities
express the minors involving the deleted column in terms of the affine
minors and the two equations. The latter vanish in the actual chart quotient.

Consequently every prime of either actual affine chart misses one of its
Jacobian minors. The final statements select the corresponding actual
`chartPresentation`, so the existing `JacobianPatch` and `smoothPresentation`
apply on a proved cover. No pointwise smoothness hypothesis, root-of-two
substitution, or identification of the parameters `θ = 0` and `θ = 1` is used.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2GeometricAffineJacobianCover

open MvPolynomial CycleQ2GeometricAffineCurveCharts
  CycleQ2GeometricAdjunctionOverlap
open scoped BigOperators

/-- A two-column determinant of two differential rows. -/
def rowMinor {R : Type*} [CommRing R] (u v : Fin 3 → R) (j k : Fin 3) : R :=
  u j * v k - u k * v j

/-- The actual polynomial Jacobian minor, in the actual affine quotient. -/
def minor (v : Fin 2 → AffinePoly) (j k : Fin 3) : ChartRing v :=
  Ideal.Quotient.mk (chartIdeal v)
    (pderiv j (v 0) * pderiv k (v 1) - pderiv k (v 0) * pderiv j (v 1))

/-- All ordered pairs are included; repeated columns simply contribute zero. -/
def jacobianIdeal (v : Fin 2 → AffinePoly) : Ideal (ChartRing v) :=
  Ideal.span (Set.range (fun jk : Fin 3 × Fin 3 => minor v jk.1 jk.2))

section Algebra
variable {R : Type*} [CommRing R]

private theorem first_generator_formula (i a b c : R) :
    let q := quadricOne 57 a b c
    let h := cubicOne i 1 a b c
    let u := gradQuadricOne 57 a
    let v := gradCubicOne i 1 a b c
    CycleQ2SeedCurveGradientArithmetic.generators i a 1 b c =
      ![q, h,
        3 * h * u 0 - 2 * q * v 0 - b * rowMinor u v 0 1 - c * rowMinor u v 0 2,
        rowMinor u v 0 1,
        rowMinor u v 0 2,
        2 * q * v 1 - 3 * h * u 1 - a * rowMinor u v 0 1 + c * rowMinor u v 1 2,
        2 * q * v 2 - 3 * h * u 2 - a * rowMinor u v 0 2 - b * rowMinor u v 1 2,
        rowMinor u v 1 2] := by
  dsimp only
  funext k
  fin_cases k <;>
    simp [CycleQ2SeedCurveGradientArithmetic.generators, quadricOne, cubicOne,
      gradQuadricOne, gradCubicOne, rowMinor] <;> ring

private theorem second_generator_formula (i a b c : R) :
    let q := quadricTwo 57 a b c
    let h := cubicTwo i 1 a b c
    let u := gradQuadricTwo 57 a b c
    let v := gradCubicTwo i 1 a b c
    CycleQ2SeedCurveGradientArithmetic.generators i a b 1 c =
      ![q, h,
        rowMinor u v 0 1,
        3 * h * u 0 - 2 * q * v 0 - b * rowMinor u v 0 1 - c * rowMinor u v 0 2,
        rowMinor u v 0 2,
        3 * h * u 1 - 2 * q * v 1 + a * rowMinor u v 0 1 - c * rowMinor u v 1 2,
        rowMinor u v 1 2,
        2 * q * v 2 - 3 * h * u 2 - a * rowMinor u v 0 2 - b * rowMinor u v 1 2] := by
  dsimp only
  funext k
  fin_cases k <;>
    simp [CycleQ2SeedCurveGradientArithmetic.generators, quadricTwo, cubicTwo,
      gradQuadricTwo, gradCubicTwo, rowMinor] <;> ring

private theorem first_generators_mem (J : Ideal R) (i a b c : R)
    (hq : quadricOne 57 a b c = 0) (hh : cubicOne i 1 a b c = 0)
    (hm : ∀ j k, rowMinor (gradQuadricOne 57 a) (gradCubicOne i 1 a b c) j k ∈ J)
    (k : Fin 8) : CycleQ2SeedCurveGradientArithmetic.generators i a 1 b c k ∈ J := by
  have hform := congrFun (first_generator_formula i a b c) k
  simp only [hq, hh, mul_zero, zero_mul, zero_sub, sub_zero] at hform
  rw [hform]
  fin_cases k
  · exact J.zero_mem
  · exact J.zero_mem
  · exact J.sub_mem (J.neg_mem (J.mul_mem_left b (hm 0 1)))
      (J.mul_mem_left c (hm 0 2))
  · exact hm 0 1
  · exact hm 0 2
  · exact J.add_mem (J.neg_mem (J.mul_mem_left a (hm 0 1)))
      (J.mul_mem_left c (hm 1 2))
  · exact J.sub_mem (J.neg_mem (J.mul_mem_left a (hm 0 2)))
      (J.mul_mem_left b (hm 1 2))
  · exact hm 1 2

private theorem second_generators_mem (J : Ideal R) (i a b c : R)
    (hq : quadricTwo 57 a b c = 0) (hh : cubicTwo i 1 a b c = 0)
    (hm : ∀ j k, rowMinor (gradQuadricTwo 57 a b c) (gradCubicTwo i 1 a b c) j k ∈ J)
    (k : Fin 8) : CycleQ2SeedCurveGradientArithmetic.generators i a b 1 c k ∈ J := by
  have hform := congrFun (second_generator_formula i a b c) k
  simp only [hq, hh, mul_zero, zero_mul, zero_sub, sub_zero, zero_add] at hform
  rw [hform]
  fin_cases k
  · exact J.zero_mem
  · exact J.zero_mem
  · exact hm 0 1
  · exact J.sub_mem (J.neg_mem (J.mul_mem_left b (hm 0 1)))
      (J.mul_mem_left c (hm 0 2))
  · exact hm 0 2
  · exact J.sub_mem (J.mul_mem_left a (hm 0 1)) (J.mul_mem_left c (hm 1 2))
  · exact hm 1 2
  · exact J.sub_mem (J.neg_mem (J.mul_mem_left a (hm 0 2)))
      (J.mul_mem_left b (hm 1 2))

private theorem first_minors_unit_ideal (φ : ℂ →+* R) (a b c : R) (J : Ideal R)
    (hq : quadricOne 57 a b c = 0) (hh : cubicOne (φ Complex.I) 1 a b c = 0)
    (hm : ∀ j k,
      rowMinor (gradQuadricOne 57 a) (gradCubicOne (φ Complex.I) 1 a b c) j k ∈ J) :
    J = ⊤ := by
  have hi : (φ Complex.I) ^ 2 + 1 = 0 := by
    simpa only [map_add, map_pow, map_one, map_zero] using
      congrArg φ (show Complex.I ^ 2 + 1 = 0 by simp)
  have hcert := CycleQ2SeedCurveGradientArithmetic.identity1 (φ Complex.I) a 1 b c hi
  simp only [one_pow, mul_one] at hcert
  have hmem :
      (6059424584881633543806844729000010994813153255561185835799340535703920806958867401340 : R)
        ∈ J := by
    rw [hcert]
    exact J.sum_mem fun k _ => J.mul_mem_left _ (first_generators_mem J _ a b c hq hh hm k)
  have hu : IsUnit
      (6059424584881633543806844729000010994813153255561185835799340535703920806958867401340 : ℂ) :=
    isUnit_iff_ne_zero.mpr (by norm_num)
  exact J.eq_top_of_isUnit_mem hmem (by simpa only [map_ofNat] using hu.map φ)

private theorem second_minors_unit_ideal (φ : ℂ →+* R) (a b c : R) (J : Ideal R)
    (hq : quadricTwo 57 a b c = 0) (hh : cubicTwo (φ Complex.I) 1 a b c = 0)
    (hm : ∀ j k,
      rowMinor (gradQuadricTwo 57 a b c) (gradCubicTwo (φ Complex.I) 1 a b c) j k ∈ J) :
    J = ⊤ := by
  have hi : (φ Complex.I) ^ 2 + 1 = 0 := by
    simpa only [map_add, map_pow, map_one, map_zero] using
      congrArg φ (show Complex.I ^ 2 + 1 = 0 by simp)
  have hcert := CycleQ2SeedCurveGradientArithmetic.identity2 (φ Complex.I) a b 1 c hi
  simp only [one_pow, mul_one] at hcert
  have hmem :
      (12118849169763267087613689458000021989626306511122371671598681071407841613917734802680 : R)
        ∈ J := by
    rw [hcert]
    exact J.sum_mem fun k _ => J.mul_mem_left _ (second_generators_mem J _ a b c hq hh hm k)
  have hu : IsUnit
      (12118849169763267087613689458000021989626306511122371671598681071407841613917734802680 : ℂ) :=
    isUnit_iff_ne_zero.mpr (by norm_num)
  exact J.eq_top_of_isUnit_mem hmem (by simpa only [map_ofNat] using hu.map φ)

private theorem first_rowMinor_map (π : AffinePoly →+* R) (j k : Fin 3) :
    π (pderiv j (firstQuadric 57) * pderiv k (firstCubic 1) -
      pderiv k (firstQuadric 57) * pderiv j (firstCubic 1)) =
      rowMinor (gradQuadricOne 57 (π (X 0)))
        (gradCubicOne (π (C Complex.I)) 1 (π (X 0)) (π (X 1)) (π (X 2))) j k := by
  have hq : (fun l => π (pderiv l (firstQuadric 57))) =
      gradQuadricOne 57 (π (X 0)) := by
    funext l
    rw [congrFun (firstQuadric_gradient 57) l]
    fin_cases l <;> simp [gradQuadricOne, map_ofNat]
  have hh : (fun l => π (pderiv l (firstCubic 1))) =
      gradCubicOne (π (C Complex.I)) 1 (π (X 0)) (π (X 1)) (π (X 2)) := by
    funext l
    rw [congrFun (firstCubic_gradient 1) l]
    fin_cases l <;> simp [gradCubicOne, map_ofNat]
  simp only [map_sub, map_mul, rowMinor, congrFun hq j, congrFun hq k,
    congrFun hh j, congrFun hh k]

private theorem second_rowMinor_map (π : AffinePoly →+* R) (j k : Fin 3) :
    π (pderiv j (secondQuadric 57) * pderiv k (secondCubic 1) -
      pderiv k (secondQuadric 57) * pderiv j (secondCubic 1)) =
      rowMinor (gradQuadricTwo 57 (π (X 0)) (π (X 1)) (π (X 2)))
        (gradCubicTwo (π (C Complex.I)) 1 (π (X 0)) (π (X 1)) (π (X 2))) j k := by
  have hq : (fun l => π (pderiv l (secondQuadric 57))) =
      gradQuadricTwo 57 (π (X 0)) (π (X 1)) (π (X 2)) := by
    funext l
    rw [congrFun (secondQuadric_gradient 57) l]
    fin_cases l <;> simp [gradQuadricTwo, map_ofNat]
  have hh : (fun l => π (pderiv l (secondCubic 1))) =
      gradCubicTwo (π (C Complex.I)) 1 (π (X 0)) (π (X 1)) (π (X 2)) := by
    funext l
    rw [congrFun (secondCubic_gradient 1) l]
    fin_cases l <;> simp [gradCubicTwo, map_ofNat]
  simp only [map_sub, map_mul, rowMinor, congrFun hq j, congrFun hq k,
    congrFun hh j, congrFun hh k]

end Algebra

/-- The first affine chart of the literal `(57, 1)` seed is covered by its
actual Jacobian opens. This is an equality of ideals in its actual quotient. -/
theorem first_jacobianIdeal_eq_top :
    jacobianIdeal ![firstQuadric 57, firstCubic 1] = ⊤ := by
  let v : Fin 2 → AffinePoly := ![firstQuadric 57, firstCubic 1]
  let π := Ideal.Quotient.mk (chartIdeal v)
  have hz (k : Fin 2) : π (v k) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨k, rfl⟩)
  have hq : π (firstQuadric 57) = 0 := hz 0
  have hh : π (firstCubic 1) = 0 := hz 1
  apply first_minors_unit_ideal (π.comp C) (π (X 0)) (π (X 1)) (π (X 2))
  · simpa only [firstQuadric, quadricOne, map_sub, map_pow, map_mul, map_ofNat] using hq
  · simpa only [firstCubic, cubicOne, map_add, map_sub, map_pow, map_mul,
      map_one, RingHom.comp_apply] using hh
  · intro j k
    simp only [RingHom.comp_apply]
    rw [← first_rowMinor_map π j k]
    exact Ideal.subset_span ⟨(j, k), rfl⟩

/-- The same unit-ideal statement for the second affine chart, with the
same literal parameters and no assumed smoothness. -/
theorem second_jacobianIdeal_eq_top :
    jacobianIdeal ![secondQuadric 57, secondCubic 1] = ⊤ := by
  let v : Fin 2 → AffinePoly := ![secondQuadric 57, secondCubic 1]
  let π := Ideal.Quotient.mk (chartIdeal v)
  have hz (k : Fin 2) : π (v k) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨k, rfl⟩)
  have hq : π (secondQuadric 57) = 0 := hz 0
  have hh : π (secondCubic 1) = 0 := hz 1
  apply second_minors_unit_ideal (π.comp C) (π (X 0)) (π (X 1)) (π (X 2))
  · simpa only [secondQuadric, quadricTwo, map_sub, map_pow, map_mul, map_ofNat] using hq
  · simpa only [secondCubic, cubicTwo, map_add, map_sub, map_pow, map_mul,
      map_one, RingHom.comp_apply] using hh
  · intro j k
    simp only [RingHom.comp_apply]
    rw [← second_rowMinor_map π j k]
    exact Ideal.subset_span ⟨(j, k), rfl⟩

private theorem prime_minor_cover (v : Fin 2 → AffinePoly)
    (h : jacobianIdeal v = ⊤) (Q : Ideal (ChartRing v)) [Q.IsPrime] :
    ∃ j k, minor v j k ∉ Q := by
  by_contra hn
  push Not at hn
  have hle : jacobianIdeal v ≤ Q := by
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨j, k⟩, rfl⟩
    exact hn j k
  rw [h] at hle
  exact (inferInstance : Q.IsPrime).ne_top (top_unique hle)

/-- The cover holds at every prime, including nonclosed points. -/
theorem first_prime_minor_cover
    (Q : Ideal (ChartRing ![firstQuadric 57, firstCubic 1])) [Q.IsPrime] :
    ∃ j k, minor ![firstQuadric 57, firstCubic 1] j k ∉ Q :=
  prime_minor_cover _ first_jacobianIdeal_eq_top Q

/-- Every prime of the second actual chart lies in a Jacobian open. -/
theorem second_prime_minor_cover
    (Q : Ideal (ChartRing ![secondQuadric 57, secondCubic 1])) [Q.IsPrime] :
    ∃ j k, minor ![secondQuadric 57, secondCubic 1] j k ∉ Q :=
  prime_minor_cover _ second_jacobianIdeal_eq_top Q

private theorem exists_pivot_permutation (j k : Fin 3) (h : j ≠ k) :
    ∃ e : Equiv.Perm (Fin 3), e 1 = j ∧ e 2 = k := by
  fin_cases j <;> fin_cases k
  · exact (h rfl).elim
  · exact ⟨(Equiv.swap 0 2).trans (Equiv.swap 0 1), by decide, by decide⟩
  · exact ⟨Equiv.swap 0 1, by decide, by decide⟩
  · exact ⟨Equiv.swap 0 2, by decide, by decide⟩
  · exact (h rfl).elim
  · exact ⟨Equiv.refl (Fin 3), by decide, by decide⟩
  · exact ⟨(Equiv.swap 0 1).trans (Equiv.swap 0 2), by decide, by decide⟩
  · exact ⟨Equiv.swap 1 2, by decide, by decide⟩
  · exact (h rfl).elim

private theorem prime_presentation_cover (v : Fin 2 → AffinePoly)
    (h : jacobianIdeal v = ⊤) (Q : Ideal (ChartRing v)) [Q.IsPrime] :
    ∃ e : Equiv.Perm (Fin 3), (chartPresentation v e).jacobian ∉ Q := by
  obtain ⟨j, k, hjk⟩ := prime_minor_cover v h Q
  have hne : j ≠ k := by
    rintro rfl
    apply hjk
    simp [minor]
  obtain ⟨e, he1, he2⟩ := exists_pivot_permutation j k hne
  refine ⟨e, ?_⟩
  have hpoly :
      pderiv (e 1) (v 0) * pderiv (e 2) (v 1) -
          pderiv (e 1) (v 1) * pderiv (e 2) (v 0) =
        pderiv j (v 0) * pderiv k (v 1) - pderiv k (v 0) * pderiv j (v 1) := by
    rw [he1, he2]
    ring
  have hdet : (chartPresentation v e).jacobian = minor v j k :=
    (CycleQ2GeometricKaehlerResidue.chartPresentation_jacobian v e).trans
      (congrArg (fun p : AffinePoly => Ideal.Quotient.mk (chartIdeal v) p) hpoly)
  rw [hdet]
  exact hjk

/-- Every prime of the first literal seed chart belongs to one of the actual
`JacobianPatch` opens used by the constructed submersive presentations. -/
theorem first_prime_presentation_cover
    (Q : Ideal (ChartRing ![firstQuadric 57, firstCubic 1])) [Q.IsPrime] :
    ∃ e : Equiv.Perm (Fin 3),
      (chartPresentation ![firstQuadric 57, firstCubic 1] e).jacobian ∉ Q :=
  prime_presentation_cover _ first_jacobianIdeal_eq_top Q

/-- The corresponding actual smooth-presentation cover of the second chart. -/
theorem second_prime_presentation_cover
    (Q : Ideal (ChartRing ![secondQuadric 57, secondCubic 1])) [Q.IsPrime] :
    ∃ e : Equiv.Perm (Fin 3),
      (chartPresentation ![secondQuadric 57, secondCubic 1] e).jacobian ∉ Q :=
  prime_presentation_cover _ second_jacobianIdeal_eq_top Q

end CycleQ2GeometricAffineJacobianCover

end
