import Proposal.GeometricTraceBoundary
import Mathlib.Data.Finsupp.Weight

/-!
# Arbitrary homogeneous poles in the actual curve Cech quotient

The sparse four-generator quotient has no homogeneous components above
degree nine. The proof uses the existing degree-nine calculation and
proves that each coordinate annihilates its actual normalization class.
This is used to reduce arbitrary homogeneous overlap sections to the
degree-nine simple-pole image. All localization and homogeneous-section
objects are the existing objects of `GeometricDegreeOneCech`.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2GeometricCechPoleReduction

open MvPolynomial CycleQ2SeedTrace CycleQ2SeedCechTheta CycleQ2NormalConnecting
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricKoszulTrace

private theorem mon_class (r : ℂ) (hr : r ^ 3 = 2) (a b c d : ℕ)
    (hn : a + b + c + d = 9) :
    reducedQuotient r (mon a b c d) = traceValue r a b c d • normalizationClass r := by
  have hp : (mon a b c d).IsHomogeneous 9 := hn ▸ mon_homogeneous a b c d
  have h := degreeNine_class_eq_trace_smul r hr
    (show reducedQuotient r (mon a b c d) ∈ degreeNinePiece r from ⟨_, hp, rfl⟩)
  simpa only [reducedTrace_mk, traceLinear_mon] using h

private theorem x0_mul_normalization (r : ℂ) (hr : r ^ 3 = 2) :
    reducedQuotient r (X 0) * normalizationClass r = 0 := by
  have hnonzero : -(r ^ 2 / 6) ≠ (0 : ℂ) := by
    have hr0 : r ≠ 0 := by intro h; simp [h] at hr
    exact neg_ne_zero.mpr (div_ne_zero (pow_ne_zero 2 hr0) (by norm_num))
  have hq : reducedQuotient r (mon 1 7 0 1) =
      (-(r ^ 2 / 6)) • normalizationClass r := by
    have ht : traceValue r 1 7 0 1 = -(r ^ 2 / 6) := by
      norm_num [traceValue]
      ring
    simpa only [ht] using mon_class r hr 1 7 0 1 (by norm_num)
  have hz : reducedQuotient r (X 0) * reducedQuotient r (mon 1 7 0 1) = 0 := by
    rw [← map_mul]
    have heq : (X 0 : Poly) * mon 1 7 0 1 = mon 2 7 0 1 := by simp [mon]; ring
    rw [heq]
    change reducedQuotient r (mon (0 + 2) 7 0 1) = 0
    rw [quotient_mon_add_two]
    have hzero : reducedQuotient r (mon 0 8 0 2) = 0 :=
      quotient_mon_bd_add_two_zero r 0 6 0 0
    rw [hzero, smul_zero]
  rw [hq, mul_smul_comm] at hz
  exact (smul_eq_zero.mp hz).resolve_left hnonzero

/-- Every coordinate annihilates the actual nonzero degree-nine class.
No assertion about a geometric trace is used here. -/
theorem coordinate_mul_normalization (r : ℂ) (hr : r ^ 3 = 2) (i : Fin 4) :
    reducedQuotient r (X i) * normalizationClass r = 0 := by
  have hx0 := x0_mul_normalization r hr
  have hx1 : reducedQuotient r (X 1) * normalizationClass r = 0 := by
    have hq : reducedQuotient r (mon 0 9 0 0) =
        (-(4 * Complex.I / 3)) • normalizationClass r := by
      have ht : traceValue r 0 9 0 0 = -(4 * Complex.I / 3) := by
        norm_num [traceValue]
        ring
      simpa only [ht] using mon_class r hr 0 9 0 0 (by norm_num)
    calc
      reducedQuotient r (X 1) * normalizationClass r =
          reducedQuotient r (X 0) * reducedQuotient r (mon 0 9 0 0) := by
        unfold normalizationClass
        rw [← map_mul, ← map_mul]
        apply congrArg (reducedQuotient r)
        simp only [mon, pow_zero, pow_one, mul_one]
        ring
      _ = 0 := by rw [hq, mul_smul_comm, hx0, smul_zero]
  have hx2 : reducedQuotient r (X 2) * normalizationClass r = 0 := by
    have hq : reducedQuotient r (mon 0 8 1 0) = 0 := by
      simpa [traceValue] using mon_class r hr 0 8 1 0 (by norm_num)
    calc
      reducedQuotient r (X 2) * normalizationClass r =
          reducedQuotient r (X 0) * reducedQuotient r (mon 0 8 1 0) := by
        unfold normalizationClass
        rw [← map_mul, ← map_mul]
        apply congrArg (reducedQuotient r)
        simp only [mon, pow_zero, pow_one, mul_one]
        ring
      _ = 0 := by rw [hq, mul_zero]
  have hx3 : reducedQuotient r (X 3) * normalizationClass r = 0 := by
    have hq : reducedQuotient r (mon 1 7 0 1) =
        (-(r ^ 2 / 6)) • normalizationClass r := by
      have ht : traceValue r 1 7 0 1 = -(r ^ 2 / 6) := by
        norm_num [traceValue]
        ring
      simpa only [ht] using mon_class r hr 1 7 0 1 (by norm_num)
    calc
      reducedQuotient r (X 3) * normalizationClass r =
          reducedQuotient r (X 1) * reducedQuotient r (mon 1 7 0 1) := by
        unfold normalizationClass
        rw [← map_mul, ← map_mul]
        apply congrArg (reducedQuotient r)
        simp only [mon, pow_zero, pow_one, mul_one]
        ring
      _ = 0 := by rw [hq, mul_smul_comm, hx1, smul_zero]
  fin_cases i
  · exact hx0
  · exact hx1
  · exact hx2
  · exact hx3

private theorem positive_monomial_mul_normalization (r : ℂ) (hr : r ^ 3 = 2)
    (d : Fin 4 →₀ ℕ) (hd : 0 < d.degree) (z : ℂ) :
    reducedQuotient r (monomial d z) * normalizationClass r = 0 := by
  classical
  have hd0 : d ≠ 0 := by intro h; simp [h] at hd
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hd0
  have hle : Finsupp.single i 1 ≤ d :=
    Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))
  have heq : d = Finsupp.single i 1 + (d - Finsupp.single i 1) :=
    (add_tsub_cancel_of_le hle).symm
  have hmon : monomial d z = (X i : Poly) * monomial (d - Finsupp.single i 1) z := by
    rw [X, monomial_mul, one_mul, ← heq]
  rw [hmon, map_mul, mul_right_comm, coordinate_mul_normalization r hr i, zero_mul]

/-- The actual sparse quotient has no homogeneous components above its
degree-nine normalization class. This is an ideal-membership statement
for every polynomial, not a bounded list of tested monomials. -/
theorem homogeneous_mem_reducedIdeal_of_degree_gt_nine
    (r : ℂ) (hr : r ^ 3 = 2) {n : ℕ} (hn : 9 < n)
    {p : Poly} (hp : p.IsHomogeneous n) : p ∈ reducedIdeal r := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change reducedQuotient r p = 0
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => exact map_zero _
  | add p q _ _ hp hq => rw [map_add, hp, hq, add_zero]
  | monomial d z hd =>
      have hdegree : d.degree = n := by
        simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hd
      obtain ⟨e, hed, he⟩ := Finsupp.exists_le_degree_eq d 9 (by omega)
      have hsplit : d = (d - e) + e := (tsub_add_cancel_of_le hed).symm
      have hpositive : 0 < (d - e).degree := by
        have hs : d.degree = (d - e).degree + e.degree := by
          simpa only [map_add] using congrArg Finsupp.degree hsplit
        omega
      have hehom : (monomial e (1 : ℂ)).IsHomogeneous 9 := isHomogeneous_monomial _ he
      have hclass := degreeNine_class_eq_trace_smul r hr
        (show reducedQuotient r (monomial e (1 : ℂ)) ∈ degreeNinePiece r from
          ⟨_, hehom, rfl⟩)
      have hmon : monomial d z = monomial (d - e) z * monomial e (1 : ℂ) := by
        rw [monomial_mul, mul_one, ← hsplit]
      rw [hmon, map_mul, hclass, mul_smul_comm,
        positive_monomial_mul_normalization r hr (d - e) hpositive z, smul_zero]

end CycleQ2GeometricCechPoleReduction

end
