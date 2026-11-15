import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# A lower-degree class cannot be a multiple of a higher-degree class

This elementary graded-quotient argument uses nonnegative variable weights.
It does not assume that the quotient ring is a domain or that the multiplier
is homogeneous. In the seed application the two degrees are 10 and 14.

Source-only draft. Not elaborated, compiled, or kernel-replayed.
Prepared for fqlx with OpenAI ChatGPT assistance, 15 November 2026.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2SectionDegreeGap

open MvPolynomial

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {R σ : Type*} [CommRing R]

/-- Every coefficient below the weight of a homogeneous factor vanishes. -/
theorem coeff_mul_eq_zero_below (w : σ → ℕ) (f p : MvPolynomial σ R)
    (m : ℕ) (hf : f.IsWeightedHomogeneous w m)
    (d : σ →₀ ℕ) (hd : Finsupp.weight w d < m) :
    (f * p).coeff d = 0 := by
  classical
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro ab hab
  by_cases ha : f.coeff ab.1 = 0
  · rw [ha, zero_mul]
  · have hweight := hf ha
    have he : ab.1 + ab.2 = d := Finset.mem_antidiagonal.mp hab
    have hadd : Finsupp.weight w ab.1 + Finsupp.weight w ab.2 =
        Finsupp.weight w d := by
      rw [← map_add, he]
    have hle : m ≤ Finsupp.weight w d := by
      rw [← hadd, hweight]
      exact Nat.le_add_right m _
    exact (not_le_of_gt hd hle).elim

/-- No nonnegative-degree multiplier can create a lower weighted component. -/
theorem component_mul_eq_zero_below (w : σ → ℕ) (f p : MvPolynomial σ R)
    (m n : ℕ) (hf : f.IsWeightedHomogeneous w m) (hn : n < m) :
    weightedHomogeneousComponent w n (f * p) = 0 := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [coeff_weightedHomogeneousComponent, coeff_zero]
  by_cases hd : Finsupp.weight w d = n
  · rw [if_pos hd]
    exact coeff_mul_eq_zero_below w f p m hf d (by simpa only [hd] using hn)
  · rw [if_neg hd]

/-- In a homogeneous quotient, an equation `f*p = l` with `deg l < deg f`
forces the class of `l` to vanish. The multiplier is completely unrestricted. -/
theorem lower_class_zero_of_multiple (w : σ → ℕ)
    (I : Ideal (MvPolynomial σ R))
    (hI : I.IsHomogeneous (weightedHomogeneousSubmodule R w))
    (f p l : MvPolynomial σ R) (m n : ℕ)
    (hf : f.IsWeightedHomogeneous w m)
    (hl : l.IsWeightedHomogeneous w n) (hn : n < m)
    (h : Ideal.Quotient.mk I f * Ideal.Quotient.mk I p =
      Ideal.Quotient.mk I l) :
    Ideal.Quotient.mk I l = 0 := by
  have hmem : f * p - l ∈ I := Ideal.Quotient.eq.mp (by
    simpa only [map_mul] using h)
  have hc := weightedHomogeneousComponent_mem_of_mem R w hI hmem n
  rw [map_sub, component_mul_eq_zero_below w f p m n hf hn,
    weightedHomogeneousComponent_eq_self hl, zero_sub] at hc
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  simpa only [neg_neg] using I.neg_mem hc

end CycleQ2SectionDegreeGap

end

#print axioms CycleQ2SectionDegreeGap.lower_class_zero_of_multiple
