import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-! Projection to one weighted degree commutes with multiplication by a
homogeneous polynomial, after shifting the requested degree. -/

namespace MvPolynomial

open Finsupp

theorem weightedComponent_mul_homogeneous
    {R σ M : Type*} [CommSemiring R] [AddCancelCommMonoid M]
    (w : σ → M) {g : MvPolynomial σ R} {m : M}
    (hg : g.IsWeightedHomogeneous w m) (k : M) (p : MvPolynomial σ R) :
    weightedHomogeneousComponent w (k + m) (p * g) =
      weightedHomogeneousComponent w k p * g := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d a =>
    have hd : (monomial d a).IsWeightedHomogeneous w (weight w d) :=
      isWeightedHomogeneous_monomial w d a rfl
    by_cases h : weight w d = k
    · subst k
      rw [(hd.mul hg).weightedHomogeneousComponent_same,
        hd.weightedHomogeneousComponent_same]
    · have hn : k + m ≠ weight w d + m := by
        intro hh
        exact h (add_right_cancel hh).symm
      rw [(hd.mul hg).weightedHomogeneousComponent_ne (k + m) hn,
        hd.weightedHomogeneousComponent_ne k (Ne.symm h), zero_mul]
  | add p q hp hq =>
    simp only [add_mul, map_add, hp, hq]

end MvPolynomial
