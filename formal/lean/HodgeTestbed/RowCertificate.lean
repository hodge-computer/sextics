import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Int.Cast.Lemmas

/-!
# Exact finite-row obstructions

A row functional which kills every correction column but not the target
prevents a solution. Integer witnesses remain valid over every field of
characteristic zero. Concrete source-coefficient identification is separate.
This is a certificate-oriented wrapper around finite-sum linear algebra,
not a change to HodgeComputer.Verify or an instance solve.
Developed with OpenAI Codex assistance in rbajaj5/hodge-lab.
-/

open scoped BigOperators

namespace HodgeTestbed

/-- A finite left-annihilator certificate rules out the corresponding linear
equations. No rank computation or independence assumption is required. -/
theorem no_solution_of_row_certificate
    {R C K : Type*} [Fintype R] [Fintype C] [CommRing K]
    (matrix : R → C → K) (target dual : R → K)
    (annihilates : ∀ c, ∑ r, dual r * matrix r c = 0)
    (separates : ∑ r, dual r * target r ≠ 0) :
    ¬ ∃ coefficients : C → K,
      ∀ r, ∑ c, matrix r c * coefficients c = target r := by
  rintro ⟨coefficients, equations⟩
  apply separates
  calc
    ∑ r, dual r * target r =
        ∑ r, dual r * (∑ c, matrix r c * coefficients c) := by
          simp only [equations]
    _ = ∑ c, (∑ r, dual r * matrix r c) * coefficients c := by
          simp_rw [Finset.mul_sum, ← mul_assoc]
          rw [Finset.sum_comm]
          simp only [Finset.sum_mul]
    _ = 0 := by simp only [annihilates, zero_mul, Finset.sum_const_zero]

/-- Kernel-checked integer cancellations imply an obstruction over every
characteristic-zero field, including the rationals and complex numbers. -/
theorem no_solution_of_integer_row_certificate
    {R C K : Type*} [Fintype R] [Fintype C] [Field K] [CharZero K]
    (matrix : R → C → ℤ) (target dual : R → ℤ)
    (annihilates : ∀ c, ∑ r, dual r * matrix r c = 0)
    (separates : ∑ r, dual r * target r ≠ 0) :
    ¬ ∃ coefficients : C → K,
      ∀ r, ∑ c, (matrix r c : K) * coefficients c = (target r : K) := by
  apply no_solution_of_row_certificate
      (fun r c => (matrix r c : K)) (fun r => (target r : K))
      (fun r => (dual r : K))
  · intro c
    have equality := congrArg (fun z : ℤ => (z : K)) (annihilates c)
    simpa only [Int.cast_sum, Int.cast_mul, Int.cast_zero] using equality
  · have nonzero : ((∑ r, dual r * target r : ℤ) : K) ≠ 0 :=
        Int.cast_ne_zero.mpr separates
    simpa only [Int.cast_sum, Int.cast_mul] using nonzero

end HodgeTestbed
