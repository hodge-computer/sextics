import Proposal.GeometricCommonFractionDenominator
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Eval.Coeff

/-!
# One denominator clears every coefficient of a polynomial over Frac(R)

This is a direct algebraic spreading input for the finite primitive minimal
polynomial of the cycle-q2 parameter field extension. The leading polynomial
and all its coefficients are the actual ones over Frac(R). The theorem gives
a nonzero denominator and a polynomial in R[X] mapping to that denominator
times the original polynomial. It avoids a hand-selected degree cutoff and
handles every coefficient via the polynomial's finite support.

No assumption or conclusion concerns etaleness of the resulting relative
scheme or extension of the Hilbert parameter morphism; those require the
separability/Bézout data, localization, and geometric binding separately.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

open Polynomial

namespace CycleQ2PolynomialDenominator

variable {R : Type*} [CommRing R] [IsDomain R]

/-- There is a *single* nonzero denominator and a polynomial with all
coefficients in R, whose image is the cleared original rational polynomial.
This is an equation in the actual polynomial ring over Frac(R). -/
theorem exists_cleared_polynomial (p : Polynomial (FractionRing R)) :
    ∃ b : R, b ≠ 0 ∧ ∃ q : Polynomial R,
      p * C (algebraMap R (FractionRing R) b) =
        q.map (algebraMap R (FractionRing R)) := by
  classical
  obtain ⟨b, hb, h⟩ :=
    CycleQ2CommonFractionDenominator.exists_finset_common_denominator
      (fun i => p.coeff i) p.support
  let numerator : ℕ → R := fun i =>
    if hi : i ∈ p.support then Classical.choose (h i hi) else 0
  have hnum (i : ℕ) (hi : i ∈ p.support) :
      p.coeff i * algebraMap R (FractionRing R) b =
        algebraMap R (FractionRing R) (numerator i) := by
    simpa only [numerator, dif_pos hi] using Classical.choose_spec (h i hi)
  let q : Polynomial R := ∑ i ∈ p.support, monomial i (numerator i)
  refine ⟨b, hb, q, ?_⟩
  calc
    p * C (algebraMap R (FractionRing R) b) =
        (∑ i ∈ p.support, monomial i (p.coeff i)) *
          C (algebraMap R (FractionRing R) b) := by rw [← p.as_sum_support]
    _ = ∑ i ∈ p.support,
          monomial i (p.coeff i * algebraMap R (FractionRing R) b) := by
            simp only [Finset.sum_mul, monomial_mul_C]
    _ = ∑ i ∈ p.support,
          monomial i (algebraMap R (FractionRing R) (numerator i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hnum i hi]
    _ = q.map (algebraMap R (FractionRing R)) := by
            simp only [q, Polynomial.map_sum, map_monomial]

end CycleQ2PolynomialDenominator

end

#print axioms CycleQ2PolynomialDenominator.exists_cleared_polynomial
