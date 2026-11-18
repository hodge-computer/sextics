import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/- Source component: PolynomialNormal -/
section
/-!
A polynomial normal vector from an invertible matrix of positive
coefficients. This is a generic linear-algebra construction; the exact
weighted-conic incidence supplies its coefficient and degree hypotheses.
-/

noncomputable section

namespace HoldoutConstruction

open Polynomial
open scoped BigOperators

variable {R ι κ : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- Rows select polynomial coefficients, and columns are the available
polynomial variations. -/
def positiveCoefficientMatrix (degree : ι → ℕ) (Q : ι → Polynomial R) : Matrix ι ι R :=
  fun i j => (Q j).coeff (degree i)

/-- A finite invertible coefficient system cancels every positive
coefficient of a polynomial with constant coefficient one. -/
theorem polynomial_linear_combination_one
    (degree : ι → ℕ) (bound : ℕ) (B : Polynomial R) (Q : ι → Polynomial R)
    (covers : ∀ n, 0 < n → n ≤ bound → ∃ i, degree i = n)
    (constant_B : B.coeff 0 = 1)
    (constant_Q : ∀ j, (Q j).coeff 0 = 0)
    (bound_B : B.natDegree ≤ bound)
    (bound_Q : ∀ j, (Q j).natDegree ≤ bound)
    (invertible : IsUnit (positiveCoefficientMatrix degree Q).det) :
    ∃ u : ι → R, B + ∑ j, C (u j)*Q j = 1 := by
  let J := positiveCoefficientMatrix degree Q
  let r : ι → R := fun i => -(B.coeff (degree i))
  let u : ι → R := J⁻¹.mulVec r
  have hu : J.mulVec u = r := by
    dsimp [u]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv J invertible, Matrix.one_mulVec]
  have hrow (i : ι) :
      B.coeff (degree i) + ∑ j, u j*(Q j).coeff (degree i) = 0 := by
    have h := congrFun hu i
    simp only [Matrix.mulVec, dotProduct, J, positiveCoefficientMatrix, r] at h
    rw [show (∑ j, u j*(Q j).coeff (degree i)) =
      ∑ j, (Q j).coeff (degree i)*u j by
        apply Finset.sum_congr rfl
        intro j _
        ring]
    rw [h, add_neg_cancel]
  refine ⟨u, ?_⟩
  ext n
  by_cases hn : n = 0
  · subst n
    simp [constant_B, constant_Q]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    by_cases hb : n ≤ bound
    · obtain ⟨i, hi⟩ := covers n hnpos hb
      subst n
      simpa only [coeff_add, finsetSum_coeff, coeff_C_mul, coeff_one,
        ite_eq_right hn] using hrow i
    · have hB : B.coeff n = 0 := coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt bound_B
        (Nat.lt_of_not_ge hb))
      have hQ (j : ι) : (Q j).coeff n = 0 := coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (bound_Q j) (Nat.lt_of_not_ge hb))
      simp [hB, hQ, coeff_one, hn]

section Vectors

variable [Fintype κ]

/-- Pair a gradient with a polynomial vector. -/
def polynomialPairing (G v : κ → Polynomial R) : Polynomial R := ∑ i, G i*v i

omit [DecidableEq ι] in
theorem polynomialPairing_affine (G b : κ → Polynomial R)
    (v : ι → κ → Polynomial R) (u : ι → R) :
    polynomialPairing G (fun i => b i + ∑ j, C (u j)*v j i) =
      polynomialPairing G b + ∑ j, C (u j)*polynomialPairing G (v j) := by
  simp only [polynomialPairing, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The desired normal vector is a constant normal direction plus a finite
linear combination of allowed positive-degree coordinate variations.
Its pairing with the gradient is identically one as a polynomial. -/
theorem polynomial_normal_from_coefficients
    (G b : κ → Polynomial R) (v : ι → κ → Polynomial R)
    (degree : ι → ℕ) (bound : ℕ)
    (covers : ∀ n, 0 < n → n ≤ bound → ∃ i, degree i = n)
    (constant_b : (polynomialPairing G b).coeff 0 = 1)
    (constant_v : ∀ j, (polynomialPairing G (v j)).coeff 0 = 0)
    (bound_b : (polynomialPairing G b).natDegree ≤ bound)
    (bound_v : ∀ j, (polynomialPairing G (v j)).natDegree ≤ bound)
    (invertible : IsUnit (positiveCoefficientMatrix degree
      (fun j => polynomialPairing G (v j))).det) :
    ∃ u : ι → R,
      polynomialPairing G (fun i => b i + ∑ j, C (u j)*v j i) = 1 := by
  obtain ⟨u, hu⟩ := polynomial_linear_combination_one degree bound (polynomialPairing G b)
    (fun j => polynomialPairing G (v j)) covers constant_b constant_v bound_b bound_v invertible
  exact ⟨u, (polynomialPairing_affine G b v u).trans hu⟩

end Vectors

end HoldoutConstruction

#print axioms HoldoutConstruction.polynomial_linear_combination_one
#print axioms HoldoutConstruction.polynomial_normal_from_coefficients
end
end
