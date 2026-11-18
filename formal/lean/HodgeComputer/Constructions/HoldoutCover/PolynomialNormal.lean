import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/- Source component: PolynomialNormal -/
section
/-!
Polynomial normal vectors from invertible coefficient matrices. The
positive-coefficient version preserves a separately normalized constant
direction; the full-coefficient version includes the constant term in the
linear system. Applications supply the incidence and degree hypotheses.
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

/-- An invertible matrix of all coefficients through degree `n - 1`
expresses the constant polynomial one as a linear combination of the
available variations. Unlike the positive-coefficient version, this
requires no separately normalized constant direction. -/
theorem full_polynomial_combination_one {n : ℕ} (hn : 0 < n)
    (Q : Fin n → Polynomial R) (bound : ∀ j, (Q j).natDegree < n)
    (hunit : IsUnit (Matrix.det (fun i j : Fin n => (Q j).coeff i.val))) :
    ∃ u : Fin n → R, ∑ j, C (u j)*Q j = 1 := by
  let J : Matrix (Fin n) (Fin n) R := fun i j => (Q j).coeff i.val
  let e : Fin n → R := Pi.single ⟨0, hn⟩ 1
  let u := J⁻¹.mulVec e
  have hu : J.mulVec u = e := by
    dsimp [u]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv J hunit, Matrix.one_mulVec]
  refine ⟨u, ?_⟩
  ext k
  by_cases hk : k < n
  · have h := congrFun hu ⟨k, hk⟩
    simp only [Matrix.mulVec, dotProduct, J, e, Pi.single_apply] at h
    rw [show (∑ j, (Q j).coeff k*u j) = ∑ j, u j*(Q j).coeff k by
      apply Finset.sum_congr rfl
      intro j _
      ring] at h
    simpa [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_one,
      Fin.ext_iff] using h
  · have hQ (j : Fin n) : (Q j).coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (bound j) (Nat.le_of_not_gt hk))
    have hk0 : k ≠ 0 := by omega
    simp [Polynomial.coeff_C_mul, hQ, Polynomial.coeff_one, hk0]

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
#print axioms HoldoutConstruction.full_polynomial_combination_one
#print axioms HoldoutConstruction.polynomial_normal_from_coefficients
end
end
