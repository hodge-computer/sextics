import Proposal.ContactExactArithmetic
import Proposal.ContactNewtonCertificate

/-! Complex row bounds obtained from exact Gaussian integer computations. -/

namespace ContactExactArithmetic

open scoped BigOperators Matrix
open ContactPolynomialBounds

set_option backward.isDefEq.respectTransparency false

theorem mass_scaled (z : GaussianInt) (D : ℕ) :
    complexMass ((z : ℂ) / (D : ℂ)) = (mass z : ℝ) / (D : ℝ) := by
  have hD : ((D : ℝ) : ℂ) = (D : ℂ) := by simp
  have hn : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  simp only [complexMass, ← hD, Complex.div_ofReal_re, Complex.div_ofReal_im,
    abs_div, abs_of_nonneg hn, ← add_div, mass_cast]

theorem rowMass_scaled {n : ℕ} (v : Fin n → GaussianInt) (D : ℕ) :
    (∑ i, complexMass ((v i : ℂ) / (D : ℂ))) = (rowMass v : ℝ) / (D : ℝ) := by
  simp only [mass_scaled]
  simp only [rowMass, Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul]

theorem dotInt_cast {n : ℕ} (v w : Fin n → GaussianInt) :
    (dotInt v w : ℂ) = ∑ i, (v i : ℂ) * (w i : ℂ) := by
  simp [dotInt, map_sum, GaussianInt.toComplex_mul]

theorem dot_scaled {n : ℕ} (v w : Fin n → GaussianInt) (D E : ℕ) :
    (∑ i, ((v i : ℂ) / (D : ℂ)) * ((w i : ℂ) / (E : ℂ))) =
      (dotInt v w : ℂ) / ((D * E : ℕ) : ℂ) := by
  simp only [div_mul_div_comm]
  simp only [Nat.cast_mul, dotInt_cast, div_eq_mul_inv, Finset.sum_mul]

theorem defect_scaled {n : ℕ} (B J : Fin n → Fin n → GaussianInt)
    (D E : ℕ) (hD : 0 < D) (hE : 0 < E) (i j : Fin n) :
    ((1 : Matrix (Fin n) (Fin n) ℂ) -
      (show Matrix (Fin n) (Fin n) ℂ from fun a b => (B a b : ℂ) / (D : ℂ)) *
      (show Matrix (Fin n) (Fin n) ℂ from fun a b => (J a b : ℂ) / (E : ℂ))) i j =
    (((if i = j then ((D * E : ℕ) : GaussianInt) else 0) -
      dotInt (B i) (fun k => J k j) : GaussianInt) : ℂ) / ((D * E : ℕ) : ℂ) := by
  have hd : ((D * E : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.mul_pos hD hE)
  simp only [Matrix.sub_apply, Matrix.mul_apply, dot_scaled]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.one_apply_eq, ite_true, GaussianInt.toComplex_sub,
      map_natCast]
    field_simp
  · simp only [Matrix.one_apply_ne hij, if_neg hij, GaussianInt.toComplex_sub,
      GaussianInt.toComplex_zero, zero_sub, GaussianInt.toComplex_neg, neg_div]

end ContactExactArithmetic
