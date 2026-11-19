import Proposal.GenericEliminant
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Ring

namespace GenericMonicPolynomial
open Polynomial
variable {K : Type*} [CommRing K]
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable def coefficient0 (p q s k u v : K) : K :=
  GenericLineChart.eliminantCoeff0 p q s k u v

noncomputable def coefficient1 (p q s k u v : K) : K :=
  GenericLineChart.eliminantCoeff1 p q s k u v

noncomputable def coefficient2 (p q s k u v : K) : K :=
  GenericLineChart.eliminantCoeff2 p q s k u v

noncomputable def coefficient3 (p q s k u v : K) : K :=
  GenericLineChart.eliminantCoeff3 p q s k u v

noncomputable def coefficient4 (p q s k u v : K) : K :=
  GenericLineChart.eliminantCoeff4 p q s k u v

noncomputable def coefficient5 (p q s k u v : K) : K :=
  GenericLineChart.eliminantCoeff5 p q s k u v

noncomputable def coefficient6 (p q s k u v : K) : K :=
  GenericLineChart.eliminantCoeff6 p q s k u v

noncomputable def coefficient7 (p q s k u v : K) : K :=
  GenericLineChart.eliminantCoeff7 p q s k u v

noncomputable def coefficient8 (p q s k u v : K) : K :=
  GenericLineChart.eliminantCoeff8 p q s k u v

noncomputable def coefficient9 (p q s k u v : K) : K :=
  GenericLineChart.eliminantCoeff9 p q s k u v

noncomputable def coefficient10 (p q s k u v : K) : K :=
  GenericLineChart.eliminantCoeff10 p q s k u v

noncomputable def coefficient11 (p q s k u v : K) : K :=
  GenericLineChart.eliminantCoeff11 p q s k u v

noncomputable def coefficient12 (p q s k u v : K) : K :=
  GenericLineChart.eliminantCoeff12 p q s k u v

noncomputable def coefficient13 (p q s k u v : K) : K :=
  GenericLineChart.eliminantCoeff13 p q s k u v

noncomputable def coefficient14 (p q s k u v : K) : K :=
  GenericLineChart.eliminantCoeff14 p q s k u v

noncomputable def coefficient15 (p q s k u v : K) : K :=
  GenericLineChart.eliminantCoeff15 p q s k u v

noncomputable def coefficient16 (p q s k u v : K) : K :=
  GenericLineChart.eliminantCoeff16 p q s k u v

noncomputable def coefficient17 (p q s k u v : K) : K :=
  GenericLineChart.eliminantCoeff17 p q s k u v

noncomputable def coefficient18 (p q s k u v : K) : K :=
  GenericLineChart.eliminantCoeff18 p q s k u v

noncomputable def coefficient19 (p q s k u v : K) : K :=
  GenericLineChart.eliminantCoeff19 p q s k u v

noncomputable def coefficient20 (p q s k u v : K) : K :=
  GenericLineChart.eliminantCoeff20 p q s k u v

noncomputable def coefficient21 (p q s k u v : K) : K :=
  GenericLineChart.eliminantCoeff21 p q s k u v

noncomputable def coefficient22 (p q s k u v : K) : K :=
  GenericLineChart.eliminantCoeff22 p q s k u v

noncomputable def coefficient23 (p q s k u v : K) : K :=
  GenericLineChart.eliminantCoeff23 p q s k u v

noncomputable def coefficient24 (p q s k u v : K) : K :=
  GenericLineChart.eliminantCoeff24 p q s k u v

noncomputable def coefficient25 (p q s k u v : K) : K :=
  GenericLineChart.eliminantCoeff25 p q s k u v

noncomputable def coefficient26 (p q s k u v : K) : K :=
  GenericLineChart.eliminantCoeff26 p q s k u v

noncomputable def coefficient (p q s k u v : K) (i : Fin 27) : K :=
  List.getD [coefficient0 p q s k u v, coefficient1 p q s k u v, coefficient2 p q s k u v, coefficient3 p q s k u v, coefficient4 p q s k u v, coefficient5 p q s k u v, coefficient6 p q s k u v, coefficient7 p q s k u v, coefficient8 p q s k u v, coefficient9 p q s k u v, coefficient10 p q s k u v, coefficient11 p q s k u v, coefficient12 p q s k u v, coefficient13 p q s k u v, coefficient14 p q s k u v, coefficient15 p q s k u v, coefficient16 p q s k u v, coefficient17 p q s k u v, coefficient18 p q s k u v, coefficient19 p q s k u v, coefficient20 p q s k u v, coefficient21 p q s k u v, coefficient22 p q s k u v, coefficient23 p q s k u v, coefficient24 p q s k u v, coefficient25 p q s k u v, coefficient26 p q s k u v] i.val 0

#check coefficient

noncomputable def rawPolynomial (p q s k u v : K) : K[X] :=
  C (u^10*v)*X^27 + ∑ i : Fin 27, C (coefficient p q s k u v i)*X^(i:ℕ)

noncomputable def monicPolynomial (p q s k u v : K) : K[X] :=
  X^27 + ∑ i : Fin 27, C (Ring.inverse (u^10*v)*coefficient p q s k u v i)*X^(i:ℕ)

theorem monicPolynomial_monic (p q s k u v : K) (_h : IsUnit (u^10*v)) :
    (monicPolynomial p q s k u v).Monic :=
  monic_X_pow_add (degree_sum_fin_lt _)

theorem monicPolynomial_natDegree [Nontrivial K] (p q s k u v : K)
    (_h : IsUnit (u^10*v)) : (monicPolynomial p q s k u v).natDegree = 27 := by
  apply natDegree_eq_of_degree_eq_some
  change degree (X^27 + _) = 27
  rw [degree_add_eq_left_of_degree_lt]
  · simp
  · simpa only [degree_X_pow] using degree_sum_fin_lt
      (fun i : Fin 27 => Ring.inverse (u^10*v)*coefficient p q s k u v i)

#check monicPolynomial_natDegree

theorem coefficient0_map {L : Type*} [CommRing L] (f : K →+* L) (p q s k u v : K) :
    f (coefficient0 p q s k u v) = coefficient0 (f p) (f q) (f s) (f k) (f u) (f v) := by
  simp only [coefficient0, GenericLineChart.eliminantCoeff0, map_add, map_mul,
    map_sub, map_neg, map_pow, map_ofNat]

theorem coefficient1_map {L : Type*} [CommRing L] (f : K →+* L) (p q s k u v : K) :
    f (coefficient1 p q s k u v) = coefficient1 (f p) (f q) (f s) (f k) (f u) (f v) := by
  simp only [coefficient1, GenericLineChart.eliminantCoeff1, map_add, map_mul,
    map_sub, map_neg, map_pow, map_ofNat]

theorem coefficient2_map {L : Type*} [CommRing L] (f : K →+* L) (p q s k u v : K) :
    f (coefficient2 p q s k u v) = coefficient2 (f p) (f q) (f s) (f k) (f u) (f v) := by
  simp only [coefficient2, GenericLineChart.eliminantCoeff2, map_add, map_mul,
    map_sub, map_neg, map_pow, map_ofNat]

theorem coefficient3_map {L : Type*} [CommRing L] (f : K →+* L) (p q s k u v : K) :
    f (coefficient3 p q s k u v) = coefficient3 (f p) (f q) (f s) (f k) (f u) (f v) := by
  simp only [coefficient3, GenericLineChart.eliminantCoeff3, map_add, map_mul,
    map_sub, map_neg, map_pow, map_ofNat]

theorem coefficient4_map {L : Type*} [CommRing L] (f : K →+* L) (p q s k u v : K) :
    f (coefficient4 p q s k u v) = coefficient4 (f p) (f q) (f s) (f k) (f u) (f v) := by
  simp only [coefficient4, GenericLineChart.eliminantCoeff4, map_add, map_mul,
    map_sub, map_neg, map_pow, map_ofNat]

theorem coefficient5_map {L : Type*} [CommRing L] (f : K →+* L) (p q s k u v : K) :
    f (coefficient5 p q s k u v) = coefficient5 (f p) (f q) (f s) (f k) (f u) (f v) := by
  simp only [coefficient5, GenericLineChart.eliminantCoeff5, map_add, map_mul,
    map_sub, map_neg, map_pow, map_ofNat]

theorem coefficient6_map {L : Type*} [CommRing L] (f : K →+* L) (p q s k u v : K) :
    f (coefficient6 p q s k u v) = coefficient6 (f p) (f q) (f s) (f k) (f u) (f v) := by
  simp only [coefficient6, GenericLineChart.eliminantCoeff6, map_add, map_mul,
    map_sub, map_neg, map_pow, map_ofNat]

theorem coefficient7_map {L : Type*} [CommRing L] (f : K →+* L) (p q s k u v : K) :
    f (coefficient7 p q s k u v) = coefficient7 (f p) (f q) (f s) (f k) (f u) (f v) := by
  simp only [coefficient7, GenericLineChart.eliminantCoeff7, map_add, map_mul,
    map_sub, map_neg, map_pow, map_ofNat]

theorem coefficient8_map {L : Type*} [CommRing L] (f : K →+* L) (p q s k u v : K) :
    f (coefficient8 p q s k u v) = coefficient8 (f p) (f q) (f s) (f k) (f u) (f v) := by
  simp only [coefficient8, GenericLineChart.eliminantCoeff8, map_add, map_mul,
    map_sub, map_neg, map_pow, map_ofNat]

theorem coefficient9_map {L : Type*} [CommRing L] (f : K →+* L) (p q s k u v : K) :
    f (coefficient9 p q s k u v) = coefficient9 (f p) (f q) (f s) (f k) (f u) (f v) := by
  simp only [coefficient9, GenericLineChart.eliminantCoeff9, map_add, map_mul,
    map_sub, map_neg, map_pow, map_ofNat]

theorem coefficient10_map {L : Type*} [CommRing L] (f : K →+* L) (p q s k u v : K) :
    f (coefficient10 p q s k u v) = coefficient10 (f p) (f q) (f s) (f k) (f u) (f v) := by
  simp only [coefficient10, GenericLineChart.eliminantCoeff10, map_add, map_mul,
    map_sub, map_neg, map_pow, map_ofNat]

theorem coefficient11_map {L : Type*} [CommRing L] (f : K →+* L) (p q s k u v : K) :
    f (coefficient11 p q s k u v) = coefficient11 (f p) (f q) (f s) (f k) (f u) (f v) := by
  simp only [coefficient11, GenericLineChart.eliminantCoeff11, map_add, map_mul,
    map_sub, map_neg, map_pow, map_ofNat]

theorem coefficient12_map {L : Type*} [CommRing L] (f : K →+* L) (p q s k u v : K) :
    f (coefficient12 p q s k u v) = coefficient12 (f p) (f q) (f s) (f k) (f u) (f v) := by
  simp only [coefficient12, GenericLineChart.eliminantCoeff12, map_add, map_mul,
    map_sub, map_neg, map_pow, map_ofNat]

theorem coefficient13_map {L : Type*} [CommRing L] (f : K →+* L) (p q s k u v : K) :
    f (coefficient13 p q s k u v) = coefficient13 (f p) (f q) (f s) (f k) (f u) (f v) := by
  simp only [coefficient13, GenericLineChart.eliminantCoeff13, map_add, map_mul,
    map_sub, map_neg, map_pow, map_ofNat]

theorem coefficient14_map {L : Type*} [CommRing L] (f : K →+* L) (p q s k u v : K) :
    f (coefficient14 p q s k u v) = coefficient14 (f p) (f q) (f s) (f k) (f u) (f v) := by
  simp only [coefficient14, GenericLineChart.eliminantCoeff14, map_add, map_mul,
    map_sub, map_neg, map_pow, map_ofNat]

theorem coefficient15_map {L : Type*} [CommRing L] (f : K →+* L) (p q s k u v : K) :
    f (coefficient15 p q s k u v) = coefficient15 (f p) (f q) (f s) (f k) (f u) (f v) := by
  simp only [coefficient15, GenericLineChart.eliminantCoeff15, map_add, map_mul,
    map_sub, map_neg, map_pow, map_ofNat]

theorem coefficient16_map {L : Type*} [CommRing L] (f : K →+* L) (p q s k u v : K) :
    f (coefficient16 p q s k u v) = coefficient16 (f p) (f q) (f s) (f k) (f u) (f v) := by
  simp only [coefficient16, GenericLineChart.eliminantCoeff16, map_add, map_mul,
    map_sub, map_neg, map_pow, map_ofNat]

theorem coefficient17_map {L : Type*} [CommRing L] (f : K →+* L) (p q s k u v : K) :
    f (coefficient17 p q s k u v) = coefficient17 (f p) (f q) (f s) (f k) (f u) (f v) := by
  simp only [coefficient17, GenericLineChart.eliminantCoeff17, map_add, map_mul,
    map_sub, map_neg, map_pow, map_ofNat]

theorem coefficient18_map {L : Type*} [CommRing L] (f : K →+* L) (p q s k u v : K) :
    f (coefficient18 p q s k u v) = coefficient18 (f p) (f q) (f s) (f k) (f u) (f v) := by
  simp only [coefficient18, GenericLineChart.eliminantCoeff18, map_add, map_mul,
    map_sub, map_neg, map_pow, map_ofNat]

theorem coefficient19_map {L : Type*} [CommRing L] (f : K →+* L) (p q s k u v : K) :
    f (coefficient19 p q s k u v) = coefficient19 (f p) (f q) (f s) (f k) (f u) (f v) := by
  simp only [coefficient19, GenericLineChart.eliminantCoeff19, map_add, map_mul,
    map_sub, map_neg, map_pow, map_ofNat]

theorem coefficient20_map {L : Type*} [CommRing L] (f : K →+* L) (p q s k u v : K) :
    f (coefficient20 p q s k u v) = coefficient20 (f p) (f q) (f s) (f k) (f u) (f v) := by
  simp only [coefficient20, GenericLineChart.eliminantCoeff20, map_add, map_mul,
    map_sub, map_neg, map_pow, map_ofNat]

theorem coefficient21_map {L : Type*} [CommRing L] (f : K →+* L) (p q s k u v : K) :
    f (coefficient21 p q s k u v) = coefficient21 (f p) (f q) (f s) (f k) (f u) (f v) := by
  simp only [coefficient21, GenericLineChart.eliminantCoeff21, map_add, map_mul,
    map_sub, map_neg, map_pow, map_ofNat]

theorem coefficient22_map {L : Type*} [CommRing L] (f : K →+* L) (p q s k u v : K) :
    f (coefficient22 p q s k u v) = coefficient22 (f p) (f q) (f s) (f k) (f u) (f v) := by
  simp only [coefficient22, GenericLineChart.eliminantCoeff22, map_add, map_mul,
    map_sub, map_neg, map_pow, map_ofNat]

theorem coefficient23_map {L : Type*} [CommRing L] (f : K →+* L) (p q s k u v : K) :
    f (coefficient23 p q s k u v) = coefficient23 (f p) (f q) (f s) (f k) (f u) (f v) := by
  simp only [coefficient23, GenericLineChart.eliminantCoeff23, map_add, map_mul,
    map_sub, map_neg, map_pow, map_ofNat]

theorem coefficient24_map {L : Type*} [CommRing L] (f : K →+* L) (p q s k u v : K) :
    f (coefficient24 p q s k u v) = coefficient24 (f p) (f q) (f s) (f k) (f u) (f v) := by
  simp only [coefficient24, GenericLineChart.eliminantCoeff24, map_add, map_mul,
    map_sub, map_neg, map_pow, map_ofNat]

theorem coefficient25_map {L : Type*} [CommRing L] (f : K →+* L) (p q s k u v : K) :
    f (coefficient25 p q s k u v) = coefficient25 (f p) (f q) (f s) (f k) (f u) (f v) := by
  simp only [coefficient25, GenericLineChart.eliminantCoeff25, map_add, map_mul,
    map_sub, map_neg, map_pow, map_ofNat]

theorem coefficient26_map {L : Type*} [CommRing L] (f : K →+* L) (p q s k u v : K) :
    f (coefficient26 p q s k u v) = coefficient26 (f p) (f q) (f s) (f k) (f u) (f v) := by
  simp only [coefficient26, GenericLineChart.eliminantCoeff26, map_add, map_mul,
    map_sub, map_neg, map_pow, map_ofNat]

theorem coefficient_map {L : Type*} [CommRing L] (f : K →+* L) (p q s k u v : K)
    (i : Fin 27) : f (coefficient p q s k u v i) =
      coefficient (f p) (f q) (f s) (f k) (f u) (f v) i := by
  unfold coefficient
  rw [← List.getD_map (f := (f : K → L))]
  simp only [List.map_cons, List.map_nil, map_zero, coefficient0_map, coefficient1_map, coefficient2_map, coefficient3_map, coefficient4_map, coefficient5_map, coefficient6_map, coefficient7_map, coefficient8_map, coefficient9_map, coefficient10_map, coefficient11_map, coefficient12_map, coefficient13_map, coefficient14_map, coefficient15_map, coefficient16_map, coefficient17_map, coefficient18_map, coefficient19_map, coefficient20_map, coefficient21_map, coefficient22_map, coefficient23_map, coefficient24_map, coefficient25_map, coefficient26_map]

#check coefficient_map

theorem rawPolynomial_map {L : Type*} [CommRing L] (f : K →+* L) (p q s k u v : K) :
    (rawPolynomial p q s k u v).map f =
      rawPolynomial (f p) (f q) (f s) (f k) (f u) (f v) := by
  simp only [rawPolynomial, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_sum, map_mul, map_pow]
  simp only [coefficient_map]

theorem leading_mul_monicPolynomial (p q s k u v : K) (h : IsUnit (u^10*v)) :
    C (u^10*v) * monicPolynomial p q s k u v = rawPolynomial p q s k u v := by
  unfold monicPolynomial rawPolynomial
  rw [mul_add, Finset.mul_sum]
  apply congrArg (fun t : K[X] => C (u^10*v)*X^27 + t)
  apply Finset.sum_congr rfl
  intro i hi
  rw [← mul_assoc, ← map_mul, ← mul_assoc, Ring.mul_inverse_cancel _ h, one_mul]

end GenericMonicPolynomial
