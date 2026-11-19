import Proposal.GenericEliminant
import Proposal.GenericMonicPolynomial

namespace GenericMonicPolynomial
open Polynomial
variable {K A : Type*} [CommRing K] [CommRing A]

theorem coefficient0_eq (p q s k u v : K) : coefficient0 p q s k u v =
    GenericLineChart.eliminantCoeff0 p q s k u v := rfl

theorem coefficient1_eq (p q s k u v : K) : coefficient1 p q s k u v =
    GenericLineChart.eliminantCoeff1 p q s k u v := rfl

theorem coefficient2_eq (p q s k u v : K) : coefficient2 p q s k u v =
    GenericLineChart.eliminantCoeff2 p q s k u v := rfl

theorem coefficient3_eq (p q s k u v : K) : coefficient3 p q s k u v =
    GenericLineChart.eliminantCoeff3 p q s k u v := rfl

theorem coefficient4_eq (p q s k u v : K) : coefficient4 p q s k u v =
    GenericLineChart.eliminantCoeff4 p q s k u v := rfl

theorem coefficient5_eq (p q s k u v : K) : coefficient5 p q s k u v =
    GenericLineChart.eliminantCoeff5 p q s k u v := rfl

theorem coefficient6_eq (p q s k u v : K) : coefficient6 p q s k u v =
    GenericLineChart.eliminantCoeff6 p q s k u v := rfl

theorem coefficient7_eq (p q s k u v : K) : coefficient7 p q s k u v =
    GenericLineChart.eliminantCoeff7 p q s k u v := rfl

theorem coefficient8_eq (p q s k u v : K) : coefficient8 p q s k u v =
    GenericLineChart.eliminantCoeff8 p q s k u v := rfl

theorem coefficient9_eq (p q s k u v : K) : coefficient9 p q s k u v =
    GenericLineChart.eliminantCoeff9 p q s k u v := rfl

theorem coefficient10_eq (p q s k u v : K) : coefficient10 p q s k u v =
    GenericLineChart.eliminantCoeff10 p q s k u v := rfl

theorem coefficient11_eq (p q s k u v : K) : coefficient11 p q s k u v =
    GenericLineChart.eliminantCoeff11 p q s k u v := rfl

theorem coefficient12_eq (p q s k u v : K) : coefficient12 p q s k u v =
    GenericLineChart.eliminantCoeff12 p q s k u v := rfl

theorem coefficient13_eq (p q s k u v : K) : coefficient13 p q s k u v =
    GenericLineChart.eliminantCoeff13 p q s k u v := rfl

theorem coefficient14_eq (p q s k u v : K) : coefficient14 p q s k u v =
    GenericLineChart.eliminantCoeff14 p q s k u v := rfl

theorem coefficient15_eq (p q s k u v : K) : coefficient15 p q s k u v =
    GenericLineChart.eliminantCoeff15 p q s k u v := rfl

theorem coefficient16_eq (p q s k u v : K) : coefficient16 p q s k u v =
    GenericLineChart.eliminantCoeff16 p q s k u v := rfl

theorem coefficient17_eq (p q s k u v : K) : coefficient17 p q s k u v =
    GenericLineChart.eliminantCoeff17 p q s k u v := rfl

theorem coefficient18_eq (p q s k u v : K) : coefficient18 p q s k u v =
    GenericLineChart.eliminantCoeff18 p q s k u v := rfl

theorem coefficient19_eq (p q s k u v : K) : coefficient19 p q s k u v =
    GenericLineChart.eliminantCoeff19 p q s k u v := rfl

theorem coefficient20_eq (p q s k u v : K) : coefficient20 p q s k u v =
    GenericLineChart.eliminantCoeff20 p q s k u v := rfl

theorem coefficient21_eq (p q s k u v : K) : coefficient21 p q s k u v =
    GenericLineChart.eliminantCoeff21 p q s k u v := rfl

theorem coefficient22_eq (p q s k u v : K) : coefficient22 p q s k u v =
    GenericLineChart.eliminantCoeff22 p q s k u v := rfl

theorem coefficient23_eq (p q s k u v : K) : coefficient23 p q s k u v =
    GenericLineChart.eliminantCoeff23 p q s k u v := rfl

theorem coefficient24_eq (p q s k u v : K) : coefficient24 p q s k u v =
    GenericLineChart.eliminantCoeff24 p q s k u v := rfl

theorem coefficient25_eq (p q s k u v : K) : coefficient25 p q s k u v =
    GenericLineChart.eliminantCoeff25 p q s k u v := rfl

theorem coefficient26_eq (p q s k u v : K) : coefficient26 p q s k u v =
    GenericLineChart.eliminantCoeff26 p q s k u v := rfl

theorem rawPolynomial_eval₂ (f : K →+* A) (r : A) (p q s k u v : K) :
    (rawPolynomial p q s k u v).eval₂ f r =
      GenericLineChart.eliminant r (f p) (f q) (f s) (f k) (f u) (f v) := by
  simp only [rawPolynomial, eval₂_add, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X,
    eval₂_finsetSum, map_mul, map_pow]
  simp only [coefficient_map]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, coefficient, List.getD_cons_zero, List.getD_cons_succ,
    Fin.sum_univ_zero, add_zero]
  simp only [coefficient0_eq, coefficient1_eq, coefficient2_eq, coefficient3_eq, coefficient4_eq, coefficient5_eq, coefficient6_eq, coefficient7_eq, coefficient8_eq, coefficient9_eq, coefficient10_eq, coefficient11_eq, coefficient12_eq, coefficient13_eq, coefficient14_eq, coefficient15_eq, coefficient16_eq, coefficient17_eq, coefficient18_eq, coefficient19_eq, coefficient20_eq, coefficient21_eq, coefficient22_eq, coefficient23_eq, coefficient24_eq, coefficient25_eq, coefficient26_eq]
  unfold GenericLineChart.eliminant GenericLineChart.eliminantCoeff27
  ring

end GenericMonicPolynomial

#print axioms GenericMonicPolynomial.rawPolynomial_eval₂
