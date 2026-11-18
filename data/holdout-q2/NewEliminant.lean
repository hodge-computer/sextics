import Proposal.NewLineChart
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Ring

noncomputable section
namespace HoldoutQ2.NewEliminant
open Polynomial NewLineChart
variable {K : Type*} [CommRing K]
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def coefficient0 (a b c d : K) : K := (((((5832)*((a)^2))*((b)^9) + ((729)*((b)^8))*((c)^3)) - (((54)*((b)^4))*((c)^3))*((d)^6)) + ((c)^3)*((d)^12))
def coefficient1 (a b c d : K) : K := (1)*(((((((-(729)))*(a))*((b)^8))*((c)^2) + ((((1134)*(a))*((b)^4))*((c)^2))*((d)^6)) - (((9)*(a))*((c)^2))*((d)^12)))
def coefficient2 (a b c d : K) : K := ((1)^2)*((((((((45927)*((a)^2))*((b)^8))*(c) - ((((4374)*((a)^2))*((b)^4))*(c))*((d)^6)) + (((27)*((a)^2))*(c))*((d)^12)) + ((5832)*((b)^7))*((c)^4)) + (((648)*((b)^3))*((c)^4))*((d)^6)))
def coefficient3 (a b c d : K) : K := ((1)^3)*((((((((-(45927)))*((a)^3))*((b)^8) + (((4374)*((a)^3))*((b)^4))*((d)^6)) - ((27)*((a)^3))*((d)^12)) - (((11664)*(a))*((b)^7))*((c)^3)) - ((((4752)*(a))*((b)^3))*((c)^3))*((d)^6)))
def coefficient4 (a b c d : K) : K := ((1)^4)*(((((((163296)*((a)^2))*((b)^7))*((c)^2) + ((((11016)*((a)^2))*((b)^3))*((c)^2))*((d)^6)) + ((20412)*((b)^6))*((c)^5)) + (((540)*((b)^2))*((c)^5))*((d)^6)))
def coefficient5 (a b c d : K) : K := ((1)^5)*((((((((-(314928)))*((a)^3))*((b)^7))*(c) - ((((11664)*((a)^3))*((b)^3))*(c))*((d)^6)) - (((61236)*(a))*((b)^6))*((c)^4)) - ((((8100)*(a))*((b)^2))*((c)^4))*((d)^6)))
def coefficient6 (a b c d : K) : K := ((1)^6)*((((((((157464)*((a)^4))*((b)^7) + (((5832)*((a)^4))*((b)^3))*((d)^6)) + (((367416)*((a)^2))*((b)^6))*((c)^3)) + ((((33048)*((a)^2))*((b)^2))*((c)^3))*((d)^6)) + ((40824)*((b)^5))*((c)^6)) - (((1080)*(b))*((c)^6))*((d)^6)))
def coefficient7 (a b c d : K) : K := ((1)^7)*((((((((-(938952)))*((a)^3))*((b)^6))*((c)^2) - ((((60264)*((a)^3))*((b)^2))*((c)^2))*((d)^6)) - (((163296)*(a))*((b)^5))*((c)^5)) + ((((6048)*(a))*(b))*((c)^5))*((d)^6)))
def coefficient8 (a b c d : K) : K := ((1)^8)*(((((((((918540)*((a)^4))*((b)^6))*(c) + ((((52488)*((a)^4))*((b)^2))*(c))*((d)^6)) + (((612360)*((a)^2))*((b)^5))*((c)^4)) - ((((12960)*((a)^2))*(b))*((c)^4))*((d)^6)) + ((51030)*((b)^4))*((c)^7)) - ((918)*((c)^7))*((d)^6)))
def coefficient9 (a b c d : K) : K := ((1)^9)*(((((((((-(306180)))*((a)^5))*((b)^6) - (((17496)*((a)^5))*((b)^2))*((d)^6)) - (((1632960)*((a)^3))*((b)^5))*((c)^3)) + ((((12528)*((a)^3))*(b))*((c)^3))*((d)^6)) - (((255150)*(a))*((b)^4))*((c)^6)) + (((8262)*(a))*((c)^6))*((d)^6)))
def coefficient10 (a b c d : K) : K := ((1)^10)*((((((((2245320)*((a)^4))*((b)^5))*((c)^2) - ((((4536)*((a)^4))*(b))*((c)^2))*((d)^6)) + (((785862)*((a)^2))*((b)^4))*((c)^5)) - (((32346)*((a)^2))*((c)^5))*((d)^6)) + ((40824)*((b)^3))*((c)^8)))
def coefficient11 (a b c d : K) : K := ((1)^11)*((((((((-(1469664)))*((a)^5))*((b)^5))*(c) - (((1888110)*((a)^3))*((b)^4))*((c)^4)) + (((71442)*((a)^3))*((c)^4))*((d)^6)) - (((244944)*(a))*((b)^3))*((c)^7)))
def coefficient12 (a b c d : K) : K := ((1)^12)*(((((((367416)*((a)^6))*((b)^5) + (((3010770)*((a)^4))*((b)^4))*((c)^3)) - (((96174)*((a)^4))*((c)^3))*((d)^6)) + (((734832)*((a)^2))*((b)^3))*((c)^6)) + ((20412)*((b)^2))*((c)^9)))
def coefficient13 (a b c d : K) : K := ((1)^13)*((((((((-(2806650)))*((a)^5))*((b)^4))*((c)^2) + (((78894)*((a)^5))*((c)^2))*((d)^6)) - (((1551312)*((a)^3))*((b)^3))*((c)^5)) - (((142884)*(a))*((b)^2))*((c)^8)))
def coefficient14 (a b c d : K) : K := ((1)^14)*((((((((1377810)*((a)^6))*((b)^4))*(c) - (((36450)*((a)^6))*(c))*((d)^6)) + (((2449440)*((a)^4))*((b)^3))*((c)^4)) + (((454896)*((a)^2))*((b)^2))*((c)^7)) + ((5832)*(b))*((c)^10)))
def coefficient15 (a b c d : K) : K := ((1)^15)*((((((((-(275562)))*((a)^7))*((b)^4) + ((7290)*((a)^7))*((d)^6)) - (((2694384)*((a)^5))*((b)^3))*((c)^3)) - (((898128)*((a)^3))*((b)^2))*((c)^6)) - (((46656)*(a))*(b))*((c)^9)))
def coefficient16 (a b c d : K) : K := ((1)^16)*(((((((1877904)*((a)^6))*((b)^3))*((c)^2) + (((1265544)*((a)^4))*((b)^2))*((c)^5)) + (((163296)*((a)^2))*(b))*((c)^8)) + (729)*((c)^11)))
def coefficient17 (a b c d : K) : K := ((1)^17)*((((((((-(734832)))*((a)^7))*((b)^3))*(c) - (((1347192)*((a)^5))*((b)^2))*((c)^4)) - (((326592)*((a)^3))*(b))*((c)^7)) - ((6561)*(a))*((c)^10)))
def coefficient18 (a b c d : K) : K := ((1)^18)*((((((122472)*((a)^8))*((b)^3) + (((1061424)*((a)^6))*((b)^2))*((c)^3)) + (((408240)*((a)^4))*(b))*((c)^6)) + ((25515)*((a)^2))*((c)^9)))
def coefficient19 (a b c d : K) : K := ((1)^19)*(((((((-(571536)))*((a)^7))*((b)^2))*((c)^2) - (((326592)*((a)^5))*(b))*((c)^5)) - ((54675)*((a)^3))*((c)^8)))
def coefficient20 (a b c d : K) : K := ((1)^20)*((((((183708)*((a)^8))*((b)^2))*(c) + (((163296)*((a)^6))*(b))*((c)^4)) + ((65610)*((a)^4))*((c)^7)))
def coefficient21 (a b c d : K) : K := ((1)^21)*((((((-(26244)))*((a)^9))*((b)^2) - (((46656)*((a)^7))*(b))*((c)^3)) - ((30618)*((a)^5))*((c)^6)))
def coefficient22 (a b c d : K) : K := ((1)^22)*(((((5832)*((a)^8))*(b))*((c)^2) - ((30618)*((a)^6))*((c)^5)))
def coefficient23 (a b c d : K) : K := (((65610)*((a)^7))*((c)^4))*((1)^23)
def coefficient24 (a b c d : K) : K := (-((((54675)*((a)^8))*((c)^3))*((1)^24)))
def coefficient25 (a b c d : K) : K := (((25515)*((a)^9))*((c)^2))*((1)^25)
def coefficient26 (a b c d : K) : K := (-((((6561)*((a)^10))*(c))*((1)^26)))
def coefficient27 (a b c d : K) : K := ((729)*((a)^11))*((1)^27)

def eliminant (r a b c d : K) : K := coefficient0 a b c d+r*(coefficient1 a b c d+r*(coefficient2 a b c d+r*(coefficient3 a b c d+r*(coefficient4 a b c d+r*(coefficient5 a b c d+r*(coefficient6 a b c d+r*(coefficient7 a b c d+r*(coefficient8 a b c d+r*(coefficient9 a b c d+r*(coefficient10 a b c d+r*(coefficient11 a b c d+r*(coefficient12 a b c d+r*(coefficient13 a b c d+r*(coefficient14 a b c d+r*(coefficient15 a b c d+r*(coefficient16 a b c d+r*(coefficient17 a b c d+r*(coefficient18 a b c d+r*(coefficient19 a b c d+r*(coefficient20 a b c d+r*(coefficient21 a b c d+r*(coefficient22 a b c d+r*(coefficient23 a b c d+r*(coefficient24 a b c d+r*(coefficient25 a b c d+r*(coefficient26 a b c d+r*(coefficient27 a b c d)))))))))))))))))))))))))))

theorem quadratic_factor (r a b c d : K) :
    qa r a b c*(coordinateNum r a b c d)^2+
      qb r a b c d*coordinateNum r a b c d*coordinateDen r a b c d+
      qc r a c d*(coordinateDen r a b c d)^2 =
    18*d^4*(3*a*r-c)*(kappa r a b c)^5*eliminant r a b c d := by
  unfold qa qb qc coordinateNum coordinateDen kappa tt uu eliminant
  unfold coefficient0 coefficient1 coefficient2 coefficient3 coefficient4 coefficient5 coefficient6 coefficient7 coefficient8 coefficient9 coefficient10 coefficient11 coefficient12 coefficient13 coefficient14 coefficient15 coefficient16 coefficient17 coefficient18 coefficient19 coefficient20 coefficient21 coefficient22 coefficient23 coefficient24 coefficient25 coefficient26 coefficient27
  ring

def coefficient (a b c d : K) (i : Fin 27) : K :=
  List.getD [coefficient0 a b c d, coefficient1 a b c d, coefficient2 a b c d, coefficient3 a b c d, coefficient4 a b c d, coefficient5 a b c d, coefficient6 a b c d, coefficient7 a b c d, coefficient8 a b c d, coefficient9 a b c d, coefficient10 a b c d, coefficient11 a b c d, coefficient12 a b c d, coefficient13 a b c d, coefficient14 a b c d, coefficient15 a b c d, coefficient16 a b c d, coefficient17 a b c d, coefficient18 a b c d, coefficient19 a b c d, coefficient20 a b c d, coefficient21 a b c d, coefficient22 a b c d, coefficient23 a b c d, coefficient24 a b c d, coefficient25 a b c d, coefficient26 a b c d] i.val 0

def rawPolynomial (a b c d : K) : K[X] :=
  C (729*a^11)*X^27 + ∑ i : Fin 27, C (coefficient a b c d i)*X^(i:ℕ)

noncomputable def monicPolynomial (a b c d : K) : K[X] :=
  X^27 + ∑ i : Fin 27, C (Ring.inverse (729*a^11)*coefficient a b c d i)*X^(i:ℕ)

theorem monicPolynomial_monic (a b c d : K) :
    (monicPolynomial a b c d).Monic :=
  monic_X_pow_add (degree_sum_fin_lt _)

theorem monicPolynomial_natDegree [Nontrivial K] (a b c d : K) :
    (monicPolynomial a b c d).natDegree = 27 := by
  apply natDegree_eq_of_degree_eq_some
  change degree (X^27 + _) = 27
  rw [degree_add_eq_left_of_degree_lt]
  · simp
  · simpa only [degree_X_pow] using degree_sum_fin_lt
      (fun i : Fin 27 => Ring.inverse (729*a^11)*coefficient a b c d i)

theorem coefficient0_map {L : Type*} [CommRing L] (f : K →+* L) (a b c d : K) :
    f (coefficient0 a b c d) = coefficient0 (f a) (f b) (f c) (f d) := by
  simp only [coefficient0, map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_one]

theorem coefficient1_map {L : Type*} [CommRing L] (f : K →+* L) (a b c d : K) :
    f (coefficient1 a b c d) = coefficient1 (f a) (f b) (f c) (f d) := by
  simp only [coefficient1, map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_one]

theorem coefficient2_map {L : Type*} [CommRing L] (f : K →+* L) (a b c d : K) :
    f (coefficient2 a b c d) = coefficient2 (f a) (f b) (f c) (f d) := by
  simp only [coefficient2, map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_one]

theorem coefficient3_map {L : Type*} [CommRing L] (f : K →+* L) (a b c d : K) :
    f (coefficient3 a b c d) = coefficient3 (f a) (f b) (f c) (f d) := by
  simp only [coefficient3, map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_one]

theorem coefficient4_map {L : Type*} [CommRing L] (f : K →+* L) (a b c d : K) :
    f (coefficient4 a b c d) = coefficient4 (f a) (f b) (f c) (f d) := by
  simp only [coefficient4, map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_one]

theorem coefficient5_map {L : Type*} [CommRing L] (f : K →+* L) (a b c d : K) :
    f (coefficient5 a b c d) = coefficient5 (f a) (f b) (f c) (f d) := by
  simp only [coefficient5, map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_one]

theorem coefficient6_map {L : Type*} [CommRing L] (f : K →+* L) (a b c d : K) :
    f (coefficient6 a b c d) = coefficient6 (f a) (f b) (f c) (f d) := by
  simp only [coefficient6, map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_one]

theorem coefficient7_map {L : Type*} [CommRing L] (f : K →+* L) (a b c d : K) :
    f (coefficient7 a b c d) = coefficient7 (f a) (f b) (f c) (f d) := by
  simp only [coefficient7, map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_one]

theorem coefficient8_map {L : Type*} [CommRing L] (f : K →+* L) (a b c d : K) :
    f (coefficient8 a b c d) = coefficient8 (f a) (f b) (f c) (f d) := by
  simp only [coefficient8, map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_one]

theorem coefficient9_map {L : Type*} [CommRing L] (f : K →+* L) (a b c d : K) :
    f (coefficient9 a b c d) = coefficient9 (f a) (f b) (f c) (f d) := by
  simp only [coefficient9, map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_one]

theorem coefficient10_map {L : Type*} [CommRing L] (f : K →+* L) (a b c d : K) :
    f (coefficient10 a b c d) = coefficient10 (f a) (f b) (f c) (f d) := by
  simp only [coefficient10, map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_one]

theorem coefficient11_map {L : Type*} [CommRing L] (f : K →+* L) (a b c d : K) :
    f (coefficient11 a b c d) = coefficient11 (f a) (f b) (f c) (f d) := by
  simp only [coefficient11, map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_one]

theorem coefficient12_map {L : Type*} [CommRing L] (f : K →+* L) (a b c d : K) :
    f (coefficient12 a b c d) = coefficient12 (f a) (f b) (f c) (f d) := by
  simp only [coefficient12, map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_one]

theorem coefficient13_map {L : Type*} [CommRing L] (f : K →+* L) (a b c d : K) :
    f (coefficient13 a b c d) = coefficient13 (f a) (f b) (f c) (f d) := by
  simp only [coefficient13, map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_one]

theorem coefficient14_map {L : Type*} [CommRing L] (f : K →+* L) (a b c d : K) :
    f (coefficient14 a b c d) = coefficient14 (f a) (f b) (f c) (f d) := by
  simp only [coefficient14, map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_one]

theorem coefficient15_map {L : Type*} [CommRing L] (f : K →+* L) (a b c d : K) :
    f (coefficient15 a b c d) = coefficient15 (f a) (f b) (f c) (f d) := by
  simp only [coefficient15, map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_one]

theorem coefficient16_map {L : Type*} [CommRing L] (f : K →+* L) (a b c d : K) :
    f (coefficient16 a b c d) = coefficient16 (f a) (f b) (f c) (f d) := by
  simp only [coefficient16, map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_one]

theorem coefficient17_map {L : Type*} [CommRing L] (f : K →+* L) (a b c d : K) :
    f (coefficient17 a b c d) = coefficient17 (f a) (f b) (f c) (f d) := by
  simp only [coefficient17, map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_one]

theorem coefficient18_map {L : Type*} [CommRing L] (f : K →+* L) (a b c d : K) :
    f (coefficient18 a b c d) = coefficient18 (f a) (f b) (f c) (f d) := by
  simp only [coefficient18, map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_one]

theorem coefficient19_map {L : Type*} [CommRing L] (f : K →+* L) (a b c d : K) :
    f (coefficient19 a b c d) = coefficient19 (f a) (f b) (f c) (f d) := by
  simp only [coefficient19, map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_one]

theorem coefficient20_map {L : Type*} [CommRing L] (f : K →+* L) (a b c d : K) :
    f (coefficient20 a b c d) = coefficient20 (f a) (f b) (f c) (f d) := by
  simp only [coefficient20, map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_one]

theorem coefficient21_map {L : Type*} [CommRing L] (f : K →+* L) (a b c d : K) :
    f (coefficient21 a b c d) = coefficient21 (f a) (f b) (f c) (f d) := by
  simp only [coefficient21, map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_one]

theorem coefficient22_map {L : Type*} [CommRing L] (f : K →+* L) (a b c d : K) :
    f (coefficient22 a b c d) = coefficient22 (f a) (f b) (f c) (f d) := by
  simp only [coefficient22, map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_one]

theorem coefficient23_map {L : Type*} [CommRing L] (f : K →+* L) (a b c d : K) :
    f (coefficient23 a b c d) = coefficient23 (f a) (f b) (f c) (f d) := by
  simp only [coefficient23, map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_one]

theorem coefficient24_map {L : Type*} [CommRing L] (f : K →+* L) (a b c d : K) :
    f (coefficient24 a b c d) = coefficient24 (f a) (f b) (f c) (f d) := by
  simp only [coefficient24, map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_one]

theorem coefficient25_map {L : Type*} [CommRing L] (f : K →+* L) (a b c d : K) :
    f (coefficient25 a b c d) = coefficient25 (f a) (f b) (f c) (f d) := by
  simp only [coefficient25, map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_one]

theorem coefficient26_map {L : Type*} [CommRing L] (f : K →+* L) (a b c d : K) :
    f (coefficient26 a b c d) = coefficient26 (f a) (f b) (f c) (f d) := by
  simp only [coefficient26, map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_one]

theorem coefficient_map {L : Type*} [CommRing L] (f : K →+* L) (a b c d : K)
    (i : Fin 27) : f (coefficient a b c d i) =
      coefficient (f a) (f b) (f c) (f d) i := by
  unfold coefficient
  rw [← List.getD_map (f := (f : K → L))]
  simp only [List.map_cons, List.map_nil, map_zero, coefficient0_map, coefficient1_map, coefficient2_map, coefficient3_map, coefficient4_map, coefficient5_map, coefficient6_map, coefficient7_map, coefficient8_map, coefficient9_map, coefficient10_map, coefficient11_map, coefficient12_map, coefficient13_map, coefficient14_map, coefficient15_map, coefficient16_map, coefficient17_map, coefficient18_map, coefficient19_map, coefficient20_map, coefficient21_map, coefficient22_map, coefficient23_map, coefficient24_map, coefficient25_map, coefficient26_map]

theorem leading_mul_monicPolynomial (a b c d : K) (h : IsUnit (729*a^11)) :
    C (729*a^11) * monicPolynomial a b c d = rawPolynomial a b c d := by
  unfold monicPolynomial rawPolynomial
  rw [mul_add, Finset.mul_sum]
  apply congrArg (fun t : K[X] => C (729*a^11)*X^27 + t)
  apply Finset.sum_congr rfl
  intro i hi
  rw [← mul_assoc, ← map_mul, ← mul_assoc, Ring.mul_inverse_cancel _ h, one_mul]

theorem rawPolynomial_eval₂ {A : Type*} [CommRing A] (f : K →+* A) (r : A) (a b c d : K) :
    (rawPolynomial a b c d).eval₂ f r = eliminant r (f a) (f b) (f c) (f d) := by
  simp only [rawPolynomial, eval₂_add, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X,
    eval₂_finsetSum, eval₂_ofNat, map_mul, map_pow, map_ofNat, map_one]
  simp only [coefficient_map]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, coefficient, List.getD_cons_zero, List.getD_cons_succ, Fin.sum_univ_zero, add_zero]
  unfold eliminant coefficient27
  ring

end HoldoutQ2.NewEliminant
