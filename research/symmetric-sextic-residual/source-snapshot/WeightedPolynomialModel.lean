import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-!
An exact coefficient model for the weighted multiplication calculation.
The coefficient functions are executable arithmetic on exponent vectors;
their meaning is proved using Mathlib's MvPolynomial coefficient theorems.
-/
namespace WeightedSupport.PolynomialModel

open scoped BigOperators
open MvPolynomial

abbrev Exponent := Fin 6 → ℕ
abbrev Poly := MvPolynomial (Fin 6) ℤ

noncomputable def exponent (e : Exponent) : Fin 6 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm e

@[simp] theorem exponent_apply (e : Exponent) (i : Fin 6) : exponent e i = e i := rfl

def subtract (e a : Exponent) : Exponent := fun i => e i - a i

def lower (e : Exponent) (i : Fin 6) : Exponent :=
  fun j => e j - if i = j then 1 else 0

theorem exponent_subtract (e a : Exponent) :
    exponent (subtract e a) = exponent e - exponent a := by
  ext i
  rfl

theorem exponent_lower (e : Exponent) (i : Fin 6) :
    exponent (lower e i) = exponent e - Finsupp.single i 1 := by
  ext j
  simp [lower, Finsupp.single_apply]

noncomputable def L : Poly :=
  ∑ i : Fin 6, (if i = 5 then (0 : ℤ) else 1) • X i

noncomputable def D : Poly := X 0 - X 1 + X 2 - X 3
noncomputable def H : Poly := X 0 + X 1 + X 2 + X 3
noncomputable def Q : Poly := D * L ^ 10 + C 5 * X 5 * (D * L ^ 8)

def total (e : Exponent) : ℕ := e 0 + (e 1 + (e 2 + (e 3 + (e 4 + e 5))))

def factorialProduct (e : Exponent) : ℕ :=
  (e 0).factorial * ((e 1).factorial * ((e 2).factorial *
    ((e 3).factorial * ((e 4).factorial * (e 5).factorial))))

def powerCoeff (n : ℕ) (e : Exponent) : ℤ :=
  if e 5 = 0 ∧ total e = n then
    (n.factorial / factorialProduct e : ℕ)
  else 0

def variableCoeff (i : Fin 6) (f : Exponent → ℤ) (e : Exponent) : ℤ :=
  if e i = 0 then 0 else f (lower e i)

def differenceCoeff (f : Exponent → ℤ) (e : Exponent) : ℤ :=
  variableCoeff 0 f e - variableCoeff 1 f e + variableCoeff 2 f e - variableCoeff 3 f e

def sumCoeff (f : Exponent → ℤ) (e : Exponent) : ℤ :=
  variableCoeff 0 f e + variableCoeff 1 f e + variableCoeff 2 f e + variableCoeff 3 f e

def qCoeff (e : Exponent) : ℤ :=
  differenceCoeff (powerCoeff 10) e + 5 * variableCoeff 5 (differenceCoeff (powerCoeff 8)) e

def hqCoeff (e : Exponent) : ℤ := sumCoeff qCoeff e

theorem L_explicit : L = X 0 + X 1 + X 2 + X 3 + X 4 := by
  simp [L, Fin.sum_univ_succ, add_assoc]

theorem coeff_power (n : ℕ) (e : Exponent) :
    coeff (exponent e) (L ^ n) = powerCoeff n e := by
  rw [L, coeff_linearCombination_X_pow_of_fintype]
  rw [Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)]
  rw [(exponent e).sum_fintype (fun _ m => m) (fun _ => rfl)]
  rw [(exponent e).prod_fintype (fun r m => (if r = 5 then (0 : ℤ) else 1) ^ m)
    (fun _ => pow_zero _)]
  simp only [exponent_apply]
  have hs : (∑ i : Fin 6, e i) = total e := by simp [total, Fin.sum_univ_succ]
  have hm : Nat.multinomial Finset.univ (exponent e) = (total e).factorial / factorialProduct e := by
    simp [Nat.multinomial, Fin.sum_univ_succ, Fin.prod_univ_succ, exponent, total, factorialProduct]
  have hp : (∏ i : Fin 6, (if i = 5 then (0 : ℤ) else 1) ^ e i) = (0 : ℤ) ^ e 5 := by
    simp [Fin.prod_univ_succ]
  simp only [hs, hm, hp]
  by_cases h : e 5 = 0
  · simp only [powerCoeff, h, pow_zero, mul_one, true_and]
    split_ifs with hn
    · rw [hn]
    · rfl
  · simp [powerCoeff, h, zero_pow h]

theorem coeff_variable (i : Fin 6) (p : Poly) (f : Exponent → ℤ)
    (hf : ∀ e, coeff (exponent e) p = f e) (e : Exponent) :
    coeff (exponent e) (X i * p) = variableCoeff i f e := by
  rw [coeff_X_mul']
  simp only [Finsupp.mem_support_iff, exponent_apply, ← exponent_lower]
  by_cases h : e i = 0
  · simp [variableCoeff, h]
  · simp [variableCoeff, h, hf]

theorem coeff_difference (p : Poly) (f : Exponent → ℤ)
    (hf : ∀ e, coeff (exponent e) p = f e) (e : Exponent) :
    coeff (exponent e) (D * p) = differenceCoeff f e := by
  simp only [D, sub_mul, add_mul, coeff_sub, coeff_add, coeff_variable _ p f hf,
    differenceCoeff]

theorem coeff_sum (p : Poly) (f : Exponent → ℤ)
    (hf : ∀ e, coeff (exponent e) p = f e) (e : Exponent) :
    coeff (exponent e) (H * p) = sumCoeff f e := by
  simp only [H, add_mul, MvPolynomial.coeff_add, coeff_variable _ p f hf, sumCoeff]

theorem coeff_Q (e : Exponent) : coeff (exponent e) Q = qCoeff e := by
  unfold Q
  rw [coeff_add, mul_assoc, coeff_C_mul, coeff_difference _ _ (coeff_power 10),
    coeff_variable 5 _ _ (coeff_difference _ _ (coeff_power 8))]
  rfl

theorem coeff_HQ (e : Exponent) : coeff (exponent e) (H * Q) = hqCoeff e :=
  coeff_sum _ _ coeff_Q e

def swapIndex : Fin 6 → Fin 6 := ![1, 0, 3, 2, 4, 5]

def sigma (e : Exponent) : Exponent := fun i => e (swapIndex i)

noncomputable def orbitPolynomial (a : Exponent) : Poly :=
  monomial (exponent a) 1 + if a = sigma a then 0 else monomial (exponent (sigma a)) 1

def shiftedCoeff (f : Exponent → ℤ) (a e : Exponent) : ℤ :=
  if ∀ i, a i ≤ e i then f (subtract e a) else 0

def orbitCoeff (f : Exponent → ℤ) (a e : Exponent) : ℤ :=
  shiftedCoeff f a e + if a = sigma a then 0 else shiftedCoeff f (sigma a) e

theorem coeff_times_monomial (p : Poly) (f : Exponent → ℤ)
    (hf : ∀ e, coeff (exponent e) p = f e) (a e : Exponent) :
    coeff (exponent e) (p * monomial (exponent a) 1) = shiftedCoeff f a e := by
  rw [coeff_mul_monomial', ← exponent_subtract]
  have hle : exponent a ≤ exponent e ↔ ∀ i, a i ≤ e i := Finsupp.le_def
  simp only [hle, mul_one, hf, shiftedCoeff]

theorem coeff_times_orbit (p : Poly) (f : Exponent → ℤ)
    (hf : ∀ e, coeff (exponent e) p = f e) (a e : Exponent) :
    coeff (exponent e) (p * orbitPolynomial a) = orbitCoeff f a e := by
  classical
  by_cases h : a = sigma a
  · rw [orbitPolynomial, if_pos h, add_zero, orbitCoeff, if_pos h, add_zero]
    exact coeff_times_monomial p f hf a e
  · rw [orbitPolynomial, if_neg h, mul_add, MvPolynomial.coeff_add,
      coeff_times_monomial p f hf, coeff_times_monomial p f hf,
      orbitCoeff, if_neg h]

theorem coeff_Q_orbit (a e : Exponent) :
    coeff (exponent e) (Q * orbitPolynomial a) = orbitCoeff qCoeff a e :=
  coeff_times_orbit Q qCoeff coeff_Q a e

theorem coeff_HQ_orbit (a e : Exponent) :
    coeff (exponent e) ((H * Q) * orbitPolynomial a) = orbitCoeff hqCoeff a e :=
  coeff_times_orbit (H * Q) hqCoeff coeff_HQ a e

#print axioms coeff_Q_orbit
#print axioms coeff_HQ_orbit

end WeightedSupport.PolynomialModel
