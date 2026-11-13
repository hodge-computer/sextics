import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.Polynomial.Div
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Lifting modular seed conditions to a complex cube root of two

The modular seed uses `r = 57` and `i = 33` in `ZMod 109`.  These satisfy
`r ^ 3 = 2` and `i ^ 2 = -1`.  Lifting the literal integer `57` to the complex
numbers does not preserve the first equation.  This file instead lifts finitely
many polynomial nonvanishing conditions to one complex root of `r ^ 3 = 2`.

The real intermediate value theorem supplies `a ^ 3 = 2` and `s ^ 2 = 3`.
The three distinct roots `a`, `(-a + a*s*i)/2`, and `(-a - a*s*i)/2` give
an explicit factorization of `X ^ 3 - 2`.  If a Gaussian-integer polynomial
vanishes at these three roots, the cubic divides it over the complex numbers.
Monic division descends this divisibility to the Gaussian integers.
Reduction modulo 109 and evaluation at 57 would then give zero.
The contrapositive supplies the required root.  Applying this argument to a
product preserves all the nonvanishing conditions at the same root.

The matrix version includes an additional polynomial factor for any
denominators introduced when clearing rational matrix entries.  It proves
transfer of stated modular determinant conditions; it does not assert the
unproved geometric interpretation of any matrix or the final residue theorem.
-/

noncomputable section

namespace CycleQ2DiamondSeed

open Polynomial
open scoped BigOperators

abbrev F109 := ZMod 109

instance : Fact (Nat.Prime 109) := ⟨by decide⟩
instance : Fact (1 < (109 : ℕ)) := ⟨by decide⟩

/-- Reduction of Gaussian integers with the modular square root of minus one. -/
def reduction : GaussianInt →+* F109 :=
  Zsqrtd.lift ⟨33, by decide⟩

@[simp] theorem reduction_i :
    reduction (Zsqrtd.sqrtd : GaussianInt) = 33 := by
  simp [reduction, Zsqrtd.lift_apply_apply]

@[simp] theorem complex_i :
    GaussianInt.toComplex (Zsqrtd.sqrtd : GaussianInt) = Complex.I := by
  simp [GaussianInt.toComplex, Zsqrtd.lift_apply_apply]

theorem modular_cube_root_two : (57 : F109) ^ 3 = 2 := by decide

/-- The monic relation that must survive the lift to characteristic zero. -/
def cubePolynomial : Polynomial GaussianInt := X ^ 3 - C 2

theorem cubePolynomial_monic : cubePolynomial.Monic :=
  monic_X_pow_sub_C 2 (by decide)

theorem cubePolynomial_reduction :
    cubePolynomial.eval₂ reduction (57 : F109) = 0 := by
  simp [cubePolynomial, map_ofNat, modular_cube_root_two]

/-- An elementary factorization of the cubic into three distinct complex
linear factors.  Only the real intermediate value theorem is needed. -/
theorem complex_cube_polynomial_factors :
    ∃ a b c : ℂ, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      (X ^ 3 - C (2 : ℂ)) = (X - C a) * (X - C b) * (X - C c) := by
  obtain ⟨r, _, hr⟩ :=
    intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 2)
      (continuous_pow 3).continuousOn
      (by norm_num : (2 : ℝ) ∈ Set.Icc ((1 : ℝ) ^ 3) ((2 : ℝ) ^ 3))
  obtain ⟨s, _, hs⟩ :=
    intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 2)
      (continuous_pow 2).continuousOn
      (by norm_num : (3 : ℝ) ∈ Set.Icc ((1 : ℝ) ^ 2) ((2 : ℝ) ^ 2))
  change r ^ 3 = 2 at hr
  change s ^ 2 = 3 at hs
  have hr0 : r ≠ 0 := by
    intro hz
    rw [hz] at hr
    norm_num at hr
  have hs0 : s ≠ 0 := by
    intro hz
    rw [hz] at hs
    norm_num at hs
  let a : ℂ := r
  let t : ℂ := (s : ℂ) * Complex.I
  let b : ℂ := (-a + a * t) / 2
  let c : ℂ := (-a - a * t) / 2
  have ha : a ^ 3 = 2 := by
    dsimp [a]
    rw [← Complex.ofReal_pow, hr]
    norm_num
  have ht : t ^ 2 = -3 := by
    dsimp [t]
    rw [mul_pow, ← Complex.ofReal_pow, hs, Complex.I_sq]
    norm_num
  have hbim : b.im = r * s / 2 := by
    simp [b, a, t, Complex.mul_im, Complex.mul_re]
  have hcim : c.im = -(r * s) / 2 := by
    simp [c, a, t, Complex.mul_im, Complex.mul_re]
  have hab : a ≠ b := by
    intro heq
    have heq' := congrArg Complex.im heq
    rw [hbim] at heq'
    change 0 = r * s / 2 at heq'
    exact div_ne_zero (mul_ne_zero hr0 hs0) (by norm_num) heq'.symm
  have hac : a ≠ c := by
    intro heq
    have heq' := congrArg Complex.im heq
    rw [hcim] at heq'
    change 0 = -(r * s) / 2 at heq'
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero hr0 hs0)) (by norm_num) heq'.symm
  have hbc : b ≠ c := by
    intro heq
    have heq' := congrArg Complex.im heq
    rw [hbim, hcim] at heq'
    apply mul_ne_zero hr0 hs0
    linear_combination heq'
  have hsum : a + b + c = 0 := by
    dsimp [b, c]
    ring
  have hpair : a * b + a * c + b * c = 0 := by
    dsimp [b, c]
    linear_combination -(a ^ 2 / 4) * ht
  have hprod : a * b * c = 2 := by
    dsimp [b, c]
    linear_combination ha - (a ^ 3 / 4) * ht
  refine ⟨a, b, c, hab, hac, hbc, ?_⟩
  calc
    X ^ 3 - C (2 : ℂ) =
        X ^ 3 - C (a + b + c) * X ^ 2 +
          C (a * b + a * c + b * c) * X - C (a * b * c) := by
      rw [hsum, hpair, hprod]
      simp
    _ = (X - C a) * (X - C b) * (X - C c) := by
      simp only [map_add, map_mul]
      ring

/-- A modular nonvanishing condition holds at some genuine complex cube root
of two.  This lifts the parameter relation, rather than the literal integer 57. -/
theorem exists_cube_root_two_eval_ne_zero (p : Polynomial GaussianInt)
    (hmod : p.eval₂ reduction (57 : F109) ≠ 0) :
    ∃ r : ℂ, r ^ 3 = 2 ∧ p.eval₂ GaussianInt.toComplex r ≠ 0 := by
  classical
  by_contra h
  have hall (r : ℂ) (hr : r ^ 3 = 2) :
      p.eval₂ GaussianInt.toComplex r = 0 := by
    by_contra hne
    exact h ⟨r, hr, hne⟩
  obtain ⟨a, b, c, hab, hac, hbc, hfactor⟩ := complex_cube_polynomial_factors
  have ha : a ^ 3 = 2 := by
    simpa [sub_eq_zero] using
      congrArg (fun q : Polynomial ℂ => q.eval a) hfactor
  have hb : b ^ 3 = 2 := by
    simpa [sub_eq_zero] using
      congrArg (fun q : Polynomial ℂ => q.eval b) hfactor
  have hc : c ^ 3 = 2 := by
    simpa [sub_eq_zero] using
      congrArg (fun q : Polynomial ℂ => q.eval c) hfactor
  have hdivC : (X ^ 3 - C (2 : ℂ)) ∣ p.map GaussianInt.toComplex := by
    have hpa : (p.map GaussianInt.toComplex).IsRoot a := by
      simpa only [Polynomial.IsRoot, Polynomial.eval_map] using hall a ha
    obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr hpa
    have hqb : q.eval b = 0 := by
      have hz : (p.map GaussianInt.toComplex).eval b = 0 := by
        simpa only [Polynomial.eval_map] using hall b hb
      rw [hq, eval_mul, eval_sub, eval_X, eval_C] at hz
      exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hab.symm)
    have hqc : q.eval c = 0 := by
      have hz : (p.map GaussianInt.toComplex).eval c = 0 := by
        simpa only [Polynomial.eval_map] using hall c hc
      rw [hq, eval_mul, eval_sub, eval_X, eval_C] at hz
      exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hac.symm)
    obtain ⟨q₂, hq₂⟩ := Polynomial.dvd_iff_isRoot.mpr hqb
    have hq₂c : q₂.eval c = 0 := by
      rw [hq₂, eval_mul, eval_sub, eval_X, eval_C] at hqc
      exact (mul_eq_zero.mp hqc).resolve_left (sub_ne_zero.mpr hbc.symm)
    obtain ⟨q₃, hq₃⟩ := Polynomial.dvd_iff_isRoot.mpr hq₂c
    refine ⟨q₃, ?_⟩
    rw [hq, hq₂, hq₃, hfactor]
    ring
  have hdiv : cubePolynomial ∣ p := by
    apply (Polynomial.map_dvd_map GaussianInt.toComplex
      GaussianInt.toComplex_injective cubePolynomial_monic).1
    simpa [cubePolynomial, map_ofNat] using hdivC
  exact hmod (Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero
    reduction (57 : F109) hdiv cubePolynomial_reduction)

/-- Finitely many modular conditions can be preserved at one common cube root.
This applies equally to determinant numerators and cleared denominators. -/
theorem exists_cube_root_two_simultaneous {ι : Type*} (s : Finset ι)
    (p : ι → Polynomial GaussianInt)
    (hmod : ∀ j ∈ s, (p j).eval₂ reduction (57 : F109) ≠ 0) :
    ∃ r : ℂ, r ^ 3 = 2 ∧
      ∀ j ∈ s, (p j).eval₂ GaussianInt.toComplex r ≠ 0 := by
  classical
  have hprod : (∏ j ∈ s, p j).eval₂ reduction (57 : F109) ≠ 0 := by
    rw [Polynomial.eval₂_finsetProd]
    exact Finset.prod_ne_zero_iff.mpr hmod
  obtain ⟨r, hr, hne⟩ := exists_cube_root_two_eval_ne_zero (∏ j ∈ s, p j) hprod
  refine ⟨r, hr, ?_⟩
  rw [Polynomial.eval₂_finsetProd] at hne
  exact Finset.prod_ne_zero_iff.mp hne

/-- A nonzero modular determinant can be lifted while imposing `r ^ 3 = 2`. -/
theorem exists_cube_root_two_matrix_det_ne_zero {n : Type*}
    [Fintype n] [DecidableEq n]
    (M : Matrix n n (Polynomial GaussianInt))
    (hmod : (M.map (Polynomial.eval₂ reduction (57 : F109))).det ≠ 0) :
    ∃ r : ℂ, r ^ 3 = 2 ∧
      (M.map (Polynomial.eval₂ GaussianInt.toComplex r)).det ≠ 0 := by
  have hdet : M.det.eval₂ reduction (57 : F109) ≠ 0 := by
    change (Polynomial.eval₂RingHom reduction (57 : F109)) M.det ≠ 0
    rw [RingHom.map_det]
    exact hmod
  obtain ⟨r, hr, hne⟩ := exists_cube_root_two_eval_ne_zero M.det hdet
  refine ⟨r, hr, ?_⟩
  change ((Polynomial.eval₂RingHom GaussianInt.toComplex r).mapMatrix M).det ≠ 0
  rw [← RingHom.map_det]
  exact hne

/-- Simultaneously lift any finite family of square minors, of possibly
different sizes, together with a factor containing all cleared denominators.
All the resulting determinant and denominator conditions use the same `r`. -/
theorem exists_cube_root_two_matrix_family {ι : Type*} [Fintype ι]
    {n : ι → Type*} [∀ j, Fintype (n j)] [∀ j, DecidableEq (n j)]
    (M : ∀ j, Matrix (n j) (n j) (Polynomial GaussianInt))
    (d : Polynomial GaussianInt)
    (hd : d.eval₂ reduction (57 : F109) ≠ 0)
    (hmod : ∀ j, ((M j).map (Polynomial.eval₂ reduction (57 : F109))).det ≠ 0) :
    ∃ r : ℂ, r ^ 3 = 2 ∧ d.eval₂ GaussianInt.toComplex r ≠ 0 ∧
      ∀ j, ((M j).map (Polynomial.eval₂ GaussianInt.toComplex r)).det ≠ 0 := by
  classical
  have hdet (j : ι) : (M j).det.eval₂ reduction (57 : F109) ≠ 0 := by
    change (Polynomial.eval₂RingHom reduction (57 : F109)) (M j).det ≠ 0
    rw [RingHom.map_det]
    exact hmod j
  have hprod : (d * ∏ j, (M j).det).eval₂ reduction (57 : F109) ≠ 0 := by
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_finsetProd]
    exact mul_ne_zero hd (Finset.prod_ne_zero_iff.mpr (fun j _ => hdet j))
  obtain ⟨r, hr, hne⟩ :=
    exists_cube_root_two_eval_ne_zero (d * ∏ j, (M j).det) hprod
  rw [Polynomial.eval₂_mul] at hne
  obtain ⟨hdC, hprodC⟩ := mul_ne_zero_iff.mp hne
  rw [Polynomial.eval₂_finsetProd] at hprodC
  refine ⟨r, hr, hdC, fun j => ?_⟩
  change ((Polynomial.eval₂RingHom GaussianInt.toComplex r).mapMatrix (M j)).det ≠ 0
  rw [← RingHom.map_det]
  exact Finset.prod_ne_zero_iff.mp hprodC j (Finset.mem_univ j)

end CycleQ2DiamondSeed
