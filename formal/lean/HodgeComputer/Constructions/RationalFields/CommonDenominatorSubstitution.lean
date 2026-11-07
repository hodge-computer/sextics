import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Prime.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Homogeneous polynomial substitution with one common denominator

For homogeneous polynomials `B, G i` of the same degree, this finite sum
represents `B^L * p(G/B)` without introducing rational functions. Its map
identity also proves the pullback needed to preserve denominator legality.
The degree bound is the only hypothesis on `p`; coefficients and variable
sets are arbitrary. The prime pullback criterion keeps denominator legality
separate from the rational substitution.

Extracted from the homogeneous transport prepared for `fqlx`'s symmetric
sextic draft, with OpenAI ChatGPT and Codex assistance.
-/

noncomputable section

namespace CommonDenominatorSubstitution

open MvPolynomial
open scoped BigOperators

variable {R σ τ S : Type*} [CommSemiring R] [CommSemiring S]

def cleared (p : MvPolynomial σ R) (B : MvPolynomial τ R)
    (G : σ → MvPolynomial τ R) (L : ℕ) : MvPolynomial τ R :=
  ∑ a ∈ p.support,
    C (coeff a p) * (∏ i ∈ a.support, G i ^ a i) *
      B ^ (L - a.sum (fun _ e => e))

/-- Equal homogeneous degrees make the denominator clearing homogeneous. -/
theorem cleared_homogeneous (p : MvPolynomial σ R) (B : MvPolynomial τ R)
    (G : σ → MvPolynomial τ R) (L k : ℕ)
    (hp : p.totalDegree ≤ L) (hB : B.IsHomogeneous k)
    (hG : ∀ i, (G i).IsHomogeneous k) :
    (cleared p B G L).IsHomogeneous (k * L) := by
  classical
  apply IsHomogeneous.sum
  intro a ha
  have hdeg : a.sum (fun _ e => e) ≤ L :=
    (MvPolynomial.le_totalDegree ha).trans hp
  have hprod : (∏ i ∈ a.support, G i ^ a i).IsHomogeneous
      (k * a.sum (fun _ e => e)) := by
    simpa only [Finsupp.sum, Finset.mul_sum] using
      IsHomogeneous.prod a.support (fun i => G i ^ a i) (fun i => k * a i)
        (fun i _ => (hG i).pow (a i))
  convert (hprod.C_mul (coeff a p)).mul (hB.pow (L - a.sum (fun _ e => e))) using 1
  rw [← Nat.mul_add, Nat.add_sub_of_le hdeg]

/-- Polynomial pullback identity. It works even when `b = 0`, since no
division occurs. In particular, it can prove legality before passing to a
fraction field. -/
theorem map_cleared (p : MvPolynomial σ R) (B : MvPolynomial τ R)
    (G : σ → MvPolynomial τ R) (L : ℕ) (hp : p.totalDegree ≤ L)
    (φ : MvPolynomial τ R →+* S) (b : S) (y : σ → S)
    (hB : φ B = b) (hG : ∀ i, φ (G i) = b * y i) :
    φ (cleared p B G L) =
      b ^ L * MvPolynomial.eval₂ (φ.comp MvPolynomial.C) y p := by
  classical
  rw [cleared, map_sum]
  change _ = b ^ L * (∑ a ∈ p.support,
    φ (C (coeff a p)) * (∏ i ∈ a.support, y i ^ a i))
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hdeg : a.sum (fun _ e => e) ≤ L :=
    (MvPolynomial.le_totalDegree ha).trans hp
  simp only [map_mul, map_pow, map_prod, hB, hG, mul_pow,
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hpow : b ^ (∑ i ∈ a.support, a i) *
      b ^ (L - a.sum (fun _ e => e)) = b ^ L := by
    rw [← pow_add]
    congr 1
    exact Nat.add_sub_of_le hdeg
  calc
    _ = (b ^ (∑ i ∈ a.support, a i) * b ^ (L - a.sum (fun _ e => e))) *
        (φ (C (coeff a p)) * ∏ i ∈ a.support, y i ^ a i) := by ring
    _ = _ := by rw [hpow]

/-- A prime divisor on the pullback chart detects denominator legality of
the homogeneous clearing. This uses only polynomial substitution, so it
does not assume the very denominator nonvanishing that it establishes. -/
theorem not_dvd_cleared (p : MvPolynomial σ R) (B : MvPolynomial τ R)
    (G : σ → MvPolynomial τ R) (L : ℕ) (hp : p.totalDegree ≤ L)
    (φ : MvPolynomial τ R →+* S) (b : S) (y : σ → S)
    (hB : φ B = b) (hG : ∀ i, φ (G i) = b * y i)
    (q : MvPolynomial τ R) (a : S) (ha : Prime a)
    (hq : a ∣ φ q) (hb : ¬a ∣ b)
    (hpull : ¬a ∣ MvPolynomial.eval₂ (φ.comp MvPolynomial.C) y p) :
    ¬q ∣ cleared p B G L := by
  intro hdiv
  have hmap : a ∣ φ (cleared p B G L) := hq.trans (map_dvd φ hdiv)
  rw [map_cleared p B G L hp φ b y hB hG] at hmap
  exact ha.not_dvd_mul (fun hpow => hb (ha.dvd_of_dvd_pow hpow)) hpull hmap

/-- The same finite polynomial is the usual rational substitution whenever
the common denominator is nonzero. -/
theorem map_cleared_fraction {K : Type*} [Field K]
    (p : MvPolynomial σ R) (B : MvPolynomial τ R)
    (G : σ → MvPolynomial τ R) (L : ℕ) (hp : p.totalDegree ≤ L)
    (φ : MvPolynomial τ R →+* K) (hB : φ B ≠ 0) :
    φ (cleared p B G L) = (φ B) ^ L *
      MvPolynomial.eval₂ (φ.comp MvPolynomial.C) (fun i => φ (G i) / φ B) p := by
  apply map_cleared p B G L hp φ (φ B) _ rfl
  intro i
  field_simp

#print axioms cleared_homogeneous
#print axioms map_cleared
#print axioms not_dvd_cleared
#print axioms map_cleared_fraction

end CommonDenominatorSubstitution
