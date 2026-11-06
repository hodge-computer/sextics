import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

/-! Exact positional encoding of polynomials with natural coefficients.
Evaluation at b is injective when each polynomial has coefficient sum less
than b. The bound is essential: a successful numerical evaluation without it
does not prove a polynomial identity. Prepared with OpenAI Codex assistance. -/
namespace CyclePolynomialDigits
open Polynomial

lemma eval_divX (p : Polynomial ℕ) (b : ℕ) :
    p.eval b=p.divX.eval b*b+p.coeff 0 := by
  conv_lhs => rw [← divX_mul_X_add p]
  simp

lemma coeff_zero_le_eval_one (p : Polynomial ℕ) : p.coeff 0≤p.eval 1 := by
  rw [eval_divX]
  omega

lemma divX_eval_one_le (p : Polynomial ℕ) : p.divX.eval 1≤p.eval 1 := by
  rw [eval_divX p]
  simp only [mul_one]
  omega

lemma eval_eq_implies_constant_eq (b : ℕ) (p q : Polynomial ℕ)
    (hp : p.eval 1<b) (hq : q.eval 1<b) (he : p.eval b=q.eval b) :
    p.coeff 0=q.coeff 0 := by
  have hp0 := (coeff_zero_le_eval_one p).trans_lt hp
  have hq0 := (coeff_zero_le_eval_one q).trans_lt hq
  have hm := congrArg (fun n => n%b) he
  rw [eval_divX p,eval_divX q] at hm
  simpa only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.mul_zero,Nat.zero_add,
    Nat.mod_eq_of_lt hp0,Nat.mod_eq_of_lt hq0,Nat.mod_mod,Nat.zero_mod] using hm

theorem eval_injective_bounded (b : ℕ) (hb : 0<b) (p q : Polynomial ℕ)
    (hp : p.eval 1<b) (hq : q.eval 1<b) (he : p.eval b=q.eval b) : p=q := by
  suffices h : ∀ n (p q : Polynomial ℕ),p.natDegree≤n → q.natDegree≤n →
      p.eval 1<b → q.eval 1<b → p.eval b=q.eval b → p=q by
    exact h (max p.natDegree q.natDegree) p q (le_max_left ..) (le_max_right ..) hp hq he
  intro n
  induction n with
  | zero =>
    intro p q hpd hqd hp hq he
    have hpC := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hpd)
    have hqC := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hqd)
    rw [hpC,hqC] at he ⊢
    simpa using he
  | succ n ih =>
    intro p q hpd hqd hp hq he
    have hc := eval_eq_implies_constant_eq b p q hp hq he
    have hd : p.divX.eval b=q.divX.eval b := by
      rw [eval_divX p,eval_divX q,hc] at he
      exact Nat.eq_of_mul_eq_mul_right hb (Nat.add_right_cancel he)
    have hdiv : p.divX=q.divX := by
      apply ih
      · rw [natDegree_divX_eq_natDegree_tsub_one]; omega
      · rw [natDegree_divX_eq_natDegree_tsub_one]; omega
      · exact (divX_eval_one_le p).trans_lt hp
      · exact (divX_eval_one_le q).trans_lt hq
      · exact hd
    calc
      p=p.divX*X+C (p.coeff 0) := (divX_mul_X_add p).symm
      _=q.divX*X+C (q.coeff 0) := by rw [hdiv,hc]
      _=q := divX_mul_X_add q

end CyclePolynomialDigits
#print axioms CyclePolynomialDigits.eval_injective_bounded
