import HodgeComputer.Constructions.PolynomialEncoding.SignedExpressions
import Mathlib.Tactic

/-! Sparse bivariate polynomials whose coefficients are ring expressions.
The operations preserve evaluation, with no assumptions about ordering or
uniqueness of the input terms. This connects coefficient certificates to the
whole covariant identity. Prepared with OpenAI Codex assistance. -/
namespace PolynomialEncoding.BivariateExpressions
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions

inductive Biv where
  | nil
  | cons (coefficient : Expr) (xDegree yDegree : ℕ) (rest : Biv)

def append : Biv → Biv → Biv
  | .nil,q => q
  | .cons a i j p,q => .cons a i j (append p q)

def merge : ℕ → Biv → Biv → Biv
  | 0,p,q => append p q
  | _+1,.nil,q => q
  | _+1,p,.nil => p
  | n+1,.cons a i j p,.cons b k l q =>
    if i=k ∧ j=l then .cons (.add a b) i j (merge n p q)
    else if 32*i+j>32*k+l then .cons a i j (merge n p (.cons b k l q))
    else .cons b k l (merge n (.cons a i j p) q)

def scale (a : Expr) (i j : ℕ) : Biv → Biv
  | .nil => .nil
  | .cons b k l q => .cons (.mul a b) (i+k) (j+l) (scale a i j q)

def multiply : Biv → Biv → Biv
  | .nil,_ => .nil
  | .cons a i j p,q => merge 512 (scale a i j q) (multiply p q)

variable {K : Type*} [CommRing K]
def denote (v : ℕ → K) (x y : K) : Biv → K
  | .nil => 0
  | .cons a i j p => ringEval v a*x^i*y^j+denote v x y p

lemma append_denote (v : ℕ → K) (x y : K) (p q : Biv) :
    denote v x y (append p q)=denote v x y p+denote v x y q := by
  induction p with
  | nil => simp [append,denote]
  | cons a i j p ih => simp [append,denote,ih,add_assoc]

lemma merge_denote (v : ℕ → K) (x y : K) (n : ℕ) (p q : Biv) :
    denote v x y (merge n p q)=denote v x y p+denote v x y q := by
  induction n generalizing p q with
  | zero => exact append_denote v x y p q
  | succ n ih =>
    cases p with
    | nil => simp [merge,denote]
    | cons a i j p =>
      cases q with
      | nil => simp [merge,denote]
      | cons b k l q =>
        simp only [merge]
        split_ifs with h h'
        · obtain ⟨rfl,rfl⟩ := h
          simp only [denote,ringEval,ih]
          ring
        · simp only [denote,ih]; ring
        · simp only [denote,ih]; ring

lemma scale_denote (v : ℕ → K) (x y : K) (a : Expr) (i j : ℕ) (p : Biv) :
    denote v x y (scale a i j p)=ringEval v a*x^i*y^j*denote v x y p := by
  induction p with
  | nil => simp [scale,denote]
  | cons b k l p ih =>
    simp only [scale,denote,ringEval,ih,pow_add]
    ring

theorem multiply_denote (v : ℕ → K) (x y : K) (p q : Biv) :
    denote v x y (multiply p q)=denote v x y p*denote v x y q := by
  induction p with
  | nil => simp [multiply,denote]
  | cons a i j p ih =>
    rw [multiply,merge_denote,scale_denote,ih]
    simp only [denote]
    ring

lemma cons_denote_eq (v : ℕ → K) (x y : K) (a b : Expr) (i j : ℕ) (p q : Biv)
    (hab : ringEval v a=ringEval v b) (hpq : denote v x y p=denote v x y q) :
    denote v x y (.cons a i j p)=denote v x y (.cons b i j q) := by
  simp only [denote,hab,hpq]

end PolynomialEncoding.BivariateExpressions
#print axioms PolynomialEncoding.BivariateExpressions.multiply_denote
