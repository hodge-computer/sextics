import HodgeComputer.Constructions.PolynomialEncoding.BivariateExpressions
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! Differentiation of the sparse bivariate expressions used in the exact
coefficient certificates. Prepared for fqlx with OpenAI Codex assistance. -/
namespace PolynomialEncoding.BivariateExpressions
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions MvPolynomial

def dx : Biv → Biv
  | .nil => .nil
  | .cons _ 0 _ p => dx p
  | .cons a (i+1) j p => .cons (.mul (.natCast (i+1)) a) i j (dx p)

def dy : Biv → Biv
  | .nil => .nil
  | .cons _ _ 0 p => dy p
  | .cons a i (j+1) p => .cons (.mul (.natCast (j+1)) a) i j (dy p)

variable {K : Type*} [CommRing K]

lemma ringEval_C (v : ℕ → K) (e : Expr) :
    ringEval (fun i => C (σ := Fin 2) (v i)) e=C (ringEval v e) := by
  induction e <;> simp_all [ringEval]

lemma pderiv_denote_dx (v : ℕ → K) (p : Biv) :
    pderiv 0 (denote (fun i => C (v i)) (X (0 : Fin 2)) (X 1) p)=
      denote (fun i => C (v i)) (X (0 : Fin 2)) (X 1) (dx p) := by
  induction p with
  | nil => simp [denote,dx]
  | cons a i j p ih =>
    rw [denote,map_add,ih]
    rw [ringEval_C]
    cases i with
    | zero => simp [dx,denote,pderiv_mul,pderiv_pow,Pi.single_apply]
    | succ i =>
      simp [dx,denote,ringEval,ringEval_C,pderiv_mul,pderiv_pow,Pi.single_apply]
      ring

lemma pderiv_denote_dy (v : ℕ → K) (p : Biv) :
    pderiv 1 (denote (fun i => C (v i)) (X (0 : Fin 2)) (X 1) p)=
      denote (fun i => C (v i)) (X (0 : Fin 2)) (X 1) (dy p) := by
  induction p with
  | nil => simp [denote,dy]
  | cons a i j p ih =>
    rw [denote,map_add,ih]
    rw [ringEval_C]
    cases j with
    | zero => simp [dy,denote,pderiv_mul,pderiv_pow,Pi.single_apply]
    | succ j =>
      simp [dy,denote,ringEval,ringEval_C,pderiv_mul,pderiv_pow,Pi.single_apply]
      ring

end PolynomialEncoding.BivariateExpressions
