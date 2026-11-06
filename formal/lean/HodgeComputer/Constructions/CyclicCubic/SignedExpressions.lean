import Mathlib.Algebra.Ring.GrindInstances
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Positive and negative semiring parts of a ring expression.
This permits positional-encoding certificates to use nonnegative polynomial
coefficients while retaining the exact signed expression. All semantic
identities are proved, and no executable extension is introduced.
Prepared with OpenAI Codex assistance. -/
namespace CycleSignedExpressions
open Lean.Grind.CommRing

def pairMul {R : Type*} [CommSemiring R] (p q : R × R) : R × R :=
  (p.1*q.1+p.2*q.2,p.1*q.2+p.2*q.1)
def pairPow {R : Type*} [CommSemiring R] (p : R × R) : ℕ → R × R
  | 0 => (1,0)
  | n+1 => pairMul p (pairPow p n)
def numberPair {R : Type*} [CommSemiring R] : Int → R × R
  | .ofNat n => (n,0)
  | .negSucc n => (0,n+1)
def splitEval {R : Type*} [CommSemiring R] (v : Nat → R) : Expr → R × R
  | .num n => numberPair n
  | .natCast n => (n,0)
  | .intCast n => numberPair n
  | .var i => (v i,0)
  | .neg a => let p:=splitEval v a; (p.2,p.1)
  | .add a b => let p:=splitEval v a; let q:=splitEval v b; (p.1+q.1,p.2+q.2)
  | .sub a b => let p:=splitEval v a; let q:=splitEval v b; (p.1+q.2,p.2+q.1)
  | .mul a b => pairMul (splitEval v a) (splitEval v b)
  | .pow a n => pairPow (splitEval v a) n

def ringEval {R : Type*} [CommRing R] (v : Nat → R) : Expr → R
  | .num n => n
  | .natCast n => n
  | .intCast n => n
  | .var i => v i
  | .neg a => -ringEval v a
  | .add a b => ringEval v a+ringEval v b
  | .sub a b => ringEval v a-ringEval v b
  | .mul a b => ringEval v a*ringEval v b
  | .pow a n => ringEval v a^n

section Semiring
variable {R S : Type*} [CommSemiring R] [CommSemiring S]
lemma pairMul_map (φ : R →+* S) (p q : R×R) :
    (φ (pairMul p q).1,φ (pairMul p q).2)=
      pairMul (φ p.1,φ p.2) (φ q.1,φ q.2) := by simp [pairMul]
lemma pairPow_map (φ : R →+* S) (p : R×R) (n : ℕ) :
    (φ (pairPow p n).1,φ (pairPow p n).2)=pairPow (φ p.1,φ p.2) n := by
  induction n with
  | zero => simp [pairPow]
  | succ n ih =>
    change (φ (pairMul p (pairPow p n)).1,φ (pairMul p (pairPow p n)).2)=_
    rw [pairMul_map,ih]
    rfl
lemma splitEval_map (φ : R →+* S) (v : Nat → R) (e : Expr) :
    (φ (splitEval v e).1,φ (splitEval v e).2)=splitEval (fun i=>φ (v i)) e := by
  induction e with
  | num n => cases n <;> simp [splitEval,numberPair]
  | intCast n => cases n <;> simp [splitEval,numberPair]
  | natCast n => simp [splitEval]
  | var i => simp [splitEval]
  | neg a ih =>
    have h1:=congrArg Prod.fst ih
    have h2:=congrArg Prod.snd ih
    simp only [splitEval]
    exact Prod.ext h2 h1
  | add a b ha hb =>
    have ha1:=congrArg Prod.fst ha; have ha2:=congrArg Prod.snd ha
    have hb1:=congrArg Prod.fst hb; have hb2:=congrArg Prod.snd hb
    dsimp only at ha1 ha2 hb1 hb2
    simp only [splitEval,map_add,ha1,ha2,hb1,hb2]
  | sub a b ha hb =>
    have ha1:=congrArg Prod.fst ha; have ha2:=congrArg Prod.snd ha
    have hb1:=congrArg Prod.fst hb; have hb2:=congrArg Prod.snd hb
    dsimp only at ha1 ha2 hb1 hb2
    simp only [splitEval,map_add,ha1,ha2,hb1,hb2]
  | mul a b ha hb =>
    change (φ (pairMul (splitEval v a) (splitEval v b)).1,
      φ (pairMul (splitEval v a) (splitEval v b)).2)=_
    rw [pairMul_map,ha,hb]
    rfl
  | pow a n ha =>
    change (φ (pairPow (splitEval v a) n).1,φ (pairPow (splitEval v a) n).2)=_
    rw [pairPow_map,ha]
    rfl
end Semiring

section Ring
variable {R : Type*} [CommRing R]
lemma pairPow_difference (p : R×R) (n : ℕ) :
    (pairPow p n).1-(pairPow p n).2=(p.1-p.2)^n := by
  induction n with
  | zero => simp [pairPow]
  | succ n ih =>
    simp only [pairPow,pairMul,Prod.fst,Prod.snd,pow_succ']
    linear_combination (p.1-p.2)*ih
lemma splitEval_difference (v : Nat → R) (e : Expr) :
    (splitEval v e).1-(splitEval v e).2=ringEval v e := by
  induction e with
  | num n => cases n <;> simp [splitEval,numberPair,ringEval,Int.cast_negSucc]
  | intCast n => cases n <;> simp [splitEval,numberPair,ringEval,Int.cast_negSucc]
  | natCast n => simp [splitEval,ringEval]
  | var i => simp [splitEval,ringEval]
  | neg a ha => simp only [splitEval,ringEval]; linear_combination -ha
  | add a b ha hb => simp only [splitEval,ringEval]; linear_combination ha+hb
  | sub a b ha hb => simp only [splitEval,ringEval]; linear_combination ha-hb
  | mul a b ha hb =>
    simp only [splitEval,pairMul,ringEval,Prod.fst,Prod.snd]
    rw [← ha,← hb]
    ring
  | pow a n ha => rw [splitEval,pairPow_difference,ha]; rfl

lemma ringEval_denote (ctx : Context R) (e : Expr) :
    ringEval (fun i=>ctx.get i) e=e.denote ctx := by
  induction e <;> simp only [ringEval,Expr.denote,Var.denote,denoteInt_eq, *]
end Ring
end CycleSignedExpressions
#print axioms CycleSignedExpressions.splitEval_difference
