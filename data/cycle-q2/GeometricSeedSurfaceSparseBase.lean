import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-! Source-preserving extraction of the actual seed Jacobian certificates. -/

set_option Elab.async false

/- Component: continuation_20261112/SeedSurfaceBranchSparseBase.lean -/
section
/-! A kernel-checkable sparse polynomial identity checker over Gaussian integers.

All executable definitions use natural-number tuples, lists, and structural
recursion. The checker is sound for arbitrary term lists; sortedness only
improves its ability to combine equal monomials and is never a proof premise.
No external arithmetic result or evaluator axiom is used.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option Elab.async false

namespace CycleQ2SeedSurfaceSparsePolynomial

abbrev Exponent := ℕ × ℕ × ℕ × ℕ × ℕ
abbrev Term := Exponent × GaussianInt
abbrev Sparse := List Term

def exponentAdd (a b : Exponent) : Exponent :=
  (a.1+b.1, a.2.1+b.2.1, a.2.2.1+b.2.2.1, a.2.2.2.1+b.2.2.2.1,
    a.2.2.2.2+b.2.2.2.2)

def code (e : Exponent) : ℕ :=
  e.1 + 32*(e.2.1 + 32*(e.2.2.1 + 32*(e.2.2.2.1 + 32*e.2.2.2.2)))

def termProduct (a b : Term) : Term :=
  (exponentAdd a.1 b.1, a.2*b.2)

/-- Fuel exhaustion preserves every term. Equality of exponent tuples is
checked before combining; the numeric sorting key need not be injective. -/
def addFuel : ℕ → Sparse → Sparse → Sparse
  | 0, p, q => p ++ q
  | _+1, [], q => q
  | _+1, p, [] => p
  | n+1, a::p, b::q =>
      if a.1 = b.1 then (a.1, a.2+b.2) :: addFuel n p q
      else if code a.1 ≤ code b.1 then a :: addFuel n p (b::q)
      else b :: addFuel n (a::p) q

def add (p q : Sparse) : Sparse := addFuel (p.length+q.length+1) p q

def mul (p q : Sparse) : Sparse :=
  p.foldr (fun a acc => add (q.map (termProduct a)) acc) []

def neg (p : Sparse) : Sparse := p.map (fun a => (a.1, -a.2))
def checkZero (p : Sparse) : Bool := p.all (fun a => decide (a.2 = 0))

section Soundness
variable {R : Type*} [CommRing R]
variable (φ : GaussianInt →+* R)

def monomial (x : Fin 5 → R) (e : Exponent) : R :=
  x 0 ^ e.1 * x 1 ^ e.2.1 * x 2 ^ e.2.2.1 *
    x 3 ^ e.2.2.2.1 * x 4 ^ e.2.2.2.2

def termValue (φ : GaussianInt →+* R) (x : Fin 5 → R) (a : Term) : R := φ a.2 * monomial x a.1
def eval (φ : GaussianInt →+* R) (x : Fin 5 → R) (p : Sparse) : R := (p.map (termValue φ x)).sum

@[simp] theorem eval_nil (x : Fin 5 → R) : eval φ x [] = 0 := rfl
@[simp] theorem eval_cons (x : Fin 5 → R) (a : Term) (p : Sparse) :
    eval φ x (a::p) = termValue φ x a + eval φ x p := rfl

theorem eval_append (x : Fin 5 → R) (p q : Sparse) :
    eval φ x (p ++ q) = eval φ x p + eval φ x q := by simp [eval]

theorem eval_addFuel (x : Fin 5 → R) (n : ℕ) (p q : Sparse) :
    eval φ x (addFuel n p q) = eval φ x p + eval φ x q := by
  induction n generalizing p q with
  | zero => exact eval_append φ x p q
  | succ n ih =>
    cases p with
    | nil => simp [addFuel]
    | cons a p =>
      cases q with
      | nil => simp [addFuel]
      | cons b q =>
        by_cases he : a.1 = b.1
        · simp only [addFuel, if_pos he, eval_cons, ih, termValue,
            map_add]
          rw [he]
          ring
        · simp only [addFuel, if_neg he]
          split <;> simp only [eval_cons, ih] <;> ring

@[simp] theorem eval_add (x : Fin 5 → R) (p q : Sparse) :
    eval φ x (add p q) = eval φ x p + eval φ x q := eval_addFuel φ x _ p q

theorem monomial_exponentAdd (x : Fin 5 → R) (a b : Exponent) :
    monomial x (exponentAdd a b) = monomial x a * monomial x b := by
  simp only [monomial, exponentAdd, pow_add]
  ring

theorem termValue_product (x : Fin 5 → R) (a b : Term) :
    termValue φ x (termProduct a b) = termValue φ x a * termValue φ x b := by
  simp only [termValue, termProduct, map_mul,
    monomial_exponentAdd]
  ring

theorem eval_mul (x : Fin 5 → R) (p q : Sparse) :
    eval φ x (mul p q) = eval φ x p * eval φ x q := by
  induction p with
  | nil => simp [mul]
  | cons a p ih =>
    change eval φ x (add (q.map (termProduct a)) (mul p q)) = _
    rw [eval_add, ih, eval_cons]
    have h : eval φ x (q.map (termProduct a)) = termValue φ x a * eval φ x q := by
      simp only [eval, List.map_map, Function.comp_def, termValue_product,
        List.sum_map_mul_left]
    rw [h]
    ring

theorem termValue_neg (x : Fin 5 → R) (a : Term) :
    termValue φ x (a.1, -a.2) = -termValue φ x a := by
  simp only [termValue, map_neg, neg_mul]

theorem eval_neg (x : Fin 5 → R) (p : Sparse) :
    eval φ x (neg p) = -eval φ x p := by
  simp only [neg, eval, List.map_map, Function.comp_def, termValue_neg]
  simpa only [List.map_map, Function.comp_def] using (List.sum_neg (p.map (termValue φ x))).symm

theorem eval_zero_of_all (x : Fin 5 → R) (p : Sparse)
    (h : p.all (fun a => decide (a.2 = 0)) = true) : eval φ x p = 0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [eval_cons, ih h.2, add_zero]
    unfold termValue
    rw [h.1, map_zero, zero_mul]

/-- A literal zero check yields the polynomial identity under every Gaussian-integer ring homomorphism. Concrete checks use ordinary kernel reduction. -/
theorem eval_eq_zero_of_check (x : Fin 5 → R) (p : Sparse)
    (h : checkZero p = true) : eval φ x p = 0 := eval_zero_of_all φ x p h

end Soundness
end CycleQ2SeedSurfaceSparsePolynomial

#print axioms CycleQ2SeedSurfaceSparsePolynomial.eval_eq_zero_of_check
#print axioms CycleQ2SeedSurfaceSparsePolynomial.eval_mul

/-! The literal r=57 branch certificate in exact Gaussian sparse form.
All coefficient pairs come unchanged from the stored characteristic-zero
certificate. Small generators are the first argument of sparse multiplication.
-/

set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
set_option Elab.async false
namespace CycleQ2SeedSurfaceBranchSparse
open CycleQ2SeedSurfaceSparsePolynomial
open scoped BigOperators

def generators : Fin 8 → Sparse :=
  ![[((6,0,0,0,0),⟨1,0⟩),
    ((0,0,6,0,0),⟨1,0⟩),
    ((0,3,0,3,0),⟨-185193,0⟩)],
    [((3,0,0,0,0),⟨1,0⟩),
    ((1,2,0,0,0),⟨1,0⟩),
    ((0,3,0,0,0),⟨0,-1⟩),
    ((0,0,3,0,0),⟨1,0⟩),
    ((1,0,1,1,0),⟨1,0⟩),
    ((0,1,1,1,0),⟨1,0⟩),
    ((0,0,0,3,0),⟨1,-1⟩)],
    [((6,1,0,0,0),⟨12,0⟩),
    ((5,2,0,0,0),⟨0,-18⟩),
    ((5,0,1,1,0),⟨6,0⟩),
    ((2,2,0,3,0),⟨1666737,0⟩),
    ((0,4,0,3,0),⟨555579,0⟩),
    ((0,2,1,4,0),⟨555579,0⟩)],
    [((5,0,2,0,0),⟨18,0⟩),
    ((2,0,5,0,0),⟨-18,0⟩),
    ((0,2,5,0,0),⟨-6,0⟩),
    ((6,0,0,1,0),⟨6,0⟩),
    ((5,1,0,1,0),⟨6,0⟩),
    ((0,0,6,1,0),⟨-6,0⟩)],
    [((6,0,1,0,0),⟨6,0⟩),
    ((5,1,1,0,0),⟨6,0⟩),
    ((5,0,0,2,0),⟨18,-18⟩),
    ((2,3,0,2,0),⟨1666737,0⟩),
    ((0,5,0,2,0),⟨555579,0⟩),
    ((0,3,1,3,0),⟨555579,0⟩)],
    [((1,1,5,0,0),⟨-12,0⟩),
    ((0,2,5,0,0),⟨0,18⟩),
    ((0,0,6,1,0),⟨-6,0⟩),
    ((0,2,2,3,0),⟨-1666737,0⟩),
    ((1,2,0,4,0),⟨-555579,0⟩),
    ((0,3,0,4,0),⟨-555579,0⟩)],
    [((1,4,0,2,0),⟨1111158,0⟩),
    ((0,5,0,2,0),⟨0,-1666737⟩),
    ((1,2,1,3,0),⟨-555579,0⟩),
    ((0,2,0,5,0),⟨-1666737,1666737⟩)],
    [((1,0,6,0,0),⟨6,0⟩),
    ((0,1,6,0,0),⟨6,0⟩),
    ((0,3,2,2,0),⟨1666737,0⟩),
    ((0,0,5,2,0),⟨18,-18⟩),
    ((1,3,0,3,0),⟨555579,0⟩),
    ((0,4,0,3,0),⟨555579,0⟩)]]

def combine (g n : Fin 8 → Sparse) : Sparse :=
  add (mul (g 0) (n 0)) (add (mul (g 1) (n 1))
    (add (mul (g 2) (n 2)) (add (mul (g 3) (n 3))
    (add (mul (g 4) (n 4)) (add (mul (g 5) (n 5))
    (add (mul (g 6) (n 6)) (mul (g 7) (n 7))))))))

theorem eval_combine {R : Type*} [CommRing R] (φ : GaussianInt →+* R)
    (x : Fin 5 → R) (g n : Fin 8 → Sparse) :
    eval φ x (combine g n) = ∑ k, eval φ x (g k) * eval φ x (n k) := by
  simp only [combine,eval_add,eval_mul,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,Fin.reduceSucc]

end CycleQ2SeedSurfaceBranchSparse
end


/- End of source-preserving extraction. -/
