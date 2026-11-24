import Mathlib.Tactic

/-! # Sparse polynomials and Horner blocks over the field of 109 elements -/

set_option Elab.async false

/- Component: continuation_3/SparseModularPolynomial.lean -/
section
/-! A kernel-checkable sparse polynomial identity checker in characteristic 109.

All executable definitions use natural-number tuples, lists, and structural
recursion. The checker is sound for arbitrary term lists; sortedness only
improves its ability to combine equal monomials and is never a proof premise.
No external arithmetic result or evaluator axiom is used.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option Elab.async false

namespace CycleQ2SparseModularPolynomial

abbrev Exponent := ℕ × ℕ × ℕ × ℕ × ℕ
abbrev Term := Exponent × ℕ
abbrev Sparse := List Term

def exponentAdd (a b : Exponent) : Exponent :=
  (a.1+b.1, a.2.1+b.2.1, a.2.2.1+b.2.2.1, a.2.2.2.1+b.2.2.2.1,
    a.2.2.2.2+b.2.2.2.2)

def code (e : Exponent) : ℕ :=
  e.1 + 32*(e.2.1 + 32*(e.2.2.1 + 32*(e.2.2.2.1 + 32*e.2.2.2.2)))

def termProduct (a b : Term) : Term :=
  (exponentAdd a.1 b.1, (a.2*b.2)%109)

/-- Fuel exhaustion preserves every term. Equality of exponent tuples is
checked before combining; the numeric sorting key need not be injective. -/
def addFuel : ℕ → Sparse → Sparse → Sparse
  | 0, p, q => p ++ q
  | _+1, [], q => q
  | _+1, p, [] => p
  | n+1, a::p, b::q =>
      if a.1 = b.1 then (a.1, (a.2+b.2)%109) :: addFuel n p q
      else if code a.1 ≤ code b.1 then a :: addFuel n p (b::q)
      else b :: addFuel n (a::p) q

def add (p q : Sparse) : Sparse := addFuel (p.length+q.length+1) p q

def mul (p q : Sparse) : Sparse :=
  p.foldr (fun a acc => add (q.map (termProduct a)) acc) []

def neg (p : Sparse) : Sparse := p.map (fun a => (a.1, (108*a.2)%109))
def checkZero (p : Sparse) : Bool := p.all (fun a => a.2%109 == 0)

section Soundness
variable {R : Type*} [CommRing R] [CharP R 109]

def monomial (x : Fin 5 → R) (e : Exponent) : R :=
  x 0 ^ e.1 * x 1 ^ e.2.1 * x 2 ^ e.2.2.1 *
    x 3 ^ e.2.2.2.1 * x 4 ^ e.2.2.2.2

def termValue (x : Fin 5 → R) (a : Term) : R := a.2 * monomial x a.1
def eval (x : Fin 5 → R) (p : Sparse) : R := (p.map (termValue x)).sum

@[simp] theorem eval_nil (x : Fin 5 → R) : eval x [] = 0 := rfl
@[simp] theorem eval_cons (x : Fin 5 → R) (a : Term) (p : Sparse) :
    eval x (a::p) = termValue x a + eval x p := rfl

theorem eval_append (x : Fin 5 → R) (p q : Sparse) :
    eval x (p ++ q) = eval x p + eval x q := by simp [eval]

theorem eval_addFuel (x : Fin 5 → R) (n : ℕ) (p q : Sparse) :
    eval x (addFuel n p q) = eval x p + eval x q := by
  induction n generalizing p q with
  | zero => exact eval_append x p q
  | succ n ih =>
    cases p with
    | nil => simp [addFuel]
    | cons a p =>
      cases q with
      | nil => simp [addFuel]
      | cons b q =>
        by_cases he : a.1 = b.1
        · simp only [addFuel, if_pos he, eval_cons, ih, termValue,
            ← CharP.cast_eq_mod R 109, Nat.cast_add]
          rw [he]
          ring
        · simp only [addFuel, if_neg he]
          split <;> simp only [eval_cons, ih] <;> ring

@[simp] theorem eval_add (x : Fin 5 → R) (p q : Sparse) :
    eval x (add p q) = eval x p + eval x q := eval_addFuel x _ p q

theorem monomial_exponentAdd (x : Fin 5 → R) (a b : Exponent) :
    monomial x (exponentAdd a b) = monomial x a * monomial x b := by
  simp only [monomial, exponentAdd, pow_add]
  ring

theorem termValue_product (x : Fin 5 → R) (a b : Term) :
    termValue x (termProduct a b) = termValue x a * termValue x b := by
  simp only [termValue, termProduct, ← CharP.cast_eq_mod R 109, Nat.cast_mul,
    monomial_exponentAdd]
  ring

theorem eval_mul (x : Fin 5 → R) (p q : Sparse) :
    eval x (mul p q) = eval x p * eval x q := by
  induction p with
  | nil => simp [mul]
  | cons a p ih =>
    change eval x (add (q.map (termProduct a)) (mul p q)) = _
    rw [eval_add, ih, eval_cons]
    have h : eval x (q.map (termProduct a)) = termValue x a * eval x q := by
      simp only [eval, List.map_map, Function.comp_def, termValue_product,
        List.sum_map_mul_left]
    rw [h]
    ring

theorem termValue_neg (x : Fin 5 → R) (a : Term) :
    termValue x (a.1, (108*a.2)%109) = -termValue x a := by
  have h108 : (108 : R) = -1 := by
    have h109 := CharP.cast_eq_zero R 109
    linear_combination h109
  simp only [termValue, ← CharP.cast_eq_mod R 109, Nat.cast_mul, Nat.cast_ofNat]
  rw [h108]
  ring

theorem eval_neg (x : Fin 5 → R) (p : Sparse) :
    eval x (neg p) = -eval x p := by
  simp only [neg, eval, List.map_map, Function.comp_def, termValue_neg]
  simpa only [List.map_map, Function.comp_def] using (List.sum_neg (p.map (termValue x))).symm

theorem eval_zero_of_all (x : Fin 5 → R) (p : Sparse)
    (h : p.all (fun a => a.2%109 == 0) = true) : eval x p = 0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    rw [eval_cons, ih h.2, add_zero]
    unfold termValue
    rw [CharP.cast_eq_mod R 109 a.2, h.1, Nat.cast_zero, zero_mul]

/-- A literal zero check yields the polynomial identity in any commutative
ring of characteristic 109. Concrete checks use ordinary kernel reduction. -/
theorem eval_eq_zero_of_check (x : Fin 5 → R) (p : Sparse)
    (h : checkZero p = true) : eval x p = 0 := eval_zero_of_all x p h

end Soundness
end CycleQ2SparseModularPolynomial

#print axioms CycleQ2SparseModularPolynomial.eval_eq_zero_of_check
#print axioms CycleQ2SparseModularPolynomial.eval_mul
end

/- Component: continuation_3/SparseModularLayers.lean -/
section
/-! Horner blocks for small independent kernel checks of sparse identities. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option Elab.async false

namespace CycleQ2SparseModularPolynomial

abbrev Layers := List Sparse

def addLayers : Layers → Layers → Layers
  | [], q => q
  | p, [] => p
  | a::p, b::q => add a b :: addLayers p q

def mulLayers (p q : Layers) : Layers :=
  p.foldr (fun a acc => addLayers (q.map (mul a)) ([]::acc)) []

def negLayers (p : Layers) : Layers := p.map neg

def checkLayer (p : Layers) (n : ℕ) : Bool := checkZero (p[n]?.getD [])

section Soundness
variable {R : Type*} [CommRing R] [CharP R 109]

def evalLayers (x : Fin 5 → R) (z : R) : Layers → R
  | [] => 0
  | a::p => eval x a + z * evalLayers x z p

theorem eval_addLayers (x : Fin 5 → R) (z : R) (p q : Layers) :
    evalLayers x z (addLayers p q) = evalLayers x z p + evalLayers x z q := by
  induction p generalizing q with
  | nil => simp [addLayers, evalLayers]
  | cons a p ih =>
    cases q with
    | nil => simp [addLayers, evalLayers]
    | cons b q => simp only [addLayers, evalLayers, eval_add, ih]; ring

theorem eval_scaleLayers (x : Fin 5 → R) (z : R) (a : Sparse) (q : Layers) :
    evalLayers x z (q.map (mul a)) = eval x a * evalLayers x z q := by
  induction q with
  | nil => simp [evalLayers]
  | cons b q ih => simp only [List.map_cons, evalLayers, eval_mul, ih]; ring

theorem eval_mulLayers (x : Fin 5 → R) (z : R) (p q : Layers) :
    evalLayers x z (mulLayers p q) = evalLayers x z p * evalLayers x z q := by
  induction p with
  | nil => simp [mulLayers, evalLayers]
  | cons a p ih =>
    change evalLayers x z (addLayers (q.map (mul a)) ([]::mulLayers p q)) = _
    rw [eval_addLayers, eval_scaleLayers, evalLayers, eval_nil, ih, evalLayers]
    ring

theorem eval_negLayers (x : Fin 5 → R) (z : R) (p : Layers) :
    evalLayers x z (negLayers p) = -evalLayers x z p := by
  induction p with
  | nil => simp [negLayers, evalLayers]
  | cons a p ih =>
    change eval x (neg a) + z * evalLayers x z (negLayers p) = _
    rw [eval_neg, ih, evalLayers]
    ring

/-- Separate checked coefficient blocks imply the whole polynomial identity.
The bound concerns only the list of Horner blocks, never an arithmetic rank. -/
theorem evalLayers_eq_zero_of_checks (x : Fin 5 → R) (z : R) (N : ℕ) (p : Layers)
    (hlen : p.length ≤ N) (h : ∀ n : Fin N, checkLayer p n = true) :
    evalLayers x z p = 0 := by
  induction N generalizing p with
  | zero =>
    have hp : p = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    rw [hp, evalLayers]
  | succ N ih =>
    cases p with
    | nil => rfl
    | cons a p =>
      have ha : checkZero a = true := by
        simpa only [checkLayer, Fin.val_zero, List.getElem?_cons_zero, Option.getD_some] using h 0
      have hp : p.length ≤ N := Nat.succ_le_succ_iff.mp hlen
      have hh : ∀ n : Fin N, checkLayer p n = true := by
        intro n
        simpa only [checkLayer, Fin.val_succ, List.getElem?_cons_succ] using h n.succ
      rw [evalLayers, eval_eq_zero_of_check x a ha, ih p hp hh, mul_zero, add_zero]

end Soundness
end CycleQ2SparseModularPolynomial

#print axioms CycleQ2SparseModularPolynomial.evalLayers_eq_zero_of_checks
#print axioms CycleQ2SparseModularPolynomial.eval_mulLayers
end

/- Component: continuation_3/SparseModularBlocks.lean -/
section
/-! Two independent Horner variables keep concrete kernel reductions small. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option Elab.async false

namespace CycleQ2SparseModularPolynomial

abbrev Blocks := List Layers

def addBlocks : Blocks → Blocks → Blocks
  | [], q => q
  | p, [] => p
  | a::p, b::q => addLayers a b :: addBlocks p q

def mulBlocks (p q : Blocks) : Blocks :=
  p.foldr (fun a acc => addBlocks (q.map (mulLayers a)) ([]::acc)) []

def negBlocks (p : Blocks) : Blocks := p.map negLayers

def checkBlock (p : Blocks) (n m : ℕ) : Bool := checkLayer (p[n]?.getD []) m

section Soundness
variable {R : Type*} [CommRing R] [CharP R 109]

def evalBlocks (x : Fin 5 → R) (z w : R) : Blocks → R
  | [] => 0
  | a::p => evalLayers x w a + z * evalBlocks x z w p

theorem eval_addBlocks (x : Fin 5 → R) (z w : R) (p q : Blocks) :
    evalBlocks x z w (addBlocks p q) = evalBlocks x z w p + evalBlocks x z w q := by
  induction p generalizing q with
  | nil => simp [addBlocks, evalBlocks]
  | cons a p ih =>
    cases q with
    | nil => simp [addBlocks, evalBlocks]
    | cons b q => simp only [addBlocks, evalBlocks, eval_addLayers, ih]; ring

theorem eval_scaleBlocks (x : Fin 5 → R) (z w : R) (a : Layers) (q : Blocks) :
    evalBlocks x z w (q.map (mulLayers a)) = evalLayers x w a * evalBlocks x z w q := by
  induction q with
  | nil => simp [evalBlocks]
  | cons b q ih => simp only [List.map_cons, evalBlocks, eval_mulLayers, ih]; ring

theorem eval_mulBlocks (x : Fin 5 → R) (z w : R) (p q : Blocks) :
    evalBlocks x z w (mulBlocks p q) = evalBlocks x z w p * evalBlocks x z w q := by
  induction p with
  | nil => simp [mulBlocks, evalBlocks]
  | cons a p ih =>
    change evalBlocks x z w (addBlocks (q.map (mulLayers a)) ([]::mulBlocks p q)) = _
    rw [eval_addBlocks, eval_scaleBlocks, evalBlocks, evalLayers, ih, evalBlocks]
    ring

theorem eval_negBlocks (x : Fin 5 → R) (z w : R) (p : Blocks) :
    evalBlocks x z w (negBlocks p) = -evalBlocks x z w p := by
  induction p with
  | nil => simp [negBlocks, evalBlocks]
  | cons a p ih =>
    change evalLayers x w (negLayers a) + z * evalBlocks x z w (negBlocks p) = _
    rw [eval_negLayers, ih, evalBlocks]
    ring

/-- Independently checked scalar blocks imply the complete identity. -/
theorem evalBlocks_eq_zero_of_checks (x : Fin 5 → R) (z w : R) (N M : ℕ) (p : Blocks)
    (hlen : p.length ≤ N)
    (hinner : ∀ n : Fin N, (p[n.val]?.getD []).length ≤ M)
    (h : ∀ n : Fin N, ∀ m : Fin M, checkBlock p n m = true) :
    evalBlocks x z w p = 0 := by
  induction N generalizing p with
  | zero =>
    have hp : p = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    rw [hp, evalBlocks]
  | succ N ih =>
    cases p with
    | nil => rfl
    | cons a p =>
      have hla : a.length ≤ M := by
        simpa only [Fin.val_zero, List.getElem?_cons_zero, Option.getD_some] using hinner 0
      have ha : evalLayers x w a = 0 :=
        evalLayers_eq_zero_of_checks x w M a hla (fun m => by
          simpa only [checkBlock, Fin.val_zero, List.getElem?_cons_zero, Option.getD_some]
            using h 0 m)
      have hp : p.length ≤ N := Nat.succ_le_succ_iff.mp hlen
      have hli : ∀ n : Fin N, (p[n.val]?.getD []).length ≤ M := by
        intro n
        simpa only [Fin.val_succ, List.getElem?_cons_succ] using hinner n.succ
      have hh : ∀ n : Fin N, ∀ m : Fin M, checkBlock p n m = true := by
        intro n m
        simpa only [checkBlock, Fin.val_succ, List.getElem?_cons_succ] using h n.succ m
      rw [evalBlocks, ha, ih p hp hli hh, mul_zero, add_zero]

end Soundness
end CycleQ2SparseModularPolynomial

#print axioms CycleQ2SparseModularPolynomial.evalBlocks_eq_zero_of_checks
#print axioms CycleQ2SparseModularPolynomial.eval_mulBlocks
end
