import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic

/-! # Sparse Gaussian polynomials and their Horner towers -/

set_option Elab.async false

/- Component: continuation_3/SparseGaussianPolynomial.lean -/
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

namespace CycleQ2SparseGaussianPolynomial

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
end CycleQ2SparseGaussianPolynomial

#print axioms CycleQ2SparseGaussianPolynomial.eval_eq_zero_of_check
#print axioms CycleQ2SparseGaussianPolynomial.eval_mul
end

/- Component: continuation_3/SparseGaussianLayers.lean -/
section
/-! Horner blocks for small independent kernel checks of sparse identities. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option Elab.async false

namespace CycleQ2SparseGaussianPolynomial

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
variable {R : Type*} [CommRing R]
variable (φ : GaussianInt →+* R)

def evalLayers (φ : GaussianInt →+* R) (x : Fin 5 → R) (z : R) : Layers → R
  | [] => 0
  | a::p => eval φ x a + z * evalLayers φ x z p

theorem eval_addLayers (x : Fin 5 → R) (z : R) (p q : Layers) :
    evalLayers φ x z (addLayers p q) = evalLayers φ x z p + evalLayers φ x z q := by
  induction p generalizing q with
  | nil => simp [addLayers, evalLayers]
  | cons a p ih =>
    cases q with
    | nil => simp [addLayers, evalLayers]
    | cons b q => simp only [addLayers, evalLayers, eval_add, ih]; ring

theorem eval_scaleLayers (x : Fin 5 → R) (z : R) (a : Sparse) (q : Layers) :
    evalLayers φ x z (q.map (mul a)) = eval φ x a * evalLayers φ x z q := by
  induction q with
  | nil => simp [evalLayers]
  | cons b q ih => simp only [List.map_cons, evalLayers, eval_mul, ih]; ring

theorem eval_mulLayers (x : Fin 5 → R) (z : R) (p q : Layers) :
    evalLayers φ x z (mulLayers p q) = evalLayers φ x z p * evalLayers φ x z q := by
  induction p with
  | nil => simp [mulLayers, evalLayers]
  | cons a p ih =>
    change evalLayers φ x z (addLayers (q.map (mul a)) ([]::mulLayers p q)) = _
    rw [eval_addLayers, eval_scaleLayers, evalLayers, eval_nil, ih, evalLayers]
    ring

theorem eval_negLayers (x : Fin 5 → R) (z : R) (p : Layers) :
    evalLayers φ x z (negLayers p) = -evalLayers φ x z p := by
  induction p with
  | nil => simp [negLayers, evalLayers]
  | cons a p ih =>
    change eval φ x (neg a) + z * evalLayers φ x z (negLayers p) = _
    rw [eval_neg, ih, evalLayers]
    ring

/-- Separate checked coefficient blocks imply the whole polynomial identity.
The bound concerns only the list of Horner blocks, never an arithmetic rank. -/
theorem evalLayers_eq_zero_of_checks (x : Fin 5 → R) (z : R) (N : ℕ) (p : Layers)
    (hlen : p.length ≤ N) (h : ∀ n : Fin N, checkLayer p n = true) :
    evalLayers φ x z p = 0 := by
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
      rw [evalLayers, eval_eq_zero_of_check φ x a ha, ih p hp hh, mul_zero, add_zero]

end Soundness
end CycleQ2SparseGaussianPolynomial

#print axioms CycleQ2SparseGaussianPolynomial.evalLayers_eq_zero_of_checks
#print axioms CycleQ2SparseGaussianPolynomial.eval_mulLayers
end

/- Component: continuation_3/SparseGaussianBlocks.lean -/
section
/-! Two independent Horner variables keep concrete kernel reductions small. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option Elab.async false

namespace CycleQ2SparseGaussianPolynomial

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
variable {R : Type*} [CommRing R]
variable (φ : GaussianInt →+* R)

def evalBlocks (φ : GaussianInt →+* R) (x : Fin 5 → R) (z w : R) : Blocks → R
  | [] => 0
  | a::p => evalLayers φ x w a + z * evalBlocks φ x z w p

theorem eval_addBlocks (x : Fin 5 → R) (z w : R) (p q : Blocks) :
    evalBlocks φ x z w (addBlocks p q) = evalBlocks φ x z w p + evalBlocks φ x z w q := by
  induction p generalizing q with
  | nil => simp [addBlocks, evalBlocks]
  | cons a p ih =>
    cases q with
    | nil => simp [addBlocks, evalBlocks]
    | cons b q => simp only [addBlocks, evalBlocks, eval_addLayers, ih]; ring

theorem eval_scaleBlocks (x : Fin 5 → R) (z w : R) (a : Layers) (q : Blocks) :
    evalBlocks φ x z w (q.map (mulLayers a)) = evalLayers φ x w a * evalBlocks φ x z w q := by
  induction q with
  | nil => simp [evalBlocks]
  | cons b q ih => simp only [List.map_cons, evalBlocks, eval_mulLayers, ih]; ring

theorem eval_mulBlocks (x : Fin 5 → R) (z w : R) (p q : Blocks) :
    evalBlocks φ x z w (mulBlocks p q) = evalBlocks φ x z w p * evalBlocks φ x z w q := by
  induction p with
  | nil => simp [mulBlocks, evalBlocks]
  | cons a p ih =>
    change evalBlocks φ x z w (addBlocks (q.map (mulLayers a)) ([]::mulBlocks p q)) = _
    rw [eval_addBlocks, eval_scaleBlocks, evalBlocks, evalLayers, ih, evalBlocks]
    ring

theorem eval_negBlocks (x : Fin 5 → R) (z w : R) (p : Blocks) :
    evalBlocks φ x z w (negBlocks p) = -evalBlocks φ x z w p := by
  induction p with
  | nil => simp [negBlocks, evalBlocks]
  | cons a p ih =>
    change evalLayers φ x w (negLayers a) + z * evalBlocks φ x z w (negBlocks p) = _
    rw [eval_negLayers, ih, evalBlocks]
    ring

/-- Independently checked scalar blocks imply the complete identity. -/
theorem evalBlocks_eq_zero_of_checks (x : Fin 5 → R) (z w : R) (N M : ℕ) (p : Blocks)
    (hlen : p.length ≤ N)
    (hinner : ∀ n : Fin N, (p[n.val]?.getD []).length ≤ M)
    (h : ∀ n : Fin N, ∀ m : Fin M, checkBlock p n m = true) :
    evalBlocks φ x z w p = 0 := by
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
      have ha : evalLayers φ x w a = 0 :=
        evalLayers_eq_zero_of_checks φ x w M a hla (fun m => by
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
end CycleQ2SparseGaussianPolynomial

#print axioms CycleQ2SparseGaussianPolynomial.evalBlocks_eq_zero_of_checks
#print axioms CycleQ2SparseGaussianPolynomial.eval_mulBlocks
end

/- Component: continuation_3/SparseGaussianTowers.lean -/
section
/-! Three Horner variables for independent exact Gaussian coefficient checks. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option Elab.async false

namespace CycleQ2SparseGaussianPolynomial

abbrev Towers := List Blocks

def addTowers : Towers → Towers → Towers
  | [], q => q
  | p, [] => p
  | a::p, b::q => addBlocks a b :: addTowers p q

def mulTowers (p q : Towers) : Towers :=
  p.foldr (fun a acc => addTowers (q.map (mulBlocks a)) ([]::acc)) []

def negTowers (p : Towers) : Towers := p.map negBlocks

def checkTower (p : Towers) (n m l : ℕ) : Bool :=
  checkBlock (p[n]?.getD []) m l

section Soundness
variable {R : Type*} [CommRing R]
variable (φ : GaussianInt →+* R)

def evalTowers (φ : GaussianInt →+* R) (x : Fin 5 → R)
    (z w v : R) : Towers → R
  | [] => 0
  | a::p => evalBlocks φ x w v a + z * evalTowers φ x z w v p

theorem eval_addTowers (x : Fin 5 → R) (z w v : R) (p q : Towers) :
    evalTowers φ x z w v (addTowers p q) =
      evalTowers φ x z w v p + evalTowers φ x z w v q := by
  induction p generalizing q with
  | nil => simp [addTowers, evalTowers]
  | cons a p ih =>
    cases q with
    | nil => simp [addTowers, evalTowers]
    | cons b q => simp only [addTowers, evalTowers, eval_addBlocks, ih]; ring

theorem eval_scaleTowers (x : Fin 5 → R) (z w v : R) (a : Blocks) (q : Towers) :
    evalTowers φ x z w v (q.map (mulBlocks a)) =
      evalBlocks φ x w v a * evalTowers φ x z w v q := by
  induction q with
  | nil => simp [evalTowers]
  | cons b q ih => simp only [List.map_cons, evalTowers, eval_mulBlocks, ih]; ring

theorem eval_mulTowers (x : Fin 5 → R) (z w v : R) (p q : Towers) :
    evalTowers φ x z w v (mulTowers p q) =
      evalTowers φ x z w v p * evalTowers φ x z w v q := by
  induction p with
  | nil => simp [mulTowers, evalTowers]
  | cons a p ih =>
    change evalTowers φ x z w v
      (addTowers (q.map (mulBlocks a)) ([]::mulTowers p q)) = _
    rw [eval_addTowers, eval_scaleTowers, evalTowers, evalBlocks, ih, evalTowers]
    ring

theorem eval_negTowers (x : Fin 5 → R) (z w v : R) (p : Towers) :
    evalTowers φ x z w v (negTowers p) = -evalTowers φ x z w v p := by
  induction p with
  | nil => simp [negTowers, evalTowers]
  | cons a p ih =>
    change evalBlocks φ x w v (negBlocks a) +
      z * evalTowers φ x z w v (negTowers p) = _
    rw [eval_negBlocks, ih, evalTowers]
    ring

theorem evalTowers_eq_zero_of_checks (x : Fin 5 → R) (z w v : R)
    (N M L : ℕ) (p : Towers)
    (hlen : p.length ≤ N)
    (hinner : ∀ n : Fin N, (p[n.val]?.getD []).length ≤ M)
    (hdeep : ∀ n : Fin N, ∀ m : Fin M,
      ((p[n.val]?.getD [])[m.val]?.getD []).length ≤ L)
    (h : ∀ n : Fin N, ∀ m : Fin M, ∀ l : Fin L, checkTower p n m l = true) :
    evalTowers φ x z w v p = 0 := by
  induction N generalizing p with
  | zero =>
    have hp : p = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    rw [hp, evalTowers]
  | succ N ih =>
    cases p with
    | nil => rfl
    | cons a p =>
      have hla : a.length ≤ M := by
        simpa only [Fin.val_zero, List.getElem?_cons_zero, Option.getD_some] using hinner 0
      have hda : ∀ m : Fin M, (a[m.val]?.getD []).length ≤ L := by
        intro m
        simpa only [Fin.val_zero, List.getElem?_cons_zero, Option.getD_some] using hdeep 0 m
      have ha : evalBlocks φ x w v a = 0 :=
        evalBlocks_eq_zero_of_checks φ x w v M L a hla hda (fun m l => by
          simpa only [checkTower, Fin.val_zero, List.getElem?_cons_zero, Option.getD_some]
            using h 0 m l)
      have hp : p.length ≤ N := Nat.succ_le_succ_iff.mp hlen
      have hli : ∀ n : Fin N, (p[n.val]?.getD []).length ≤ M := by
        intro n
        simpa only [Fin.val_succ, List.getElem?_cons_succ] using hinner n.succ
      have hld : ∀ n : Fin N, ∀ m : Fin M,
          ((p[n.val]?.getD [])[m.val]?.getD []).length ≤ L := by
        intro n m
        simpa only [Fin.val_succ, List.getElem?_cons_succ] using hdeep n.succ m
      have hh : ∀ n : Fin N, ∀ m : Fin M, ∀ l : Fin L,
          checkTower p n m l = true := by
        intro n m l
        simpa only [checkTower, Fin.val_succ, List.getElem?_cons_succ] using h n.succ m l
      rw [evalTowers, ha, ih p hp hli hld hh, mul_zero, add_zero]

end Soundness
end CycleQ2SparseGaussianPolynomial

#print axioms CycleQ2SparseGaussianPolynomial.evalTowers_eq_zero_of_checks
#print axioms CycleQ2SparseGaussianPolynomial.eval_mulTowers
end

/- Component: continuation_3/SparseGaussianNaturality.lean -/
section
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace CycleQ2SparseGaussianPolynomial
variable {R S : Type*} [CommRing R] [CommRing S]
variable (φ : GaussianInt →+* R) (ψ : R →+* S)

theorem map_eval (x : Fin 5 → R) (p : Sparse) :
    ψ (eval φ x p) = eval (ψ.comp φ) (fun j => ψ (x j)) p := by
  induction p with
  | nil => simp
  | cons a p ih =>
    simp only [eval_cons, map_add, ih, termValue, monomial,
      map_mul, map_pow, RingHom.comp_apply]

theorem map_evalLayers (x : Fin 5 → R) (z : R) (p : Layers) :
    ψ (evalLayers φ x z p) =
      evalLayers (ψ.comp φ) (fun j => ψ (x j)) (ψ z) p := by
  induction p with
  | nil => simp [evalLayers]
  | cons a p ih => simp only [evalLayers, map_add, map_mul, map_eval, ih]

theorem map_evalBlocks (x : Fin 5 → R) (z w : R) (p : Blocks) :
    ψ (evalBlocks φ x z w p) =
      evalBlocks (ψ.comp φ) (fun j => ψ (x j)) (ψ z) (ψ w) p := by
  induction p with
  | nil => simp [evalBlocks]
  | cons a p ih => simp only [evalBlocks, map_add, map_mul, map_evalLayers, ih]

theorem map_evalTowers (x : Fin 5 → R) (z w v : R) (p : Towers) :
    ψ (evalTowers φ x z w v p) =
      evalTowers (ψ.comp φ) (fun j => ψ (x j)) (ψ z) (ψ w) (ψ v) p := by
  induction p with
  | nil => simp [evalTowers]
  | cons a p ih => simp only [evalTowers, map_add, map_mul, map_evalBlocks, ih]

end CycleQ2SparseGaussianPolynomial

#print axioms CycleQ2SparseGaussianPolynomial.map_evalTowers
end

/- Component: continuation_3/SparseGaussianNormalForm.lean -/
section
/-! A sparse reducer for the actual two monic seed equations.

The semantic statement holds for every fuel bound, because exhaustion retains
the unreduced monomial. Concrete zero checks therefore do not need to trust a
termination estimate, an externally supplied quotient, or a normal-form oracle.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false

namespace CycleQ2SparseGaussianPolynomial

def oneLayers : Layers := [[((0,0,0,0,0),1)]]

def monomialTower (c : Layers) (a b : ℕ) : Towers :=
  List.replicate b [] ++ [List.replicate a [] ++ [c]]

def scaleTower (c : Layers) (p : Towers) : Towers :=
  p.map (fun q => q.map (mulLayers c))

/-- The intended relations are z³=a₀+a₁*z and w³=b₀−z⁶. -/
def normalCore (a₀ a₁ b₀ : Layers) : ℕ → ℕ → ℕ → Towers
  | 0, a, b => monomialTower oneLayers a b
  | n+1, a, b =>
      if 3 ≤ b then
        addTowers (scaleTower b₀ (normalCore a₀ a₁ b₀ n a (b-3)))
          (negTowers (normalCore a₀ a₁ b₀ n (a+6) (b-3)))
      else if 3 ≤ a then
        addTowers (scaleTower a₀ (normalCore a₀ a₁ b₀ n (a-3) b))
          (scaleTower a₁ (normalCore a₀ a₁ b₀ n (a-2) b))
      else monomialTower oneLayers a b

def normalizeBlock (a₀ a₁ b₀ : Layers) (fuel b : ℕ) : ℕ → Blocks → Towers
  | _, [] => []
  | a, c::p =>
      addTowers (scaleTower c (normalCore a₀ a₁ b₀ fuel a b))
        (normalizeBlock a₀ a₁ b₀ fuel b (a+1) p)

def normalizeTowerFrom (a₀ a₁ b₀ : Layers) (fuel : ℕ) : ℕ → Towers → Towers
  | _, [] => []
  | b, q::p => addTowers (normalizeBlock a₀ a₁ b₀ fuel b 0 q)
      (normalizeTowerFrom a₀ a₁ b₀ fuel (b+1) p)

def normalizeTower (a₀ a₁ b₀ : Layers) (fuel : ℕ) (p : Towers) : Towers :=
  normalizeTowerFrom a₀ a₁ b₀ fuel 0 p

section Soundness
variable {R : Type*} [CommRing R]
variable (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)

theorem eval_oneLayers : evalLayers φ x v oneLayers = 1 := by
  simp [oneLayers, evalLayers, eval, termValue, monomial]

theorem evalBlocks_shift (n : ℕ) (p : Blocks) :
    evalBlocks φ x z v (List.replicate n [] ++ p) = z^n * evalBlocks φ x z v p := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, evalBlocks, evalLayers, ih, pow_succ]
    ring

theorem evalTowers_shift (n : ℕ) (p : Towers) :
    evalTowers φ x w z v (List.replicate n [] ++ p) =
      w^n * evalTowers φ x w z v p := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, evalTowers, evalBlocks, ih, pow_succ]
    ring

theorem eval_monomialTower (c : Layers) (a b : ℕ) :
    evalTowers φ x w z v (monomialTower c a b) =
      z^a * w^b * evalLayers φ x v c := by
  simp only [monomialTower, evalTowers_shift, evalTowers, evalBlocks_shift,
    evalBlocks, mul_zero, add_zero]
  ring

theorem eval_scaleTower (c : Layers) (p : Towers) :
    evalTowers φ x w z v (scaleTower c p) =
      evalLayers φ x v c * evalTowers φ x w z v p := by
  induction p with
  | nil => simp [scaleTower, evalTowers]
  | cons q p ih =>
    simp only [scaleTower, List.map_cons, evalTowers, eval_scaleBlocks] at ⊢ ih
    rw [ih]
    ring

variable (a₀ a₁ b₀ : Layers)
variable (hz : z^3 = evalLayers φ x v a₀ + evalLayers φ x v a₁ * z)
variable (hw : w^3 = evalLayers φ x v b₀ - z^6)

include hz hw

theorem eval_normalCore (n a b : ℕ) :
    evalTowers φ x w z v (normalCore a₀ a₁ b₀ n a b) = z^a * w^b := by
  induction n generalizing a b with
  | zero => rw [normalCore, eval_monomialTower, eval_oneLayers, mul_one]
  | succ n ih =>
    by_cases hb : 3 ≤ b
    · simp only [normalCore, if_pos hb, eval_addTowers, eval_scaleTower, eval_negTowers, ih]
      calc
        evalLayers φ x v b₀ * (z^a * w^(b-3)) + -(z^(a+6) * w^(b-3)) =
            z^a * w^(b-3) * (evalLayers φ x v b₀-z^6) := by rw [pow_add]; ring
        _ = z^a * w^(b-3) * w^3 := by rw [hw]
        _ = z^a * w^b := by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hb]
    · by_cases ha : 3 ≤ a
      · simp only [normalCore, if_neg hb, if_pos ha, eval_addTowers, eval_scaleTower, ih]
        have haa : a-2 = a-3+1 := by omega
        calc
          evalLayers φ x v a₀ * (z^(a-3)*w^b) +
              evalLayers φ x v a₁ * (z^(a-2)*w^b) =
              z^(a-3) * w^b * (evalLayers φ x v a₀ + evalLayers φ x v a₁*z) := by
                rw [haa, pow_succ]
                ring
          _ = z^(a-3) * w^b * z^3 := by rw [hz]
          _ = z^a * w^b := by
            rw [mul_right_comm, ← pow_add, Nat.sub_add_cancel ha]
      · rw [normalCore, if_neg hb, if_neg ha, eval_monomialTower, eval_oneLayers, mul_one]

theorem eval_normalizeBlock (fuel b a : ℕ) (p : Blocks) :
    evalTowers φ x w z v (normalizeBlock a₀ a₁ b₀ fuel b a p) =
      z^a * w^b * evalBlocks φ x z v p := by
  induction p generalizing a with
  | nil => simp [normalizeBlock, evalTowers, evalBlocks]
  | cons c p ih =>
    simp only [normalizeBlock, eval_addTowers, eval_scaleTower,
      eval_normalCore φ x w z v a₀ a₁ b₀ hz hw, ih, evalBlocks, pow_succ]
    ring

theorem eval_normalizeTowerFrom (fuel b : ℕ) (p : Towers) :
    evalTowers φ x w z v (normalizeTowerFrom a₀ a₁ b₀ fuel b p) =
      w^b * evalTowers φ x w z v p := by
  induction p generalizing b with
  | nil => simp [normalizeTowerFrom, evalTowers]
  | cons q p ih =>
    simp only [normalizeTowerFrom, eval_addTowers,
      eval_normalizeBlock φ x w z v a₀ a₁ b₀ hz hw, ih, evalTowers, pow_zero, pow_succ]
    ring

/-- Exact semantic preservation under the two actual monic seed relations. -/
theorem eval_normalizeTower (fuel : ℕ) (p : Towers) :
    evalTowers φ x w z v (normalizeTower a₀ a₁ b₀ fuel p) =
      evalTowers φ x w z v p := by
  simpa only [normalizeTower, pow_zero, one_mul] using
    eval_normalizeTowerFrom φ x w z v a₀ a₁ b₀ hz hw fuel 0 p

end Soundness
end CycleQ2SparseGaussianPolynomial

#print axioms CycleQ2SparseGaussianPolynomial.eval_normalizeTower
end

/- Component: continuation_3/SparseGaussianAction.lean -/
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false

namespace CycleQ2SparseGaussianPolynomial

def applyBlock (action : ℕ → ℕ → Towers) (b : ℕ) : ℕ → Blocks → Towers
  | _, [] => []
  | a, c::p => addTowers (scaleTower c (action a b)) (applyBlock action b (a+1) p)

def applyTowersFrom (action : ℕ → ℕ → Towers) : ℕ → Towers → Towers
  | _, [] => []
  | b, q::p => addTowers (applyBlock action b 0 q) (applyTowersFrom action (b+1) p)

def applyTowers (action : ℕ → ℕ → Towers) (p : Towers) : Towers :=
  applyTowersFrom action 0 p

def checkLayers (p : Layers) : Bool := p.all checkZero
def checkBlocks (p : Blocks) : Bool := p.all checkLayers
def checkTowers (p : Towers) : Bool := p.all checkBlocks
def checkTowerBlock (p : Towers) (b a : ℕ) : Bool :=
  checkLayers ((p[b]?.getD [])[a]?.getD [])

section Soundness
variable {R : Type*} [CommRing R]
variable (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)

theorem evalLayers_eq_zero_of_checkLayers (p : Layers) (h : checkLayers p = true) :
    evalLayers φ x v p = 0 := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    simp only [checkLayers, List.all_cons, Bool.and_eq_true] at h
    rw [evalLayers, eval_eq_zero_of_check φ x c h.1, ih h.2, mul_zero, add_zero]

theorem evalBlocks_eq_zero_of_checkBlocks (p : Blocks) (h : checkBlocks p = true) :
    evalBlocks φ x z v p = 0 := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    simp only [checkBlocks, List.all_cons, Bool.and_eq_true] at h
    rw [evalBlocks, evalLayers_eq_zero_of_checkLayers φ x v c h.1,
      ih h.2, mul_zero, add_zero]

theorem evalTowers_eq_zero_of_checkTowers (p : Towers) (h : checkTowers p = true) :
    evalTowers φ x w z v p = 0 := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    simp only [checkTowers, List.all_cons, Bool.and_eq_true] at h
    rw [evalTowers, evalBlocks_eq_zero_of_checkBlocks φ x z v c h.1,
      ih h.2, mul_zero, add_zero]

theorem evalBlocks_eq_zero_of_layer_checks (N : ℕ) (p : Blocks)
    (hlen : p.length ≤ N)
    (h : ∀ n : Fin N, checkLayers (p[n.val]?.getD []) = true) :
    evalBlocks φ x z v p = 0 := by
  induction N generalizing p with
  | zero =>
    have hp : p = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    rw [hp, evalBlocks]
  | succ N ih =>
    cases p with
    | nil => rfl
    | cons a p =>
      have ha : checkLayers a = true := by
        simpa only [Fin.val_zero, List.getElem?_cons_zero, Option.getD_some] using h 0
      have hp : p.length ≤ N := Nat.succ_le_succ_iff.mp hlen
      have hh : ∀ n : Fin N, checkLayers (p[n.val]?.getD []) = true := by
        intro n
        simpa only [Fin.val_succ, List.getElem?_cons_succ] using h n.succ
      rw [evalBlocks, evalLayers_eq_zero_of_checkLayers φ x v a ha,
        ih p hp hh, mul_zero, add_zero]

theorem evalTowers_eq_zero_of_block_checks (N M : ℕ) (p : Towers)
    (hlen : p.length ≤ N)
    (hinner : ∀ n : Fin N, (p[n.val]?.getD []).length ≤ M)
    (h : ∀ n : Fin N, ∀ m : Fin M, checkTowerBlock p n m = true) :
    evalTowers φ x w z v p = 0 := by
  induction N generalizing p with
  | zero =>
    have hp : p = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    rw [hp, evalTowers]
  | succ N ih =>
    cases p with
    | nil => rfl
    | cons a p =>
      have hla : a.length ≤ M := by
        simpa only [Fin.val_zero, List.getElem?_cons_zero, Option.getD_some] using hinner 0
      have ha : evalBlocks φ x z v a = 0 :=
        evalBlocks_eq_zero_of_layer_checks φ x z v M a hla (fun m => by
          simpa only [checkTowerBlock, Fin.val_zero, List.getElem?_cons_zero,
            Option.getD_some] using h 0 m)
      have hp : p.length ≤ N := Nat.succ_le_succ_iff.mp hlen
      have hli : ∀ n : Fin N, (p[n.val]?.getD []).length ≤ M := by
        intro n
        simpa only [Fin.val_succ, List.getElem?_cons_succ] using hinner n.succ
      have hh : ∀ n : Fin N, ∀ m : Fin M, checkTowerBlock p n m = true := by
        intro n m
        simpa only [checkTowerBlock, Fin.val_succ, List.getElem?_cons_succ] using h n.succ m
      rw [evalTowers, ha, ih p hp hli hh, mul_zero, add_zero]

variable (action : ℕ → ℕ → Towers) (c : R)
variable (haction : ∀ a b, evalTowers φ x w z v (action a b) = c * z^a * w^b)
include haction

theorem eval_applyBlock (b a : ℕ) (p : Blocks) :
    evalTowers φ x w z v (applyBlock action b a p) =
      c * z^a * w^b * evalBlocks φ x z v p := by
  induction p generalizing a with
  | nil => simp [applyBlock, evalTowers, evalBlocks]
  | cons q p ih =>
    simp only [applyBlock, eval_addTowers, eval_scaleTower, haction, ih,
      evalBlocks, pow_succ]
    ring

theorem eval_applyTowersFrom (b : ℕ) (p : Towers) :
    evalTowers φ x w z v (applyTowersFrom action b p) =
      c * w^b * evalTowers φ x w z v p := by
  induction p generalizing b with
  | nil => simp [applyTowersFrom, evalTowers]
  | cons q p ih =>
    simp only [applyTowersFrom, eval_addTowers,
      eval_applyBlock φ x w z v action c haction, ih, evalTowers, pow_zero, pow_succ]
    ring

theorem eval_applyTowers (p : Towers) :
    evalTowers φ x w z v (applyTowers action p) = c * evalTowers φ x w z v p := by
  simpa only [applyTowers, pow_zero, mul_one] using
    eval_applyTowersFrom φ x w z v action c haction 0 p

end Soundness
end CycleQ2SparseGaussianPolynomial

#print axioms CycleQ2SparseGaussianPolynomial.eval_applyTowers
#print axioms CycleQ2SparseGaussianPolynomial.evalTowers_eq_zero_of_block_checks
end
