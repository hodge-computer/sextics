import Proposal.Workspace
import HodgeTarget
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.MvPolynomial.Equiv
import HodgeComputer.Constructions.HoldoutCover.HypersurfaceDomain
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import HodgeComputer.CertificateOperations
import HodgeComputer.Verify
import HodgeComputer.Constructions.RationalFields.Calculus
import HodgeComputer.Constructions.FiniteAlgebra.FractionDerivation
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Tactic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Topology.Irreducible
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.LinearAlgebra.Isomorphisms
import Proposal.GeometricSeed
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import HodgeComputer.Constructions.HigherResidues.HigherResidue
import HodgeComputer.Constructions.HoldoutCover.ResidueDerivatives
import HodgeComputer.Constructions.RationalFields.Homogenization
import HodgeComputer.Constructions.RationalFields.CommonDenominatorSubstitution
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Set.Countable
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.HahnSeries.PowerSeries
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.FreeModule.Basic
import HodgeComputer.Constructions.PolynomialCurves.ArithmeticLifting
import HodgeComputer.Constructions.HoldoutCover.GenericIncidence
import Mathlib.RingTheory.Smooth.AdicCompletion
import HodgeComputer.Constructions.HoldoutCover.FiniteTrace
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.Fintype.Card
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.Data.Finsupp.MonomialOrder.DegLex
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.FunProp
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.CharP.Basic
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Data.Finsupp.Encodable
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Tactic.Abel
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Data.List.OfFn
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Data.Fintype.Fin
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.Module
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.Localization.AtPrime.Basic
import HodgeComputer.Constructions.HoldoutCover.FiniteDifferentials
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Proposal.GeometricFormalInputs
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Proposal.GeometricTarget01Part03

/-! Source partition of GeometricTarget.lean. See solution.md for verification status. -/

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


/- Component: continuation_3/UnitFiberRegular.lean -/
section
/-!
# A unit in one fiber detects a nonzerodivisor in a finite free algebra

The base is an integral domain. No domain hypothesis is imposed on the
finite free algebra. The proof uses the determinant of multiplication and
its checked compatibility with scalar extension.
-/

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2UnitFiberRegular

open scoped TensorProduct

variable {R A S : Type*} [CommRing R] [IsDomain R]
  [CommRing A] [Nontrivial A] [Algebra R A]
  [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S]

theorem multiplication_baseChange (p : S) :
    (Algebra.lmul R S p).baseChange A =
      Algebra.lmul A (A ⊗[R] S) (Algebra.TensorProduct.includeRight p) := by
  ext a s
  simp [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul]

/-- A single fiber on which p is a unit proves that multiplication by p
is injective on the original finite free algebra. -/
theorem injective_mul_of_unit_fiber (p : S)
    (hp : IsUnit (Algebra.TensorProduct.includeRight p : A ⊗[R] S)) :
    Function.Injective (fun x : S => p*x) := by
  have hu : IsUnit ((Algebra.lmul R S p).baseChange A) := by
    rw [multiplication_baseChange]
    exact Algebra.lmul_isUnit_iff.mpr hp
  have hd := LinearMap.isUnit_det _ hu
  rw [LinearMap.det_baseChange] at hd
  have hn : (Algebra.lmul R S p).det ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hd
    exact not_isUnit_zero hd
  have hk : LinearMap.ker (Algebra.lmul R S p) = ⊥ := by
    by_contra h
    exact hn (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h)
  exact LinearMap.ker_eq_bot.mp hk

end CycleQ2UnitFiberRegular

#print axioms CycleQ2UnitFiberRegular.multiplication_baseChange
#print axioms CycleQ2UnitFiberRegular.injective_mul_of_unit_fiber
end
end


/- Component: continuation_3/VeryGeneralPencil.lean -/
section
/-!
# Faithful generic coefficient pencils through a prescribed complex point

A countable coefficient ring embedded in the complex numbers admits a
faithful generic coefficient pencil through any specified complex point.
The embedding is over that countable ring. It is not asserted to be an
embedding of a multivariable complex polynomial ring into C(t).

The endpoint is selected by the proved countable polynomial avoidance
theorem, and evaluation at t=1 proves faithfulness of the whole pencil.
This is the actual coefficient-ring embedding needed before specializing
a generic algebraic construction along a pencil through a fixed target.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2VeryGeneralPencil

open MvPolynomial

variable {R : Type*} [CommRing R] [Countable R]

theorem exists_faithful_endpoint (f : R →+* ℂ) (hf : Function.Injective f) (n : ℕ) :
    ∃ b : Fin n → ℂ, Function.Injective (eval₂Hom f b) := by
  classical
  letI : Uncountable ℂ := Set.not_countable_univ_iff.mp not_countable_complex
  letI : Countable (MvPolynomial (Fin n) R) :=
    Countable.of_equiv _ AddMonoidAlgebra.coeffEquiv.symm
  let Family := {p : MvPolynomial (Fin n) R // p ≠ 0}
  have hm : Function.Injective (MvPolynomial.map f : MvPolynomial (Fin n) R → _) :=
    MvPolynomial.map_injective f hf
  obtain ⟨b, hb⟩ := CycleQ2VeryGeneral.exists_avoiding_polynomials n
    (fun p : Family => MvPolynomial.map f p.val)
    (fun p => by intro h; exact p.property (hm (by simpa using h)))
  refine ⟨b, ?_⟩
  intro p q hpq
  by_contra hne
  have h := hb ⟨p-q, sub_ne_zero.mpr hne⟩
  apply h
  change eval₂ f b p = eval₂ f b q at hpq
  simpa only [eval_map, map_sub, sub_eq_zero] using hpq

def pencilCoefficient {n : ℕ} (a b : Fin n → ℂ) (j : Fin n) : Polynomial ℂ :=
  Polynomial.C (a j) + Polynomial.X * Polynomial.C (b j-a j)

def pencilMap {n : ℕ} (f : R →+* ℂ) (a b : Fin n → ℂ) :
    MvPolynomial (Fin n) R →+* Polynomial ℂ :=
  eval₂Hom (Polynomial.C.comp f) (pencilCoefficient a b)

theorem pencil_eval_zero {n : ℕ} (f : R →+* ℂ) (a b : Fin n → ℂ) :
    (Polynomial.evalRingHom 0).comp (pencilMap f a b) = eval₂Hom f a := by
  ext r j <;> simp [pencilMap, pencilCoefficient]

theorem pencil_eval_one {n : ℕ} (f : R →+* ℂ) (a b : Fin n → ℂ) :
    (Polynomial.evalRingHom 1).comp (pencilMap f a b) = eval₂Hom f b := by
  ext r j <;> simp [pencilMap, pencilCoefficient]

theorem pencilMap_injective {n : ℕ} (f : R →+* ℂ) (a b : Fin n → ℂ)
    (hb : Function.Injective (eval₂Hom f b)) : Function.Injective (pencilMap f a b) := by
  intro p q hpq
  apply hb
  have h := congrArg (Polynomial.evalRingHom 1) hpq
  change ((Polynomial.evalRingHom 1).comp (pencilMap f a b)) p =
    ((Polynomial.evalRingHom 1).comp (pencilMap f a b)) q at h
  rwa [pencil_eval_one] at h

/-- The polynomial pencil passes through the specified point at t=0, while
its generic coefficient map is faithful over the countable coefficient ring. -/
theorem exists_faithful_pencil (f : R →+* ℂ) (hf : Function.Injective f)
    (n : ℕ) (a : Fin n → ℂ) :
    ∃ b : Fin n → ℂ,
      Function.Injective (pencilMap f a b) ∧
      (Polynomial.evalRingHom 0).comp (pencilMap f a b) = eval₂Hom f a := by
  obtain ⟨b, hb⟩ := exists_faithful_endpoint f hf n
  exact ⟨b, pencilMap_injective f a b hb, pencil_eval_zero f a b⟩

def rationalPencilMap {n : ℕ} (f : R →+* ℂ) (a b : Fin n → ℂ) :
    MvPolynomial (Fin n) R →+* RatFunc ℂ :=
  (algebraMap (Polynomial ℂ) (RatFunc ℂ)).comp (pencilMap f a b)

theorem rationalPencilMap_injective {n : ℕ} (f : R →+* ℂ) (a b : Fin n → ℂ)
    (hb : Function.Injective (pencilMap f a b)) :
    Function.Injective (rationalPencilMap f a b) :=
  (RatFunc.algebraMap_injective ℂ).comp hb

variable [IsDomain R]

def fractionPencilMap {n : ℕ} (f : R →+* ℂ) (a b : Fin n → ℂ)
    (hb : Function.Injective (pencilMap f a b)) :
    FractionRing (MvPolynomial (Fin n) R) →+* RatFunc ℂ :=
  IsFractionRing.lift (rationalPencilMap_injective f a b hb)

theorem fractionPencilMap_apply {n : ℕ} (f : R →+* ℂ) (a b : Fin n → ℂ)
    (hb : Function.Injective (pencilMap f a b)) (p : MvPolynomial (Fin n) R) :
    fractionPencilMap f a b hb
      (algebraMap (MvPolynomial (Fin n) R) (FractionRing (MvPolynomial (Fin n) R)) p) =
      rationalPencilMap f a b p := by
  exact IsFractionRing.lift_algebraMap _ _

theorem fractionPencilMap_injective {n : ℕ} (f : R →+* ℂ) (a b : Fin n → ℂ)
    (hb : Function.Injective (pencilMap f a b)) :
    Function.Injective (fractionPencilMap f a b hb) :=
  (fractionPencilMap f a b hb).injective

end CycleQ2VeryGeneralPencil

#print axioms CycleQ2VeryGeneralPencil.exists_faithful_pencil
#print axioms CycleQ2VeryGeneralPencil.fractionPencilMap_apply
#print axioms CycleQ2VeryGeneralPencil.fractionPencilMap_injective
end
end


/- Component: continuation_3/WeightedComponentProduct.lean -/
section
/-! # Homogeneous projection for the actual degree-and-character grading -/

namespace CycleQ2WeightedComponent

open MvPolynomial

variable {σ R M : Type*} [CommSemiring R] [AddCancelCommMonoid M]

theorem component_mul (w : σ → M) (p q : MvPolynomial σ R)
    (d e : M) (hq : q.IsWeightedHomogeneous w e) :
    weightedHomogeneousComponent w (d+e) (p*q) =
      weightedHomogeneousComponent w d p*q := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial a c =>
    have hm : (monomial a c : MvPolynomial σ R).IsWeightedHomogeneous w (Finsupp.weight w a) :=
      isWeightedHomogeneous_monomial w a c rfl
    rw [weightedHomogeneousComponent_of_mem (hm.mul hq),
      weightedHomogeneousComponent_of_mem hm]
    simp only [add_left_inj]
    split_ifs <;> simp_all
  | add p s hp hs =>
    simp only [add_mul, map_add, hp, hs]

theorem component_mul_left (w : σ → M) (p q : MvPolynomial σ R)
    (d e : M) (hp : p.IsWeightedHomogeneous w d) :
    weightedHomogeneousComponent w (d+e) (p*q) =
      p*weightedHomogeneousComponent w e q := by
  rw [mul_comm p q, add_comm d e, component_mul w q p e d hp, mul_comm]

end CycleQ2WeightedComponent

#print axioms CycleQ2WeightedComponent.component_mul
#print axioms CycleQ2WeightedComponent.component_mul_left
end


/- Component: continuation_3/cylinder_bridge/CechLinearAlgebra.lean -/
section
/-! Generic linear maps for the three-term Čech differential and surjective descent. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CechLinearAlgebra

variable {R A B C T : Type*} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C] [AddCommGroup T] [Module R T]

def signedThree (f : A →ₗ[R] T) (g : B →ₗ[R] T) (h : C →ₗ[R] T) :
    A × B × C →ₗ[R] T where
  toFun x := f x.1-g x.2.1+h x.2.2
  map_add' x y := by
    change f (x.1+y.1)-g (x.2.1+y.2.1)+h (x.2.2+y.2.2)=_
    rw [map_add,map_add,map_add]
    abel
  map_smul' c x := by
    change f (c • x.1)-g (c • x.2.1)+h (c • x.2.2)=
      c • (f x.1-g x.2.1+h x.2.2)
    rw [map_smul,map_smul,map_smul,smul_add,smul_sub]

def descendSurjective (f : A →ₗ[R] B) (g : A →ₗ[R] T)
    (h : LinearMap.ker f≤LinearMap.ker g) (hf : Function.Surjective f) : B →ₗ[R] T :=
  (CycleQ2LinearRangeDescent.descendRange f g h).comp
    ((LinearMap.id : B →ₗ[R] B).codRestrict (LinearMap.range f) hf)

theorem descendSurjective_apply (f : A →ₗ[R] B) (g : A →ₗ[R] T)
    (h : LinearMap.ker f≤LinearMap.ker g) (hf : Function.Surjective f) (x : A) :
    descendSurjective f g h hf (f x)=g x :=
  CycleQ2LinearRangeDescent.descendRange_apply_image f g h x

end CycleQ2CechLinearAlgebra
end
end


/- Component: continuation_3/cylinder_bridge/CompatibleEquationCoordinates.lean -/
section
/-! Compatible equation coordinates turn an exact linear splitting into
the literal complementary polynomial relation block required by generic
lifting.  This file proves the reconstruction and transformed identities;
it does not assume an independent minor or a generic solution. -/

noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CompatibleEquationCoordinates
open Matrix MvPolynomial CycleQ2PolynomialAffineSlice

variable {R S m l ι κ σ : Type*} [CommRing R] [CommRing S]
  [Fintype m] [Fintype l] [Fintype ι] [Fintype κ]
  [DecidableEq m]

theorem reconstruction (P : Matrix ι m R) (Q : Matrix m ι R)
    (V : Matrix m κ R) (W : Matrix κ m R) (h : Q*P+V*W=1)
    (e : m → R) : Q *ᵥ (P *ᵥ e) + V *ᵥ (W *ᵥ e) = e := by
  rw [mulVec_mulVec,mulVec_mulVec,← add_mulVec,h,one_mulVec]

theorem equations_zero_iff (P : Matrix ι m R) (Q : Matrix m ι R)
    (V : Matrix m κ R) (W : Matrix κ m R) (h : Q*P+V*W=1)
    (e : m → R) : P*ᵥe=0 ∧ W*ᵥe=0 ↔ e=0 := by
  constructor
  · rintro ⟨hP,hW⟩
    have hr := reconstruction P Q V W h e
    rw [hP,hW,mulVec_zero,mulVec_zero,add_zero] at hr
    exact hr.symm
  · rintro rfl
    exact ⟨mulVec_zero _,mulVec_zero _⟩

theorem transformed_relations (P : Matrix ι m R) (Q : Matrix m ι R)
    (V : Matrix m κ R) (W : Matrix κ m R) (T : Matrix κ l R)
    (D : Matrix l m R) (h : Q*P+V*W=1) (e : m → R) (he : D*ᵥe=0) :
    (T*D*V) *ᵥ (W*ᵥe) + (T*D*Q) *ᵥ (P*ᵥe) = 0 := by
  calc
    _ = (T*D) *ᵥ (V*ᵥ(W*ᵥe) + Q*ᵥ(P*ᵥe)) := by
      simp only [mulVec_add,mulVec_mulVec,Matrix.mul_assoc]
    _ = (T*D) *ᵥ e := by rw [add_comm,reconstruction P Q V W h]
    _ = 0 := by rw [← mulVec_mulVec,he,mulVec_zero]

theorem mapped_decomposition (φ : R →+* S)
    (P : Matrix ι m R) (Q : Matrix m ι R) (V : Matrix m κ R) (W : Matrix κ m R)
    (h : Q*P+V*W=1) : Q.map φ * P.map φ + V.map φ * W.map φ = 1 := by
  have hm := congrArg (fun M : Matrix m m R => M.map φ) h
  simpa only [Matrix.map_add φ (map_add φ),Matrix.map_mul,
    Matrix.map_one φ (map_zero φ) (map_one φ)] using hm

def retained (P : Matrix ι m R) (e : m → MvPolynomial σ R) :
    ι → MvPolynomial σ R := P.map C *ᵥ e

def complementary (T : Matrix κ l R) (D : Matrix l m (MvPolynomial σ R))
    (V : Matrix m κ R) : Matrix κ κ (MvPolynomial σ R) := T.map C * D * V.map C

def crossBlock (T : Matrix κ l R) (D : Matrix l m (MvPolynomial σ R))
    (Q : Matrix m ι R) : Matrix κ ι (MvPolynomial σ R) := T.map C * D * Q.map C

theorem polynomial_relations
    (P : Matrix ι m R) (Q : Matrix m ι R) (V : Matrix m κ R) (W : Matrix κ m R)
    (T : Matrix κ l R) (D : Matrix l m (MvPolynomial σ R))
    (h : Q*P+V*W=1) (e : m → MvPolynomial σ R) (he : D*ᵥe=0) :
    complementary T D V *ᵥ retained W e + crossBlock T D Q *ᵥ retained P e = 0 :=
  transformed_relations (P.map C) (Q.map C) (V.map C) (W.map C) (T.map C) D
    (mapped_decomposition C P Q V W h) e he

theorem eval_retained (φ : R →+* S) (x : σ → S)
    (P : Matrix ι m R) (e : m → MvPolynomial σ R) :
    (fun q => eval₂Hom φ x (retained P e q)) =
      P.map φ *ᵥ (fun q => eval₂Hom φ x (e q)) := by
  funext q
  simp only [retained,Matrix.mulVec,Matrix.map_apply,dotProduct,map_sum,map_mul,eval₂Hom_C]

theorem eval_complementary (φ : R →+* S) (x : σ → S)
    (T : Matrix κ l R) (D : Matrix l m (MvPolynomial σ R)) (V : Matrix m κ R) :
    (complementary T D V).map (eval₂Hom φ x) =
      T.map φ * D.map (eval₂Hom φ x) * V.map φ := by
  simp only [complementary,Matrix.map_mul,Matrix.map_map,Function.comp_def,eval₂Hom_C]

theorem jacobian_retained [Fintype σ] (φ : R →+* S) (x : σ → S)
    (P : Matrix ι m R) (e : m → MvPolynomial σ R) :
    jacobian φ x (retained P e) = P.map φ * jacobian φ x e := by
  funext q j
  simp only [jacobian,retained,Matrix.mulVec,dotProduct,Matrix.map_apply,Matrix.mul_apply,
    map_sum,pderiv_C_mul,map_mul,eval₂Hom_C]

theorem sliced_jacobian [Fintype σ] (φ : R →+* S) (a : σ → R)
    (B : Matrix σ ι R) (P : Matrix ι m R) (e : m → MvPolynomial σ R) :
    jacobian φ (0 : ι → S) (fun q => substitute a B (retained P e q)) =
      P.map φ * jacobian φ (φ ∘ a) e * B.map φ := by
  rw [jacobian_zero_substitute,jacobian_retained]

end CycleQ2CompatibleEquationCoordinates

#print axioms CycleQ2CompatibleEquationCoordinates.polynomial_relations
#print axioms CycleQ2CompatibleEquationCoordinates.sliced_jacobian
end
end


/- Component: continuation_3/GenericFiniteSpecialization.lean -/
section
/-!
# Finite algebraic descent followed by actual specialization

A primitive may be constructed over any finite extension of the actual
generic hypersurface field.  Canonical extension of the derivations and
normalized trace descend it before the proved Laurent specialization.
The finite field need not admit an embedding into the chosen Laurent chart.
The initial existence assertion is a hypothesis, not a consequence of trace.
-/

noncomputable section

namespace CycleQ2GenericFiniteSpecialization

open HodgeComputer CycleQ2GenericSpecialization CycleQ2AffineClearing
open scoped BigOperators

local instance coefficientCharZero : CharZero RF :=
  charZero_of_injective_algebraMap (algebraMap ℂ RF).injective

local instance coefficientIntAlgebra : Algebra ℤ RF := Ring.toIntAlgebra _

variable (L : Type*) [Field L] [Algebra RF L] [FiniteDimensional RF L]

/-- Canonical extension of the actual generic tangent derivations. -/
def tangent (direction : Direction) (j : Fin 4) : Derivation ℤ L L :=
  CycleQ2FiniteDifferentialDescent.extend
    ((CycleQ2GenericSpecialization.tangent direction j).restrictScalars ℤ)

@[simp] theorem tangent_algebraMap (direction : Direction) (j : Fin 4) (z : RF) :
    tangent L direction j (algebraMap RF L z) =
      algebraMap RF L (CycleQ2GenericSpecialization.tangent direction j z) :=
  CycleQ2FiniteDifferentialDescent.extend_algebraMap _ z

/-- These are relative operators: every rational function of the base
parameter has derivative zero, even after the finite field extension. -/
@[simp] theorem tangent_base (direction : Direction) (j : Fin 4) (b : Base) :
    tangent L direction j (algebraMap RF L (baseEmbedding direction b)) = 0 := by
  rw [tangent_algebraMap, tangent_baseEmbedding, map_zero]

theorem tangents_commute (direction : Direction) (i j : Fin 4) :
    Function.Commute (tangent L direction i) (tangent L direction j) :=
  CycleQ2FiniteDifferentialDescent.extend_commute
    ((CycleQ2GenericSpecialization.tangent direction i).restrictScalars ℤ)
    ((CycleQ2GenericSpecialization.tangent direction j).restrictScalars ℤ)
    (CycleQ2GenericSpecialization.tangents_commute direction i j)

theorem primitive_descends (direction : Direction) (A : Poly) (u : Fin 4 → L)
    (hu : ∑ j, tangent L direction j (u j) = algebraMap RF L (genericDensity direction A)) :
    ∑ j, CycleQ2GenericSpecialization.tangent direction j
      (Algebra.normalizedTrace RF L (u j)) = genericDensity direction A := by
  have ht := HoldoutConstruction.finiteNormalizedTrace_firstOrder
    (fun j => (CycleQ2GenericSpecialization.tangent direction j).restrictScalars ℤ)
    (tangent L direction)
    (fun j z => tangent_algebraMap L direction j z)
    (fun _ => 0) (genericDensity direction A) u
    (by simpa only [map_zero, mul_zero, add_zero] using hu)
  simpa only [Derivation.restrictScalars_apply, mul_zero, add_zero] using ht

theorem primitive_ascends (direction : Direction) (u : Fin 4 → RF) :
    (∑ j, tangent L direction j (algebraMap RF L (u j))) =
      algebraMap RF L (∑ j, CycleQ2GenericSpecialization.tangent direction j (u j)) := by
  simp only [tangent_algebraMap, map_sum]

theorem primitive_exists_iff (direction : Direction) (A : Poly) :
    (∃ u : Fin 4 → L,
      ∑ j, tangent L direction j (u j) = algebraMap RF L (genericDensity direction A)) ↔
    (∃ u : Fin 4 → RF,
      ∑ j, CycleQ2GenericSpecialization.tangent direction j (u j) = genericDensity direction A) := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨fun j => Algebra.normalizedTrace RF L (u j),
      primitive_descends L direction A u hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨fun j => algebraMap RF L (u j), by rw [primitive_ascends, hu]⟩

/-- The complete finite-generic-to-protected implication. No specialization
regularity, Galois hypothesis, or compatible-extension operators are supplied
by the caller; all are proved or constructed in the preceding modules. -/
theorem protected_certificate_of_finite_generic_primitive
    (direction : Direction)
    (h : ∃ u : Fin 4 → L, ∑ j, tangent L direction j (u j) =
      algebraMap RF L (genericDensity direction affineA)) :
    HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A := by
  exact protected_certificate_of_generic_primitive direction
    ((primitive_exists_iff L direction affineA).mp h)

end CycleQ2GenericFiniteSpecialization

#print axioms CycleQ2GenericFiniteSpecialization.tangent_base
#print axioms CycleQ2GenericFiniteSpecialization.primitive_exists_iff
#print axioms CycleQ2GenericFiniteSpecialization.protected_certificate_of_finite_generic_primitive
end
end


/- Component: continuation_3/IncidenceFullIndexCounts.lean -/
section
/-! The literal cubic and sextic coefficient indices have the cardinalities
already proved for the efficient exhaustive monomial enumeration. -/

namespace CycleQ2IncidenceFullIndexCounts

open CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials

def fullExponentEquiv (d : ℕ) :
    FullInvariantIndex d ≃ Exponents d (d+1) (d/2+1) where
  toFun e := ⟨fun i => (e.val i).val,by
    have hd := e.property.1
    change (e.val 0).val+(e.val 1).val+(e.val 2).val+(e.val 3).val+
      2*(e.val 4).val=d at hd
    refine ⟨(e.val 0).isLt,?_,hd,e.property.2⟩
    change (e.val 4).val<d/2+1
    omega⟩
  invFun e := ⟨fun i => ⟨e.val i,by
    have hd := e.property.2.2.1
    fin_cases i
    · change e.val 0<d+1
      omega
    · change e.val 1<d+1
      omega
    · change e.val 2<d+1
      omega
    · change e.val 3<d+1
      omega
    · change e.val 4<d+1
      omega⟩,e.property.2.2.1,e.property.2.2.2⟩
  left_inv e := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    rfl
  right_inv e := by
    apply Subtype.ext
    rfl

def fullIndexEquiv (d : ℕ) : FullInvariantIndex d ≃ FullIndex d :=
  (fullExponentEquiv d).trans (exponentEquiv d (d+1) (d/2+1)).symm

theorem cubic_count : Fintype.card (FullInvariantIndex 3)=9 :=
  (Fintype.card_congr (fullIndexEquiv 3)).trans invariant_cubic_count

theorem sextic_count : Fintype.card (FullInvariantIndex 6)=45 :=
  (Fintype.card_congr (fullIndexEquiv 6)).trans invariant_sextic_count

end CycleQ2IncidenceFullIndexCounts

#print axioms CycleQ2IncidenceFullIndexCounts.sextic_count
end


/- Component: continuation_3/IncidenceGradedBasis.lean -/
section
/-!
# The actual graded quotient basis in the incidence chart

The homogeneous piece is the image of the genuine weighted-homogeneous
polynomial submodule under the quotient map. Its basis is constructed using
the proved reduction theorem, with no dimension or flatness hypothesis.
-/

noncomputable section

namespace CycleQ2IncidenceGradedBasis

open MvPolynomial CycleQ2IncidenceNormalForm

variable {σ R M : Type*} [CommRing R] [AddCommMonoid M]

def gradedExponents (w : σ → M) (m : MonomialOrder σ)
    (h F : MvPolynomial σ R) (d : M) : Set (σ →₀ ℕ) :=
  {e | e ∈ reducedExponents m h F ∧ Finsupp.weight w e = d}

def gradedReduced (w : σ → M) (m : MonomialOrder σ)
    (h F : MvPolynomial σ R) (d : M) : Submodule R (MvPolynomial σ R) :=
  restrictSupport R (gradedExponents w m h F d)

theorem mem_gradedReduced (w : σ → M) (m : MonomialOrder σ)
    (h F p : MvPolynomial σ R) (d : M) :
    p ∈ gradedReduced w m h F d ↔ Reduced m h F p ∧ p.IsWeightedHomogeneous w d := by
  constructor
  · intro hp
    constructor
    · intro e he
      exact (hp he).1
    · intro e he
      exact (hp (mem_support_iff.mpr he)).2
  · rintro ⟨hr, hh⟩ e he
    exact ⟨hr e he, hh (mem_support_iff.mp he)⟩

/-- The genuine degree-d piece of the quotient; its definition does not
mention a proposed basis or a normal form. -/
def quotientPiece (w : σ → M) (h F : MvPolynomial σ R) (d : M) :
    Submodule R (MvPolynomial σ R ⧸ equationsIdeal h F) :=
  (weightedHomogeneousSubmodule R w d).map
    (Ideal.Quotient.mkₐ R (equationsIdeal h F)).toLinearMap

def gradedQuotientMap (w : σ → M) (m : MonomialOrder σ)
    (h F : MvPolynomial σ R) (d : M) :
    gradedReduced w m h F d →ₗ[R] quotientPiece w h F d :=
  (((Ideal.Quotient.mkₐ R (equationsIdeal h F)).toLinearMap.comp
    (gradedReduced w m h F d).subtype).codRestrict (quotientPiece w h F d)
      (fun p => Submodule.mem_map.mpr
        ⟨p.val, ((mem_gradedReduced w m h F p.val d).mp p.property).2, rfl⟩))

theorem gradedQuotientMap_bijective
    (w : σ → M) (m : MonomialOrder σ) (h F : MvPolynomial σ R) (d : M)
    (hh : m.Monic h) (hF : m.Monic F)
    (hcop : ∀ i, m.degree h i = 0 ∨ m.degree F i = 0)
    {dh dF : M} (hhhom : h.IsWeightedHomogeneous w dh)
    (hFhom : F.IsWeightedHomogeneous w dF) :
    Function.Bijective (gradedQuotientMap w m h F d) := by
  constructor
  · intro p q hpq
    apply Subtype.ext
    have hpq' := congrArg Subtype.val hpq
    change Ideal.Quotient.mk (equationsIdeal h F) p.val =
      Ideal.Quotient.mk (equationsIdeal h F) q.val at hpq'
    obtain ⟨a, b, heq⟩ := Ideal.mem_span_pair.mp (Ideal.Quotient.eq.mp hpq')
    apply sub_eq_zero.mp
    exact reduced_eq_zero_of_representation m hh hF hcop
      (reduced_sub m
        ((mem_gradedReduced w m h F p.val d).mp p.property).1
        ((mem_gradedReduced w m h F q.val d).mp q.property).1) heq.symm
  · intro q
    obtain ⟨p, hp, hpq⟩ := Submodule.mem_map.mp q.property
    obtain ⟨a, b, r, hrep, hr⟩ := exists_reduced_representation m h F p hh hF
    have hrhom : r.IsWeightedHomogeneous w d :=
      reduced_isWeightedHomogeneous w m hh hF hcop hhhom hFhom hp hr hrep
    refine ⟨⟨r, (mem_gradedReduced w m h F r d).mpr ⟨hr, hrhom⟩⟩, ?_⟩
    apply Subtype.ext
    change Ideal.Quotient.mk (equationsIdeal h F) r = q.val
    calc
      _ = Ideal.Quotient.mk (equationsIdeal h F) p := by
        apply Ideal.Quotient.eq.mpr
        apply Ideal.mem_span_pair.mpr
        refine ⟨-a, -b, ?_⟩
        rw [hrep]
        ring
      _ = q.val := hpq

def gradedQuotientEquiv
    (w : σ → M) (m : MonomialOrder σ) (h F : MvPolynomial σ R) (d : M)
    (hh : m.Monic h) (hF : m.Monic F)
    (hcop : ∀ i, m.degree h i = 0 ∨ m.degree F i = 0)
    {dh dF : M} (hhhom : h.IsWeightedHomogeneous w dh)
    (hFhom : F.IsWeightedHomogeneous w dF) :
    gradedReduced w m h F d ≃ₗ[R] quotientPiece w h F d :=
  LinearEquiv.ofBijective (gradedQuotientMap w m h F d)
    (gradedQuotientMap_bijective w m h F d hh hF hcop hhhom hFhom)

def basis
    (w : σ → M) (m : MonomialOrder σ) (h F : MvPolynomial σ R) (d : M)
    (hh : m.Monic h) (hF : m.Monic F)
    (hcop : ∀ i, m.degree h i = 0 ∨ m.degree F i = 0)
    {dh dF : M} (hhhom : h.IsWeightedHomogeneous w dh)
    (hFhom : F.IsWeightedHomogeneous w dF) :
    Module.Basis (gradedExponents w m h F d) R (quotientPiece w h F d) :=
  (MvPolynomial.basisRestrictSupport R (gradedExponents w m h F d)).map
    (gradedQuotientEquiv w m h F d hh hF hcop hhhom hFhom)

theorem basis_apply
    (w : σ → M) (m : MonomialOrder σ) (h F : MvPolynomial σ R) (d : M)
    (hh : m.Monic h) (hF : m.Monic F)
    (hcop : ∀ i, m.degree h i = 0 ∨ m.degree F i = 0)
    {dh dF : M} (hhhom : h.IsWeightedHomogeneous w dh)
    (hFhom : F.IsWeightedHomogeneous w dF)
    (e : gradedExponents w m h F d) :
    (basis w m h F d hh hF hcop hhhom hFhom e :
        MvPolynomial σ R ⧸ equationsIdeal h F) =
      Ideal.Quotient.mk (equationsIdeal h F) (monomial e.val 1) := by
  change Ideal.Quotient.mk (equationsIdeal h F)
    (AddMonoidAlgebra.ofCoeff
      (((Finsupp.supportedEquivFinsupp (R := R) (gradedExponents w m h F d)).symm
        (Finsupp.single e 1) : Finsupp.supported R R (gradedExponents w m h F d)) :
        (σ →₀ ℕ) →₀ R)) = _
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  rfl

section FullIncidence

variable [Nontrivial R]

/-- Identifies every standard invariant exponent, rather than only a displayed
list of monomials, with the finite index used by the checked counts. -/
def fullExponentEquiv (d : ℕ)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    gradedExponents fullGrading fullAuxiliaryOrder
      (normalizedFullCubic hcoeff) (normalizedFullSextic Fcoeff) (d, 0) ≃
      CycleQ2IncidenceMonomials.Exponents d 3 3 where
  toFun e := ⟨e.val, by
    have hb := e.property.1
    change (¬ fullAuxiliaryOrder.degree (normalizedFullCubic hcoeff) ≤ e.val) ∧
      (¬ fullAuxiliaryOrder.degree (normalizedFullSextic Fcoeff) ≤ e.val) at hb
    rw [(normalizedFullCubic_leading_data hcoeff).1,
      (normalizedFullSextic_leading_data Fcoeff).1,
      single_three_le_iff, single_three_le_iff] at hb
    have hg := e.property.2
    rw [fullGrading_weight] at hg
    have hd := congrArg Prod.fst hg
    have hc := congrArg Prod.snd hg
    refine ⟨Nat.lt_of_not_ge hb.1, Nat.lt_of_not_ge hb.2, hd, ?_⟩
    exact Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).mp hc)⟩
  invFun e := ⟨Finsupp.equivFunOnFinite.symm e.val, by
    constructor
    · change (¬ fullAuxiliaryOrder.degree (normalizedFullCubic hcoeff) ≤
          Finsupp.equivFunOnFinite.symm e.val) ∧
        (¬ fullAuxiliaryOrder.degree (normalizedFullSextic Fcoeff) ≤
          Finsupp.equivFunOnFinite.symm e.val)
      rw [(normalizedFullCubic_leading_data hcoeff).1,
        (normalizedFullSextic_leading_data Fcoeff).1,
        single_three_le_iff, single_three_le_iff]
      exact ⟨Nat.not_le_of_lt e.property.1, Nat.not_le_of_lt e.property.2.1⟩
    · rw [fullGrading_weight]
      apply Prod.ext
      · exact e.property.2.2.1
      · apply (ZMod.natCast_eq_zero_iff _ _).mpr
        exact Nat.dvd_of_mod_eq_zero e.property.2.2.2⟩
  left_inv e := by
    apply Subtype.ext
    exact Finsupp.equivFunOnFinite.symm_apply_apply e.val
  right_inv e := by
    apply Subtype.ext
    rfl

/-- Basis of the actual invariant weighted-degree piece of the full incidence
quotient. Its index is the completely enumerated standard monomial set. -/
def fullBasis (d : ℕ)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    Module.Basis (CycleQ2IncidenceMonomials.StandardIndex d) R
      (quotientPiece fullGrading (normalizedFullCubic hcoeff)
        (normalizedFullSextic Fcoeff) (d, 0)) :=
  (basis fullGrading fullAuxiliaryOrder
    (normalizedFullCubic hcoeff) (normalizedFullSextic Fcoeff) (d, 0)
    (normalizedFullCubic_leading_data hcoeff).2 (normalizedFullSextic_leading_data Fcoeff).2
    (full_coprime hcoeff Fcoeff) (normalizedFullCubic_homogeneous hcoeff)
    (normalizedFullSextic_homogeneous Fcoeff)).reindex
      ((fullExponentEquiv d hcoeff Fcoeff).trans
        (CycleQ2IncidenceMonomials.exponentEquiv d 3 3).symm)

theorem fullBasis_apply (d : ℕ)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (e : CycleQ2IncidenceMonomials.StandardIndex d) :
    (fullBasis d hcoeff Fcoeff e : MvPolynomial (Fin 5) R ⧸
        equationsIdeal (normalizedFullCubic hcoeff) (normalizedFullSextic Fcoeff)) =
      Ideal.Quotient.mk (equationsIdeal (normalizedFullCubic hcoeff)
        (normalizedFullSextic Fcoeff))
        (monomial (Finsupp.equivFunOnFinite.symm
          (CycleQ2IncidenceMonomials.coordinates e)) 1) := by
  rw [fullBasis, Module.Basis.reindex_apply, basis_apply]
  rfl

theorem fullPiece_finrank [StrongRankCondition R] (d : ℕ)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    Module.finrank R (quotientPiece fullGrading (normalizedFullCubic hcoeff)
      (normalizedFullSextic Fcoeff) (d, 0)) =
        Fintype.card (CycleQ2IncidenceMonomials.StandardIndex d) :=
  Module.finrank_eq_card_basis (fullBasis d hcoeff Fcoeff)

theorem fullPiece_degree14_finrank [StrongRankCondition R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    Module.finrank R (quotientPiece fullGrading (normalizedFullCubic hcoeff)
      (normalizedFullSextic Fcoeff) (14, 0)) = 239 := by
  rw [fullPiece_finrank, CycleQ2IncidenceMonomials.standard_degree14_count]

theorem fullPiece_degree28_finrank [StrongRankCondition R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    Module.finrank R (quotientPiece fullGrading (normalizedFullCubic hcoeff)
      (normalizedFullSextic Fcoeff) (28, 0)) = 1058 := by
  rw [fullPiece_finrank, CycleQ2IncidenceMonomials.standard_degree28_count]

theorem fullPiece_degree42_finrank [StrongRankCondition R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    Module.finrank R (quotientPiece fullGrading (normalizedFullCubic hcoeff)
      (normalizedFullSextic Fcoeff) (42, 0)) = 2465 := by
  rw [fullPiece_finrank, CycleQ2IncidenceMonomials.standard_degree42_count]

end FullIncidence

end CycleQ2IncidenceGradedBasis

#print axioms CycleQ2IncidenceGradedBasis.gradedQuotientMap_bijective
#print axioms CycleQ2IncidenceGradedBasis.basis_apply
#print axioms CycleQ2IncidenceGradedBasis.fullBasis_apply
#print axioms CycleQ2IncidenceGradedBasis.fullPiece_degree42_finrank
end
end


/- Component: continuation_3/cylinder_bridge/LinearQuotientSurjectivity.lean -/
section
/-! Surjectivity and evaluation for the actual kernel quotient map. -/

noncomputable section
namespace CycleQ2LinearRangeDescent

variable {R M P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]

theorem kernelQuotientInjection_apply_mk (g : M →ₗ[R] P) (K : Submodule R M)
    (h : LinearMap.ker g=K) (x : M) :
    kernelQuotientInjection g K h (K.mkQ x)=g x := rfl

theorem kernelQuotientInjection_surjective (g : M →ₗ[R] P) (K : Submodule R M)
    (h : LinearMap.ker g=K) (hg : Function.Surjective g) :
    Function.Surjective (kernelQuotientInjection g K h) := by
  intro p
  obtain ⟨x,hx⟩ := hg p
  exact ⟨K.mkQ x,hx⟩

end CycleQ2LinearRangeDescent

#print axioms CycleQ2LinearRangeDescent.kernelQuotientInjection_surjective
end
end


/- Component: continuation_3/PointedSquareGeneric.lean -/
section
/-! The generic component of a literal Jacobian-localized square system can
be chosen to specialize to its given nonsingular seed.  The resulting
coordinates satisfy the same actual equations and Jacobian condition, and
every polynomial identity at the generic point remains an identity at the
seed.  No map from the entire generic field to the special field is asserted.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2PointedSquareGeneric

open MvPolynomial HoldoutConstruction CycleQ2PointedEtaleGeneric
open scoped TensorProduct

variable {R K T ι : Type*} [CommRing R] [IsDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field T] [Algebra R T] [Fintype ι] [DecidableEq ι]

theorem seedEtaleEval_polynomial
    (e : ι → MvPolynomial ι R) (seed : ι → T)
    (he : ∀i,aeval seed (e i)=0)
    (hj : IsUnit (Matrix.det (fun i j => aeval seed (pderiv i (e j)))))
    (p : MvPolynomial ι R) :
    squareSystemEtaleEval e seed he hj
      (algebraMap (SquareSystemRing e) (SquareEtaleRing e) (Ideal.Quotient.mk _ p))=
        aeval seed p := by
  rw [squareSystemEtaleEval,IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

theorem polynomial_zero_specializes
    (e : ι → MvPolynomial ι R) (seed : ι → T)
    (he : ∀i,aeval seed (e i)=0)
    (hj : IsUnit (Matrix.det (fun i j => aeval seed (pderiv i (e j)))))
    (I : Ideal (SquareGenericAlgebra K e))
    (hI : I.comap (Algebra.TensorProduct.includeRight :
        SquareEtaleRing e →ₐ[R] SquareGenericAlgebra K e).toRingHom ≤
      RingHom.ker (squareSystemEtaleEval e seed he hj).toRingHom)
    (p : MvPolynomial ι R)
    (hp : aeval (squareGenericCoordinates e I) p=0) : aeval seed p=0 := by
  let b : SquareEtaleRing e :=
    algebraMap (SquareSystemRing e) (SquareEtaleRing e) (Ideal.Quotient.mk _ p)
  have hb : Ideal.Quotient.mk I (Algebra.TensorProduct.includeRight b)=0 := by
    change squareGenericMap e I (Ideal.Quotient.mk _ p)=0
    rw [←squareGeneric_eval]
    exact hp
  have hs := seed_zero_of_generic_zero K (squareSystemEtaleEval e seed he hj) I hI b hb
  change squareSystemEtaleEval e seed he hj
    (algebraMap (SquareSystemRing e) (SquareEtaleRing e) (Ideal.Quotient.mk _ p))=0 at hs
  rwa [seedEtaleEval_polynomial] at hs

theorem exists_pointed_square_fieldFactor
    (e : ι → MvPolynomial ι R) (seed : ι → T)
    (he : ∀i,aeval seed (e i)=0)
    (hj : IsUnit (Matrix.det (fun i j => aeval seed (pderiv i (e j))))) :
    ∃ I : Ideal (SquareGenericAlgebra K e), I.IsMaximal ∧
      Module.Finite K ((SquareGenericAlgebra K e) ⧸ I) ∧
      Algebra.IsSeparable K ((SquareGenericAlgebra K e) ⧸ I) ∧
      (I.comap (Algebra.TensorProduct.includeRight :
          SquareEtaleRing e →ₐ[R] SquareGenericAlgebra K e).toRingHom ≤
        RingHom.ker (squareSystemEtaleEval e seed he hj).toRingHom) ∧
      (∀ i,aeval (squareGenericCoordinates e I) (e i)=0) ∧
      IsUnit (Matrix.det (fun i j =>
        aeval (squareGenericCoordinates e I) (pderiv i (e j)))) ∧
      (∀ p : MvPolynomial ι R,
        aeval (squareGenericCoordinates e I) p=0 → aeval seed p=0) := by
  letI : Algebra.Etale R (SquareEtaleRing e) := square_system_jacobian_etale e
  obtain ⟨I,hmax,hfin,hsep,hpoint⟩ :=
    exists_pointed_fieldFactor K (squareSystemEtaleEval e seed he hj)
  exact ⟨I,hmax,hfin,hsep,hpoint,squareGeneric_solution e I,
    squareGeneric_jacobian e I,polynomial_zero_specializes e seed he hj I hpoint⟩

end CycleQ2PointedSquareGeneric

#print axioms CycleQ2PointedSquareGeneric.exists_pointed_square_fieldFactor
#print axioms CycleQ2PointedSquareGeneric.polynomial_zero_specializes
end
end


/- Component: continuation_3/cylinder_bridge/PolynomialAffineBaseChange.lean -/
section
/-! Coefficient base change of the literal affine-slice Jacobian, and the
fact that a zero direction row fixes the corresponding external parameter. -/

noncomputable section
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2PolynomialAffineSlice
open MvPolynomial Matrix

variable {R S T σ ι m : Type*} [CommRing R] [CommRing S] [CommRing T]

theorem jacobian_map (ψ : R →+* S) (φ : S →+* T) (x : σ → T)
    (e : m → MvPolynomial σ R) :
    jacobian φ x (fun q => MvPolynomial.map ψ (e q)) = jacobian (φ.comp ψ) x e := by
  funext q j
  simp only [jacobian,pderiv_map,eval₂Hom_map_hom]

theorem pointValue_of_zero_row [Fintype ι] (φ : R →+* S)
    (a : σ → R) (B : Matrix σ ι R) (x : ι → S) (k : σ)
    (hB : ∀ j, B k j=0) : pointValue φ a B x k=φ (a k) := by
  simp only [pointValue,hB,map_zero,zero_mul,Finset.sum_const_zero,add_zero]

theorem affinePoint_of_zero_row [Fintype ι] (a : σ → R) (B : Matrix σ ι R)
    (k : σ) (hB : ∀ j, B k j=0) : affinePoint a B k=C (a k) := by
  simp only [affinePoint,hB,map_zero,zero_mul,Finset.sum_const_zero,add_zero]

end CycleQ2PolynomialAffineSlice

#print axioms CycleQ2PolynomialAffineSlice.jacobian_map
#print axioms CycleQ2PolynomialAffineSlice.pointValue_of_zero_row
end
end


/- Component: continuation_3/cylinder_bridge/PolynomialDerivationChainRule.lean -/
section
/-! Differentiating an actual polynomial solution gives the literal
Jacobian equation.  In affine coordinates this is exactly the relation
used by the adjugate trace numerator. -/

noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2PolynomialDerivationChainRule
open MvPolynomial Matrix CycleQ2PolynomialAffineSlice

variable {R S σ m ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Fintype σ]

theorem derivation_aeval (D : Derivation R S S) (x : σ → S)
    (p : MvPolynomial σ R) :
    D (aeval x p) = ∑ k, aeval x (pderiv k p) * D (x k) := by
  classical
  refine MvPolynomial.induction_on (motive := fun f =>
    D (aeval x f) = ∑ k, aeval x (pderiv k f) * D (x k)) p ?_ ?_ ?_
  · intro r
    simp only [aeval_C,Derivation.map_algebraMap,pderiv_C,map_zero,zero_mul,
      Finset.sum_const_zero]
  · intro p q hp hq
    simp only [map_add,hp,hq,add_mul,Finset.sum_add_distrib]
  · intro p j hp
    have hs : (∑ k, aeval x p * aeval x (pderiv k (X j : MvPolynomial σ R)) * D (x k)) =
        aeval x p * D (x j) := by
      rw [Finset.sum_eq_single j]
      · rw [pderiv_X_self,map_one,mul_one]
      · intro k _ hk
        rw [pderiv_X_of_ne (Ne.symm hk),map_zero,mul_zero,zero_mul]
      · intro hj
        exact (hj (Finset.mem_univ j)).elim
    calc
      _ = aeval x p * D (x j) + x j * (∑ k, aeval x (pderiv k p) * D (x k)) := by
        rw [map_mul,aeval_X,Derivation.leibniz,hp]
        rfl
      _ = (∑ k, aeval x (pderiv k p) * x j * D (x k)) +
          ∑ k, aeval x p * aeval x (pderiv k (X j : MvPolynomial σ R)) * D (x k) := by
        rw [hs,Finset.mul_sum,add_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = ∑ k, aeval x (pderiv k (p*X j)) * D (x k) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        rw [pderiv_mul,map_add,map_mul,map_mul,aeval_X]
        ring

theorem differentiated_equations (D : Derivation R S S) (x : σ → S)
    (e : m → MvPolynomial σ R) (he : ∀ q, aeval x (e q)=0) :
    jacobian (algebraMap R S) x e *ᵥ (fun k => D (x k))=0 := by
  funext q
  have h := derivation_aeval D x (e q)
  rw [he q,map_zero] at h
  exact h.symm

theorem derivation_affine_value [Fintype ι] (D : Derivation R S S)
    (a : σ → S) (B : Matrix σ ι R) (z : ι → S) (k : σ) :
    D (a k + ∑ j, algebraMap R S (B k j) * z j) =
      D (a k) + ∑ j, algebraMap R S (B k j) * D (z j) := by
  simp only [map_add,map_sum,Derivation.leibniz,Derivation.map_algebraMap,
    smul_eq_mul,mul_zero,add_zero]

theorem implicit_derivative_relation [Fintype m] [Fintype ι]
    (D : Derivation R S S) (x : σ → S) (z : ι → S)
    (P : Matrix ι m R) (B : Matrix σ ι R) (direction : σ → S)
    (e : m → MvPolynomial σ R) (he : ∀ q, aeval x (e q)=0)
    (hder : ∀ k, D (x k)=direction k+
      (B.map (algebraMap R S) *ᵥ (fun j => D (z j))) k) :
    (P.map (algebraMap R S) * jacobian (algebraMap R S) x e * B.map (algebraMap R S)) *ᵥ
        (fun j => D (z j)) +
      (P.map (algebraMap R S) * jacobian (algebraMap R S) x e) *ᵥ direction=0 := by
  have hy : (fun k => D (x k))=direction+B.map (algebraMap R S) *ᵥ (fun j => D (z j)) :=
    funext hder
  have h := differentiated_equations D x e he
  rw [hy,mulVec_add] at h
  have hp := congrArg (fun v => P.map (algebraMap R S) *ᵥ v) h
  simp only [mulVec_add,mulVec_mulVec,mulVec_zero,← Matrix.mul_assoc] at hp
  exact (add_comm _ _).trans hp

end CycleQ2PolynomialDerivationChainRule

#print axioms CycleQ2PolynomialDerivationChainRule.derivation_aeval
#print axioms CycleQ2PolynomialDerivationChainRule.implicit_derivative_relation
end
end


/- Component: continuation_3/cylinder_bridge/SeedCechCharts.lean -/
section
/-!
# Honest power-series charts for the sparse curve Čech trace

At each endpoint of the finite map to P¹ with coordinates (x₁:x₃), x₂ is
already a unit over the power-series ring.  Thus every element of the x₂-open
has zero endpoint Laurent residue.  This is the first full coboundary check;
it applies to all powers of the denominator.
-/

noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace CycleQ2SeedCech

abbrev PS := PowerSeries ℂ
abbrev LS := LaurentSeries ℂ

def endpointX : Bool → PS
  | false => 1
  | true => PowerSeries.X

def endpointY : Bool → PS
  | false => PowerSeries.X
  | true => 1

def seriesMap : PS →+* LS := HahnSeries.ofPowerSeries ℤ ℂ

abbrev PowerChart (r : ℂ) (e : Bool) :=
  CurveAlgebra (PowerSeries.C r) (PowerSeries.C Complex.I) (endpointX e) (endpointY e)

abbrev LaurentChart (r : ℂ) (e : Bool) :=
  CurveAlgebra (seriesMap (PowerSeries.C r)) (seriesMap (PowerSeries.C Complex.I))
    (seriesMap (endpointX e)) (seriesMap (endpointY e))

def chartEmbedding (r : ℂ) (e : Bool) : PowerChart r e →+* LaurentChart r e :=
  curveMap seriesMap (PowerSeries.C r) (PowerSeries.C Complex.I)
    (endpointX e) (endpointY e)

def endpointResidue (r : ℂ) (e : Bool) : LaurentChart r e →+ ℂ :=
  (HahnSeries.coeff.addMonoidHom (-1 : ℤ)).comp
    ((coefficient (seriesMap (PowerSeries.C r)) (seriesMap (PowerSeries.C Complex.I))
      (seriesMap (endpointX e)) (seriesMap (endpointY e))).toAddMonoidHom)

theorem endpointResidue_integral (r : ℂ) (e : Bool) (z : PowerChart r e) :
    endpointResidue r e (chartEmbedding r e z) = 0 := by
  change (coefficient (seriesMap (PowerSeries.C r)) (seriesMap (PowerSeries.C Complex.I))
    (seriesMap (endpointX e)) (seriesMap (endpointY e))
    (curveMap seriesMap (PowerSeries.C r) (PowerSeries.C Complex.I)
      (endpointX e) (endpointY e) z)).coeff (-1) = 0
  rw [coefficient_curveMap]
  exact PowerSeries.coeff_coe _ _ |>.trans (by norm_num)

theorem endpointNorm_isUnit (r : ℂ) (e : Bool) :
    IsUnit (norm (PowerSeries.C r) (PowerSeries.C Complex.I)
      (endpointX e) (endpointY e)) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  rw [isUnit_iff_ne_zero]
  cases e <;>
    norm_num [norm, endpointX, endpointY, Complex.ext_iff, Complex.I_sq]

def endpointNormUnit (r : ℂ) (e : Bool) : PSˣ := (endpointNorm_isUnit r e).unit

theorem endpointNormUnit_spec (r : ℂ) (e : Bool) :
    (endpointNormUnit r e : PS) = norm (PowerSeries.C r) (PowerSeries.C Complex.I)
      (endpointX e) (endpointY e) := (endpointNorm_isUnit r e).unit_spec

def powerX2Unit (r : ℂ) (e : Bool) : (PowerChart r e)ˣ :=
  x2Unit _ _ _ _ (endpointNormUnit r e) (endpointNormUnit_spec r e)

def laurentX2Unit (r : ℂ) (e : Bool) : (LaurentChart r e)ˣ :=
  Units.map (chartEmbedding r e) (powerX2Unit r e)

/-- Every x₂-localized polynomial expression is integral in both endpoint
charts, so its Laurent residue vanishes for arbitrary denominator powers. -/
theorem endpointResidue_x2_open (r : ℂ) (e : Bool) (z : PowerChart r e) (n : ℕ) :
    endpointResidue r e
      (chartEmbedding r e z * ((laurentX2Unit r e)⁻¹ : (LaurentChart r e)ˣ) ^ n) = 0 := by
  have heq : chartEmbedding r e z * ((laurentX2Unit r e)⁻¹ : (LaurentChart r e)ˣ) ^ n =
      chartEmbedding r e (z * ((powerX2Unit r e)⁻¹ : (PowerChart r e)ˣ) ^ n) := by
    simp [laurentX2Unit]
  rw [heq]
  exact endpointResidue_integral r e _

end CycleQ2SeedCech

#print axioms CycleQ2SeedCech.endpointResidue_x2_open
end
end


/- Component: continuation_3/cylinder_bridge/SeedCechCoefficient.lean -/
section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

namespace CycleQ2SeedCech
open Polynomial

variable {R : Type*} [CommRing R] [Nontrivial R]

instance quadratic_nontrivial (r x y : R) : Nontrivial (Quadratic r x y) :=
  Ideal.Quotient.nontrivial_iff.mpr (by
    intro hh
    have he := (quadratic_monic r x y).eq_one_of_isUnit
      (Ideal.span_singleton_eq_top.mp hh)
    have hn := congrArg Polynomial.natDegree he
    rw [quadratic, natDegree_X_pow_sub_C, natDegree_one] at hn
    omega)

theorem cubic_degree (r i x y : R) : (cubic r i x y).degree = 3 := by
  unfold cubic
  rw [add_assoc]
  have hl : (C ((a r x y + algebraMap R _ x) * algebraMap R _ y) * X +
    C (a r x y * algebraMap R _ (x ^ 2) +
      algebraMap R _ ((1 - i) * y ^ 3 - i * x ^ 3))).degree < 3 := by
    apply lt_of_le_of_lt (degree_add_le _ _)
    apply max_lt
    · exact lt_of_le_of_lt (degree_C_mul_X_le _) (by norm_num)
    · exact lt_of_le_of_lt degree_C_le (by norm_num)
  rw [degree_add_eq_left_of_degree_lt (by simpa using hl)]
  simp

theorem coefficient_small_monomial (r i x y z : R) (j k : ℕ)
    (hj : j < 2) (hk : k < 3) :
    coefficient r i x y (base r i x y z * x0 r i x y ^ j * x2 r i x y ^ k) =
      if j = 1 ∧ k = 2 then z else 0 := by
  have hc : AdjoinRoot.modByMonicHom (cubic_monic r i x y)
      (base r i x y z * x0 r i x y ^ j * x2 r i x y ^ k) =
      C (algebraMap R (Quadratic r x y) z * a r x y ^ j) * X ^ k := by
    have heq : base r i x y z * x0 r i x y ^ j * x2 r i x y ^ k =
        AdjoinRoot.mk (cubic r i x y)
          (C (algebraMap R (Quadratic r x y) z * a r x y ^ j) * X ^ k) := by
      simp [base, x0, x2, AdjoinRoot.algebraMap_eq]
    rw [heq, AdjoinRoot.modByMonicHom_mk]
    apply (modByMonic_eq_self_iff (cubic_monic r i x y)).mpr
    exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) (by
      rw [cubic_degree]
      exact_mod_cast hk)
  have hq : AdjoinRoot.modByMonicHom (quadratic_monic r x y)
      (algebraMap R (Quadratic r x y) z * a r x y ^ j) = C z * X ^ j := by
    have heq : algebraMap R (Quadratic r x y) z * a r x y ^ j =
        AdjoinRoot.mk (quadratic r x y) (C z * X ^ j) := by
      simp [a, AdjoinRoot.algebraMap_eq]
    rw [heq, AdjoinRoot.modByMonicHom_mk]
    apply (modByMonic_eq_self_iff (quadratic_monic r x y)).mpr
    apply lt_of_le_of_lt (degree_C_mul_X_pow_le _ _)
    rw [quadratic, degree_X_pow_sub_C (by decide)]
    exact_mod_cast hj
  change ((AdjoinRoot.modByMonicHom (quadratic_monic r x y))
    (((AdjoinRoot.modByMonicHom (cubic_monic r i x y))
      (base r i x y z * x0 r i x y ^ j * x2 r i x y ^ k)).coeff 2)).coeff 1 = _
  rw [hc]
  simp only [coeff_C_mul_X_pow]
  by_cases hk2 : k = 2
  · subst k
    simp only [ite_true, hq, coeff_C_mul_X_pow]
    simp [eq_comm]
  · simp [hk2, eq_comm]

theorem coefficient_base_mul (r i x y z : R) (v : CurveAlgebra r i x y) :
    coefficient r i x y (base r i x y z * v) = z * coefficient r i x y v := by
  unfold base
  rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply R
    (Quadratic r x y) (CurveAlgebra r i x y)]
  simpa only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply] using
    (coefficient r i x y).map_smul z v

def quadraticCoefficient (r x y : R) : Quadratic r x y →ₗ[R] R :=
  (Polynomial.lcoeff R 1).comp (AdjoinRoot.modByMonicHom (quadratic_monic r x y))

theorem coefficient_quadratic (r i x y : R) (q : Quadratic r x y) (k : ℕ)
    (hk : k < 3) :
    coefficient r i x y
      (algebraMap (Quadratic r x y) (CurveAlgebra r i x y) q * x2 r i x y ^ k) =
      if k = 2 then quadraticCoefficient r x y q else 0 := by
  have heq : algebraMap (Quadratic r x y) (CurveAlgebra r i x y) q * x2 r i x y ^ k =
      AdjoinRoot.mk (cubic r i x y) (C q * X ^ k) := by
    simp [x2, AdjoinRoot.algebraMap_eq]
  change ((AdjoinRoot.modByMonicHom (quadratic_monic r x y))
    (((AdjoinRoot.modByMonicHom (cubic_monic r i x y))
      (algebraMap (Quadratic r x y) (CurveAlgebra r i x y) q *
        x2 r i x y ^ k)).coeff 2)).coeff 1 = _
  rw [heq, AdjoinRoot.modByMonicHom_mk,
    (modByMonic_eq_self_iff (cubic_monic r i x y)).mpr (by
      apply lt_of_le_of_lt (degree_C_mul_X_pow_le _ _)
      rw [cubic_degree]
      exact_mod_cast hk)]
  simp only [coeff_C_mul_X_pow]
  by_cases h : k = 2
  · subst k
    rfl
  · simp only [Ne.symm h, h, if_false, map_zero, coeff_zero]

theorem quadraticCoefficient_small (r x y z : R) (j : ℕ) (hj : j < 2) :
    quadraticCoefficient r x y
      (algebraMap R (Quadratic r x y) z * a r x y ^ j) =
      if j = 1 then z else 0 := by
  have heq : algebraMap R (Quadratic r x y) z * a r x y ^ j =
      AdjoinRoot.mk (quadratic r x y) (C z * X ^ j) := by
    simp [a, AdjoinRoot.algebraMap_eq]
  change ((AdjoinRoot.modByMonicHom (quadratic_monic r x y))
    (algebraMap R (Quadratic r x y) z * a r x y ^ j)).coeff 1 = _
  rw [heq, AdjoinRoot.modByMonicHom_mk,
    (modByMonic_eq_self_iff (quadratic_monic r x y)).mpr (by
      apply lt_of_le_of_lt (degree_C_mul_X_pow_le _ _)
      rw [quadratic, degree_X_pow_sub_C (by decide)]
      exact_mod_cast hj)]
  simp [coeff_C_mul_X_pow, eq_comm]

end CycleQ2SeedCech
end
end


/- Component: continuation_3/cylinder_bridge/SeedCechNormal.lean -/
section
/-! Homogeneous normal forms for the actual published sparse curve. -/

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedCech
open MvPolynomial CycleQ2SeedTrace CycleQ2IncidenceNormalForm
open scoped MonomialOrder

@[simp] private lemma vec4_two {α : Type*} (a b c d : α) :
    ![a,b,c,d] (2 : Fin 4) = c := rfl
@[simp] private lemma vec4_three {α : Type*} (a b c d : α) :
    ![a,b,c,d] (3 : Fin 4) = d := rfl
@[simp] private lemma vec5_two {α : Type*} (a b c d e : α) :
    ![a,b,c,d,e] (2 : Fin 5) = c := rfl
@[simp] private lemma vec5_three {α : Type*} (a b c d e : α) :
    ![a,b,c,d,e] (3 : Fin 5) = d := rfl
@[simp] private lemma vec5_four {α : Type*} (a b c d e : α) :
    ![a,b,c,d,e] (4 : Fin 5) = e := rfl

def curveWeight : Exp →+ ℕ where
  toFun d := 3 * d 0 + d 1 + 3 * d 2 + d 3
  map_zero' := by simp
  map_add' d e := by simp only [Finsupp.add_apply]; omega

def curveOrder : MonomialOrder (Fin 4) := weightedOrder MonomialOrder.lex curveWeight

def curveF1 (r : ℂ) : Poly := relation r 0
def curveH : Poly := h
def curveIdeal (r : ℂ) : Ideal Poly := Ideal.span {curveF1 r, curveH}

def hTailExponent (j : Fin 5) : Exp :=
  ![exponent ![0,0,0,3], exponent ![0,1,1,1], exponent ![1,0,1,1],
    exponent ![1,2,0,0], exponent ![0,3,0,0]] j

def hTailCoefficient (j : Fin 5) : ℂ := ![1 - Complex.I, 1, 1, 1, -Complex.I] j

theorem curveF1_shape (r : ℂ) :
    curveF1 r = monomial (exponent ![2,0,0,0]) 1 +
      ∑ _j : Fin 1, monomial (exponent ![0,1,0,1]) (-r) := by
  simp only [Fin.sum_univ_one]
  rw [monomial_eq_C_mul_mon, monomial_eq_C_mul_mon]
  simp [curveF1, relation, mon] <;> ring

theorem curveH_shape :
    curveH = monomial (exponent ![0,0,3,0]) 1 +
      ∑ j : Fin 5, monomial (hTailExponent j) (hTailCoefficient j) := by
  simp only [Fin.sum_univ_succ, hTailExponent, hTailCoefficient,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_succ, Fin.reduceSucc,
    monomial_eq_C_mul_mon]
  norm_num [curveH, h, b, mon, Matrix.cons_val_succ, Fin.reduceSucc]
  ring

theorem curveF1_leading_data (r : ℂ) :
    curveOrder.degree (curveF1 r) = exponent ![2,0,0,0] ∧ curveOrder.Monic (curveF1 r) := by
  rw [curveF1_shape]
  apply degree_monic_add_sum
  · apply weightedOrder_lt_of_weight_lt
    change (0 : ℕ) < 6
    decide
  · intro j
    apply weightedOrder_lt_of_weight_lt
    change (2 : ℕ) < 6
    decide

theorem curveH_leading_data :
    curveOrder.degree curveH = exponent ![0,0,3,0] ∧ curveOrder.Monic curveH := by
  rw [curveH_shape]
  apply degree_monic_add_sum
  · apply weightedOrder_lt_of_weight_lt
    change (0 : ℕ) < 9
    decide
  · intro j
    apply weightedOrder_lt_of_weight_lt
    fin_cases j <;> norm_num [curveWeight, hTailExponent, Matrix.cons_val_succ, Fin.reduceSucc]

theorem curve_leading_coprime (r : ℂ) :
    ∀ j, curveOrder.degree (curveF1 r) j = 0 ∨ curveOrder.degree curveH j = 0 := by
  rw [(curveF1_leading_data r).1, curveH_leading_data.1]
  intro j
  fin_cases j <;> simp

theorem mon_homogeneous (a b c d : ℕ) : (mon a b c d).IsHomogeneous (a+b+c+d) := by
  rw [mon_eq_monomial]
  apply isHomogeneous_monomial
  norm_num [Finsupp.degree_eq_sum, Fin.sum_univ_succ, add_assoc,
    Matrix.cons_val_succ, Fin.reduceSucc]

theorem curveF1_homogeneous (r : ℂ) : (curveF1 r).IsHomogeneous 2 := by
  have h0 : (mon 2 0 0 0).IsHomogeneous 2 := by simpa using mon_homogeneous 2 0 0 0
  have h1 : (mon 0 1 0 1).IsHomogeneous 2 := by simpa using mon_homogeneous 0 1 0 1
  simpa [curveF1, relation, mon, mul_assoc] using h0.sub (h1.C_mul r)

theorem curveH_homogeneous : curveH.IsHomogeneous 3 := by
  have hm (a b c d : ℕ) (hd : a+b+c+d=3) : (mon a b c d).IsHomogeneous 3 := by
    simpa only [hd] using mon_homogeneous a b c d
  have h1 := (hm 0 0 0 3 (by omega)).add (hm 0 0 3 0 (by omega))
  have h2 := h1.add (hm 0 1 1 1 (by omega))
  have h3 := h2.add (hm 1 0 1 1 (by omega))
  have h4 := h3.add (hm 1 2 0 0 (by omega))
  have h5 := h4.sub (((hm 0 3 0 0 (by omega)).add (hm 0 0 0 3 (by omega))).C_mul Complex.I)
  simpa [curveH, h, b, mon, mul_assoc] using h5

def CurveReduced (p : Poly) : Prop := ∀ d ∈ p.support, d 0 < 2 ∧ d 2 < 3

theorem curveReduced_iff (r : ℂ) (p : Poly) :
    CurveReduced p ↔ Reduced curveOrder (curveF1 r) curveH p := by
  simp only [CurveReduced, Reduced, (curveF1_leading_data r).1, curveH_leading_data.1]
  apply forall_congr'
  intro d
  apply forall_congr'
  intro hd
  have he0 : exponent ![2,0,0,0] = Finsupp.single (0 : Fin 4) 2 := by
    ext j; fin_cases j <;> simp
  have he2 : exponent ![0,0,3,0] = Finsupp.single (2 : Fin 4) 3 := by
    ext j; fin_cases j <;> simp
  rw [he0, he2, Finsupp.single_le_iff, Finsupp.single_le_iff]
  omega

/-- Every homogeneous function on the actual curve has a homogeneous
representative whose x₀ and x₂ exponents are respectively less than 2 and 3. -/
theorem exists_homogeneous_curve_normal (r : ℂ) (p : Poly) (d : ℕ)
    (hp : p.IsHomogeneous d) :
    ∃ q : Poly, CurveReduced q ∧ q.IsHomogeneous d ∧ p - q ∈ curveIdeal r := by
  obtain ⟨u,v,q,hpq,hq⟩ := exists_reduced_representation curveOrder (curveF1 r) curveH p
    (curveF1_leading_data r).2 curveH_leading_data.2
  refine ⟨q, (curveReduced_iff r q).mpr hq, ?_, ?_⟩
  · exact reduced_isHomogeneous curveOrder (curveF1_leading_data r).2
      curveH_leading_data.2 (curve_leading_coprime r)
      (curveF1_homogeneous r) curveH_homogeneous hp hq hpq
  · apply Ideal.mem_span_pair.mpr
    exact ⟨u,v,by rw [hpq]; ring⟩

end CycleQ2SeedCech

#print axioms CycleQ2SeedCech.exists_homogeneous_curve_normal
end
end


/- Component: continuation_3/cylinder_bridge/SegreGenericSection.lean -/
section
/-! The three literal components of M·T define one common homogeneous
ideal.  On every unit-pivot chart this actual ideal is generated by a
regular linear form, and the local generators are related by the already
proved matrix transition units.  The section parameters are independent
polynomial variables, so regularity needs no domain assumption. -/

noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SegreGenericSection
open MvPolynomial Matrix CycleQ2SegreCech CycleQ2GenericLinearSection

variable {R : Type*} [CommRing R]

def sectionVector (M : Matrix (Fin 3) (Fin 3) R) (i : Fin 3) :
    MvPolynomial (Fin 3) R := linearForm (M i)

def sectionIdeal (M : Matrix (Fin 3) (Fin 3) R) : Ideal (MvPolynomial (Fin 3) R) :=
  Ideal.span (Set.range (sectionVector M))

def localEquation (M : Matrix (Fin 3) (Fin 3) R) (p : Chart) : MvPolynomial (Fin 3) R :=
  sectionVector M p.1

/-- When the matrix entries have the same homogeneous degree, division
by the pivot gives the degree-zero local equation on its projective chart. -/
def normalizedEquation (M : Matrix (Fin 3) (Fin 3) R) (p : Chart) (u : Rˣ) :
    MvPolynomial (Fin 3) R := C (↑(u⁻¹) : R)*localEquation M p

theorem section_factorization
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M=0)
    (p : Chart) (u : Rˣ) (hu : (u : R)=M p.1 p.2) (i : Fin 3) :
    sectionVector M i=C (column M p u i)*localEquation M p := by
  simp only [sectionVector,localEquation,linearForm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [CycleQ2SegreLocal.unit_pivot_factorization M hM p.1 p.2 u hu i j,
    map_mul,mul_assoc]
  rfl

theorem sectionIdeal_principal
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M=0)
    (p : Chart) (u : Rˣ) (hu : (u : R)=M p.1 p.2) :
    sectionIdeal M=Ideal.span {localEquation M p} := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    rw [section_factorization M hM p u hu i]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))
  · apply Ideal.span_le.mpr
    rintro _ rfl
    exact Ideal.subset_span (Set.mem_range_self p.1)

theorem localEquation_regular (M : Matrix (Fin 3) (Fin 3) R) (p : Chart)
    (hu : IsUnit (M p.1 p.2)) : IsRegular (localEquation M p) :=
  linearForm_regular (M p.1) p.2 hu

theorem normalizedEquation_regular (M : Matrix (Fin 3) (Fin 3) R) (p : Chart)
    (u : Rˣ) (hu : (u : R)=M p.1 p.2) : IsRegular (normalizedEquation M p u) := by
  exact ((u⁻¹).isUnit.map C).isRegular.mul
    (localEquation_regular M p (hu ▸ u.isUnit))

/-- Both principal generators come from the same literal section ideal;
the displayed unit is the original image-line transition, mapped into the
section-parameter polynomial ring. -/
theorem localEquation_overlap
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M=0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R)=M p.1 p.2) (hq : (uq : R)=M q.1 q.2) :
    localEquation M q=C (transition M hM p q up uq hp hq : R)*localEquation M p := by
  simp only [localEquation,sectionVector,linearForm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [row_overlap M hM p q up uq hp hq j,map_mul,mul_assoc]

theorem normalizedEquation_overlap
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M=0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R)=M p.1 p.2) (hq : (uq : R)=M q.1 q.2) :
    normalizedEquation M q uq=
      C ((up*uq⁻¹*transition M hM p q up uq hp hq : Rˣ) : R)*
        normalizedEquation M p up := by
  rw [normalizedEquation,normalizedEquation,localEquation_overlap M hM p q up uq hp hq]
  simp only [Units.val_mul,map_mul]
  have hunit : C (up : R)*C (↑(up⁻¹) : R)=(1 : MvPolynomial (Fin 3) R) := by
    rw [←map_mul,Units.mul_inv,map_one]
  linear_combination
    -(C (↑(uq⁻¹) : R)*C (transition M hM p q up uq hp hq : R)*localEquation M p)*hunit

theorem sectionVector_map {S : Type*} [CommRing S] (f : R →+* S)
    (M : Matrix (Fin 3) (Fin 3) R) (i : Fin 3) :
    MvPolynomial.map f (sectionVector M i)=sectionVector (f.mapMatrix M) i := by
  simp only [sectionVector,linearForm,map_sum,map_mul,map_C,map_X]
  rfl

theorem normalizedEquation_transition_cocycle
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M=0)
    (p q r : Chart) (up uq ur : Rˣ)
    (hp : (up : R)=M p.1 p.2) (hq : (uq : R)=M q.1 q.2)
    (hr : (ur : R)=M r.1 r.2) :
    (up*uq⁻¹*transition M hM p q up uq hp hq)*
      (uq*ur⁻¹*transition M hM q r uq ur hq hr)=
        up*ur⁻¹*transition M hM p r up ur hp hr := by
  simpa only [twistedTransition,pow_one] using
    twistedTransition_cocycle M hM p q r up uq ur hp hq hr up uq ur 1

end CycleQ2SegreGenericSection

#print axioms CycleQ2SegreGenericSection.sectionIdeal_principal
#print axioms CycleQ2SegreGenericSection.localEquation_regular
#print axioms CycleQ2SegreGenericSection.localEquation_overlap
#print axioms CycleQ2SegreGenericSection.normalizedEquation_overlap
#print axioms CycleQ2SegreGenericSection.normalizedEquation_transition_cocycle
end
end


