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
import Proposal.GeometricTarget01

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


/- Component: continuation_3/cylinder_bridge/CechLiftRelation.lean -/
section
/-! # Linear descent for a two-stage Čech lifting relation

The simultaneous lifts form a linear submodule. Surjectivity of its first
projection and the actual boundary criterion induce an injection between
the two cohomology quotients, independently of any chosen lifts.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CechLiftRelation

variable {R P F C X G : Type*} [CommRing R]
  [AddCommGroup P] [Module R P] [AddCommGroup F] [Module R F]
  [AddCommGroup C] [Module R C] [AddCommGroup X] [Module R X]
  [AddCommGroup G] [Module R G]

variable (u : P →ₗ[R] X) (v : F →ₗ[R] X) (d : F →ₗ[R] G) (g : C →ₗ[R] G)

def lifts : Submodule R (P × F × C) where
  carrier L := v L.2.1=u L.1 ∧ d L.2.1=g L.2.2
  zero_mem' := by
    change v 0=u 0 ∧ d 0=g 0
    simp only [map_zero,and_self]
  add_mem' {L M} hL hM := by
    constructor
    · change v (L.2.1+M.2.1)=u (L.1+M.1)
      rw [map_add,map_add,hL.1,hM.1]
    · change d (L.2.1+M.2.1)=g (L.2.2+M.2.2)
      rw [map_add,map_add,hL.2,hM.2]
  smul_mem' a L hL := by
    constructor
    · change v (a • L.2.1)=u (a • L.1)
      rw [map_smul,map_smul,hL.1]
    · change d (a • L.2.1)=g (a • L.2.2)
      rw [map_smul,map_smul,hL.2]

def firstProjection : lifts u v d g →ₗ[R] P :=
  (LinearMap.fst R P (F×C)).comp (lifts u v d g).subtype

def lastProjection : lifts u v d g →ₗ[R] C :=
  (LinearMap.snd R F C).comp
    ((LinearMap.snd R P (F×C)).comp (lifts u v d g).subtype)

variable (K : Submodule R P) (H : Submodule R C)

def topClass : lifts u v d g →ₗ[R] C ⧸ H :=
  H.mkQ.comp (lastProjection u v d g)

variable (hex : ∀ p : P, ∃ f c, v f=u p ∧ d f=g c)
  (hzero : ∀ p f c, v f=u p → d f=g c → (c∈H ↔ p∈K))

include hex in
theorem firstProjection_surjective : Function.Surjective (firstProjection u v d g) := by
  intro p
  obtain ⟨f,c,hf,hc⟩ := hex p
  exact ⟨⟨(p,f,c),hf,hc⟩,rfl⟩

include hzero in
theorem ker_firstProjection_le :
    LinearMap.ker (firstProjection u v d g) ≤ LinearMap.ker (topClass u v d g H) := by
  intro L hL
  change H.mkQ L.val.2.2=0
  change (Submodule.Quotient.mk L.val.2.2 : C ⧸ H)=0
  rw [Submodule.Quotient.mk_eq_zero]
  apply (hzero L.val.1 L.val.2.1 L.val.2.2 L.property.1 L.property.2).mpr
  have hz : L.val.1=0 := hL
  rw [hz]
  exact K.zero_mem

def connecting : P →ₗ[R] C ⧸ H :=
  CycleQ2CechLinearAlgebra.descendSurjective
    (firstProjection u v d g) (topClass u v d g H)
    (ker_firstProjection_le u v d g K H hzero)
    (firstProjection_surjective u v d g hex)

theorem connecting_apply (p : P) (f : F) (c : C)
    (hf : v f=u p) (hc : d f=g c) :
    connecting u v d g K H hex hzero p=H.mkQ c := by
  exact CycleQ2CechLinearAlgebra.descendSurjective_apply
    (firstProjection u v d g) (topClass u v d g H)
    (ker_firstProjection_le u v d g K H hzero)
    (firstProjection_surjective u v d g hex) ⟨(p,f,c),hf,hc⟩

theorem ker_connecting : LinearMap.ker (connecting u v d g K H hex hzero)=K := by
  ext p
  change connecting u v d g K H hex hzero p=0 ↔ p∈K
  obtain ⟨f,c,hf,hc⟩ := hex p
  rw [connecting_apply u v d g K H hex hzero p f c hf hc]
  change (Submodule.Quotient.mk c : C ⧸ H)=0 ↔ p∈K
  rw [Submodule.Quotient.mk_eq_zero]
  exact hzero p f c hf hc

def quotientInjection : (P ⧸ K) →ₗ[R] (C ⧸ H) :=
  CycleQ2LinearRangeDescent.kernelQuotientInjection
    (connecting u v d g K H hex hzero) K (ker_connecting u v d g K H hex hzero)

theorem quotientInjection_injective :
    Function.Injective (quotientInjection u v d g K H hex hzero) :=
  CycleQ2LinearRangeDescent.kernelQuotientInjection_injective
    (connecting u v d g K H hex hzero) K (ker_connecting u v d g K H hex hzero)

end CycleQ2CechLiftRelation

#print axioms CycleQ2CechLiftRelation.quotientInjection_injective
end
end


/- Component: continuation_3/IncidenceEquations.lean -/
section
/-! # The actual coefficient equations of the Segre incidence

The matrix is centered at the literal raw seed matrix.  Coefficients of its
cofactor remainders, indexed by the complete invariant standard monomials of
degree twenty-eight, are the incidence equations.
-/

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2IncidenceEquations

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials

variable {R : Type*} [CommRing R]

abbrev Poly (R : Type*) [CommRing R] := MvPolynomial (Fin 5) R
abbrev Grade := ℕ × ZMod 3
abbrev HG (p : Poly R) (d : Grade) := p.IsWeightedHomogeneous fullGrading d

private lemma regrade {p : Poly R} {a b : Grade} (hp : HG p a) (h : a = b) : HG p b := h ▸ hp

def standardExponent {d : ℕ} (q : StandardIndex d) : FullExponent :=
  Finsupp.equivFunOnFinite.symm (coordinates q)

@[simp] lemma standardExponent_apply {d : ℕ} (q : StandardIndex d) (i : Fin 5) :
    standardExponent q i = coordinates q i := rfl

theorem standardExponent_grade {d : ℕ} (q : StandardIndex d) :
    Finsupp.weight fullGrading (standardExponent q) = (d, 0) := by
  have hq := ((exponentEquiv d 3 3) q).property
  rw [fullGrading_eq_iff]
  exact ⟨hq.2.2.1, hq.2.2.2⟩

theorem standard_eq_zero_of_coefficients {d : ℕ} {p : Poly R}
    (hs : FullStandard p) (hp : HG p (d, 0))
    (hc : ∀ q : StandardIndex d, p.coeff (standardExponent q) = 0) : p = 0 := by
  ext e
  simp only [coeff_zero]
  by_contra he
  have hs' := hs e (mem_support_iff.mpr he)
  have hd := (fullGrading_eq_iff e d).mp (hp he)
  let v : Exponents d 3 3 := ⟨e, hs'.1, hs'.2, hd.1, hd.2⟩
  let q : StandardIndex d := (exponentEquiv d 3 3).symm v
  have hq : standardExponent q = e := by
    ext i
    change coordinates q i = e i
    exact congrArg (fun z : Exponents d 3 3 ↦ z.val i)
      ((exponentEquiv d 3 3).apply_symm_apply v)
  exact he (hq ▸ hc q)

def rawSeedMatrix (r : R) : Matrix (Fin 3) (Fin 3) (Poly R) :=
  CycleQ2SegreSeed.rawMatrix (C r) (X 0) (X 1) (X 2) (X 3) (X 4)

def perturbation (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) :
    Matrix (Fin 3) (Fin 3) (Poly R) :=
  fun i j ↦ ∑ q, monomial (standardExponent q) (δ i j q)

/-- The raw seed is unchanged when the cubic and sextic parameters vary. -/
def incidenceMatrix (r : R) (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) :
    Matrix (Fin 3) (Fin 3) (Poly R) := rawSeedMatrix r + perturbation δ

@[simp] theorem incidenceMatrix_zero (r : R) :
    incidenceMatrix r (fun _ _ _ ↦ 0) = rawSeedMatrix r := by
  ext i j
  simp [incidenceMatrix, perturbation]

theorem perturbation_homogeneous
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) (i j : Fin 3) :
    HG (perturbation δ i j) (14, 0) := by
  apply (weightedHomogeneousSubmodule R fullGrading (14, 0)).sum_mem
  intro q _
  exact isWeightedHomogeneous_monomial _ _ _ (standardExponent_grade q)

private lemma hx0 : HG (X 0 : Poly R) (1, 2) := isWeightedHomogeneous_X R fullGrading 0
private lemma hx1 : HG (X 1 : Poly R) (1, 2) := isWeightedHomogeneous_X R fullGrading 1
private lemma hx2 : HG (X 2 : Poly R) (1, 1) := isWeightedHomogeneous_X R fullGrading 2
private lemma hx3 : HG (X 3 : Poly R) (1, 0) := isWeightedHomogeneous_X R fullGrading 3
private lemma hw : HG (X 4 : Poly R) (2, 0) := isWeightedHomogeneous_X R fullGrading 4

private theorem leftCoeff0_homogeneous (i : Fin 3) :
    HG (CycleQ2SegreSeed.leftCoeff0 (X 0) (X 1) (X 2) (X 3) (X 4) i : Poly R) (6, 2) := by
  fin_cases i
  · exact (regrade (((hw.pow 2).neg.mul hx1).mul hx3) (by decide)).add
      (regrade ((hx1.pow 2).mul (hx2.pow 4)) (by decide))
  · exact ((regrade (hw.neg.mul (hx1.pow 4)) (by decide)).add
      (regrade ((hx0.pow 2).mul (hx2.pow 4)) (by decide))).add
      (regrade ((hx1.mul (hx2.pow 3)).mul (hx3.pow 2)) (by decide))
  · exact ((regrade (((hw.pow 2).neg.mul hx0).mul hx3) (by decide)).add
      (regrade ((hx1.pow 4).mul (hx3.pow 2)) (by decide))).add
      (regrade ((hx2.pow 2).mul (hx3.pow 4)) (by decide))

private theorem leftCoeff1_homogeneous (i : Fin 3) :
    HG (CycleQ2SegreSeed.leftCoeff1 (X 0) (X 1) (X 2) (X 3) (X 4) i : Poly R) (4, 0) := by
  fin_cases i
  · exact (regrade ((hx0.mul hx1).mul (hx2.pow 2)) (by decide)).sub
      (regrade ((hx0.mul hx2).mul (hx3.pow 2)) (by decide))
  · exact regrade (hx3.pow 4) (by decide)
  · exact regrade (hx3.pow 4) (by decide)

private theorem rightCoeff0_homogeneous (i : Fin 3) :
    HG (CycleQ2SegreSeed.rightCoeff0 (X 0) (X 1) (X 2) (X 3) (X 4) i : Poly R) (4, 0) := by
  fin_cases i
  · change HG (2 * (X 4 : Poly R) ^ 2 + 2 * X 4 * X 3 ^ 2) (4, 0)
    have h0 : HG ((C (2 : R)) * X 4 ^ 2) (4, 0) := regrade ((hw.pow 2).C_mul 2) (by decide)
    have h1 : HG ((C (2 : R)) * X 4 * X 3 ^ 2) (4, 0) :=
      regrade ((hw.C_mul 2).mul (hx3.pow 2)) (by decide)
    simpa only [map_ofNat] using h0.add h1
  · exact (regrade ((hw.mul hx0).mul hx2) (by decide)).add
      (regrade ((hx0.pow 2).mul (hx2.pow 2)) (by decide))
  · exact (((regrade ((hx0.mul (hx1.pow 2)).mul hx3) (by decide)).add
      (regrade ((hx1.mul hx2).mul (hx3.pow 2)) (by decide))).sub
      (regrade ((hx2.pow 3).mul hx3) (by decide))).add
      (regrade (hx3.pow 4) (by decide))

private theorem rightCoeff2_homogeneous (i : Fin 3) :
    HG (CycleQ2SegreSeed.rightCoeff2 (X 0) (X 1) (X 2) (X 3) (X 4) i : Poly R) (2, 0) := by
  fin_cases i
  · exact hw.add (regrade (hx3.pow 2) (by decide))
  · exact hw
  · exact isWeightedHomogeneous_zero _ _ _

private theorem rightCoeff3_homogeneous (i : Fin 3) :
    HG (CycleQ2SegreSeed.rightCoeff3 (X 0) (X 1) (X 2) (X 3) (X 4) i : Poly R) (2, 2) := by
  fin_cases i
  · exact isWeightedHomogeneous_zero _ _ _
  · exact regrade (hx0.mul hx3) (by decide)
  · exact isWeightedHomogeneous_zero _ _ _

private theorem baseRow0_homogeneous (r : R) (j : Fin 3) :
    HG (CycleQ2SegreSeed.baseRow0 (C r) (X 0) (X 1) (X 2) (X 3) (X 4) j) (8, 1) := by
  have ha : HG (X 0 ^ 2 : Poly R) (2, 1) := regrade (hx0.pow 2) (by decide)
  have hb : HG (C r * X 1 * X 3) (2, 2) := regrade ((hx1.C_mul r).mul hx3) (by decide)
  have hd : HG (X 2 ^ 2 : Poly R) (2, 2) := regrade (hx2.pow 2) (by decide)
  have hP := (regrade (ha.mul hw) (by decide : ((2,1) : Grade)+(2,0)=(4,1))).add
    (regrade (hb.mul hd) (by decide))
  have hQ := (regrade ((ha.pow 2).mul hb) (by decide : 2 • ((2,1) : Grade)+(2,2)=(6,1))).sub
    (regrade (hw.mul (hd.pow 2)) (by decide))
  have hT := (regrade (ha.mul (hb.pow 2)) (by decide : ((2,1) : Grade)+2 • (2,2)=(6,2))).add
    (regrade ((hw.pow 2).mul hd) (by decide))
  exact ((regrade (hP.mul (rightCoeff0_homogeneous j)) (by decide)).add
    (regrade (hQ.mul (rightCoeff2_homogeneous j)) (by decide))).add
    (regrade (hT.mul (rightCoeff3_homogeneous j)) (by decide))

private theorem baseRow1_homogeneous (r : R) (j : Fin 3) :
    HG (CycleQ2SegreSeed.baseRow1 (C r) (X 0) (X 1) (X 2) (X 3) (X 4) j) (10, 0) := by
  have ha : HG (X 0 ^ 2 : Poly R) (2, 1) := regrade (hx0.pow 2) (by decide)
  have hb : HG (C r * X 1 * X 3) (2, 2) := regrade ((hx1.C_mul r).mul hx3) (by decide)
  have hd : HG (X 2 ^ 2 : Poly R) (2, 2) := regrade (hx2.pow 2) (by decide)
  have hP := (regrade (ha.pow 3) (by decide : 3 • ((2,1) : Grade)=(6,0))).sub
    (regrade (hb.pow 3) (by decide))
  have hQ := ((regrade ((ha.pow 2).neg.mul (hd.pow 2)) (by decide : 2 • ((2,1) : Grade)+2 • (2,2)=(8,0))).sub
    (regrade ((ha.mul hb).mul (hw.pow 2)) (by decide))).add
    (regrade (((hb.pow 2).mul hw).mul hd) (by decide))
  have hT := ((regrade (((ha.pow 2).mul hw).mul hd) (by decide : 2 • ((2,1) : Grade)+(2,0)+(2,2)=(8,1))).sub
    (regrade ((ha.mul hb).mul (hd.pow 2)) (by decide))).sub
    (regrade ((hb.pow 2).mul (hw.pow 2)) (by decide))
  exact ((regrade (hP.mul (rightCoeff0_homogeneous j)) (by decide)).add
    (regrade (hQ.mul (rightCoeff2_homogeneous j)) (by decide))).add
    (regrade (hT.mul (rightCoeff3_homogeneous j)) (by decide))

theorem rawSeedMatrix_homogeneous (r : R) (i j : Fin 3) :
    HG (rawSeedMatrix r i j) (14, 0) :=
  (regrade ((leftCoeff0_homogeneous i).mul (baseRow0_homogeneous r j)) (by decide)).add
    (regrade ((leftCoeff1_homogeneous i).mul (baseRow1_homogeneous r j)) (by decide))

theorem incidenceMatrix_homogeneous (r : R)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) (i j : Fin 3) :
    HG (incidenceMatrix r δ i j) (14, 0) :=
  (rawSeedMatrix_homogeneous r i j).add (perturbation_homogeneous δ i j)

theorem cofactors_homogeneous (M : Matrix (Fin 3) (Fin 3) (Poly R))
    (hM : ∀ i j, HG (M i j) (14, 0)) (i j : Fin 3) :
    HG (CycleQ2SegreLocal.cofactors M i j) (28, 0) := by
  have hprod (i j k l : Fin 3) : HG (M i j * M k l) (28, 0) :=
    regrade ((hM i j).mul (hM k l)) (by decide)
  rw [CycleQ2SegreLocal.cofactors, Matrix.adjugate_fin_three]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero',
      Matrix.cons_val_succ']
  all_goals first
  | exact (hprod _ _ _ _).sub (hprod _ _ _ _)
  | exact (hprod _ _ _ _).neg.add (hprod _ _ _ _)

abbrev EquationIndex := (Fin 3 × Fin 3) × StandardIndex 28

theorem equationIndex_count : Fintype.card EquationIndex = 9522 := by
  simp only [EquationIndex, Fintype.card_prod, Fintype.card_fin, standard_degree28_count]

def cofactorEquations [Nontrivial R]
    (hcoeff : FullInvariantIndex 3 → R) (Fcoeff : FullInvariantIndex 6 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (M : Matrix (Fin 3) (Fin 3) (Poly R)) (q : EquationIndex) : R :=
  (fullRemainder hcoeff Fcoeff hu Fu (CycleQ2SegreLocal.cofactors M q.1.1 q.1.2)).coeff
    (standardExponent q.2)

def incidenceEquations [Nontrivial R]
    (hcoeff : FullInvariantIndex 3 → R) (Fcoeff : FullInvariantIndex 6 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (r : R) (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) : EquationIndex → R :=
  cofactorEquations hcoeff Fcoeff hu Fu (incidenceMatrix r δ)

theorem cofactorEquations_zero_iff [Nontrivial R]
    (hcoeff : FullInvariantIndex 3 → R) (Fcoeff : FullInvariantIndex 6 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (M : Matrix (Fin 3) (Fin 3) (Poly R)) (hM : ∀ i j, HG (M i j) (14, 0)) :
    (∀ q, cofactorEquations hcoeff Fcoeff hu Fu M q = 0) ↔
      ∀ i j, CycleQ2SegreLocal.cofactors M i j ∈
        equationsIdeal (fullInvariantPolynomial 3 hcoeff) (fullInvariantPolynomial 6 Fcoeff) := by
  constructor
  · intro hq i j
    apply (fullRemainder_eq_zero_iff hcoeff Fcoeff hu Fu _).mp
    apply standard_eq_zero_of_coefficients
    · exact (fullRemainder_spec hcoeff Fcoeff hu Fu _).1
    · exact fullRemainder_preserves_grading hcoeff Fcoeff hu Fu (cofactors_homogeneous M hM i j)
    · intro q
      exact hq ((i,j),q)
  · intro hM q
    have hz := (fullRemainder_eq_zero_iff hcoeff Fcoeff hu Fu _).mpr (hM q.1.1 q.1.2)
    simp [cofactorEquations, hz]

theorem incidenceEquations_zero_iff [Nontrivial R]
    (hcoeff : FullInvariantIndex 3 → R) (Fcoeff : FullInvariantIndex 6 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (r : R) (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) :
    (∀ q, incidenceEquations hcoeff Fcoeff hu Fu r δ q = 0) ↔
      ∀ i j, CycleQ2SegreLocal.cofactors (incidenceMatrix r δ) i j ∈
        equationsIdeal (fullInvariantPolynomial 3 hcoeff) (fullInvariantPolynomial 6 Fcoeff) :=
  cofactorEquations_zero_iff hcoeff Fcoeff hu Fu (incidenceMatrix r δ)
    (incidenceMatrix_homogeneous r δ)

section Naturality

variable {S : Type*} [CommRing S]

theorem map_rawSeedMatrix (φ : R →+* S) (r : R) :
    (map φ).mapMatrix (rawSeedMatrix r) = rawSeedMatrix (φ r) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rawSeedMatrix, CycleQ2SegreSeed.rawMatrix,
      CycleQ2SegreSeed.leftCoeff0, CycleQ2SegreSeed.leftCoeff1,
      CycleQ2SegreSeed.baseRow0, CycleQ2SegreSeed.baseRow1,
      CycleQ2SegreSeed.coreRight0, CycleQ2SegreSeed.coreRight1,
      CycleQ2SegreSeed.rightCoeff0, CycleQ2SegreSeed.rightCoeff2,
      CycleQ2SegreSeed.rightCoeff3, RingHom.mapMatrix_apply]

theorem map_perturbation (φ : R →+* S)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) :
    (map φ).mapMatrix (perturbation δ) = perturbation (fun i j q ↦ φ (δ i j q)) := by
  ext i j
  simp [perturbation, RingHom.mapMatrix_apply]

theorem map_incidenceMatrix (φ : R →+* S) (r : R)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) :
    (map φ).mapMatrix (incidenceMatrix r δ) =
      incidenceMatrix (φ r) (fun i j q ↦ φ (δ i j q)) := by
  unfold incidenceMatrix
  rw [map_add, map_rawSeedMatrix, map_perturbation]

theorem map_cofactors (φ : R →+* S)
    (M : Matrix (Fin 3) (Fin 3) (Poly R)) (i j : Fin 3) :
    map φ (CycleQ2SegreLocal.cofactors M i j) =
      CycleQ2SegreLocal.cofactors ((map φ).mapMatrix M) i j := by
  exact congrArg (fun N : Matrix (Fin 3) (Fin 3) (Poly S) ↦ N j i)
    ((map φ).map_adjugate M)

/-- All 9522 equations commute with every coefficient specialization for which
the two leading coefficients remain units. -/
theorem cofactorEquations_map [Nontrivial R] [Nontrivial S]
    (φ : R →+* S)
    (hcoeff : FullInvariantIndex 3 → R) (Fcoeff : FullInvariantIndex 6 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (M : Matrix (Fin 3) (Fin 3) (Poly R)) (q : EquationIndex) :
    φ (cofactorEquations hcoeff Fcoeff hu Fu M q) =
      cofactorEquations (φ ∘ hcoeff) (φ ∘ Fcoeff) (hu.map φ) (Fu.map φ)
        ((map φ).mapMatrix M) q := by
  unfold cofactorEquations
  rw [← coeff_map, fullRemainder_map, map_cofactors]

theorem incidenceEquations_map [Nontrivial R] [Nontrivial S]
    (φ : R →+* S)
    (hcoeff : FullInvariantIndex 3 → R) (Fcoeff : FullInvariantIndex 6 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (r : R) (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) (q : EquationIndex) :
    φ (incidenceEquations hcoeff Fcoeff hu Fu r δ q) =
      incidenceEquations (φ ∘ hcoeff) (φ ∘ Fcoeff) (hu.map φ) (Fu.map φ)
        (φ r) (fun i j e ↦ φ (δ i j e)) q := by
  unfold incidenceEquations
  rw [cofactorEquations_map, map_incidenceMatrix]

end Naturality

/-! ## The literal smooth incidence seed

The parameter `ι` may be specialized to `Complex.I`.  The cubic used by the
incidence chart contains the additional term `x0^3`; the raw matrix itself is
exactly the published raw matrix.
-/

def smoothB : Poly R :=
  X 3 ^ 3 + X 2 ^ 3 + X 1 * X 2 * X 3 + X 0 * X 2 * X 3 +
    X 0 * X 1 ^ 2 + X 0 ^ 3

def smoothA : Poly R := X 1 ^ 3 + X 3 ^ 3
def smoothH (ι : R) : Poly R := smoothB - C ι * smoothA
def smoothK (ι : R) : Poly R := smoothB + C ι * smoothA

def seedG (r : R) : Poly R :=
  CycleQ2SegreSeed.seedG (C r) (X 0) (X 1) (X 2) (X 3) (X 4)

def smoothF (r ι : R) : Poly R := seedG r + smoothH ι * smoothK ι

theorem smoothB_homogeneous : HG (smoothB : Poly R) (3, 0) :=
  (((((regrade (hx3.pow 3) (by decide)).add
    (regrade (hx2.pow 3) (by decide))).add
    (regrade ((hx1.mul hx2).mul hx3) (by decide))).add
    (regrade ((hx0.mul hx2).mul hx3) (by decide))).add
    (regrade (hx0.mul (hx1.pow 2)) (by decide))).add
    (regrade (hx0.pow 3) (by decide))

theorem smoothA_homogeneous : HG (smoothA : Poly R) (3, 0) :=
  (regrade (hx1.pow 3) (by decide)).add (regrade (hx3.pow 3) (by decide))

theorem smoothH_homogeneous (ι : R) : HG (smoothH ι) (3, 0) :=
  smoothB_homogeneous.sub (smoothA_homogeneous.C_mul ι)

theorem smoothK_homogeneous (ι : R) : HG (smoothK ι) (3, 0) :=
  smoothB_homogeneous.add (smoothA_homogeneous.C_mul ι)

theorem seedG_homogeneous (r : R) : HG (seedG r) (6, 0) := by
  rw [seedG, CycleQ2SegreSeed.seedG_expanded]
  exact (((regrade (hx0.pow 6) (by decide)).sub
    (regrade ((((isWeightedHomogeneous_C fullGrading r).pow 3).mul
      (hx1.pow 3)).mul (hx3.pow 3)) (by decide))).add
    (regrade (hx2.pow 6) (by decide))).add (regrade (hw.pow 3) (by decide))

theorem smoothF_homogeneous (r ι : R) : HG (smoothF r ι) (6, 0) :=
  (seedG_homogeneous r).add
    (regrade ((smoothH_homogeneous ι).mul (smoothK_homogeneous ι)) (by decide))

theorem smoothH_leading_coefficient (ι : R) :
    (smoothH ι).coeff (Finsupp.single 0 3) = 1 := by
  simp only [smoothH, smoothB, smoothA, coeff_sub, coeff_add, coeff_C_mul,
    X_pow_eq_monomial]
  simp only [X, monomial_mul, coeff_monomial]
  have h3 : (Finsupp.single (3 : Fin 5) 3 : FullExponent) ≠ Finsupp.single 0 3 := by
    intro he
    have h0 := congrArg (fun e : FullExponent ↦ e 0) he
    have h30 : (3 : Fin 5) ≠ 0 := by decide
    rw [Finsupp.single_eq_of_ne' h30, Finsupp.single_eq_same] at h0
    omega
  simp only [if_neg h3]
  norm_num [Finsupp.ext_iff, Fin.forall_fin_succ]

private def wOnly : Fin 5 → ℕ := fun i ↦ if i = 4 then 1 else 0

private theorem wOnly_X (i : Fin 5) (hi : i ≠ 4) :
    (X i : Poly R).IsWeightedHomogeneous wOnly 0 := by
  simpa only [wOnly, if_neg hi] using isWeightedHomogeneous_X R wOnly i

private theorem smoothB_no_w :
    (smoothB : Poly R).IsWeightedHomogeneous wOnly 0 := by
  have h0 := wOnly_X (R := R) 0 (by decide)
  have h1 := wOnly_X (R := R) 1 (by decide)
  have h2 := wOnly_X (R := R) 2 (by decide)
  have h3 := wOnly_X (R := R) 3 (by decide)
  exact (((((h3.pow 3).add (h2.pow 3)).add ((h1.mul h2).mul h3)).add
    ((h0.mul h2).mul h3)).add (h0.mul (h1.pow 2))).add (h0.pow 3)

private theorem smoothA_no_w :
    (smoothA : Poly R).IsWeightedHomogeneous wOnly 0 :=
  ((wOnly_X 1 (by decide)).pow 3).add ((wOnly_X 3 (by decide)).pow 3)

private theorem wOnly_leading_ne :
    Finsupp.weight wOnly (Finsupp.single 4 3) ≠ 0 := by
  simp [Finsupp.weight_single, wOnly]

theorem smoothF_leading_coefficient (r ι : R) :
    (smoothF r ι).coeff (Finsupp.single 4 3) = 1 := by
  have hprod : (smoothH ι * smoothK ι).IsWeightedHomogeneous wOnly 0 :=
    (smoothB_no_w.sub (smoothA_no_w.C_mul ι)).mul
      (smoothB_no_w.add (smoothA_no_w.C_mul ι))
  have h0 := wOnly_X (R := R) 0 (by decide)
  have h1 := wOnly_X (R := R) 1 (by decide)
  have h2 := wOnly_X (R := R) 2 (by decide)
  have h3 := wOnly_X (R := R) 3 (by decide)
  have hpart : IsWeightedHomogeneous wOnly
      ((X 0 : Poly R)^6 - (C r)^3 * X 1^3 * X 3^3 + X 2^6) 0 :=
    ((h0.pow 6).sub ((((isWeightedHomogeneous_C wOnly r).pow 3).mul
      (h1.pow 3)).mul (h3.pow 3))).add (h2.pow 6)
  rw [smoothF, coeff_add, hprod.coeff_eq_zero _ wOnly_leading_ne, add_zero,
    seedG, CycleQ2SegreSeed.seedG_expanded, coeff_add,
    hpart.coeff_eq_zero _ wOnly_leading_ne, zero_add, coeff_X_pow, if_pos rfl]

def seedCubicCoefficients (ι : R) (e : FullInvariantIndex 3) : R :=
  (smoothH ι).coeff (fullExponentOf e.val)

def seedSexticCoefficients (r ι : R) (e : FullInvariantIndex 6) : R :=
  (smoothF r ι).coeff (fullExponentOf e.val)

theorem seedCubicCoefficients_polynomial (ι : R) :
    fullInvariantPolynomial 3 (seedCubicCoefficients ι) = smoothH ι :=
  fullInvariantPolynomial_of_homogeneous (smoothH_homogeneous ι)

theorem seedSexticCoefficients_polynomial (r ι : R) :
    fullInvariantPolynomial 6 (seedSexticCoefficients r ι) = smoothF r ι :=
  fullInvariantPolynomial_of_homogeneous (smoothF_homogeneous r ι)

theorem seedCubicCoefficients_unit (ι : R) :
    IsUnit (seedCubicCoefficients ι fullCubicLeadingIndex) := by
  have he := fullCubicLeadingIndex_exponent
  simpa only [seedCubicCoefficients, he, smoothH_leading_coefficient] using (isUnit_one : IsUnit (1 : R))

theorem seedSexticCoefficients_unit (r ι : R) :
    IsUnit (seedSexticCoefficients r ι fullSexticLeadingIndex) := by
  have he := fullSexticLeadingIndex_exponent
  simpa only [seedSexticCoefficients, he, smoothF_leading_coefficient] using (isUnit_one : IsUnit (1 : R))

/-- The literal cofactor factorization supplies the actual seed incidence,
without a numerical rank hypothesis or an assumed minor value. -/
theorem rawSeedMatrix_cofactor_mem (r ι : R) (i j : Fin 3) :
    CycleQ2SegreLocal.cofactors (rawSeedMatrix r) i j ∈
      equationsIdeal (smoothH ι) (smoothF r ι) := by
  have hid := congrArg (fun N : Matrix (Fin 3) (Fin 3) (Poly R) ↦ N i j)
    (CycleQ2SegreSeed.rawMatrix_cofactor_identity (C r) (X 0) (X 1) (X 2) (X 3) (X 4))
  change CycleQ2SegreLocal.cofactors (rawSeedMatrix r) i j =
    seedG r * CycleQ2SegreSeed.rawCofactorQuotient (C r) (X 0) (X 1) (X 2) (X 3) (X 4) i j at hid
  rw [hid, equationsIdeal, Ideal.mem_span_pair]
  let Q : Poly R := CycleQ2SegreSeed.rawCofactorQuotient (C r) (X 0) (X 1) (X 2) (X 3) (X 4) i j
  refine ⟨-(smoothK ι * Q), Q, ?_⟩
  dsimp [smoothF]
  ring

theorem smoothSeed_equations_zero [Nontrivial R] (r ι : R) (q : EquationIndex) :
    incidenceEquations (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
      (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι)
      r (fun _ _ _ ↦ 0) q = 0 := by
  apply (incidenceEquations_zero_iff _ _ _ _ r (fun _ _ _ ↦ 0)).mpr _ q
  intro i j
  rw [incidenceMatrix_zero, seedCubicCoefficients_polynomial, seedSexticCoefficients_polynomial]
  exact rawSeedMatrix_cofactor_mem r ι i j

theorem complexSmoothSeed_equations_zero (r : ℂ) (q : EquationIndex) :
    incidenceEquations (seedCubicCoefficients Complex.I) (seedSexticCoefficients r Complex.I)
      (seedCubicCoefficients_unit Complex.I) (seedSexticCoefficients_unit r Complex.I)
      r (fun _ _ _ ↦ 0) q = 0 :=
  smoothSeed_equations_zero r Complex.I q

end CycleQ2IncidenceEquations

#print axioms CycleQ2IncidenceEquations.incidenceEquations_zero_iff
#print axioms CycleQ2IncidenceEquations.incidenceEquations_map
#print axioms CycleQ2IncidenceEquations.complexSmoothSeed_equations_zero
end
end


/- Component: continuation_3/PointedOpenLifting.lean -/
section
/-! A generic solution on a prescribed polynomial open, chosen on a
component through the actual nonsingular seed.  The field quotient and
coordinates are those of the same Jacobian-localized open-square system
used by the original lifting construction. -/

noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2PointedOpenLifting

open MvPolynomial HoldoutConstruction CycleQ2OpenSquareLifting
  CycleQ2PointedSquareGeneric

variable {R K T ι : Type*} [CommRing R] [IsDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field T] [Algebra R T] [Fintype ι] [DecidableEq ι]

theorem square_system_pointed_lift_on_open
    (e : ι → MvPolynomial ι R) (c : MvPolynomial ι R)
    (seed : ι → T) (he : ∀i,aeval seed (e i)=0)
    (hj : IsUnit (Matrix.det (fun i j => aeval seed (pderiv i (e j)))))
    (hc : IsUnit (aeval seed c)) :
    ∃ I : Ideal (SquareGenericAlgebra K (openSystem e c)), I.IsMaximal ∧
      Module.Finite K ((SquareGenericAlgebra K (openSystem e c)) ⧸ I) ∧
      Algebra.IsSeparable K ((SquareGenericAlgebra K (openSystem e c)) ⧸ I) ∧
      ∃ x : ι → ((SquareGenericAlgebra K (openSystem e c)) ⧸ I),
        (∀i,aeval x (e i)=0) ∧ IsUnit (aeval x c) ∧
        (∀p : MvPolynomial ι R,aeval x p=0 → aeval seed p=0) := by
  obtain ⟨u,hu⟩ := hc.exists_left_inv
  have haug := openSystem_seed e c seed u he hu
  have hjaug : IsUnit (Matrix.det (fun i j =>
      aeval (extendedPoint seed u) (pderiv i (openSystem e c j)))) := by
    rw [openSystem_jacobian_det]
    exact hc.mul hj
  obtain ⟨I,hmax,hfin,hsep,hpoint,hsol,hjac,hspecializes⟩ :=
    exists_pointed_square_fieldFactor (K := K) (openSystem e c)
      (extendedPoint seed u) haug hjaug
  let z := squareGenericCoordinates (openSystem e c) I
  let x : ι → ((SquareGenericAlgebra K (openSystem e c)) ⧸ I) :=
    fun i => z (Sum.inr i)
  have hx := solution_on_open e c z hsol
  refine ⟨I,hmax,hfin,hsep,x,hx.1,hx.2,?_⟩
  intro p hp
  have hp' : aeval z (rename (Sum.inr : ι → Unit ⊕ ι) p)=0 := by
    rw [aeval_rename]
    exact hp
  have hs := hspecializes (rename (Sum.inr : ι → Unit ⊕ ι) p) hp'
  rwa [aeval_extended_rename] at hs

end CycleQ2PointedOpenLifting

#print axioms CycleQ2PointedOpenLifting.square_system_pointed_lift_on_open
end
end


/- Component: continuation_3/cylinder_bridge/PolynomialImplicitTrace.lean -/
section
/-! The implicit trace numerator is a literal polynomial in the original
parameters.  At a compatible seed and a trace-one kernel direction it has
value one.  On a genuine differentiated solution, its being a unit forces
the fixed linear trace of that derivative to be a unit. -/

noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2PolynomialImplicitTrace
open Matrix MvPolynomial CycleQ2PolynomialAffineSlice
  CycleQ2PolynomialDerivationChainRule CycleQ2ImplicitTraceNumerator

variable {R S σ m ι : Type*} [CommRing R] [CommRing S]
  [Fintype σ] [Fintype m] [Fintype ι] [DecidableEq ι]

def polynomialJacobian (e : m → MvPolynomial σ R) : Matrix m σ (MvPolynomial σ R) :=
  fun q k => pderiv k (e q)

def retainedJacobian (P : Matrix ι m R) (B : Matrix σ ι R)
    (e : m → MvPolynomial σ R) : Matrix ι ι (MvPolynomial σ R) :=
  P.map C * polynomialJacobian e * B.map C

def directionDerivative (P : Matrix ι m R) (direction : σ → R)
    (e : m → MvPolynomial σ R) : ι → MvPolynomial σ R :=
  (P.map C * polynomialJacobian e) *ᵥ (C ∘ direction)

def tracePolynomial (P : Matrix ι m R) (B : Matrix σ ι R)
    (e : m → MvPolynomial σ R) (weights direction : σ → R) : MvPolynomial σ R :=
  traceNumerator (retainedJacobian P B e) (directionDerivative P direction e)
    (C ∘ weights) (C ∘ direction) (B.map C)

theorem eval_polynomialJacobian (φ : R →+* S) (x : σ → S)
    (e : m → MvPolynomial σ R) :
    (polynomialJacobian e).map (eval₂Hom φ x)=jacobian φ x e := rfl

theorem eval_retainedJacobian (φ : R →+* S) (x : σ → S)
    (P : Matrix ι m R) (B : Matrix σ ι R) (e : m → MvPolynomial σ R) :
    (retainedJacobian P B e).map (eval₂Hom φ x)=
      P.map φ * jacobian φ x e * B.map φ := by
  simp only [retainedJacobian,Matrix.map_mul,eval_polynomialJacobian,Matrix.map_map,
    Function.comp_def,eval₂Hom_C]

theorem eval_directionDerivative (φ : R →+* S) (x : σ → S)
    (P : Matrix ι m R) (direction : σ → R) (e : m → MvPolynomial σ R) :
    (eval₂Hom φ x) ∘ directionDerivative P direction e =
      (P.map φ * jacobian φ x e) *ᵥ (φ ∘ direction) := by
  funext i
  simp only [directionDerivative,Function.comp_apply,RingHom.map_mulVec,
    Matrix.map_mul,eval_polynomialJacobian,Matrix.map_map,Function.comp_def,eval₂Hom_C]

theorem eval_tracePolynomial (φ : R →+* S) (x : σ → S)
    (P : Matrix ι m R) (B : Matrix σ ι R) (e : m → MvPolynomial σ R)
    (weights direction : σ → R) :
    eval₂Hom φ x (tracePolynomial P B e weights direction) =
      traceNumerator (P.map φ * jacobian φ x e * B.map φ)
        ((P.map φ * jacobian φ x e) *ᵥ (φ ∘ direction))
        (φ ∘ weights) (φ ∘ direction) (B.map φ) := by
  rw [tracePolynomial,traceNumerator_map,eval_retainedJacobian,eval_directionDerivative]
  simp only [Function.comp_def,eval₂Hom_C,Matrix.map_map]

theorem seed_tracePolynomial_one (φ : R →+* S) (x : σ → S)
    (P : Matrix ι m R) (B : Matrix σ ι R) (e : m → MvPolynomial σ R)
    (weights direction : σ → R)
    (hJ : P.map φ * jacobian φ x e * B.map φ=1)
    (hkernel : jacobian φ x e *ᵥ (φ ∘ direction)=0)
    (htrace : (φ ∘ weights) ⬝ᵥ (φ ∘ direction)=1) :
    eval₂Hom φ x (tracePolynomial P B e weights direction)=1 := by
  rw [eval_tracePolynomial,hJ,← mulVec_mulVec,hkernel,mulVec_zero]
  exact traceNumerator_seed _ _ _ htrace

theorem derivative_trace_isUnit [Algebra R S]
    (D : Derivation R S S) (x : σ → S) (z : ι → S)
    (P : Matrix ι m R) (B : Matrix σ ι R) (e : m → MvPolynomial σ R)
    (weights direction : σ → R)
    (he : ∀ q, aeval x (e q)=0)
    (hder : ∀ k, D (x k)=algebraMap R S (direction k)+
      (B.map (algebraMap R S) *ᵥ (fun j => D (z j))) k)
    (hN : IsUnit (aeval x (tracePolynomial P B e weights direction))) :
    IsUnit ((algebraMap R S ∘ weights) ⬝ᵥ (fun k => D (x k))) := by
  have hu := implicit_derivative_relation D x z P B ((algebraMap R S) ∘ direction) e he hder
  change IsUnit (eval₂Hom (algebraMap R S) x (tracePolynomial P B e weights direction)) at hN
  rw [eval_tracePolynomial] at hN
  have ht := trace_isUnit_of_numerator_isUnit
    (P.map (algebraMap R S) * jacobian (algebraMap R S) x e * B.map (algebraMap R S))
    ((P.map (algebraMap R S) * jacobian (algebraMap R S) x e) *ᵥ ((algebraMap R S) ∘ direction))
    (fun j => D (z j)) ((algebraMap R S) ∘ weights) ((algebraMap R S) ∘ direction)
    (B.map (algebraMap R S)) hu hN
  have hx : (fun k => D (x k))=((algebraMap R S) ∘ direction)+
      B.map (algebraMap R S) *ᵥ (fun j => D (z j)) := funext hder
  rw [hx]
  exact ht

end CycleQ2PolynomialImplicitTrace

#print axioms CycleQ2PolynomialImplicitTrace.seed_tracePolynomial_one
#print axioms CycleQ2PolynomialImplicitTrace.derivative_trace_isUnit
end
end


/- Component: continuation_3/cylinder_bridge/SeedCechFractions.lean -/
section
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedCech
open MvPolynomial CycleQ2SeedTrace

def powerCoordinates (r : ℂ) (e : Bool) : Fin 4 → PowerChart r e :=
  ![x0 (PowerSeries.C r) (PowerSeries.C Complex.I) (endpointX e) (endpointY e),
    base (PowerSeries.C r) (PowerSeries.C Complex.I) (endpointX e) (endpointY e) (endpointX e),
    x2 (PowerSeries.C r) (PowerSeries.C Complex.I) (endpointX e) (endpointY e),
    base (PowerSeries.C r) (PowerSeries.C Complex.I) (endpointX e) (endpointY e) (endpointY e)]

def powerEval (r : ℂ) (e : Bool) : Poly →+* PowerChart r e :=
  MvPolynomial.eval₂Hom
    ((base (PowerSeries.C r) (PowerSeries.C Complex.I)
      (endpointX e) (endpointY e)).comp PowerSeries.C)
    (powerCoordinates r e)

def laurentEval (r : ℂ) (e : Bool) : Poly →+* LaurentChart r e :=
  (chartEmbedding r e).comp (powerEval r e)

@[simp] theorem powerCoordinates_zero (r : ℂ) (e : Bool) :
    powerCoordinates r e 0 = x0 (PowerSeries.C r) (PowerSeries.C Complex.I)
      (endpointX e) (endpointY e) := rfl
@[simp] theorem powerCoordinates_one (r : ℂ) (e : Bool) :
    powerCoordinates r e 1 = base (PowerSeries.C r) (PowerSeries.C Complex.I)
      (endpointX e) (endpointY e) (endpointX e) := rfl
@[simp] theorem powerCoordinates_two (r : ℂ) (e : Bool) :
    powerCoordinates r e 2 = x2 (PowerSeries.C r) (PowerSeries.C Complex.I)
      (endpointX e) (endpointY e) := rfl
@[simp] theorem powerCoordinates_three (r : ℂ) (e : Bool) :
    powerCoordinates r e 3 = base (PowerSeries.C r) (PowerSeries.C Complex.I)
      (endpointX e) (endpointY e) (endpointY e) := rfl

@[simp] theorem powerEval_X (r : ℂ) (e : Bool) (j : Fin 4) :
    powerEval r e (X j) = powerCoordinates r e j := by simp [powerEval]

@[simp] theorem powerEval_C (r : ℂ) (e : Bool) (c : ℂ) :
    powerEval r e (C c) = base (PowerSeries.C r) (PowerSeries.C Complex.I)
      (endpointX e) (endpointY e) (PowerSeries.C c) := by simp [powerEval]

theorem powerEval_curveF1 (r : ℂ) (e : Bool) : powerEval r e (curveF1 r) = 0 := by
  simp only [curveF1, relation, Matrix.cons_val_zero, map_sub, map_mul, map_pow,
    powerEval_X, powerEval_C, powerCoordinates_zero, powerCoordinates_one, powerCoordinates_three]
  rw [x0_sq, sub_eq_zero]
  simp [map_mul]

theorem powerEval_curveH (r : ℂ) (e : Bool) : powerEval r e curveH = 0 := by
  have h2 := x2_cubic (PowerSeries.C r) (PowerSeries.C Complex.I)
    (endpointX e) (endpointY e)
  simp only [map_sub, map_mul, map_pow, map_one] at h2
  simp only [curveH, h, b, map_sub, map_add, map_mul, map_pow,
    powerEval_X, powerEval_C, powerCoordinates_zero, powerCoordinates_one,
    powerCoordinates_two, powerCoordinates_three]
  linear_combination h2

theorem powerEval_zero_of_curveIdeal (r : ℂ) (e : Bool) {p : Poly}
    (hp : p ∈ curveIdeal r) : powerEval r e p = 0 := by
  obtain ⟨u,v,hp⟩ := Ideal.mem_span_pair.mp hp
  rw [← hp, map_add, map_mul, map_mul, powerEval_curveF1, powerEval_curveH]
  ring

theorem laurentEval_zero_of_curveIdeal (r : ℂ) (e : Bool) {p : Poly}
    (hp : p ∈ curveIdeal r) : laurentEval r e p = 0 := by
  change chartEmbedding r e (powerEval r e p) = 0
  rw [powerEval_zero_of_curveIdeal r e hp, map_zero]

def curveA : Poly := X 1 * X 3
def curveB : Poly := X 2

theorem uniformizer_ne_zero : seriesMap (PowerSeries.X : PS) ≠ 0 := by
  intro hh
  have hc := congrArg (fun f : LS => f.coeff 1) hh
  simpa [seriesMap, HahnSeries.ofPowerSeries_X] using hc

def uniformizerUnit : LSˣ := Units.mk0 _ uniformizer_ne_zero

def chartAUnit (r : ℂ) (e : Bool) : (LaurentChart r e)ˣ :=
  Units.map (base (seriesMap (PowerSeries.C r)) (seriesMap (PowerSeries.C Complex.I))
    (seriesMap (endpointX e)) (seriesMap (endpointY e))) uniformizerUnit

theorem laurentEval_curveA (r : ℂ) (e : Bool) :
    laurentEval r e curveA = (chartAUnit r e : LaurentChart r e) := by
  have hp : powerEval r e curveA = base (PowerSeries.C r) (PowerSeries.C Complex.I)
      (endpointX e) (endpointY e) PowerSeries.X := by
    simp only [curveA, map_mul, powerEval_X, powerCoordinates_one, powerCoordinates_three]
    rw [← map_mul]
    congr 1
    cases e <;> simp [endpointX, endpointY]
  change chartEmbedding r e (powerEval r e curveA) = _
  rw [hp]
  exact curveMap_base seriesMap _ _ _ _ _

theorem laurentEval_curveB (r : ℂ) (e : Bool) :
    laurentEval r e curveB = (laurentX2Unit r e : LaurentChart r e) := by
  change chartEmbedding r e (powerEval r e (X 2)) =
    chartEmbedding r e (powerX2Unit r e : PowerChart r e)
  congr 1
  simp only [powerEval_X, powerCoordinates_two, powerX2Unit, coe_x2Unit]

def fraction (r : ℂ) (e : Bool) (p : Poly) (n m : ℕ) : LaurentChart r e :=
  laurentEval r e p * ((chartAUnit r e)⁻¹ : (LaurentChart r e)ˣ) ^ n *
    ((laurentX2Unit r e)⁻¹ : (LaurentChart r e)ˣ) ^ m

def fractionResidue (r : ℂ) (e : Bool) (p : Poly) (n m : ℕ) : ℂ :=
  endpointResidue r e (fraction r e p n m)

def cechResidue (r : ℂ) (p : Poly) (n m : ℕ) : ℂ :=
  fractionResidue r false p n m - fractionResidue r true p n m

theorem fraction_add (r : ℂ) (e : Bool) (p q : Poly) (n m : ℕ) :
    fraction r e (p+q) n m = fraction r e p n m + fraction r e q n m := by
  simp [fraction, add_mul]

theorem fraction_sub (r : ℂ) (e : Bool) (p q : Poly) (n m : ℕ) :
    fraction r e (p-q) n m = fraction r e p n m - fraction r e q n m := by
  simp [fraction, sub_mul]

theorem cechResidue_add (r : ℂ) (p q : Poly) (n m : ℕ) :
    cechResidue r (p+q) n m = cechResidue r p n m + cechResidue r q n m := by
  simp only [cechResidue, fractionResidue, fraction_add, map_add]
  ring

theorem unit_pow_cancel {A : Type*} [CommRing A] (u : Aˣ) (n N : ℕ) (hn : n ≤ N) :
    (u : A) ^ (N-n) * ((u⁻¹ : Aˣ) : A) ^ N = ((u⁻¹ : Aˣ) : A) ^ n := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_sub_cancel_left, pow_add]
  calc
    _ = ((u : A) * ((u⁻¹ : Aˣ) : A)) ^ k * ((u⁻¹ : Aˣ) : A) ^ n := by
      rw [mul_pow]
      ring
    _ = _ := by simp

theorem fraction_change_denominator (r : ℂ) (e : Bool) (p : Poly)
    (n m N M : ℕ) (hn : n ≤ N) (hm : m ≤ M) :
    fraction r e (p * curveA ^ (N-n) * curveB ^ (M-m)) N M =
      fraction r e p n m := by
  unfold fraction
  simp only [map_mul, map_pow, laurentEval_curveA, laurentEval_curveB]
  calc
    _ = laurentEval r e p *
        (((chartAUnit r e : (LaurentChart r e)ˣ) : LaurentChart r e) ^ (N-n) *
          (((chartAUnit r e)⁻¹ : (LaurentChart r e)ˣ) : LaurentChart r e) ^ N) *
        (((laurentX2Unit r e : (LaurentChart r e)ˣ) : LaurentChart r e) ^ (M-m) *
          (((laurentX2Unit r e)⁻¹ : (LaurentChart r e)ˣ) : LaurentChart r e) ^ M) := by ring
    _ = _ := by rw [unit_pow_cancel _ n N hn, unit_pow_cancel _ m M hm]

theorem fraction_first_open_term (r : ℂ) (e : Bool) (p : Poly) (N M : ℕ) :
    fraction r e (p * curveA^N) N M = fraction r e p 0 M := by
  simpa using fraction_change_denominator r e p 0 M N M (Nat.zero_le _) le_rfl

theorem fraction_second_open_term (r : ℂ) (e : Bool) (p : Poly) (N M : ℕ) :
    fraction r e (p * curveB^M) N M = fraction r e p N 0 := by
  simpa using fraction_change_denominator r e p N 0 N M le_rfl (Nat.zero_le _)

theorem fractionResidue_x2_open (r : ℂ) (e : Bool) (p : Poly) (m : ℕ) :
    fractionResidue r e p 0 m = 0 := by
  simpa [fractionResidue, fraction, laurentEval] using
    endpointResidue_x2_open r e (powerEval r e p) m

theorem cechResidue_x2_open (r : ℂ) (p : Poly) (m : ℕ) : cechResidue r p 0 m = 0 := by
  simp [cechResidue, fractionResidue_x2_open]

theorem fraction_zero_of_curveIdeal (r : ℂ) (e : Bool) {p : Poly}
    (hp : p ∈ curveIdeal r) (n m : ℕ) : fraction r e p n m = 0 := by
  simp [fraction, laurentEval_zero_of_curveIdeal r e hp]

/-- Exact denominator-clearing definition of the degree-one Čech coboundaries
for the cover D₊(x₁x₃), D₊(x₂) of the projective sparse curve.  The two numerator
degrees enforce sections of its canonical bundle O(1). -/
def CechBoundary (r : ℂ) (p : Poly) (n m : ℕ) : Prop :=
  ∃ N M q s, n ≤ N ∧ m ≤ M ∧ q.IsHomogeneous (M + 1) ∧
    s.IsHomogeneous (2 * N + 1) ∧
    p * curveA ^ (N - n) * curveB ^ (M - m) -
      (q * curveA ^ N + s * curveB ^ M) ∈ curveIdeal r

/-- Clearing arbitrary powers gives exactly the same two endpoint values as
the sum of the two single-open cochains. -/
theorem fraction_of_boundary_witness (r : ℂ) (e : Bool) (p q s : Poly)
    (n m N M : ℕ) (hn : n ≤ N) (hm : m ≤ M)
    (hmem : p * curveA^(N-n) * curveB^(M-m) -
      (q * curveA^N + s * curveB^M) ∈ curveIdeal r) :
    fraction r e p n m = fraction r e q 0 M + fraction r e s N 0 := by
  have hz := fraction_zero_of_curveIdeal r e hmem N M
  rw [fraction_sub, fraction_add, fraction_change_denominator r e p n m N M hn hm,
    fraction_first_open_term, fraction_second_open_term, sub_eq_zero] at hz
  exact hz

end CycleQ2SeedCech
end
end


/- Component: continuation_3/cylinder_bridge/SeedCechGeneralCubic.lean -/
section
/-! A monic cubic over the actual quadratic curve algebra, allowing an
arbitrary coefficient of x₀ in the constant term.  This covers the whole
family h+θx₀³ after reduction modulo x₀²-rx₁x₃. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace CycleQ2CechLinearCubic
open Polynomial CycleQ2SeedCech
variable {R S : Type*} [CommRing R] [CommRing S]

def cubic (r i x y q : R) : (Quadratic r x y)[X] :=
  X ^ 3 + C ((a r x y + algebraMap R _ x) * algebraMap R _ y) * X +
    C (a r x y * algebraMap R _ q +
      algebraMap R _ ((1 - i) * y ^ 3 - i * x ^ 3))

theorem cubic_monic (r i x y q : R) : (cubic r i x y q).Monic := by
  unfold cubic
  rw [add_assoc]
  apply monic_X_pow_add
  apply lt_of_le_of_lt (degree_add_le _ _)
  apply max_lt
  · apply lt_of_le_of_lt (degree_mul_le _ _)
    calc
      _ ≤ 0 + 1 := add_le_add degree_C_le degree_X_le
      _ < (3 : WithBot ℕ) := by norm_num
  · exact lt_of_le_of_lt degree_C_le (by norm_num)

abbrev CurveAlgebra (r i x y q : R) := AdjoinRoot (cubic r i x y q)

def x0 (r i x y q : R) : CurveAlgebra r i x y q :=
  algebraMap (Quadratic r x y) _ (a r x y)

def x2 (r i x y q : R) : CurveAlgebra r i x y q := AdjoinRoot.root _

def base (r i x y q : R) : R →+* CurveAlgebra r i x y q :=
  (algebraMap (Quadratic r x y) _).comp (algebraMap R _)

theorem x0_sq (r i x y q : R) : x0 r i x y q ^ 2 = base r i x y q (r * x * y) := by
  rw [x0, ← map_pow, a_sq]
  rfl

theorem x2_cubic (r i x y q : R) :
    x2 r i x y q ^ 3 + (x0 r i x y q + base r i x y q x) *
        base r i x y q y * x2 r i x y q +
      x0 r i x y q * base r i x y q q +
        base r i x y q ((1 - i) * y ^ 3 - i * x ^ 3) = 0 := by
  have hh := AdjoinRoot.mk_self (f := cubic r i x y q)
  change AdjoinRoot.mk (cubic r i x y q)
    (X ^ 3 + C ((a r x y + algebraMap R _ x) * algebraMap R _ y) * X +
      C (a r x y * algebraMap R _ q +
        algebraMap R _ ((1 - i) * y ^ 3 - i * x ^ 3))) = 0 at hh
  simp only [map_add, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at hh
  simpa only [x0, x2, base, RingHom.comp_apply, AdjoinRoot.algebraMap_eq,
    map_pow, add_assoc] using hh

def coefficient (r i x y q : R) : CurveAlgebra r i x y q →ₗ[R] R :=
  (Polynomial.lcoeff R 1).comp
    ((AdjoinRoot.modByMonicHom (quadratic_monic r x y)).comp
      (((Polynomial.lcoeff (Quadratic r x y) 2).comp
        (AdjoinRoot.modByMonicHom (cubic_monic r i x y q))).restrictScalars R))

theorem cubic_map (f : R →+* S) (r i x y q : R) :
    (cubic r i x y q).map (quadraticMap f r x y) =
      cubic (f r) (f i) (f x) (f y) (f q) := by
  simp [cubic]

def curveMap (f : R →+* S) (r i x y q : R) :
    CurveAlgebra r i x y q →+* CurveAlgebra (f r) (f i) (f x) (f y) (f q) :=
  AdjoinRoot.map (quadraticMap f r x y) _ _
    (by rw [cubic_map])

@[simp] theorem curveMap_x0 (f : R →+* S) (r i x y q : R) :
    curveMap f r i x y q (x0 r i x y q) = x0 (f r) (f i) (f x) (f y) (f q) := by
  simp [curveMap, x0, AdjoinRoot.algebraMap_eq]

@[simp] theorem curveMap_x2 (f : R →+* S) (r i x y q : R) :
    curveMap f r i x y q (x2 r i x y q) = x2 (f r) (f i) (f x) (f y) (f q) := by
  simp [curveMap, x2]

@[simp] theorem curveMap_base (f : R →+* S) (r i x y q z : R) :
    curveMap f r i x y q (base r i x y q z) = base (f r) (f i) (f x) (f y) (f q) (f z) := by
  simp [curveMap, base, AdjoinRoot.algebraMap_eq]

@[simp] theorem coefficient_curveMap (f : R →+* S) (r i x y q : R)
    (z : CurveAlgebra r i x y q) :
    coefficient (f r) (f i) (f x) (f y) (f q) (curveMap f r i x y q z) =
      f (coefficient r i x y q z) := by
  change ((AdjoinRoot.modByMonicHom (quadratic_monic (f r) (f x) (f y)))
    (((AdjoinRoot.modByMonicHom (cubic_monic (f r) (f i) (f x) (f y) (f q)))
      (curveMap f r i x y q z)).coeff 2)).coeff 1 =
    f (((AdjoinRoot.modByMonicHom (quadratic_monic r x y))
      (((AdjoinRoot.modByMonicHom (cubic_monic r i x y q)) z).coeff 2)).coeff 1)
  rw [show (AdjoinRoot.modByMonicHom (cubic_monic (f r) (f i) (f x) (f y) (f q)))
      (curveMap f r i x y q z) =
      ((AdjoinRoot.modByMonicHom (cubic_monic r i x y q)) z).map
        (quadraticMap f r x y) from
    modByMonicHom_map_eq _ _ _ (cubic_monic r i x y q)
      (cubic_monic (f r) (f i) (f x) (f y) (f q)) (cubic_map f r i x y q) z]
  rw [coeff_map]
  rw [show (AdjoinRoot.modByMonicHom (quadratic_monic (f r) (f x) (f y)))
      (quadraticMap f r x y
        (((AdjoinRoot.modByMonicHom (cubic_monic r i x y q)) z).coeff 2)) =
      ((AdjoinRoot.modByMonicHom (quadratic_monic r x y))
        (((AdjoinRoot.modByMonicHom (cubic_monic r i x y q)) z).coeff 2)).map f from
    modByMonicHom_map_eq _ _ _ (quadratic_monic r x y)
      (quadratic_monic (f r) (f x) (f y)) (quadratic_map f r x y) _]
  rw [coeff_map]

def norm (r i x y q : R) : R :=
  ((1 - i) * y ^ 3 - i * x ^ 3) ^ 2 - r * x * y * q ^ 2

def inverseNumerator (r i x y q : R) : CurveAlgebra r i x y q :=
  -(x2 r i x y q ^ 2 + (x0 r i x y q + base r i x y q x) * base r i x y q y) *
    (base r i x y q ((1 - i) * y ^ 3 - i * x ^ 3) -
      x0 r i x y q * base r i x y q q)

/-- An explicit inverse numerator for x₂; no irreducibility or smoothness is
needed.  The only scalar denominator is the displayed binary sextic. -/
theorem x2_mul_inverseNumerator (r i x y q : R) :
    x2 r i x y q * inverseNumerator r i x y q = base r i x y q (norm r i x y q) := by
  have h0 := x0_sq r i x y q
  have h2 := x2_cubic r i x y q
  simp only [map_sub, map_mul, map_pow, map_one] at h0 h2 ⊢
  unfold inverseNumerator norm
  simp only [map_sub, map_mul, map_pow, map_one]
  linear_combination
    -((1 - base r i x y q i) * base r i x y q y ^ 3 -
      base r i x y q i * base r i x y q x ^ 3 -
      x0 r i x y q * base r i x y q q) * h2 -
    base r i x y q q ^ 2 * h0

def x2Unit (r i x y q : R) (u : Rˣ) (hu : (u : R) = norm r i x y q) :
    (CurveAlgebra r i x y q)ˣ where
  val := x2 r i x y q
  inv := inverseNumerator r i x y q * base r i x y q (↑(u⁻¹) : R)
  val_inv := by
    rw [← mul_assoc, x2_mul_inverseNumerator, ← hu, ← map_mul]
    simp
  inv_val := by
    rw [mul_comm, ← mul_assoc, x2_mul_inverseNumerator, ← hu, ← map_mul]
    simp

@[simp] theorem coe_x2Unit (r i x y q : R) (u : Rˣ) (hu : (u : R) = norm r i x y q) :
    (x2Unit r i x y q u hu : CurveAlgebra r i x y q) = x2 r i x y q := rfl

variable [Nontrivial R]

theorem cubic_degree (r i x y q : R) : (cubic r i x y q).degree = 3 := by
  unfold cubic
  rw [add_assoc]
  have hl : (C ((a r x y + algebraMap R _ x) * algebraMap R _ y) * X +
    C (a r x y * algebraMap R _ q +
      algebraMap R _ ((1 - i) * y ^ 3 - i * x ^ 3))).degree < 3 := by
    apply lt_of_le_of_lt (degree_add_le _ _)
    apply max_lt
    · exact lt_of_le_of_lt (degree_C_mul_X_le _) (by norm_num)
    · exact lt_of_le_of_lt degree_C_le (by norm_num)
  rw [degree_add_eq_left_of_degree_lt (by simpa using hl)]
  simp

theorem coefficient_small_monomial (r i x y q z : R) (j k : ℕ)
    (hj : j < 2) (hk : k < 3) :
    coefficient r i x y q (base r i x y q z * x0 r i x y q ^ j * x2 r i x y q ^ k) =
      if j = 1 ∧ k = 2 then z else 0 := by
  have hc : AdjoinRoot.modByMonicHom (cubic_monic r i x y q)
      (base r i x y q z * x0 r i x y q ^ j * x2 r i x y q ^ k) =
      C (algebraMap R (Quadratic r x y) z * a r x y ^ j) * X ^ k := by
    have heq : base r i x y q z * x0 r i x y q ^ j * x2 r i x y q ^ k =
        AdjoinRoot.mk (cubic r i x y q)
          (C (algebraMap R (Quadratic r x y) z * a r x y ^ j) * X ^ k) := by
      simp [base, x0, x2, AdjoinRoot.algebraMap_eq]
    rw [heq, AdjoinRoot.modByMonicHom_mk]
    apply (modByMonic_eq_self_iff (cubic_monic r i x y q)).mpr
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
    (((AdjoinRoot.modByMonicHom (cubic_monic r i x y q))
      (base r i x y q z * x0 r i x y q ^ j * x2 r i x y q ^ k)).coeff 2)).coeff 1 = _
  rw [hc]
  simp only [coeff_C_mul_X_pow]
  by_cases hk2 : k = 2
  · subst k
    simp only [ite_true, hq, coeff_C_mul_X_pow]
    simp [eq_comm]
  · simp [hk2, eq_comm]

theorem coefficient_base_mul (r i x y q z : R) (v : CurveAlgebra r i x y q) :
    coefficient r i x y q (base r i x y q z * v) = z * coefficient r i x y q v := by
  unfold base
  rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply R
    (Quadratic r x y) (CurveAlgebra r i x y q)]
  simpa only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply] using
    (coefficient r i x y q).map_smul z v

end CycleQ2CechLinearCubic

#print axioms CycleQ2CechLinearCubic.x2_mul_inverseNumerator
#print axioms CycleQ2CechLinearCubic.coefficient_small_monomial
end
end


/- Component: continuation_3/cylinder_bridge/SeedCechJets.lean -/
section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

set_option maxRecDepth 10000

namespace CycleQ2SeedCech
open TrivSqZeroExt

abbrev Jet := TrivSqZeroExt ℂ ℂ

def firstJet : PS →+* Jet where
  toFun f := (PowerSeries.constantCoeff f, PowerSeries.coeff 1 f)
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' f g := by apply TrivSqZeroExt.ext <;> simp
  map_mul' f g := by
    apply TrivSqZeroExt.ext
    · simp
    · simp [PowerSeries.coeff_one_mul, smul_eq_mul, op_smul_eq_smul]
      ring

@[simp] theorem firstJet_fst (f : PS) : (firstJet f).fst = PowerSeries.constantCoeff f := rfl
@[simp] theorem firstJet_snd (f : PS) : (firstJet f).snd = PowerSeries.coeff 1 f := rfl

theorem firstJet_X_sq : firstJet (PowerSeries.X : PS) ^ 2 = 0 := by
  apply TrivSqZeroExt.ext <;> simp [firstJet, pow_two, smul_eq_mul, op_smul_eq_smul]

theorem firstJet_I_sq : firstJet (PowerSeries.C Complex.I) ^ 2 = -1 := by
  rw [← map_pow, ← map_pow, Complex.I_sq, map_neg, map_one, map_neg, map_one]

/-- The finite second-order identity used to normalize the actual Čech
residue.  It is an identity in every commutative ring with the displayed four
relations; all coefficients are checked by `linear_combination`. -/
theorem inverse_fourth_jet_identity {A : Type*} [CommRing A]
    (a b t j r : A) (hb : b ^ 3 + (a+1)*t*b + a-j = 0)
    (ha : a ^ 2-r*t = 0) (ht : t^2=0) (hj : j^2+1=0) :
    b^4 * (-a*b^2 + 2*j*r*t*b^2 + 3*r*a*t*b^2 - 2*a*t) = a := by
  linear_combination
    (-3*a^2*b*r*t^2 + a^2*b*t - 3*a^2*r*t + a^2 +
      3*a*b^3*r*t - a*b^3 - 2*a*b*j*r*t^2 - 3*a*b*r*t^2 -
      a*b*t + a*j*r*t - a*j + 2*b^3*j*r*t - 2*b*j*r*t^2 +
      2*j^2*r*t) * hb +
    (3*a*b^2*r*t^3 - a*b^2*t^2 + 6*a*b*r*t^2 - 2*a*b*t +
      3*a*r*t - a + 2*b^2*j*r*t^3 + 6*b^2*r*t^3 -
      2*b*j*r*t^2 + 2*b*j*t + 6*b*r*t^2 - 4*j*r*t + 2*j) * ha +
    (4*a*b^2*j*r*t + 3*a*b^2*r^2*t^2 + 2*a*b^2*r*t + a*b^2 -
      4*a*b*j^2*r - 2*a*b*j*r + 6*a*b*r^2*t - 2*a*b*r +
      3*a*r^2 + 2*b^2*j*r^2*t^2 + 2*b^2*j*r*t + 6*b^2*r^2*t^2 -
      4*b*j^2*r - 2*b*j*r^2*t + 2*b*j*r + 6*b*r^2*t - 4*j*r^2) * ht +
    (-a*r*t - a + 2*j*r*t) * hj

abbrev JetChart (r : ℂ) (e : Bool) :=
  CurveAlgebra (firstJet (PowerSeries.C r)) (firstJet (PowerSeries.C Complex.I))
    (firstJet (endpointX e)) (firstJet (endpointY e))

def jetEmbedding (r : ℂ) (e : Bool) : PowerChart r e →+* JetChart r e :=
  curveMap firstJet (PowerSeries.C r) (PowerSeries.C Complex.I) (endpointX e) (endpointY e)

def jetX2Unit (r : ℂ) (e : Bool) : (JetChart r e)ˣ :=
  Units.map (jetEmbedding r e) (powerX2Unit r e)

def jetBase (r : ℂ) (e : Bool) : Jet →+* JetChart r e :=
  base (firstJet (PowerSeries.C r)) (firstJet (PowerSeries.C Complex.I))
    (firstJet (endpointX e)) (firstJet (endpointY e))

def jetX0 (r : ℂ) (e : Bool) : JetChart r e :=
  x0 (firstJet (PowerSeries.C r)) (firstJet (PowerSeries.C Complex.I))
    (firstJet (endpointX e)) (firstJet (endpointY e))

def jetX2 (r : ℂ) (e : Bool) : JetChart r e :=
  x2 (firstJet (PowerSeries.C r)) (firstJet (PowerSeries.C Complex.I))
    (firstJet (endpointX e)) (firstJet (endpointY e))

def jetCoefficient (r : ℂ) (e : Bool) : JetChart r e →ₗ[Jet] Jet :=
  coefficient (firstJet (PowerSeries.C r)) (firstJet (PowerSeries.C Complex.I))
    (firstJet (endpointX e)) (firstJet (endpointY e))

@[simp] theorem coe_jetX2Unit (r : ℂ) (e : Bool) :
    (jetX2Unit r e : JetChart r e) = jetX2 r e := by
  simp [jetX2Unit, jetEmbedding, powerX2Unit, jetX2]

theorem false_jet_relations (r : ℂ) :
    let A := jetX0 r false
    let B := jetX2 r false
    let T := jetBase r false (firstJet PowerSeries.X)
    let J := jetBase r false (firstJet (PowerSeries.C Complex.I))
    let R := jetBase r false (firstJet (PowerSeries.C r))
    (B^3+(A+1)*T*B+A-J=0) ∧ (A^2-R*T=0) ∧ T^2=0 ∧ J^2+1=0 := by
  dsimp only
  have ht : (jetBase r false (firstJet PowerSeries.X)) ^ 2 = 0 := by
    rw [← map_pow, firstJet_X_sq, map_zero]
  have ht3 : (jetBase r false (firstJet PowerSeries.X)) ^ 3 = 0 := by
    rw [pow_succ, ht, zero_mul]
  refine ⟨?_, ?_, ht, ?_⟩
  · have hh := x2_cubic (firstJet (PowerSeries.C r))
      (firstJet (PowerSeries.C Complex.I)) (firstJet (endpointX false))
      (firstJet (endpointY false))
    change jetX2 r false ^ 3 +
      (jetX0 r false + jetBase r false (firstJet (endpointX false))) *
        jetBase r false (firstJet (endpointY false)) * jetX2 r false +
      jetX0 r false * jetBase r false ((firstJet (endpointX false)) ^ 2) +
      jetBase r false ((1-firstJet (PowerSeries.C Complex.I)) *
        (firstJet (endpointY false)) ^ 3 - firstJet (PowerSeries.C Complex.I) *
        (firstJet (endpointX false)) ^ 3) = 0 at hh
    simpa only [endpointX, endpointY, map_one, map_sub, map_mul, map_pow,
      one_pow, mul_one, ht3, mul_zero, zero_sub, sub_eq_add_neg, map_add, map_neg, zero_add] using hh
  · have hh := x0_sq (firstJet (PowerSeries.C r))
      (firstJet (PowerSeries.C Complex.I)) (firstJet (endpointX false))
      (firstJet (endpointY false))
    change jetX0 r false ^ 2 = jetBase r false
      (firstJet (PowerSeries.C r) * firstJet (endpointX false) *
        firstJet (endpointY false)) at hh
    simpa only [endpointX, endpointY, map_one, mul_one, map_mul, sub_eq_zero] using hh
  · rw [← map_pow, firstJet_I_sq, map_neg, map_one]
    ring

theorem false_jet_inverse_fourth (r : ℂ) :
    jetX0 r false * ((jetX2Unit r false)⁻¹ : (JetChart r false)ˣ) ^ 4 =
      -jetX0 r false * jetX2 r false ^ 2 +
      2 * jetBase r false (firstJet (PowerSeries.C Complex.I)) *
        jetBase r false (firstJet (PowerSeries.C r)) *
        jetBase r false (firstJet PowerSeries.X) * jetX2 r false ^ 2 +
      3 * jetBase r false (firstJet (PowerSeries.C r)) * jetX0 r false *
        jetBase r false (firstJet PowerSeries.X) * jetX2 r false ^ 2 -
      2 * jetX0 r false * jetBase r false (firstJet PowerSeries.X) := by
  obtain ⟨hb,ha,ht,hj⟩ := false_jet_relations r
  have hh := inverse_fourth_jet_identity _ _ _ _ _ hb ha ht hj
  let H : JetChart r false :=
    -jetX0 r false * jetX2 r false ^ 2 +
      2 * jetBase r false (firstJet (PowerSeries.C Complex.I)) *
        jetBase r false (firstJet (PowerSeries.C r)) *
        jetBase r false (firstJet PowerSeries.X) * jetX2 r false ^ 2 +
      3 * jetBase r false (firstJet (PowerSeries.C r)) * jetX0 r false *
        jetBase r false (firstJet PowerSeries.X) * jetX2 r false ^ 2 -
      2 * jetX0 r false * jetBase r false (firstJet PowerSeries.X)
  change jetX2 r false ^ 4 * H = jetX0 r false at hh
  change jetX0 r false * ((jetX2Unit r false)⁻¹ : (JetChart r false)ˣ) ^ 4 = H
  rw [← hh]
  calc
    _ = (jetX2 r false ^ 4 * (((jetX2Unit r false)⁻¹ : (JetChart r false)ˣ) :
      JetChart r false) ^ 4) * H := by ring
    _ = H := by
      rw [← coe_jetX2Unit, ← mul_pow]
      rw [(jetX2Unit r false).mul_inv, one_pow, one_mul]

theorem false_jet_coefficient (r : ℂ) :
    jetCoefficient r false
      (jetX0 r false * ((jetX2Unit r false)⁻¹ : (JetChart r false)ˣ) ^ 4) =
      -1 + 3 * firstJet (PowerSeries.C r) * firstJet PowerSeries.X := by
  rw [false_jet_inverse_fourth]
  let rr := firstJet (PowerSeries.C r)
  let ii := firstJet (PowerSeries.C Complex.I)
  let tt := firstJet (PowerSeries.X : PS)
  have heq :
      -jetX0 r false * jetX2 r false ^ 2 +
      2 * jetBase r false ii * jetBase r false rr * jetBase r false tt * jetX2 r false ^ 2 +
      3 * jetBase r false rr * jetX0 r false * jetBase r false tt * jetX2 r false ^ 2 -
      2 * jetX0 r false * jetBase r false tt =
      jetBase r false (-1 + 3*rr*tt) * jetX0 r false ^ 1 * jetX2 r false ^ 2 +
      jetBase r false (2*ii*rr*tt) * jetX0 r false ^ 0 * jetX2 r false ^ 2 +
      jetBase r false (-2*tt) * jetX0 r false ^ 1 * jetX2 r false ^ 0 := by
    simp only [map_add, map_sub, map_mul, map_neg, map_ofNat, map_one, pow_zero, pow_one]
    ring
  rw [heq, map_add, map_add]
  unfold jetCoefficient jetBase jetX0 jetX2
  rw [coefficient_small_monomial _ _ _ _ _ 1 2 (by decide) (by decide),
    coefficient_small_monomial _ _ _ _ _ 0 2 (by decide) (by decide),
    coefficient_small_monomial _ _ _ _ _ 1 0 (by decide) (by decide)]
  simp [rr, tt]

end CycleQ2SeedCech

#print axioms CycleQ2SeedCech.inverse_fourth_jet_identity
#print axioms CycleQ2SeedCech.false_jet_coefficient
end
end


/- Component: continuation_3/cylinder_bridge/SlicedCompatibleSystem.lean -/
section
/-! The square subsystem, complementary relation determinant and prescribed
open after an affine parameter slice.  Both seed determinants are exactly
one whenever the compatible linear splitting has identity seed blocks. -/

noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SlicedCompatibleSystem
open MvPolynomial Matrix CycleQ2PolynomialAffineSlice CycleQ2CompatibleEquationCoordinates

variable {R S m l ι κ σ : Type*} [CommRing R] [CommRing S]
  [Fintype m] [Fintype l] [Fintype ι] [Fintype κ] [Fintype σ]
  [DecidableEq m] [DecidableEq ι] [DecidableEq κ]

def equations (a : σ → R) (B : Matrix σ ι R) (P : Matrix ι m R)
    (e : m → MvPolynomial σ R) : ι → MvPolynomial ι R :=
  fun q => substitute a B (retained P e q)

def residual (a : σ → R) (B : Matrix σ ι R) (W : Matrix κ m R)
    (e : m → MvPolynomial σ R) : κ → MvPolynomial ι R :=
  fun q => substitute a B (retained W e q)

def relationA (a : σ → R) (B : Matrix σ ι R) (T : Matrix κ l R)
    (D : Matrix l m (MvPolynomial σ R)) (V : Matrix m κ R) :
    Matrix κ κ (MvPolynomial ι R) :=
  (complementary T D V).map (substitute a B)

def relationC (a : σ → R) (B : Matrix σ ι R) (T : Matrix κ l R)
    (D : Matrix l m (MvPolynomial σ R)) (Q : Matrix m ι R) :
    Matrix κ ι (MvPolynomial ι R) :=
  (crossBlock T D Q).map (substitute a B)

theorem relation_identity
    (a : σ → R) (B : Matrix σ ι R)
    (P : Matrix ι m R) (Q : Matrix m ι R) (V : Matrix m κ R) (W : Matrix κ m R)
    (T : Matrix κ l R) (D : Matrix l m (MvPolynomial σ R))
    (h : Q*P+V*W=1) (e : m → MvPolynomial σ R) (he : D*ᵥe=0) :
    relationA a B T D V *ᵥ residual a B W e +
      relationC a B T D Q *ᵥ equations a B P e = 0 := by
  have hr := polynomial_relations P Q V W T D h e he
  funext q
  have hq := congrArg (substitute a B) (congrFun hr q)
  simpa only [relationA,relationC,equations,residual,Pi.add_apply,Pi.zero_apply,
    Matrix.mulVec,dotProduct,Matrix.map_apply,map_add,map_sum,map_mul,map_zero] using hq

theorem seed_equations_zero (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (P : Matrix ι m R) (e : m → MvPolynomial σ R)
    (he : ∀ q, eval₂Hom φ (φ ∘ a) (e q)=0) (q : ι) :
    eval₂Hom φ (0 : ι → S) (equations a B P e q)=0 := by
  rw [equations,eval_zero_substitute]
  have hev := congrFun (eval_retained φ (φ ∘ a) P e) q
  have hz : (fun k => eval₂Hom φ (φ ∘ a) (e k))=0 := funext he
  rw [hz,mulVec_zero] at hev
  exact hev

theorem seed_relationA (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (T : Matrix κ l R) (D : Matrix l m (MvPolynomial σ R)) (V : Matrix m κ R) :
    (relationA a B T D V).map (eval₂Hom φ (0 : ι → S)) =
      T.map φ * D.map (eval₂Hom φ (φ ∘ a)) * V.map φ := by
  have hm : (relationA a B T D V).map (eval₂Hom φ (0 : ι → S)) =
      (complementary T D V).map (eval₂Hom φ (φ ∘ a)) := by
    funext i j
    exact eval_zero_substitute φ a B (complementary T D V i j)
  rw [hm,eval_complementary]

theorem seed_relationA_det_one (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (T : Matrix κ l R) (D : Matrix l m (MvPolynomial σ R)) (V : Matrix m κ R)
    (h : T.map φ * D.map (eval₂Hom φ (φ ∘ a)) * V.map φ=1) :
    eval₂Hom φ (0 : ι → S) (relationA a B T D V).det=1 := by
  rw [RingHom.map_det]
  change ((relationA a B T D V).map (eval₂Hom φ (0 : ι → S))).det=1
  rw [seed_relationA,h,Matrix.det_one]

/-- The derivative convention used by the generic lifting theorem has
variables as rows.  Its transpose is still the identity seed block. -/
theorem seed_jacobian_one (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (P : Matrix ι m R) (e : m → MvPolynomial σ R)
    (h : P.map φ * jacobian φ (φ ∘ a) e * B.map φ=1) :
    (fun i j => eval₂Hom φ (0 : ι → S) (pderiv i (equations a B P e j))) =
      (1 : Matrix ι ι S) := by
  have hj : jacobian φ (0 : ι → S) (equations a B P e)=1 := by
    exact (sliced_jacobian φ a B P e).trans h
  funext i j
  have hji := congrFun (congrFun hj j) i
  simpa only [jacobian,Matrix.one_apply,eq_comm] using hji

theorem seed_jacobian_det_one (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (P : Matrix ι m R) (e : m → MvPolynomial σ R)
    (h : P.map φ * jacobian φ (φ ∘ a) e * B.map φ=1) :
    Matrix.det (fun i j => eval₂Hom φ (0 : ι → S) (pderiv i (equations a B P e j)))=1 := by
  rw [seed_jacobian_one φ a B P e h,Matrix.det_one]

theorem evaluated_equations_zero
    (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (P : Matrix ι m R) (Q : Matrix m ι R) (V : Matrix m κ R) (W : Matrix κ m R)
    (h : Q*P+V*W=1) (e : m → MvPolynomial σ R) (x : ι → S)
    (hP : ∀ q, eval₂Hom φ x (equations a B P e q)=0)
    (hW : ∀ q, eval₂Hom φ x (residual a B W e q)=0) :
    ∀ q, eval₂Hom φ (pointValue φ a B x) (e q)=0 := by
  have hP' : P.map φ *ᵥ (fun q => eval₂Hom φ (pointValue φ a B x) (e q))=0 := by
    rw [← eval_retained]
    funext q
    exact (eval_substitute φ a B x (retained P e q)).symm.trans (hP q)
  have hW' : W.map φ *ᵥ (fun q => eval₂Hom φ (pointValue φ a B x) (e q))=0 := by
    rw [← eval_retained]
    funext q
    exact (eval_substitute φ a B x (retained W e q)).symm.trans (hW q)
  have hz := (equations_zero_iff (P.map φ) (Q.map φ) (V.map φ) (W.map φ)
    (mapped_decomposition φ P Q V W h) _).mp ⟨hP',hW'⟩
  exact fun q => congrFun hz q

end CycleQ2SlicedCompatibleSystem

#print axioms CycleQ2SlicedCompatibleSystem.relation_identity
#print axioms CycleQ2SlicedCompatibleSystem.seed_relationA_det_one
#print axioms CycleQ2SlicedCompatibleSystem.seed_jacobian_det_one
#print axioms CycleQ2SlicedCompatibleSystem.evaluated_equations_zero
end
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


/- Component: continuation_3/cylinder_bridge/CompatibleAffineGenericLifting.lean -/
section
/-! A compatible equation splitting and affine parameter directions give
an actual finite separable generic solution of the entire polynomial
system.  The two nonsingular blocks used in lifting are proved to be the
identity, rather than supplied as additional minor hypotheses. -/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CompatibleAffineGenericLifting
open MvPolynomial Matrix HoldoutConstruction
open CycleQ2PolynomialAffineSlice CycleQ2CompatibleEquationCoordinates
open CycleQ2SlicedCompatibleSystem

variable {R T K m l ι κ σ : Type*}
  [CommRing R] [CommRing T] [Nontrivial T] [Algebra R T]
  [Field K] [Algebra R K]
  [Fintype m] [Fintype l] [Fintype ι] [Fintype κ] [Fintype σ]
  [DecidableEq m] [DecidableEq ι] [DecidableEq κ]

abbrev GenericAlgebra (K : Type*) [Field K] [Algebra R K]
    (a : σ → R) (B : Matrix σ ι R) (P : Matrix ι m R)
    (T₀ : Matrix κ l R) (D : Matrix l m (MvPolynomial σ R)) (V : Matrix m κ R)
    (e : m → MvPolynomial σ R) (c : MvPolynomial σ R) :=
  SquareGenericAlgebra K (CycleQ2OpenSquareLifting.openSystem (equations a B P e)
    (substitute a B c * (relationA a B T₀ D V).det))

/-- The coefficient ring may contain the external family parameters.  The
only varied variables are the affine slice coordinates; the resulting
point satisfies every original equation and the original prescribed open. -/
theorem lift_all_on_compatible_affine_slice
    (a : σ → R) (B : Matrix σ ι R)
    (P : Matrix ι m R) (Q : Matrix m ι R) (V : Matrix m κ R) (W : Matrix κ m R)
    (T₀ : Matrix κ l R) (D : Matrix l m (MvPolynomial σ R))
    (e : m → MvPolynomial σ R) (c : MvPolynomial σ R)
    (hdecomp : Q*P+V*W=1)
    (hrelations : D*ᵥe=0)
    (hseed : ∀ q, eval₂Hom (algebraMap R T) ((algebraMap R T) ∘ a) (e q)=0)
    (hjac : P.map (algebraMap R T) *
      jacobian (algebraMap R T) ((algebraMap R T) ∘ a) e *
      B.map (algebraMap R T)=1)
    (hcomplement : T₀.map (algebraMap R T) *
      D.map (eval₂Hom (algebraMap R T) ((algebraMap R T) ∘ a)) *
      V.map (algebraMap R T)=1)
    (hc : IsUnit (eval₂Hom (algebraMap R T) ((algebraMap R T) ∘ a) c))
    (hinj : Function.Injective (algebraMap R K)) :
    ∃ I : Ideal (GenericAlgebra K a B P T₀ D V e c),
      I.IsMaximal ∧
      Module.Finite K ((GenericAlgebra K a B P T₀ D V e c) ⧸ I) ∧
      Algebra.IsSeparable K ((GenericAlgebra K a B P T₀ D V e c) ⧸ I) ∧
      ∃ x : ι → ((GenericAlgebra K a B P T₀ D V e c) ⧸ I),
        (∀ q, aeval (pointValue (algebraMap R _) a B x) (e q)=0) ∧
        IsUnit (aeval (pointValue (algebraMap R _) a B x) c) := by
  have hseed' (q : ι) : aeval (0 : ι → T) (equations a B P e q)=0 := by
    exact seed_equations_zero (algebraMap R T) a B P e hseed q
  have hjac' : IsUnit (Matrix.det (fun i j =>
      aeval (0 : ι → T) (pderiv i (equations a B P e j)))) := by
    change IsUnit (Matrix.det (fun i j =>
      eval₂Hom (algebraMap R T) (0 : ι → T) (pderiv i (equations a B P e j))))
    rw [seed_jacobian_det_one (algebraMap R T) a B P e hjac]
    exact isUnit_one
  have hcomplement' : IsUnit (aeval (0 : ι → T) (relationA a B T₀ D V).det) := by
    change IsUnit (eval₂Hom (algebraMap R T) (0 : ι → T) (relationA a B T₀ D V).det)
    rw [seed_relationA_det_one (algebraMap R T) a B T₀ D V hcomplement]
    exact isUnit_one
  have hc' : IsUnit (aeval (0 : ι → T) (substitute a B c)) := by
    change IsUnit (eval₂Hom (algebraMap R T) (0 : ι → T) (substitute a B c))
    rw [eval_zero_substitute]
    exact hc
  obtain ⟨I,hI,hfinite,hsep,x,hP,hW,hopen,_⟩ :=
    CycleQ2SegreGenericLifting.lift_all_equations_on_open (K := K)
      (equations a B P e) (residual a B W e)
      (relationA a B T₀ D V) (relationC a B T₀ D Q) (substitute a B c)
      (relation_identity a B P Q V W T₀ D hdecomp e hrelations)
      (0 : ι → T) hseed' hjac' hcomplement' hc' hinj
  refine ⟨I,hI,hfinite,hsep,x,?_,?_⟩
  · exact evaluated_equations_zero (algebraMap R _) a B P Q V W hdecomp e x hP hW
  · change IsUnit (eval₂Hom (algebraMap R _) (pointValue (algebraMap R _) a B x) c)
    rw [← eval_substitute (algebraMap R _) a B x c]
    exact hopen

end CycleQ2CompatibleAffineGenericLifting

#print axioms CycleQ2CompatibleAffineGenericLifting.lift_all_on_compatible_affine_slice
end
end


/- Component: continuation_3/CurveRestrictionNormalForm.lean -/
section
/-! Integral normal forms for both actual curve restrictions.  The right curve
uses a scaled linear change of coordinates, so every formula is integral. -/

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveRestriction

open MvPolynomial CycleQ2IncidenceNormalForm
open scoped MonomialOrder

variable {R : Type*} [CommRing R]

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

abbrev CurvePoly (R : Type*) [CommRing R] := MvPolynomial (Fin 4) R
abbrev CurveExponent := Fin 4 →₀ ℕ

def exponent (v : Fin 4 → ℕ) : CurveExponent := Finsupp.equivFunOnFinite.symm v
@[simp] theorem exponent_apply (v : Fin 4 → ℕ) (i : Fin 4) : exponent v i = v i := rfl

def mon (a b c d : ℕ) : CurvePoly R := X 0 ^ a * X 1 ^ b * X 2 ^ c * X 3 ^ d

theorem mon_eq_monomial (a b c d : ℕ) :
    (mon a b c d : CurvePoly R) = monomial (exponent ![a,b,c,d]) 1 := by
  simp only [mon, X_pow_eq_monomial, monomial_mul, one_mul]
  apply congrArg (fun e : CurveExponent => monomial e (1 : R))
  ext i
  fin_cases i <;> simp [exponent, Finsupp.single_apply, Fin.ext_iff]

theorem monomial_eq_C_mul_mon (a b c d : ℕ) (r : R) :
    monomial (exponent ![a,b,c,d]) r = C r * mon a b c d := by
  rw [mon_eq_monomial, C_mul_monomial, mul_one]

theorem mon_homogeneous (a b c d : ℕ) :
    (mon a b c d : CurvePoly R).IsHomogeneous (a+b+c+d) := by
  rw [mon_eq_monomial]
  apply isHomogeneous_monomial
  norm_num [Finsupp.degree_eq_sum, Fin.sum_univ_succ, add_assoc,
    Matrix.cons_val_succ, Fin.reduceSucc]

inductive Side | left | right deriving DecidableEq, Fintype

def xBound : Side → ℕ | .left => 2 | .right => 3
def zBound : Side → ℕ | .left => 3 | .right => 2

def curveWeight : Side → CurveExponent →+ ℕ
  | .left =>
    { toFun := fun d => 3*d 0+d 1+3*d 2+d 3
      map_zero' := by simp
      map_add' := by intro a b; simp only [Finsupp.add_apply]; omega }
  | .right =>
    { toFun := fun d => 3*d 0+d 1+4*d 2+d 3
      map_zero' := by simp
      map_add' := by intro a b; simp only [Finsupp.add_apply]; omega }

def curveOrder (s : Side) : MonomialOrder (Fin 4) :=
  weightedOrder MonomialOrder.lex (curveWeight s)

def quadric (s : Side) (r : R) : CurvePoly R :=
  match s with
  | .left => X 0 ^ 2 - C r * X 1 * X 3
  | .right => X 2 ^ 2 + X 0 ^ 2

def cubic (s : Side) (r ι : R) : CurvePoly R :=
  match s with
  | .left => X 2 ^ 3 + X 0*X 2*X 3 + X 1*X 2*X 3 + X 0*X 1^2 +
      C r*X 0*X 1*X 3 + C (1-ι)*X 3^3 - C ι*X 1^3
  | .right => X 0 ^ 3 - X 0^2*X 3 - X 0*X 1*X 3 + X 2*X 1*X 3 -
      X 0*X 1^2 - X 2*X 1^2 - C (2*(1-ι))*X 3^3 + C (2*ι)*X 1^3

def quadricLead : Side → CurveExponent
  | .left => Finsupp.single 0 2
  | .right => Finsupp.single 2 2

def cubicLead : Side → CurveExponent
  | .left => Finsupp.single 2 3
  | .right => Finsupp.single 0 3

def leftTailExponent (j : Fin 6) : CurveExponent :=
  ![exponent ![1,0,1,1], exponent ![0,1,1,1], exponent ![1,2,0,0],
    exponent ![1,1,0,1], exponent ![0,0,0,3], exponent ![0,3,0,0]] j

def leftTailCoefficient (r ι : R) (j : Fin 6) : R := ![1,1,1,r,1-ι,-ι] j

def rightTailExponent (j : Fin 7) : CurveExponent :=
  ![exponent ![2,0,0,1], exponent ![1,1,0,1], exponent ![0,1,1,1],
    exponent ![1,2,0,0], exponent ![0,2,1,0], exponent ![0,0,0,3],
    exponent ![0,3,0,0]] j

def rightTailCoefficient (ι : R) (j : Fin 7) : R :=
  ![-1,-1,1,-1,-1,-(2*(1-ι)),2*ι] j

theorem left_quadric_shape (r : R) :
    quadric .left r = monomial (quadricLead .left) 1 +
      ∑ _j : Fin 1, monomial (exponent ![0,1,0,1]) (-r) := by
  simp only [Fin.sum_univ_one, quadricLead]
  rw [← X_pow_eq_monomial, monomial_eq_C_mul_mon]
  simp [quadric, mon] <;> ring

theorem right_quadric_shape (r : R) :
    quadric .right r = monomial (quadricLead .right) 1 +
      ∑ _j : Fin 1, monomial (exponent ![2,0,0,0]) 1 := by
  simp only [Fin.sum_univ_one, quadricLead]
  rw [← X_pow_eq_monomial, monomial_eq_C_mul_mon]
  simp [quadric, mon]

theorem left_cubic_shape (r ι : R) :
    cubic .left r ι = monomial (cubicLead .left) 1 +
      ∑ j : Fin 6, monomial (leftTailExponent j) (leftTailCoefficient r ι j) := by
  simp only [cubicLead, ← X_pow_eq_monomial]
  simp only [Fin.sum_univ_succ, leftTailExponent, leftTailCoefficient,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.reduceSucc,
    Matrix.head_cons, Matrix.tail_cons, monomial_eq_C_mul_mon]
  norm_num [cubic, mon, Matrix.cons_val_succ, Fin.reduceSucc]
  ring

theorem right_cubic_shape (r ι : R) :
    cubic .right r ι = monomial (cubicLead .right) 1 +
      ∑ j : Fin 7, monomial (rightTailExponent j) (rightTailCoefficient ι j) := by
  simp only [cubicLead, ← X_pow_eq_monomial]
  simp only [Fin.sum_univ_succ, rightTailExponent, rightTailCoefficient,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.reduceSucc,
    Matrix.head_cons, Matrix.tail_cons, monomial_eq_C_mul_mon]
  norm_num [cubic, mon, Matrix.cons_val_succ, Fin.reduceSucc]
  ring

theorem quadric_leading [Nontrivial R] (s : Side) (r : R) :
    (curveOrder s).degree (quadric s r) = quadricLead s ∧
      (curveOrder s).Monic (quadric s r) := by
  cases s
  · rw [left_quadric_shape]
    apply degree_monic_add_sum
    · apply weightedOrder_lt_of_weight_lt
      norm_num [curveWeight, quadricLead, Finsupp.single_apply, Fin.ext_iff]
    · intro j
      apply weightedOrder_lt_of_weight_lt
      norm_num [curveWeight, quadricLead, Finsupp.single_apply, Fin.ext_iff]
  · rw [right_quadric_shape]
    apply degree_monic_add_sum
    · apply weightedOrder_lt_of_weight_lt
      norm_num [curveWeight, quadricLead, Finsupp.single_apply, Fin.ext_iff]
    · intro j
      apply weightedOrder_lt_of_weight_lt
      norm_num [curveWeight, quadricLead, Finsupp.single_apply, Fin.ext_iff]

theorem cubic_leading [Nontrivial R] (s : Side) (r ι : R) :
    (curveOrder s).degree (cubic s r ι) = cubicLead s ∧
      (curveOrder s).Monic (cubic s r ι) := by
  cases s
  · rw [left_cubic_shape]
    apply degree_monic_add_sum
    · apply weightedOrder_lt_of_weight_lt
      norm_num [curveWeight, cubicLead, Finsupp.single_apply, Fin.ext_iff]
    · intro j
      apply weightedOrder_lt_of_weight_lt
      fin_cases j <;> norm_num [curveWeight, leftTailExponent, cubicLead,
        Matrix.cons_val_succ, Fin.reduceSucc, Finsupp.single_apply, Fin.ext_iff]
  · rw [right_cubic_shape]
    apply degree_monic_add_sum
    · apply weightedOrder_lt_of_weight_lt
      norm_num [curveWeight, cubicLead, Finsupp.single_apply, Fin.ext_iff]
    · intro j
      apply weightedOrder_lt_of_weight_lt
      fin_cases j <;> norm_num [curveWeight, rightTailExponent, cubicLead,
        Matrix.cons_val_succ, Fin.reduceSucc, Finsupp.single_apply, Fin.ext_iff]

theorem leading_coprime [Nontrivial R] (s : Side) (r ι : R) :
    ∀ j, (curveOrder s).degree (quadric s r) j = 0 ∨
      (curveOrder s).degree (cubic s r ι) j = 0 := by
  rw [(quadric_leading s r).1, (cubic_leading s r ι).1]
  intro j
  cases s <;> fin_cases j <;> simp [quadricLead, cubicLead]

def Standard (s : Side) (p : CurvePoly R) : Prop :=
  ∀ e ∈ p.support, e 0 < xBound s ∧ e 2 < zBound s

theorem standard_iff [Nontrivial R] (s : Side) (r ι : R) (p : CurvePoly R) :
    Standard s p ↔ Reduced (curveOrder s) (quadric s r) (cubic s r ι) p := by
  simp only [Standard, Reduced, (quadric_leading s r).1, (cubic_leading s r ι).1]
  apply forall_congr'
  intro e
  apply forall_congr'
  intro he
  cases s <;> simp only [quadricLead, cubicLead, Finsupp.single_le_iff, xBound, zBound]
  · omega
  · omega

theorem quadric_homogeneous (s : Side) (r : R) :
    (quadric s r).IsHomogeneous 2 := by
  cases s
  · rw [left_quadric_shape]
    apply IsHomogeneous.add
    · exact isHomogeneous_monomial _ (by simp [quadricLead])
    · apply (homogeneousSubmodule (Fin 4) R 2).sum_mem
      intro j hj
      apply isHomogeneous_monomial
      norm_num [Finsupp.degree_eq_sum, Fin.sum_univ_succ,
        Matrix.cons_val_succ, Fin.reduceSucc]
  · rw [right_quadric_shape]
    apply IsHomogeneous.add
    · exact isHomogeneous_monomial _ (by simp [quadricLead])
    · apply (homogeneousSubmodule (Fin 4) R 2).sum_mem
      intro j hj
      apply isHomogeneous_monomial
      norm_num [Finsupp.degree_eq_sum, Fin.sum_univ_succ,
        Matrix.cons_val_succ, Fin.reduceSucc]

theorem cubic_homogeneous (s : Side) (r ι : R) :
    (cubic s r ι).IsHomogeneous 3 := by
  cases s
  · rw [left_cubic_shape]
    apply IsHomogeneous.add
    · exact isHomogeneous_monomial _ (by simp [cubicLead])
    · apply (homogeneousSubmodule (Fin 4) R 3).sum_mem
      intro j hj
      apply isHomogeneous_monomial
      fin_cases j <;> norm_num [leftTailExponent, Finsupp.degree_eq_sum,
        Fin.sum_univ_succ, Matrix.cons_val_succ, Fin.reduceSucc]
  · rw [right_cubic_shape]
    apply IsHomogeneous.add
    · exact isHomogeneous_monomial _ (by simp [cubicLead])
    · apply (homogeneousSubmodule (Fin 4) R 3).sum_mem
      intro j hj
      apply isHomogeneous_monomial
      fin_cases j <;> norm_num [rightTailExponent, Finsupp.degree_eq_sum,
        Fin.sum_univ_succ, Matrix.cons_val_succ, Fin.reduceSucc]

def curveIdeal (s : Side) (r ι : R) : Ideal (CurvePoly R) :=
  equationsIdeal (quadric s r) (cubic s r ι)

abbrev CurveRing (s : Side) (r ι : R) := CurvePoly R ⧸ curveIdeal s r ι

theorem existsUnique_normal [Nontrivial R] (s : Side) (r ι : R) (p : CurvePoly R) :
    ∃! q, Standard s q ∧ ∃ a b, p = a * quadric s r + b * cubic s r ι + q := by
  simpa only [standard_iff s r ι] using
    existsUnique_reduced_representative (curveOrder s) (quadric s r) (cubic s r ι) p
      (quadric_leading s r).2 (cubic_leading s r ι).2 (leading_coprime s r ι)

def normal [Nontrivial R] (s : Side) (r ι : R) (p : CurvePoly R) : CurvePoly R :=
  (existsUnique_normal s r ι p).choose

theorem normal_spec [Nontrivial R] (s : Side) (r ι : R) (p : CurvePoly R) :
    Standard s (normal s r ι p) ∧
      ∃ a b, p = a * quadric s r + b * cubic s r ι + normal s r ι p :=
  (existsUnique_normal s r ι p).choose_spec.1

theorem normal_unique [Nontrivial R] (s : Side) (r ι : R) (p q : CurvePoly R)
    (hq : Standard s q) (hrep : ∃ a b, p = a * quadric s r + b * cubic s r ι + q) :
    q = normal s r ι p :=
  (existsUnique_normal s r ι p).choose_spec.2 q ⟨hq, hrep⟩

theorem normal_homogeneous [Nontrivial R] (s : Side) (r ι : R)
    {p : CurvePoly R} {d : ℕ} (hp : p.IsHomogeneous d) :
    (normal s r ι p).IsHomogeneous d := by
  obtain ⟨hr, a, b, heq⟩ := normal_spec s r ι p
  exact reduced_isHomogeneous (curveOrder s) (quadric_leading s r).2
    (cubic_leading s r ι).2 (leading_coprime s r ι)
    (quadric_homogeneous s r) (cubic_homogeneous s r ι) hp
    ((standard_iff s r ι _).mp hr) heq

theorem normal_eq_self [Nontrivial R] (s : Side) (r ι : R)
    {p : CurvePoly R} (hp : Standard s p) : normal s r ι p = p := by
  exact (normal_unique s r ι p p hp ⟨0,0,by simp⟩).symm

@[simp] theorem map_quadric {S : Type*} [CommRing S] (φ : R →+* S) (s : Side) (r : R) :
    MvPolynomial.map φ (quadric s r) = quadric s (φ r) := by
  cases s <;> simp [quadric]

@[simp] theorem map_cubic {S : Type*} [CommRing S] (φ : R →+* S) (s : Side) (r ι : R) :
    MvPolynomial.map φ (cubic s r ι) = cubic s (φ r) (φ ι) := by
  cases s <;> simp [cubic, map_ofNat]

theorem standard_map {S : Type*} [CommRing S] (φ : R →+* S)
    {s : Side} {p : CurvePoly R} (hp : Standard s p) :
    Standard s (MvPolynomial.map φ p) := by
  intro e he
  exact hp e (MvPolynomial.support_map_subset φ p he)

theorem normal_map [Nontrivial R] {S : Type*} [CommRing S] [Nontrivial S]
    (φ : R →+* S) (s : Side) (r ι : R) (p : CurvePoly R) :
    MvPolynomial.map φ (normal s r ι p) =
      normal s (φ r) (φ ι) (MvPolynomial.map φ p) := by
  obtain ⟨hr,a,b,hp⟩ := normal_spec s r ι p
  apply normal_unique
  · exact standard_map φ hr
  · refine ⟨MvPolynomial.map φ a, MvPolynomial.map φ b, ?_⟩
    simpa only [map_add, map_mul, map_quadric, map_cubic] using congrArg (MvPolynomial.map φ) hp

/-- The left restriction eliminates w.  The right restriction is the integral
scaled coordinate change (x₀,x₁,x₂,x₃,w)=(u+v,2y₁,u-v,2y₃,4ry₁y₃). -/
def restrictionValues (s : Side) (r : R) : Fin 5 → CurvePoly R :=
  match s with
  | .left => ![X 0, X 1, X 2, X 3, -(X 2^2)]
  | .right => ![X 0+X 2, 2*X 1, X 0-X 2, 2*X 3, C (4*r)*X 1*X 3]

def substitution (s : Side) (r : R) : MvPolynomial (Fin 5) R →ₐ[R] CurvePoly R :=
  aeval (restrictionValues s r)

@[simp] theorem substitution_X (s : Side) (r : R) (i : Fin 5) :
    substitution s r (X i) = restrictionValues s r i := by
  simp [substitution]

@[simp] theorem substitution_C (s : Side) (r c : R) :
    substitution s r (C c) = C c := by
  simp [substitution]

theorem left_h_identity (r ι : R) :
    substitution .left r (CycleQ2IncidenceEquations.smoothH ι) =
      cubic .left r ι + X 0 * quadric .left r := by
  simp only [CycleQ2IncidenceEquations.smoothH, CycleQ2IncidenceEquations.smoothB,
    CycleQ2IncidenceEquations.smoothA, map_sub, map_add, map_mul, map_pow,
    substitution_X, substitution_C]
  norm_num [restrictionValues, cubic, quadric, Matrix.cons_val_succ, Fin.reduceSucc, map_ofNat]
  ring

theorem right_h_identity (r ι : R) :
    substitution .right r (CycleQ2IncidenceEquations.smoothH ι) =
      -4 * cubic .right r ι + (6*X 0-2*X 3) * quadric .right r := by
  simp only [CycleQ2IncidenceEquations.smoothH, CycleQ2IncidenceEquations.smoothB,
    CycleQ2IncidenceEquations.smoothA, map_sub, map_add, map_mul, map_pow,
    substitution_X, substitution_C]
  norm_num [restrictionValues, cubic, quadric, Matrix.cons_val_succ, Fin.reduceSucc, map_ofNat]
  ring

theorem left_G_identity (r : R) :
    substitution .left r (CycleQ2IncidenceEquations.seedG r) =
      quadric .left r * (X 0^4+C r*X 0^2*X 1*X 3+C (r^2)*X 1^2*X 3^2) := by
  simp only [CycleQ2IncidenceEquations.seedG, CycleQ2SegreSeed.seedG, CycleQ2SegreSeed.linkageG, map_sub, map_add, map_mul, map_pow,
    substitution_X, substitution_C]
  norm_num [restrictionValues, quadric, Matrix.cons_val_succ, Fin.reduceSucc, map_ofNat]
  ring

theorem right_G_identity (r : R) :
    substitution .right r (CycleQ2IncidenceEquations.seedG r) =
      2 * quadric .right r * (X 0^4+14*X 0^2*X 2^2+X 2^4) := by
  simp only [CycleQ2IncidenceEquations.seedG, CycleQ2SegreSeed.seedG, CycleQ2SegreSeed.linkageG, map_sub, map_add, map_mul, map_pow,
    substitution_X, substitution_C]
  norm_num [restrictionValues, quadric, Matrix.cons_val_succ, Fin.reduceSucc, map_ofNat]
  ring

theorem substitution_h_mem (s : Side) (r ι : R) :
    substitution s r (CycleQ2IncidenceEquations.smoothH ι) ∈ curveIdeal s r ι := by
  cases s
  · rw [left_h_identity]
    apply Ideal.mem_span_pair.mpr
    exact ⟨X 0, 1, by ring⟩
  · rw [right_h_identity]
    apply Ideal.mem_span_pair.mpr
    exact ⟨6*X 0-2*X 3, -4, by ring⟩

theorem substitution_G_mem (s : Side) (r ι : R) :
    substitution s r (CycleQ2IncidenceEquations.seedG r) ∈ curveIdeal s r ι := by
  cases s
  · rw [left_G_identity]
    apply Ideal.mem_span_pair.mpr
    exact ⟨X 0^4+C r*X 0^2*X 1*X 3+C (r^2)*X 1^2*X 3^2, 0, by ring⟩
  · rw [right_G_identity]
    apply Ideal.mem_span_pair.mpr
    exact ⟨2*(X 0^4+14*X 0^2*X 2^2+X 2^4), 0, by ring⟩

theorem substitution_F_mem (s : Side) (r ι : R) :
    substitution s r (CycleQ2IncidenceEquations.smoothF r ι) ∈ curveIdeal s r ι := by
  rw [CycleQ2IncidenceEquations.smoothF, map_add, map_mul]
  exact Ideal.add_mem _ (substitution_G_mem s r ι)
    (Ideal.mul_mem_right _ _ (substitution_h_mem s r ι))

theorem standard_add {s : Side} {p q : CurvePoly R}
    (hp : Standard s p) (hq : Standard s q) : Standard s (p+q) := by
  intro e he
  rcases Finset.mem_union.mp (support_add he) with h | h
  · exact hp e h
  · exact hq e h

theorem standard_C_mul {s : Side} {p : CurvePoly R} (hp : Standard s p) (c : R) :
    Standard s (C c*p) := by
  intro e he
  apply hp e
  apply mem_support_iff.mpr
  intro hz
  exact (mem_support_iff.mp he) (by rw [coeff_C_mul, hz, mul_zero])

theorem normal_add [Nontrivial R] (s : Side) (r ι : R) (p q : CurvePoly R) :
    normal s r ι (p+q) = normal s r ι p + normal s r ι q := by
  obtain ⟨hp,a,b,hab⟩ := normal_spec s r ι p
  obtain ⟨hq,c,d,hcd⟩ := normal_spec s r ι q
  symm
  apply normal_unique
  · exact standard_add hp hq
  · refine ⟨a+c,b+d,?_⟩
    linear_combination hab+hcd

theorem normal_C_mul [Nontrivial R] (s : Side) (r ι c : R) (p : CurvePoly R) :
    normal s r ι (C c*p) = C c*normal s r ι p := by
  obtain ⟨hp,a,b,hab⟩ := normal_spec s r ι p
  symm
  apply normal_unique
  · exact standard_C_mul hp c
  · refine ⟨C c*a,C c*b,?_⟩
    linear_combination C c*hab

def normalLinear [Nontrivial R] (s : Side) (r ι : R) : CurvePoly R →ₗ[R] CurvePoly R where
  toFun := normal s r ι
  map_add' := normal_add s r ι
  map_smul' := fun c p => by
    simpa only [smul_eq_C_mul, RingHom.id_apply] using normal_C_mul s r ι c p

theorem normal_sub_mem [Nontrivial R] (s : Side) (r ι : R) (p : CurvePoly R) :
    p-normal s r ι p ∈ curveIdeal s r ι := by
  obtain ⟨_,a,b,hp⟩ := normal_spec s r ι p
  apply Ideal.mem_span_pair.mpr
  exact ⟨a,b,by linear_combination -hp⟩

theorem normal_eq_zero_iff [Nontrivial R] (s : Side) (r ι : R) (p : CurvePoly R) :
    normal s r ι p = 0 ↔ p ∈ curveIdeal s r ι := by
  constructor
  · intro hp
    simpa only [hp, sub_zero] using normal_sub_mem s r ι p
  · intro hp
    obtain ⟨a,b,hab⟩ := Ideal.mem_span_pair.mp hp
    symm
    exact normal_unique s r ι p 0 (by simp [Standard])
      ⟨a,b,by simpa only [add_zero] using hab.symm⟩

@[simp] theorem map_restrictionValues {S : Type*} [CommRing S]
    (φ : R →+* S) (s : Side) (r : R) (j : Fin 5) :
    MvPolynomial.map φ (restrictionValues s r j) = restrictionValues s (φ r) j := by
  cases s <;> fin_cases j <;>
    norm_num [restrictionValues, map_ofNat, Matrix.cons_val_succ, Fin.reduceSucc]

theorem substitution_map {S : Type*} [CommRing S]
    (φ : R →+* S) (s : Side) (r : R) (p : MvPolynomial (Fin 5) R) :
    MvPolynomial.map φ (substitution s r p) =
      substitution s (φ r) (MvPolynomial.map φ p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp => simp only [map_mul, hp, map_X, substitution_X, map_restrictionValues]

/-- A linear map representing the genuine restriction, with the canonical
curve representative chosen by the proved normal-form theorem. -/
def restrictionNormal [Nontrivial R] (s : Side) (r ι : R) :
    MvPolynomial (Fin 5) R →ₗ[R] CurvePoly R :=
  (normalLinear s r ι).comp (substitution s r).toLinearMap

@[simp] theorem restrictionNormal_apply [Nontrivial R]
    (s : Side) (r ι : R) (p : MvPolynomial (Fin 5) R) :
    restrictionNormal s r ι p = normal s r ι (substitution s r p) := rfl

theorem restrictionNormal_map [Nontrivial R] {S : Type*} [CommRing S] [Nontrivial S]
    (φ : R →+* S) (s : Side) (r ι : R) (p : MvPolynomial (Fin 5) R) :
    MvPolynomial.map φ (restrictionNormal s r ι p) =
      restrictionNormal s (φ r) (φ ι) (MvPolynomial.map φ p) := by
  simp only [restrictionNormal_apply, normal_map, substitution_map]

end CycleQ2CurveRestriction

#print axioms CycleQ2CurveRestriction.quadric_leading
#print axioms CycleQ2CurveRestriction.cubic_leading
#print axioms CycleQ2CurveRestriction.normal_homogeneous
#print axioms CycleQ2CurveRestriction.substitution_F_mem
#print axioms CycleQ2CurveRestriction.restrictionNormal_map
end
end


/- Component: continuation_3/IncidenceFirstOrder.lean -/
section
/-! # First-order equations at the literal Segre seed

This file identifies the moving-cubic linearized residual directly from the
quadratic cofactor identity.  A residual in `(h,G)` produces an actual solution
of all 9522 incidence equations over any square-zero thickening.
-/

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2IncidenceFirstOrder

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations

section Cofactors

variable {A : Type*} [CommRing A]

/-- Polarization of the quadratic cofactor polynomial. -/
def cofactorDifferential (M N : Matrix (Fin 3) (Fin 3) A) : Matrix (Fin 3) (Fin 3) A :=
  CycleQ2SegreLocal.cofactors (M + N) -
    CycleQ2SegreLocal.cofactors M - CycleQ2SegreLocal.cofactors N

theorem cofactor_quadratic (M N : Matrix (Fin 3) (Fin 3) A) (t : A) (i j : Fin 3) :
    CycleQ2SegreLocal.cofactors (fun i j ↦ M i j + t * N i j) i j =
      CycleQ2SegreLocal.cofactors M i j + t * cofactorDifferential M N i j +
        t ^ 2 * CycleQ2SegreLocal.cofactors N i j := by
  simp only [cofactorDifferential, CycleQ2SegreLocal.cofactors, Matrix.adjugate_fin_three,
    Matrix.add_apply, Matrix.sub_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero',
      Matrix.cons_val_succ'] <;> ring

/-- Explicit bilinear entries, so sparse certificates need never expand a
product of two correction polynomials and subsequently cancel it. -/
theorem cofactorDifferential_fin_three (M N : Matrix (Fin 3) (Fin 3) A) :
    cofactorDifferential M N =
      ![![N 1 1 * M 2 2 + M 1 1 * N 2 2 - N 1 2 * M 2 1 - M 1 2 * N 2 1,
          -N 1 0 * M 2 2 - M 1 0 * N 2 2 + N 1 2 * M 2 0 + M 1 2 * N 2 0,
          N 1 0 * M 2 1 + M 1 0 * N 2 1 - N 1 1 * M 2 0 - M 1 1 * N 2 0],
        ![-N 0 1 * M 2 2 - M 0 1 * N 2 2 + N 0 2 * M 2 1 + M 0 2 * N 2 1,
          N 0 0 * M 2 2 + M 0 0 * N 2 2 - N 0 2 * M 2 0 - M 0 2 * N 2 0,
          -N 0 0 * M 2 1 - M 0 0 * N 2 1 + N 0 1 * M 2 0 + M 0 1 * N 2 0],
        ![N 0 1 * M 1 2 + M 0 1 * N 1 2 - N 0 2 * M 1 1 - M 0 2 * N 1 1,
          -N 0 0 * M 1 2 - M 0 0 * N 1 2 + N 0 2 * M 1 0 + M 0 2 * N 1 0,
          N 0 0 * M 1 1 + M 0 0 * N 1 1 - N 0 1 * M 1 0 - M 0 1 * N 1 0]] := by
  ext i j
  simp only [cofactorDifferential, CycleQ2SegreLocal.cofactors, Matrix.adjugate_fin_three,
    Matrix.add_apply, Matrix.sub_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero',
      Matrix.cons_val_succ'] <;> ring

theorem cofactorDifferential_add (M N P : Matrix (Fin 3) (Fin 3) A) :
    cofactorDifferential M (N + P) = cofactorDifferential M N + cofactorDifferential M P := by
  ext i j
  simp only [cofactorDifferential, CycleQ2SegreLocal.cofactors, Matrix.adjugate_fin_three,
    Matrix.add_apply, Matrix.sub_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero',
      Matrix.cons_val_succ'] <;> ring

theorem cofactorDifferential_smul (M N : Matrix (Fin 3) (Fin 3) A) (t : A) :
    cofactorDifferential M (t • N) = t • cofactorDifferential M N := by
  ext i j
  simp only [cofactorDifferential, CycleQ2SegreLocal.cofactors, Matrix.adjugate_fin_three,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero',
      Matrix.cons_val_succ'] <;> ring

def cofactorDifferentialLinear (M : Matrix (Fin 3) (Fin 3) A) :
    Matrix (Fin 3) (Fin 3) A →ₗ[A] Matrix (Fin 3) (Fin 3) A where
  toFun := cofactorDifferential M
  map_add' := cofactorDifferential_add M
  map_smul' := fun t N ↦ cofactorDifferential_smul M N t

end Cofactors

variable {R : Type*} [CommRing R]

def rawCofactorQuotient (r : R) : Matrix (Fin 3) (Fin 3) (Poly R) :=
  CycleQ2SegreSeed.rawCofactorQuotient (C r) (X 0) (X 1) (X 2) (X 3) (X 4)

theorem rawSeedMatrix_cofactor (r : R) (i j : Fin 3) :
    CycleQ2SegreLocal.cofactors (rawSeedMatrix r) i j =
      seedG r * rawCofactorQuotient r i j :=
  congrArg (fun M : Matrix (Fin 3) (Fin 3) (Poly R) ↦ M i j)
    (CycleQ2SegreSeed.rawMatrix_cofactor_identity (C r) (X 0) (X 1) (X 2) (X 3) (X 4))

def firstOrderResidual (r ι : R) (H : Poly R)
    (N : Matrix (Fin 3) (Fin 3) (Poly R)) : Matrix (Fin 3) (Fin 3) (Poly R) :=
  fun i j ↦ cofactorDifferential (rawSeedMatrix r) N i j +
    H * smoothK ι * rawCofactorQuotient r i j

/-- The plus sign in `Dcof + H*k*Q` follows from the actual seed identity
`Cof(Mraw)=G*Q` and the actual equation `F=G+h*k`. -/
theorem cofactor_seed_deformation (r ι : R) (H t : Poly R)
    (N : Matrix (Fin 3) (Fin 3) (Poly R)) (i j : Fin 3) :
    CycleQ2SegreLocal.cofactors (fun i j ↦ rawSeedMatrix r i j + t * N i j) i j =
      -(smoothK ι * rawCofactorQuotient r i j) * (smoothH ι + t * H) +
        rawCofactorQuotient r i j * smoothF r ι +
        t * firstOrderResidual r ι H N i j +
        t ^ 2 * CycleQ2SegreLocal.cofactors N i j := by
  rw [cofactor_quadratic, rawSeedMatrix_cofactor]
  unfold firstOrderResidual smoothF
  ring

theorem smoothSeed_mem_iff_linkage {p : Poly R} (r ι : R) :
    p ∈ equationsIdeal (smoothH ι) (smoothF r ι) ↔
      ∃ a b : Poly R, a * smoothH ι + b * seedG r = p := by
  rw [equationsIdeal, Ideal.mem_span_pair]
  constructor
  · rintro ⟨a, b, hab⟩
    refine ⟨a + b * smoothK ι, b, ?_⟩
    rw [← hab]
    unfold smoothF
    ring
  · rintro ⟨a, b, hab⟩
    refine ⟨a - b * smoothK ι, b, ?_⟩
    rw [← hab]
    unfold smoothF
    ring

theorem firstOrderResidual_vanishes_iff [Nontrivial R]
    (r ι : R) (H : Poly R) (N : Matrix (Fin 3) (Fin 3) (Poly R)) (i j : Fin 3) :
    fullRemainder (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
      (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι)
      (firstOrderResidual r ι H N i j) = 0 ↔
      ∃ a b : Poly R, a * smoothH ι + b * seedG r = firstOrderResidual r ι H N i j := by
  rw [fullRemainder_eq_zero_iff, seedCubicCoefficients_polynomial,
    seedSexticCoefficients_polynomial, smoothSeed_mem_iff_linkage]

theorem infinitesimal_cofactor_mem (r ι : R) (H t : Poly R)
    (N : Matrix (Fin 3) (Fin 3) (Poly R)) (ht : t ^ 2 = 0) (i j : Fin 3)
    (hD : firstOrderResidual r ι H N i j ∈ equationsIdeal (smoothH ι) (smoothF r ι)) :
    CycleQ2SegreLocal.cofactors (fun i j ↦ rawSeedMatrix r i j + t * N i j) i j ∈
      equationsIdeal (smoothH ι + t * H) (smoothF r ι) := by
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hD
  rw [equationsIdeal, Ideal.mem_span_pair, cofactor_seed_deformation, ← hab]
  refine ⟨-(smoothK ι * rawCofactorQuotient r i j) + t * a,
    rawCofactorQuotient r i j + t * b, ?_⟩
  linear_combination (a * H - CycleQ2SegreLocal.cofactors N i j) * ht

def deformedCubicCoefficients (ι t : R) (η : FullInvariantIndex 3 → R) :
    FullInvariantIndex 3 → R := fun e ↦ seedCubicCoefficients ι e + t * η e

theorem deformedCubicCoefficients_polynomial (ι t : R) (η : FullInvariantIndex 3 → R) :
    fullInvariantPolynomial 3 (deformedCubicCoefficients ι t η) =
      smoothH ι + C t * fullInvariantPolynomial 3 η := by
  rw [← seedCubicCoefficients_polynomial]
  simp [fullInvariantPolynomial, deformedCubicCoefficients, map_add,
    Finset.sum_add_distrib, Finset.mul_sum, C_mul_monomial]

theorem deformedCubicCoefficients_unit (ι t : R) (η : FullInvariantIndex 3 → R)
    (ht : t ^ 2 = 0) : IsUnit (deformedCubicCoefficients ι t η fullCubicLeadingIndex) := by
  simp only [deformedCubicCoefficients, seedCubicCoefficients,
    fullCubicLeadingIndex_exponent, smoothH_leading_coefficient]
  apply IsUnit.of_mul_eq_one (1 - t * η fullCubicLeadingIndex)
  calc
    (1 + t * η fullCubicLeadingIndex) * (1 - t * η fullCubicLeadingIndex) =
        1 - t ^ 2 * (η fullCubicLeadingIndex) ^ 2 := by ring
    _ = 1 := by rw [ht]; ring

theorem incidenceMatrix_scaled (r t : R)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) :
    incidenceMatrix r (fun i j e ↦ t * δ i j e) =
      fun i j ↦ rawSeedMatrix r i j + C t * perturbation δ i j := by
  ext i j
  simp [incidenceMatrix, perturbation, Finset.mul_sum, C_mul_monomial]

/-- A vanishing first-order residual gives a genuine square-zero solution of
the already-defined coefficient equations, with its leading unit proved. -/
theorem infinitesimal_incidenceEquations_zero [Nontrivial R]
    (r ι t : R) (ht : t ^ 2 = 0) (η : FullInvariantIndex 3 → R)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → R)
    (hD : ∀ i j, firstOrderResidual r ι (fullInvariantPolynomial 3 η) (perturbation δ) i j ∈
      equationsIdeal (smoothH ι) (smoothF r ι)) (q : EquationIndex) :
    incidenceEquations (deformedCubicCoefficients ι t η) (seedSexticCoefficients r ι)
      (deformedCubicCoefficients_unit ι t η ht) (seedSexticCoefficients_unit r ι)
      r (fun i j e ↦ t * δ i j e) q = 0 := by
  apply (incidenceEquations_zero_iff _ _ _ _ r (fun i j e ↦ t * δ i j e)).mpr _ q
  intro i j
  rw [deformedCubicCoefficients_polynomial, seedSexticCoefficients_polynomial,
    incidenceMatrix_scaled]
  apply infinitesimal_cofactor_mem r ι _ _ _ _ i j (hD i j)
  rw [← map_pow, ht, map_zero]

end CycleQ2IncidenceFirstOrder

#print axioms CycleQ2IncidenceFirstOrder.cofactor_seed_deformation
#print axioms CycleQ2IncidenceFirstOrder.firstOrderResidual_vanishes_iff
#print axioms CycleQ2IncidenceFirstOrder.infinitesimal_incidenceEquations_zero
end
end


/- Component: continuation_3/IncidenceUniversalChart.lean -/
section
/-!
# The concrete localized universal incidence coefficient ring

Every raw cubic coefficient, every raw sextic coefficient, and every matrix
perturbation coefficient is an independent polynomial variable.  The two
leading coefficient variables are genuinely inverted by localization.  The
9522 equations are elements of this ring, with their actual specialization
maps and a proved literal seed.  No polynomial identity is asserted before
imposing the inverse equations or performing this localization.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CycleQ2IncidenceUniversalChart

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations

abbrev MatrixParameter := (Fin 3 × Fin 3) × StandardIndex 14
abbrev ParameterIndex := FullInvariantIndex 3 ⊕ (FullInvariantIndex 6 ⊕ MatrixParameter)
abbrev ParameterPolynomial (R : Type*) [CommRing R] := MvPolynomial ParameterIndex R

def leadingProduct (R : Type*) [CommRing R] : ParameterPolynomial R :=
  X (Sum.inl fullCubicLeadingIndex) * X (Sum.inr (Sum.inl fullSexticLeadingIndex))

theorem leadingProduct_ne_zero (R : Type*) [CommRing R] [IsDomain R] :
    leadingProduct R ≠ 0 := mul_ne_zero (X_ne_zero _) (X_ne_zero _)

abbrev ParameterRing (R : Type*) [CommRing R] := Localization.Away (leadingProduct R)

instance parameterRingDomain (R : Type*) [CommRing R] [IsDomain R] :
    IsDomain (ParameterRing R) := Localization.Away.isDomain (leadingProduct_ne_zero R)

variable (R : Type*) [CommRing R] [IsDomain R]

def cubicCoefficient (e : FullInvariantIndex 3) : ParameterRing R :=
  algebraMap (ParameterPolynomial R) (ParameterRing R) (X (Sum.inl e))

def sexticCoefficient (e : FullInvariantIndex 6) : ParameterRing R :=
  algebraMap (ParameterPolynomial R) (ParameterRing R) (X (Sum.inr (Sum.inl e)))

def matrixCoefficient (i j : Fin 3) (e : StandardIndex 14) : ParameterRing R :=
  algebraMap (ParameterPolynomial R) (ParameterRing R) (X (Sum.inr (Sum.inr ((i, j), e))))

theorem leading_coefficients_units :
    IsUnit (cubicCoefficient R fullCubicLeadingIndex) ∧
      IsUnit (sexticCoefficient R fullSexticLeadingIndex) := by
  have hu := IsLocalization.Away.algebraMap_isUnit (S := ParameterRing R) (leadingProduct R)
  have hp : IsUnit (cubicCoefficient R fullCubicLeadingIndex *
      sexticCoefficient R fullSexticLeadingIndex) := by
    simpa only [leadingProduct, map_mul, cubicCoefficient, sexticCoefficient] using hu
  exact ⟨isUnit_of_mul_isUnit_left hp, isUnit_of_mul_isUnit_right hp⟩

def equations (r : R) : EquationIndex → ParameterRing R :=
  incidenceEquations (cubicCoefficient R) (sexticCoefficient R)
    (leading_coefficients_units R).1 (leading_coefficients_units R).2
    (algebraMap R (ParameterRing R) r) (matrixCoefficient R)

section Specialization

variable {R} {S : Type*} [CommRing S] [Algebra R S]

def coefficientPoint (hcoeff : FullInvariantIndex 3 → S)
    (Fcoeff : FullInvariantIndex 6 → S)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S) : ParameterIndex → S :=
  Sum.elim hcoeff (Sum.elim Fcoeff (fun q => δ q.1.1 q.1.2 q.2))

def polynomialSpecialization (hcoeff : FullInvariantIndex 3 → S)
    (Fcoeff : FullInvariantIndex 6 → S)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S) : ParameterPolynomial R →ₐ[R] S :=
  aeval (coefficientPoint hcoeff Fcoeff δ)

theorem polynomialSpecialization_leadingProduct
    (hcoeff : FullInvariantIndex 3 → S) (Fcoeff : FullInvariantIndex 6 → S)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S) :
    polynomialSpecialization hcoeff Fcoeff δ (leadingProduct R) =
      hcoeff fullCubicLeadingIndex * Fcoeff fullSexticLeadingIndex := by
  simp [polynomialSpecialization, leadingProduct, coefficientPoint]

/-- Every actual coefficient point in the two-leading-coefficient open has
its canonical specialization from the universal localized coefficient ring. -/
def specialization (hcoeff : FullInvariantIndex 3 → S)
    (Fcoeff : FullInvariantIndex 6 → S)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S) : ParameterRing R →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom (leadingProduct R)
    (f := polynomialSpecialization hcoeff Fcoeff δ)
    (by rw [polynomialSpecialization_leadingProduct]; exact hu.mul Fu)

@[simp] theorem specialization_polynomial
    (hcoeff : FullInvariantIndex 3 → S) (Fcoeff : FullInvariantIndex 6 → S)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S) (p : ParameterPolynomial R) :
    specialization hcoeff Fcoeff hu Fu δ
      (algebraMap (ParameterPolynomial R) (ParameterRing R) p) =
        polynomialSpecialization hcoeff Fcoeff δ p := by
  simp [specialization, IsLocalization.Away.liftAlgHom_apply]

@[simp] theorem specialization_cubicCoefficient
    (hcoeff : FullInvariantIndex 3 → S) (Fcoeff : FullInvariantIndex 6 → S)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S) (e : FullInvariantIndex 3) :
    specialization hcoeff Fcoeff hu Fu δ (cubicCoefficient R e) = hcoeff e := by
  simp [specialization, cubicCoefficient, IsLocalization.Away.liftAlgHom_apply,
    polynomialSpecialization, coefficientPoint]

@[simp] theorem specialization_sexticCoefficient
    (hcoeff : FullInvariantIndex 3 → S) (Fcoeff : FullInvariantIndex 6 → S)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S) (e : FullInvariantIndex 6) :
    specialization hcoeff Fcoeff hu Fu δ (sexticCoefficient R e) = Fcoeff e := by
  simp [specialization, sexticCoefficient, IsLocalization.Away.liftAlgHom_apply,
    polynomialSpecialization, coefficientPoint]

@[simp] theorem specialization_matrixCoefficient
    (hcoeff : FullInvariantIndex 3 → S) (Fcoeff : FullInvariantIndex 6 → S)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S)
    (i j : Fin 3) (e : StandardIndex 14) :
    specialization hcoeff Fcoeff hu Fu δ (matrixCoefficient R i j e) = δ i j e := by
  simp [specialization, matrixCoefficient, IsLocalization.Away.liftAlgHom_apply,
    polynomialSpecialization, coefficientPoint]

theorem specialization_equations [Nontrivial S]
    (hcoeff : FullInvariantIndex 3 → S) (Fcoeff : FullInvariantIndex 6 → S)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S) (r : R) (q : EquationIndex) :
    specialization hcoeff Fcoeff hu Fu δ (equations R r q) =
      incidenceEquations hcoeff Fcoeff hu Fu (algebraMap R S r) δ q := by
  let φ := specialization (R := R) hcoeff Fcoeff hu Fu δ
  have hh : φ.toRingHom ∘ cubicCoefficient R = hcoeff := by
    funext e
    exact specialization_cubicCoefficient hcoeff Fcoeff hu Fu δ e
  have hF : φ.toRingHom ∘ sexticCoefficient R = Fcoeff := by
    funext e
    exact specialization_sexticCoefficient hcoeff Fcoeff hu Fu δ e
  have hδ : (fun i j e => φ.toRingHom (matrixCoefficient R i j e)) = δ := by
    funext i j e
    exact specialization_matrixCoefficient hcoeff Fcoeff hu Fu δ i j e
  have hr : φ.toRingHom (algebraMap R (ParameterRing R) r) = algebraMap R S r :=
    φ.commutes r
  have hm := incidenceEquations_map φ.toRingHom
    (cubicCoefficient R) (sexticCoefficient R)
    (leading_coefficients_units R).1 (leading_coefficients_units R).2
    (algebraMap R (ParameterRing R) r) (matrixCoefficient R) q
  change φ.toRingHom (incidenceEquations (cubicCoefficient R) (sexticCoefficient R)
    (leading_coefficients_units R).1 (leading_coefficients_units R).2
    (algebraMap R (ParameterRing R) r) (matrixCoefficient R) q) = _
  simpa only [hh, hF, hδ, hr] using hm

end Specialization

/-- The literal raw smooth seed is an actual point of the universal chart. -/
def seedSpecialization (r ι : R) : ParameterRing R →ₐ[R] R :=
  specialization (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
    (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι)
    (fun _ _ _ => 0)

theorem seedSpecialization_equations (r ι : R) (q : EquationIndex) :
    seedSpecialization R r ι (equations R r q) = 0 := by
  rw [seedSpecialization, specialization_equations]
  simpa using smoothSeed_equations_zero r ι q

end CycleQ2IncidenceUniversalChart

#print axioms CycleQ2IncidenceUniversalChart.leading_coefficients_units
#print axioms CycleQ2IncidenceUniversalChart.specialization_equations
#print axioms CycleQ2IncidenceUniversalChart.seedSpecialization_equations
end
end


