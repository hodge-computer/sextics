import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic

/-! # The Fermat Jacobian ring and the scalar commutant of its Higgs forms -/

set_option Elab.async false

/- Component: higgs/FermatHiggsData.lean -/
section
/-!
Exact monomial data for Chapter 3D's Fermat Higgs forms.
These declarations check finite algebra only, not Hodge-theoretic comparison.
Every finite check below is kernel-reduced `decide`, with no native evaluator.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CycleQ2FermatHiggs

def basisMonomial : Fin 33 → Fin 5 → ℕ := ![
  ![0, 0, 1, 3, 1],
  ![0, 0, 4, 0, 1],
  ![0, 0, 4, 2, 0],
  ![0, 1, 2, 1, 1],
  ![0, 1, 2, 3, 0],
  ![0, 2, 0, 2, 1],
  ![0, 2, 0, 4, 0],
  ![0, 2, 3, 1, 0],
  ![0, 3, 1, 0, 1],
  ![0, 3, 1, 2, 0],
  ![0, 4, 2, 0, 0],
  ![1, 0, 2, 1, 1],
  ![1, 0, 2, 3, 0],
  ![1, 1, 0, 2, 1],
  ![1, 1, 0, 4, 0],
  ![1, 1, 3, 1, 0],
  ![1, 2, 1, 0, 1],
  ![1, 2, 1, 2, 0],
  ![1, 3, 2, 0, 0],
  ![1, 4, 0, 1, 0],
  ![2, 0, 0, 2, 1],
  ![2, 0, 0, 4, 0],
  ![2, 0, 3, 1, 0],
  ![2, 1, 1, 0, 1],
  ![2, 1, 1, 2, 0],
  ![2, 2, 2, 0, 0],
  ![2, 3, 0, 1, 0],
  ![3, 0, 1, 0, 1],
  ![3, 0, 1, 2, 0],
  ![3, 1, 2, 0, 0],
  ![3, 2, 0, 1, 0],
  ![4, 0, 2, 0, 0],
  ![4, 1, 0, 1, 0]]

def tangentMonomial : Fin 35 → Fin 5 → ℕ := ![
  ![0, 0, 0, 4, 1],
  ![0, 0, 3, 1, 1],
  ![0, 0, 3, 3, 0],
  ![0, 1, 1, 2, 1],
  ![0, 1, 1, 4, 0],
  ![0, 1, 4, 1, 0],
  ![0, 2, 2, 0, 1],
  ![0, 2, 2, 2, 0],
  ![0, 3, 0, 1, 1],
  ![0, 3, 0, 3, 0],
  ![0, 3, 3, 0, 0],
  ![0, 4, 1, 1, 0],
  ![1, 0, 1, 2, 1],
  ![1, 0, 1, 4, 0],
  ![1, 0, 4, 1, 0],
  ![1, 1, 2, 0, 1],
  ![1, 1, 2, 2, 0],
  ![1, 2, 0, 1, 1],
  ![1, 2, 0, 3, 0],
  ![1, 2, 3, 0, 0],
  ![1, 3, 1, 1, 0],
  ![2, 0, 2, 0, 1],
  ![2, 0, 2, 2, 0],
  ![2, 1, 0, 1, 1],
  ![2, 1, 0, 3, 0],
  ![2, 1, 3, 0, 0],
  ![2, 2, 1, 1, 0],
  ![2, 4, 0, 0, 0],
  ![3, 0, 0, 1, 1],
  ![3, 0, 0, 3, 0],
  ![3, 0, 3, 0, 0],
  ![3, 1, 1, 1, 0],
  ![3, 3, 0, 0, 0],
  ![4, 0, 1, 1, 0],
  ![4, 2, 0, 0, 0]]

def socle : Fin 5 → ℕ := ![4, 4, 4, 4, 1]

def weightedDegree (a : Fin 5 → ℕ) : ℕ :=
  a 0 + a 1 + a 2 + a 3 + 2 * a 4

def character (a : Fin 5 → ℕ) : ℕ :=
  (2 * a 0 + 2 * a 1 + a 2) % 3

def complement : Fin 35 → Fin 33 → Option (Fin 33) := ![
  ![none, none, none, none, none, none, none, none, none, none, some 31, none, none, none, none, none, none, none, some 29, none, none, none, none, none, none, some 25, none, none, none, some 18, none, some 10, none],
  ![none, none, none, none, none, none, none, none, none, some 32, none, none, none, none, none, none, none, some 30, none, some 28, none, none, none, none, some 26, none, some 24, none, some 19, none, some 17, none, some 9],
  ![none, none, none, none, none, none, none, none, some 32, none, none, none, none, none, none, none, some 30, none, none, some 27, none, none, none, some 26, none, none, some 23, some 19, none, none, some 16, none, some 8],
  ![none, none, none, none, none, none, none, some 32, none, some 31, none, none, none, none, none, some 30, none, some 29, some 28, none, none, none, some 26, none, some 25, some 24, some 22, none, some 18, some 17, some 15, some 9, some 7],
  ![none, none, none, none, none, none, none, none, some 31, none, none, none, none, none, none, none, some 29, none, some 27, none, none, none, none, some 25, none, some 23, none, some 18, none, some 16, none, some 8, none],
  ![none, none, none, none, none, some 32, none, none, none, none, none, none, none, some 30, none, none, none, none, none, none, some 26, none, none, none, none, none, some 20, none, none, none, some 13, none, some 5],
  ![none, none, none, none, some 32, none, some 31, none, none, none, none, none, some 30, none, some 29, none, none, some 28, none, none, none, some 25, none, none, some 24, some 21, none, none, some 17, some 14, some 12, some 6, some 4],
  ![none, none, none, some 32, none, some 31, none, none, none, none, none, some 30, none, some 29, none, none, some 28, some 27, none, none, some 25, none, none, some 24, some 23, some 20, none, some 17, some 16, some 13, some 11, some 5, some 3],
  ![none, none, some 32, none, some 31, none, none, none, none, none, none, none, some 29, none, none, some 28, none, none, none, none, none, none, some 24, none, some 22, none, none, none, some 15, some 12, none, some 4, some 2],
  ![none, some 32, none, some 31, none, none, none, none, none, none, none, some 29, none, none, none, some 27, none, none, none, none, none, none, some 23, some 22, none, none, none, some 15, none, some 11, none, some 3, some 1],
  ![some 32, none, none, none, none, none, none, none, none, none, none, none, none, some 28, some 27, none, none, none, none, none, some 24, some 23, none, some 21, some 20, none, none, some 14, some 13, none, none, none, some 0],
  ![some 31, none, none, none, none, none, none, none, none, none, none, some 28, some 27, none, none, none, none, none, none, none, some 22, none, some 20, none, none, none, none, some 12, some 11, none, none, some 0, none],
  ![none, none, none, none, none, none, none, some 30, none, some 29, some 28, none, none, none, none, some 26, none, some 25, some 24, some 22, none, none, some 19, none, some 18, some 17, some 15, none, some 10, some 9, some 7, none, none],
  ![none, none, none, none, none, none, none, none, some 29, none, some 27, none, none, none, none, none, some 25, none, some 23, none, none, none, none, some 18, none, some 16, none, some 10, none, some 8, none, none, none],
  ![none, none, none, none, none, some 30, none, none, none, none, none, none, none, some 26, none, none, none, none, none, some 20, some 19, none, none, none, none, none, some 13, none, none, none, some 5, none, none],
  ![none, none, none, none, some 30, none, some 29, none, none, some 28, none, none, some 26, none, some 25, none, none, some 24, some 21, none, none, some 18, none, none, some 17, some 14, some 12, none, some 9, some 6, some 4, none, none],
  ![none, none, none, some 30, none, some 29, none, none, some 28, some 27, none, some 26, none, some 25, none, none, some 24, some 23, some 20, none, some 18, none, none, some 17, some 16, some 13, some 11, some 9, some 8, some 5, some 3, none, none],
  ![none, none, some 30, none, some 29, none, none, some 28, none, none, none, none, some 25, none, none, some 24, none, some 22, none, none, none, none, some 17, none, some 15, some 12, none, none, some 7, some 4, some 2, none, none],
  ![none, some 30, none, some 29, none, none, none, some 27, none, none, none, some 25, none, none, none, some 23, some 22, none, none, none, none, none, some 16, some 15, none, some 11, none, some 7, none, some 3, some 1, none, none],
  ![some 30, none, none, none, none, some 28, some 27, none, none, none, none, none, none, some 24, some 23, none, some 21, some 20, none, none, some 17, some 16, none, some 14, some 13, none, none, some 6, some 5, none, some 0, none, none],
  ![some 29, none, none, some 28, some 27, none, none, none, none, none, none, some 24, some 23, some 22, none, some 20, none, none, none, none, some 15, none, some 13, some 12, some 11, none, none, some 4, some 3, some 0, none, none, none],
  ![none, none, none, none, some 26, none, some 25, none, none, some 24, some 21, none, some 19, none, some 18, none, none, some 17, some 14, some 12, none, some 10, none, none, some 9, some 6, some 4, none, none, none, none, none, none],
  ![none, none, none, some 26, none, some 25, none, none, some 24, some 23, some 20, some 19, none, some 18, none, none, some 17, some 16, some 13, some 11, some 10, none, none, some 9, some 8, some 5, some 3, none, none, none, none, none, none],
  ![none, none, some 26, none, some 25, none, none, some 24, none, some 22, none, none, some 18, none, none, some 17, none, some 15, some 12, none, none, none, some 9, none, some 7, some 4, some 2, none, none, none, none, none, none],
  ![none, some 26, none, some 25, none, none, none, some 23, some 22, none, none, some 18, none, none, none, some 16, some 15, none, some 11, none, none, none, some 8, some 7, none, some 3, some 1, none, none, none, none, none, none],
  ![some 26, none, none, none, none, some 24, some 23, none, some 21, some 20, none, none, none, some 17, some 16, none, some 14, some 13, none, none, some 9, some 8, none, some 6, some 5, none, some 0, none, none, none, none, none, none],
  ![some 25, none, none, some 24, some 23, some 22, none, some 20, none, none, none, some 17, some 16, some 15, none, some 13, some 12, some 11, none, none, some 7, none, some 5, some 4, some 3, some 0, none, none, none, none, none, none, none],
  ![some 22, some 21, some 20, none, none, none, none, none, none, none, none, some 12, some 11, none, none, none, none, none, none, none, some 2, some 1, some 0, none, none, none, none, none, none, none, none, none, none],
  ![none, none, some 19, none, some 18, none, none, some 17, none, some 15, some 12, none, some 10, none, none, some 9, none, some 7, some 4, some 2, none, none, none, none, none, none, none, none, none, none, none, none, none],
  ![none, some 19, none, some 18, none, none, none, some 16, some 15, none, some 11, some 10, none, none, none, some 8, some 7, none, some 3, some 1, none, none, none, none, none, none, none, none, none, none, none, none, none],
  ![some 19, none, none, none, none, some 17, some 16, none, some 14, some 13, none, none, none, some 9, some 8, none, some 6, some 5, none, some 0, none, none, none, none, none, none, none, none, none, none, none, none, none],
  ![some 18, none, none, some 17, some 16, some 15, none, some 13, some 12, some 11, none, some 9, some 8, some 7, none, some 5, some 4, some 3, some 0, none, none, none, none, none, none, none, none, none, none, none, none, none, none],
  ![some 15, some 14, some 13, some 12, some 11, none, none, none, none, none, none, some 4, some 3, some 2, some 1, some 0, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none],
  ![some 10, none, none, some 9, some 8, some 7, none, some 5, some 4, some 3, some 0, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none],
  ![some 7, some 6, some 5, some 4, some 3, some 2, some 1, some 0, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]]

theorem basis_properties : ∀ i : Fin 33,
    weightedDegree (basisMonomial i) = 6 ∧ character (basisMonomial i) = 1 ∧
      ∀ k, basisMonomial i k ≤ socle k := by
  decide

theorem tangent_properties : ∀ m : Fin 35,
    weightedDegree (tangentMonomial m) = 6 ∧ character (tangentMonomial m) = 0 ∧
      ∀ k, tangentMonomial m k ≤ socle k := by
  decide

theorem basis_injective : Function.Injective basisMonomial := by
  decide

theorem tangent_injective : Function.Injective tangentMonomial := by
  decide

theorem basis_complete : ∀ a b c d : Fin 5, ∀ w : Fin 2,
    let v : Fin 5 → ℕ := ![a.val, b.val, c.val, d.val, w.val]
    weightedDegree v = 6 → character v = 1 → ∃ i, basisMonomial i = v := by
  intro a
  fin_cases a <;> decide +kernel

theorem tangent_complete : ∀ a b c d : Fin 5, ∀ w : Fin 2,
    let v : Fin 5 → ℕ := ![a.val, b.val, c.val, d.val, w.val]
    weightedDegree v = 6 → character v = 0 → ∃ m, tangentMonomial m = v := by
  intro a
  fin_cases a <;> decide +kernel

def ComplementRow (m : Fin 35) (i : Fin 33) : Prop :=
    match complement m i with
    | some j => ∀ k : Fin 5,
        basisMonomial i k + basisMonomial j k + tangentMonomial m k = socle k
    | none => ∃ k : Fin 5, socle k < basisMonomial i k + tangentMonomial m k

instance (m : Fin 35) (i : Fin 33) : Decidable (ComplementRow m i) := by
  unfold ComplementRow
  split <;> infer_instance

/-- Each nonempty complement is correct; an empty one exceeds the socle
in at least one coordinate. This checks 35 * 33 small cases. -/
theorem complement_row : ∀ m : Fin 35, ∀ i : Fin 33, ComplementRow m i := by
  intro m
  fin_cases m <;> decide +kernel

theorem complement_spec : ∀ m : Fin 35, ∀ i j : Fin 33,
    complement m i = some j ↔
      ∀ k : Fin 5, basisMonomial i k + basisMonomial j k + tangentMonomial m k =
        socle k := by
  intro m i j
  have hr := complement_row m i
  unfold ComplementRow at hr
  cases hc : complement m i with
  | none =>
      simp only [hc] at hr
      constructor
      · intro h
        cases h
      · intro hs
        obtain ⟨k, hk⟩ := hr
        have hh := hs k
        omega
  | some r =>
      simp only [hc] at hr
      constructor
      · intro h
        have he : r = j := Option.some.inj h
        subst r
        exact hr
      · intro hs
        have he : basisMonomial r = basisMonomial j := by
          funext k
          have h1 := hr k
          have h2 := hs k
          omega
        exact congrArg some (basis_injective he)

theorem complement_symm (m : Fin 35) (i j : Fin 33) :
    complement m i = some j ↔ complement m j = some i := by
  rw [complement_spec, complement_spec]
  simp only [Nat.add_comm (basisMonomial i _) (basisMonomial j _)]

def higgsMatrix (K : Type*) [Zero K] [One K] (m : Fin 35) :
    Matrix (Fin 33) (Fin 33) K :=
  fun i j => if complement m i = some j then 1 else 0

theorem higgsMatrix_socle (K : Type*) [Zero K] [One K]
    (m : Fin 35) (i j : Fin 33) :
    higgsMatrix K m i j =
      if (∀ k : Fin 5, basisMonomial i k + basisMonomial j k +
          tangentMonomial m k = socle k) then 1 else 0 := by
  simp only [higgsMatrix, complement_spec]

end CycleQ2FermatHiggs

#print axioms CycleQ2FermatHiggs.complement_spec
#print axioms CycleQ2FermatHiggs.basis_complete
end


/- Component: higgs/FermatHiggs.lean -/
section
/-!
The 35 Fermat Higgs forms have only scalar compatible endomorphisms.
Each off-diagonal entry vanishes because one Higgs matrix pairs its row
and leaves its column unpaired. Diagonal entries agree along each pairing,
and every index reaches index zero in at most two pairings.
-/

namespace CycleQ2FermatHiggs
open scoped BigOperators

def entryConstraints {K : Type*} [Zero K] (P : Matrix (Fin 33) (Fin 33) K) : Prop :=
  ∀ m : Fin 35, ∀ i j : Fin 33,
    (match complement m j with | none => 0 | some k => P k i) =
    (match complement m i with | none => 0 | some k => P k j)

/-- Given distinct indices, some Higgs matrix pairs the first index and
leaves the second unpaired. -/
private theorem separates_entries : ∀ i j : Fin 33, i ≠ j →
    ∃ m : Fin 35, (complement m i).isSome ∧ complement m j = none := by
  intro i
  fin_cases i <;> decide +kernel

private abbrev adjacentToZero (i : Fin 33) : Prop :=
  ∃ m : Fin 35, complement m i = some 0

/-- The graph pairing basis indices through the Higgs matrices has radius
at most two about index zero. -/
private theorem diagonal_reachable : ∀ i : Fin 33, i = 0 ∨ adjacentToZero i ∨
    ∃ m : Fin 35, ∃ j : Fin 33, complement m i = some j ∧ adjacentToZero j := by
  intro i
  fin_cases i <;> decide +kernel

theorem scalar_of_entryConstraints {K : Type*} [Zero K]
    (P : Matrix (Fin 33) (Fin 33) K) (h : entryConstraints P) :
    ∃ c : K, ∀ i j, P i j = if i = j then c else 0 := by
  have edge (m : Fin 35) (i j : Fin 33) (hij : complement m i = some j) :
      P i i = P j j := by
    simpa only [hij, (complement_symm m i j).mp hij] using h m i j
  have near (i : Fin 33) (hi : adjacentToZero i) : P i i = P 0 0 := by
    obtain ⟨m, hm⟩ := hi
    exact edge m i 0 hm
  refine ⟨P 0 0, fun i j => ?_⟩
  split_ifs with hij
  · subst j
    rcases diagonal_reachable i with rfl | hi | ⟨m, j, hj, hnear⟩
    · rfl
    · exact near i hi
    · exact (edge m i j hj).trans (near j hnear)
  · obtain ⟨m, hi, hj⟩ := separates_entries i j hij
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hi
    simpa only [(complement_symm m i k).mp hk, hj] using h m j k


theorem transpose_mul_higgs_apply {K : Type*} [Semiring K]
    (P : Matrix (Fin 33) (Fin 33) K) (m : Fin 35) (i j : Fin 33) :
    (P.transpose * higgsMatrix K m) i j =
      (match complement m j with | none => 0 | some k => P k i) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, higgsMatrix]
  simp_rw [complement_symm m _ j]
  cases hc : complement m j with
  | none => simp [hc]
  | some k => simp [hc, eq_comm]

theorem higgs_mul_apply {K : Type*} [Semiring K]
    (P : Matrix (Fin 33) (Fin 33) K) (m : Fin 35) (i j : Fin 33) :
    (higgsMatrix K m * P) i j =
      (match complement m i with | none => 0 | some k => P k j) := by
  simp only [Matrix.mul_apply, higgsMatrix]
  cases hc : complement m i with
  | none => simp [hc]
  | some k => simp [hc, eq_comm]

theorem scalar_of_higgs_equations {K : Type*} [Semiring K]
    (P : Matrix (Fin 33) (Fin 33) K)
    (h : ∀ m : Fin 35, P.transpose * higgsMatrix K m = higgsMatrix K m * P) :
    ∃ c : K, ∀ i j, P i j = if i = j then c else 0 := by
  apply scalar_of_entryConstraints P
  intro m i j
  have he := congrArg (fun M : Matrix (Fin 33) (Fin 33) K => M i j) (h m)
  simpa only [transpose_mul_higgs_apply, higgs_mul_apply] using he

/-- The compatible idempotents are exactly zero and the identity. Turning
a geometric subvariation into such a matrix remains a separate theorem. -/
theorem compatible_projector_trivial {K : Type*} [Field K]
    (P : Matrix (Fin 33) (Fin 33) K)
    (h : ∀ m : Fin 35, P.transpose * higgsMatrix K m = higgsMatrix K m * P)
    (hP : P * P = P) : P = 0 ∨ P = 1 := by
  obtain ⟨c, hc⟩ := scalar_of_higgs_equations P h
  have hm : (P * P) 0 0 = c * c := by
    simp [Matrix.mul_apply, hc, eq_comm]
  have he : c * c = c := by
    have ht := congrArg (fun M : Matrix (Fin 33) (Fin 33) K => M 0 0) hP
    simpa only [hm, hc 0 0, ite_true] using ht
  have hz : c * (c - 1) = 0 := by
    rw [mul_sub, mul_one, he, sub_self]
  rcases mul_eq_zero.mp hz with hzero | hone
  · left
    ext i j
    simpa only [hzero, ite_self, Matrix.zero_apply] using hc i j
  · right
    have hc1 : c = 1 := sub_eq_zero.mp hone
    ext i j
    simpa only [hc1, Matrix.one_apply] using hc i j

end CycleQ2FermatHiggs

#print axioms CycleQ2FermatHiggs.scalar_of_higgs_equations
#print axioms CycleQ2FermatHiggs.compatible_projector_trivial
end


/- Component: jacobian/FermatJacobian.lean -/
section
/-!
# The actual weighted Fermat Jacobian algebra

The coefficient functionals and the socle pairing in this file descend from
the polynomial ring to its actual Jacobian quotient. They are not supplied
as abstract pairing hypotheses. The comparison with geometric Hodge theory
remains a different assertion.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace CycleQ2FermatJacobian

open MvPolynomial
open CycleQ2FermatHiggs

abbrev Poly := MvPolynomial (Fin 5) ℂ
abbrev Exp := Fin 5 →₀ ℕ

def exponent (a : Fin 5 → ℕ) : Exp := Finsupp.equivFunOnFinite.symm a

@[simp] theorem exponent_apply (a : Fin 5 → ℕ) (i : Fin 5) : exponent a i = a i := rfl

def cutoff (i : Fin 5) : ℕ := socle i + 1
def fermat : Poly := X 0 ^ 6 + X 1 ^ 6 + X 2 ^ 6 + X 3 ^ 6 + X 4 ^ 3
def generator (i : Fin 5) : Poly := X i ^ cutoff i
def derivativeScalar (i : Fin 5) : ℂ := if i = 4 then 3 else 6
def jacobianIdeal : Ideal Poly := Ideal.span (Set.range fun i => pderiv i fermat)
def powerIdeal : Ideal Poly := Ideal.span (Set.range generator)

theorem derivative_eq (i : Fin 5) :
    pderiv i fermat = C (derivativeScalar i) * generator i := by
  fin_cases i <;>
    norm_num [fermat, derivativeScalar, generator, cutoff, socle, Pi.single_apply,
      Fin.ext_iff, map_ofNat] <;> ring <;> rfl

theorem derivativeScalar_ne_zero (i : Fin 5) : derivativeScalar i ≠ 0 := by
  unfold derivativeScalar
  split <;> norm_num

theorem jacobianIdeal_eq_powerIdeal : jacobianIdeal = powerIdeal := by
  apply le_antisymm
  · rw [jacobianIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change pderiv i fermat ∈ powerIdeal
    rw [derivative_eq]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rw [powerIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have hi : pderiv i fermat ∈ jacobianIdeal := Ideal.subset_span ⟨i, rfl⟩
    have hs := Ideal.mul_mem_left jacobianIdeal (C ((derivativeScalar i)⁻¹)) hi
    rw [derivative_eq, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (derivativeScalar_ne_zero i),
      map_one, one_mul] at hs
    exact hs

theorem powerIdeal_eq_monomialIdeal : powerIdeal =
    Ideal.span ((fun d : Exp => monomial d (1 : ℂ)) ''
      Set.range (fun i : Fin 5 => Finsupp.single i (cutoff i))) := by
  unfold powerIdeal
  congr 1
  ext p
  simp only [Set.mem_range, Set.mem_image, generator, X_pow_eq_monomial]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩

/-- An exact membership criterion in the ideal generated by the five actual
partial derivatives. -/
theorem mem_jacobianIdeal_iff (p : Poly) : p ∈ jacobianIdeal ↔
    ∀ d ∈ p.support, ∃ i : Fin 5, socle i < d i := by
  rw [jacobianIdeal_eq_powerIdeal, powerIdeal_eq_monomialIdeal,
    mem_ideal_span_monomial_image]
  simp only [Set.mem_range, exists_exists_eq_and, Finsupp.single_le_iff, cutoff,
    Nat.succ_le_iff]

def bounded : Set Exp := {d | ∀ i, d i ≤ socle i}
abbrev BoundedExp := bounded

theorem bounded_coeff_zero_of_mem {p : Poly} (hp : p ∈ jacobianIdeal)
    {d : Exp} (hd : d ∈ bounded) : coeff d p = 0 := by
  by_contra hc
  obtain ⟨i, hi⟩ := (mem_jacobianIdeal_iff p).mp hp d (mem_support_iff.mpr hc)
  exact (not_lt_of_ge (hd i)) hi

theorem mem_jacobianIdeal_iff_bounded_coeff_zero (p : Poly) :
    p ∈ jacobianIdeal ↔ ∀ d ∈ bounded, coeff d p = 0 := by
  constructor
  · exact fun hp d hd => bounded_coeff_zero_of_mem hp hd
  · intro hp
    apply (mem_jacobianIdeal_iff p).mpr
    intro d hd
    by_contra h
    push Not at h
    have hz := hp d (by simpa only [bounded, Set.mem_ofPred_eq, not_lt] using h)
    exact (mem_support_iff.mp hd) hz

abbrev JacobianRing := Poly ⧸ jacobianIdeal

def quotientMap : Poly →ₐ[ℂ] JacobianRing := Ideal.Quotient.mkₐ ℂ jacobianIdeal

/-- Coefficients inside the exponent box descend to the true Jacobian ring. -/
def quotientCoeff (d : BoundedExp) : JacobianRing →ₗ[ℂ] ℂ :=
  (jacobianIdeal.restrictScalars ℂ).liftQ (lcoeff ℂ d.val) (by
    intro p hp
    exact bounded_coeff_zero_of_mem hp d.property)

@[simp] theorem quotientCoeff_mk (d : BoundedExp) (p : Poly) :
    quotientCoeff d (quotientMap p) = coeff d.val p := rfl

def socleTrace : JacobianRing →ₗ[ℂ] ℂ :=
  quotientCoeff ⟨exponent socle, fun _ => le_rfl⟩

@[simp] theorem socleTrace_mk (p : Poly) :
    socleTrace (quotientMap p) = coeff (exponent socle) p := rfl

def monomialClass (a : Fin 5 → ℕ) : JacobianRing :=
  quotientMap (monomial (exponent a) 1)

theorem exponent_add (a b : Fin 5 → ℕ) :
    exponent a + exponent b = exponent (fun i => a i + b i) := by
  ext i
  rfl

/-- The socle trace of a triple product in the actual quotient is precisely
the exponent-sum test used to construct the finite Higgs matrices. -/
theorem socleTrace_triple_monomial (a b c : Fin 5 → ℕ) :
    socleTrace (monomialClass a * monomialClass b * monomialClass c) =
      if (∀ i, a i + b i + c i = socle i) then 1 else 0 := by
  classical
  rw [monomialClass, monomialClass, monomialClass, ← map_mul, ← map_mul,
    socleTrace_mk, monomial_mul, monomial_mul, one_mul, one_mul, coeff_monomial]
  congr 1
  apply propext
  constructor
  · intro h i
    exact congrArg (fun d : Exp => d i) h
  · intro h
    ext i
    exact h i

/-- This is a literal equality with the already checked finite matrix, not
an assumption naming an unspecified residue pairing. -/
theorem socleTrace_triple_eq_higgsMatrix (m : Fin 35) (i j : Fin 33) :
    socleTrace (monomialClass (basisMonomial i) * monomialClass (basisMonomial j) *
      monomialClass (tangentMonomial m)) = higgsMatrix ℂ m i j := by
  rw [socleTrace_triple_monomial, higgsMatrix_socle]

end CycleQ2FermatJacobian

#print axioms CycleQ2FermatJacobian.jacobianIdeal_eq_powerIdeal
#print axioms CycleQ2FermatJacobian.mem_jacobianIdeal_iff
#print axioms CycleQ2FermatJacobian.socleTrace_triple_eq_higgsMatrix
end
end


/- Component: jacobian/FermatJacobianBasis.lean -/
section
/-!
# Monomial basis of the actual Fermat Jacobian quotient

The normal form is constructed by retaining bounded coefficients. Its kernel
is proved to be the derivative ideal, so the basis below is a basis of the
actual quotient rather than a separately introduced finite algebra.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace CycleQ2FermatJacobian
open MvPolynomial
open CycleQ2FermatHiggs

def normalForm : Poly →ₗ[ℂ] (BoundedExp →₀ ℂ) :=
  (Finsupp.lsubtypeDomain bounded).comp
    (MvPolynomial.basisMonomials (Fin 5) ℂ).repr.toLinearMap

@[simp] theorem normalForm_apply (p : Poly) (d : BoundedExp) :
    normalForm p d = coeff d.val p := rfl

theorem normalForm_surjective : Function.Surjective normalForm := by
  classical
  intro f
  refine ⟨(MvPolynomial.basisMonomials (Fin 5) ℂ).repr.symm f.extendDomain, ?_⟩
  change Finsupp.subtypeDomain (fun x => x ∈ bounded)
    ((MvPolynomial.basisMonomials (Fin 5) ℂ).repr
      ((MvPolynomial.basisMonomials (Fin 5) ℂ).repr.symm f.extendDomain)) = f
  rw [LinearEquiv.apply_symm_apply, Finsupp.subtypeDomain_extendDomain]

theorem normalForm_ker :
    LinearMap.ker normalForm = jacobianIdeal.restrictScalars ℂ := by
  ext p
  rw [LinearMap.mem_ker, Finsupp.ext_iff]
  change (∀ d : BoundedExp, coeff d.val p = 0) ↔ p ∈ jacobianIdeal
  rw [mem_jacobianIdeal_iff_bounded_coeff_zero]
  exact Subtype.forall

/-- Unique bounded monomial coordinates in the actual Jacobian quotient. -/
def normalCoordinates : JacobianRing ≃ₗ[ℂ] (BoundedExp →₀ ℂ) :=
  (Submodule.quotEquivOfEq (jacobianIdeal.restrictScalars ℂ)
    (LinearMap.ker normalForm) normalForm_ker.symm).trans
      (normalForm.quotKerEquivOfSurjective normalForm_surjective)

@[simp] theorem normalCoordinates_mk (p : Poly) :
    normalCoordinates (quotientMap p) = normalForm p := rfl

/-- The classes of every monomial within the derivative exponent bounds form
a basis of the quotient over the complex numbers. -/
def quotientBasis : Module.Basis BoundedExp ℂ JacobianRing :=
  (Finsupp.basisSingleOne : Module.Basis BoundedExp ℂ (BoundedExp →₀ ℂ)).map
    normalCoordinates.symm

@[simp] theorem normalForm_monomial (d : BoundedExp) :
    normalForm (monomial d.val 1) = Finsupp.single d 1 := by
  classical
  ext e
  simp only [normalForm_apply, coeff_monomial, Finsupp.single_apply]
  congr 1
  exact propext Subtype.ext_iff.symm

theorem quotientBasis_eq_monomialClass (d : BoundedExp) :
    quotientBasis d = quotientMap (monomial d.val 1) := by
  apply normalCoordinates.injective
  simp [quotientBasis]

theorem boundedMonomials_linearIndependent :
    LinearIndependent ℂ (fun d : BoundedExp => quotientMap (monomial d.val 1)) := by
  simpa only [← quotientBasis_eq_monomialClass] using quotientBasis.linearIndependent

theorem boundedMonomials_span :
    Submodule.span ℂ (Set.range fun d : BoundedExp =>
      quotientMap (monomial d.val 1)) = ⊤ := by
  simpa only [← quotientBasis_eq_monomialClass] using quotientBasis.span_eq

/-- The exponent box has four side lengths five and one side length two. -/
def boundedExponentEquiv : BoundedExp ≃ (∀ i : Fin 5, Fin (cutoff i)) where
  toFun d i := ⟨d.val i, Nat.lt_succ_of_le (d.property i)⟩
  invFun a := ⟨exponent (fun i => (a i).val), fun i => Nat.le_of_lt_succ (a i).isLt⟩
  left_inv d := by
    apply Subtype.ext
    ext i
    rfl
  right_inv a := by
    funext i
    apply Fin.ext
    rfl

theorem boundedExponent_card : Nat.card BoundedExp = 1250 := by
  rw [Nat.card_congr boundedExponentEquiv, Nat.card_eq_fintype_card, Fintype.card_pi]
  norm_num [cutoff, socle, Fin.prod_univ_succ]

theorem jacobian_finrank : Module.finrank ℂ JacobianRing = 1250 := by
  rw [Module.finrank_eq_nat_card_basis quotientBasis, boundedExponent_card]

def basisIndex (i : Fin 33) : BoundedExp :=
  ⟨exponent (basisMonomial i), (basis_properties i).2.2⟩

def tangentIndex (m : Fin 35) : BoundedExp :=
  ⟨exponent (tangentMonomial m), (tangent_properties m).2.2⟩

theorem basisIndex_injective : Function.Injective basisIndex := by
  intro i j h
  apply basis_injective
  funext k
  exact congrArg (fun d : BoundedExp => d.val k) h

theorem tangentIndex_injective : Function.Injective tangentIndex := by
  intro i j h
  apply tangent_injective
  funext k
  exact congrArg (fun d : BoundedExp => d.val k) h

theorem basisMonomialClass_linearIndependent :
    LinearIndependent ℂ (fun i : Fin 33 => monomialClass (basisMonomial i)) :=
  boundedMonomials_linearIndependent.comp basisIndex basisIndex_injective

theorem tangentMonomialClass_linearIndependent :
    LinearIndependent ℂ (fun m : Fin 35 => monomialClass (tangentMonomial m)) :=
  boundedMonomials_linearIndependent.comp tangentIndex tangentIndex_injective

end CycleQ2FermatJacobian

#print axioms CycleQ2FermatJacobian.normalCoordinates
#print axioms CycleQ2FermatJacobian.quotientBasis_eq_monomialClass
#print axioms CycleQ2FermatJacobian.boundedMonomials_linearIndependent
#print axioms CycleQ2FermatJacobian.boundedMonomials_span
#print axioms CycleQ2FermatJacobian.jacobian_finrank
#print axioms CycleQ2FermatJacobian.basisMonomialClass_linearIndependent
#print axioms CycleQ2FermatJacobian.tangentMonomialClass_linearIndependent
end
end


/- Component: jacobian/FermatJacobianGraded.lean -/
section
/-!
# The actual degree-six character components

These components are images of polynomial support subspaces under the actual
Jacobian quotient map. The finite lists are proved to span those components;
their independence comes from the normal-form theorem for the quotient.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace CycleQ2FermatJacobian
open MvPolynomial
open CycleQ2FermatHiggs

def pieceSupport (n χ : ℕ) : Set Exp :=
  {d | weightedDegree d = n ∧ character d = χ}

def gradedPiece (n χ : ℕ) : Submodule ℂ JacobianRing :=
  Submodule.map quotientMap.toLinearMap (restrictSupport ℂ (pieceSupport n χ))

theorem unbounded_monomial_eq_zero (d : Exp) (hd : d ∉ bounded) :
    quotientMap (monomial d 1) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply (mem_jacobianIdeal_iff_bounded_coeff_zero _).mpr
  intro e he
  have hde : d ≠ e := by
    intro h
    exact hd (h ▸ he)
  simp [coeff_monomial, hde]

theorem bounded_exponent_tuple (d : Exp) (hd : d ∈ bounded) :
    ∃ a b c e : Fin 5, ∃ w : Fin 2,
      (d : Fin 5 → ℕ) = ![a.val, b.val, c.val, e.val, w.val] := by
  have h0 : d 0 < 5 := by simpa [socle] using Nat.lt_succ_of_le (hd 0)
  have h1 : d 1 < 5 := by simpa [socle] using Nat.lt_succ_of_le (hd 1)
  have h2 : d 2 < 5 := by simpa [socle] using Nat.lt_succ_of_le (hd 2)
  have h3 : d 3 < 5 := by simpa [socle] using Nat.lt_succ_of_le (hd 3)
  have h4 : d 4 < 2 := by simpa [socle] using Nat.lt_succ_of_le (hd 4)
  refine ⟨⟨d 0, h0⟩, ⟨d 1, h1⟩, ⟨d 2, h2⟩, ⟨d 3, h3⟩, ⟨d 4, h4⟩, ?_⟩
  funext i
  fin_cases i <;> rfl

theorem basis_complete_bounded (d : Exp) (hb : d ∈ bounded)
    (hn : weightedDegree d = 6) (hc : character d = 1) :
    ∃ i : Fin 33, exponent (basisMonomial i) = d := by
  obtain ⟨a, b, c, e, w, h⟩ := bounded_exponent_tuple d hb
  obtain ⟨i, hi⟩ := basis_complete a b c e w (h ▸ hn) (h ▸ hc)
  refine ⟨i, ?_⟩
  ext k
  exact congrFun (hi.trans h.symm) k

theorem tangent_complete_bounded (d : Exp) (hb : d ∈ bounded)
    (hn : weightedDegree d = 6) (hc : character d = 0) :
    ∃ m : Fin 35, exponent (tangentMonomial m) = d := by
  obtain ⟨a, b, c, e, w, h⟩ := bounded_exponent_tuple d hb
  obtain ⟨m, hm⟩ := tangent_complete a b c e w (h ▸ hn) (h ▸ hc)
  refine ⟨m, ?_⟩
  ext k
  exact congrFun (hm.trans h.symm) k

theorem gradedPiece_eq_span_of_enumeration {ι : Type} (a : ι → Fin 5 → ℕ)
    (n χ : ℕ) (hprop : ∀ i, weightedDegree (a i) = n ∧ character (a i) = χ)
    (hcomplete : ∀ d ∈ bounded, weightedDegree d = n → character d = χ →
      ∃ i, exponent (a i) = d) :
    gradedPiece n χ = Submodule.span ℂ (Set.range fun i => monomialClass (a i)) := by
  classical
  rw [gradedPiece, restrictSupport_eq_span, Submodule.map_span, Set.image_image]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro q ⟨d, hd, rfl⟩
    change quotientMap (monomial d 1) ∈ _
    by_cases hb : d ∈ bounded
    · obtain ⟨i, hi⟩ := hcomplete d hb hd.1 hd.2
      apply Submodule.subset_span
      refine ⟨i, ?_⟩
      change quotientMap (monomial (exponent (a i)) 1) = quotientMap (monomial d 1)
      rw [hi]
    · rw [unbounded_monomial_eq_zero d hb]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro q ⟨i, rfl⟩
    apply Submodule.subset_span
    exact ⟨exponent (a i), hprop i, rfl⟩

theorem degreeSixCharacterOne_eq_span :
    gradedPiece 6 1 = Submodule.span ℂ
      (Set.range fun i : Fin 33 => monomialClass (basisMonomial i)) :=
  gradedPiece_eq_span_of_enumeration basisMonomial 6 1
    (fun i => ⟨(basis_properties i).1, (basis_properties i).2.1⟩)
    basis_complete_bounded

theorem degreeSixCharacterZero_eq_span :
    gradedPiece 6 0 = Submodule.span ℂ
      (Set.range fun m : Fin 35 => monomialClass (tangentMonomial m)) :=
  gradedPiece_eq_span_of_enumeration tangentMonomial 6 0
    (fun m => ⟨(tangent_properties m).1, (tangent_properties m).2.1⟩)
    tangent_complete_bounded

def degreeSixCharacterOneBasis : Module.Basis (Fin 33) ℂ (gradedPiece 6 1) :=
  (Module.Basis.span basisMonomialClass_linearIndependent).map
    (LinearEquiv.ofEq _ _ degreeSixCharacterOne_eq_span.symm)

def degreeSixCharacterZeroBasis : Module.Basis (Fin 35) ℂ (gradedPiece 6 0) :=
  (Module.Basis.span tangentMonomialClass_linearIndependent).map
    (LinearEquiv.ofEq _ _ degreeSixCharacterZero_eq_span.symm)

theorem degreeSixCharacterOne_finrank : Module.finrank ℂ (gradedPiece 6 1) = 33 := by
  rw [Module.finrank_eq_card_basis degreeSixCharacterOneBasis]
  rfl

theorem degreeSixCharacterZero_finrank : Module.finrank ℂ (gradedPiece 6 0) = 35 := by
  rw [Module.finrank_eq_card_basis degreeSixCharacterZeroBasis]
  rfl

theorem degreeSixCharacterOneBasis_coe (i : Fin 33) :
    (degreeSixCharacterOneBasis i : JacobianRing) = monomialClass (basisMonomial i) := by
  simp [degreeSixCharacterOneBasis]

theorem degreeSixCharacterZeroBasis_coe (m : Fin 35) :
    (degreeSixCharacterZeroBasis m : JacobianRing) = monomialClass (tangentMonomial m) := by
  simp [degreeSixCharacterZeroBasis]

/-- The checked finite matrices are the trace matrices on the actual
degree-six character components of the Fermat derivative quotient. -/
theorem actual_component_trace_matrix (m : Fin 35) (i j : Fin 33) :
    socleTrace ((degreeSixCharacterOneBasis i : JacobianRing) *
      (degreeSixCharacterOneBasis j : JacobianRing) *
      (degreeSixCharacterZeroBasis m : JacobianRing)) = higgsMatrix ℂ m i j := by
  rw [degreeSixCharacterOneBasis_coe, degreeSixCharacterOneBasis_coe,
    degreeSixCharacterZeroBasis_coe, socleTrace_triple_eq_higgsMatrix]

theorem socle_weightedDegree_character :
    weightedDegree socle = 18 ∧ character socle = 2 := by decide

theorem socleTrace_normalized : socleTrace (monomialClass socle) = 1 := by
  rw [monomialClass, socleTrace_mk, coeff_monomial]
  simp

/-- The distinguished degree-eighteen class is actually in the socle:
each variable class annihilates it in the derivative quotient. -/
theorem socle_annihilated_by_variables (i : Fin 5) :
    quotientMap (X i) * monomialClass socle = 0 := by
  change quotientMap (monomial (Finsupp.single i 1) 1) *
    quotientMap (monomial (exponent socle) 1) = 0
  rw [← map_mul, monomial_mul, one_mul]
  apply unbounded_monomial_eq_zero
  intro h
  have hi := h i
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, exponent_apply] at hi
  omega

end CycleQ2FermatJacobian

#print axioms CycleQ2FermatJacobian.degreeSixCharacterOne_finrank
#print axioms CycleQ2FermatJacobian.degreeSixCharacterZero_finrank
#print axioms CycleQ2FermatJacobian.actual_component_trace_matrix
#print axioms CycleQ2FermatJacobian.socle_annihilated_by_variables
end
end
