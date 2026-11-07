import HodgeTestbed.Algebra
import HodgeComputer.Constructions.HoldoutCover.PolynomialCalculus
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Polynomial tangent coordinates

For an arbitrary polynomial `F`, the fields
`(∂ⱼF) ∂ᵢ - (∂ᵢF) ∂ⱼ` annihilate `F` and have zero divergence.
Fixing the last coordinate as a pivot gives `n` generators in `n + 1`
variables. Every polynomial tangent vector is a linear combination of these
generators after multiplication by the pivot derivative. The same calculation
retains all moving-denominator terms in the cleared divergence.

These identities are over an arbitrary commutative coefficient ring. They do
not assume that the pivot is nonzero or legal as a denominator; applications
using its reciprocal must prove those additional facts.

Extracted and generalized from the tangent-coordinate reduction accompanying
`fqlx`'s physical-current construction, with OpenAI assistance.
-/

noncomputable section
set_option autoImplicit false

namespace HodgeComputer.TangentCoordinates

open MvPolynomial HodgeTestbed
open scoped BigOperators

variable {R σ ι : Type*} [CommRing R] [Fintype σ]

theorem directional_sub (P : MvPolynomial σ R) (N M : σ → MvPolynomial σ R) :
    directional P (fun i => N i - M i) = directional P N - directional P M := by
  simp [directional, mul_sub, Finset.sum_sub_distrib]

theorem divergence_sub (N M : σ → MvPolynomial σ R) :
    divergence (fun i => N i - M i) = divergence N - divergence M := by
  simp [divergence, map_sub, Finset.sum_sub_distrib]

theorem directional_sum [Fintype ι] (P : MvPolynomial σ R)
    (V : ι → σ → MvPolynomial σ R) :
    directional P (fun k => ∑ i, V i k) = ∑ i, directional P (V i) := by
  simp only [directional, Finset.mul_sum]
  exact Finset.sum_comm

theorem divergence_sum [Fintype ι] (V : ι → σ → MvPolynomial σ R) :
    divergence (fun k => ∑ i, V i k) = ∑ i, divergence (V i) := by
  simp only [divergence, map_sum]
  exact Finset.sum_comm

/-- The elementary tangent field associated to two coordinate directions. -/
def tangentPair (F : MvPolynomial σ R) (i j : σ) : σ → MvPolynomial σ R :=
  fun k => coordinateField i (pderiv j F) k - coordinateField j (pderiv i F) k

/-- Differentiation along an elementary tangent field. -/
def tangentOperator (F : MvPolynomial σ R) (i j : σ) (P : MvPolynomial σ R) :
    MvPolynomial σ R := pderiv j F * pderiv i P - pderiv i F * pderiv j P

theorem tangentPair_directional (F P : MvPolynomial σ R) (i j : σ) :
    directional P (tangentPair F i j) = tangentOperator F i j P := by
  unfold tangentPair
  rw [directional_sub, directional_coordinateField, directional_coordinateField]
  unfold tangentOperator
  ring

theorem tangentPair_annihilates (F : MvPolynomial σ R) (i j : σ) :
    directional F (tangentPair F i j) = 0 := by
  rw [tangentPair_directional]
  unfold tangentOperator
  ring

theorem tangentPair_divergence (F : MvPolynomial σ R) (i j : σ) :
    divergence (tangentPair F i j) = 0 := by
  unfold tangentPair
  rw [divergence_sub, divergence_coordinateField, divergence_coordinateField]
  exact sub_eq_zero.mpr (HoldoutConstruction.pderiv_commute i j F)

theorem weighted_tangent_divergence (F P : MvPolynomial σ R) (i j : σ) :
    divergence (fun k => P * tangentPair F i j k) = tangentOperator F i j P := by
  rw [HodgeTestbed.divergence_mul, tangentPair_directional, tangentPair_divergence]
  ring

omit [Fintype σ] in
theorem tangentPair_homogeneous {F : MvPolynomial σ R} {d : ℕ}
    (hF : F.IsHomogeneous d) (i j k : σ) :
    (tangentPair F i j k).IsHomogeneous (d - 1) := by
  classical
  have hc (i j k : σ) :
      (coordinateField i (pderiv j F) k).IsHomogeneous (d - 1) := by
    by_cases hki : k = i
    · simpa [coordinateField, hki] using hF.pderiv (i := j)
    · simpa [coordinateField, hki] using
        (isHomogeneous_zero (R := R) (σ := σ) (d - 1))
  exact (hc i j k).sub (hc j i k)

variable {n : ℕ}

/-- Sum of the tangent directions using the last coordinate as pivot. -/
def tangentNumerators (F : MvPolynomial (Fin (n + 1)) R)
    (P : Fin n → MvPolynomial (Fin (n + 1)) R) :
    Fin (n + 1) → MvPolynomial (Fin (n + 1)) R :=
  fun k => ∑ i : Fin n, P i * tangentPair F i.castSucc (Fin.last n) k

/-- The numerator of the tangent divergence, including derivatives of `H`. -/
def tangentBoundary (F H : MvPolynomial (Fin (n + 1)) R)
    (P : Fin n → MvPolynomial (Fin (n + 1)) R) : MvPolynomial (Fin (n + 1)) R :=
  ∑ i : Fin n, (H * tangentOperator F i.castSucc (Fin.last n) (P i) -
    P i * tangentOperator F i.castSucc (Fin.last n) H)

theorem tangentNumerators_annihilates (F : MvPolynomial (Fin (n + 1)) R)
    (P : Fin n → MvPolynomial (Fin (n + 1)) R) :
    directional F (tangentNumerators F P) = 0 := by
  unfold tangentNumerators
  rw [directional_sum]
  simp only [HodgeTestbed.directional_mul, tangentPair_annihilates,
    mul_zero, Finset.sum_const_zero]

theorem tangentNumerators_divergence (F H : MvPolynomial (Fin (n + 1)) R)
    (P : Fin n → MvPolynomial (Fin (n + 1)) R) :
    divergenceNumerator H (tangentNumerators F P) = tangentBoundary F H P := by
  unfold divergenceNumerator tangentNumerators tangentBoundary
  rw [divergence_sum, directional_sum]
  simp only [weighted_tangent_divergence, HodgeTestbed.directional_mul,
    tangentPair_directional, Finset.mul_sum, Finset.sum_sub_distrib]

/-- One multiplication by the pivot expresses every polynomial tangent vector
in the displayed generators. No division or generic-rank assertion is used. -/
theorem tangentNumerators_of_tangent (F : MvPolynomial (Fin (n + 1)) R)
    (M : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R)
    (hM : directional F M = 0) :
    tangentNumerators F (fun i => M i.castSucc) =
      fun k => pderiv (Fin.last n) F * M k := by
  classical
  funext k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · have hm := hM
    rw [directional, Fin.sum_univ_castSucc] at hm
    have hne (i : Fin n) : Fin.last n ≠ i.castSucc := (Fin.castSucc_ne_last i).symm
    simp only [tangentNumerators, tangentPair, coordinateField,
      hne, ↓reduceIte, zero_sub, mul_neg, Finset.sum_neg_distrib]
    simpa only [mul_comm] using (eq_neg_of_add_eq_zero_right hm).symm
  · simp [tangentNumerators, tangentPair, coordinateField, Fin.castSucc_inj, mul_comm]

/-- Scaling the denominator by the pivot introduces precisely its square in
the cleared divergence. The derivatives of the pivot cancel. -/
theorem tangentBoundary_of_tangent (F H : MvPolynomial (Fin (n + 1)) R)
    (M : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R)
    (hM : directional F M = 0) :
    tangentBoundary F (pderiv (Fin.last n) F * H) (fun i => M i.castSucc) =
      (pderiv (Fin.last n) F) ^ 2 * divergenceNumerator H M := by
  rw [← tangentNumerators_divergence, tangentNumerators_of_tangent F M hM,
    HodgeTestbed.divergenceNumerator_mul]

theorem tangentNumerators_homogeneous {F : MvPolynomial (Fin (n + 1)) R}
    {d e : ℕ} (hF : F.IsHomogeneous d)
    (P : Fin n → MvPolynomial (Fin (n + 1)) R)
    (hP : ∀ i, (P i).IsHomogeneous e) (k : Fin (n + 1)) :
    (tangentNumerators F P k).IsHomogeneous (e + (d - 1)) := by
  apply IsHomogeneous.sum
  intro i _
  exact (hP i).mul (tangentPair_homogeneous hF i.castSucc (Fin.last n) k)

end HodgeComputer.TangentCoordinates
