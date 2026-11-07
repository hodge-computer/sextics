import Proposal.CurrentNormalGauge

/-! Five polynomial tangent directions, including moving-denominator terms.
This optional route requires proving the explicit ArchivedPartialIdentityGoal.
It is not substituted for the unrestricted six-component correction interface. -/
noncomputable section
namespace CycleQ2Concrete
open MvPolynomial HodgeTestbed HodgeComputer
open scoped BigOperators

def tangentPair (i j : Fin 6) : Fin 6 → Poly :=
  fun k => coordinateField i (pderiv j F) k - coordinateField j (pderiv i F) k

def tangentOperator (i j : Fin 6) (P : Poly) : Poly :=
  pderiv j F * pderiv i P - pderiv i F * pderiv j P

lemma directional_sub (P : Poly) (N M : Fin 6 → Poly) :
    directional P (fun i => N i - M i) = directional P N - directional P M := by
  simp [directional, mul_sub, Finset.sum_sub_distrib]

lemma divergence_sub (N M : Fin 6 → Poly) :
    divergence (fun i => N i - M i) = divergence N - divergence M := by
  simp [divergence, map_sub, Finset.sum_sub_distrib]

lemma partials_commute (i j : Fin 6) (P : Poly) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  classical
  by_cases hij : i = j
  · subst j
    rfl
  · ext m
    simp only [coeff_pderiv]
    simp [hij, Ne.symm hij, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc]

lemma tangentPair_directional (i j : Fin 6) (P : Poly) :
    directional P (tangentPair i j) = tangentOperator i j P := by
  unfold tangentPair
  rw [directional_sub, directional_coordinateField, directional_coordinateField]
  unfold tangentOperator
  ring

lemma tangentPair_annihilates_F (i j : Fin 6) :
    directional F (tangentPair i j) = 0 := by
  rw [tangentPair_directional]
  unfold tangentOperator
  ring

lemma tangentPair_divergence (i j : Fin 6) : divergence (tangentPair i j) = 0 := by
  unfold tangentPair
  rw [divergence_sub, divergence_coordinateField, divergence_coordinateField]
  exact sub_eq_zero.mpr (partials_commute i j F)

lemma weighted_tangent_divergence (i j : Fin 6) (P : Poly) :
    divergence (fun k => P * tangentPair i j k) = tangentOperator i j P := by
  rw [HodgeTestbed.divergence_mul, tangentPair_directional, tangentPair_divergence]
  ring

def tangentNumerators (P : Fin 5 → Poly) : Fin 6 → Poly :=
  fun k => ∑ i : Fin 5, P i * tangentPair i.castSucc 5 k

def tangentBoundary (H : Poly) (P : Fin 5 → Poly) : Poly :=
  ∑ i : Fin 5, (H * tangentOperator i.castSucc 5 (P i) -
    P i * tangentOperator i.castSucc 5 H)

lemma directional_sum (T : Poly) (V : Fin 5 → Fin 6 → Poly) :
    directional T (fun k => ∑ i, V i k) = ∑ i, directional T (V i) := by
  simp only [directional, Finset.mul_sum]
  exact Finset.sum_comm

lemma divergence_sum (V : Fin 5 → Fin 6 → Poly) :
    divergence (fun k => ∑ i, V i k) = ∑ i, divergence (V i) := by
  simp only [divergence, map_sum]
  exact Finset.sum_comm

lemma tangentNumerators_annihilates_F (P : Fin 5 → Poly) :
    directional F (tangentNumerators P) = 0 := by
  unfold tangentNumerators
  rw [directional_sum]
  simp only [HodgeTestbed.directional_mul, tangentPair_annihilates_F,
    mul_zero, Finset.sum_const_zero]

lemma tangentNumerators_divergence (H : Poly) (P : Fin 5 → Poly) :
    divergenceNumerator H (tangentNumerators P) = tangentBoundary H P := by
  unfold divergenceNumerator tangentNumerators tangentBoundary
  rw [divergence_sum, directional_sum]
  simp only [weighted_tangent_divergence, HodgeTestbed.directional_mul,
    tangentPair_directional, Finset.mul_sum, Finset.sum_sub_distrib]

/-- The cleared form of the recorded five-tangent equation. -/
def FiveTangentClosureGoal (H : Poly) (P : Fin 5 → Poly) (S : Poly) : Prop :=
  normalD ^ 2 * tangentBoundary H P = F * H ^ 2 * normalR + F ^ 2 * S

/-- The original F^3 remainder survives with its full regular quotient. -/
theorem tangent_closure_original_identity
    (hsource : ArchivedPartialIdentityGoal)
    (H : Poly) (P : Fin 5 → Poly) (S : Poly)
    (hclose : FiveTangentClosureGoal H P S) :
    defect F A (normalD * H) 2
      (fun i => H * normalN i + normalD * tangentNumerators P i) =
        F ^ 3 * (H ^ 2 * normalQ + S) := by
  have hadd := HodgeComputer.defect_add F A 0 normalD H 2 normalN (tangentNumerators P)
  simp only [add_zero] at hadd
  rw [hadd, normal_defect_with_transport_error]
  change transportError = 0 at hsource
  rw [hsource]
  have hlin : defect F 0 H 2 (tangentNumerators P) = F * tangentBoundary H P := by
    unfold defect
    rw [tangentNumerators_annihilates_F, tangentNumerators_divergence]
    ring
  rw [hlin]
  change normalD ^ 2 * tangentBoundary H P =
    F * H ^ 2 * normalR + F ^ 2 * S at hclose
  linear_combination F * hclose

#print axioms partials_commute
#print axioms tangentNumerators_divergence
#print axioms tangent_closure_original_identity
end CycleQ2Concrete
