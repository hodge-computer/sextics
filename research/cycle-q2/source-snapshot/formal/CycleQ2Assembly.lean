import CycleQ2Workspace

/-!
Conditional assembly for the unchanged cycle-q2 target.
This module contains no admitted existence claim. The large compiled-current
transport is not formalized here; the input below explicitly includes all
legality, grading, and normalized equation obligations.
-/

noncomputable section
namespace CycleQ2Assembly
open MvPolynomial HodgeComputer CycleQ2Workspace

/-- A legal homogeneous rational solution, represented by common-denominator
polynomials and the two normalized equations. No denominator degree or support
is fixed, and the quotient polynomial is unrestricted. -/
structure NormalizedRationalSolution where
  degree : ℕ
  denominator : Poly
  numerators : Fin 6 → Poly
  quotient : Poly
  denominator_ne_zero : denominator ≠ 0
  denominator_homogeneous : denominator.IsHomogeneous degree
  numerator_homogeneous : ∀ i, (numerators i).IsHomogeneous (degree + 7)
  denominator_legal : IsRelPrime originalF denominator
  first_normal :
    (2 : Poly) * HodgeTestbed.directional originalF numerators =
      originalA * denominator
  second_normal :
    HodgeTestbed.divergenceNumerator denominator numerators =
      originalF ^ 2 * quotient

/-- A normalized solution yields the exact, unchanged protected existential goal.
This theorem proves the assembly only; it does not produce the input solution. -/
theorem certificate_of_normalized_solution (s : NormalizedRationalSolution) :
    OriginalGoal := by
  change HasCertificate originalF originalA 2
  refine ⟨s.degree, s.denominator, s.numerators, s.quotient, ?_⟩
  refine {
    denominator_ne_zero := s.denominator_ne_zero
    denominator_homogeneous := s.denominator_homogeneous
    numerator_homogeneous := ?_
    denominator_legal := s.denominator_legal
    identity := ?_
  }
  · intro i
    have hdeg : s.degree + 6 * 2 - 5 = s.degree + 7 := by omega
    simpa only [hdeg] using s.numerator_homogeneous i
  · simpa using
      (HodgeComputer.normalized_identity (q := 2) s.first_normal s.second_normal)

/-- Exact remainder-repair identity for a chosen common denominator.
A genuine correction must satisfy hcorrection; this theorem does not assert it.
All numerator and denominator derivatives are retained by fixedOperator. -/
theorem close_partial_identity
    (F A D R Q S : Poly) (N M : Fin 6 → Poly)
    (hpartial : defect F A D 2 N = -(F ^ 2 * R) + F ^ 3 * Q)
    (hcorrection : fixedOperator F D M S = F ^ 2 * R) :
    defect F A D 2 (fun i => N i + M i) = F ^ 3 * (Q + S) := by
  have hadd :
      defect F A D 2 (fun i => N i + M i) =
        defect F A D 2 N + fixedOperator F D M S + F ^ 3 * S := by
    unfold defect fixedOperator
    rw [CycleQ2Workspace.directional_add,
        CycleQ2Workspace.divergenceNumerator_add]
    ring
  rw [hadd, hpartial, hcorrection]
  ring

#print axioms certificate_of_normalized_solution
#print axioms close_partial_identity
end CycleQ2Assembly
