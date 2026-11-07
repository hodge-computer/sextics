import Proposal.CurrentCore
import Proposal.Normalization
import Proposal.DenominatorSpecialization
import Proposal.TangentCoordinates

/-! Specialization of the shared tangent-coordinate calculus to the protected
sextic. The explicit pivot legality and canonical forcing remain instance data. -/
noncomputable section
namespace CycleQ2Concrete
open MvPolynomial HodgeTestbed HodgeComputer
local notation "F" => CycleQ2Workspace.originalF

abbrev tangentPair (i j : Fin 6) : Fin 6 → Poly :=
  TangentCoordinates.tangentPair F i j

abbrev tangentOperator (i j : Fin 6) (P : Poly) : Poly :=
  TangentCoordinates.tangentOperator F i j P

abbrev tangentNumerators (P : Fin 5 → Poly) : Fin 6 → Poly :=
  TangentCoordinates.tangentNumerators F P

abbrev tangentBoundary (H : Poly) (P : Fin 5 → Poly) : Poly :=
  TangentCoordinates.tangentBoundary F H P

lemma directional_sub (P : Poly) (N M : Fin 6 → Poly) :
    directional P (fun i => N i - M i) = directional P N - directional P M :=
  TangentCoordinates.directional_sub P N M

lemma tangentNumerators_annihilates_F (P : Fin 5 → Poly) :
    directional F (tangentNumerators P) = 0 :=
  TangentCoordinates.tangentNumerators_annihilates F P

lemma tangentNumerators_divergence (H : Poly) (P : Fin 5 → Poly) :
    divergenceNumerator H (tangentNumerators P) = tangentBoundary H P :=
  TangentCoordinates.tangentNumerators_divergence F H P

/-- The shared polynomial identity needs no generic-rank assumption. -/
theorem tangentNumerators_of_tangent (M : Fin 6 → Poly)
    (hM : directional F M = 0) :
    tangentNumerators (fun i => M i.castSucc) =
      fun k => pderiv (5 : Fin 6) F * M k :=
  TangentCoordinates.tangentNumerators_of_tangent F M hM

/-- The common denominator calculation retains derivatives of the pivot. -/
theorem tangentBoundary_of_tangent (H : Poly) (M : Fin 6 → Poly)
    (hM : directional F M = 0) :
    tangentBoundary (pderiv (5 : Fin 6) F * H) (fun i => M i.castSucc) =
      (pderiv (5 : Fin 6) F) ^ 2 * divergenceNumerator H M :=
  TangentCoordinates.tangentBoundary_of_tangent F H M hM

lemma tangentNumerators_homogeneous {d : ℕ} (P : Fin 5 → Poly)
    (hP : ∀ i, (P i).IsHomogeneous (d + 2)) (k : Fin 6) :
    (tangentNumerators P k).IsHomogeneous (d + 7) := by
  simpa only [Nat.add_assoc] using TangentCoordinates.tangentNumerators_homogeneous
    CycleQ2Workspace.originalF_homogeneous P hP k

end CycleQ2Concrete

namespace CycleQ2Canonical
open MvPolynomial HodgeTestbed HodgeComputer CycleQ2Concrete
abbrev Poly := CycleQ2Concrete.Poly
local notation "F" => CycleQ2Workspace.originalF
local notation "A" => CycleQ2Workspace.originalA

/-- A small first-normal current, independent of the saved physical current. -/
def normalDenominator : Poly := pderiv (5 : Fin 6) F

def normalNumerators : Fin 6 → Poly := coordinateField 5 (C (1 / 2 : ℂ) * A)

/-- The exact numerator of the divergence of A/(2 F_5) in direction 5. -/
def normalDivergence : Poly := divergenceNumerator normalDenominator normalNumerators

lemma normalDenominator_homogeneous : normalDenominator.IsHomogeneous 5 :=
  CycleQ2Workspace.originalF_homogeneous.pderiv

lemma normalDenominator_ne_zero : normalDenominator ≠ 0 :=
  Denominator.tangentPivot_ne_zero

lemma normalDenominator_legal : IsRelPrime F normalDenominator :=
  Denominator.tangentPivot_legal

lemma normalNumerators_homogeneous (i : Fin 6) :
    (normalNumerators i).IsHomogeneous 12 := by
  classical
  by_cases hi : i = 5
  · simpa [normalNumerators, coordinateField, hi] using
      CycleQ2Workspace.originalA_homogeneous.C_mul (1 / 2 : ℂ)
  · simpa [normalNumerators, coordinateField, hi] using
      (isHomogeneous_zero (R := ℂ) (σ := Fin 6) 12)

private lemma half_cancel : (2 : Poly) * C (1 / 2 : ℂ) = 1 := by
  calc
    _ = C (2 : ℂ) * C (1 / 2 : ℂ) := by rw [_root_.map_ofNat]
    _ = C ((2 : ℂ) * (1 / 2)) := by rw [map_mul]
    _ = 1 := by norm_num

lemma normal_first : 2 * directional F normalNumerators = A * normalDenominator := by
  unfold normalNumerators normalDenominator
  rw [directional_coordinateField]
  linear_combination (A * pderiv (5 : Fin 6) F) * half_cancel

lemma normal_defect :
    defect F A normalDenominator 2 normalNumerators = F * normalDivergence := by
  unfold defect normalDivergence
  linear_combination -normalDenominator * normal_first

/-- The compact forcing numerator on the literal protected sextic.
In rational notation, -div(v0) equals this polynomial divided by (2 F_5)^2. -/
theorem normalDivergence_explicit :
    -4 * normalDivergence =
      (X (0 : Fin 6) ^ 2 * X 1 ^ 2 * X 2 ^ 3 * X 3 ^ 2 * X 4 ^ 2) *
        (48 * X 5 ^ 5 - (X 0 * X 2 ^ 3 * X 3 + X 1 ^ 3 * X 2 * X 4)) := by
  have h6 : pderiv (5 : Fin 6) (6 : Poly) = 0 :=
    (pderiv (5 : Fin 6) : Derivation ℂ Poly Poly).map_natCast 6
  unfold normalDivergence divergenceNumerator normalNumerators normalDenominator
  rw [divergence_coordinateField, directional_coordinateField]
  apply MvPolynomial.funext
  intro x
  norm_num [CycleQ2Workspace.originalF, HodgeSubmission.F,
    CycleQ2Workspace.originalA, HodgeSubmission.A,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X,
    Pi.single_apply, Fin.ext_iff, h6]
  ring

/-- This compact equation retains arbitrary legal new poles and the full F^3
quotient. There is no source-comparison hypothesis or archived-current input. -/
def CanonicalTangentClosureGoal (H : Poly) (P : Fin 5 → Poly) (S : Poly) : Prop :=
  normalDenominator ^ 2 * tangentBoundary H P + H ^ 2 * normalDivergence = F ^ 2 * S

structure CanonicalTangentSolution where
  degree : ℕ
  denominator : Poly
  coefficients : Fin 5 → Poly
  quotient : Poly
  denominator_homogeneous : denominator.IsHomogeneous degree
  coefficient_homogeneous : ∀ i, (coefficients i).IsHomogeneous (degree + 2)
  denominator_ne_zero : denominator ≠ 0
  denominator_legal : IsRelPrime F denominator
  closes : CanonicalTangentClosureGoal denominator coefficients quotient

lemma canonical_reconstruction_identity (H : Poly) (P : Fin 5 → Poly) :
    defect F A (normalDenominator * H) 2
      (fun i => H * normalNumerators i + normalDenominator * tangentNumerators P i) =
        F * (normalDenominator ^ 2 * tangentBoundary H P + H ^ 2 * normalDivergence) := by
  have hadd := HodgeComputer.defect_add F A 0 normalDenominator H 2
    normalNumerators (tangentNumerators P)
  simp only [add_zero] at hadd
  rw [hadd, normal_defect]
  have hlin : defect F 0 H 2 (tangentNumerators P) = F * tangentBoundary H P := by
    unfold defect
    rw [tangentNumerators_annihilates_F, tangentNumerators_divergence]
    ring
  rw [hlin]
  ring

theorem certificate_of_canonical_tangent_solution (c : CanonicalTangentSolution) :
    CycleQ2Workspace.OriginalGoal := by
  let D := normalDenominator * c.denominator
  let N := fun i => c.denominator * normalNumerators i +
    normalDenominator * tangentNumerators c.coefficients i
  have hDne : D ≠ 0 := mul_ne_zero normalDenominator_ne_zero c.denominator_ne_zero
  have hD : D.IsHomogeneous (5 + c.degree) :=
    normalDenominator_homogeneous.mul c.denominator_homogeneous
  have hdeg : D.totalDegree = 5 + c.degree := hD.totalDegree hDne
  have hN (i : Fin 6) : (N i).IsHomogeneous (5 + c.degree + 7) := by
    have hl : (c.denominator * normalNumerators i).IsHomogeneous (5 + c.degree + 7) := by
      convert c.denominator_homogeneous.mul (normalNumerators_homogeneous i) using 1 <;> omega
    have hr : (normalDenominator * tangentNumerators c.coefficients i).IsHomogeneous
        (5 + c.degree + 7) := by
      convert normalDenominator_homogeneous.mul
        (tangentNumerators_homogeneous c.coefficients c.coefficient_homogeneous i)
        using 1 <;> omega
    exact hl.add hr
  have hid : defect F A D 2 N = F ^ 3 * c.quotient := by
    rw [canonical_reconstruction_identity]
    rw [show normalDenominator ^ 2 * tangentBoundary c.denominator c.coefficients +
      c.denominator ^ 2 * normalDivergence = F ^ 2 * c.quotient from c.closes]
    ring
  change HasCertificate F 2 A
  apply HodgeComputer.Verify.hasCertificate (d := 6) (D := D) (N := N) (Q := c.quotient)
  refine {
    hypersurface_ne_zero := CycleQ2Workspace.originalF_ne_zero
    hypersurface_homogeneous := CycleQ2Workspace.originalF_homogeneous
    source_homogeneous := ?_
    denominator_ne_zero := hDne
    denominator_homogeneous := ?_
    numerator_homogeneous := ?_
    denominator_legal := normalDenominator_legal.mul_right c.denominator_legal
    identity := hid
  }
  · simpa using Homogeneous.of_isHomogeneous CycleQ2Workspace.originalA_homogeneous
  · rw [hdeg]
    exact hD
  · intro i
    rw [hdeg]
    convert Homogeneous.of_isHomogeneous (hN i) using 1 <;> omega

/-- An unconditional, exact five-function version of the protected target.
This proves equivalence; it does not assert a closing rational current exists. -/
theorem originalGoal_iff_canonical_tangent_solution :
    CycleQ2Workspace.OriginalGoal ↔ Nonempty CanonicalTangentSolution := by
  constructor
  · intro h
    obtain ⟨s⟩ := CycleQ2Normalization.originalGoal_iff_normalized.mp h
    let g := normalDenominator
    let M : Fin 6 → Poly := fun i => g * s.numerators i - s.denominator * normalNumerators i
    let H : Poly := g * (g * s.denominator)
    let P : Fin 5 → Poly := fun i => M i.castSucc
    let S : Poly := (g ^ 3) ^ 2 * s.quotient
    have ht : directional F M = 0 := by
      apply mul_left_cancel₀ (show (2 : Poly) ≠ 0 by norm_num)
      dsimp only [M]
      rw [directional_sub, HodgeTestbed.directional_mul, HodgeTestbed.directional_mul]
      linear_combination g * s.first_normal - s.denominator * normal_first
    have htan : tangentNumerators P = fun k => g * M k :=
      tangentNumerators_of_tangent M ht
    have hH : H.IsHomogeneous (10 + s.degree) := by
      convert normalDenominator_homogeneous.mul
        (normalDenominator_homogeneous.mul s.denominator_homogeneous) using 1 <;> omega
    have hP (i : Fin 5) : (P i).IsHomogeneous (10 + s.degree + 2) := by
      have hl : (g * s.numerators i.castSucc).IsHomogeneous (10 + s.degree + 2) := by
        convert normalDenominator_homogeneous.mul (s.numerator_homogeneous i.castSucc)
          using 1 <;> omega
      have hr : (s.denominator * normalNumerators i.castSucc).IsHomogeneous
          (10 + s.degree + 2) := by
        convert s.denominator_homogeneous.mul (normalNumerators_homogeneous i.castSucc)
          using 1 <;> omega
      exact hl.sub hr
    have hDnew : normalDenominator * H = g ^ 3 * s.denominator := by
      dsimp only [H, g]
      ring
    have hNnew : (fun i => H * normalNumerators i + normalDenominator * tangentNumerators P i) =
        fun i => g ^ 3 * s.numerators i := by
      rw [htan]
      funext i
      dsimp only [H, M, g]
      ring
    have hs : defect F A s.denominator 2 s.numerators = F ^ 3 * s.quotient := by
      simpa using HodgeComputer.normalized_identity (q := 2) s.first_normal s.second_normal
    have hid : defect F A (normalDenominator * H) 2
        (fun i => H * normalNumerators i + normalDenominator * tangentNumerators P i) =
          F ^ 3 * S := by
      rw [hDnew, hNnew, HodgeComputer.defect_scale_denominator, hs]
      dsimp only [S]
      ring
    have hclose : CanonicalTangentClosureGoal H P S := by
      unfold CanonicalTangentClosureGoal
      apply mul_left_cancel₀ CycleQ2Workspace.originalF_ne_zero
      rw [canonical_reconstruction_identity] at hid
      linear_combination hid
    exact ⟨{
      degree := 10 + s.degree
      denominator := H
      coefficients := P
      quotient := S
      denominator_homogeneous := hH
      coefficient_homogeneous := hP
      denominator_ne_zero := mul_ne_zero normalDenominator_ne_zero
        (mul_ne_zero normalDenominator_ne_zero s.denominator_ne_zero)
      denominator_legal := normalDenominator_legal.mul_right
        (normalDenominator_legal.mul_right s.denominator_legal)
      closes := hclose
    }⟩
  · rintro ⟨c⟩
    exact certificate_of_canonical_tangent_solution c

#print axioms normalDivergence_explicit
#print axioms canonical_reconstruction_identity
#print axioms originalGoal_iff_canonical_tangent_solution
end CycleQ2Canonical
