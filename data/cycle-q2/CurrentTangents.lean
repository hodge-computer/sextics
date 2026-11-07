import Proposal.CurrentNormalGauge
import Proposal.CanonicalTangents

/-! Five polynomial tangent directions, including moving-denominator terms.
This optional route requires proving the explicit ArchivedPartialIdentityGoal.
It is not substituted for the unrestricted six-component correction interface. -/
noncomputable section
namespace CycleQ2Concrete
open MvPolynomial HodgeTestbed HodgeComputer
open scoped BigOperators

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

/-- A legal solution of the five scalar tangent equation. The new denominator
is arbitrary; its support is not restricted to factors of the saved current. -/
structure FiveTangentSolution where
  degree : ℕ
  denominator : Poly
  coefficients : Fin 5 → Poly
  quotientCorrection : Poly
  denominator_homogeneous : denominator.IsHomogeneous degree
  coefficient_homogeneous : ∀ i, (coefficients i).IsHomogeneous (degree + 2)
  denominator_ne_zero : denominator ≠ 0
  denominator_legal : IsRelPrime F denominator
  closes : FiveTangentClosureGoal denominator coefficients quotientCorrection

lemma normalD_ne_zero : normalD ≠ 0 :=
  pow_ne_zero 2 Denominator.baseD_ne_zero

lemma normalD_legal : IsRelPrime F normalD := by
  simpa only [normalD, pow_two] using
    Denominator.baseD_legal.mul_right Denominator.baseD_legal

/-- The five-tangent input now includes every grading and legality obligation
needed to obtain the protected certificate, conditional on the source comparison. -/
theorem certificate_of_five_tangent_solution
    (hsource : ArchivedPartialIdentityGoal) (c : FiveTangentSolution) :
    CycleQ2Workspace.OriginalGoal := by
  let D := normalD * c.denominator
  let N := fun i => c.denominator * normalN i +
    normalD * tangentNumerators c.coefficients i
  have hDne : D ≠ 0 := mul_ne_zero normalD_ne_zero c.denominator_ne_zero
  have hD : D.IsHomogeneous (7452 + c.degree) :=
    h_normalD.mul c.denominator_homogeneous
  have hdeg : D.totalDegree = 7452 + c.degree := hD.totalDegree hDne
  have hN (i : Fin 6) : (N i).IsHomogeneous (7452 + c.degree + 7) := by
    have hl : (c.denominator * normalN i).IsHomogeneous (7452 + c.degree + 7) := by
      convert c.denominator_homogeneous.mul (h_normalN i) using 1 <;> omega
    have hr : (normalD * tangentNumerators c.coefficients i).IsHomogeneous
        (7452 + c.degree + 7) := by
      convert h_normalD.mul
        (tangentNumerators_homogeneous c.coefficients c.coefficient_homogeneous i)
        using 1 <;> omega
    exact hl.add hr
  change HasCertificate F 2 A
  apply HodgeComputer.Verify.hasCertificate (d := 6)
    (D := D) (N := N) (Q := c.denominator ^ 2 * normalQ + c.quotientCorrection)
  refine {
    hypersurface_ne_zero := CycleQ2Workspace.originalF_ne_zero
    hypersurface_homogeneous := CycleQ2Workspace.originalF_homogeneous
    source_homogeneous := ?_
    denominator_ne_zero := hDne
    denominator_homogeneous := ?_
    numerator_homogeneous := ?_
    denominator_legal := normalD_legal.mul_right c.denominator_legal
    identity := tangent_closure_original_identity hsource _ _ _ c.closes
  }
  · simpa using Homogeneous.of_isHomogeneous CycleQ2Workspace.originalA_homogeneous
  · rw [hdeg]
    exact hD
  · intro i
    rw [hdeg]
    convert Homogeneous.of_isHomogeneous (hN i) using 1 <;> omega

/-- The five-tangent restriction is lossless once the archived source comparison
is established. The proof uses the actual legal pivot and retains arbitrary new
poles and the unrestricted F^3 quotient. It does not assert existence. -/
theorem originalGoal_iff_five_tangent_solution
    (hsource : ArchivedPartialIdentityGoal) :
    CycleQ2Workspace.OriginalGoal ↔ Nonempty FiveTangentSolution := by
  constructor
  · intro h
    obtain ⟨s⟩ := CycleQ2Normalization.originalGoal_iff_normalized.mp h
    let pivot : Poly := pderiv (5 : Fin 6) F
    let M : Fin 6 → Poly := fun i => normalD * s.numerators i - s.denominator * normalN i
    let H : Poly := pivot * (normalD * s.denominator)
    let P : Fin 5 → Poly := fun i => M i.castSucc
    let S : Poly := (pivot * normalD ^ 2) ^ 2 * s.quotient - H ^ 2 * normalQ
    have ht : directional F M = 0 := by
      apply mul_left_cancel₀ (show (2 : Poly) ≠ 0 by norm_num)
      dsimp only [M]
      rw [directional_sub, HodgeTestbed.directional_mul, HodgeTestbed.directional_mul]
      have hn := normal_first_of_transport_verified hsource
      linear_combination normalD * s.first_normal - s.denominator * hn
    have htan : tangentNumerators P = fun k => pivot * M k :=
      tangentNumerators_of_tangent M ht
    have hp : pivot.IsHomogeneous 5 := CycleQ2Workspace.originalF_homogeneous.pderiv
    have hH : H.IsHomogeneous (7457 + s.degree) := by
      convert hp.mul (h_normalD.mul s.denominator_homogeneous) using 1 <;> omega
    have hP (i : Fin 5) : (P i).IsHomogeneous (7457 + s.degree + 2) := by
      have hl : (normalD * s.numerators i.castSucc).IsHomogeneous
          (7457 + s.degree + 2) := by
        convert h_normalD.mul (s.numerator_homogeneous i.castSucc) using 1 <;> omega
      have hr : (s.denominator * normalN i.castSucc).IsHomogeneous
          (7457 + s.degree + 2) := by
        convert s.denominator_homogeneous.mul (h_normalN i.castSucc) using 1 <;> omega
      exact hl.sub hr
    have hDnew : normalD * H = (pivot * normalD ^ 2) * s.denominator := by
      dsimp only [H]
      ring
    have hNnew : (fun i => H * normalN i + normalD * tangentNumerators P i) =
        fun i => (pivot * normalD ^ 2) * s.numerators i := by
      rw [htan]
      funext i
      dsimp only [H, M]
      ring
    have hs : defect F A s.denominator 2 s.numerators = F ^ 3 * s.quotient := by
      simpa using HodgeComputer.normalized_identity (q := 2) s.first_normal s.second_normal
    have hid : defect F A (normalD * H) 2
        (fun i => H * normalN i + normalD * tangentNumerators P i) =
          F ^ 3 * (H ^ 2 * normalQ + S) := by
      rw [hDnew, hNnew, HodgeComputer.defect_scale_denominator, hs]
      dsimp only [S]
      ring
    have hclose : FiveTangentClosureGoal H P S := by
      have hadd := HodgeComputer.defect_add F A 0 normalD H 2 normalN (tangentNumerators P)
      simp only [add_zero] at hadd
      have hzero : transportError = 0 := hsource
      rw [hadd, normal_defect_with_transport_error, hzero] at hid
      have hlin : defect F 0 H 2 (tangentNumerators P) = F * tangentBoundary H P := by
        unfold defect
        rw [tangentNumerators_annihilates_F, tangentNumerators_divergence]
        ring
      rw [hlin] at hid
      unfold FiveTangentClosureGoal
      apply mul_left_cancel₀ CycleQ2Workspace.originalF_ne_zero
      linear_combination hid
    exact ⟨{
      degree := 7457 + s.degree
      denominator := H
      coefficients := P
      quotientCorrection := S
      denominator_homogeneous := hH
      coefficient_homogeneous := hP
      denominator_ne_zero := mul_ne_zero Denominator.tangentPivot_ne_zero
        (mul_ne_zero normalD_ne_zero s.denominator_ne_zero)
      denominator_legal := Denominator.tangentPivot_legal.mul_right
        (normalD_legal.mul_right s.denominator_legal)
      closes := hclose
    }⟩
  · rintro ⟨c⟩
    exact certificate_of_five_tangent_solution hsource c

#print axioms tangentNumerators_of_tangent
#print axioms tangentBoundary_of_tangent
#print axioms originalGoal_iff_five_tangent_solution

#print axioms tangentNumerators_divergence
#print axioms tangent_closure_original_identity
end CycleQ2Concrete
