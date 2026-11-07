import Proposal.CurrentDenominator
import HodgeComputer.CertificateOperations

/-! Common-denominator reconstruction for the concrete physical current.
The literal source-comparison error is retained throughout. -/
noncomputable section
namespace CycleQ2Concrete
open MvPolynomial HodgeComputer HodgeTestbed

abbrev F : Poly := CycleQ2Workspace.originalF
abbrev A : Poly := CycleQ2Workspace.originalA

/-- New poles are allowed: H is NOT fixed to a factor of the archived denominator. -/
def completedD (H : Poly) : Poly := baseD * H

def completedN (H : Poly) (M : Fin 6 → Poly) : Fin 6 → Poly :=
  fun i => H * baseN i + baseD * M i

def completedQ (H S : Poly) : Poly := H ^ 2 * baseQ + S

/-- All moving derivatives of H and M occur in the maintained exact defect. -/
def correctionResidual (H : Poly) (M : Fin 6 → Poly) (S : Poly) : Poly :=
  baseD ^ 2 * defect F 0 H 2 M + H ^ 2 * transportError -
    F ^ 2 * H ^ 2 * baseR - F ^ 3 * S

/-- Generic polynomial identity, not an assumed equality of rational functions. -/
theorem concrete_reconstruction_identity (H : Poly) (M : Fin 6 → Poly) (S : Poly) :
    defect F A (completedD H) 2 (completedN H M) -
        F ^ 3 * completedQ H S = correctionResidual H M S := by
  have h := HodgeComputer.defect_add F A 0 baseD H 2 baseN M
  simp only [add_zero] at h
  unfold completedD completedN completedQ correctionResidual
  rw [h]
  unfold transportError literalDefect
  ring

/-- Only AFTER proving the archived partial identity may its comparison error be dropped. -/
theorem correctionResidual_of_transport_verified
    (h : ArchivedPartialIdentityGoal) (H : Poly) (M : Fin 6 → Poly) (S : Poly) :
    correctionResidual H M S =
      baseD ^ 2 * defect F 0 H 2 M - F ^ 2 * H ^ 2 * baseR - F ^ 3 * S := by
  change transportError = 0 at h
  unfold correctionResidual
  rw [h]
  ring

/-- A new legal homogeneous denominator and its six correction numerators must
close the literal defect of the fixed current. Its old denominator legality is
proved separately in CurrentDenominator. The quotient correction is unrestricted. -/
structure ActualCurrentCorrection where
  degree : ℕ
  denominator : Poly
  numerators : Fin 6 → Poly
  quotientCorrection : Poly
  denominator_homogeneous : denominator.IsHomogeneous degree
  numerator_homogeneous : ∀ i, (numerators i).IsHomogeneous (degree + 7)
  denominator_ne_zero : denominator ≠ 0
  denominator_legal : IsRelPrime F denominator
  closes : correctionResidual denominator numerators quotientCorrection = 0

/-- This is reconstruction, not a proof that ActualCurrentCorrection is inhabited. -/
theorem certificate_of_actual_current_correction (c : ActualCurrentCorrection) :
    CycleQ2Workspace.OriginalGoal := by
  have hDne : completedD c.denominator ≠ 0 :=
    mul_ne_zero Denominator.baseD_ne_zero c.denominator_ne_zero
  have hDlegal : IsRelPrime F (completedD c.denominator) :=
    Denominator.baseD_legal.mul_right c.denominator_legal
  have hD : (completedD c.denominator).IsHomogeneous (3726 + c.degree) := by
    exact h_baseD.mul c.denominator_homogeneous
  have hdegree : (completedD c.denominator).totalDegree = 3726 + c.degree :=
    hD.totalDegree hDne
  have hN : ∀ i, (completedN c.denominator c.numerators i).IsHomogeneous
      (3726 + c.degree + 7) := by
    intro i
    have hl := c.denominator_homogeneous.mul (h_baseN i)
    have hr := h_baseD.mul (c.numerator_homogeneous i)
    have hl' : (c.denominator * baseN i).IsHomogeneous (3726 + c.degree + 7) := by
      convert hl using 1 <;> omega
    have hr' : (baseD * c.numerators i).IsHomogeneous (3726 + c.degree + 7) := by
      convert hr using 1 <;> omega
    exact hl'.add hr'
  have hid : defect F A (completedD c.denominator) 2
      (completedN c.denominator c.numerators) =
        F ^ 3 * completedQ c.denominator c.quotientCorrection := by
    apply sub_eq_zero.mp
    rw [concrete_reconstruction_identity, c.closes]
  change HasCertificate F 2 A
  apply HodgeComputer.Verify.hasCertificate (d := 6)
    (D := completedD c.denominator)
    (N := completedN c.denominator c.numerators)
    (Q := completedQ c.denominator c.quotientCorrection)
  refine {
    hypersurface_ne_zero := CycleQ2Workspace.originalF_ne_zero
    hypersurface_homogeneous := CycleQ2Workspace.originalF_homogeneous
    source_homogeneous := ?_
    denominator_ne_zero := hDne
    denominator_homogeneous := ?_
    numerator_homogeneous := ?_
    denominator_legal := hDlegal
    identity := hid
  }
  · simpa using HodgeComputer.Homogeneous.of_isHomogeneous
      CycleQ2Workspace.originalA_homogeneous
  · rw [hdegree]
    exact hD
  · intro i
    rw [hdegree]
    convert HodgeComputer.Homogeneous.of_isHomogeneous (hN i) using 1 <;> omega

/-- The concrete base current imposes no denominator-family restriction:
any certificate can be written as a correction after clearing denominators. -/
theorem originalGoal_iff_actual_current_correction :
    CycleQ2Workspace.OriginalGoal ↔ Nonempty ActualCurrentCorrection := by
  constructor
  · intro h
    change HasCertificate F 2 A at h
    obtain ⟨D, N, Q, h⟩ := h
    rw [show F.totalDegree = 6 from CycleQ2Workspace.originalF_totalDegree] at h
    have hN (i : Fin 6) : (N i).IsHomogeneous (D.totalDegree + 7) := by
      have hn : HodgeComputer.Homogeneous (N i) ((D.totalDegree + 7 : ℕ) : ℤ) := by
        convert h.numerator_homogeneous i using 1 <;> omega
      simpa only [Int.toNat_natCast] using hn.isHomogeneous (by omega)
    let H : Poly := baseD * D
    let M : Fin 6 → Poly := fun i => baseD * N i - D * baseN i
    let S : Poly := baseD ^ 4 * Q - H ^ 2 * baseQ
    have hDnew : completedD H = baseD ^ 2 * D := by
      unfold completedD H
      ring
    have hNnew : completedN H M = fun i => baseD ^ 2 * N i := by
      funext i
      unfold completedN H M
      ring
    have hQnew : completedQ H S = baseD ^ 4 * Q := by
      unfold completedQ S
      ring
    have hid : defect F A (completedD H) 2 (completedN H M) =
        F ^ 3 * completedQ H S := by
      rw [hDnew, hNnew, hQnew, HodgeComputer.defect_scale_denominator, h.identity]
      ring
    refine ⟨{
      degree := 3726 + D.totalDegree
      denominator := H
      numerators := M
      quotientCorrection := S
      denominator_homogeneous := h_baseD.mul h.denominator_homogeneous
      numerator_homogeneous := ?_
      denominator_ne_zero := mul_ne_zero Denominator.baseD_ne_zero h.denominator_ne_zero
      denominator_legal := Denominator.baseD_legal.mul_right h.denominator_legal
      closes := ?_
    }⟩
    · intro i
      have hl : (baseD * N i).IsHomogeneous (3726 + D.totalDegree + 7) := by
        simpa only [Nat.add_assoc] using h_baseD.mul (hN i)
      have hr : (D * baseN i).IsHomogeneous (3726 + D.totalDegree + 7) := by
        convert h.denominator_homogeneous.mul (h_baseN i) using 1 <;> omega
      exact hl.sub hr
    · rw [← concrete_reconstruction_identity]
      exact sub_eq_zero.mpr hid
  · rintro ⟨c⟩
    exact certificate_of_actual_current_correction c

/-- Clearing to a larger denominator does not itself close the source. -/
theorem zero_correction_keeps_defect (H : Poly) :
    defect F A (completedD H) 2 (completedN H (fun _ => 0)) =
      H ^ 2 * literalDefect := by
  unfold completedD completedN
  simp only [mul_zero, add_zero]
  rw [mul_comm baseD H, HodgeComputer.defect_scale_denominator]
  rfl

#print axioms concrete_reconstruction_identity
#print axioms certificate_of_actual_current_correction
#print axioms originalGoal_iff_actual_current_correction
#print axioms zero_correction_keeps_defect
end CycleQ2Concrete
