import HodgeTarget
import Proposal.PhysicalPrimitive

/-! Binding the holdout-moving-branch construction to the protected immutable target. -/
noncomputable section
namespace Submission

theorem certificate :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q := by
  have hF : HodgeSubmission.F = CyclePhysical.sextic := by
    unfold HodgeSubmission.F CyclePhysical.sextic
    ring
  have hA : HodgeSubmission.A = CyclePhysical.source := by
    unfold HodgeSubmission.A CyclePhysical.source
    ring
  rw [hF, hA]
  exact CyclePhysicalPrimitive.certificate

end Submission
#print axioms Submission.certificate
