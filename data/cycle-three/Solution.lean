import HodgeTarget
import Proposal.PhysicalPrimitive

/-! The certificate for the immutable cycle-three target. See solution.md
for the construction, its scope, and mathematical and implementation credits. -/
noncomputable section
namespace Submission
theorem certificate :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q := by
  have hF : HodgeSubmission.F=CyclePhysical.sextic := by
    unfold HodgeSubmission.F CyclePhysical.sextic
    ring
  rw [hF]
  exact CyclePhysicalPrimitive.certificate
end Submission
#print axioms Submission.certificate
