import Proposal.TargetBinding
import Proposal.SexticCertificate

noncomputable section
namespace Submission

/-- The complete certificate for the exact protected open case. -/
theorem certificate : HodgeComputer.HasCertificate
    HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q := by
  rw [← target_F, ← target_A]
  exact QuadricContactSextic.certificate

end Submission

#print axioms Submission.certificate
