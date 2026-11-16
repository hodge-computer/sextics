import Proposal.TargetBinding
import Proposal.PhysicalPrimitive

/-! Bind the compact quadratic-shear construction to the immutable target. -/
noncomputable section
namespace Submission

theorem certificate :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A := by
  rw [MixedPolarTargetBinding.equation,MixedPolarTargetBinding.source,
    MixedPolarTargetBinding.pole_order]
  exact MixedPolarPhysicalPrimitive.certificate

end Submission
#print axioms Submission.certificate
