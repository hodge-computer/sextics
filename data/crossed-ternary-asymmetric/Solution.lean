import HodgeTarget
import Proposal.CertificateClosure

noncomputable section
namespace Submission

theorem certificate :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q := by
  have hF : HodgeSubmission.F=CrossedPhysicalChart.physicalF := by
    unfold HodgeSubmission.F CrossedPhysicalChart.physicalF CrossedPhysicalChart.ternary
    simp only [show (5/7 : ℂ)=5*(1/7) by ring, map_mul, map_ofNat]
    ring
  have hA : HodgeSubmission.A=CrossedPhysicalChart.physicalA := by
    unfold HodgeSubmission.A CrossedPhysicalChart.physicalA
    ring
  rw [hF,hA]
  exact CrossedPhysicalChart.physical_certificate

end Submission
