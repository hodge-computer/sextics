import HodgeTarget
import Proposal.CompanionAssembly

noncomputable section
namespace Submission

theorem certificate :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q := by
  have hF : HodgeSubmission.F=SplitTernaryPhysical.physicalF := by
    unfold HodgeSubmission.F SplitTernaryPhysical.physicalF
      SplitTernaryPhysical.leftTernary SplitTernaryPhysical.rightTernary
    simp only [show (5/7 : ℂ)=5*(1/7) by ring,map_mul,map_ofNat]
    ring
  have hA : HodgeSubmission.A=SplitTernaryPhysical.physicalA := by
    unfold HodgeSubmission.A SplitTernaryPhysical.physicalA
    ring
  rw [hF,hA]
  exact SplitTernaryProduct.physical_certificate

end Submission
