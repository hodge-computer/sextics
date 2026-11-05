import HodgeTarget
import Proposal.FinalAssembly

namespace Submission

theorem certificate : HodgeComputer.HasCertificate
    HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q := by
  have hF : HodgeSubmission.F = HoldoutEndpointTarget.F := by
    unfold HodgeSubmission.F HoldoutEndpointTarget.F HoldoutAlgebra.sextic
    ring
  have hA : HodgeSubmission.A = HoldoutEndpointTarget.A := by
    rfl
  rw [hF, hA]
  exact HoldoutFinalAssembly.certificate

end Submission
