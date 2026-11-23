import HodgeTarget
import Proposal.Certificate

/-! Formal certificate for `symmetric-sextic-residual` (`q = 1`). -/

noncomputable section

namespace Submission

theorem certificate :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A :=
  SymmetricSexticResidual.Certificate.main_certificate

end Submission
