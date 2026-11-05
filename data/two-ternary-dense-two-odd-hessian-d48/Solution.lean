import HodgeTarget
import Proposal.PDenseP0
set_option maxHeartbeats 8000000
noncomputable section
open HodgeComputer HodgeTestbed
namespace Submission
 theorem certificate : HasCertificate HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q := by
  have hf : HodgeSubmission.F = DenseP0.F := by
    apply MvPolynomial.funext; intro x
    norm_num [HodgeSubmission.F,DenseP0.F,DenseP0.cm,Frozen.F,Frozen.X0,Frozen.X1,Frozen.X2,Frozen.Y0,Frozen.Y1,Frozen.Y2] <;> ring
  have ha : HodgeSubmission.A = DenseP0.A := by
    apply MvPolynomial.funext; intro x
    norm_num [HodgeSubmission.A,DenseP0.A,DenseP0.cm,Frozen.A,Frozen.X0,Frozen.Y1] <;> ring
  simpa only [hf,ha,HodgeSubmission.q] using DenseP0.solved
end Submission
