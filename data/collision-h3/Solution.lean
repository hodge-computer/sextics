import HodgeWitness
import Proposal.Witness
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
noncomputable section
namespace Submission
theorem witness : HodgeComputer.Verify HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q HodgeWitness.d HodgeWitness.D HodgeWitness.N HodgeWitness.Q := by
  have hF : HodgeSubmission.F = HodgeComputer.Instances.CollisionH3.F := by
    apply MvPolynomial.funext; intro x
    norm_num [HodgeSubmission.F, HodgeComputer.Instances.CollisionH3.F] <;> ring
  have hA : HodgeSubmission.A = HodgeComputer.Instances.CollisionH3.A := by
    apply MvPolynomial.funext; intro x
    norm_num [HodgeSubmission.A, HodgeComputer.Instances.CollisionH3.A] <;> ring
  have hD : HodgeWitness.D = HodgeComputer.Instances.CollisionH3.D := by
    apply MvPolynomial.funext; intro x
    norm_num [HodgeWitness.D, HodgeComputer.Instances.CollisionH3.D] <;> ring
  have hQ : HodgeWitness.Q = HodgeComputer.Instances.CollisionH3.Q := by
    apply MvPolynomial.funext; intro x
    norm_num [HodgeWitness.Q, HodgeComputer.Instances.CollisionH3.Q] <;> ring
  have hN : HodgeWitness.N = HodgeComputer.Instances.CollisionH3.N := by
    funext i; fin_cases i
    · change HodgeWitness.N0 = HodgeComputer.Instances.CollisionH3.N0
      apply MvPolynomial.funext; intro x
      norm_num [HodgeWitness.N0, HodgeComputer.Instances.CollisionH3.N0] <;> ring
    · change HodgeWitness.N1 = HodgeComputer.Instances.CollisionH3.N1
      apply MvPolynomial.funext; intro x
      norm_num [HodgeWitness.N1, HodgeComputer.Instances.CollisionH3.N1] <;> ring
    · change HodgeWitness.N2 = HodgeComputer.Instances.CollisionH3.N2
      apply MvPolynomial.funext; intro x
      norm_num [HodgeWitness.N2, HodgeComputer.Instances.CollisionH3.N2] <;> ring
    · change HodgeWitness.N3 = HodgeComputer.Instances.CollisionH3.N3
      apply MvPolynomial.funext; intro x
      norm_num [HodgeWitness.N3, HodgeComputer.Instances.CollisionH3.N3] <;> ring
    · change HodgeWitness.N4 = HodgeComputer.Instances.CollisionH3.N4
      apply MvPolynomial.funext; intro x
      norm_num [HodgeWitness.N4, HodgeComputer.Instances.CollisionH3.N4] <;> ring
    · change HodgeWitness.N5 = HodgeComputer.Instances.CollisionH3.N5
      apply MvPolynomial.funext; intro x
      norm_num [HodgeWitness.N5, HodgeComputer.Instances.CollisionH3.N5] <;> ring
  simpa only [hF,hA,hD,hQ,hN,HodgeSubmission.q,HodgeWitness.d] using HodgeComputer.Instances.CollisionH3.certificate
theorem certificate : HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q := ⟨HodgeWitness.d,HodgeWitness.D,HodgeWitness.N,HodgeWitness.Q,witness⟩
end Submission
