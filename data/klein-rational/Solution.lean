import HodgeWitness
import Proposal.Witness
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
noncomputable section
namespace Submission
theorem witness : HodgeComputer.Verify HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q HodgeWitness.d HodgeWitness.D HodgeWitness.N HodgeWitness.Q := by
  have hF : HodgeSubmission.F = HodgeComputer.Instances.KleinRational.F := by
    apply MvPolynomial.funext; intro x
    norm_num [HodgeSubmission.F, HodgeComputer.Instances.KleinRational.F] <;> ring
  have hA : HodgeSubmission.A = HodgeComputer.Instances.KleinRational.A := by
    apply MvPolynomial.funext; intro x
    norm_num [HodgeSubmission.A, HodgeComputer.Instances.KleinRational.A] <;> ring
  have hD : HodgeWitness.D = HodgeComputer.Instances.KleinRational.D := by
    apply MvPolynomial.funext; intro x
    norm_num [HodgeWitness.D, HodgeComputer.Instances.KleinRational.D] <;> ring
  have hQ : HodgeWitness.Q = HodgeComputer.Instances.KleinRational.Q := by
    apply MvPolynomial.funext; intro x
    norm_num [HodgeWitness.Q, HodgeComputer.Instances.KleinRational.Q] <;> ring
  have hN : HodgeWitness.N = HodgeComputer.Instances.KleinRational.N := by
    funext i; fin_cases i
    · change HodgeWitness.N0 = HodgeComputer.Instances.KleinRational.N0
      apply MvPolynomial.funext; intro x
      norm_num [HodgeWitness.N0, HodgeComputer.Instances.KleinRational.N0] <;> ring
    · change HodgeWitness.N1 = HodgeComputer.Instances.KleinRational.N1
      apply MvPolynomial.funext; intro x
      norm_num [HodgeWitness.N1, HodgeComputer.Instances.KleinRational.N1] <;> ring
    · change HodgeWitness.N2 = HodgeComputer.Instances.KleinRational.N2
      apply MvPolynomial.funext; intro x
      norm_num [HodgeWitness.N2, HodgeComputer.Instances.KleinRational.N2] <;> ring
    · change HodgeWitness.N3 = HodgeComputer.Instances.KleinRational.N3
      apply MvPolynomial.funext; intro x
      norm_num [HodgeWitness.N3, HodgeComputer.Instances.KleinRational.N3] <;> ring
    · change HodgeWitness.N4 = HodgeComputer.Instances.KleinRational.N4
      apply MvPolynomial.funext; intro x
      norm_num [HodgeWitness.N4, HodgeComputer.Instances.KleinRational.N4] <;> ring
    · change HodgeWitness.N5 = HodgeComputer.Instances.KleinRational.N5
      apply MvPolynomial.funext; intro x
      norm_num [HodgeWitness.N5, HodgeComputer.Instances.KleinRational.N5] <;> ring
  simpa only [hF,hA,hD,hQ,hN,HodgeSubmission.q,HodgeWitness.d] using HodgeComputer.Instances.KleinRational.certificate
theorem certificate : HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q := ⟨HodgeWitness.d,HodgeWitness.D,HodgeWitness.N,HodgeWitness.Q,witness⟩
end Submission
