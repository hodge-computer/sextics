import HodgeWitness
import Proposal.Witness
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
noncomputable section
namespace Submission
theorem witness : HodgeComputer.Verify HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q HodgeWitness.d HodgeWitness.D HodgeWitness.N HodgeWitness.Q := by
  have hF : HodgeSubmission.F = HodgeComputer.Instances.CoupledPairRationalD4Strict.F := by
    apply MvPolynomial.funext; intro x
    norm_num [HodgeSubmission.F, HodgeComputer.Instances.CoupledPairRationalD4Strict.F] <;> ring
  have hA : HodgeSubmission.A = HodgeComputer.Instances.CoupledPairRationalD4Strict.A := by
    apply MvPolynomial.funext; intro x
    norm_num [HodgeSubmission.A, HodgeComputer.Instances.CoupledPairRationalD4Strict.A] <;> ring
  have hD : HodgeWitness.D = HodgeComputer.Instances.CoupledPairRationalD4Strict.D := by
    apply MvPolynomial.funext; intro x
    norm_num [HodgeWitness.D, HodgeComputer.Instances.CoupledPairRationalD4Strict.D] <;> ring
  have hQ : HodgeWitness.Q = HodgeComputer.Instances.CoupledPairRationalD4Strict.Q := by
    apply MvPolynomial.funext; intro x
    norm_num [HodgeWitness.Q, HodgeComputer.Instances.CoupledPairRationalD4Strict.Q] <;> ring
  have hN : HodgeWitness.N = HodgeComputer.Instances.CoupledPairRationalD4Strict.N := by
    funext i; fin_cases i
    · change HodgeWitness.N0 = HodgeComputer.Instances.CoupledPairRationalD4Strict.N0
      apply MvPolynomial.funext; intro x
      norm_num [HodgeWitness.N0, HodgeComputer.Instances.CoupledPairRationalD4Strict.N0] <;> ring
    · change HodgeWitness.N1 = HodgeComputer.Instances.CoupledPairRationalD4Strict.N1
      apply MvPolynomial.funext; intro x
      norm_num [HodgeWitness.N1, HodgeComputer.Instances.CoupledPairRationalD4Strict.N1] <;> ring
    · change HodgeWitness.N2 = HodgeComputer.Instances.CoupledPairRationalD4Strict.N2
      apply MvPolynomial.funext; intro x
      norm_num [HodgeWitness.N2, HodgeComputer.Instances.CoupledPairRationalD4Strict.N2] <;> ring
    · change HodgeWitness.N3 = HodgeComputer.Instances.CoupledPairRationalD4Strict.N3
      apply MvPolynomial.funext; intro x
      norm_num [HodgeWitness.N3, HodgeComputer.Instances.CoupledPairRationalD4Strict.N3] <;> ring
    · change HodgeWitness.N4 = HodgeComputer.Instances.CoupledPairRationalD4Strict.N4
      apply MvPolynomial.funext; intro x
      norm_num [HodgeWitness.N4, HodgeComputer.Instances.CoupledPairRationalD4Strict.N4] <;> ring
    · change HodgeWitness.N5 = HodgeComputer.Instances.CoupledPairRationalD4Strict.N5
      apply MvPolynomial.funext; intro x
      norm_num [HodgeWitness.N5, HodgeComputer.Instances.CoupledPairRationalD4Strict.N5] <;> ring
  simpa only [hF,hA,hD,hQ,hN,HodgeSubmission.q,HodgeWitness.d] using HodgeComputer.Instances.CoupledPairRationalD4Strict.certificate
theorem certificate : HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q := ⟨HodgeWitness.d,HodgeWitness.D,HodgeWitness.N,HodgeWitness.Q,witness⟩
end Submission
