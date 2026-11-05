import HodgeWitness
import Proposal.Witness
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
noncomputable section
namespace Submission
theorem witness : HodgeComputer.Verify HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q HodgeWitness.d HodgeWitness.D HodgeWitness.N HodgeWitness.Q := by
  have hF : HodgeSubmission.F = HodgeComputer.Instances.FamilyRootCube.F := by
    apply MvPolynomial.funext; intro x
    norm_num [HodgeSubmission.F, HodgeComputer.Instances.FamilyRootCube.F] <;> ring
  have hA : HodgeSubmission.A = HodgeComputer.Instances.FamilyRootCube.A := by
    apply MvPolynomial.funext; intro x
    norm_num [HodgeSubmission.A, HodgeComputer.Instances.FamilyRootCube.A] <;> ring
  have hD : HodgeWitness.D = HodgeComputer.Instances.FamilyRootCube.D := by
    apply MvPolynomial.funext; intro x
    norm_num [HodgeWitness.D, HodgeComputer.Instances.FamilyRootCube.D] <;> ring
  have hQ : HodgeWitness.Q = HodgeComputer.Instances.FamilyRootCube.Q := by
    apply MvPolynomial.funext; intro x
    norm_num [HodgeWitness.Q, HodgeComputer.Instances.FamilyRootCube.Q] <;> ring
  have hN : HodgeWitness.N = HodgeComputer.Instances.FamilyRootCube.N := by
    funext i; fin_cases i
    · change HodgeWitness.N0 = HodgeComputer.Instances.FamilyRootCube.N0
      apply MvPolynomial.funext; intro x
      norm_num [HodgeWitness.N0, HodgeComputer.Instances.FamilyRootCube.N0] <;> ring
    · change HodgeWitness.N1 = HodgeComputer.Instances.FamilyRootCube.N1
      apply MvPolynomial.funext; intro x
      norm_num [HodgeWitness.N1, HodgeComputer.Instances.FamilyRootCube.N1] <;> ring
    · change HodgeWitness.N2 = HodgeComputer.Instances.FamilyRootCube.N2
      apply MvPolynomial.funext; intro x
      norm_num [HodgeWitness.N2, HodgeComputer.Instances.FamilyRootCube.N2] <;> ring
    · change HodgeWitness.N3 = HodgeComputer.Instances.FamilyRootCube.N3
      apply MvPolynomial.funext; intro x
      norm_num [HodgeWitness.N3, HodgeComputer.Instances.FamilyRootCube.N3] <;> ring
    · change HodgeWitness.N4 = HodgeComputer.Instances.FamilyRootCube.N4
      apply MvPolynomial.funext; intro x
      norm_num [HodgeWitness.N4, HodgeComputer.Instances.FamilyRootCube.N4] <;> ring
    · change HodgeWitness.N5 = HodgeComputer.Instances.FamilyRootCube.N5
      apply MvPolynomial.funext; intro x
      norm_num [HodgeWitness.N5, HodgeComputer.Instances.FamilyRootCube.N5] <;> ring
  simpa only [hF,hA,hD,hQ,hN,HodgeSubmission.q,HodgeWitness.d] using HodgeComputer.Instances.FamilyRootCube.certificate
theorem certificate : HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q := ⟨HodgeWitness.d,HodgeWitness.D,HodgeWitness.N,HodgeWitness.Q,witness⟩
end Submission
