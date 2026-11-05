import Proposal.SexticAssembly
import Proposal.PassiveQ2
import Proposal.DenominatorFiberLink

noncomputable section
namespace HoldoutFinalAssembly
open MvPolynomial

theorem endpointCertificate_of_norm {k : ℂ} (hk : k^2+k+1=0)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M K : Matrix ι ι ℂ)
    (hK : (M^3+(5 : ℂ) • (1 : Matrix ι ι ℂ))*K=1)
    (hD : HoldoutSexticAssembly.activeNormFiber k (HoldoutQ2.PassiveQ2.D k hk)=
      Polynomial.C (6 : ℂ)*HoldoutDenominator.normFiber M) :
    HodgeComputer.HasCertificate HoldoutEndpointTarget.F
      (HoldoutEndpointTarget.reflectionTarget k) 2 := by
  have he := HoldoutQ2.PassiveQ2.equations k hk
  apply HoldoutSexticAssembly.hasCertificate_endpoint_from_cubic hk
    (HoldoutQ2.PassiveQ2.D k hk) (HoldoutQ2.PassiveQ2.N k hk) 27
    (HoldoutQ2.PassiveQ2.D_homogeneous k hk) (HoldoutQ2.PassiveQ2.N_homogeneous k hk)
    ?_ ?_ M K 6 (by norm_num) hK hD
  · simpa only [HodgeTestbed.directional,HoldoutQ2.PassiveQ2.F,
      HoldoutQ2.PassiveQ2.source,HoldoutQ2.PassiveQ2.parameterPolynomialMap,
      HoldoutSexticAssembly.regularCubic,HoldoutSexticAssembly.regularSource,mul_comm]
      using he.1
  · exact sub_eq_zero.mp (by
      simpa only [HodgeTestbed.divergenceNumerator,HodgeTestbed.divergence,
        HodgeTestbed.directional,mul_comm] using he.2)

theorem endpointCertificate (k : ℂ) (hk : k^2+k+1=0) :
    HodgeComputer.HasCertificate HoldoutEndpointTarget.F
      (HoldoutEndpointTarget.reflectionTarget k) 2 := by
  apply endpointCertificate_of_norm hk
    HoldoutQ2.DenominatorFiberLink.complexSumMatrix
    HoldoutQ2.DenominatorFiberLink.complexInverseMatrix
    HoldoutQ2.DenominatorFiberLink.complex_matrix_inverse
  unfold HoldoutQ2.PassiveQ2.D HoldoutQ2.PassiveQ2.coefficientPolynomialMap
  rw [HoldoutQ2.GenericQ2.D_eq]
  exact HoldoutQ2.DenominatorFiberLink.passive_q2Denominator_fiber k hk

/-- The constructed cubic solver supplies both endpoint fields; their exact
linear combination serves the immutable holdout-q2 numerator. -/
theorem certificate : HodgeComputer.HasCertificate
    HoldoutEndpointTarget.F HoldoutEndpointTarget.A 2 :=
  HoldoutEndpointTarget.hasCertificate_of_endpoint_solver endpointCertificate

end HoldoutFinalAssembly

#print axioms HoldoutFinalAssembly.endpointCertificate_of_norm
#print axioms HoldoutFinalAssembly.certificate
