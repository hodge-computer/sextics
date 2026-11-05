import Proposal.GenericCubicCertificate
import Proposal.CubicLiftAssembly
import Proposal.ClearedDenominatorLegal

noncomputable section
namespace QuadricContactSextic
open MvPolynomial QuadricContactClearing QuadricContactAssembly QuadricContactComplex
open QuadricContactLift
open scoped BigOperators

/-- The closed sextic existence theorem: the denominator, all six numerators,
homogeneity, strict differential equations, and denominator legality are proved. -/
theorem certificate : HodgeComputer.HasCertificate
    QuadricContactDenominator.targetF QuadricContactComplex.targetA 1 := by
  let D := QuadricContact.GenericCubicCertificate.D
  let N := QuadricContact.GenericCubicCertificate.N
  have hsrc : (∑ i, N i * pderiv i QuadricContactTarget.cubic) = D * (X 1 * X 2) := by
    simpa only [HodgeTestbed.directional, QuadricContact.GenericCubicCertificate.F,
      QuadricContactTarget.cubic, D, N, mul_comm] using
      QuadricContact.GenericCubicCertificate.directional_identity
  have hdiv : D * (∑ i, pderiv i (N i)) = ∑ i, N i * pderiv i D := by
    have hh := QuadricContact.GenericCubicCertificate.divergence_identity
    simpa only [HodgeTestbed.divergenceNumerator, HodgeTestbed.divergence,
      HodgeTestbed.directional, sub_eq_zero, mul_comm] using hh
  obtain ⟨n,κ,Q,P,hκ,hQ,hP,hsource,hdivergence,hprofile⟩ :=
    exists_cleared_cubic D N 27 QuadricContact.GenericCubicCertificate.D_homogeneous
      QuadricContact.GenericCubicCertificate.N_homogeneous hsrc hdiv
  have hlegal : IsRelPrime QuadricContactDenominator.targetF (complexMap (denominator Q)) := by
    apply QuadricContactClearedDenominator.denominator_legal Q n κ hκ
    exact hprofile
  have hEq := lift_strict_equations QuadricContactTarget.F QuadricContactTarget.A
    Q (P 0) (P 1) (P 2) (P 3) hsource hdivergence
  refine ⟨2*(n+27)+4, complexMap (denominator Q),
    (fun i => complexMap (numerators (P 0) (P 1) (P 2) (P 3) i)), 0, ?_⟩
  apply strict_verify
  · exact denominator_homogeneous hQ
  · intro i
    simpa only [Nat.add_assoc] using numerators_homogeneous (hP 0) (hP 1) (hP 2) (hP 3) i
  · exact hEq.e1
  · simpa only [mul_zero] using hEq.e2
  · exact hlegal

end QuadricContactSextic

#print axioms QuadricContactSextic.certificate
