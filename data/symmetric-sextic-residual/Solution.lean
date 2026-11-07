import HodgeTarget
import Proposal.SymmetricPrimitiveEndpoint
import Proposal.SymmetricRegularCurrent
import Proposal.SymmetricCertificateTransport
import Proposal.SymmetricCoefficientField
import Proposal.SymmetricNormalTransport

/-!
# Incomplete symmetric-sextic certificate

This draft uses the ordinary protected target and proposal helper layout.
One substantive proof obligation remains below: a primitive for the explicit
reduced density. Its equivalence with the original relative primitive and
its projective transport are proved. The final theorem depends
on the remaining `sorry` placeholder and is not an accepted certificate.

The independent four-direction route in
`SymmetricBalancedTransport.certificate_of_base_coefficients` permits
normal-variable dependence in the component numerators. The full five-
component ordinary-game endpoint is
`SymmetricNormalTransport.certificate_of_weighted_game`, with a normal
component and any nonzero coefficient-space denominator. The research
obstruction to the purely normal-independent scalar-correction strategy
does not exclude these broader endpoints. No current solving their
equations has yet been supplied; the relative existence lemma below
retains its original single admission.
-/

noncomputable section
namespace Submission

/-- Remaining existence problem, with the coefficient field and its
denominator already constructed and checked. The reduced source is exactly
`2*div(W)/f_u`; no restriction on additional poles of its primitive is imposed. -/
theorem residual_primitive_exists :
    ResidueCoefficientReduction.HasPrimitive
      SymmetricCoefficientReduction.relativeTangent
      SymmetricCoefficientField.residualDensity := by
  sorry

/-- The checked coefficient-field correction recovers the original relative
primitive from the equivalent residual problem. -/
theorem relative_primitive_exists :
    Nonempty SymmetricPrimitiveEndpoint.RelativePrimitive :=
  SymmetricCoefficientField.primitive_iff_residual.mpr residual_primitive_exists

/-- The finite polynomial transport supplies a certificate, and the proved
certificate-to-current bridge gives the original regular-current endpoint. -/
theorem regular_game_of_relative_primitive
    (beta : SymmetricPrimitiveEndpoint.RelativePrimitive) :
    SymmetricRegularCurrent.RegularGameExists := by
  exact SymmetricRegularCurrent.regular_game_exists_of_certificate
    (SymmetricCertificateTransport.certificate_of_relative_primitive beta)

/-- Standard submission entry point, conditional on the unfinished primitive
existence lemma. Its transitive axioms still include sorryAx. -/
theorem certificate :
    HodgeComputer.HasCertificate
      HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A := by
  obtain ⟨gamma, hgamma⟩ := residual_primitive_exists
  exact SymmetricCoefficientField.certificate_of_residual gamma hgamma

end Submission

#print axioms Submission.regular_game_of_relative_primitive
#print axioms Submission.certificate
