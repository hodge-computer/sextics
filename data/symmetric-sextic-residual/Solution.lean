import HodgeTarget
import Proposal.SymmetricPrimitiveEndpoint
import Proposal.SymmetricRegularCurrent
import Proposal.SymmetricCertificateTransport

/-!
# Incomplete symmetric-sextic certificate

This draft uses the ordinary protected target and proposal helper layout.
One substantive proof obligation remains below: existence of the relative
primitive. Its projective transport is proved. The final theorem depends
on the remaining `sorry` placeholder and is not an accepted certificate.
-/

noncomputable section
namespace Submission

/-- Missing geometric step: identify the actual contact correspondence with
the required residue class and prove exactness in the chart function field.
The finite contact-rank calculation alone does not establish this theorem. -/
theorem relative_primitive_exists :
    Nonempty SymmetricPrimitiveEndpoint.RelativePrimitive := by
  sorry

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
  obtain ⟨beta⟩ := relative_primitive_exists
  exact SymmetricCertificateTransport.certificate_of_relative_primitive beta

end Submission

#print axioms Submission.regular_game_of_relative_primitive
#print axioms Submission.certificate
