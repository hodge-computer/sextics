import HodgeTarget
import Proposal.SymmetricPrimitiveEndpoint
import Proposal.SymmetricCertificateTransport

/-!
# Incomplete symmetric-sextic certificate

This draft uses the ordinary protected target and proposal helper layout.
Exactly one substantive proof obligation remains below. The final theorem
depends on its `sorry` placeholder and is not an accepted certificate.
The primitive-to-certificate transport is proved by the helpers from PR #223.
-/

noncomputable section
namespace Submission

/-- Missing geometric step: identify the actual contact correspondence with
the required residue class and prove exactness in the chart function field.
The finite contact-rank calculation alone does not establish this theorem. -/
theorem relative_primitive_exists :
    Nonempty SymmetricPrimitiveEndpoint.RelativePrimitive := by
  sorry

/-- Standard submission entry point, conditional only on primitive existence.
Its transitive axioms include sorryAx until that existence theorem is proved. -/
theorem certificate :
    HodgeComputer.HasCertificate
      HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A := by
  obtain ⟨beta⟩ := relative_primitive_exists
  exact SymmetricCertificateTransport.certificate_of_relative_primitive beta

end Submission

#print axioms Submission.certificate
