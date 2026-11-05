import Proposal.BundleCertificate
import Proposal.BundleTarget

/-!
The protected holdout-bundle certificate. The new complementary quotient
handles X0^3 Y0 Y1^2; the accepted Fermat-cover construction handles
X0^3 Y0^3. Certificate addition retains both quotient remainders.

Prepared with OpenAI ChatGPT collaborating-agent assistance, using the
repository's shared moving-conic, residue, finite-trace, and clearing
machinery credited in the accompanying explanation.
-/

namespace Submission

theorem certificate :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q :=
  HoldoutBundle.protected_certificate_of_bundle HoldoutBundle.bundle_certificate

end Submission

#print axioms Submission.certificate
