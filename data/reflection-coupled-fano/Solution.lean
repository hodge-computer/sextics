import HodgeTarget
import Proposal.ArithmeticSeed
import Proposal.ArithmeticFamily
import Proposal.FamilyClosure
import Proposal.SourceBinding

/-!
The exact reflection-coupled-fano certificate. A checked modular quartic
gives a finite field factor over the generic complex endpoint, the actual
quartic family yields a normalized quotient certificate, and reflection
transport followed by homogeneous normalization supplies the protected
HodgeComputer.HasCertificate statement.

Prepared for contributor fqlx with OpenAI ChatGPT collaborating-agent
assistance. See solution.md for the construction, limits, and prior credit.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Submission
open ReflectionCoupledFano

theorem certificate :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q := by
  obtain ⟨I, hI, hfinite, _⟩ := Arithmetic.exists_generic_field
  letI : I.IsMaximal := hI
  letI : Module.Finite Arithmetic.GenericEndpoint (Arithmetic.CoefficientField I) := hfinite
  have h := physical_certificate_of_quartic_family (Arithmetic.arithmeticFamily I)
  rw [protected_F, protected_A, protected_q]
  simpa only [Arithmetic.complexMap_coupling] using h

end Submission

#print axioms Submission.certificate
