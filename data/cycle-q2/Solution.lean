import HodgeTarget
import Proposal.GeometricTarget
import Proposal.GeometricSeed

/-!
Nonconstructive geometric route for the unchanged cycle-q2 target.

DRAFT: the geometric support and certificate bridge have not been formalized.
The admission below is the entire remaining existence obligation, not a
routine tactic gap. A development build would still leave the protected
theorem dependent on sorryAx. No completed solve is claimed.

The previous explicit-current development is preserved in Current*.lean and
is no longer an import dependency of this entry point.
-/

noncomputable section
namespace CycleQ2Nonconstructive

/-- The fixed-instance consequence of Chapters 3D and 1 after separating the
finite algebraic inputs. This definition proves nothing about support.

Its proof must still bind the seed matrix to the geometric trace pairings,
prove smoothness, integrate the Hodge locus, construct and specialize the
supported projector, transfer support, and obtain the legal homogeneous
certificate. It is NOT a theorem for arbitrary symmetric hypersurfaces. -/
def GeometricExistenceBridge : Prop :=
  CycleQ2GeometricTarget.AlgebraicInputs →
    CycleQ2GeometricSeed.FiniteSeedInputs →
      HodgeComputer.HasCertificate
        HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A

/-- Conditional assembly only; the input h must be proved, not postulated. -/
theorem certificate_of_geometric_bridge (h : GeometricExistenceBridge) :
    HodgeComputer.HasCertificate
      HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A :=
  h CycleQ2GeometricTarget.algebraicInputs CycleQ2GeometricSeed.finiteSeedInputs

end CycleQ2Nonconstructive

namespace Submission

/-- UNPROVED: formalize the geometric support and support-to-certificate chain.
The already separated finite algebra is not a proof of this implication. -/
theorem missing_geometric_existence :
    CycleQ2Nonconstructive.GeometricExistenceBridge := by
  sorry

theorem certificate :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A := by
  exact CycleQ2Nonconstructive.certificate_of_geometric_bridge missing_geometric_existence

end Submission

#print axioms CycleQ2Nonconstructive.certificate_of_geometric_bridge
#print axioms Submission.certificate
