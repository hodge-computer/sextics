import HodgeTarget
import Proposal.Normalization

/-! Radial normalization for the protected cycle-q2 certificate. -/

noncomputable section

namespace Submission

/-- The remaining existence of a legal homogeneous normalized rational current. -/
theorem missing_rational_solution :
    Nonempty CycleQ2Assembly.NormalizedRationalSolution := by
  sorry

theorem certificate :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A := by
  exact CycleQ2Normalization.originalGoal_iff_normalized.mpr missing_rational_solution

end Submission

#print axioms Submission.certificate
