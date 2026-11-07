import HodgeTarget
import Proposal.Normalization

/-!
Incomplete cycle-q2 certificate draft. The helper modules preserve the full
protected target and the legal homogeneous witness obligations. The existence
theorem below is the remaining mathematical problem; the protected verifier
will reject this draft until its explicit admission is replaced by a proof.
-/

noncomputable section

namespace Submission

/-- Construct a legal homogeneous rational solution of the two normalized
equations for the exact protected target. This substantive existence claim
remains unproved. -/
theorem missing_rational_solution :
    Nonempty CycleQ2Assembly.NormalizedRationalSolution := by
  sorry

theorem certificate :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A := by
  exact CycleQ2Normalization.originalGoal_iff_normalized.mpr missing_rational_solution

end Submission
