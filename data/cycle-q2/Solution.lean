import HodgeTarget
import Proposal.CurrentCorrection
import Proposal.CurrentTangents
import Proposal.CurrentAmbientLift
import Proposal.CurrentDenominator

/-! A source-bound correction of the saved physical current for cycle-q2. -/

noncomputable section

namespace Submission

/-- Close the literal defect of the concrete saved current, allowing new poles. -/
theorem missing_rational_correction :
    Nonempty CycleQ2Concrete.ActualCurrentCorrection := by
  sorry

theorem certificate :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A := by
  obtain ⟨c⟩ := missing_rational_correction
  exact CycleQ2Concrete.certificate_of_actual_current_correction c

end Submission

#print axioms Submission.certificate
