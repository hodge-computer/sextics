import HodgeTarget
import Proposal.PhysicalField

/-! Exact binding to the protected immutable mixed-polar input. -/
noncomputable section
namespace MixedPolarTargetBinding

theorem equation : HodgeSubmission.F=MixedPolarPhysical.sextic := by
  unfold HodgeSubmission.F MixedPolarPhysical.sextic
  ring

theorem source : HodgeSubmission.A=MixedPolarPhysical.source := by
  unfold HodgeSubmission.A MixedPolarPhysical.source
  ring

theorem pole_order : HodgeSubmission.q=1 := rfl

end MixedPolarTargetBinding
