import Proposal.PhysicalNormalTransport

/-! Exact coefficient bindings for the physical mixed-biweight cubic.
The integral Jacobian API uses scales216 and5832; these identities bind its
coefficients to the actual prescribed physical equation. Adapted by fqlx with
OpenAI Codex assistance from the accepted cycle-three construction. -/
noncomputable section
namespace CyclePhysicalJacobianCoefficients
open CyclePhysical CyclePhysicalCoordinates

lemma a8_scaling : CycleJacobian.a8 cOne cTwo 1 radial (radial*t)=
    216*radial^4*TransitiveCubic.s4 coeffA coeffB coeffC coeffD coeffE coeffF := by
  simp only [CycleJacobian.a8,TransitiveCubic.s4,TransitiveCubic.s4Numerator,
    coeffA,coeffB,coeffC,coeffD,coeffE,coeffF,t]
  ring
lemma b256_scaling : CycleJacobian.b256 cOne cTwo 1 radial (radial*t)=
    5832*radial^6*(-TransitiveCubic.s6 coeffA coeffB coeffC coeffD coeffE coeffF/4) := by
  simp only [CycleJacobian.b256,TransitiveCubic.s6,TransitiveCubic.s6Numerator,
    coeffA,coeffB,coeffC,coeffD,coeffE,coeffF,t]
  ring
end CyclePhysicalJacobianCoefficients
