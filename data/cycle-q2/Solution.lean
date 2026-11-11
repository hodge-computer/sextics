import HodgeTarget
import Proposal.GeometricTarget
import Proposal.GeometricSeed
import Proposal.GeometricFormalInputs

/-!
Nonconstructive geometric route for the unchanged cycle-q2 target.

DRAFT: the algebraic residue-to-certificate bridge is proved and bound to the
actual projective affine chart. Geometric primitive existence remains open.
The admission below is that precise existence obligation, not a routine
tactic gap. The protected theorem still depends on sorryAx. No completed
solve is claimed.

The previous explicit-current development is preserved in Current*.lean and
is no longer an import dependency of this entry point.
-/

noncomputable section
namespace CycleQ2Nonconstructive

/-- The actual remaining geometric obligation in the chart X0 = 1.
The field is Frac(C[x0,...,x4]/(F(1,x))). Its four tangent derivations and
normal-source coefficient are concrete definitions, not assumed operators
or identities. A nonconstructive existence proof suffices. -/
def AffineResiduePrimitiveExists : Prop :=
  ∃ w : Fin 4 → CycleQ2AffineHypersurface.AffineFunctionField,
    CycleQ2AffineResidueClosure.affineResidueExpression
      CycleQ2AffineClearing.affineA w = 0

end CycleQ2Nonconstructive

namespace Submission

/-- UNPROVED: establish primitive existence from geometric support and the
algebraic de Rham comparison, or prove this concrete existential directly.
The checked finite seed/Higgs calculations alone do not supply this theorem.
All subsequent algebraic steps to the protected target are proved. -/
theorem missing_geometric_existence :
    CycleQ2Nonconstructive.AffineResiduePrimitiveExists := by
  sorry

theorem certificate :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A := by
  exact CycleQ2AffineResidueClosure.protected_certificate_of_affine_residue_primitive
    missing_geometric_existence

end Submission

#print axioms CycleQ2AffineResidueClosure.protected_certificate_of_affine_residue_primitive
#print axioms Submission.certificate
