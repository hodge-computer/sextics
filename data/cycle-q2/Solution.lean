import HodgeTarget
import Proposal.GeometricTarget
import Proposal.GeometricSeed
import Proposal.GeometricFormalInputs

/-!
Nonconstructive geometric route for the unchanged cycle-q2 target.

DRAFT: the algebraic residue-to-certificate bridge is proved and bound to the
actual projective affine chart. The genuine relative exterior forms, their
degree-three derivative, the local formal residue density, and the actual
universal exterior pullback are now proved.
Geometric primitive existence remains open.
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

/-- The equivalent remaining assertion in genuine mathlib exterior powers
of the actual relative Kaehler module over the complex numbers. -/
def AffineResidueFormExact : Prop :=
  ∃ η : CycleQ2AffineExterior.Form 3,
    CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm CycleQ2AffineClearing.affineA

theorem exact_form_iff_primitive :
    AffineResidueFormExact ↔ AffineResiduePrimitiveExists :=
  CycleQ2AffineExactness.exact_residueSourceForm_iff CycleQ2AffineClearing.affineA

end CycleQ2Nonconstructive

namespace Submission

/-- UNPROVED: establish actual exterior-form exactness from geometric support
and global algebraic de Rham comparison, or prove this existential directly.
The checked finite seed/Higgs calculations alone do not supply this theorem.
All subsequent algebraic steps to the protected target are proved. -/
theorem missing_geometric_existence :
    CycleQ2Nonconstructive.AffineResidueFormExact := by
  sorry

theorem certificate :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A := by
  exact CycleQ2AffineExactness.protected_certificate_of_exact_residueSourceForm
    missing_geometric_existence

end Submission

#print axioms CycleQ2Nonconstructive.exact_form_iff_primitive
#print axioms CycleQ2AffineExactness.protected_certificate_of_exact_residueSourceForm
#print axioms CycleQ2FormalResidue.residueSourceForm_eq_formalResidue
#print axioms CycleQ2NormalChart.exteriorPullback_ambientCoordinateVolume
#print axioms CycleQ2AffineWeightedTransfer.protected_certificate_of_relative_primitive
#print axioms Submission.certificate
