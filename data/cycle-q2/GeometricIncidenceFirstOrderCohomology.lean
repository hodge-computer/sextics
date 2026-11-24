import Proposal.GeometricIncidenceFirstOrderTrace
import Proposal.GeometricLiteralCanonicalClass

/-!
# The actual pointed tangent gives nonzero projective differential cohomology

The cubic part of the original seed/time-derivation dual-number path
already has a nonzero paired homogeneous Cech class. The existing
Mayer--Vietoris injection sends that exact class into genuine derived
projective H1. The existing literal canonical-sheaf isomorphism then
transports it into H1 of the projective differential sheaf on the same
literal r=57, theta=1 curve, preserving nonvanishing.

These are the existing cohomology groups and maps. No new cohomology
model or nonvanishing premise is introduced. The comparison with the
moving fixed-section curve's Abel--Jacobi class is still a separate
geometric obligation, as are support and affine residue exactness.

Source-only draft: no Lean elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric strategy and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2IncidenceFirstOrderCohomology

open CycleQ2GeometricProjectiveCurve
  CycleQ2GeometricProjectiveCanonicalH1 CycleQ2GeometricLiteralCanonicalClass
  CycleQ2IncidenceFirstOrderTrace

/-- The original Mayer--Vietoris image of the actual pointed cubic
direction, on the unchanged literal projective curve. -/
def firstOrderProjectiveClass : ProjectiveSheafH1 57 1 :=
  degreeOneToProjectiveH1 57 1 (by norm_num)
    (pairedDegreeOneClass 57 1 firstOrderCubicDirection)

theorem firstOrderProjectiveClass_ne_zero : firstOrderProjectiveClass ≠ 0 := by
  intro h
  apply firstOrder_pairedClass_ne_zero
  apply degreeOneToProjectiveH1_injective 57 1 (by norm_num)
  simpa only [firstOrderProjectiveClass, map_zero] using h

/-- Transport through the actual literal canonical-sheaf isomorphism. -/
def firstOrderDifferentialClass : DifferentialSheafH1 57 1 :=
  literalCanonicalH1Equiv firstOrderProjectiveClass

theorem firstOrderDifferentialClass_ne_zero : firstOrderDifferentialClass ≠ 0 := by
  intro h
  apply firstOrderProjectiveClass_ne_zero
  apply literalCanonicalH1Equiv.injective
  simpa only [firstOrderDifferentialClass, map_zero] using h

#print axioms firstOrderProjectiveClass_ne_zero
#print axioms firstOrderDifferentialClass_ne_zero

end CycleQ2IncidenceFirstOrderCohomology
end
