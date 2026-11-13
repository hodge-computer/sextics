import Proposal.GeometricKoszulTrace
import Proposal.GeometricFormalInputs02Part03

/-!
# The finite sparse trace kills the actual homogeneous Cech class

This binds the existing degree-nine socle calculation to the actual
homogeneous chart quotient. It uses the proved polynomial relation and
the explicit quintic chart witnesses; no regular-pair hypothesis or
injectivity of a forgetful comparison is supplied.

This is an algebraic trace criterion in one direction. It does not
identify the trace with a geometric Serre trace or construct a moving
algebraic cycle.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2GeometricTraceBoundary

open MvPolynomial CycleQ2SeedTrace CycleQ2GeometricProjectiveCurve

/-- The existing finite trace-zero condition gives a boundary in the
actual degree-one homogeneous chart modules at a genuine cube root of two. -/
theorem degreeNineCechClass_zero_of_trace_zero
    (r : ℂ) (hcube : r ^ 3 = 2) (p : Poly) (hp : p.IsHomogeneous 9)
    (htrace : traceLinear r p = 0) : degreeNineCechClass r 0 p hp = 0 := by
  have hr : r ≠ 0 := by
    intro hz
    rw [hz] at hcube
    norm_num at hcube
  apply CycleQ2GeometricKoszulTrace.degreeNineCechClass_zero_of_reducedIdeal
    r hr p hp
  simpa only [htrace, map_zero, zero_mul, sub_zero] using
    (CycleQ2SeedTrace.homogeneous_degreeNine_mod_trace r hcube hp)

end CycleQ2GeometricTraceBoundary

end
