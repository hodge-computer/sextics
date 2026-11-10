import Proposal.CubicResidueTrace
import Mathlib.Tactic.LinearCombination

/-!
# Literal source reconstruction for a cubic residue

This module identifies the coefficient condition for a quadratic numerator
to have zero cubic companion trace after division by the cube of `f_u`.
It then gives the unique linear source producing that numerator under
`P |-> f_u P_u - f_uu P`.  Subtracting a normal derivative from a quadratic
source supplies its canonical linear representative without changing the
residue density.

These are source identities.  No existence of a primitive or a contact
trace realizing the prescribed source is asserted.
-/

namespace CubicSourceReconstruction

open CubicResidueTrace Matrix
open scoped Matrix BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

section RingIdentities

variable {R : Type*} [CommRing R]

/-- Trace of an arbitrary quadratic numerator against the inverse normal
cube.  This extends the existing zero-trace identity to a complete test. -/
theorem quadratic_normal_inverse_cube_trace (a b c c0 c1 c2 : R) :
    Matrix.trace (quadraticMatrix a b c c0 c1 c2 *
      (derivativeInverseNumerator a b c)^3) =
      (3*c0-a*c1+b*c2)*(discriminantDenominator a b c)^2 := by
  simp [derivativeInverseNumerator, quadraticMatrix, companion,
    discriminantDenominator, Matrix.trace, pow_succ,
    Matrix.mul_apply, Fin.sum_univ_succ]
  ring

def cubicNormal (l B C u : R) : R := 3*l*u^2+2*B*u+C
def cubicSecond (l B u : R) : R := 6*l*u+2*B

theorem linear_source_coefficients (l B C a b u : R) :
    cubicNormal l B C u*b - cubicSecond l B u*(a+b*u) =
      (-2*B*a+C*b) - 6*l*a*u - 3*l*b*u^2 := by
  simp only [cubicNormal, cubicSecond]
  ring

/-- Adding a constant multiple of `f_u` does not change the residue source. -/
theorem normal_source_gauge (g gu p pu k : R) :
    g*(pu-k*gu)-gu*(p-k*g) = g*pu-gu*p := by
  ring

end RingIdentities

section FieldIdentities

variable {K : Type*} [Field K]

def quadraticNormalDensityMatrix (ell a b c c0 c1 c2 : K) :
    Matrix (Fin 3) (Fin 3) K :=
  (1 / (ell^3*(discriminantDenominator a b c)^3)) •
    (quadraticMatrix a b c c0 c1 c2 * (derivativeInverseNumerator a b c)^3)

/-- The complete trace functional, with its nonzero discriminant explicit. -/
theorem quadratic_normal_density_trace (ell a b c c0 c1 c2 : K)
    (hell : ell ≠ 0) (hdisc : discriminantDenominator a b c ≠ 0) :
    Matrix.trace (quadraticNormalDensityMatrix ell a b c c0 c1 c2) =
      (3*c0-a*c1+b*c2)/(ell^3*discriminantDenominator a b c) := by
  rw [quadraticNormalDensityMatrix, Matrix.trace_smul,
    quadratic_normal_inverse_cube_trace]
  simp only [smul_eq_mul]
  field_simp [hell, hdisc]

theorem quadratic_normal_density_trace_zero_iff (ell a b c c0 c1 c2 : K)
    (hell : ell ≠ 0) (hdisc : discriminantDenominator a b c ≠ 0) :
    Matrix.trace (quadraticNormalDensityMatrix ell a b c c0 c1 c2) = 0 ↔
      3*c0-a*c1+b*c2 = 0 := by
  rw [quadratic_normal_density_trace ell a b c c0 c1 c2 hell hdisc]
  simp only [div_eq_zero_iff, mul_ne_zero (pow_ne_zero 3 hell) hdisc, or_false]

variable [CharZero K]

/-- Every quadratic numerator in the trace-zero coefficient hyperplane has
this explicit linear preimage.  The identity is literal, before quotienting
by the cubic equation. -/
theorem linear_source_reconstruction (l B C c0 c1 c2 u : K)
    (hl : l ≠ 0) (htrace : 3*l*c0-B*c1+C*c2 = 0) :
    cubicNormal l B C u * (-c2/(3*l)) -
      cubicSecond l B u * (-c1/(6*l) + (-c2/(3*l))*u) =
      c0+c1*u+c2*u^2 := by
  have h3 : (3 : K)*l ≠ 0 := mul_ne_zero (by norm_num) hl
  have h0 : (B*c1-C*c2)/(3*l) = c0 := by
    apply (div_eq_iff h3).mpr
    linear_combination -htrace
  calc
    _ = (B*c1-C*c2)/(3*l)+c1*u+c2*u^2 := by
      rw [linear_source_coefficients]
      field_simp [hl]
      ring
    _ = _ := by rw [h0]

/-- The exact canonical linear representative of a quadratic source. -/
theorem quadratic_source_linear_representative (l B C p0 p1 p2 u : K)
    (hl : l ≠ 0) :
    (p0+p1*u+p2*u^2) - (p2/(3*l))*cubicNormal l B C u =
      (p0-p2*C/(3*l))+(p1-2*p2*B/(3*l))*u := by
  simp only [cubicNormal]
  field_simp [hl]
  ring

/-- Canonicalizing a quadratic source preserves the entire residue numerator. -/
theorem canonical_source_numerator (l B C p0 p1 p2 u : K)
    (hl : l ≠ 0) :
    cubicNormal l B C u*(p1+2*p2*u) -
      cubicSecond l B u*(p0+p1*u+p2*u^2) =
    cubicNormal l B C u*(p1-2*p2*B/(3*l)) -
      cubicSecond l B u*
        ((p0-p2*C/(3*l))+(p1-2*p2*B/(3*l))*u) := by
  simp only [cubicNormal, cubicSecond]
  field_simp [hl]
  ring

end FieldIdentities

end CubicSourceReconstruction

#print axioms CubicSourceReconstruction.quadratic_normal_inverse_cube_trace
#print axioms CubicSourceReconstruction.quadratic_normal_density_trace_zero_iff
#print axioms CubicSourceReconstruction.linear_source_reconstruction
#print axioms CubicSourceReconstruction.quadratic_source_linear_representative
#print axioms CubicSourceReconstruction.canonical_source_numerator
