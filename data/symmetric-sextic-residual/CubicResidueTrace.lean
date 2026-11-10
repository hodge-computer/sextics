import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases

/-!
# Exact trace cancellation for the cubic reflection cover

For f(U)=U^3+a*U^2+b*U+c and a quadratic P, the coefficient
2*(f'*P'-f''*P)/f'^3 has trace zero. The companion-matrix identities below
are polynomial identities, with no primitive, cohomology, or support
hypothesis. The finite-root identity gives the same calculation on the
three distinct sheets. Consequently the unordered-pair source is the
negative original source under the complementary-root identification.

This is a source computation, not an existence proof for a primitive.
-/

namespace CubicResidueTrace

open Matrix
open scoped Matrix BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

section RingIdentities

variable {R : Type*} [CommRing R]

def companion (a b c : R) : Matrix (Fin 3) (Fin 3) R :=
  !![0,0,-c; 1,0,-b; 0,1,-a]

def quadraticMatrix (a b c p0 p1 p2 : R) : Matrix (Fin 3) (Fin 3) R :=
  p0 • (1 : Matrix (Fin 3) (Fin 3) R) +
    p1 • companion a b c + p2 • (companion a b c)^2

def discriminantDenominator (a b c : R) : R :=
  4*a^3*c-a^2*b^2-18*a*b*c+4*b^3+27*c^2

def derivativeInverseNumerator (a b c : R) : Matrix (Fin 3) (Fin 3) R :=
  quadraticMatrix a b c (-a^2*b-3*a*c+4*b^2)
    (-2*a^3+7*a*b-9*c) (-2*a^2+6*b)

def residueNumerator (a b c p0 p1 p2 : R) : Matrix (Fin 3) (Fin 3) R :=
  quadraticMatrix a b c (b*p1-2*a*p0) (2*b*p2-6*p0) (2*a*p2-3*p1)

/-- The matrix numerator is exactly multiplication by f'P'-f''P. -/
theorem residue_numerator_binding (a b c p0 p1 p2 : R) :
    residueNumerator a b c p0 p1 p2 =
      quadraticMatrix a b c b (2*a) 3 * quadraticMatrix a b c p1 (2*p2) 0 -
      quadraticMatrix a b c (2*a) 6 0 * quadraticMatrix a b c p0 p1 p2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [residueNumerator, quadraticMatrix, companion, pow_succ,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
      norm_num [Matrix.one_apply] <;> ring

theorem companion_cubic (a b c : R) :
    (companion a b c)^3 + a • (companion a b c)^2 +
      b • companion a b c + c • (1 : Matrix (Fin 3) (Fin 3) R) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [companion, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem derivative_inverse_numerator (a b c : R) :
    quadraticMatrix a b c b (2*a) 3 * derivativeInverseNumerator a b c =
      discriminantDenominator a b c • (1 : Matrix (Fin 3) (Fin 3) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quadraticMatrix, derivativeInverseNumerator, companion,
      discriminantDenominator, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ] <;>
      norm_num [Matrix.one_apply] <;> ring

/-- The entire numerator vanishes before inverting the discriminant. -/
theorem companion_residue_numerator_trace (a b c p0 p1 p2 : R) :
    Matrix.trace (residueNumerator a b c p0 p1 p2 *
      (derivativeInverseNumerator a b c)^3) = 0 := by
  simp [residueNumerator, derivativeInverseNumerator, quadraticMatrix,
    companion, Matrix.trace, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

end RingIdentities

section FieldIdentities

variable {K : Type*} [Field K]

def companionResidue (ell a b c p0 p1 p2 : K) : Matrix (Fin 3) (Fin 3) K :=
  (2 / (ell^2 * (discriminantDenominator a b c)^3)) •
    (residueNumerator a b c p0 p1 p2 * (derivativeInverseNumerator a b c)^3)

theorem companion_residue_binding (ell a b c p0 p1 p2 : K) :
    companionResidue ell a b c p0 p1 p2 =
      (2/ell^2) • ((quadraticMatrix a b c b (2*a) 3 *
        quadraticMatrix a b c p1 (2*p2) 0 -
        quadraticMatrix a b c (2*a) 6 0 * quadraticMatrix a b c p0 p1 p2) *
        ((discriminantDenominator a b c)⁻¹ • derivativeInverseNumerator a b c)^3) := by
  rw [← residue_numerator_binding, smul_pow, Matrix.mul_smul, smul_smul]
  simp [companionResidue, div_eq_mul_inv, mul_inv_rev, inv_pow, mul_assoc, mul_comm]

theorem companion_residue_trace_zero (ell a b c p0 p1 p2 : K) :
    Matrix.trace (companionResidue ell a b c p0 p1 p2) = 0 := by
  simp [companionResidue, Matrix.trace_smul, companion_residue_numerator_trace]

/-- The explicit matrix is genuinely the inverse of multiplication by f'. -/
theorem derivative_matrix_inverse (a b c : K)
    (h : discriminantDenominator a b c ≠ 0) :
    quadraticMatrix a b c b (2*a) 3 *
      ((discriminantDenominator a b c)⁻¹ • derivativeInverseNumerator a b c) = 1 := by
  rw [Matrix.mul_smul, derivative_inverse_numerator, smul_smul]
  simp [h]

def sheetResidue (ell p0 p1 p2 x y z : K) : K :=
  2 * (((x-y)*(x-z))*(p1+2*p2*x) -
    2*(2*x-y-z)*(p0+p1*x+p2*x^2)) /
    (ell^2 * (((x-y)*(x-z))^3))

/-- Trace on three distinct sheets; all denominator conditions are explicit. -/
theorem three_sheet_residue_trace (ell p0 p1 p2 x y z : K)
    (hell : ell ≠ 0) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    sheetResidue ell p0 p1 p2 x y z +
      sheetResidue ell p0 p1 p2 y x z +
      sheetResidue ell p0 p1 p2 z x y = 0 := by
  have hxy' := sub_ne_zero.mpr hxy
  have hyx' := sub_ne_zero.mpr hxy.symm
  have hxz' := sub_ne_zero.mpr hxz
  have hzx' := sub_ne_zero.mpr hxz.symm
  have hyz' := sub_ne_zero.mpr hyz
  have hzy' := sub_ne_zero.mpr hyz.symm
  unfold sheetResidue
  field_simp
  <;> ring

/-- The cubic unordered-pair cover carries minus the original source. -/
theorem complementary_pair_source (ell p0 p1 p2 x y z : K)
    (hell : ell ≠ 0) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    sheetResidue ell p0 p1 p2 x y z + sheetResidue ell p0 p1 p2 y x z =
      -sheetResidue ell p0 p1 p2 z x y := by
  exact eq_neg_of_add_eq_zero_left
    (three_sheet_residue_trace ell p0 p1 p2 x y z hell hxy hxz hyz)

end FieldIdentities

#print axioms companion_cubic
#print axioms residue_numerator_binding
#print axioms derivative_inverse_numerator
#print axioms companion_residue_numerator_trace
#print axioms companion_residue_trace_zero
#print axioms companion_residue_binding
#print axioms derivative_matrix_inverse
#print axioms three_sheet_residue_trace
#print axioms complementary_pair_source

end CubicResidueTrace
