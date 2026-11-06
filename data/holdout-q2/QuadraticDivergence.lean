import HodgeComputer.Constructions.CubicSurfaces.QuinticReduction
import HodgeComputer.Constructions.CubicSurfaces.Q2Reduction
import Proposal.QuadraticSolver

namespace HodgeComputer.CubicSurfaces.QuinticReduction
theorem denominator_good : denominator (2 : ℚ) 2 1 1 = 515198970880 := by
  norm_num [denominator, e, r]

theorem denominator_good_ne_zero : denominator (2 : ℚ) 2 1 1 ≠ 0 := by
  rw [denominator_good]
  norm_num

end HodgeComputer.CubicSurfaces.QuinticReduction


/-! The actual divergence source for the explicit quintic Jacobian primitive.
The expansion uses the same ten monomials as the generic contact solver. -/
noncomputable section
open scoped BigOperators
namespace HoldoutQ2.QuadraticDivergence
open MvPolynomial HodgeTestbed
variable {R : Type*} [CommRing R]

/-- Coefficients in order U²,UV,US,UT,V²,VS,VT,S²,ST,T². -/
def coefficients (a b c d : R) : Fin 10 → R :=
  let z := HodgeComputer.CubicSurfaces.QuinticReduction.r a b c
  let w := HodgeComputer.CubicSurfaces.QuinticReduction.e a b c d
  ![0,
    8*c^2*w,
    -3888*z*a^6*c^2*d^4,
    -72*z^3*a^2*c^2*d,
    9*a*b*w+104976*a^9*b*d^6,
    1296*z*a^5*c^3*d^4,
    24*z^3*a*c^3*d+69984*a^9*d^7,
    0,
    -23328*a^7*c^3*d^5,
    -432*z^2*a^3*c^3*d^2]

set_option maxHeartbeats 2000000
 theorem numerators_divergence (a b c d : R) :
    divergence (HodgeComputer.CubicSurfaces.QuinticReduction.numerators a b c d) =
      QuadraticSolver.quadratic (coefficients a b c d) := by
  simp only [divergence, Fin.sum_univ_four, HodgeComputer.CubicSurfaces.QuinticReduction.numerators,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, HodgeComputer.CubicSurfaces.QuinticReduction.term,
    map_add, map_sub, pderiv_mul, pderiv_C, pderiv_X, Pi.single_apply, Fin.isValue]
  norm_num [Fin.ext_iff]
  simp only [QuadraticSolver.quadratic, coefficients, HodgeComputer.CubicSurfaces.LineContact.quadraticMonomials,
    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_zero]
  ring

/-- Scalar normalization of the primitive gives the same scalar normalization
of every source coefficient. -/
def normalizedCoefficients (a b c d u : R) : Fin 10 → R :=
  fun i => u * coefficients a b c d i

 theorem primitive_divergence (a b c d u : R) :
    divergence (HodgeComputer.CubicSurfaces.QuinticReduction.primitive a b c d u) =
      QuadraticSolver.quadratic (normalizedCoefficients a b c d u) := by
  unfold HodgeComputer.CubicSurfaces.QuinticReduction.primitive
  rw [HodgeComputer.CubicSurfaces.Q2Reduction.divergence_C_mul, numerators_divergence]
  simp only [QuadraticSolver.quadratic, normalizedCoefficients,
    map_mul, Finset.mul_sum, mul_assoc]

 theorem cubic_eq (a b c d : R) :
    HodgeComputer.CubicSurfaces.QuinticReduction.cubic a b c d = HodgeComputer.CubicSurfaces.LineContact.cubic a b c d := by
  simp only [HodgeComputer.CubicSurfaces.QuinticReduction.cubic, HodgeComputer.CubicSurfaces.QuinticReduction.term, HodgeComputer.CubicSurfaces.LineContact.cubic, map_one]
  ring

end HoldoutQ2.QuadraticDivergence
#print axioms HoldoutQ2.QuadraticDivergence.primitive_divergence
