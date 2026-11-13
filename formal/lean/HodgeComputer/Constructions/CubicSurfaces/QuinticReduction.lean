import HodgeTestbed.Algebra
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Extracted from `HeadOfNaps`’s holdout-q2 proof (#124).
The coefficient and denominator hypotheses remain explicit. -/

/-!
# Direct quintic Jacobian reduction for the holdout cubic

The four explicitly displayed cubic polynomials replace the 56 by 56 matrix
inverse in the preliminary construction. Their common coefficient denominator
is regular at the good coefficient point (2,2,1,1). All identities are universal
polynomial identities, with no computational oracle or algebraic existence axiom.
-/

noncomputable section
namespace HodgeComputer.CubicSurfaces.QuinticReduction
open MvPolynomial HodgeTestbed
open scoped BigOperators

variable {R : Type*} [CommRing R]
abbrev Poly := MvPolynomial (Fin 4) R

/-- Active coordinate order is U,V,S,T. -/
def term (v : R) (i j k : Fin 4) : Poly (R := R) := C v * X i * X j * X k

/-- The normalized cubic after replacing the old T coordinate by k*T. -/
def cubic (a b c d : R) : Poly (R := R) :=
  term a 0 0 0 + term b 1 1 1 + term c 0 0 1 +
    term 1 2 2 2 - term 3 2 3 3 + term d 1 1 3

/-- Two compact coefficient factors of the Jacobian discriminant. -/
def r (a b c : R) : R := 27*a^2*b + 4*c^3
def e (a b c d : R) : R := r a b c ^ 4 - 2916*a^8*d^6
def denominator (a b c d : R) : R := r a b c * e a b c d

/-- Cleared coefficient numerators of the polynomial Jacobian primitive. -/
def numerators (a b c d : R) : Fin 4 → Poly (R := R) :=
  let z := r a b c
  let w := e a b c d
  ![term (9*a*b*w) 0 1 1 +
      term (1296*z*a^5*c^3*d^4) 0 1 2 +
      term (24*z^3*a*c^3*d) 0 1 3 -
      term (23328*a^7*c^3*d^5) 0 2 3 -
      term (432*z^2*a^3*c^3*d^2) 0 3 3 -
      term (6*b*c*w) 1 1 1 +
      term (5832*z*a^6*b*c*d^4) 1 1 2 +
      term (16*c*d*(729*a^8*d^6-z^3*c^3)) 1 1 3 +
      term (15552*a^6*c^4*d^5) 1 2 3 +
      term (288*z^2*a^2*c^4*d^2) 1 3 3 -
      term (69984*a^8*c*d^6) 2 3 3 -
      term (1296*z^2*a^4*c*d^3) 3 3 3,
    term (4*c^2*w) 0 1 1 -
      term (3888*z*a^6*c^2*d^4) 0 1 2 -
      term (72*z^3*a^2*c^2*d) 0 1 3 +
      term (69984*a^8*c^2*d^5) 0 2 3 +
      term (1296*z^2*a^4*c^2*d^2) 0 3 3 -
      term (648*z^2*a^5*d^4) 1 1 2 -
      term (34992*a^9*d^7) 1 1 3 +
      term (209952*a^9*d^6) 2 3 3 +
      term (3888*z^2*a^5*d^3) 3 3 3,
    term (3888*z^2*a^5*b*d^3) 1 1 3 +
      term (2592*z^2*a^5*d^4) 1 3 3,
    term (1944*z^2*a^5*b*d^3) 1 1 2 +
      term (104976*a^9*b*d^6) 1 1 3 +
      term (1296*z^2*a^5*d^4) 1 2 3 +
      term (69984*a^9*d^7) 1 3 3]

set_option maxHeartbeats 2000000

/-- The complete quintic reduction, with only scalar coefficient clearing. -/
theorem source (a b c d : R) :
    directional (cubic a b c d) (numerators a b c d) =
      C (denominator a b c d) * (X 0 ^ 3 * X 1 ^ 2) := by
  classical
  simp only [directional, Fin.sum_univ_four, cubic, term, map_add, map_sub,
    pderiv_mul, pderiv_C, pderiv_X, Pi.single_apply, Fin.isValue]
  norm_num [Fin.ext_iff]
  simp only [numerators, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    term, denominator, e, r, map_add, map_sub, map_mul, map_pow, map_ofNat]

  ring

theorem term_homogeneous (v : R) (i j k : Fin 4) :
    (term v i j k).IsHomogeneous 3 := by
  exact (((isHomogeneous_X R i).C_mul v).mul
    (isHomogeneous_X R j)).mul (isHomogeneous_X R k)

theorem cubic_homogeneous (a b c d : R) :
    (cubic a b c d).IsHomogeneous 3 := by
  unfold cubic
  repeat first
    | apply IsHomogeneous.add
    | apply IsHomogeneous.sub
    | exact term_homogeneous _ _ _ _

theorem numerators_homogeneous (a b c d : R) (i : Fin 4) :
    (numerators a b c d i).IsHomogeneous 3 := by
  fin_cases i <;> simp only [numerators]
  all_goals
    repeat first
      | apply IsHomogeneous.add
      | apply IsHomogeneous.sub
      | exact term_homogeneous _ _ _ _

/-- Normalize once an inverse has been supplied in the coefficient localization. -/
def primitive (a b c d u : R) : Fin 4 → Poly (R := R) :=
  fun i => C u * numerators a b c d i

theorem primitive_source (a b c d u : R)
    (hu : u * denominator a b c d = 1) :
    directional (cubic a b c d) (primitive a b c d u) = X 0 ^ 3 * X 1 ^ 2 := by
  unfold primitive
  rw [directional_mul, source, ← mul_assoc, ← map_mul, hu, map_one, one_mul]

theorem primitive_homogeneous (a b c d u : R) (i : Fin 4) :
    (primitive a b c d u i).IsHomogeneous 3 :=
  (numerators_homogeneous a b c d i).C_mul u

end HodgeComputer.CubicSurfaces.QuinticReduction
