import HodgeTarget
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A rational equation for the paired-sign and order-three quotient

On the protected chart X0 = 1, write (x,a,y,z,b) = (X1,X2,Y0,Y1,Y2).
The invariant coordinates are t = y*z, u = z*a^2, r = z^3, lambda = b/a.
This file checks the literal polynomial substitution, its differential
coefficients, and the transformed third-order-pole density. In particular,
the source is retained, including its factor lambda and its Jacobian sign.

These are coordinate identities. They do not assert rational exactness,
construct a primitive, or discharge Submission.missing_geometric_existence.
-/

set_option Elab.async false
set_option autoImplicit false

noncomputable section
namespace CycleQ2InvariantQuotient

variable {K : Type*} [Field K] [CharZero K]

def physicalEquation (x a y z b : K) : K :=
  1 + x^6 + a^6 + y^6 + z^6 + b^6 +
    (x*y*z + x^3*a*z*b + a^3*y*b) / 2

def physicalSource (x a y z b : K) : K := x^2*a^3*y^2*z^2*b

def quotientEquation (x t u r l : K) : K :=
  r^4 + (1 + x^6 + x*t/2 + l*x^3*u/2)*r^2 +
    ((1+l^6)*u^3 + l*t*u^2/2)*r + t^6

def quotientSource (x t u r l : K) : K := -(l*x^2*t^2*u^2*r^4)/6

theorem quotient_equation_substitution (x a y z b : K) (ha : a ≠ 0) :
    quotientEquation x (y*z) (z*a^2) (z^3) (b/a) =
      z^6 * physicalEquation x a y z b := by
  unfold quotientEquation physicalEquation
  field_simp
  <;> ring

theorem quotient_source_substitution (x a y z b : K) :
    6*a * quotientSource x (y*z) (z*a^2) (z^3) (b/a) =
      -(a*x^2*y^2*a^3*b*z^16) := by
  by_cases ha : a = 0
  · simp [ha, quotientSource]
  · unfold quotientSource
    field_simp
    <;> ring

/-- The four nontrivial rows of the quotient Jacobian, in the column order
(a,y,z,b) and row order (t,u,r,lambda). The x row is the identity. -/
def quotientJacobian (a y z b : K) : Matrix (Fin 4) (Fin 4) K :=
  !![0, z, y, 0;
     2*z*a, 0, a^2, 0;
     0, 0, 3*z^2, 0;
     -b/a^2, 0, 0, 1/a]

theorem quotientJacobian_det (a y z b : K) (ha : a ≠ 0) :
    (quotientJacobian a y z b).det = -6*z^4 := by
  have h12 : Fin.succAbove (1 : Fin 4) (2 : Fin 3) = 3 := rfl
  simp [quotientJacobian, Matrix.det_succ_row_zero, Fin.sum_univ_succ, h12]
  field_simp
  <;> ring

section Differential

variable {R : Type*} [CommRing R] [Algebra R K]

theorem differential_t (D : Derivation R K K) (y z : K) :
    D (y*z) = z*D y + y*D z := by
  simp only [Derivation.leibniz, smul_eq_mul]
  ring

theorem differential_u (D : Derivation R K K) (a z : K) :
    D (z*a^2) = 2*z*a*D a + a^2*D z := by
  simp only [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul]
  norm_num
  ring

theorem differential_r (D : Derivation R K K) (z : K) :
    D (z^3) = 3*z^2*D z := by
  norm_num [Derivation.leibniz_pow, smul_eq_mul]
  ring

theorem differential_lambda (D : Derivation R K K) (a b : K) :
    D (b/a) = -(b/a^2)*D a + (1/a)*D b := by
  simp only [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv,
    smul_eq_mul, inv_pow]
  ring

end Differential

/-- Equality of the actual rational top-form coefficients under this
coordinate change. Its scalar Jacobian is -6*z^4. -/
theorem protected_density_pullback (x a y z b : K)
    (ha : a ≠ 0) (hz : z ≠ 0) :
    quotientSource x (y*z) (z*a^2) (z^3) (b/a) /
        (quotientEquation x (y*z) (z*a^2) (z^3) (b/a))^3 * (-6*z^4) =
      physicalSource x a y z b / (physicalEquation x a y z b)^3 := by
  rw [quotient_equation_substitution x a y z b ha]
  unfold quotientSource physicalSource
  by_cases hf : physicalEquation x a y z b = 0
  · simp [hf]
  · field_simp
    <;> ring

/-- The normal coefficient of the residue of a third-order pole. The
arguments are the numerator's first three normal jets and the normal
gradient's first three jets, in that order. -/
def residueDensity (A0 A1 A2 g0 g1 g2 : K) : K :=
  (A2/g0^3 - (3*A1*g1+A0*g2)/g0^4 + 3*A0*g1^2/g0^5)/2

/-- The quotient's normal coordinate is still x. Its equation jets scale
by z^6, its numerator jets by -z^14/6, and its four-dimensional residue
Jacobian by -6*z^4. Thus the literal residue density is preserved as well
as the ambient rational form. -/
theorem residue_density_pullback (A0 A1 A2 g0 g1 g2 z : K) (hz : z ≠ 0) :
    residueDensity (-(z^14/6)*A0) (-(z^14/6)*A1) (-(z^14/6)*A2)
      (z^6*g0) (z^6*g1) (z^6*g2) * (-6*z^4) =
        residueDensity A0 A1 A2 g0 g1 g2 := by
  unfold residueDensity
  by_cases hg : g0 = 0
  · simp [hg]
  · field_simp
    <;> ring

section Protected

variable [Algebra ℂ K]

/-- Binding to the generated protected sextic, with the original coordinate
order and the affine value X0 = 1. -/
theorem protected_equation_eval (x a y z b : K) :
    MvPolynomial.eval₂ (algebraMap ℂ K) ![1,x,a,y,z,b] HodgeSubmission.F =
      physicalEquation x a y z b := by
  have htwo : algebraMap ℂ K 2 = (2 : K) := map_ofNat (algebraMap ℂ K) 2
  simp [HodgeSubmission.F, physicalEquation, htwo]
  ring

theorem protected_source_eval (x a y z b : K) :
    MvPolynomial.eval₂ (algebraMap ℂ K) ![1,x,a,y,z,b] HodgeSubmission.A =
      physicalSource x a y z b := by
  simp [HodgeSubmission.A, physicalSource]

end Protected

end CycleQ2InvariantQuotient

#print axioms CycleQ2InvariantQuotient.quotient_equation_substitution
#print axioms CycleQ2InvariantQuotient.quotientJacobian_det
#print axioms CycleQ2InvariantQuotient.protected_density_pullback
#print axioms CycleQ2InvariantQuotient.residue_density_pullback
#print axioms CycleQ2InvariantQuotient.protected_equation_eval
