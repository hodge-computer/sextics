import HodgeTestbed.Algebra
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
namespace QuadricContact.ConcreteLine
open MvPolynomial HodgeTestbed
variable {R : Type*} [CommRing R]
abbrev P (R : Type*) [CommRing R] := MvPolynomial (Fin 4) R

def cubic (p q s k u v : R) : P R :=
  C (2:R) * X 0 ^ 3 + X 0 * X 1 ^ 2 +
  X 0 * (C p * X 2 ^ 2 + C q * X 2 * X 3 + C s * X 3 ^ 2) +
  C k * X 1 * X 2 * X 3 + C u * X 2 ^ 3 + C v * X 3 ^ 3

def rel0 (p u x z : R) := 2*x^3+x*z^2+p*x+u
def rel1 (p q k x y z w : R) := 6*x^2*y+2*x*z*w+y*z^2+q*x+p*y+k*z
def rel2 (q s k x y z w : R) := 6*x*y^2+x*w^2+2*y*z*w+s*x+q*y+k*w
def rel3 (s v y w : R) := 2*y^3+y*w^2+s*y+v

def pole (x y : R) : P R := X 0-C x*X 2-C y*X 3
def nb (k x y z w : R) : P R :=
  C y*X 1+C (2*x*w+y*z+k)*X 2+C (3*y*w)*X 3
def minusNC (k x y z w : R) : P R :=
  C x*X 1+C (3*x*z)*X 2+C (x*w+2*y*z+k)*X 3
def numerator (k x y z w : R) : Fin 4 → P R :=
  ![C x*nb k x y z w-C y*minusNC k x y z w,
    C z*nb k x y z w-C w*minusNC k x y z w,
    nb k x y z w, -minusNC k x y z w]
def source (p q s k x y z w : R) : P R :=
  (C (6*x)*X 0+C (2*z)*X 1+C (6*x^2+2*p)*X 2+C (6*x*y+q)*X 3)*
      nb k x y z w -
  (C (6*y)*X 0+C (2*w)*X 1+C (6*x*y+q)*X 2+C (6*y^2+2*s)*X 3)*
      minusNC k x y z w

theorem pole_homogeneous (x y : R) : (pole x y).IsHomogeneous 1 :=
  ((isHomogeneous_X R 0).sub (isHomogeneous_C_mul_X x 2)).sub
    (isHomogeneous_C_mul_X y 3)

theorem nb_homogeneous (k x y z w : R) : (nb k x y z w).IsHomogeneous 1 :=
  ((isHomogeneous_C_mul_X y 1).add (isHomogeneous_C_mul_X (2*x*w+y*z+k) 2)).add
    (isHomogeneous_C_mul_X (3*y*w) 3)

theorem minusNC_homogeneous (k x y z w : R) : (minusNC k x y z w).IsHomogeneous 1 :=
  ((isHomogeneous_C_mul_X x 1).add (isHomogeneous_C_mul_X (3*x*z) 2)).add
    (isHomogeneous_C_mul_X (x*w+2*y*z+k) 3)

theorem numerator_homogeneous (k x y z w : R) (i : Fin 4) :
    (numerator k x y z w i).IsHomogeneous 1 := by
  fin_cases i
  · exact ((nb_homogeneous k x y z w).C_mul x).sub ((minusNC_homogeneous k x y z w).C_mul y)
  · exact ((nb_homogeneous k x y z w).C_mul z).sub ((minusNC_homogeneous k x y z w).C_mul w)
  · exact nb_homogeneous k x y z w
  · exact (minusNC_homogeneous k x y z w).neg


theorem numerator_divergence (k x y z w : R) :
    divergence (numerator k x y z w) = 0 := by
  simp only [divergence, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change pderiv 0 (C x*nb k x y z w-C y*minusNC k x y z w) +
    (pderiv 1 (C z*nb k x y z w-C w*minusNC k x y z w) +
      (pderiv 2 (nb k x y z w) + pderiv 3 (-minusNC k x y z w))) = 0
  simp only [nb, minusNC, map_add, map_sub, map_neg, pderiv_mul, pderiv_C,
    pderiv_X, Pi.single_apply]
  norm_num [Fin.ext_iff, map_ofNat]
  <;> ring

theorem numerator_tangency (k x y z w : R) :
    directional (pole x y) (numerator k x y z w) = 0 := by
  simp only [directional, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change pderiv 0 (pole x y)*(C x*nb k x y z w-C y*minusNC k x y z w) +
    (pderiv 1 (pole x y)*(C z*nb k x y z w-C w*minusNC k x y z w) +
      (pderiv 2 (pole x y)*nb k x y z w + pderiv 3 (pole x y)*(-minusNC k x y z w))) = 0
  simp only [pole, map_sub, pderiv_mul, pderiv_C, pderiv_X, Pi.single_apply]
  norm_num [Fin.ext_iff]
  <;> ring

theorem source_with_residual (p q s k u v x y z w : R) :
    directional (cubic p q s k u v) (numerator k x y z w) =
    pole x y * source p q s k x y z w +
    nb k x y z w *
      (3*C (rel0 p u x z)*X 2^2 + 2*C (rel1 p q k x y z w)*X 2*X 3 +
        C (rel2 q s k x y z w)*X 3^2) -
    minusNC k x y z w *
      (C (rel1 p q k x y z w)*X 2^2 + 2*C (rel2 q s k x y z w)*X 2*X 3 +
        3*C (rel3 s v y w)*X 3^2) := by
  simp only [directional, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  simp only [numerator, Matrix.cons_val_zero, Matrix.cons_val_succ,
    cubic, pderiv_mul, pderiv_pow, map_add, map_sub, pderiv_C, pderiv_X,
    Pi.single_apply]
  norm_num [Fin.ext_iff]
  simp only [pole, source, nb, minusNC, rel0, rel1, rel2, rel3,
    map_add, map_mul, map_pow, map_ofNat]
  ring

theorem certificate_equations (p q s k u v x y z w : R)
    (h0 : rel0 p u x z = 0) (h1 : rel1 p q k x y z w = 0)
    (h2 : rel2 q s k x y z w = 0) (h3 : rel3 s v y w = 0) :
    Equations (cubic p q s k u v) (source p q s k x y z w)
      (pole x y) (numerator k x y z w) 0 := by
  apply strict_to_equations
  · rw [source_with_residual, h0, h1, h2, h3]
    simp only [map_zero, mul_zero, zero_mul, add_zero, sub_zero]
    ring
  · unfold divergenceNumerator
    rw [numerator_divergence, numerator_tangency]
    ring

def sourceCoefficients (p q s k x y z w : R) : Fin 8 → R :=
  ![12*x^2*w-12*x*y*z+6*k*x,
    12*x*y*w-12*y^2*z-6*k*y,
    2*y*z-2*x*w,
    -2*x*z*w+2*y*z^2+2*k*z+2*p*y-q*x,
    2*y*z*w-2*x*w^2-2*k*w+q*y-2*s*x,
    (6*x^2+2*p)*(2*x*w+y*z+k)-(6*x*y+q)*(3*x*z),
    (6*x^2+2*p)*(3*y*w)+(6*x*y+q)*(2*x*w+y*z+k)-
      (6*x*y+q)*(x*w+2*y*z+k)-(6*y^2+2*s)*(3*x*z),
    (6*x*y+q)*(3*y*w)-(6*y^2+2*s)*(x*w+2*y*z+k)]

def quadraticMonomials : Fin 8 → P R :=
  ![X 0*X 2, X 0*X 3, X 1^2, X 1*X 2, X 1*X 3, X 2^2, X 2*X 3, X 3^2]

/-- All sources lie in the indicated eight-dimensional quadratic subspace. -/
theorem source_expansion (p q s k x y z w : R) :
    source p q s k x y z w =
      ∑ j : Fin 8, C (sourceCoefficients p q s k x y z w j)*quadraticMonomials j := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  simp only [sourceCoefficients, quadraticMonomials, Matrix.cons_val_zero,
    Matrix.cons_val_succ, source, nb, minusNC,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
  ring

end QuadricContact.ConcreteLine

#print axioms QuadricContact.ConcreteLine.certificate_equations
