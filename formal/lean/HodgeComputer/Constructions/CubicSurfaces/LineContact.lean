import HodgeTestbed.Algebra
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Extracted from `HeadOfNaps`’s holdout-q2 proof (#124).
The coefficient and denominator hypotheses remain explicit. -/

/-! The elementary line primitive for the holdout cubic. Coordinate order is
`U,V,S,T`, and the line is `S=eU+fV`, `T=gU+hV`. This adapts the accepted
`quadric-contact-broken/ConcreteLine.lean` construction to the new cubic. -/
noncomputable section
namespace HodgeComputer.CubicSurfaces.LineContact
open MvPolynomial HodgeTestbed
variable {R : Type*} [CommRing R]
abbrev P (R : Type*) [CommRing R] := MvPolynomial (Fin 4) R

def cubic (a b c d : R) : P R :=
  X 2 ^ 3 - C (3:R) * X 2 * X 3 ^ 2 +
  C a * X 0 ^ 3 + C b * X 1 ^ 3 + C c * X 0 ^ 2 * X 1 + C d * X 1 ^ 2 * X 3

def rel0 (a e g : R) := e^3-3*e*g^2+a
def rel1 (c e f g h : R) := 3*e^2*f-6*e*g*h-3*f*g^2+c
def rel2 (d e f g h : R) := 3*e*f^2-3*e*h^2-6*f*g*h+d*g
def rel3 (b d f h : R) := f^3-3*f*h^2+b+d*h

def pole (e f : R) : P R := X 2-C e*X 0-C f*X 1

def nb (d e f g h : R) : P R :=
  C (-3*f)*X 3+C (-3*(f*g+2*e*h))*X 0+C (2*d-9*f*h)*X 1

def minusNC (e f g h : R) : P R :=
  C (-3*e)*X 3+C (-9*e*g)*X 0+C (-3*(e*h+2*f*g))*X 1

def numerator (d e f g h : R) : Fin 4 → P R :=
  ![nb d e f g h, -minusNC e f g h,
    C e*nb d e f g h-C f*minusNC e f g h,
    C g*nb d e f g h-C h*minusNC e f g h]

def source (d e f g h : R) : P R :=
  (C (3*e)*X 2+C (3*e^2)*X 0+C (3*e*f)*X 1-C (6*g)*X 3)*nb d e f g h -
  (C (3*f)*X 2+C (3*e*f)*X 0+C (3*f^2)*X 1-C (6*h)*X 3)*minusNC e f g h

theorem pole_homogeneous (e f : R) : (pole e f).IsHomogeneous 1 :=
  ((isHomogeneous_X R 2).sub (isHomogeneous_C_mul_X e 0)).sub
    (isHomogeneous_C_mul_X f 1)

theorem nb_homogeneous (d e f g h : R) : (nb d e f g h).IsHomogeneous 1 :=
  ((isHomogeneous_C_mul_X (-3*f) 3).add
    (isHomogeneous_C_mul_X (-3*(f*g+2*e*h)) 0)).add
    (isHomogeneous_C_mul_X (2*d-9*f*h) 1)

theorem minusNC_homogeneous (e f g h : R) : (minusNC e f g h).IsHomogeneous 1 :=
  ((isHomogeneous_C_mul_X (-3*e) 3).add
    (isHomogeneous_C_mul_X (-9*e*g) 0)).add
    (isHomogeneous_C_mul_X (-3*(e*h+2*f*g)) 1)

theorem numerator_homogeneous (d e f g h : R) (i : Fin 4) :
    (numerator d e f g h i).IsHomogeneous 1 := by
  fin_cases i
  · exact nb_homogeneous d e f g h
  · exact (minusNC_homogeneous e f g h).neg
  · exact ((nb_homogeneous d e f g h).C_mul e).sub
      ((minusNC_homogeneous e f g h).C_mul f)
  · exact ((nb_homogeneous d e f g h).C_mul g).sub
      ((minusNC_homogeneous e f g h).C_mul h)

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

theorem numerator_divergence (d e f g h : R) :
    divergence (numerator d e f g h) = 0 := by
  simp only [divergence, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  simp only [numerator, Matrix.cons_val_zero, Matrix.cons_val_succ,
    nb, minusNC, map_add, map_sub, map_neg, pderiv_mul, pderiv_C,
    pderiv_X, Pi.single_apply]
  norm_num [Fin.ext_iff, map_ofNat]
  ring

theorem numerator_tangency (d e f g h : R) :
    directional (pole e f) (numerator d e f g h) = 0 := by
  simp only [directional, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  simp only [numerator, Matrix.cons_val_zero, Matrix.cons_val_succ,
    pole, map_sub, pderiv_mul, pderiv_C, pderiv_X, Pi.single_apply]
  norm_num [Fin.ext_iff]

theorem source_with_residual (a b c d e f g h : R) :
    directional (cubic a b c d) (numerator d e f g h) =
    pole e f * source d e f g h +
    nb d e f g h *
      (3*C (rel0 a e g)*X 0^2+2*C (rel1 c e f g h)*X 0*X 1+
        C (rel2 d e f g h)*X 1^2) -
    minusNC e f g h *
      (C (rel1 c e f g h)*X 0^2+2*C (rel2 d e f g h)*X 0*X 1+
        3*C (rel3 b d f h)*X 1^2) := by
  simp only [directional, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  simp only [numerator, Matrix.cons_val_zero, Matrix.cons_val_succ,
    cubic, pderiv_mul, pderiv_pow, map_add, map_sub, pderiv_C, pderiv_X,
    Pi.single_apply]
  norm_num [Fin.ext_iff]
  simp only [pole, source, nb, minusNC, rel0, rel1, rel2, rel3,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
  ring

theorem certificate_equations (a b c d e f g h : R)
    (h0 : rel0 a e g = 0) (h1 : rel1 c e f g h = 0)
    (h2 : rel2 d e f g h = 0) (h3 : rel3 b d f h = 0) :
    Equations (cubic a b c d) (source d e f g h)
      (pole e f) (numerator d e f g h) 0 := by
  apply strict_to_equations
  · rw [source_with_residual, h0, h1, h2, h3]
    simp only [map_zero, mul_zero, zero_mul, add_zero, sub_zero]
    ring
  · unfold divergenceNumerator
    rw [numerator_divergence, numerator_tangency]
    ring

def sourceCoefficients (d e f g h : R) : Fin 10 → R :=
  ![-18*e^3*h+18*e^2*f*g,
    6*d*e^2-36*e^2*f*h+36*e*f^2*g,
    -18*e^2*h+18*e*f*g,
    -18*e*g*h+18*f*g^2,
    6*d*e*f-18*e*f^2*h+18*f^3*g,
    6*d*e-18*e*f*h+18*f^2*g,
    -12*d*g-18*e*h^2+18*f*g*h,
    0, 0, -18*e*h+18*f*g]

def quadraticMonomials : Fin 10 → P R :=
  ![X 0^2, X 0*X 1, X 0*X 2, X 0*X 3, X 1^2,
    X 1*X 2, X 1*X 3, X 2^2, X 2*X 3, X 3^2]

theorem source_expansion (d e f g h : R) :
    source d e f g h =
      ∑ j : Fin 10, C (sourceCoefficients d e f g h j)*quadraticMonomials j := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  simp only [sourceCoefficients, quadraticMonomials, Matrix.cons_val_zero,
    Matrix.cons_val_succ, source, nb, minusNC,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero]
  ring

theorem sourceCoefficients_map {S : Type*} [CommRing S] (φ : R →+* S)
    (d e f g h : R) (i : Fin 10) :
    φ (sourceCoefficients d e f g h i) =
      sourceCoefficients (φ d) (φ e) (φ f) (φ g) (φ h) i := by
  fin_cases i <;> simp [sourceCoefficients, map_ofNat]

/-- Columns are the four constant vector fields, in order U,V,S,T. -/
def gradientCoefficients (a b c d : R) : Matrix (Fin 10) (Fin 4) R :=
  !![3*a, c, 0, 0;
     2*c, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0;
     0, 3*b, 0, d;
     0, 0, 0, 0;
     0, 2*d, 0, 0;
     0, 0, 3, 0;
     0, 0, 0, -6;
     0, 0, -3, 0]

theorem gradient_expansion (a b c d : R) (i : Fin 4) :
    pderiv i (cubic a b c d) =
      ∑ j : Fin 10, C (gradientCoefficients a b c d j i)*quadraticMonomials j := by
  fin_cases i <;>
    simp only [cubic, pderiv_mul, pderiv_pow, map_add, map_sub, pderiv_C,
      pderiv_X, Pi.single_apply] <;>
    norm_num [Fin.ext_iff] <;>
    simp only [gradientCoefficients, quadraticMonomials, Fin.sum_univ_succ,
      Fin.sum_univ_zero, add_zero, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one,
      map_mul, map_neg, map_ofNat, map_zero] <;>
    ring

theorem gradientCoefficients_map {S : Type*} [CommRing S] (φ : R →+* S)
    (a b c d : R) (i : Fin 10) (j : Fin 4) :
    φ (gradientCoefficients a b c d i j) =
      gradientCoefficients (φ a) (φ b) (φ c) (φ d) i j := by
  fin_cases i <;> fin_cases j <;> simp [gradientCoefficients, map_ofNat]

end HodgeComputer.CubicSurfaces.LineContact
#print axioms HodgeComputer.CubicSurfaces.LineContact.certificate_equations
