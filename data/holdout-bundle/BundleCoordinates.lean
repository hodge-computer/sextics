import Proposal.BundleConic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
The exact complementary diagonal quotient.  Coordinate order is
`X0,X1,X2,p,q,lambda`, with `p=Y0*Y1`, `q=Y1*Y2`, and
`lambda=Y1^3/(Y0^3+i*Y2^3)`.  These lemmas retain the complete volume
character; they are algebraic coordinate identities, not a certificate.
-/

noncomputable section

namespace HoldoutBundle

section ScalarCoordinates

variable {R : Type*} [Field R]

def coeffA (l : R) : R := l + l⁻¹
def coeffB (i l : R) : R := i * (l - l⁻¹)
def lambdaValue (i y0 y1 y2 : R) : R := y1^3 / (y0^3 + i*y2^3)
def densityValue (l x0 p : R) : R := -(x0^3*p)/(6*l)

theorem binary_factorization (i p q : R) (hi : i^2 = -1) :
    (p^3+i*q^3)*(p^3-i*q^3) = p^6+q^6 := by
  linear_combination -(q^6)*hi

theorem lambdaValue_ne_zero (i y0 y1 y2 : R)
    (hy1 : y1 ≠ 0) (hT : y0^3+i*y2^3 ≠ 0) :
    lambdaValue i y0 y1 y2 ≠ 0 :=
  div_ne_zero (pow_ne_zero 3 hy1) hT

theorem lambdaValue_times_factor (i y0 y1 y2 : R)
    (hT : y0^3+i*y2^3 ≠ 0) :
    lambdaValue i y0 y1 y2 * ((y0*y1)^3+i*(y1*y2)^3) = y1^6 := by
  unfold lambdaValue
  field_simp [hT] <;> ring

theorem cubic_density_equation (i y0 y1 y2 : R) (hi : i^2 = -1)
    (hy1 : y1 ≠ 0) (hT : y0^3+i*y2^3 ≠ 0) :
    coeffA (lambdaValue i y0 y1 y2)*(y0*y1)^3 +
      coeffB i (lambdaValue i y0 y1 y2)*(y1*y2)^3 =
      y0^6+y1^6+y2^6 := by
  unfold coeffA coeffB lambdaValue
  field_simp [hy1,hT]
  linear_combination -(y0^3+i*y2^3)*y2^6*hi

theorem quotient_equation_binding (i : R) (x : Fin 6 → R)
    (hi : i^2 = -1) (hy1 : x 4 ≠ 0) (hT : x 3^3+i*x 5^3 ≠ 0) :
    K (coeffA (lambdaValue i (x 3) (x 4) (x 5)))
      (coeffB i (lambdaValue i (x 3) (x 4) (x 5)))
      ![x 0,x 1,x 2,x 3*x 4,x 4*x 5] =
      x 0^6+x 1^6+x 2^6+x 3^6+x 4^6+x 5^6+
        x 0^3*x 1*x 3*x 4+x 1^3*x 2*x 4*x 5 := by
  have h := cubic_density_equation i (x 3) (x 4) (x 5) hi hy1 hT
  simp only [K, Matrix.cons_val]
  linear_combination h

variable [CharZero R]

theorem density_binding (i x0 y0 y1 y2 : R)
    (hy1 : y1 ≠ 0) (hT : y0^3+i*y2^3 ≠ 0) :
    (-6*lambdaValue i y0 y1 y2*y1) *
      densityValue (lambdaValue i y0 y1 y2) x0 (y0*y1) =
      x0^3*y0*y1^2 := by
  have hl := lambdaValue_ne_zero i y0 y1 y2 hy1 hT
  unfold densityValue
  field_simp [hl] <;> ring

/-- Full three-coordinate derivative matrix, in `(p,q,lambda)` order. -/
def diagonalJacobian (i y0 y1 y2 : R) : Matrix (Fin 3) (Fin 3) R :=
  let l := lambdaValue i y0 y1 y2
  let T := y0^3+i*y2^3
  !![y1,y0,0;
     0,y2,y1;
     -3*l*y0^2/T, 3*l/y1, -3*i*l*y2^2/T]

theorem diagonalJacobian_det (i y0 y1 y2 : R)
    (hy1 : y1 ≠ 0) (hT : y0^3+i*y2^3 ≠ 0) :
    (diagonalJacobian i y0 y1 y2).det =
      -6*lambdaValue i y0 y1 y2*y1 := by
  simp only [diagonalJacobian, Matrix.det_fin_three, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
    Matrix.cons_val_one, Matrix.cons_val]
  unfold lambdaValue
  field_simp [hy1, hT]
  ring_nf
  have hT' : y2^3*i+y0^3 ≠ 0 := by
    convert hT using 1 <;> ring
  have hT2 : y2^3*i*y0^3*2+y2^6*i^2+y0^6 ≠ 0 := by
    convert pow_ne_zero 2 hT using 1 <;> ring
  field_simp [hT', hT2]
  linear_combination -(mul_inv_cancel₀ hT2)

theorem diagonalJacobian_det_ne_zero (i y0 y1 y2 : R)
    (hy1 : y1 ≠ 0) (hT : y0^3+i*y2^3 ≠ 0) :
    (diagonalJacobian i y0 y1 y2).det ≠ 0 := by
  rw [diagonalJacobian_det i y0 y1 y2 hy1 hT]
  exact mul_ne_zero (mul_ne_zero (by norm_num)
    (lambdaValue_ne_zero i y0 y1 y2 hy1 hT)) hy1

end ScalarCoordinates

end HoldoutBundle
