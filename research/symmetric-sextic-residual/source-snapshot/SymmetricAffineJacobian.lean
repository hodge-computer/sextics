import WeightedPrimitiveTransportCore
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The exact six-coordinate Jacobian and projective source coefficient

The input order is `(a,lambda,b,c,d,v)` and the output order is
`(X0,X1,X2,Y0,Y1,Y2)`. The map is
`X=a*(1+v,1-v,b)`, `Y=a*(c+lambda*v,c-lambda*v,d)`.

The polynomial derivative matrix is proved equal to the displayed matrix,
whose determinant is `+4*a^5*v`. The scale identities are bound to the
protected polynomials. Their combination proves the exact rational source
coefficient after radial contraction of the ambient volume. This last
statement is a coefficient identity; it does not assume or construct any
differential-form primitive.
-/

noncomputable section

namespace SymmetricAffineJacobian

open MvPolynomial
open WeightedPrimitiveTransport

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

def chartPolynomials : Fin 6 → MvPolynomial (Fin 6) ℂ :=
  let X := MvPolynomial.X (R := ℂ)
  ![X 0*(1+X 5), X 0*(1-X 5), X 0*X 2,
    X 0*(X 3+X 1*X 5), X 0*(X 3-X 1*X 5), X 0*X 4]

def chartCoordinates (a lam b c d v : ℂ) : Fin 6 → ℂ :=
  ![a*(1+v),a*(1-v),a*b,a*(c+lam*v),a*(c-lam*v),a*d]

theorem chartPolynomials_eval (a lam b c d v : ℂ) (i : Fin 6) :
    eval ![a,lam,b,c,d,v] (chartPolynomials i) =
      chartCoordinates a lam b c d v i := by
  fin_cases i <;> simp [chartPolynomials, chartCoordinates]

def polynomialJacobian (p : Fin 6 → ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j => eval p (pderiv j (chartPolynomials i))

def chartJacobian (a lam b c d v : ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  !![1+v, 0, 0, 0, 0, a;
     1-v, 0, 0, 0, 0, -a;
     b, 0, a, 0, 0, 0;
     c+lam*v, a*v, 0, a, 0, a*lam;
     c-lam*v, -a*v, 0, a, 0, -a*lam;
     d, 0, 0, 0, a, 0]

/-- Every entry is the actual polynomial partial derivative of the chart. -/
theorem polynomialJacobian_eq (a lam b c d v : ℂ) :
    polynomialJacobian ![a,lam,b,c,d,v] = chartJacobian a lam b c d v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [polynomialJacobian, chartPolynomials, chartJacobian] <;> ring

/-- The sign uses exactly `(a,lambda,b,c,d,v)`, without reordering a volume. -/
theorem chartJacobian_det (a lam b c d v : ℂ) :
    (chartJacobian a lam b c d v).det = 4*a^5*v := by
  simp [chartJacobian, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix]
  dsimp [Fin.succAbove, Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  ring

theorem exact_polynomial_jacobian_det (a lam b c d v : ℂ) :
    (polynomialJacobian ![a,lam,b,c,d,v]).det = 4*a^5*v := by
  rw [polynomialJacobian_eq, chartJacobian_det]

/-- The protected sextic has precisely the required sixth-power scale. -/
theorem exactF_scaled_chart (a lam b c d v : ℂ) :
    eval (chartCoordinates a lam b c d v) HodgeSubmission.F =
      a^6 * eval ![lam,b,c,d,v] chartEquation := by
  rw [exact_chart_equation]
  change SymmetricReflections.evaluateF (a*(1+v)) (a*(1-v)) (a*b)
    (a*(c+lam*v)) (a*(c-lam*v)) (a*d) =
    a^6 * SymmetricReflections.evaluateF (1+v) (1-v) b
      (c+lam*v) (c-lam*v) d
  simp only [SymmetricReflections.evaluateF_eq]
  ring

/-- The protected numerator has the same sixth-power scale. -/
theorem exactA_scaled_chart (a lam b c d v : ℂ) :
    eval (chartCoordinates a lam b c d v) HodgeSubmission.A =
      a^6 * eval (chartCoordinates 1 lam b c d v) HodgeSubmission.A := by
  change SymmetricReflections.evaluateA (a*(1+v)) (a*(1-v)) (a*b)
    (a*(c+lam*v)) (a*(c-lam*v)) (a*d) =
    a^6 * SymmetricReflections.evaluateA (1*(1+v)) (1*(1-v)) (1*b)
      (1*(c+lam*v)) (1*(c-lam*v)) (1*d)
  simp only [SymmetricReflections.evaluateA_eq]
  ring

theorem exactA_scaled_source (a lam b c d v : ℂ) :
    4*v * eval (chartCoordinates a lam b c d v) HodgeSubmission.A =
      a^6 * eval ![lam,b,c,d,v] chartSource := by
  rw [exactA_scaled_chart, exact_chart_source]
  simp only [chartCoordinates, one_mul]
  ring

/-- Radial contraction multiplies the ordinary Jacobian by `a`. -/
theorem projective_jacobian_factor (a lam b c d v : ℂ) :
    a * (polynomialJacobian ![a,lam,b,c,d,v]).det = 4*a^6*v := by
  rw [exact_polynomial_jacobian_det]
  ring

/-- Exact coefficient of the projective source in the ordered affine volume.
The equation is valid as a field identity, with only the chart scale nonzero;
no hidden factor of `a`, `v`, or the monic leading coefficient remains. -/
theorem exact_projective_source_coefficient (a lam b c d v : ℂ) (ha : a ≠ 0) :
    eval (chartCoordinates a lam b c d v) HodgeSubmission.A *
        (a * (polynomialJacobian ![a,lam,b,c,d,v]).det) /
      (eval (chartCoordinates a lam b c d v) HodgeSubmission.F)^2 =
    eval ![lam,b,c,d,v] chartSource /
      (eval ![lam,b,c,d,v] chartEquation)^2 := by
  rw [projective_jacobian_factor, exactF_scaled_chart, exactA_scaled_chart,
    exact_chart_source]
  simp only [chartCoordinates, one_mul]
  by_cases hH : eval ![lam,b,c,d,v] chartEquation = 0
  · simp [hH]
  · field_simp
    <;> ring

#print axioms chartPolynomials_eval
#print axioms polynomialJacobian_eq
#print axioms exact_polynomial_jacobian_det
#print axioms exactF_scaled_chart
#print axioms exactA_scaled_source
#print axioms exact_projective_source_coefficient

end SymmetricAffineJacobian
