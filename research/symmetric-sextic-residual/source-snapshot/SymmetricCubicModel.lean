import SymmetricReflections
import Mathlib.Tactic.FieldSimp
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
The exact protected `symmetric-sextic-residual` polynomials in the general-cubic
chart X=(1+v,1-v,r), Y=(z+lambda*v,z-lambda*v,s*z).

The import binds these identities to the unmodified generated HodgeTarget.
The results are polynomial and field identities only; they do not assert a
moving-point family, a trace identity, a differential-form primitive, or a
certificate.
-/

noncomputable section
namespace SymmetricCubicModel

set_option maxHeartbeats 2000000

def qx (r w : ℂ) : ℂ := 1 + 2 * r - w
def qy (s lam x w : ℂ) : ℂ := (1 + 2 * s) * x - lam ^ 2 * w

def originalCubic (r s lam x w : ℂ) : ℂ :=
  r ^ 6 + s ^ 6 * x ^ 3 + 2 + 30 * w + 30 * w ^ 2 + 2 * w ^ 3
  + 2 * x ^ 3 + 30 * lam ^ 2 * x ^ 2 * w
  + 30 * lam ^ 4 * x * w ^ 2 + 2 * lam ^ 6 * w ^ 3
  + (5 / 7 : ℂ) * qx r w ^ 2 * qy s lam x w
  + (10 / 7 : ℂ) * qx r w * qy s lam x w ^ 2

/-- Evaluation of the exact protected sextic, rather than an assumed model. -/
theorem exactF_affine_chart (r s lam z v : ℂ) :
    MvPolynomial.eval ![1 + v, 1 - v, r, z + lam * v, z - lam * v, s * z]
      HodgeSubmission.F = originalCubic r s lam (z ^ 2) (v ^ 2) := by
  change SymmetricReflections.transformedF 1 r z (s * z) v (lam * v) = _
  rw [SymmetricReflections.transformedF_formula]
  unfold originalCubic qx qy
  ring

/-- Evaluation of the exact protected numerator on the same chart. -/
theorem exactA_affine_chart (r s lam z v : ℂ) :
    MvPolynomial.eval ![1 + v, 1 - v, r, z + lam * v, z - lam * v, s * z]
      HodgeSubmission.A = r * s * z * (1 - v ^ 2) * (z ^ 2 - lam ^ 2 * v ^ 2) := by
  change SymmetricReflections.transformedA 1 r z (s * z) v (lam * v) = _
  rw [SymmetricReflections.transformedA_formula]
  ring

def ell (lam : ℂ) : ℂ :=
  (14 * lam ^ 6 - 10 * lam ^ 4 - 5 * lam ^ 2 + 14) / 7

def coefficient2 (r s lam x : ℂ) : ℂ :=
  30 + 30 * lam ^ 4 * x
  + (10 / 7 : ℂ) * (1 + 2 * r) * (lam ^ 2 + lam ^ 4)
  + (5 / 7 : ℂ) * (1 + 4 * lam ^ 2) * (1 + 2 * s) * x

def coefficient1 (r s lam x : ℂ) : ℂ :=
  30 - (5 / 7 : ℂ) * lam ^ 2 * (1 + 2 * r) ^ 2
  - (10 / 7 : ℂ) * (1 + 2 * lam ^ 2) * (1 + 2 * r) * (1 + 2 * s) * x
  + (30 * lam ^ 2 - (10 / 7 : ℂ) * (1 + 2 * s) ^ 2) * x ^ 2

def coefficient0 (r s x : ℂ) : ℂ :=
  r ^ 6 + 2 + (5 / 7 : ℂ) * (1 + 2 * r) ^ 2 * (1 + 2 * s) * x
  + (10 / 7 : ℂ) * (1 + 2 * r) * (1 + 2 * s) ^ 2 * x ^ 2
  + (s ^ 6 + 2) * x ^ 3

/-- In particular, the coefficient of `w^3` is the displayed `ell`, independent
of `r,s,x`. This is a full cubic expansion, not merely an evaluation at a point. -/
theorem originalCubic_expansion (r s lam x w : ℂ) :
    originalCubic r s lam x w =
      ell lam * w ^ 3 + coefficient2 r s lam x * w ^ 2
        + coefficient1 r s lam x * w + coefficient0 r s x := by
  unfold originalCubic qx qy ell coefficient2 coefficient1 coefficient0
  ring

def monicCubic (r s lam x w : ℂ) : ℂ :=
  w ^ 3 + (coefficient2 r s lam x / ell lam) * w ^ 2
  + (coefficient1 r s lam x / ell lam) * w
  + coefficient0 r s x / ell lam

/-- Actual monic normalization on its stated nonvanishing chart. -/
theorem monic_normalization (r s lam x w : ℂ) (hell : ell lam ≠ 0) :
    originalCubic r s lam x w / ell lam = monicCubic r s lam x w := by
  rw [originalCubic_expansion]
  unfold monicCubic
  field_simp

theorem ell_at_zero : ell 0 = 2 := by
  norm_num [ell]

/-- The same exact equation on the affine cone, with the scale retained. -/
theorem exactF_scaled_chart (a r s lam z v : ℂ) :
    MvPolynomial.eval
      ![a * (1 + v), a * (1 - v), a * r,
        a * (z + lam * v), a * (z - lam * v), a * s * z]
      HodgeSubmission.F = a ^ 6 * originalCubic r s lam (z ^ 2) (v ^ 2) := by
  change SymmetricReflections.evaluateF _ _ _ _ _ _ = _
  rw [SymmetricReflections.evaluateF_eq]
  unfold originalCubic qx qy
  ring

theorem exactA_scaled_chart (a r s lam z v : ℂ) :
    MvPolynomial.eval
      ![a * (1 + v), a * (1 - v), a * r,
        a * (z + lam * v), a * (z - lam * v), a * s * z]
      HodgeSubmission.A =
      a ^ 6 * (r * s * z * (1 - v ^ 2) * (z ^ 2 - lam ^ 2 * v ^ 2)) := by
  change SymmetricReflections.evaluateA _ _ _ _ _ _ = _
  rw [SymmetricReflections.evaluateA_eq]
  ring

/-- Polynomial coordinates of the scaled chart. The input order is
`(a,r,z,s,v,lambda)` and the output order is `(X0,X1,X2,Y0,Y1,Y2)`. -/
def chartPolynomials : Fin 6 → MvPolynomial (Fin 6) ℂ :=
  let X := MvPolynomial.X (R := ℂ)
  ![X 0 * (1 + X 4), X 0 * (1 - X 4), X 0 * X 1,
    X 0 * (X 2 + X 5 * X 4), X 0 * (X 2 - X 5 * X 4),
    X 0 * X 3 * X 2]

def polynomialJacobian (p : Fin 6 → ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j => MvPolynomial.eval p (MvPolynomial.pderiv j (chartPolynomials i))

def chartJacobian (a r z s v lam : ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  !![1 + v, 0, 0, 0, a, 0;
     1 - v, 0, 0, 0, -a, 0;
     r, a, 0, 0, 0, 0;
     z + lam * v, 0, a, 0, a * lam, a * v;
     z - lam * v, 0, a, 0, -a * lam, -a * v;
     s * z, 0, a * s, a * z, 0, 0]

/-- The displayed matrix is bound to the polynomial partial derivatives. -/
theorem polynomialJacobian_eq (a r z s v lam : ℂ) :
    polynomialJacobian ![a,r,z,s,v,lam] = chartJacobian a r z s v lam := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [polynomialJacobian, chartPolynomials, chartJacobian]
    <;> ring

/-- The full six-coordinate sign and scale before replacing `v²` by `w`. -/
theorem chartJacobian_det (a r z s v lam : ℂ) :
    (chartJacobian a r z s v lam).det = 4 * a ^ 5 * v * z := by
  simp [chartJacobian, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Matrix.submatrix]
  dsimp [Fin.succAbove, Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  ring

theorem exact_polynomial_jacobian_det (a r z s v lam : ℂ) :
    (polynomialJacobian ![a,r,z,s,v,lam]).det = 4 * a ^ 5 * v * z := by
  rw [polynomialJacobian_eq, chartJacobian_det]

end SymmetricCubicModel

#print axioms SymmetricCubicModel.exactF_affine_chart
#print axioms SymmetricCubicModel.exactA_affine_chart
#print axioms SymmetricCubicModel.originalCubic_expansion
#print axioms SymmetricCubicModel.monic_normalization
#print axioms SymmetricCubicModel.ell_at_zero
#print axioms SymmetricCubicModel.exactF_scaled_chart
#print axioms SymmetricCubicModel.exactA_scaled_chart
#print axioms SymmetricCubicModel.polynomialJacobian_eq
#print axioms SymmetricCubicModel.chartJacobian_det
#print axioms SymmetricCubicModel.exact_polynomial_jacobian_det
