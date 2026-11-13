import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

/-!
Exact finite algebra from the saved sparse Chapter 3D seed.
The matrix is the SCALED trace-pairing matrix recorded in solution.md.
Its identification with geometric trace pairings is not formalized here.
No cohomology, divisor support, or cycle-q2 certificate is asserted.
-/

noncomputable section
namespace CycleQ2GeometricSeed
open Matrix

/-- Seven scaled Noether--Lefschetz rows followed by the derivative row. -/
def seedMatrix : Matrix (Fin 8) (Fin 9) ℂ :=
  ![![(-1 + -Complex.I), 0, 1, 0, 1, 0, 0, 0, 0],
    ![1, 0, -2 * Complex.I, (-4 + -2 * Complex.I), (1 + Complex.I), -2 * Complex.I, 0, 0, 0],
    ![0, -2 * Complex.I, 0, -4, 0, -2 * Complex.I, 0, 0, 0],
    ![1, 0, (1 + Complex.I), -2 * Complex.I, 0, 0, 0, 0, 0],
    ![1, (1 + Complex.I), 0, -2 * Complex.I, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, -1],
    ![0, 0, 0, -2 * Complex.I, 0, 2, 2 * Complex.I, (-1 + -Complex.I), 0],
    ![0, 0, 0, 0, 0, 0, 0, (-1 + -Complex.I), 0]]

/-- An explicit rational Gaussian right inverse; no solver is called by Lean. -/
def seedRightInverse : Matrix (Fin 9) (Fin 8) ℂ :=
  ![![((-1 / 2) + (-1 / 2) * Complex.I), (1 / 2), (-1 + (-1 / 2) * Complex.I), (1 + (1 / 2) * Complex.I), ((-1 / 2) + (-3 / 2) * Complex.I), 0, 0, 0],
    ![((1 / 2) + (-1 / 2) * Complex.I), (1 / 2) * Complex.I, -Complex.I, ((-1 / 2) + Complex.I), ((3 / 2) + (-3 / 2) * Complex.I), 0, 0, 0],
    ![((1 / 2) + (-1 / 2) * Complex.I), (1 / 2) * Complex.I, -Complex.I, (1 / 2) * Complex.I, (1 + -Complex.I), 0, 0, 0],
    ![((-1 / 4) + (-1 / 4) * Complex.I), (1 / 4), (-3 / 4), ((1 / 2) + (1 / 4) * Complex.I), ((-3 / 4) + (-3 / 4) * Complex.I), 0, 0, 0],
    ![((1 / 2) + (-1 / 2) * Complex.I), (1 / 2), ((-1 / 2) + (-1 / 2) * Complex.I), ((1 / 2) + Complex.I), -Complex.I, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![((-1 / 4) + (-1 / 4) * Complex.I), (1 / 4), (-3 / 4), ((1 / 2) + (1 / 4) * Complex.I), ((-3 / 4) + (-3 / 4) * Complex.I), 0, (-1 / 2) * Complex.I, (1 / 2) * Complex.I],
    ![0, 0, 0, 0, 0, 0, 0, ((-1 / 2) + (1 / 2) * Complex.I)],
    ![0, 0, 0, 0, 0, -1, 0, 0]]

/-- Coefficients of I*x0^2*x1 + (I-1)*x0^3 in the displayed cubic basis. -/
def seedTangent : Fin 9 → ℂ := ![0, 0, 0, 0, 0, 0, Complex.I, Complex.I - 1, 0]

def tangentImage : Fin 8 → ℂ := ![0, 0, 0, 0, 0, 0, 0, 2]

set_option maxHeartbeats 4000000 in
theorem seed_right_inverse : seedMatrix * seedRightInverse = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, seedMatrix, seedRightInverse] <;>
    ring_nf <;> norm_num [Complex.I_sq]

set_option maxHeartbeats 1000000 in
theorem seed_tangent_image : seedMatrix.mulVec seedTangent = tangentImage := by
  ext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      seedMatrix, seedTangent, tangentImage] <;>
    ring_nf <;> norm_num [Complex.I_sq]

/-- Concrete finite inputs only. The geometric interpretation is a separate gate. -/
structure FiniteSeedInputs : Prop where
  right_inverse : seedMatrix * seedRightInverse = 1
  tangent_image : seedMatrix.mulVec seedTangent = tangentImage

theorem finiteSeedInputs : FiniteSeedInputs where
  right_inverse := seed_right_inverse
  tangent_image := seed_tangent_image

#print axioms seed_right_inverse
#print axioms seed_tangent_image
#print axioms finiteSeedInputs
end CycleQ2GeometricSeed
