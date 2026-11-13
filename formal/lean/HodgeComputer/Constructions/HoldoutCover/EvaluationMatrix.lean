import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/- Source component: EvaluationMatrix -/
section
/-! The evaluation matrix of the polynomial curve family is nonsingular.
The proof uses two single-column/row Laplace expansions and the determinant
of the identity matrix. No derivative construction is assumed here. -/

noncomputable section
set_option maxRecDepth 10000

namespace HoldoutConstruction

variable {R : Type*} [CommRing R]

theorem det_single_first_column {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) R)
    (h : ∀ i : Fin n, M i.succ 0 = 0) :
    Matrix.det M = M 0 0 * Matrix.det (M.submatrix Fin.succ Fin.succ) := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [h]

theorem det_single_first_row {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) R)
    (h : ∀ i : Fin n, M 0 i.succ = 0) :
    Matrix.det M = M 0 0 * Matrix.det (M.submatrix Fin.succ Fin.succ) := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp [h]

/-- The normal and time columns are followed by the three endpoint columns.
The unspecified top-row and time-column entries do not affect the determinant. -/
theorem endpoint_evaluation_det (M : Matrix (Fin 5) (Fin 5) R) (g k : R)
    (hnormal : ∀ i : Fin 5, M i 0 = if i = 0 then g else 0)
    (htime : M 1 1 = k)
    (hmiddle : ∀ j : Fin 3, M 1 j.succ.succ = 0)
    (hendpoints : ∀ i j : Fin 3,
      M i.succ.succ j.succ.succ = if i = j then 1 else 0) :
    Matrix.det M = g*k := by
  have hc (i : Fin 4) : M i.succ 0 = 0 := by
    rw [hnormal, if_neg (Fin.succ_ne_zero i)]
  rw [det_single_first_column M hc]
  have hr (j : Fin 3) : (M.submatrix Fin.succ Fin.succ) 0 j.succ = 0 := by
    exact hmiddle j
  rw [det_single_first_row (M.submatrix Fin.succ Fin.succ) hr]
  have hi : (M.submatrix Fin.succ Fin.succ).submatrix Fin.succ Fin.succ =
      (1 : Matrix (Fin 3) (Fin 3) R) := by
    ext i j
    exact hendpoints i j
  rw [hi, Matrix.det_one, mul_one]
  change M 0 0 * M 1 1 = g*k
  rw [hnormal, if_pos rfl, htime]

/-- Constant coefficient commutes with the determinant. -/
theorem polynomial_evaluation_det_constant
    (M : Matrix (Fin 5) (Fin 5) (Polynomial R)) (g k : R)
    (hnormal : ∀ i : Fin 5, (M i 0).coeff 0 = if i = 0 then g else 0)
    (htime : (M 1 1).coeff 0 = k)
    (hmiddle : ∀ j : Fin 3, (M 1 j.succ.succ).coeff 0 = 0)
    (hendpoints : ∀ i j : Fin 3,
      (M i.succ.succ j.succ.succ).coeff 0 = if i = j then 1 else 0) :
    (Matrix.det M).coeff 0 = g*k := by
  calc
    (Matrix.det M).coeff 0 = Matrix.det (fun i j => (M i j).coeff 0) :=
      (Polynomial.constantCoeff : Polynomial R →+* R).map_det M
    _ = g*k := endpoint_evaluation_det _ _ _ hnormal htime hmiddle hendpoints

section Field

variable {E : Type*} [Field E]

/-- A nonzero normal coefficient and a nonzero fixed time coefficient make
the full polynomial evaluation determinant nonzero. -/
theorem polynomial_evaluation_det_ne_zero
    (M : Matrix (Fin 5) (Fin 5) (Polynomial E)) (g0 k : E)
    (hg0 : g0 ≠ 0) (hk : k ≠ 0)
    (hnormal : ∀ i : Fin 5, (M i 0).coeff 0 = if i = 0 then g0⁻¹ else 0)
    (htime : (M 1 1).coeff 0 = k)
    (hmiddle : ∀ j : Fin 3, (M 1 j.succ.succ).coeff 0 = 0)
    (hendpoints : ∀ i j : Fin 3,
      (M i.succ.succ j.succ.succ).coeff 0 = if i = j then 1 else 0) :
    Matrix.det M ≠ 0 := by
  intro hz
  have h := polynomial_evaluation_det_constant M g0⁻¹ k hnormal htime hmiddle hendpoints
  rw [hz, Polynomial.coeff_zero] at h
  exact (mul_ne_zero (inv_ne_zero hg0) hk) h.symm

end Field

end HoldoutConstruction

#print axioms HoldoutConstruction.endpoint_evaluation_det
#print axioms HoldoutConstruction.polynomial_evaluation_det_ne_zero
end
end
