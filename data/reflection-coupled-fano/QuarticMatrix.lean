import Proposal.QuarticSeed

noncomputable section
namespace CoupledFanoQuarticSeed
open Matrix
variable {K : Type*} [Field K] [CharP K 5]

lemma two_sub_j_ne_zero {j : K} (hj : j^2=2) : 2-j ≠ 0 := by
  intro h
  have h2 : (2 : K) = 0 := by linear_combination (2+j)*h + hj
  exact two_ne_zero h2

lemma three_ne_zero : (3 : K) ≠ 0 :=
  (CharP.cast_eq_zero_iff K 5 3).not.mpr (by decide)

lemma four_ne_zero : (4 : K) ≠ 0 :=
  (CharP.cast_eq_zero_iff K 5 4).not.mpr (by decide)

/-- The 24 by 24 endpoint-fixed coefficient Jacobian at the quartic seed.
Rows are coefficients t^1 through t^24. Columns are the four positive
coefficients of each of the five weight-one coordinates, then those of u. -/
def seedMatrix (j : K) : Matrix (Fin 24) (Fin 24) K :=
  ![![-j, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0],
    ![0, -j, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0],
    ![0, 0, -j, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0],
    ![0, 0, 0, -j, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 2 - j, 0, 0, 0, 0, 0, 0, 0, -j, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 2 - j, 0, 0, 0, 0, 0, 0, 0, -j, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 2 - j, 0, 0, 0, 0, 0, 0, 0, -j, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 2 - j, 0, 0, 0, 0, 0, 0, 0, -j, 0, 0, 0, 0, 4, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, -j, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -j, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -j, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -j, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 2 - j, 0, 0, 0, 0, 0, 0, 0, j, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 2 - j, 0, 0, 0, 0, 0, 0, 0, j, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 2 - j, 0, 0, 0, 0, 0, 0, 0, j, 0, 0, 0, 0, 0, 0, 3, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 2 - j, 0, 0, 0, 0, 0, 0, 0, j, 0, 0, 0, 0, 0, 0, 3, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3],
    ![-j, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0],
    ![0, -j, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0],
    ![0, 0, -j, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
    ![0, 0, 0, -j, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0]]

lemma seedMatrix_ker {j : K} (hj : j^2=2) (v : Fin 24 → K)
    (h : (seedMatrix j).mulVec v = 0) : v = 0 := by
  have hn := j_ne_zero hj
  have hc := two_sub_j_ne_zero hj
  have h2j : (2:K)*j ≠ 0 := mul_ne_zero two_ne_zero hn
  have h2c : (2:K)*(2-j) ≠ 0 := mul_ne_zero two_ne_zero hc
  have h0 : (-j) * v 0 + v 16 + (3) * v 20 = 0 := by
    simpa only [seedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.sum_univ_zero,
      mul_zero, zero_mul, add_zero, zero_add, one_mul, Pi.zero_apply, add_assoc, Fin.reduceSucc]
      using congrFun h (0 : Fin 24)
  have h1 : (-j) * v 1 + v 17 + (3) * v 21 = 0 := by
    simpa only [seedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.sum_univ_zero,
      mul_zero, zero_mul, add_zero, zero_add, one_mul, Pi.zero_apply, add_assoc, Fin.reduceSucc]
      using congrFun h (1 : Fin 24)
  have h2 : (-j) * v 2 + v 18 + (3) * v 22 = 0 := by
    simpa only [seedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.sum_univ_zero,
      mul_zero, zero_mul, add_zero, zero_add, one_mul, Pi.zero_apply, add_assoc, Fin.reduceSucc]
      using congrFun h (2 : Fin 24)
  have h3 : (-j) * v 3 + v 19 + (3) * v 23 = 0 := by
    simpa only [seedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.sum_univ_zero,
      mul_zero, zero_mul, add_zero, zero_add, one_mul, Pi.zero_apply, add_assoc, Fin.reduceSucc]
      using congrFun h (3 : Fin 24)
  have h4 : v 20 = 0 := by
    simpa only [seedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.sum_univ_zero,
      mul_zero, zero_mul, add_zero, zero_add, one_mul, Pi.zero_apply, add_assoc, Fin.reduceSucc]
      using congrFun h (4 : Fin 24)
  have h5 : (2 - j) * v 4 + (-j) * v 12 + v 21 = 0 := by
    simpa only [seedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.sum_univ_zero,
      mul_zero, zero_mul, add_zero, zero_add, one_mul, Pi.zero_apply, add_assoc, Fin.reduceSucc]
      using congrFun h (5 : Fin 24)
  have h6 : (2 - j) * v 5 + (-j) * v 13 + v 22 = 0 := by
    simpa only [seedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.sum_univ_zero,
      mul_zero, zero_mul, add_zero, zero_add, one_mul, Pi.zero_apply, add_assoc, Fin.reduceSucc]
      using congrFun h (6 : Fin 24)
  have h7 : (2 - j) * v 6 + (-j) * v 14 + v 23 = 0 := by
    simpa only [seedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.sum_univ_zero,
      mul_zero, zero_mul, add_zero, zero_add, one_mul, Pi.zero_apply, add_assoc, Fin.reduceSucc]
      using congrFun h (7 : Fin 24)
  have h8 : (2 - j) * v 7 + (-j) * v 15 + (4) * v 20 = 0 := by
    simpa only [seedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.sum_univ_zero,
      mul_zero, zero_mul, add_zero, zero_add, one_mul, Pi.zero_apply, add_assoc, Fin.reduceSucc]
      using congrFun h (8 : Fin 24)
  have h9 : (4) * v 21 = 0 := by
    simpa only [seedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.sum_univ_zero,
      mul_zero, zero_mul, add_zero, zero_add, one_mul, Pi.zero_apply, add_assoc, Fin.reduceSucc]
      using congrFun h (9 : Fin 24)
  have h10 : (-j) * v 8 + (4) * v 22 = 0 := by
    simpa only [seedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.sum_univ_zero,
      mul_zero, zero_mul, add_zero, zero_add, one_mul, Pi.zero_apply, add_assoc, Fin.reduceSucc]
      using congrFun h (10 : Fin 24)
  have h11 : (-j) * v 9 + (4) * v 23 = 0 := by
    simpa only [seedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.sum_univ_zero,
      mul_zero, zero_mul, add_zero, zero_add, one_mul, Pi.zero_apply, add_assoc, Fin.reduceSucc]
      using congrFun h (11 : Fin 24)
  have h12 : (-j) * v 10 + v 20 = 0 := by
    simpa only [seedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.sum_univ_zero,
      mul_zero, zero_mul, add_zero, zero_add, one_mul, Pi.zero_apply, add_assoc, Fin.reduceSucc]
      using congrFun h (12 : Fin 24)
  have h13 : (-j) * v 11 + v 21 = 0 := by
    simpa only [seedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.sum_univ_zero,
      mul_zero, zero_mul, add_zero, zero_add, one_mul, Pi.zero_apply, add_assoc, Fin.reduceSucc]
      using congrFun h (13 : Fin 24)
  have h14 : v 22 = 0 := by
    simpa only [seedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.sum_univ_zero,
      mul_zero, zero_mul, add_zero, zero_add, one_mul, Pi.zero_apply, add_assoc, Fin.reduceSucc]
      using congrFun h (14 : Fin 24)
  have h15 : (2 - j) * v 4 + (j) * v 12 + v 23 = 0 := by
    simpa only [seedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.sum_univ_zero,
      mul_zero, zero_mul, add_zero, zero_add, one_mul, Pi.zero_apply, add_assoc, Fin.reduceSucc]
      using congrFun h (15 : Fin 24)
  have h16 : (2 - j) * v 5 + (j) * v 13 + (3) * v 20 = 0 := by
    simpa only [seedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.sum_univ_zero,
      mul_zero, zero_mul, add_zero, zero_add, one_mul, Pi.zero_apply, add_assoc, Fin.reduceSucc]
      using congrFun h (16 : Fin 24)
  have h17 : (2 - j) * v 6 + (j) * v 14 + (3) * v 21 = 0 := by
    simpa only [seedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.sum_univ_zero,
      mul_zero, zero_mul, add_zero, zero_add, one_mul, Pi.zero_apply, add_assoc, Fin.reduceSucc]
      using congrFun h (17 : Fin 24)
  have h18 : (2 - j) * v 7 + (j) * v 15 + (3) * v 22 = 0 := by
    simpa only [seedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.sum_univ_zero,
      mul_zero, zero_mul, add_zero, zero_add, one_mul, Pi.zero_apply, add_assoc, Fin.reduceSucc]
      using congrFun h (18 : Fin 24)
  have h19 : (3) * v 23 = 0 := by
    simpa only [seedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.sum_univ_zero,
      mul_zero, zero_mul, add_zero, zero_add, one_mul, Pi.zero_apply, add_assoc, Fin.reduceSucc]
      using congrFun h (19 : Fin 24)
  have h20 : (-j) * v 0 + (-1) * v 16 = 0 := by
    simpa only [seedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.sum_univ_zero,
      mul_zero, zero_mul, add_zero, zero_add, one_mul, Pi.zero_apply, add_assoc, Fin.reduceSucc]
      using congrFun h (20 : Fin 24)
  have h21 : (-j) * v 1 + (-1) * v 17 = 0 := by
    simpa only [seedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.sum_univ_zero,
      mul_zero, zero_mul, add_zero, zero_add, one_mul, Pi.zero_apply, add_assoc, Fin.reduceSucc]
      using congrFun h (21 : Fin 24)
  have h22 : (-j) * v 2 + (-1) * v 18 = 0 := by
    simpa only [seedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.sum_univ_zero,
      mul_zero, zero_mul, add_zero, zero_add, one_mul, Pi.zero_apply, add_assoc, Fin.reduceSucc]
      using congrFun h (22 : Fin 24)
  have h23 : (-j) * v 3 + (-1) * v 19 = 0 := by
    simpa only [seedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.sum_univ_zero,
      mul_zero, zero_mul, add_zero, zero_add, one_mul, Pi.zero_apply, add_assoc, Fin.reduceSucc]
      using congrFun h (23 : Fin 24)
  have v20 : v 20 = 0 := h4
  have v21 : v 21 = 0 := (mul_eq_zero.mp h9).resolve_left four_ne_zero
  have v22 : v 22 = 0 := h14
  have v23 : v 23 = 0 := (mul_eq_zero.mp h19).resolve_left three_ne_zero
  simp only [v20, v21, v22, v23, mul_zero, add_zero, zero_add] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23
  have a0 : (2*j)*v 0 = 0 := by linear_combination -h0-h20
  have v0 : v 0 = 0 := (mul_eq_zero.mp a0).resolve_left h2j
  have v16 : v 16 = 0 := by simpa only [v0, mul_zero, zero_add] using h0
  have b0 : (2*(2-j))*v 4 = 0 := by linear_combination h5+h15
  have v4 : v 4 = 0 := (mul_eq_zero.mp b0).resolve_left h2c
  have d0 : (2*j)*v 12 = 0 := by linear_combination h15-h5
  have v12 : v 12 = 0 := (mul_eq_zero.mp d0).resolve_left h2j
  have v8 : v 8 = 0 := (mul_eq_zero.mp h10).resolve_left (neg_ne_zero.mpr hn)
  have a1 : (2*j)*v 1 = 0 := by linear_combination -h1-h21
  have v1 : v 1 = 0 := (mul_eq_zero.mp a1).resolve_left h2j
  have v17 : v 17 = 0 := by simpa only [v1, mul_zero, zero_add] using h1
  have b1 : (2*(2-j))*v 5 = 0 := by linear_combination h6+h16
  have v5 : v 5 = 0 := (mul_eq_zero.mp b1).resolve_left h2c
  have d1 : (2*j)*v 13 = 0 := by linear_combination h16-h6
  have v13 : v 13 = 0 := (mul_eq_zero.mp d1).resolve_left h2j
  have v9 : v 9 = 0 := (mul_eq_zero.mp h11).resolve_left (neg_ne_zero.mpr hn)
  have a2 : (2*j)*v 2 = 0 := by linear_combination -h2-h22
  have v2 : v 2 = 0 := (mul_eq_zero.mp a2).resolve_left h2j
  have v18 : v 18 = 0 := by simpa only [v2, mul_zero, zero_add] using h2
  have b2 : (2*(2-j))*v 6 = 0 := by linear_combination h7+h17
  have v6 : v 6 = 0 := (mul_eq_zero.mp b2).resolve_left h2c
  have d2 : (2*j)*v 14 = 0 := by linear_combination h17-h7
  have v14 : v 14 = 0 := (mul_eq_zero.mp d2).resolve_left h2j
  have v10 : v 10 = 0 := (mul_eq_zero.mp h12).resolve_left (neg_ne_zero.mpr hn)
  have a3 : (2*j)*v 3 = 0 := by linear_combination -h3-h23
  have v3 : v 3 = 0 := (mul_eq_zero.mp a3).resolve_left h2j
  have v19 : v 19 = 0 := by simpa only [v3, mul_zero, zero_add] using h3
  have b3 : (2*(2-j))*v 7 = 0 := by linear_combination h8+h18
  have v7 : v 7 = 0 := (mul_eq_zero.mp b3).resolve_left h2c
  have d3 : (2*j)*v 15 = 0 := by linear_combination h18-h8
  have v15 : v 15 = 0 := (mul_eq_zero.mp d3).resolve_left h2j
  have v11 : v 11 = 0 := (mul_eq_zero.mp h13).resolve_left (neg_ne_zero.mpr hn)
  funext i
  fin_cases i <;> assumption

theorem seedMatrix_det_ne_zero {j : K} (hj : j^2=2) : (seedMatrix j).det ≠ 0 := by
  have hi : Function.Injective (seedMatrix j).mulVec := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply seedMatrix_ker hj
    rw [Matrix.mulVec_sub, hxy, sub_self]
  exact ((seedMatrix j).isUnit_iff_isUnit_det.mp
    (Matrix.mulVec_injective_iff_isUnit.mp hi)).ne_zero

end CoupledFanoQuarticSeed
