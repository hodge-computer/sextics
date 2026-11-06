import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ext

/-! Reusable finite-algebra and contact calculus extracted from `HeadOfNaps`’
accepted quadric-contact-broken (#122) and holdout-q2 (#124) proofs.
See this directory’s README for hypotheses, entry points, and attribution. -/

noncomputable section
namespace QuadricContactMatrixBezout

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- A matrix Bezout identity is enough for scalar relative primality, without
expanding a determinant or assuming the coefficient ring is a field. -/
theorem relPrime_det_of_matrix_bezout (f : R) (A B C : Matrix n n R)
    (h : A * B + f • C = 1) : IsRelPrime f A.det := by
  intro p hpf hpdet
  let I : Ideal R := Ideal.span ({p} : Set R)
  let φ : R →+* R ⧸ I := Ideal.Quotient.mk I
  have hf : φ f = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_span_singleton.mpr hpf
  have hd : φ A.det = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_span_singleton.mpr hpdet
  have hzero : φ.mapMatrix (f • C) = 0 := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply,
      smul_eq_mul, map_mul, hf, zero_mul, Matrix.zero_apply]
  have hm : φ.mapMatrix A * φ.mapMatrix B = 1 := by
    have hh := congrArg φ.mapMatrix h
    simpa only [map_add, map_mul, map_one, hzero, add_zero] using hh
  have hz : (0 : R ⧸ I) = 1 := by
    have hh := congrArg Matrix.det hm
    rw [Matrix.det_mul, ← φ.map_det A, hd, zero_mul, Matrix.det_one] at hh
    exact hh
  apply isUnit_of_dvd_one
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  exact (map_one φ).trans hz.symm

/-- A cubic evaluated at a matrix has an explicit polynomial Bezout relation
with zI-M whenever that matrix value has a right inverse. -/
theorem cubic_matrix_bezout (z a b : R) (M K : Matrix n n R)
    (hK : (M ^ 3 + a • M + b • (1 : Matrix n n R)) * K = 1) :
    (z • (1 : Matrix n n R) - M) *
      (-(z ^ 2 • (1 : Matrix n n R) + z • M + M ^ 2 + a • (1 : Matrix n n R)) * K) +
      (z ^ 3 + a * z + b) • K = 1 := by
  have hf :
      (z • (1 : Matrix n n R) - M) *
        (z ^ 2 • (1 : Matrix n n R) + z • M + M ^ 2 + a • (1 : Matrix n n R)) =
      (z ^ 3 + a * z + b) • (1 : Matrix n n R) - (M ^ 3 + a • M + b • (1 : Matrix n n R)) := by
    simp only [sub_mul, mul_add, add_mul, smul_mul_assoc, mul_smul_comm,
      smul_smul, pow_succ, pow_zero, one_mul, mul_one, mul_assoc]
    module
  rw [← mul_assoc, mul_neg, hf, neg_sub, sub_mul,
    smul_mul_assoc, one_mul, hK]
  abel

/-- Scalar determinant coprimality without expanding the characteristic polynomial. -/
theorem relPrime_cubic_det (z a b : R) (M K : Matrix n n R)
    (hK : (M ^ 3 + a • M + b • (1 : Matrix n n R)) * K = 1) :
    IsRelPrime (z ^ 3 + a * z + b) (z • (1 : Matrix n n R) - M).det := by
  apply relPrime_det_of_matrix_bezout (z ^ 3 + a * z + b)
    (z • (1 : Matrix n n R) - M)
    (-(z ^ 2 • (1 : Matrix n n R) + z • M + M ^ 2 + a • (1 : Matrix n n R)) * K) K
  exact cubic_matrix_bezout z a b M K hK

end QuadricContactMatrixBezout

#print axioms QuadricContactMatrixBezout.relPrime_cubic_det

