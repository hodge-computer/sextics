import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.ZMod.Basic

/-!
Exact modular rank certificates for the finite-dimensional stage of PR #218.
This file contains no Hodge-theoretic assumptions and proves no certificate
existence statement. A verified inverse modulo a prime proves a rational minor
is nonsingular; a nonsingular minor proves the full rectangular matrix rank.
-/

namespace WeightedSupport

open Matrix

theorem rational_det_ne_zero_of_modular_inverse
    {n p : ℕ} [Fact p.Prime]
    (A : Matrix (Fin n) (Fin n) ℤ)
    (B : Matrix (Fin n) (Fin n) (ZMod p))
    (h : A.map (Int.castRingHom (ZMod p)) * B = 1) :
    (A.map (Int.castRingHom ℚ)).det ≠ 0 := by
  have hmod : (A.map (Int.castRingHom (ZMod p))).det ≠ 0 :=
    Matrix.det_ne_zero_of_right_inverse h
  intro hzero
  have hmapQ : (A.map (Int.castRingHom ℚ)).det = (A.det : ℚ) :=
    ((Int.castRingHom ℚ).map_det A).symm
  have hz : A.det = 0 := by
    apply Int.cast_injective (α := ℚ)
    simpa only [Int.cast_zero, hmapQ] using hzero
  apply hmod
  have hmapP : (A.map (Int.castRingHom (ZMod p))).det = (A.det : ZMod p) :=
    ((Int.castRingHom (ZMod p)).map_det A).symm
  rw [hmapP, hz, Int.cast_zero]

theorem full_column_rank_of_nonsingular_minor
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (rows : Fin n → Fin m)
    (h : (A.submatrix rows id).det ≠ 0) : A.rank = n := by
  have hminor := Matrix.rank_of_det_ne_zero h
  have hle := Matrix.rank_submatrix_le A rows id
  have hub := Matrix.rank_le_card_width A
  simp only [Fintype.card_fin] at hminor hub
  omega

theorem full_row_rank_of_nonsingular_minor
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (cols : Fin m → Fin n)
    (h : (A.submatrix id cols).det ≠ 0) : A.rank = m := by
  have hminor := Matrix.rank_of_det_ne_zero h
  have hle := Matrix.rank_submatrix_le A id cols
  have hub := Matrix.rank_le_card_height A
  simp only [Fintype.card_fin] at hminor hub
  omega

end WeightedSupport

#print axioms WeightedSupport.rational_det_ne_zero_of_modular_inverse
#print axioms WeightedSupport.full_column_rank_of_nonsingular_minor
#print axioms WeightedSupport.full_row_rank_of_nonsingular_minor
