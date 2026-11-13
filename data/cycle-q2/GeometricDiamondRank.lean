import Proposal.GeometricDiamondSeed
import Proposal.GeometricRankRetraction

/-!
# Simultaneous rectangular rank bounds at a complex cube root of two

The modular rank of a rectangular Gaussian-polynomial matrix is witnessed by
a square compression `C * A * B = 1` over `ZMod 109`.  Lifting the entries of
`C` and `B` to constant Gaussian polynomials gives a square polynomial matrix
whose determinant is nonzero at the modular seed.  The simultaneous lifting
theorem from `GeometricDiamondSeed` preserves these determinants, and any
additional denominator factor, at one complex parameter satisfying `r ^ 3 = 2`.
The rank inequalities for matrix products then recover the rectangular ranks.

The rank retraction is the same generic theorem used by the existing faithful
Gaussian specialization argument; it is imported from its small shared module.
This file proves a transfer of modular lower bounds.  It supplies no rank upper
bound and does not transfer a lower bound known only at literal complex `57`.
-/

noncomputable section

namespace CycleQ2DiamondRank

open Matrix CycleQ2DiamondSeed

abbrev Poly := Polynomial GaussianInt

/-- Evaluation at the modular seed, including `i ↦ 33`. -/
def modularEvaluation : Poly →+* F109 :=
  Polynomial.eval₂RingHom reduction (57 : F109)

/-- Evaluation at a complex parameter, using the faithful Gaussian embedding. -/
def complexEvaluation (r : ℂ) : Poly →+* ℂ :=
  Polynomial.eval₂RingHom GaussianInt.toComplex r

private def modularLift (x : F109) : Poly :=
  Polynomial.C (x.val : GaussianInt)

private theorem modularEvaluation_modularLift (x : F109) :
    modularEvaluation (modularLift x) = x := by
  change (Polynomial.C (x.val : GaussianInt)).eval₂ reduction (57 : F109) = x
  rw [Polynomial.eval₂_C, map_natCast]
  exact ZMod.natCast_zmod_val x

/-- A modular rank is witnessed by a square polynomial compression whose
modular specialization is the identity.  The lifting matrices are constant. -/
theorem exists_polynomial_rank_compression {m n : Type*}
    [Fintype m] [Fintype n] (A : Matrix m n Poly) :
    ∃ (C : Matrix (Fin (A.map modularEvaluation).rank) m Poly)
      (B : Matrix n (Fin (A.map modularEvaluation).rank) Poly),
      (C * A * B).map modularEvaluation = 1 := by
  classical
  obtain ⟨C, B, hCB⟩ :=
    CycleQ2ArithmeticRankTransfer.exists_rank_retraction (A.map modularEvaluation)
  have hC : (C.map modularLift).map modularEvaluation = C := by
    ext i j
    exact modularEvaluation_modularLift (C i j)
  have hB : (B.map modularLift).map modularEvaluation = B := by
    ext i j
    exact modularEvaluation_modularLift (B i j)
  refine ⟨C.map modularLift, B.map modularLift, ?_⟩
  simp only [Matrix.map_mul]
  rw [hC, hB, hCB]

/-- All modular ranks of a finite family of rectangular polynomial matrices
are lower bounds at one common complex root of two.  The additional factor
`d` can retain all denominators used to clear rational matrix entries. -/
theorem exists_cube_root_two_rank_family {ι : Type*} [Fintype ι]
    {m n : ι → Type*} [∀ j, Fintype (m j)] [∀ j, Fintype (n j)]
    (A : ∀ j, Matrix (m j) (n j) Poly)
    (d : Poly) (hd : modularEvaluation d ≠ 0) :
    ∃ r : ℂ, r ^ 3 = 2 ∧ complexEvaluation r d ≠ 0 ∧
      ∀ j, ((A j).map modularEvaluation).rank ≤
        ((A j).map (complexEvaluation r)).rank := by
  classical
  let C (j : ι) := Classical.choose (exists_polynomial_rank_compression (A j))
  let B (j : ι) := Classical.choose
    (Classical.choose_spec (exists_polynomial_rank_compression (A j)))
  have hCB (j : ι) : (C j * A j * B j).map modularEvaluation = 1 :=
    Classical.choose_spec
      (Classical.choose_spec (exists_polynomial_rank_compression (A j)))
  let T (j : ι) :
      Matrix (Fin ((A j).map modularEvaluation).rank)
        (Fin ((A j).map modularEvaluation).rank) Poly := C j * A j * B j
  have hdet (j : ι) : ((T j).map modularEvaluation).det ≠ 0 := by
    change ((C j * A j * B j).map modularEvaluation).det ≠ 0
    rw [hCB j, Matrix.det_one]
    exact one_ne_zero
  obtain ⟨r, hr, hdC, hTC⟩ :=
    CycleQ2DiamondSeed.exists_cube_root_two_matrix_family T d hd hdet
  refine ⟨r, hr, hdC, fun j => ?_⟩
  have hTrank : ((T j).map (complexEvaluation r)).rank =
      ((A j).map modularEvaluation).rank := by
    have hdetC : ((T j).map (complexEvaluation r)).det ≠ 0 := hTC j
    rw [Matrix.rank_of_det_ne_zero hdetC, Fintype.card_fin]
  have hTmap : (T j).map (complexEvaluation r) =
      (C j).map (complexEvaluation r) * (A j).map (complexEvaluation r) *
        (B j).map (complexEvaluation r) := by
    simp only [T, Matrix.map_mul]
  rw [← hTrank, hTmap]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

/-- A version accepting explicit modular lower bounds, for direct use with
rank certificates such as the fixed-sextic and augmented incidence bounds. -/
theorem exists_cube_root_two_rank_lower_bounds {ι : Type*} [Fintype ι]
    {m n : ι → Type*} [∀ j, Fintype (m j)] [∀ j, Fintype (n j)]
    (A : ∀ j, Matrix (m j) (n j) Poly) (k : ι → ℕ)
    (d : Poly) (hd : modularEvaluation d ≠ 0)
    (hmod : ∀ j, k j ≤ ((A j).map modularEvaluation).rank) :
    ∃ r : ℂ, r ^ 3 = 2 ∧ complexEvaluation r d ≠ 0 ∧
      ∀ j, k j ≤ ((A j).map (complexEvaluation r)).rank := by
  obtain ⟨r, hr, hdC, hRank⟩ := exists_cube_root_two_rank_family A d hd
  exact ⟨r, hr, hdC, fun j => (hmod j).trans (hRank j)⟩

end CycleQ2DiamondRank
