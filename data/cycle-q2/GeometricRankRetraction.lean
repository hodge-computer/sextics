import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# A square retraction of a rectangular matrix

This is the generic rank retraction previously proved in
`SolutionSupport01Part01.lean`.  It is separated here so both the original
faithful-specialization argument and the cube-root specialization argument
can use the same theorem without importing their unrelated dependencies.
-/

noncomputable section

namespace CycleQ2ArithmeticRankTransfer

open Matrix

variable {K : Type*} [Field K] {m n : Type*} [Fintype m] [Fintype n]

/-- A matrix of rank `r` admits a square compression `C * A * B = 1` of size `r`. -/
theorem exists_rank_retraction (A : Matrix m n K) :
    ∃ (C : Matrix (Fin A.rank) m K) (B : Matrix n (Fin A.rank) K), C * A * B = 1 := by
  classical
  let V := LinearMap.range (Matrix.mulVecLin A)
  let b := Module.finBasis K V
  obtain ⟨s, hs⟩ := (Matrix.mulVecLin A).rangeRestrict.exists_rightInverse_of_surjective
    (Matrix.mulVecLin A).range_rangeRestrict
  obtain ⟨t, ht⟩ := V.subtype.exists_leftInverse_of_injective V.ker_subtype
  let C : (m → K) →ₗ[K] (Fin A.rank → K) := b.equivFun.toLinearMap.comp t
  let B : (Fin A.rank → K) →ₗ[K] (n → K) := s.comp b.equivFun.symm.toLinearMap
  refine ⟨LinearMap.toMatrix' C, LinearMap.toMatrix' B, ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix',
    Matrix.toLin'_toMatrix', Matrix.toLin'_one]
  apply LinearMap.ext
  intro x
  change b.equivFun (t (Matrix.mulVecLin A (s (b.equivFun.symm x)))) = x
  have hpre := congrArg Subtype.val (LinearMap.congr_fun hs (b.equivFun.symm x))
  change Matrix.mulVecLin A (s (b.equivFun.symm x)) = (b.equivFun.symm x).val at hpre
  rw [hpre]
  have hpost := LinearMap.congr_fun ht (b.equivFun.symm x)
  change t (b.equivFun.symm x).val = b.equivFun.symm x at hpost
  rw [hpost]
  exact b.equivFun.apply_symm_apply x

end CycleQ2ArithmeticRankTransfer
