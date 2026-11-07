import SymmetricReflections
import SymmetricSmoothness
import TwoReflectionSectors

/-!
The exact protected equation and its determinant-twisted polynomial source
characters. A coordinate transposition and the three-coordinate Y sign change
each have determinant -1, so their numerator actions include that sign.

These are polynomial and linear-map statements. Identifying the signed action
with pullback on Griffiths residues is a separate geometric theorem.
-/

noncomputable section
namespace SignedSourceCharacters

open MvPolynomial SymmetricReflections

abbrev Poly := MvPolynomial (Fin 6) ℂ

def swapX : Poly →ₐ[ℂ] Poly := rename (Equiv.swap (0 : Fin 6) 1)
def swapY : Poly →ₐ[ℂ] Poly := rename (Equiv.swap (3 : Fin 6) 4)
def blockSign (i : Fin 6) : ℂ := if i.val < 3 then 1 else -1
def blockY : Poly →ₐ[ℂ] Poly := aeval (fun i => C (blockSign i) * X i)

def τ : Poly →ₗ[ℂ] Poly := -blockY.toLinearMap
def r : Poly →ₗ[ℂ] Poly := -swapX.toLinearMap
def s : Poly →ₗ[ℂ] Poly := -swapY.toLinearMap

theorem swapX_involutive : Function.Involutive swapX := by
  have h : swapX.comp swapX = AlgHom.id ℂ Poly := by
    ext i
    fin_cases i <;> simp [swapX, Equiv.swap_apply_def]
  intro p
  exact DFunLike.congr_fun h p

theorem swapY_involutive : Function.Involutive swapY := by
  have h : swapY.comp swapY = AlgHom.id ℂ Poly := by
    ext i
    fin_cases i <;> simp [swapY, Equiv.swap_apply_def]
  intro p
  exact DFunLike.congr_fun h p

theorem blockY_involutive : Function.Involutive blockY := by
  have h : blockY.comp blockY = AlgHom.id ℂ Poly := by
    ext i
    fin_cases i <;> simp [blockY, blockSign]
  intro p
  exact DFunLike.congr_fun h p

theorem blockY_swapX : Function.Commute blockY swapX := by
  have h : blockY.comp swapX = swapX.comp blockY := by
    ext i
    fin_cases i <;> simp [blockY, blockSign, swapX, Equiv.swap_apply_def]
  intro p
  exact DFunLike.congr_fun h p

theorem blockY_swapY : Function.Commute blockY swapY := by
  have h : blockY.comp swapY = swapY.comp blockY := by
    ext i
    fin_cases i <;> simp [blockY, blockSign, swapY, Equiv.swap_apply_def]
  intro p
  exact DFunLike.congr_fun h p

theorem swapX_swapY : Function.Commute swapX swapY := by
  have h : swapX.comp swapY = swapY.comp swapX := by
    ext i
    fin_cases i <;> simp [swapX, swapY, Equiv.swap_apply_def]
  intro p
  exact DFunLike.congr_fun h p

theorem τ_involutive : Function.Involutive τ := by
  intro p
  simpa [τ] using blockY_involutive p

theorem r_involutive : Function.Involutive r := by
  intro p
  simpa [r] using swapX_involutive p

theorem s_involutive : Function.Involutive s := by
  intro p
  simpa [s] using swapY_involutive p

theorem τ_r_commute : Function.Commute τ r := by
  intro p
  simpa [τ, r] using blockY_swapX p

theorem τ_s_commute : Function.Commute τ s := by
  intro p
  simpa [τ, s] using blockY_swapY p

theorem r_s_commute : Function.Commute r s := by
  intro p
  simpa [r, s] using swapX_swapY p

theorem equation_swapX : swapX HodgeSubmission.F = HodgeSubmission.F := by
  rw [exactF_compact]
  simp [swapX, compactF, QX, QY, Equiv.swap_apply_def, map_ofNat]
  ring

theorem equation_swapY : swapY HodgeSubmission.F = HodgeSubmission.F := by
  rw [exactF_compact]
  simp [swapY, compactF, QX, QY, Equiv.swap_apply_def, map_ofNat]
  ring

theorem equation_blockY : blockY HodgeSubmission.F = HodgeSubmission.F := by
  rw [exactF_compact]
  simp [blockY, blockSign, compactF, QX, QY, map_ofNat]
  ring

theorem source_swapX : swapX HodgeSubmission.A = HodgeSubmission.A := by
  rw [exactA_compact]
  simp [swapX, compactA, Equiv.swap_apply_def]
  ring

theorem source_swapY : swapY HodgeSubmission.A = HodgeSubmission.A := by
  rw [exactA_compact]
  simp [swapY, compactA, Equiv.swap_apply_def]
  ring

theorem source_blockY : blockY HodgeSubmission.A = -HodgeSubmission.A := by
  rw [exactA_compact]
  simp [blockY, blockSign, compactA]

theorem source_τ : τ HodgeSubmission.A = HodgeSubmission.A := by
  simp only [τ, LinearMap.neg_apply, AlgHom.toLinearMap_apply,
    source_blockY, neg_neg]

theorem source_r : r HodgeSubmission.A = -HodgeSubmission.A := by
  simp only [r, LinearMap.neg_apply, AlgHom.toLinearMap_apply, source_swapX]

theorem source_s : s HodgeSubmission.A = -HodgeSubmission.A := by
  simp only [s, LinearMap.neg_apply, AlgHom.toLinearMap_apply, source_swapY]

theorem exact_source_residual_characters :
    τ HodgeSubmission.A = HodgeSubmission.A ∧
    r HodgeSubmission.A = -HodgeSubmission.A ∧
    s HodgeSubmission.A = -HodgeSubmission.A ∧
    r (s HodgeSubmission.A) = HodgeSubmission.A ∧
    τ (s HodgeSubmission.A) = -HodgeSubmission.A := by
  refine ⟨source_τ, source_r, source_s, ?_, ?_⟩
  · rw [source_s, map_neg, source_r, neg_neg]
  · rw [source_s, map_neg, source_τ]

theorem source_first_positive_zero :
    TwoReflectionSectors.positive r HodgeSubmission.A = 0 := by
  rw [TwoReflectionSectors.positive_apply, source_r, add_neg_cancel, smul_zero]

theorem source_second_positive_zero :
    TwoReflectionSectors.positive s
      (TwoReflectionSectors.negative r HodgeSubmission.A) = 0 := by
  have h : TwoReflectionSectors.negative r HodgeSubmission.A = HodgeSubmission.A := by
    rw [TwoReflectionSectors.negative_apply, source_r]
    module
  rw [h, TwoReflectionSectors.positive_apply, source_s, add_neg_cancel, smul_zero]

theorem source_residual_eq_source :
    TwoReflectionSectors.negative s
      (TwoReflectionSectors.negative r HodgeSubmission.A) = HodgeSubmission.A := by
  rw [TwoReflectionSectors.negative_apply, TwoReflectionSectors.negative_apply,
    source_r, map_smul, map_sub, map_neg, source_s]
  module

#print axioms equation_swapX
#print axioms equation_swapY
#print axioms equation_blockY
#print axioms exact_source_residual_characters
#print axioms source_residual_eq_source

end SignedSourceCharacters
