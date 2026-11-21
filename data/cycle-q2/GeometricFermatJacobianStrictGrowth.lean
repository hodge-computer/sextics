import Proposal.GeometricFermatStrictGrowth
import Proposal.GeometricVariation

/-!
# Strict growth for multiplication in the Fermat Jacobian ring

The lower-coordinate reversal agrees with the complementary socle basis.
This transfers the finite matching theorem to actual multiplication from
degree six to degree twelve in the invariant sector of the Fermat ring.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
noncomputable section
namespace CycleQ2FermatJacobianStrictGrowth

open CycleQ2FermatVariationAlgebra CycleQ2FermatJacobian
open CycleQ2FermatStrictGrowth
open CycleQ2GeometricBridgeAlgebra (actualTracePairing_basis)

abbrev upperCoords : Upper ≃ₗ[ℂ] (Fin 33 → ℂ) :=
  degreeSixCharacterOneBasis.equivFun

private def reverseCoords : (Fin 33 → ℂ) ≃ₗ[ℂ] (Fin 33 → ℂ) where
  toFun x j := x j.rev
  invFun x j := x j.rev
  left_inv x := funext fun j => congrArg x (Fin.rev_rev j)
  right_inv x := funext fun j => congrArg x (Fin.rev_rev j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def lowerCoords : ActualLower ≃ₗ[ℂ] (Fin 33 → ℂ) :=
  lowerBasis.equivFun.trans reverseCoords

private theorem lower_coordinate (j : Fin 33) (z : ActualLower) :
    lowerCoords z j = lowerDualEquiv z (degreeSixCharacterOneBasis j.rev) := by
  let lhs : ActualLower →ₗ[ℂ] ℂ := (LinearMap.proj j).comp lowerCoords.toLinearMap
  let rhs : ActualLower →ₗ[ℂ] ℂ :=
    (Module.Dual.eval ℂ Upper (degreeSixCharacterOneBasis j.rev)).comp lowerDualEquiv.toLinearMap
  have he : lhs = rhs := by
    apply lowerBasis.ext
    intro i
    change lowerBasis.equivFun (lowerBasis i) j.rev =
      lowerDualEquiv (lowerBasis i) (degreeSixCharacterOneBasis j.rev)
    rw [show lowerDualEquiv (lowerBasis i) = lowerToDual (lowerBasis i) from
      DFunLike.congr_fun lowerDualEquiv_toLinearMap _, lowerToDual_basis_apply]
    simp [eq_comm]
  exact DFunLike.congr_fun he z

theorem ordered_higgs (m : Fin 35) (x : Upper) :
    (ordered ℂ m).mulVec (upperCoords x) =
      lowerCoords (actualHiggsLower (degreeSixCharacterZeroBasis m) x) := by
  let lhs := ((ordered ℂ m).mulVecLin).comp upperCoords.toLinearMap
  let rhs := lowerCoords.toLinearMap.comp (actualHiggsLower (degreeSixCharacterZeroBasis m))
  have he : lhs = rhs := by
    apply degreeSixCharacterOneBasis.ext
    intro i
    funext j
    change ((ordered ℂ m).mulVec (upperCoords (degreeSixCharacterOneBasis i))) j =
      lowerCoords (actualHiggsLower (degreeSixCharacterZeroBasis m) (degreeSixCharacterOneBasis i)) j
    rw [lower_coordinate, lowerDualEquiv_actualHiggsLower, actualTracePairing_basis]
    change (∑ k, ordered ℂ m j k * upperCoords (degreeSixCharacterOneBasis i) k) = _
    rw [Finset.sum_eq_single i]
    · simp [upperCoords, ordered]
    · intro k _ hk
      simp [upperCoords, Ne.symm hk]
    · simp
  exact DFunLike.congr_fun he x

theorem stable_pair_trivial (U : Submodule ℂ Upper) (V : Submodule ℂ ActualLower)
    (hstable : ∀ (t : Tangent) (u : Upper), u ∈ U → actualHiggsLower t u ∈ V)
    (hrank : Module.finrank ℂ V ≤ Module.finrank ℂ U) :
    (U = ⊥ ∧ V = ⊥) ∨ (U = ⊤ ∧ V = ⊤) := by
  let U' := U.map upperCoords.toLinearMap
  let V' := V.map lowerCoords.toLinearMap
  have hr : Module.finrank ℂ V' ≤ Module.finrank ℂ U' := by
    simpa only [U', V', LinearEquiv.finrank_map_eq] using hrank
  have hm (m : Fin 35) (x : Fin 33 → ℂ) (hx : x ∈ U') : (ordered ℂ m).mulVec x ∈ V' := by
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
    change (ordered ℂ m).mulVec (upperCoords u) ∈ V'
    rw [ordered_higgs]
    exact Submodule.mem_map.mpr ⟨_, hstable _ u hu, rfl⟩
  rcases CycleQ2FermatStrictGrowth.stable_pair_trivial ℂ U' V' hm hr with h | h
  · left
    exact ⟨(Submodule.map_injective_of_injective upperCoords.injective) (by simpa [U'] using h.1),
      (Submodule.map_injective_of_injective lowerCoords.injective) (by simpa [V'] using h.2)⟩
  · right
    exact ⟨(Submodule.map_injective_of_injective upperCoords.injective) (by simpa [U'] using h.1),
      (Submodule.map_injective_of_injective lowerCoords.injective) (by simpa [V'] using h.2)⟩

end CycleQ2FermatJacobianStrictGrowth

#print axioms CycleQ2FermatJacobianStrictGrowth.stable_pair_trivial
