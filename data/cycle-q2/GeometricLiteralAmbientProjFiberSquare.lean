import Proposal.GeometricLiteralAmbientProjFiberChart
import Proposal.GeometricLiteralAmbientProjFiberGluing

/-! Scalar compatibility for the affine charts of a graded projective specialization.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAmbientProjFiberSquare

open HomogeneousLocalization
open scoped TensorProduct

variable {R K A B σ τ : Type} [CommRing R] [CommRing K] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R K] [SetLike σ A] [SetLike τ B]
  [AddSubgroupClass σ A] [AddSubgroupClass τ B]
variable {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

private theorem awayMap_scalar (f : 𝒜 →+*ᵍ ℬ) (x : A) (z : 𝒜 0) :
    Away.map f x (fromZeroRingHom 𝒜 (Submonoid.powers x) z) =
      fromZeroRingHom ℬ (Submonoid.powers (f x)) (f.gradedZeroRingHom z) := by
  apply HomogeneousLocalization.val_injective
  simp [Away.map, fromZeroRingHom, HomogeneousLocalization.map_mk]

/-- Degreewise surjectivity and generators of the homogeneous kernel give
the tensor square on each standard open, with the original coefficient maps. -/
theorem tensorChart (f : 𝒜 →+*ᵍ ℬ) (cA : R →+* 𝒜 0) (cB : K →+* ℬ 0)
    (hcA : ∀ r, (cA r : A) = algebraMap R A r)
    (hc : f.gradedZeroRingHom.comp cA = cB.comp (algebraMap R K))
    (hα : Function.Surjective (algebraMap R K))
    (hsurj : ∀ n (b : B), b ∈ ℬ n → ∃ a : A, a ∈ 𝒜 n ∧ f a = b)
    (hker : CycleQ2LiteralAmbientProjFiberChart.HasHomogeneousKernelDecomposition
      (R := R) (K := K) f) {x : A} {d : ℕ} (hx : x ∈ 𝒜 d) :
    CycleQ2LiteralAmbientProjFiberGluing.TensorChart f (algebraMap R K) cA cB x := by
  let := ((fromZeroRingHom 𝒜 (Submonoid.powers x)).comp cA).toAlgebra
  let := ((fromZeroRingHom ℬ (Submonoid.powers (f x))).comp cB).toAlgebra
  let P (h : Algebra R K) : Prop :=
    letI := h
    ∃ e : K ⊗[R] Away 𝒜 x ≃ₐ[K] Away ℬ (f x), ∀ z, e (1 ⊗ₜ[R] z) = Away.map f x z
  change P (algebraMap R K).toAlgebra
  rw [toAlgebra_algebraMap]
  change ∃ e : K ⊗[R] Away 𝒜 x ≃ₐ[K] Away ℬ (f x), ∀ z, e (1 ⊗ₜ[R] z) = Away.map f x z
  have hs (r : R) : (algebraMap R (Away 𝒜 x) r).val =
      algebraMap A (Localization.Away x) (algebraMap R A r) := by
    rw [← hcA r]
    rfl
  have ht (r : R) : Away.map f x (algebraMap R (Away 𝒜 x) r) =
      algebraMap K (Away ℬ (f x)) (algebraMap R K r) := by
    change Away.map f x (fromZeroRingHom 𝒜 _ (cA r)) = fromZeroRingHom ℬ _ _
    rw [awayMap_scalar]
    exact congrArg (fromZeroRingHom ℬ _) (DFunLike.congr_fun hc r)
  obtain ⟨e, he⟩ := CycleQ2LiteralAmbientProjFiberChart.exists_awayTensorEquiv
    f hα hsurj hker hx hs ht
  exact ⟨e, fun z => by simpa using he 1 z⟩

end CycleQ2LiteralAmbientProjFiberSquare
end
