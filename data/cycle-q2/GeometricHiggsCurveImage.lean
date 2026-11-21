import Proposal.GeometricHiggsFamilyStrictGrowth
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Spanning from the weight-one dimension inequality

The image of a split weight-one source is the sum of the image of
its upper piece and its conjugate. Thus its lower rank is at most its
upper rank. After identifying the two graded spaces and supplying the
Higgs stability condition, the checked family strict-growth theorem
forces the correspondence image to be zero or all of the target.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false

noncomputable section

namespace CycleQ2HiggsCurveImage

open Module
open CycleQ2GenericSexticGradient (CoeffRing seedEvaluation)
open CycleQ2HiggsFamilyGrading (Upper Lower Tangent higgs)

section LinearAlgebra

variable {K H V : Type} [Field K] [AddCommGroup H] [Module K H]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (σ : K →+* K) {τ : K →+* K} [RingHomInvPair σ τ] [RingHomInvPair τ σ]
  (cH : H ≃ₛₗ[σ] H) (cV : V ≃ₛₗ[σ] V)
  (Θ : H →ₗ[K] V) (F₁ : Submodule K H) (F₂ : Submodule K V)

omit [FiniteDimensional K V] in
private theorem conj_finrank (A : Submodule K V) :
    finrank K (A.map cV.toLinearMap) = finrank K A := by
  let j := cV.submoduleMap A
  let σe := RingHomInvPair.toRingEquiv σ τ
  exact congrArg Cardinal.toNat
    (rank_eq_of_equiv_equiv σe j.toAddEquiv σe.bijective (fun c x => j.map_smulₛₗ c x)).symm

omit [FiniteDimensional K V] in
private theorem map_conj (ε : Kˣ) (hε : ∀ x, Θ (cH x) = (ε : K) • cV (Θ x)) :
    (F₁.map cH.toLinearMap).map Θ = (F₁.map Θ).map cV.toLinearMap := by
  apply le_antisymm
  · intro v hv
    obtain ⟨y, ⟨x, hx, rfl⟩, rfl⟩ := Submodule.mem_map.mp hv
    change Θ (cH x) ∈ (F₁.map Θ).map cV.toLinearMap
    rw [hε]
    exact Submodule.smul_mem _ _ (Submodule.mem_map.mpr ⟨Θ x, Submodule.mem_map_of_mem hx, rfl⟩)
  · intro v hv
    obtain ⟨y, ⟨x, hx, rfl⟩, rfl⟩ := Submodule.mem_map.mp hv
    have hp : Θ (cH x) ∈ (F₁.map cH.toLinearMap).map Θ :=
      Submodule.mem_map.mpr ⟨cH x, Submodule.mem_map.mpr ⟨x,hx,rfl⟩,rfl⟩
    rw [hε] at hp
    have ht := Submodule.smul_mem ((F₁.map cH.toLinearMap).map Θ) ((ε⁻¹ : Kˣ) : K) hp
    change cV (Θ x) ∈ (F₁.map cH.toLinearMap).map Θ
    have hcoeff : ((ε⁻¹ : Kˣ) : K) * (ε : K) = 1 :=
      congrArg Units.val (inv_mul_cancel ε)
    rwa [smul_smul, hcoeff, one_smul] at ht

private theorem image_le_double (hsplit : F₁ ⊔ F₁.map cH.toLinearMap = ⊤)
    (ε : Kˣ) (hε : ∀ x, Θ (cH x) = (ε : K) • cV (Θ x)) :
    finrank K Θ.range ≤ finrank K (F₁.map Θ) + finrank K (F₁.map Θ) := by
  have he : Θ.range = F₁.map Θ ⊔ (F₁.map Θ).map cV.toLinearMap := by
    rw [← map_conj σ cH cV Θ F₁ ε hε, ← Submodule.map_sup, hsplit, Submodule.map_top]
  rw [he]
  exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans_eq
    (congrArg (finrank K (F₁.map Θ) + ·) (conj_finrank σ cV _))

/-- Rank-nullity for the image of a subspace in the quotient by the filtration. -/
private theorem rank_graded (U : Submodule K V) :
    finrank K (U.map F₂.mkQ) + finrank K (U.comap F₂.subtype) = finrank K U := by
  let q := F₂.mkQ.comp U.subtype
  have hq : q.range = U.map F₂.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hker : q.ker.map U.subtype = (U.comap F₂.subtype).map F₂.subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.map_comap_subtype,
      Submodule.map_comap_subtype, inf_comm]
  have hk : finrank K q.ker = finrank K (U.comap F₂.subtype) := by
    rw [← Submodule.finrank_map_subtype_eq U q.ker, hker, Submodule.finrank_map_subtype_eq]
  exact (hq ▸ hk ▸ q.finrank_range_add_finrank_ker)

theorem dimension_inequality (hsplit : F₁ ⊔ F₁.map cH.toLinearMap = ⊤)
    (ε : Kˣ) (hε : ∀ x, Θ (cH x) = (ε : K) • cV (Θ x))
    (hf : F₁.map Θ ≤ F₂) :
    finrank K (Θ.range.map F₂.mkQ) ≤ finrank K (Θ.range.comap F₂.subtype) := by
  have hUpper : (F₁.map Θ) ≤ (Θ.range.comap F₂.subtype).map F₂.subtype := by
    rw [Submodule.map_comap_subtype]
    refine le_inf hf ?_
    intro v hv
    obtain ⟨x, _, rfl⟩ := Submodule.mem_map.mp hv
    exact ⟨x, rfl⟩
  have he := Submodule.finrank_mono hUpper
  rw [Submodule.finrank_map_subtype_eq] at he
  have hsum := rank_graded F₂ Θ.range
  have hboth := image_le_double σ cH cV Θ F₁ hsplit ε hε
  omega

theorem range_bot_or_top (hsplit : F₁ ⊔ F₁.map cH.toLinearMap = ⊤)
    (ε : Kˣ) (hε : ∀ x, Θ (cH x) = (ε : K) • cV (Θ x))
    (hf : F₁.map Θ ≤ F₂)
    (h : finrank K (Θ.range.map F₂.mkQ) ≤ finrank K (Θ.range.comap F₂.subtype) →
      (Θ.range.comap F₂.subtype = ⊥ ∧ Θ.range.map F₂.mkQ = ⊥) ∨
      (Θ.range.comap F₂.subtype = ⊤ ∧ Θ.range.map F₂.mkQ = ⊤)) :
    Θ.range = ⊥ ∨ Θ.range = ⊤ := by
  rcases h (dimension_inequality σ cH cV Θ F₁ F₂ hsplit ε hε hf) with hz | ht
  · left
    apply Submodule.finrank_eq_zero.mp
    rw [← rank_graded F₂ Θ.range, hz.1, hz.2, finrank_bot, finrank_bot]
  · right
    apply Submodule.eq_top_of_finrank_eq
    rw [← rank_graded F₂ Θ.range, ht.1, ht.2]
    simpa only [finrank_top] using F₂.finrank_quotient_add_finrank

end LinearAlgebra

/-- This statement retains the geometric comparison and stability as
hypotheses. The lower-dimension bound follows from the curve data. -/
theorem exists_parameter_spanning :
    ∃ p : CoeffRing, seedEvaluation p ≠ 0 ∧
      Dense (PrimeSpectrum.basicOpen p : Set (PrimeSpectrum CoeffRing)) ∧
      ∀ (K H V : Type) [Field K] [AddCommGroup H] [Module K H] [AddCommGroup V]
        [Module K V] [FiniteDimensional K V] (φ : CoeffRing →+* K), φ p ≠ 0 →
        ∀ (σ τ : K →+* K) [RingHomInvPair σ τ] [RingHomInvPair τ σ]
          (cH : H ≃ₛₗ[σ] H) (cV : V ≃ₛₗ[σ] V)
          (Θ : H →ₗ[K] V) (F₁ : Submodule K H) (F₂ : Submodule K V)
          (e : F₂ ≃ₗ[K] Upper φ) (f : (V ⧸ F₂) ≃ₗ[K] Lower φ),
          F₁ ⊔ F₁.map cH.toLinearMap = ⊤ →
          (∃ ε : Kˣ, ∀ x, Θ (cH x) = (ε : K) • cV (Θ x)) →
          F₁.map Θ ≤ F₂ →
          (∀ (t : Tangent φ) x, x ∈ (Θ.range.comap F₂.subtype).map e.toLinearMap →
            higgs φ t x ∈ (Θ.range.map F₂.mkQ).map f.toLinearMap) →
          Θ.range = ⊥ ∨ Θ.range = ⊤ := by
  obtain ⟨p,hp,hDense,hgrowth⟩ := CycleQ2HiggsFamilyStrictGrowth.exists_parameter
  refine ⟨p,hp,hDense,?_⟩
  intro K H V _ _ _ _ _ _ φ hφ σ τ _ _ cH cV Θ F₁ F₂ e f hsplit hconj hf hstable
  obtain ⟨ε,hε⟩ := hconj
  apply range_bot_or_top σ cH cV Θ F₁ F₂ hsplit ε hε hf
  intro hrank
  rcases hgrowth K φ hφ _ _ hstable (by simpa only [LinearEquiv.finrank_map_eq] using hrank)
    with hz | ht
  · left
    exact ⟨Submodule.map_injective_of_injective e.injective (by simpa using hz.1),
      Submodule.map_injective_of_injective f.injective (by simpa using hz.2)⟩
  · right
    exact ⟨Submodule.map_injective_of_injective e.injective (by simpa using ht.1),
      Submodule.map_injective_of_injective f.injective (by simpa using ht.2)⟩

end CycleQ2HiggsCurveImage

#print axioms CycleQ2HiggsCurveImage.exists_parameter_spanning
