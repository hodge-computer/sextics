import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Homogeneous Away maps with an explicitly identified denominator

Specialization sends an original homogeneous coordinate to the literal
coordinate in the seed ring. The equality need not be definitional.
Using the general homogeneous-localization map makes the target Away
ring exact, while substitution of the equality recovers the usual
fraction formula and the actual Proj chart naturality square.

Source-only draft: no Lean elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GradedAwaySpecialization

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

variable {A B σ τ : Type*}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
variable {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

def awayMapOfEq (g : 𝒜 →+*ᵍ ℬ) (s : A) (b : B) (h : g s = b) :
    Away 𝒜 s →+* Away ℬ b :=
  HomogeneousLocalization.map g (by
    rintro a ⟨n, rfl⟩
    change g (s ^ n) ∈ Submonoid.powers b
    exact ⟨n, by rw [map_pow, h]⟩)

@[simp] theorem awayMapOfEq_mk (g : 𝒜 →+*ᵍ ℬ) (s : A) (b : B) (h : g s = b)
    {d : ℕ} (hs : s ∈ 𝒜 d) (hb : b ∈ ℬ d) (n : ℕ)
    (a : A) (ha : a ∈ 𝒜 (n • d)) :
    awayMapOfEq g s b h (Away.mk 𝒜 hs n a ha) =
      Away.mk ℬ hb n (g a) (g.2 ha) := by
  subst b
  exact Away.map_mk g s hs n a ha

/-- Naturality for the actual Proj chart maps, with a target denominator
identified by equality rather than required to be syntactically g s. -/
@[reassoc] theorem awayι_comp_map_of_eq (g : 𝒜 →+*ᵍ ℬ)
    (hg : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g)
    (s : A) (b : B) (h : g s = b) {d : ℕ} (hd : 0 < d)
    (hs : s ∈ 𝒜 d) (hb : b ∈ ℬ d) :
    Proj.awayι ℬ b hb hd ≫ Proj.map g hg =
      Spec.map (CommRingCat.ofHom (awayMapOfEq g s b h)) ≫ Proj.awayι 𝒜 s hs hd := by
  subst b
  exact Proj.awayι_comp_map g hg hd s hs

#print axioms awayMapOfEq_mk
#print axioms awayι_comp_map_of_eq

end CycleQ2GradedAwaySpecialization
end
