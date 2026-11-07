import ProjectorCore
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Pi

/-!
# Finite monodromy translates of a nonzero correspondence

This formalizes the linear-algebra passage in §3B.5 of the weighted-threefold
argument from one nonzero correspondence and irreducible monodromy to finitely
many correspondences whose images span the target.

The orbit-image span is proved invariant using the monoid action law. Finite
dimensionality then supplies a finite selection. The resulting map from a
finite product of source spaces is surjective and admits a linear right inverse.
The last theorem obtains the irreducibility input from the already checked
Picard–Lefschetz criterion in `ProjectorCore`.

No cohomology space, algebraic cycle, spreading theorem, or geometric monodromy
hypothesis is constructed here. In particular, the plain linear section below
is not asserted to be induced by an algebraic correspondence. That geometric
step requires the separate polynomial-in-a-correspondence projector argument.
-/

namespace WeightedSexticMonodromy

variable {K V W G : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [Monoid G]

/-- The span of all monodromy translates of the image of one correspondence. -/
def orbitImageSpan (ρ : G →* Module.End K V) (Γ : W →ₗ[K] V) : Submodule K V :=
  Submodule.span K (Set.range fun p : G × W => ρ p.1 (Γ p.2))

/-- The original image is included, by the identity monodromy operator. -/
theorem image_mem_orbitImageSpan (ρ : G →* Module.End K V) (Γ : W →ₗ[K] V) (w : W) :
    Γ w ∈ orbitImageSpan ρ Γ := by
  have h : ρ 1 (Γ w) ∈ orbitImageSpan ρ Γ :=
    Submodule.subset_span ⟨(1, w), rfl⟩
  simpa using h

/-- Invariance is a consequence of the action law, rather than an extra
hypothesis on the span of correspondence images. -/
theorem orbitImageSpan_stable (ρ : G →* Module.End K V) (Γ : W →ₗ[K] V)
    (g : G) {v : V} (hv : v ∈ orbitImageSpan ρ Γ) :
    ρ g v ∈ orbitImageSpan ρ Γ := by
  have hle : orbitImageSpan ρ Γ ≤ (orbitImageSpan ρ Γ).comap (ρ g) := by
    apply Submodule.span_le.mpr
    rintro x ⟨⟨a, w⟩, rfl⟩
    change ρ g (ρ a (Γ w)) ∈ orbitImageSpan ρ Γ
    apply Submodule.subset_span
    exact ⟨(g * a, w), by simp only [map_mul, Module.End.mul_apply]⟩
  exact hle hv

/-- Nonzero source image and irreducibility force the full orbit span to be
the target. Surjectivity of any individual correspondence is not assumed. -/
theorem orbitImageSpan_eq_top
    (ρ : G →* Module.End K V) (Γ : W →ₗ[K] V) (hΓ : Γ ≠ 0)
    (hirred : ∀ U : Submodule K V,
      (∀ g v, v ∈ U → ρ g v ∈ U) → U = ⊥ ∨ U = ⊤) :
    orbitImageSpan ρ Γ = ⊤ := by
  have hnonzero : orbitImageSpan ρ Γ ≠ ⊥ := by
    intro hzero
    apply hΓ
    apply LinearMap.ext
    intro w
    have hw := image_mem_orbitImageSpan ρ Γ w
    simpa only [hzero, Submodule.mem_bot, LinearMap.zero_apply] using hw
  exact (hirred (orbitImageSpan ρ Γ)
    (fun g v hv => orbitImageSpan_stable ρ Γ g hv)).resolve_left hnonzero

/-- An arbitrary spanning set in a finite-dimensional vector space has a
finite spanning subset. The finite subset remains inside the original set. -/
theorem finite_spanning_subset_of_span_eq_top [FiniteDimensional K V]
    {A : Set V} (hA : Submodule.span K A = ⊤) :
    ∃ s : Finset V, (s : Set V) ⊆ A ∧ Submodule.span K (s : Set V) = ⊤ := by
  classical
  obtain ⟨b, hb⟩ := Module.Finite.fg_top (R := K) (M := V)
  have hbA : (b : Set V) ⊆ Submodule.span K A := by
    intro v hv
    rw [hA]
    trivial
  obtain ⟨s, hsA, hbs⟩ := Submodule.subset_span_finite_of_subset_span hbA
  refine ⟨s, hsA, top_unique ?_⟩
  rw [← hb]
  exact Submodule.span_le.mpr hbs

/-- The correspondence from a finite product of source spaces obtained by
adding the selected translated correspondences. -/
noncomputable def finiteTranslateMap {J : Type*} [Fintype J]
    (ρ : G →* Module.End K V) (Γ : W →ₗ[K] V) (g : J → G) :
    (J → W) →ₗ[K] V :=
  ∑ i, ((ρ (g i)).comp Γ).comp (LinearMap.proj i)

theorem finiteTranslateMap_single {J : Type*} [Fintype J] [DecidableEq J]
    (ρ : G →* Module.End K V) (Γ : W →ₗ[K] V) (g : J → G)
    (i : J) (w : W) :
    finiteTranslateMap ρ Γ g (Pi.single i w) = ρ (g i) (Γ w) := by
  simp [finiteTranslateMap, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Pi.single_apply, apply_ite]

/-- Finitely many translates of a nonzero correspondence jointly surject
onto an irreducible finite-dimensional target, and possess a linear section.

The finite index set consists of selected vectors in the orbit image. Repeated
monodromy operators are allowed, as for repeated copies of a source curve.
Neither scalarity of a correspondence composition nor an inverse geometric
correspondence is assumed.
-/
theorem exists_finite_translates_rightInverse [FiniteDimensional K V]
    (ρ : G →* Module.End K V) (Γ : W →ₗ[K] V) (hΓ : Γ ≠ 0)
    (hirred : ∀ U : Submodule K V,
      (∀ g v, v ∈ U → ρ g v ∈ U) → U = ⊥ ∨ U = ⊤) :
    ∃ (s : Finset V) (g : s → G),
      Function.Surjective (finiteTranslateMap ρ Γ g) ∧
      ∃ sectionMap : V →ₗ[K] (s → W),
        (finiteTranslateMap ρ Γ g).comp sectionMap = LinearMap.id := by
  classical
  obtain ⟨s, hs, hspan⟩ := finite_spanning_subset_of_span_eq_top
    (orbitImageSpan_eq_top ρ Γ hΓ hirred)
  have hchoices : ∀ x : s, ∃ p : G × W, ρ p.1 (Γ p.2) = (x : V) := by
    intro x
    exact hs x.property
  choose p hp using hchoices
  let g : s → G := fun x => (p x).1
  have hrange : Submodule.span K (s : Set V) ≤
      LinearMap.range (finiteTranslateMap ρ Γ g) := by
    apply Submodule.span_le.mpr
    intro v hv
    let x : s := ⟨v, hv⟩
    refine ⟨Pi.single x (p x).2, ?_⟩
    simpa only [finiteTranslateMap_single, g] using hp x
  have htop : LinearMap.range (finiteTranslateMap ρ Γ g) = ⊤ := by
    apply top_unique
    rw [← hspan]
    exact hrange
  refine ⟨s, g, LinearMap.range_eq_top.mp htop, ?_⟩
  exact (finiteTranslateMap ρ Γ g).exists_rightInverse_of_surjective htop

/-- The same finite-surjection and splitting conclusion, now deriving
irreducibility from the explicit Picard–Lefschetz data rather than assuming it.

The geometric inputs still required are precisely: a nondegenerate pairing,
spanning vanishing directions, monodromy transvections and transports, and a
nonzero correspondence. All of them are visible hypotheses of this theorem.
-/
theorem exists_finite_translates_rightInverse_of_picardLefschetz
    [FiniteDimensional K V] {I : Type*}
    (ρ : G →* Module.End K V) (Γ : W →ₗ[K] V) (hΓ : Γ ≠ 0)
    (B : V →ₗ[K] V →ₗ[K] K)
    (hB : ∀ v, (∀ x, B v x = 0) → v = 0)
    (w : I → V) (hspan : Submodule.span K (Set.range w) = ⊤)
    (c : I → K) (hc : ∀ i, c i ≠ 0)
    (transvection : I → G)
    (htransvection : ∀ i v,
      ρ (transvection i) v = v + (c i * B v (w i)) • w i)
    (transport : I → I → G) (a : I → I → K)
    (ha : ∀ i j, a i j ≠ 0)
    (htransport : ∀ i j, ρ (transport i j) (w i) = a i j • w j) :
    ∃ (s : Finset V) (g : s → G),
      Function.Surjective (finiteTranslateMap ρ Γ g) ∧
      ∃ sectionMap : V →ₗ[K] (s → W),
        (finiteTranslateMap ρ Γ g).comp sectionMap = LinearMap.id := by
  apply exists_finite_translates_rightInverse ρ Γ hΓ
  intro U hstable
  apply invariant_submodule_eq_bot_or_top B hB w hspan c hc
    (fun i j => ρ (transport i j)) a ha htransport U
  · intro i v hv
    rw [← htransvection i v]
    exact hstable (transvection i) v hv
  · intro i j v hv
    exact hstable (transport i j) v hv

#print axioms orbitImageSpan_stable
#print axioms orbitImageSpan_eq_top
#print axioms finite_spanning_subset_of_span_eq_top
#print axioms exists_finite_translates_rightInverse
#print axioms exists_finite_translates_rightInverse_of_picardLefschetz

end WeightedSexticMonodromy
