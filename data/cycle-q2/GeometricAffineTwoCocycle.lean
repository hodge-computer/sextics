import Proposal.GeometricAffineCohomology
import Proposal.GeometricCechRefinement

/-!
# Principal-cover degree-two exactness for the additive affine structure sheaf

Clear each triple-overlap section to a common power. A second common power
removes the localization torsion from the quadruple relations. A partition
of one then contracts the resulting polynomial cocycle.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricAffineTwoCocycle

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricAffineCohomology
open scoped BigOperators

variable {A : Type} [CommRing A] {ι : Type} [Fintype ι]

private theorem triple₀ (x y z : A) :
    PrimeSpectrum.basicOpen (x*y*z) ≤ PrimeSpectrum.basicOpen (y*z) := by
  simp only [PrimeSpectrum.basicOpen_mul]
  exact inf_le_inf_right _ inf_le_right

private theorem triple₁ (x y z : A) :
    PrimeSpectrum.basicOpen (x*y*z) ≤ PrimeSpectrum.basicOpen (x*z) := by
  simp only [PrimeSpectrum.basicOpen_mul]
  exact inf_le_inf_right _ inf_le_left

private theorem triple₂ (x y z : A) :
    PrimeSpectrum.basicOpen (x*y*z) ≤ PrimeSpectrum.basicOpen (x*y) :=
  PrimeSpectrum.basicOpen_mul_le_left _ _

private theorem quad₀ (x y z t : A) :
    PrimeSpectrum.basicOpen (x*y*z*t) ≤ PrimeSpectrum.basicOpen (y*z*t) := by
  simp only [PrimeSpectrum.basicOpen_mul]
  exact inf_le_inf_right _ (inf_le_inf_right _ inf_le_right)

private theorem quad₁ (x y z t : A) :
    PrimeSpectrum.basicOpen (x*y*z*t) ≤ PrimeSpectrum.basicOpen (x*z*t) := by
  simp only [PrimeSpectrum.basicOpen_mul]
  exact inf_le_inf_right _ (inf_le_inf_right _ inf_le_left)

private theorem quad₂ (x y z t : A) :
    PrimeSpectrum.basicOpen (x*y*z*t) ≤ PrimeSpectrum.basicOpen (x*y*t) := by
  simp only [PrimeSpectrum.basicOpen_mul]
  exact inf_le_inf_right _ inf_le_left

private theorem quad₃ (x y z t : A) :
    PrimeSpectrum.basicOpen (x*y*z*t) ≤ PrimeSpectrum.basicOpen (x*y*z) :=
  PrimeSpectrum.basicOpen_mul_le_left _ _

def IsProductTwoCocycle (f : ι → A) (c : ∀ i j k, Sections (f i * f j * f k)) : Prop :=
  ∀ i j k l, restrict (quad₀ (f i) (f j) (f k) (f l)) (c j k l) -
    restrict (quad₁ (f i) (f j) (f k) (f l)) (c i k l) +
    restrict (quad₂ (f i) (f j) (f k) (f l)) (c i j l) =
    restrict (quad₃ (f i) (f j) (f k) (f l)) (c i j k)

private theorem cleared_two_cocycle (f : ι → A)
    (c : ∀ i j k, Sections (f i * f j * f k)) (hc : IsProductTwoCocycle f c) :
    ∃ (N : ℕ) (a : ι → ι → ι → A),
      (∀ i j k, c i j k * algebraMap A _ ((f i * f j * f k) ^ N) = algebraMap A _ (a i j k)) ∧
      (∀ i j k l, a j k l * f i ^ N - a i k l * f j ^ N + a i j l * f k ^ N =
        a i j k * f l ^ N) := by
  classical
  obtain ⟨N, num, hnum⟩ := uniform_denominators
    (fun p : ι × ι × ι => f p.1 * f p.2.1 * f p.2.2) (fun p => c p.1 p.2.1 p.2.2)
  let a (i j k : ι) := num (i, j, k)
  have ha (i j k : ι) : c i j k * algebraMap A _ ((f i * f j * f k) ^ N) =
      algebraMap A _ (a i j k) := hnum (i,j,k)
  have hloc (i j k l : ι) :
      algebraMap A (Sections (f i * f j * f k * f l))
        (a j k l * f i ^ N - a i k l * f j ^ N + a i j l * f k ^ N) =
      algebraMap A _ (a i j k * f l ^ N) := by
    have h₀ := congrArg (restrict (quad₀ (f i) (f j) (f k) (f l))) (ha j k l)
    have h₁ := congrArg (restrict (quad₁ (f i) (f j) (f k) (f l))) (ha i k l)
    have h₂ := congrArg (restrict (quad₂ (f i) (f j) (f k) (f l))) (ha i j l)
    have h₃ := congrArg (restrict (quad₃ (f i) (f j) (f k) (f l))) (ha i j k)
    simp only [map_mul, restrict_algebraMap] at h₀ h₁ h₂ h₃
    simp only [map_add, map_sub, map_mul, ← h₀, ← h₁, ← h₂, ← h₃, map_pow, mul_pow]
    have H := congrArg (fun z : Sections (f i * f j * f k * f l) =>
      z * algebraMap A _ ((f i * f j * f k * f l)^N)) (hc i j k l)
    simp only [map_mul, mul_pow, map_pow] at H
    linear_combination H
  choose m hm using fun i j k l =>
    IsLocalization.Away.exists_of_eq (f i * f j * f k * f l) (hloc i j k l)
  let M := Finset.univ.sup (fun p : ι × ι × ι × ι => m p.1 p.2.1 p.2.2.1 p.2.2.2)
  have hM (i j k l : ι) : m i j k l ≤ M :=
    Finset.le_sup (f := fun p : ι × ι × ι × ι => m p.1 p.2.1 p.2.2.1 p.2.2.2)
      (Finset.mem_univ (i, j, k, l))
  refine ⟨M+N, fun i j k => (f i * f j * f k)^M * a i j k, ?_, ?_⟩
  · intro i j k
    rw [map_mul, ← ha i j k, pow_add, map_mul]
    ring
  · intro i j k l
    have H := congrArg (fun z : A => (f i * f j * f k * f l) ^ (M - m i j k l) * z)
      (hm i j k l)
    simp only [← mul_assoc, ← pow_add, Nat.sub_add_cancel (hM i j k l)] at H
    simp only [pow_add, mul_pow] at H ⊢
    linear_combination H

private theorem power_two_cocycle_exact (f : ι → A) (hf : Ideal.span (Set.range f) = ⊤)
    (N : ℕ) (a : ι → ι → ι → A)
    (hc : ∀ i j k l, a j k l * f i ^ N - a i k l * f j ^ N + a i j l * f k ^ N =
      a i j k * f l ^ N) :
    ∃ b : ι → ι → A, ∀ i j k,
      b j k * f i ^ N - b i k * f j ^ N + b i j * f k ^ N = a i j k := by
  classical
  obtain ⟨w, hw⟩ := finite_power_partition f hf N
  refine ⟨fun i j => ∑ l, w l * a i j l, fun i j k => ?_⟩
  simp only [Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  calc
    _ = ∑ l, w l * (a i j k * f l ^ N) := by
      apply Finset.sum_congr rfl
      intro l _
      linear_combination w l * hc i j k l
    _ = a i j k * (∑ l, w l * f l ^ N) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = _ := by rw [hw, mul_one]

theorem finite_two_cocycle_exact (f : ι → A) (hf : Ideal.span (Set.range f) = ⊤)
    (c : ∀ i j k, Sections (f i * f j * f k)) (hc : IsProductTwoCocycle f c) :
    ∃ b : ∀ i j, Sections (f i * f j), ∀ i j k,
      restrict (triple₀ (f i) (f j) (f k)) (b j k) -
      restrict (triple₁ (f i) (f j) (f k)) (b i k) +
      restrict (triple₂ (f i) (f j) (f k)) (b i j) = c i j k := by
  obtain ⟨N, a, ha, hc'⟩ := cleared_two_cocycle f c hc
  obtain ⟨b, hb⟩ := power_two_cocycle_exact f hf N a hc'
  let s (i j : ι) : Sections (f i * f j) :=
    IsLocalization.mk' (Sections (f i * f j)) (b i j) (Submonoid.pow (f i * f j) N)
  have hs (i j : ι) : s i j * algebraMap A _ ((f i * f j) ^ N) = algebraMap A _ (b i j) :=
    IsLocalization.mk'_spec (Sections (f i * f j)) (b i j) (Submonoid.pow (f i * f j) N)
  refine ⟨s, fun i j k => ?_⟩
  have hjk := congrArg (restrict (triple₀ (f i) (f j) (f k))) (hs j k)
  have hik := congrArg (restrict (triple₁ (f i) (f j) (f k))) (hs i k)
  have hij := congrArg (restrict (triple₂ (f i) (f j) (f k))) (hs i j)
  simp only [map_mul, restrict_algebraMap] at hjk hik hij
  have hu : IsUnit (algebraMap A (Sections (f i * f j * f k)) ((f i * f j * f k) ^ N)) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit (f i * f j * f k)).pow N
  apply hu.mul_left_inj.mp
  rw [ha i j k, ← hb i j k, map_add, map_sub, map_mul, map_mul, map_mul,
    ← hjk, ← hik, ← hij]
  simp only [mul_pow, map_mul, map_pow]
  ring

open CycleQ2FiniteInjectiveCech CycleQ2GeometricSheafLocalIso

/-- Every two-cocycle of the additive structure sheaf on a finite principal
cover is the boundary of sections on the original pair intersections. -/
theorem primitive (f : ι → A) (hf : Ideal.span (Set.range f) = ⊤)
    (c : Two (X := PrimeSpectrum.Top A) (additiveStructureSheaf A) (fun i => PrimeSpectrum.basicOpen (f i)))
    (hc : IsTwoCocycle (additiveStructureSheaf A) (fun i => PrimeSpectrum.basicOpen (f i)) c) :
    ∃ b : One (X := PrimeSpectrum.Top A) (additiveStructureSheaf A) (fun i => PrimeSpectrum.basicOpen (f i)),
      ∀ i j k W hi hj hk,
        boundaryValue (additiveStructureSheaf A) _ b i j k W hi hj hk =
          faceValue (additiveStructureSheaf A) _ c i j k W hi hj hk := by
  let F := additiveStructureSheaf A
  let U := fun i => PrimeSpectrum.basicOpen (f i)
  let d (i j k : ι) : Sections (f i * f j * f k) :=
    res F (show PrimeSpectrum.basicOpen (f i * f j * f k) ≤ (U i ⊓ U j) ⊓ U k by
      simp [U, PrimeSpectrum.basicOpen_mul]) (c i j k)
  have hr (i j k : ι) (g : A) (h : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen (f i * f j * f k))
      (hi : PrimeSpectrum.basicOpen g ≤ U i) (hj : PrimeSpectrum.basicOpen g ≤ U j)
      (hk : PrimeSpectrum.basicOpen g ≤ U k) :
      restrict h (d i j k) = faceValue F U c i j k (PrimeSpectrum.basicOpen g) hi hj hk :=
    res_comp F _ h (c i j k)
  obtain ⟨b, hb⟩ := finite_two_cocycle_exact f hf d (by
    intro i j k l
    let g := f i * f j * f k * f l
    have h : PrimeSpectrum.basicOpen g ≤ ((U i ⊓ U j) ⊓ U k) ⊓ U l := by
      simp [g, U, PrimeSpectrum.basicOpen_mul]
    have hi := h.trans ((inf_le_left.trans inf_le_left).trans inf_le_left)
    have hj := h.trans ((inf_le_left.trans inf_le_left).trans inf_le_right)
    have hk := h.trans (inf_le_left.trans inf_le_right)
    have hl := h.trans inf_le_right
    rw [hr j k l g _ hj hk hl, hr i k l g _ hi hk hl, hr i j l g _ hi hj hl,
      hr i j k g _ hi hj hk]
    exact sub_eq_zero.mp (hc i j k l (PrimeSpectrum.basicOpen g) hi hj hk hl))
  let a : One F U := fun i j =>
    res F (show U i ⊓ U j ≤ PrimeSpectrum.basicOpen (f i * f j) by
      simp [U, PrimeSpectrum.basicOpen_mul]) (b i j)
  refine ⟨a, fun i j k W hi hj hk => ?_⟩
  have hW : W ≤ PrimeSpectrum.basicOpen (f i * f j * f k) := by
    simpa only [PrimeSpectrum.basicOpen_mul, U] using le_inf (le_inf hi hj) hk
  have hedge (u v : ι) (hu : W ≤ U u) (hv : W ≤ U v)
      (h : PrimeSpectrum.basicOpen (f i * f j * f k) ≤ PrimeSpectrum.basicOpen (f u * f v)) :
      res F hW (restrict h (b u v)) = edgeValue F U a u v W hu hv := by
    change res F hW (res F h (b u v)) = res F (le_inf hu hv) (res F _ (b u v))
    rw [res_comp, res_comp]
  have he := congrArg (res F hW) (hb i j k)
  simp only [map_sub, map_add] at he
  rw [hedge j k hj hk, hedge i k hi hk, hedge i j hi hj] at he
  exact he.trans (res_comp F _ hW (c i j k))

end CycleQ2GeometricAffineTwoCocycle
end

#print axioms CycleQ2GeometricAffineTwoCocycle.finite_two_cocycle_exact
#print axioms CycleQ2GeometricAffineTwoCocycle.primitive
