import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Finset.Max

/-!
# Strict growth for ordered monomial maps

The leading indices of a coordinate subspace count its dimension.
An ordered partial monomial map sends a leading index in its domain
to a leading index of the image. Two matchings whose relative
permutation is transitive force strict growth on every proper nonzero
subspace, as in the strict-growth lemma of Chapter 4, Section 4.4.

Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
noncomputable section

namespace CycleQ2HiggsStrictGrowth

open scoped BigOperators

variable {K I J D : Type*} [Field K] [Fintype I] [Fintype J]
  [LinearOrder I] [LinearOrder J] [Fintype D]

def Leads (x : I → K) (i : I) : Prop :=
  x i ≠ 0 ∧ ∀ j, i < j → x j = 0

private theorem exists_leading (x : I → K) (hx : x ≠ 0) : ∃ i, Leads x i := by
  classical
  let s : Finset I := Finset.univ.filter (fun i => x i ≠ 0)
  have hs : s.Nonempty := by
    by_contra hn
    apply hx
    funext i
    by_contra hi
    exact hn ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  refine ⟨s.max' hs, (Finset.mem_filter.mp (s.max'_mem hs)).2, ?_⟩
  intro j hj
  by_contra hn
  exact (not_le_of_gt hj) (s.le_max' _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩))

def pivots (W : Submodule K (I → K)) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => ∃ x : W, Leads x.val i)

theorem mem_pivots (W : Submodule K (I → K)) (i : I) :
    i ∈ pivots W ↔ ∃ x : W, Leads x.val i := by
  classical
  simp [pivots]

theorem card_pivots (W : Submodule K (I → K)) :
    (pivots W).card = Module.finrank K W := by
  classical
  let S := pivots W
  let r : W →ₗ[K] (S → K) :=
    { toFun := fun x i => x.val i.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hr : Function.Injective r := by
    intro x y h
    by_contra hxy
    have hn : (x - y : W).val ≠ 0 := by
      intro hz
      apply hxy
      apply sub_eq_zero.mp
      apply Subtype.ext
      exact hz
    obtain ⟨i, hi⟩ := exists_leading _ hn
    have hm : i ∈ S := (mem_pivots W i).mpr ⟨x - y, hi⟩
    exact hi.1 (sub_eq_zero.mpr (congrFun h ⟨i, hm⟩))
  have upper := r.finrank_le_finrank_of_injective hr
  rw [Module.finrank_pi, Fintype.card_coe] at upper
  choose v hv using fun i : S => (mem_pivots W i.val).mp i.property
  have hind : LinearIndependent K v := by
    rw [linearIndependent_iff']
    intro t c hz i hi
    by_contra hn
    let u := t.filter (fun k => c k ≠ 0)
    have hu : u.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hn⟩⟩
    let k := u.max' hu
    have hk := Finset.mem_filter.mp (u.max'_mem hu)
    let e : W →ₗ[K] K := (LinearMap.proj k.val).comp W.subtype
    have he := congrArg e hz
    simp only [map_sum, map_smul, map_zero, smul_eq_mul] at he
    rw [Finset.sum_eq_single k] at he
    · exact (mul_ne_zero hk.2 (hv k).1) he
    · intro l hl hne
      by_cases hc : c l = 0
      · rw [hc, zero_mul]
      have hlk : l < k :=
        lt_of_le_of_ne (u.le_max' _ (Finset.mem_filter.mpr ⟨hl, hc⟩)) hne
      change c l * (v l).val k.val = 0
      rw [(hv l).2 _ hlk, mul_zero]
    · exact fun hn => (hn hk.1).elim
  have lower := hind.fintype_card_le_finrank
  rw [Fintype.card_coe] at lower
  exact le_antisymm lower upper

variable (M : D → Matrix J I K)

def Edge (i : I) (j : J) : Prop := ∃ m, M m j i ≠ 0

def neighbors (s : Finset I) : Finset J := by
  classical
  exact Finset.univ.filter (fun j => ∃ i ∈ s, Edge M i j)

omit [Fintype I] [LinearOrder I] [LinearOrder J] [Fintype D] in
theorem mem_neighbors (s : Finset I) (j : J) :
    j ∈ neighbors M s ↔ ∃ i ∈ s, Edge M i j := by
  classical
  simp [neighbors]

/-- Two matchings with a transitive relative permutation give strict
expansion for every nonempty proper subset. -/
theorem card_lt_neighbors (μ τ : I ≃ J)
    (hμ : ∀ i, Edge M i (μ i)) (hτ : ∀ i, Edge M i (τ i))
    (hconn : ∀ i j, ∃ n : ℕ, ((τ.trans μ.symm)^[n]) i = j)
    (s : Finset I) (hs : s.Nonempty) (hproper : s ≠ Finset.univ) :
    s.card < (neighbors M s).card := by
  classical
  have hsub : s.image μ ⊆ neighbors M s := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact (mem_neighbors M s _).mpr ⟨i, hi, hμ i⟩
  by_contra hn
  have he : s.image μ = neighbors M s := Finset.eq_of_subset_of_card_le hsub (by
    rw [Finset.card_image_of_injective _ μ.injective]
    exact Nat.le_of_not_gt hn)
  have step (i : I) (hi : i ∈ s) : (τ.trans μ.symm) i ∈ s := by
    have hb : τ i ∈ s.image μ := by
      rw [he]
      exact (mem_neighbors M s _).mpr ⟨i, hi, hτ i⟩
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hb
    have hj' : j = (τ.trans μ.symm) i := by
      apply μ.injective
      simpa using heq
    exact hj' ▸ hj
  obtain ⟨i, hi⟩ := hs
  have closed (n : ℕ) : ((τ.trans μ.symm)^[n]) i ∈ s := by
    induction n with
    | zero => exact hi
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact step _ ih
  apply hproper
  apply Finset.eq_univ_of_forall
  intro j
  obtain ⟨n, hn⟩ := hconn i j
  exact hn ▸ closed n

/-- The top coordinate survives every partial monomial map defined on it. -/
theorem leading_mulVec (m : D)
    (hcol : ∀ (i : I) (j j' : J), M m j i ≠ 0 → M m j' i ≠ 0 → j = j')
    (hord : ∀ (i i' : I) (j j' : J), i < i' → M m j i ≠ 0 → M m j' i' ≠ 0 → j < j')
    {x : I → K} {i : I} {j : J} (hx : Leads x i) (hij : M m j i ≠ 0) :
    Leads ((M m).mulVec x) j := by
  classical
  constructor
  · rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
    · exact mul_ne_zero hij hx.1
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with hlt | hgt
      · have hm : M m j k = 0 := by
          by_contra hn
          exact (lt_irrefl j) (hord _ _ _ _ hlt hn hij)
        rw [hm, zero_mul]
      · rw [hx.2 k hgt, mul_zero]
    · simp
  · intro l hl
    change (∑ k, M m l k * x k) = 0
    apply Finset.sum_eq_zero
    intro k _
    rcases lt_trichotomy k i with hk | rfl | hk
    · have hm : M m l k = 0 := by
        by_contra hn
        exact (not_lt_of_ge hl.le) (hord _ _ _ _ hk hn hij)
      rw [hm, zero_mul]
    · have hm : M m l k = 0 := by
        by_contra hn
        exact (ne_of_lt hl) (hcol _ _ _ hij hn)
      rw [hm, zero_mul]
    · rw [hx.2 _ hk, mul_zero]

theorem neighbors_pivots_subset (W : Submodule K (I → K)) (V : Submodule K (J → K))
    (hcol : ∀ (m : D) (i : I) (j j' : J), M m j i ≠ 0 → M m j' i ≠ 0 → j = j')
    (hord : ∀ (m : D) (i i' : I) (j j' : J), i < i' →
      M m j i ≠ 0 → M m j' i' ≠ 0 → j < j')
    (hmap : ∀ (m : D) (x : I → K), x ∈ W → (M m).mulVec x ∈ V) :
    neighbors M (pivots W) ⊆ pivots V := by
  intro j hj
  obtain ⟨i, hi, m, hm⟩ := (mem_neighbors M _ _).mp hj
  obtain ⟨x, hx⟩ := (mem_pivots W i).mp hi
  exact (mem_pivots V j).mpr ⟨⟨_, hmap m x.val x.property⟩,
    leading_mulVec M m (hcol m) (hord m) hx hm⟩

end CycleQ2HiggsStrictGrowth

#print axioms CycleQ2HiggsStrictGrowth.card_pivots
#print axioms CycleQ2HiggsStrictGrowth.card_lt_neighbors
#print axioms CycleQ2HiggsStrictGrowth.neighbors_pivots_subset
