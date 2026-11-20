import Proposal.GeometricVariation
import Proposal.GeometricHiggsStrictGrowth
import Mathlib.Data.Fin.Rev
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The Fermat Higgs maps grow strictly

A cycle visiting all 33 upper labels gives two matchings of upper labels
with lower labels. Lower labels are reversed from the complementary
socle order so that each partial multiplication is increasing.
The cycle uses the very same complement table as the Fermat matrices.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
noncomputable section
namespace CycleQ2FermatStrictGrowth

open CycleQ2FermatHiggs CycleQ2HiggsStrictGrowth

/-- The output row is indexed in increasing lower monomial order. -/
def ordered (K : Type*) [Zero K] [One K] (m : Fin 35) :
    Matrix (Fin 33) (Fin 33) K :=
  fun j i => higgsMatrix K m i j.rev

private def successor : Fin 33 → Fin 33 := ![10, 6, 32, 26, 18, 28, 31, 16, 14, 13, 21, 30, 29, 22, 27, 9, 15, 23, 12, 2, 17, 1, 20, 24, 25, 0, 11, 19, 7, 3, 5, 8, 4]
private def predecessor : Fin 33 → Fin 33 := ![25, 21, 19, 29, 32, 30, 1, 28, 31, 15, 0, 26, 18, 9, 8, 16, 7, 20, 4, 27, 22, 10, 13, 17, 23, 24, 3, 14, 5, 12, 11, 6, 2]

private def cycle : Fin 33 ≃ Fin 33 where
  toFun := successor
  invFun := predecessor
  left_inv := by decide
  right_inv := by decide

private def forward : Fin 33 ≃ Fin 33 := cycle.trans Fin.revPerm
private def backward : Fin 33 ≃ Fin 33 := cycle.symm.trans Fin.revPerm

private theorem next_edge : ∀ i : Fin 33, ∃ m : Fin 35, complement m i = some (successor i) := by
  decide +kernel

private theorem prev_edge : ∀ i : Fin 33, ∃ m : Fin 35, complement m i = some (predecessor i) := by
  decide +kernel

private theorem orbit_zero : ∀ j : Fin 33, ∃ n : Fin 33, ((backward.trans forward.symm)^[n.val]) 0 = j := by
  decide +kernel

private theorem loop : ((backward.trans forward.symm)^[33]) (0 : Fin 33) = 0 := by
  decide +kernel

private theorem connected (i j : Fin 33) : ∃ n : ℕ, ((backward.trans forward.symm)^[n]) i = j := by
  obtain ⟨a, ha⟩ := orbit_zero i
  obtain ⟨b, hb⟩ := orbit_zero j
  let e := backward.trans forward.symm
  have hi : (e^[33 - a.val]) i = 0 := by
    rw [← ha, ← Function.iterate_add_apply, Nat.sub_add_cancel a.isLt.le]
    exact loop
  refine ⟨b.val + (33 - a.val), ?_⟩
  change (e^[b.val + (33 - a.val)]) i = j
  rw [Function.iterate_add_apply, hi]
  exact hb

private theorem entry_iff (K : Type*) [Field K] (m : Fin 35) (i j : Fin 33) :
    ordered K m j i ≠ 0 ↔ complement m i = some j.rev := by
  unfold ordered higgsMatrix
  split <;> simp_all

private def Increases (m : Fin 35) (i i' : Fin 33) : Prop :=
  match complement m i, complement m i' with
  | some j, some j' => i < i' → j.rev < j'.rev
  | _, _ => True

private instance (m : Fin 35) (i i' : Fin 33) : Decidable (Increases m i i') := by
  unfold Increases
  split <;> infer_instance

private theorem increases (m : Fin 35) : ∀ i i' : Fin 33, Increases m i i' := by
  fin_cases m <;> decide +kernel

variable (K : Type*) [Field K]

private theorem forward_edge (i : Fin 33) : Edge (ordered K) i (forward i) := by
  obtain ⟨m, hm⟩ := next_edge i
  refine ⟨m, (entry_iff K m i _).mpr ?_⟩
  change complement m i = some (successor i).rev.rev
  rwa [Fin.rev_rev]

private theorem backward_edge (i : Fin 33) : Edge (ordered K) i (backward i) := by
  obtain ⟨m, hm⟩ := prev_edge i
  refine ⟨m, (entry_iff K m i _).mpr ?_⟩
  change complement m i = some (predecessor i).rev.rev
  rwa [Fin.rev_rev]

private theorem column_unique (m : Fin 35) (i j j' : Fin 33)
    (hj : ordered K m j i ≠ 0) (hj' : ordered K m j' i ≠ 0) : j = j' := by
  apply Fin.rev_injective
  exact Option.some.inj (((entry_iff K m i j).mp hj).symm.trans ((entry_iff K m i j').mp hj'))

private theorem order_preserving (m : Fin 35) (i i' j j' : Fin 33) (hi : i < i')
    (hj : ordered K m j i ≠ 0) (hj' : ordered K m j' i' ≠ 0) : j < j' := by
  have h := increases m i i'
  unfold Increases at h
  rw [(entry_iff K m i j).mp hj, (entry_iff K m i' j').mp hj'] at h
  simpa only [Fin.rev_rev] using h hi

theorem strict_growth (W V : Submodule K (Fin 33 → K))
    (hmap : ∀ (m : Fin 35) (x : Fin 33 → K), x ∈ W → (ordered K m).mulVec x ∈ V)
    (hpos : 0 < Module.finrank K W) (hproper : Module.finrank K W < 33) :
    Module.finrank K W < Module.finrank K V := by
  have he := card_pivots W
  have hne : (pivots W).Nonempty := Finset.card_pos.mp (he.symm ▸ hpos)
  have hnot : pivots W ≠ Finset.univ := by
    intro h
    rw [h, Finset.card_univ, Fintype.card_fin] at he
    exact (Nat.ne_of_lt hproper) he.symm
  have hg := card_lt_neighbors (ordered K) forward backward
    (forward_edge K) (backward_edge K) connected (pivots W) hne hnot
  have hs := neighbors_pivots_subset (ordered K) W V
    (column_unique K) (order_preserving K) hmap
  rw [← card_pivots W, ← card_pivots V]
  exact hg.trans_le (Finset.card_le_card hs)

/-- The images of the full upper space span all lower coordinates. -/
theorem full_span (V : Submodule K (Fin 33 → K))
    (hmap : ∀ (m : Fin 35) (x : Fin 33 → K), (ordered K m).mulVec x ∈ V) : V = ⊤ := by
  classical
  apply Submodule.eq_top_of_finrank_eq
  rw [← card_pivots V]
  have hs := neighbors_pivots_subset (ordered K) ⊤ V
    (column_unique K) (order_preserving K) (fun m x _ => hmap m x)
  have hfull : pivots V = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro j
    let i := forward.symm j
    apply hs
    apply (mem_neighbors (ordered K) _ j).mpr
    refine ⟨i, (mem_pivots ⊤ i).mpr ⟨⟨Pi.single i 1, Submodule.mem_top⟩, ?_⟩, ?_⟩
    · exact ⟨by simp, fun k hk => by simp [ne_of_gt hk]⟩
    · simpa [i] using forward_edge K i
  rw [hfull, Finset.card_univ, Module.finrank_pi]

/-- In a Higgs-stable pair with lower dimension at most the upper
dimension, both spaces are zero or both spaces are full. -/
theorem stable_pair_trivial (W V : Submodule K (Fin 33 → K))
    (hmap : ∀ (m : Fin 35) (x : Fin 33 → K), x ∈ W → (ordered K m).mulVec x ∈ V)
    (hrank : Module.finrank K V ≤ Module.finrank K W) :
    (W = ⊥ ∧ V = ⊥) ∨ (W = ⊤ ∧ V = ⊤) := by
  by_cases hzero : W = ⊥
  · left
    refine ⟨hzero, Submodule.finrank_eq_zero.mp ?_⟩
    rw [hzero, finrank_bot] at hrank
    exact Nat.eq_zero_of_le_zero hrank
  by_cases hfull : W = ⊤
  · right
    refine ⟨hfull, full_span K V ?_⟩
    intro m x
    exact hmap m x (hfull ▸ Submodule.mem_top)
  · have h := Submodule.finrank_lt hfull
    rw [Module.finrank_pi, Fintype.card_fin] at h
    have hz : 0 < Module.finrank K W :=
      Nat.pos_of_ne_zero (fun hz => hzero (Submodule.finrank_eq_zero.mp hz))
    exact (not_lt_of_ge hrank (strict_growth K W V hmap hz h)).elim

end CycleQ2FermatStrictGrowth

#print axioms CycleQ2FermatStrictGrowth.strict_growth
#print axioms CycleQ2FermatStrictGrowth.stable_pair_trivial
