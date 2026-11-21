import Proposal.GeometricVariation
import Proposal.GeometricHiggsStrictGrowth
import Mathlib.Data.Fin.Rev
import Mathlib.LinearAlgebra.Prod
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

/-- All images of a space have total rank at least its original rank, with strict
growth for every nonzero proper space. -/
def RankGrowth (M : Fin 35 → Matrix (Fin 33) (Fin 33) K) : Prop :=
  ∀ W V : Submodule K (Fin 33 → K),
    (∀ (m : Fin 35) (x : Fin 33 → K), x ∈ W → (M m).mulVec x ∈ V) →
    Module.finrank K W ≤ Module.finrank K V ∧
      (0 < Module.finrank K W → Module.finrank K W < 33 → Module.finrank K W < Module.finrank K V)

private theorem growth_of_matchings (M : Fin 35 → Matrix (Fin 33) (Fin 33) K)
    (μ τ : Fin 33 ≃ Fin 33) (hμ : ∀ i, Edge M i (μ i)) (hτ : ∀ i, Edge M i (τ i))
    (hc : ∀ i j, ∃ n : ℕ, ((τ.trans μ.symm)^[n]) i = j)
    (cu : ∀ m i j j', M m j i ≠ 0 → M m j' i ≠ 0 → j = j')
    (incr : ∀ m i i' j j', i < i' → M m j i ≠ 0 → M m j' i' ≠ 0 → j < j') :
    RankGrowth K M := by
  classical
  intro W V hmap
  have hs := neighbors_pivots_subset M W V cu incr hmap
  have sub : (pivots W).image μ ⊆ neighbors M (pivots W) := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    exact (mem_neighbors M _ _).mpr ⟨i,hi,hμ i⟩
  constructor
  · have h := Finset.card_le_card (sub.trans hs)
    simpa only [Finset.card_image_of_injective _ μ.injective, card_pivots] using h
  · intro hpos hproper
    have he := card_pivots W
    have hne : (pivots W).Nonempty := Finset.card_pos.mp (he.symm ▸ hpos)
    have hnot : pivots W ≠ Finset.univ := by
      intro h
      rw [h, Finset.card_univ, Fintype.card_fin] at he
      exact (Nat.ne_of_lt hproper) he.symm
    have h := (card_lt_neighbors M μ τ hμ hτ hc _ hne hnot).trans_le (Finset.card_le_card hs)
    simpa only [card_pivots] using h

private theorem weighted_forward (M : Fin 35 → Matrix (Fin 33) (Fin 33) K)
    (h : ∀ m i j, M m j i ≠ 0 ↔ ordered K m j i ≠ 0) : RankGrowth K M := by
  have edge {i j : Fin 33} (e : Edge (ordered K) i j) : Edge M i j := by
    obtain ⟨m,hm⟩ := e
    exact ⟨m,(h m i j).mpr hm⟩
  exact growth_of_matchings K M forward backward (fun i => edge (forward_edge K i))
    (fun i => edge (backward_edge K i)) connected
    (fun m i j j' a b => column_unique K m i j j' ((h ..).mp a) ((h ..).mp b))
    (fun m i i' j j' lt a b => order_preserving K m i i' j j' lt ((h ..).mp a) ((h ..).mp b))

private theorem weighted_reverse (M : Fin 35 → Matrix (Fin 33) (Fin 33) K)
    (h : ∀ m i j, M m i j ≠ 0 ↔ ordered K m j i ≠ 0) : RankGrowth K M := by
  have edge {i j : Fin 33} (e : Edge (ordered K) i j) : Edge M j i := by
    obtain ⟨m,hm⟩ := e
    exact ⟨m,(h m i j).mpr hm⟩
  apply growth_of_matchings K M backward.symm forward.symm
  · intro i
    simpa using edge (backward_edge K (backward.symm i))
  · intro i
    simpa using edge (forward_edge K (forward.symm i))
  · intro i j
    obtain ⟨n,hn⟩ := connected (forward.symm i) (forward.symm j)
    have hsc : Function.Semiconj forward (backward.trans forward.symm) (forward.symm.trans backward) :=
      fun x => by simp
    refine ⟨n, ?_⟩
    simpa using ((hsc.iterate_right n (forward.symm i)).symm.trans (congrArg forward hn))
  · intro m i j j' a b
    rcases lt_trichotomy j j' with lt | eq | gt
    · exact (lt_irrefl i (order_preserving K m j j' i i lt ((h ..).mp a) ((h ..).mp b))).elim
    · exact eq
    · exact (lt_irrefl i (order_preserving K m j' j i i gt ((h ..).mp b) ((h ..).mp a))).elim
  · intro m i i' j j' hii a b
    rcases lt_trichotomy j j' with lt | rfl | gt
    · exact lt
    · exact (hii.ne (column_unique K m j i i' ((h ..).mp a) ((h ..).mp b))).elim
    · exact (hii.not_gt (order_preserving K m j' j i' i gt ((h ..).mp b) ((h ..).mp a))).elim

open CycleQ2FermatVariationAlgebra (lowerExponent)

/-- An upper monomial times a tangent monomial equals the specified lower monomial
when the exponents add in every coordinate. The lower labels use the checked socle basis. -/
def exponentEdge (m : Fin 35) (i j : Fin 33) : Prop :=
  ∀ k, basisMonomial i k + tangentMonomial m k = lowerExponent j.rev k

theorem exponentEdge_iff_complement (m : Fin 35) (i j : Fin 33) :
    exponentEdge m i j ↔ complement m i = some j.rev := by
  rw [complement_spec]
  constructor <;> intro h k <;> specialize h k <;> unfold lowerExponent at * <;>
    have hb := (basis_properties j.rev).2.2 k <;> omega

private theorem ordered_exponent (m : Fin 35) (i j : Fin 33) :
    ordered K m j i ≠ 0 ↔ exponentEdge m i j :=
  (entry_iff K m i j).trans (exponentEdge_iff_complement m i j).symm

/-- Upper-to-lower addition with arbitrary nonzero coefficients on the Fermat edges. -/
theorem weighted_forward_growth (M : Fin 35 → Matrix (Fin 33) (Fin 33) K)
    (h : ∀ m i j, M m j i ≠ 0 ↔ exponentEdge m i j) : RankGrowth K M :=
  weighted_forward K M fun m i j => (h m i j).trans (ordered_exponent K m i j).symm

/-- Lower-to-upper subtraction with arbitrary nonzero coefficients on the reverse edges. -/
theorem weighted_reverse_growth (M : Fin 35 → Matrix (Fin 33) (Fin 33) K)
    (h : ∀ m i j, M m i j ≠ 0 ↔ exponentEdge m i j) : RankGrowth K M :=
  weighted_reverse K M fun m i j => (h m i j).trans (ordered_exponent K m i j).symm

/-- Subtraction in the lower monomial exists precisely on the same Fermat edges. -/
theorem exponentEdge_iff_sub (m : Fin 35) (i j : Fin 33) :
    exponentEdge m i j ↔ ∀ k, tangentMonomial m k ≤ lowerExponent j.rev k ∧
      lowerExponent j.rev k - tangentMonomial m k = basisMonomial i k := by
  constructor <;> intro h k <;> specialize h k <;> omega

/-- A pair of ranks preserved in opposite directions over two fields must be either
zero in both pieces or full in both pieces when both reductions have strict growth. -/
theorem opposite_rank_dichotomy {L : Type*} [Field L]
    {F : Fin 35 → Matrix (Fin 33) (Fin 33) K} {G : Fin 35 → Matrix (Fin 33) (Fin 33) L}
    (hF : RankGrowth K F) (hG : RankGrowth L G)
    (U V : Submodule K (Fin 33 → K)) (U' V' : Submodule L (Fin 33 → L))
    (fu : ∀ m x, x ∈ U → (F m).mulVec x ∈ V)
    (gv : ∀ m x, x ∈ V' → (G m).mulVec x ∈ U')
    (hu : Module.finrank K U = Module.finrank L U')
    (hv : Module.finrank K V = Module.finrank L V') :
    (Module.finrank K U = 0 ∧ Module.finrank K V = 0) ∨
      (Module.finrank K U = 33 ∧ Module.finrank K V = 33) := by
  obtain ⟨huv,hstrict⟩ := hF U V fu
  have hvu := (hG V' U' gv).1
  rw [← hu, ← hv] at hvu
  have bound := Submodule.finrank_le U
  rw [Module.finrank_pi, Fintype.card_fin] at bound
  by_cases hz : Module.finrank K U = 0
  · exact Or.inl ⟨hz, by omega⟩
  · by_contra! contrary
    have mid : Module.finrank K U < 33 := by omega
    have lt := hstrict (Nat.pos_of_ne_zero hz) mid
    omega

section TotalSpace

abbrev Piece := Fin 33 → K
abbrev Total := Piece K × Piece K

abbrev upperProjection (W : Submodule K (Total K)) := W.map (LinearMap.fst K (Piece K) (Piece K))
abbrev lowerProjection (W : Submodule K (Total K)) := W.map (LinearMap.snd K (Piece K) (Piece K))
abbrev upperIntersection (W : Submodule K (Total K)) := W.comap (LinearMap.inl K (Piece K) (Piece K))
abbrev lowerIntersection (W : Submodule K (Total K)) := W.comap (LinearMap.inr K (Piece K) (Piece K))

/-- Ranks of the two coordinate projections followed by the intersections with the two axes. -/
def rankProfile (W : Submodule K (Total K)) : Fin 4 → ℕ :=
  ![Module.finrank K (upperProjection K W), Module.finrank K (lowerProjection K W),
    Module.finrank K (upperIntersection K W), Module.finrank K (lowerIntersection K W)]

private theorem projected_rank_add_intersection (W : Submodule K (Total K))
    (p : Total K →ₗ[K] Piece K) (a : Piece K →ₗ[K] Total K)
    (ha : Function.Injective a) (hk : LinearMap.ker p = LinearMap.range a) :
    Module.finrank K (W.map p) + Module.finrank K (W.comap a) = Module.finrank K W := by
  let pW := p.comp W.subtype
  have hp : LinearMap.range pW = W.map p := by
    dsimp only [pW]
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hs : (LinearMap.ker pW).map W.subtype = (W.comap a).map a := by
    dsimp only [pW]
    rw [LinearMap.ker_comp, Submodule.map_comap_eq, Submodule.map_comap_eq,
      Submodule.range_subtype, hk, inf_comm]
  have hker : Module.finrank K (LinearMap.ker pW) = Module.finrank K (W.comap a) := by
    calc
      _ = Module.finrank K ((LinearMap.ker pW).map W.subtype) :=
        (Submodule.equivMapOfInjective W.subtype W.subtype_injective _).finrank_eq
      _ = Module.finrank K ((W.comap a).map a) := congrArg (fun S : Submodule K (Total K) => Module.finrank K S) hs
      _ = _ := (Submodule.equivMapOfInjective a ha _).finrank_eq.symm
  have h := pW.finrank_range_add_finrank_ker
  rw [hp,hker] at h
  exact h

private theorem upper_rank_decomposition (S : Submodule K (Total K)) :
      Module.finrank K (upperProjection K S) + Module.finrank K (lowerIntersection K S) =
        Module.finrank K S :=
    projected_rank_add_intersection K S _ _ (LinearMap.inr_injective ..) (LinearMap.ker_fst ..)

private theorem lower_rank_decomposition (S : Submodule K (Total K)) :
      Module.finrank K (lowerProjection K S) + Module.finrank K (upperIntersection K S) =
        Module.finrank K S :=
    projected_rank_add_intersection K S _ _ (LinearMap.inl_injective ..) (LinearMap.ker_snd ..)

/-- Stability of total rank and of the two projection ranks suffices to specialize all four
entries of the rank profile, by rank-nullity of each restricted projection. -/
theorem rankProfile_eq_of_projection_ranks {L : Type*} [Field L]
    (W : Submodule K (Total K)) (W' : Submodule L (Total L))
    (hd : Module.finrank K W = Module.finrank L W')
    (hu : Module.finrank K (upperProjection K W) = Module.finrank L (upperProjection L W'))
    (hl : Module.finrank K (lowerProjection K W) = Module.finrank L (lowerProjection L W')) :
    rankProfile K W = rankProfile L W' := by
  have hU := upper_rank_decomposition K W
  have hU' := upper_rank_decomposition L W'
  have hL := lower_rank_decomposition K W
  have hL' := lower_rank_decomposition L W'
  funext i
  fin_cases i
  · exact hu
  · exact hl
  · change Module.finrank K (upperIntersection K W) = Module.finrank L (upperIntersection L W')
    omega
  · change Module.finrank K (lowerIntersection K W) = Module.finrank L (lowerIntersection L W')
    omega

private theorem bot_of_projections (W : Submodule K (Total K))
    (hu : Module.finrank K (upperProjection K W) = 0)
    (hl : Module.finrank K (lowerProjection K W) = 0) : W = ⊥ := by
  have hU := Submodule.finrank_eq_zero.mp hu
  have hL := Submodule.finrank_eq_zero.mp hl
  apply W.eq_bot_iff.mpr
  intro x hx
  have u : x.1 ∈ upperProjection K W := ⟨x,hx,rfl⟩
  have l : x.2 ∈ lowerProjection K W := ⟨x,hx,rfl⟩
  exact Prod.ext (hU ▸ u : x.1 ∈ (⊥ : Submodule K (Piece K)))
    (hL ▸ l : x.2 ∈ (⊥ : Submodule K (Piece K)))

private theorem top_of_intersections (W : Submodule K (Total K))
    (hu : 33 ≤ Module.finrank K (upperIntersection K W))
    (hl : 33 ≤ Module.finrank K (lowerIntersection K W)) : W = ⊤ := by
  have full (A : Submodule K (Piece K)) (h : 33 ≤ Module.finrank K A) : A = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    exact le_antisymm (Submodule.finrank_le A) (by simpa only [Piece, Module.finrank_pi, Fintype.card_fin] using h)
  apply top_unique
  rintro ⟨u,l⟩ _
  have a : u ∈ upperIntersection K W := full _ hu ▸ Submodule.mem_top
  have b : l ∈ lowerIntersection K W := full _ hl ▸ Submodule.mem_top
  change (u,0) ∈ W at a
  change (0,l) ∈ W at b
  simpa using W.add_mem a b

/-- Forward and reverse blocks in two specializations force an arbitrary invariant space to be
zero or full when its two projection ranks and its two axis-intersection ranks specialize equally. -/
theorem nonsplit_dichotomy {L : Type*} [Field L]
    {F : Fin 35 → Matrix (Fin 33) (Fin 33) K} {G : Fin 35 → Matrix (Fin 33) (Fin 33) L}
    (hF : RankGrowth K F) (hG : RankGrowth L G)
    (W : Submodule K (Total K)) (W' : Submodule L (Total L))
    (forward_stable : ∀ m x, x ∈ W → (0,(F m).mulVec x.1) ∈ W)
    (reverse_stable : ∀ m x, x ∈ W' → ((G m).mulVec x.2,0) ∈ W')
    (hr : rankProfile K W = rankProfile L W') :
    (W = ⊥ ∧ W' = ⊥) ∨ (W = ⊤ ∧ W' = ⊤) := by
  have pU : Module.finrank K (upperProjection K W) = Module.finrank L (upperProjection L W') :=
    congrFun hr 0
  have pL : Module.finrank K (lowerProjection K W) = Module.finrank L (lowerProjection L W') :=
    congrFun hr 1
  have iU : Module.finrank K (upperIntersection K W) = Module.finrank L (upperIntersection L W') :=
    congrFun hr 2
  have iL : Module.finrank K (lowerIntersection K W) = Module.finrank L (lowerIntersection L W') :=
    congrFun hr 3
  have f : ∀ m x, x ∈ upperProjection K W → (F m).mulVec x ∈ lowerIntersection K W := by
    rintro m _ ⟨x,hx,rfl⟩
    exact forward_stable m x hx
  have g : ∀ m x, x ∈ lowerProjection L W' → (G m).mulVec x ∈ upperIntersection L W' := by
    rintro m _ ⟨x,hx,rfl⟩
    exact reverse_stable m x hx
  have toLower : lowerIntersection K W ≤ lowerProjection K W := fun x hx => ⟨(0,x),hx,rfl⟩
  have toUpper : upperIntersection L W' ≤ upperProjection L W' := fun x hx => ⟨(x,0),hx,rfl⟩
  obtain (hz | hf) := opposite_rank_dichotomy K hF hG _ _ _ _
    (fun m x hx => toLower (f m x hx)) (fun m x hx => toUpper (g m x hx)) pU pL
  · exact Or.inl ⟨bot_of_projections K W hz.1 hz.2,
      bot_of_projections L W' (pU.symm.trans hz.1) (pL.symm.trans hz.2)⟩
  · have lfull := (hF _ _ f).1
    have ufull := (hG _ _ g).1
    rw [hf.1] at lfull
    rw [← pL,hf.2] at ufull
    exact Or.inr ⟨top_of_intersections K W (iU.symm ▸ ufull) lfull,
      top_of_intersections L W' ufull (iL ▸ lfull)⟩

end TotalSpace

theorem strict_growth (W V : Submodule K (Fin 33 → K))
    (hmap : ∀ (m : Fin 35) (x : Fin 33 → K), x ∈ W → (ordered K m).mulVec x ∈ V)
    (hpos : 0 < Module.finrank K W) (hproper : Module.finrank K W < 33) :
    Module.finrank K W < Module.finrank K V :=
  ((weighted_forward K (ordered K) (fun _ _ _ => Iff.rfl)) W V hmap).2 hpos hproper

/-- The images of the full upper space span all lower coordinates. -/
theorem full_span (V : Submodule K (Fin 33 → K))
    (hmap : ∀ (m : Fin 35) (x : Fin 33 → K), (ordered K m).mulVec x ∈ V) : V = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  have h := ((weighted_forward K (ordered K) (fun _ _ _ => Iff.rfl))
    ⊤ V (fun m x _ => hmap m x)).1
  rw [finrank_top] at h
  exact le_antisymm (Submodule.finrank_le V) h

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

#print axioms CycleQ2FermatStrictGrowth.weighted_forward_growth
#print axioms CycleQ2FermatStrictGrowth.weighted_reverse_growth
#print axioms CycleQ2FermatStrictGrowth.opposite_rank_dichotomy
#print axioms CycleQ2FermatStrictGrowth.nonsplit_dichotomy
#print axioms CycleQ2FermatStrictGrowth.rankProfile_eq_of_projection_ranks
