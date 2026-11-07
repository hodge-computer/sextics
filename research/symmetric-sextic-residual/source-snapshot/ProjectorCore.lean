import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Submodule.Ker

/-!
# The linear-algebra core of the monodromy argument in PR 218, §3B.5

This file proves an abstract irreducibility criterion. It does not assert that
any geometric family satisfies its hypotheses, or construct a Hodge cycle.
The named maps encode transport between vanishing-cycle directions; their
invariance and the spanning and nondegeneracy hypotheses are explicit.
-/

namespace WeightedSexticMonodromy

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A nonzero vector pairs nontrivially with at least one member of any
spanning family, provided the pairing has zero left radical. -/
theorem exists_pairing_ne_zero_of_span_eq_top
    (B : V →ₗ[K] V →ₗ[K] K)
    (hB : ∀ v, (∀ x, B v x = 0) → v = 0)
    (w : I → V) (hspan : Submodule.span K (Set.range w) = ⊤)
    {v : V} (hv : v ≠ 0) : ∃ i, B v (w i) ≠ 0 := by
  classical
  by_contra h
  have hzero : ∀ i, B v (w i) = 0 := by
    intro i
    by_contra hi
    exact h ⟨i, hi⟩
  have hker : Submodule.span K (Set.range w) ≤ LinearMap.ker (B v) := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact LinearMap.mem_ker.mpr (hzero i)
  apply hv
  apply hB v
  intro x
  apply LinearMap.mem_ker.mp
  apply hker
  rw [hspan]
  trivial

/-- If a submodule contains a vector and its nontrivial transvection, it
contains the transvection direction. -/
theorem direction_mem_of_transvection
    (U : Submodule K V) {v w : V} {c : K}
    (hv : v ∈ U) (ht : v + c • w ∈ U) (hc : c ≠ 0) : w ∈ U := by
  apply (U.smul_mem_iff hc).mp
  have h := U.sub_mem ht hv
  simpa only [add_sub_cancel_left] using h

/-- A nondegenerate pairing, spanning directions, stable nontrivial
transvections, and transports between every pair of directions imply
irreducibility. No geometry or algebraic-cycle existence is assumed here. -/
theorem invariant_submodule_eq_bot_or_top
    (B : V →ₗ[K] V →ₗ[K] K)
    (hB : ∀ v, (∀ x, B v x = 0) → v = 0)
    (w : I → V) (hspan : Submodule.span K (Set.range w) = ⊤)
    (c : I → K) (hc : ∀ i, c i ≠ 0)
    (g : I → I → V →ₗ[K] V) (a : I → I → K)
    (ha : ∀ i j, a i j ≠ 0)
    (hg : ∀ i j, g i j (w i) = a i j • w j)
    (U : Submodule K V)
    (htrans : ∀ i v, v ∈ U → v + (c i * B v (w i)) • w i ∈ U)
    (hstable : ∀ i j v, v ∈ U → g i j v ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  classical
  by_cases hU : U = ⊥
  · exact Or.inl hU
  right
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  obtain ⟨i, hi⟩ := exists_pairing_ne_zero_of_span_eq_top B hB w hspan hv0
  have hwi : w i ∈ U :=
    direction_mem_of_transvection U hv (htrans i v hv) (mul_ne_zero (hc i) hi)
  have hwj : ∀ j, w j ∈ U := by
    intro j
    apply (U.smul_mem_iff (ha i j)).mp
    rw [← hg i j]
    exact hstable i j (w i) hwi
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro x ⟨j, rfl⟩
  exact hwj j

#print axioms exists_pairing_ne_zero_of_span_eq_top
#print axioms direction_mem_of_transvection
#print axioms invariant_submodule_eq_bot_or_top

end WeightedSexticMonodromy
