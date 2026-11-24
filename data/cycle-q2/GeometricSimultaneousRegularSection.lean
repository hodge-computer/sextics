import Mathlib.GroupTheory.CosetCover
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# A simultaneous regular constant section on finitely many pivot charts

Source-only draft against pinned Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`.
No elaboration or kernel replay has been run.

The proof avoids the finitely many inverse images of associated primes
in the coefficient vector space. The zero subspace is included among
the forbidden subspaces, so the vector is nonzero even when some or all
of the chart rings are trivial.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2SimultaneousRegularSection

universe u v w

variable {k : Type u} [Field k]

/-- Constant coefficients act on the selected three chart sections. -/
def coefficientCombination {A : Type w} [CommRing A] [Algebra k A]
    (c : Fin 3 → A) : (Fin 3 → k) →ₗ[k] A where
  toFun t := ∑ j, t j • c j
  map_add' t u := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a t := by
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul,
      Finset.smul_sum, smul_smul]

@[simp] theorem coefficientCombination_single {A : Type w}
    [CommRing A] [Algebra k A] (c : Fin 3 → A) (j : Fin 3) :
    coefficientCombination c (Pi.single j (1 : k)) = c j := by
  simp [coefficientCombination, Pi.single_apply]

/-- A single nonzero constant vector makes every coefficient sum
regular on a finite family of Noetherian chart rings. Each chart has
one unit coefficient, but the unit's position may vary between charts.
No nontriviality assumption is imposed on a chart ring. -/
theorem exists_nonzero_simultaneous_regular [Infinite k]
    {ι : Type v} [Finite ι] (R : ι → Type w)
    [∀ i, CommRing (R i)] [∀ i, Algebra k (R i)]
    [∀ i, IsNoetherianRing (R i)] (c : ∀ i, Fin 3 → R i)
    (hunit : ∀ i, ∃ j, IsUnit (c i j)) :
    ∃ t : Fin 3 → k, t ≠ 0 ∧
      ∀ i, IsSMulRegular (R i) (∑ j, t j • c i j) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  letI : ∀ i, Fintype (associatedPrimes (R i) (R i)) :=
    fun i => (associatedPrimes.finite (R i) (R i)).fintype
  let Index := Σ i : ι, associatedPrimes (R i) (R i)
  let bad : Option Index → Subspace k (Fin 3 → k) := fun a =>
    match a with
    | none => ⊥
    | some a =>
      (a.2.val.restrictScalars k).comap (coefficientCombination (c a.1))
  have hbad (a : Option Index) : bad a ≠ ⊤ := by
    cases a with
    | none =>
      exact bot_ne_top
    | some a =>
      intro htop
      obtain ⟨j, hj⟩ := hunit a.1
      have hm : Pi.single j (1 : k) ∈ bad (some a) := by
        rw [htop]
        exact Submodule.mem_top
      change coefficientCombination (c a.1) (Pi.single j (1 : k)) ∈ a.2.val at hm
      rw [coefficientCombination_single] at hm
      exact a.2.property.isPrime.ne_top (a.2.val.eq_top_of_isUnit_mem hm hj)
  have hcover : (⋃ a, (bad a : Set (Fin 3 → k))) ≠ Set.univ := by
    intro h
    obtain ⟨a, ha⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ h
    exact hbad a ha
  obtain ⟨t, ht⟩ : ∃ t : Fin 3 → k, t ∉ ⋃ a, (bad a : Set (Fin 3 → k)) := by
    by_contra! h
    exact hcover (Set.eq_univ_of_forall h)
  refine ⟨t, ?_, ?_⟩
  · intro hz
    apply ht
    refine Set.mem_iUnion.mpr ⟨none, ?_⟩
    change t ∈ (⊥ : Submodule k (Fin 3 → k))
    rw [hz]
    exact Submodule.zero_mem _
  · intro i
    by_contra hreg
    have hm : (∑ j, t j • c i j) ∈
        ⋃ p ∈ associatedPrimes (R i) (R i), (p : Set (R i)) := by
      rw [biUnion_associatedPrimes_eq_compl_regular (R i) (R i)]
      exact hreg
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hm
    obtain ⟨hp, hmem⟩ := Set.mem_iUnion.mp hp
    apply ht
    refine Set.mem_iUnion.mpr ⟨some ⟨i, ⟨p, hp⟩⟩, ?_⟩
    exact hmem

#print axioms exists_nonzero_simultaneous_regular

end CycleQ2SimultaneousRegularSection
end
