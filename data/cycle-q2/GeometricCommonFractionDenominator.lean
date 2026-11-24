import Mathlib.RingTheory.Localization.FractionRing

/-!
# A single denominator for finitely many coefficients in the function field

This is the elementary localization step needed before spreading the
primitive polynomial and a finite collection of parameter coordinates
from the generic fiber of the cycle-q2 pencil to a nonempty principal open.
For a finite set of fractions, the proof constructs one nonzero denominator
and numerators in the original domain, using only the actual fraction ring.

It does not assert that the resulting finite algebra is etale, that the
original parameter point extends to the Hilbert scheme, or that the
protected residue is exact. Those geometric steps remain separate.
-/

set_option autoImplicit false

noncomputable section

open scoped nonZeroDivisors

namespace CycleQ2CommonFractionDenominator

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Every fraction has a numerator and a nonzero denominator from R. -/
theorem exists_numerator_denominator (z : FractionRing R) :
    ∃ a b : R, b ≠ 0 ∧
      z * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a := by
  obtain ⟨a, ⟨b, hb⟩, rfl⟩ := IsLocalization.exists_mk'_eq R⁰ z
  refine ⟨a, b, (mem_nonZeroDivisors_iff_ne_zero).mp hb, ?_⟩
  exact IsLocalization.mk'_spec (FractionRing R) a (⟨b, hb⟩ : R⁰)

/-- Clear all fractions indexed by an arbitrary *finite set*, not just
by a fixed finite type. The same nonzero denominator works for all. -/
theorem exists_finset_common_denominator {ι : Type*}
    (f : ι → FractionRing R) (s : Finset ι) :
    ∃ b : R, b ≠ 0 ∧
      ∀ i ∈ s, ∃ a : R,
        f i * algebraMap R (FractionRing R) b =
          algebraMap R (FractionRing R) a := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨1, one_ne_zero, ?_⟩
      simp
  | @insert i s hi ih =>
      obtain ⟨b, hb, hs⟩ := ih
      obtain ⟨a, c, hc, hac⟩ := exists_numerator_denominator (f i)
      refine ⟨b * c, mul_ne_zero hb hc, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hji | hjs
      · subst j
        refine ⟨a * b, ?_⟩
        calc
          f i * algebraMap R (FractionRing R) (b * c) =
              (f i * algebraMap R (FractionRing R) c) *
                algebraMap R (FractionRing R) b := by
                  rw [map_mul]
                  ac_rfl
          _ = algebraMap R (FractionRing R) a *
                algebraMap R (FractionRing R) b := by rw [hac]
          _ = algebraMap R (FractionRing R) (a * b) := by rw [map_mul]
      · obtain ⟨d, hd⟩ := hs j hjs
        refine ⟨d * c, ?_⟩
        calc
          f j * algebraMap R (FractionRing R) (b * c) =
              (f j * algebraMap R (FractionRing R) b) *
                algebraMap R (FractionRing R) c := by
                  rw [map_mul, mul_assoc]
          _ = algebraMap R (FractionRing R) d *
                algebraMap R (FractionRing R) c := by rw [hd]
          _ = algebraMap R (FractionRing R) (d * c) := by rw [map_mul]

/-- A single denominator for all coefficients of any finite family. -/
theorem exists_common_denominator {ι : Type*} [Fintype ι]
    (f : ι → FractionRing R) :
    ∃ b : R, b ≠ 0 ∧
      ∀ i : ι, ∃ a : R,
        f i * algebraMap R (FractionRing R) b =
          algebraMap R (FractionRing R) a := by
  obtain ⟨b, hb, h⟩ := exists_finset_common_denominator f Finset.univ
  exact ⟨b, hb, fun i => h i (Finset.mem_univ i)⟩

end CycleQ2CommonFractionDenominator

end

#print axioms CycleQ2CommonFractionDenominator.exists_numerator_denominator
#print axioms CycleQ2CommonFractionDenominator.exists_finset_common_denominator
#print axioms CycleQ2CommonFractionDenominator.exists_common_denominator
