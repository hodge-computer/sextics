import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Algebra.Module.NatInt
import Mathlib.Tactic.NormNum

/-!
# Integral primitive multiples without a torsion-freeness assumption

This is the integral-coefficient step in the Diamond surface-section
argument. Rationalization is the actual tensor product with the rationals.
An element killed by this map is killed by a positive integer. Applied to
the integral Gysin image, this supplies a positive multiple of the orbit
class E - 2H lying in the integral Gysin kernel.

The same multiple preserves every nonzero additive observable with values
in a rational vector space, and preserves fixed-point conditions. Thus the
torsion-clearing operation cannot destroy the characteristic-zero trace
nonvanishing used in the moving-class argument.

This file does not construct geometric cohomology, a Gysin map, or an
Abel--Jacobi map. Their concrete instantiation remains a separate
obligation. The algebraic torsion-clearing conclusion is proved from
module localization, without assuming integral cohomology torsion-free.

The geometric strategy is due to Ben Diamond and the cited work of Claire
Voisin. This formalization was prepared for fqlx with ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2IntegralPrimitive

open scoped TensorProduct nonZeroDivisors

abbrev Rationalized (M : Type*) [AddCommGroup M] :=
  ℚ ⊗[ℤ] M

/-- The canonical map to the actual rational tensor product. -/
def rationalize (M : Type*) [AddCommGroup M] : M →ₗ[ℤ] Rationalized M :=
  TensorProduct.mk ℤ ℚ M 1

@[simp] theorem rationalize_apply {M : Type*} [AddCommGroup M] (x : M) :
    rationalize M x = (1 : ℚ) ⊗ₜ[ℤ] x := rfl

/-- The kernel of rationalization consists exactly of elements annihilated
by a positive integer. No finite-generation hypothesis is needed. -/
theorem rationalize_eq_zero_iff {M : Type*} [AddCommGroup M] (x : M) :
    rationalize M x = 0 ↔ ∃ n : ℕ, 0 < n ∧ n • x = 0 := by
  have hloc :
      rationalize M x = 0 ↔ ∃ c : nonZeroDivisors ℤ, c • x = 0 :=
    IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ)
      (TensorProduct.mk ℤ ℚ M 1)
  constructor
  · intro hx
    obtain ⟨c, hc⟩ := hloc.mp hx
    refine ⟨(c : ℤ).natAbs,
      Int.natAbs_pos.mpr (nonZeroDivisors.coe_ne_zero c), ?_⟩
    change (c : ℤ) • x = 0 at hc
    exact natAbs_nsmul_eq_zero.mpr hc
  · rintro ⟨n, hn, hx⟩
    apply hloc.mpr
    refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))⟩, ?_⟩
    change (n : ℤ) • x = 0
    simpa only [natCast_zsmul] using hx

section Kernel

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- A rationally trivial integral image becomes integrally trivial after
multiplying the source class by a positive integer. -/
theorem exists_positive_kernel_multiple (f : A →+ B) (x : A)
    (hx : rationalize B (f x) = 0) :
    ∃ n : ℕ, 0 < n ∧ f (n • x) = 0 := by
  obtain ⟨n, hn, hzero⟩ := (rationalize_eq_zero_iff (f x)).mp hx
  exact ⟨n, hn, by simpa only [map_nsmul] using hzero⟩

/-- The numerical Gysin identities for the orbit sum and hyperplane
produce an integral primitive multiple of E - 2H. -/
theorem exists_primitive_orbit_multiple (gysin : A →+ B) (E H : A)
    (q : Rationalized B)
    (hE : rationalize B (gysin E) = 6 • q)
    (hH : rationalize B (gysin H) = 3 • q) :
    ∃ n : ℕ, 0 < n ∧ gysin (n • (E - 2 • H)) = 0 := by
  apply exists_positive_kernel_multiple gysin (E - 2 • H)
  rw [map_sub, map_nsmul, map_sub, map_nsmul, hE, hH, smul_smul]
  norm_num

/-- Positive multiples preserve invariance under any additive action. -/
theorem multiple_fixed_of_fixed (e : A →+ A) (x : A)
    (hx : e x = x) (n : ℕ) : e (n • x) = n • x := by
  rw [map_nsmul, hx]

end Kernel

section Observables

variable {A B V : Type*} [AddCommGroup A] [AddCommGroup B]
variable [AddCommGroup V] [Module ℚ V]

/-- A nonzero characteristic-zero additive observable remains nonzero
after the positive integral rescaling used to clear Gysin torsion. -/
theorem observable_positive_multiple_ne_zero (φ : A →+ V) (x : A)
    (hφ : φ x ≠ 0) (n : ℕ) (hn : 0 < n) :
    φ (n • x) ≠ 0 := by
  rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ]
  exact smul_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)) hφ

/-- One positive multiple lies in the integral kernel and retains the
specified nonzero trace or derivative value. -/
theorem exists_kernel_multiple_with_nonzero_observable
    (f : A →+ B) (φ : A →+ V) (x : A)
    (hx : rationalize B (f x) = 0) (hφ : φ x ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ f (n • x) = 0 ∧ φ (n • x) ≠ 0 := by
  obtain ⟨n, hn, hf⟩ := exists_positive_kernel_multiple f x hx
  exact ⟨n, hn, hf, observable_positive_multiple_ne_zero φ x hφ n hn⟩

/-- The primitive orbit class can be chosen while preserving a nonzero
characteristic-zero pairing. All rational Gysin data remain explicit. -/
theorem exists_primitive_orbit_with_nonzero_observable
    (gysin : A →+ B) (φ : A →+ V) (E H : A) (q : Rationalized B)
    (hE : rationalize B (gysin E) = 6 • q)
    (hH : rationalize B (gysin H) = 3 • q)
    (hφ : φ (E - 2 • H) ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ gysin (n • (E - 2 • H)) = 0 ∧
      φ (n • (E - 2 • H)) ≠ 0 := by
  obtain ⟨n, hn, hg⟩ := exists_primitive_orbit_multiple gysin E H q hE hH
  exact ⟨n, hn, hg, observable_positive_multiple_ne_zero φ _ hφ n hn⟩

end Observables

#print axioms rationalize_eq_zero_iff
#print axioms exists_primitive_orbit_with_nonzero_observable

end CycleQ2IntegralPrimitive

end
