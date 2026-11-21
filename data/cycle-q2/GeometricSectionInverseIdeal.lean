import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Inverting a unimodular functional on an actual ideal

An R-linear map from an ideal to R that takes some ideal element to one
is injective, and that element is unique. A finite Bezout identity on
actual generators constructs it. Under a unit-twisted comparison the
inverse transforms with the negative exponent.

Source-only draft, 15 November 2026. Not elaborated or kernel-replayed.
No geometric nonemptiness or protected residue exactness is asserted by
this generic algebra file. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2SectionInverseIdeal

variable {R : Type*} [CommRing R]

/-- The ideal inclusion, not an arbitrary rank-one module, gives balance. -/
theorem balanced (I : Ideal R) (φ : I →ₗ[R] R) (a b : I) :
    (a : R) * φ b = (b : R) * φ a := by
  have hab : (a : R) • b = (b : R) • a := by
    apply Subtype.ext
    change (a : R) * (b : R) = (b : R) * (a : R)
    exact mul_comm _ _
  calc
    (a : R) * φ b = φ ((a : R) • b) := by rw [map_smul, smul_eq_mul]
    _ = φ ((b : R) • a) := congrArg φ hab
    _ = (b : R) * φ a := by rw [map_smul, smul_eq_mul]

/-- A value-one element reconstructs every element of the ideal. -/
theorem recover (I : Ideal R) (φ : I →ₗ[R] R) (a : I)
    (ha : φ a = 1) (b : I) : φ b • a = b := by
  apply Subtype.ext
  change φ b * (a : R) = (b : R)
  calc
    φ b * (a : R) = (a : R) * φ b := mul_comm _ _
    _ = (b : R) * φ a := balanced I φ a b
    _ = (b : R) := by rw [ha, mul_one]

theorem inverse_unique (I : Ideal R) (φ : I →ₗ[R] R)
    (a b : I) (ha : φ a = 1) (hb : φ b = 1) : a = b := by
  simpa only [hb, one_smul] using recover I φ a ha b

theorem functional_injective (I : Ideal R) (φ : I →ₗ[R] R)
    (a : I) (ha : φ a = 1) : Function.Injective φ := by
  intro b c hbc
  calc
    b = φ b • a := (recover I φ a ha b).symm
    _ = φ c • a := congrArg (fun r : R => r • a) hbc
    _ = c := recover I φ a ha c

section Finite

variable {ι : Type*} [Fintype ι]

/-- The inverse is an explicit finite combination in the original ideal. -/
def bezoutElement (I : Ideal R) (l : ι → I) (c : ι → R) : I :=
  ∑ j, c j • l j

theorem bezoutElement_eval (I : Ideal R) (φ : I →ₗ[R] R)
    (l : ι → I) (c : ι → R) :
    φ (bezoutElement I l c) = ∑ j, c j * φ (l j) := by
  simp only [bezoutElement, map_sum, map_smul, smul_eq_mul]

theorem exists_unique_inverse_of_bezout (I : Ideal R) (φ : I →ₗ[R] R)
    (l : ι → I) (c : ι → R) (h : (∑ j, c j * φ (l j)) = 1) :
    ∃! a : I, φ a = 1 := by
  have ha : φ (bezoutElement I l c) = 1 :=
    (bezoutElement_eval I φ l c).trans h
  refine ⟨bezoutElement I l c, ha, ?_⟩
  intro b hb
  exact inverse_unique I φ b (bezoutElement I l c) hb ha

end Finite

/-- Positive degree n for the functional gives negative degree n for
its uniquely constructed inverse. No domain assumption is required. -/
theorem inverse_rescales_of_equiv
    (I J : Ideal R) (e : I ≃ₗ[R] J)
    (φ : I →ₗ[R] R) (ψ : J →ₗ[R] R) (u : Rˣ) (n : ℕ)
    (hchange : ∀ b : J, ψ b = (u : R) ^ n * φ (e.symm b))
    (a : I) (b : J) (ha : φ a = 1) (hb : ψ b = 1) :
    b = (((u⁻¹ : Rˣ) : R) ^ n) • e a := by
  have hc : ψ ((((u⁻¹ : Rˣ) : R) ^ n) • e a) = 1 := by
    calc
      ψ ((((u⁻¹ : Rˣ) : R) ^ n) • e a) =
          (u : R) ^ n * φ (e.symm ((((u⁻¹ : Rˣ) : R) ^ n) • e a)) := hchange _
      _ = (u : R) ^ n * ((((u⁻¹ : Rˣ) : R) ^ n) * 1) := by
        rw [map_smul, LinearEquiv.symm_apply_apply, map_smul, ha, smul_eq_mul]
      _ = 1 := by
        rw [mul_one, ← mul_pow, Units.mul_inv, one_pow]
  exact inverse_unique J ψ b _ hb hc

end CycleQ2SectionInverseIdeal

end

#print axioms CycleQ2SectionInverseIdeal.recover
#print axioms CycleQ2SectionInverseIdeal.exists_unique_inverse_of_bezout
#print axioms CycleQ2SectionInverseIdeal.inverse_rescales_of_equiv
