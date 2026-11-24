import Mathlib.LinearAlgebra.Charpoly.Basic

/-!
# The polarized-kernel argument for an algebraic correspondence

The written cycle-q2 argument uses a transpose correspondence for *alternating*
Poincare pairings, not a positive-definite Hilbert-space adjoint. Positivity is
not needed: if A is surjective and the kernel pairing is nondegenerate, then
A followed by its pairing-adjoint is injective.

The actual polarized Hodge structures, the geometric transpose correspondence,
and its kernel-nondegeneracy property remain separate construction obligations.
This module constructs no geometric projector and asserts no residue vanishing.
-/

set_option autoImplicit false

noncomputable section

namespace CycleQ2PolarizedKernelAdjoint

variable {K E V : Type*} [Field K]
variable [AddCommGroup E] [Module K E]
variable [AddCommGroup V] [Module K V]

/-- The target pairing separates vectors in its first argument. -/
def TargetNondegenerate (BV : V →ₗ[K] V →ₗ[K] K) : Prop :=
  ∀ v : V, (∀ w : V, BV v w = 0) → v = 0

/-- Nondegeneracy of the pairing *restricted to the kernel* of the
surjective correspondence. This is not automatic from nondegeneracy on E. -/
def KernelNondegenerate
    (BE : E →ₗ[K] E →ₗ[K] K) (A : E →ₗ[K] V) : Prop :=
  ∀ e : E, A e = 0 →
    (∀ k : E, A k = 0 → BE e k = 0) → e = 0

/-- The transpose identity with the actual bilinear pairings.
It applies equally to alternating/symplectic pairings. -/
def TransposeCompatible
    (BE : E →ₗ[K] E →ₗ[K] K)
    (BV : V →ₗ[K] V →ₗ[K] K)
    (A : E →ₗ[K] V) (At : V →ₗ[K] E) : Prop :=
  ∀ v : V, ∀ e : E, BE (At v) e = BV v (A e)

/-- The Poincare-pairing proof that a surjective correspondence followed
by its transpose is injective, with no positivity or extra scalar sign. -/
theorem composite_injective
    (BE : E →ₗ[K] E →ₗ[K] K)
    (BV : V →ₗ[K] V →ₗ[K] K)
    (A : E →ₗ[K] V) (At : V →ₗ[K] E)
    (hA : Function.Surjective A)
    (hKer : KernelNondegenerate BE A)
    (hV : TargetNondegenerate BV)
    (hAt : TransposeCompatible BE BV A At) :
    Function.Injective (A.comp At) := by
  have hz (v : V) (hv : A (At v) = 0) : v = 0 := by
    have ht : At v = 0 := by
      apply hKer (At v) hv
      intro k hk
      calc
        BE (At v) k = BV v (A k) := hAt v k
        _ = 0 := by rw [hk, map_zero]
    apply hV v
    intro w
    obtain ⟨e, rfl⟩ := hA w
    calc
      BV v (A e) = BE (At v) e := (hAt v e).symm
      _ = 0 := by simp [ht]
  intro v w h
  change A (At v) = A (At w) at h
  apply sub_eq_zero.mp
  apply hz (v - w)
  calc
    A (At (v - w)) = A (At v - At w) := by rw [map_sub]
    _ = A (At v) - A (At w) := by rw [map_sub]
    _ = 0 := sub_eq_zero.mpr h

/-- In finite dimension the geometric transpose composite is a unit. -/
theorem composite_isUnit [FiniteDimensional K V]
    (BE : E →ₗ[K] E →ₗ[K] K)
    (BV : V →ₗ[K] V →ₗ[K] K)
    (A : E →ₗ[K] V) (At : V →ₗ[K] E)
    (hA : Function.Surjective A)
    (hKer : KernelNondegenerate BE A)
    (hV : TargetNondegenerate BV)
    (hAt : TransposeCompatible BE BV A At) :
    IsUnit (A.comp At) := by
  apply (LinearMap.isUnit_iff_ker_eq_bot (A.comp At)).mpr
  exact LinearMap.ker_eq_bot.mpr
    (composite_injective BE BV A At hA hKer hV hAt)

/-- The nonzero constant term required by the rational projector polynomial
is a consequence of the nondegenerate-kernel argument, not an axiom. -/
theorem minpoly_coeff_zero_ne [FiniteDimensional K V]
    (BE : E →ₗ[K] E →ₗ[K] K)
    (BV : V →ₗ[K] V →ₗ[K] K)
    (A : E →ₗ[K] V) (At : V →ₗ[K] E)
    (hA : Function.Surjective A)
    (hKer : KernelNondegenerate BE A)
    (hV : TargetNondegenerate BV)
    (hAt : TransposeCompatible BE BV A At) :
    (minpoly K (A.comp At)).coeff 0 ≠ 0 :=
  LinearMap.minpoly_coeff_zero_of_injective
    (composite_injective BE BV A At hA hKer hV hAt)

end CycleQ2PolarizedKernelAdjoint

end

#print axioms CycleQ2PolarizedKernelAdjoint.composite_injective
#print axioms CycleQ2PolarizedKernelAdjoint.minpoly_coeff_zero_ne
