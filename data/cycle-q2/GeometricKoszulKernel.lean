import Mathlib.Algebra.Regular.SMul
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Ring

/-!
# The simple-pole Koszul boundary for a regular pair

This module proves the algebraic exactness needed by the two-open Koszul
comparison. The ambient quotient uses the actual localization rings and all
their sections, so its boundaries have no imposed bound on pole order.

The hypotheses say precisely that `f` is regular on `R` and `g` is regular
modulo `f`. No equality of a kernel or cohomology class is assumed. This
module makes no identification with a canonical bundle or a Serre trace.
-/

set_option autoImplicit false

noncomputable section

namespace CycleQ2GeometricKoszulKernel

variable {R : Type*} [CommRing R]

/-- Regularity modulo `f` cancels every power of `g` in divisibility by `f`. -/
theorem dvd_of_pow_mul_dvd (f g : R)
    (hg : IsSMulRegular (R ⧸ Ideal.span {f}) g)
    (m : ℕ) (a : R) (h : f ∣ g ^ m * a) : f ∣ a := by
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply (IsSMulRegular.pow m hg).right_eq_zero_of_smul
  change Ideal.Quotient.mk (Ideal.span {f}) (g ^ m * a) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr h)

/-- The all-poles cancellation underlying injectivity of the simple-pole
boundary. This is proved from regularity, not supplied as a colon-ideal
hypothesis. -/
theorem cancel_powers (f g : R) (hf : IsSMulRegular R f)
    (hg : IsSMulRegular (R ⧸ Ideal.span {f}) g)
    (n m : ℕ) (p a b : R)
    (h : p * f ^ n * g ^ m = f ^ (n + 1) * a + g ^ (m + 1) * b) :
    p ∈ Ideal.span ({f, g} : Set R) := by
  induction n generalizing a b with
  | zero =>
      have hd : f ∣ g ^ m * (p - g * b) := by
        refine ⟨a, ?_⟩
        calc
          g ^ m * (p - g * b) = p * f ^ 0 * g ^ m - g ^ (m + 1) * b := by
            simp only [pow_zero, mul_one, pow_succ]
            ring
          _ = f * a := by rw [h]; simp
      obtain ⟨c, hc⟩ := dvd_of_pow_mul_dvd f g hg m (p - g * b) hd
      apply Ideal.mem_span_pair.mpr
      refine ⟨c, b, ?_⟩
      calc
        c * f + b * g = (p - g * b) + g * b := by rw [hc]; ring
        _ = p := sub_add_cancel _ _
  | succ n ih =>
      have hd : f ∣ g ^ (m + 1) * b := by
        refine ⟨p * f ^ n * g ^ m - f ^ (n + 1) * a, ?_⟩
        symm
        calc
          f * (p * f ^ n * g ^ m - f ^ (n + 1) * a) =
              p * f ^ (n + 1) * g ^ m - f ^ (n + 1 + 1) * a := by
            simp only [pow_succ]
            ring
          _ = g ^ (m + 1) * b := by rw [h]; ring
      obtain ⟨b', hb'⟩ := dvd_of_pow_mul_dvd f g hg (m + 1) b hd
      apply ih a b'
      apply hf
      change f * (p * f ^ n * g ^ m) =
        f * (f ^ (n + 1) * a + g ^ (m + 1) * b')
      calc
        f * (p * f ^ n * g ^ m) = p * f ^ (n + 1) * g ^ m := by
          rw [pow_succ]
          ring
        _ = f ^ (n + 1 + 1) * a + g ^ (m + 1) * b := h
        _ = f * (f ^ (n + 1) * a + g ^ (m + 1) * b') := by
          rw [hb', pow_succ]
          ring

/-- The actual ring on the overlap of the two principal opens. -/
abbrev Overlap (f g : R) := Localization.Away (f * g)

def firstRestriction (f g : R) : Localization.Away f →ₐ[R] Overlap f g where
  toRingHom := IsLocalization.Away.awayToAwayRight f g
  commutes' := IsLocalization.Away.awayToAwayRight_eq f g

def secondRestriction (f g : R) : Localization.Away g →ₐ[R] Overlap f g where
  toRingHom := IsLocalization.Away.awayToAwayLeft g f
  commutes' := IsLocalization.Away.awayToAwayLeft_eq g f

/-- Boundaries from arbitrary sections of the two genuine localization rings. -/
def boundaries (f g : R) : Submodule R (Overlap f g) :=
  LinearMap.range (firstRestriction f g).toLinearMap ⊔
    LinearMap.range (secondRestriction f g).toLinearMap

abbrev Cech (f g : R) := Overlap f g ⧸ boundaries f g

def denominator (f g : R) : Submonoid.powers (f * g) :=
  ⟨f * g, 1, pow_one _⟩

/-- The literal fraction `p/(f*g)`, as an `R`-linear map. -/
def representative (f g : R) : R →ₗ[R] Overlap f g where
  toFun p := IsLocalization.mk' (Overlap f g) p (denominator f g)
  map_add' p q := by
    rw [IsLocalization.mk'_eq_mul_mk'_one (p + q) (denominator f g),
      IsLocalization.mk'_eq_mul_mk'_one p (denominator f g),
      IsLocalization.mk'_eq_mul_mk'_one q (denominator f g), map_add, add_mul]
  map_smul' a p := by
    exact (IsLocalization.smul_mk' a p (denominator f g)).symm

/-- The actual simple-pole boundary into the localization Cech quotient. -/
def boundary (f g : R) : R →ₗ[R] Cech f g :=
  (boundaries f g).mkQ.comp (representative f g)

@[simp] theorem representative_spec (f g p : R) :
    representative f g p * algebraMap R (Overlap f g) (f * g) =
      algebraMap R (Overlap f g) p :=
  IsLocalization.mk'_spec (Overlap f g) p (denominator f g)

theorem representative_first (f g : R) :
    representative f g f =
      secondRestriction f g (IsLocalization.Away.invSelf g) := by
  symm
  change secondRestriction f g (IsLocalization.Away.invSelf g) =
    IsLocalization.mk' (Overlap f g) f (denominator f g)
  rw [IsLocalization.eq_mk'_iff_mul_eq]
  have hi : algebraMap R (Overlap f g) g *
      secondRestriction f g (IsLocalization.Away.invSelf g) = 1 := by
    simpa only [map_mul, AlgHom.commutes, map_one] using
      congrArg (secondRestriction f g)
        (IsLocalization.Away.mul_invSelf (S := Localization.Away g) g)
  change secondRestriction f g (IsLocalization.Away.invSelf g) *
    algebraMap R (Overlap f g) (f * g) = algebraMap R (Overlap f g) f
  rw [map_mul]
  calc
    secondRestriction f g (IsLocalization.Away.invSelf g) *
          (algebraMap R (Overlap f g) f * algebraMap R (Overlap f g) g) =
        algebraMap R (Overlap f g) f *
          (algebraMap R (Overlap f g) g *
            secondRestriction f g (IsLocalization.Away.invSelf g)) := by ring
    _ = algebraMap R (Overlap f g) f := by rw [hi, mul_one]

theorem representative_second (f g : R) :
    representative f g g =
      firstRestriction f g (IsLocalization.Away.invSelf f) := by
  symm
  change firstRestriction f g (IsLocalization.Away.invSelf f) =
    IsLocalization.mk' (Overlap f g) g (denominator f g)
  rw [IsLocalization.eq_mk'_iff_mul_eq]
  have hi : algebraMap R (Overlap f g) f *
      firstRestriction f g (IsLocalization.Away.invSelf f) = 1 := by
    simpa only [map_mul, AlgHom.commutes, map_one] using
      congrArg (firstRestriction f g)
        (IsLocalization.Away.mul_invSelf (S := Localization.Away f) f)
  change firstRestriction f g (IsLocalization.Away.invSelf f) *
    algebraMap R (Overlap f g) (f * g) = algebraMap R (Overlap f g) g
  rw [map_mul]
  calc
    firstRestriction f g (IsLocalization.Away.invSelf f) *
          (algebraMap R (Overlap f g) f * algebraMap R (Overlap f g) g) =
        algebraMap R (Overlap f g) g *
          (algebraMap R (Overlap f g) f *
            firstRestriction f g (IsLocalization.Away.invSelf f)) := by ring
    _ = algebraMap R (Overlap f g) g := by rw [hi, mul_one]

@[simp] theorem boundary_first (f g : R) : boundary f g f = 0 := by
  apply (Submodule.Quotient.mk_eq_zero (boundaries f g)).mpr
  rw [representative_first]
  exact Submodule.mem_sup_right ⟨IsLocalization.Away.invSelf g, rfl⟩

@[simp] theorem boundary_second (f g : R) : boundary f g g = 0 := by
  apply (Submodule.Quotient.mk_eq_zero (boundaries f g)).mpr
  rw [representative_second]
  exact Submodule.mem_sup_left ⟨IsLocalization.Away.invSelf f, rfl⟩

theorem span_pair_le_ker (f g : R) :
    Ideal.span ({f, g} : Set R) ≤ LinearMap.ker (boundary f g) := by
  apply Ideal.span_le.mpr
  intro p hp
  rcases Set.mem_insert_iff.mp hp with rfl | hp
  · exact boundary_first _ _
  · have hp' : p = g := Set.mem_singleton_iff.mp hp
    subst p
    exact boundary_second f g

/-- An arbitrary actual localization boundary has a finite cleared witness.
The additional exponent comes from equality in the overlap localization;
no injectivity of the localization map is assumed. -/
theorem cleared_boundary (f g p : R)
    (h : representative f g p ∈ boundaries f g) :
    ∃ (n m : ℕ) (a b : R),
      p * f ^ n * g ^ m = f ^ (n + 1) * a + g ^ (m + 1) * b := by
  obtain ⟨u, ⟨a, rfl⟩, v, ⟨b, rfl⟩, hab⟩ := Submodule.mem_sup.mp h
  obtain ⟨n, q, hq⟩ := IsLocalization.Away.surj f a
  obtain ⟨m, s, hs⟩ := IsLocalization.Away.surj g b
  have hq' : firstRestriction f g a * algebraMap R (Overlap f g) f ^ n =
      algebraMap R (Overlap f g) q := by
    simpa only [map_mul, map_pow, AlgHom.commutes] using
      congrArg (firstRestriction f g) hq
  have hs' : secondRestriction f g b * algebraMap R (Overlap f g) g ^ m =
      algebraMap R (Overlap f g) s := by
    simpa only [map_mul, map_pow, AlgHom.commutes] using
      congrArg (secondRestriction f g) hs
  change firstRestriction f g a + secondRestriction f g b =
    representative f g p at hab
  have hc : algebraMap R (Overlap f g) (p * f ^ n * g ^ m) =
      algebraMap R (Overlap f g)
        (f ^ (n + 1) * (s * g) + g ^ (m + 1) * (q * f)) := by
    calc
      algebraMap R (Overlap f g) (p * f ^ n * g ^ m) =
          (representative f g p * algebraMap R (Overlap f g) (f * g)) *
            algebraMap R (Overlap f g) f ^ n *
              algebraMap R (Overlap f g) g ^ m := by
        rw [representative_spec]
        simp only [map_mul, map_pow]
      _ = (firstRestriction f g a + secondRestriction f g b) *
            (algebraMap R (Overlap f g) f * algebraMap R (Overlap f g) g) *
              algebraMap R (Overlap f g) f ^ n *
                algebraMap R (Overlap f g) g ^ m := by rw [← hab, map_mul]
      _ = (firstRestriction f g a * algebraMap R (Overlap f g) f ^ n) *
            algebraMap R (Overlap f g) f * algebraMap R (Overlap f g) g ^ (m + 1) +
          (secondRestriction f g b * algebraMap R (Overlap f g) g ^ m) *
            algebraMap R (Overlap f g) g * algebraMap R (Overlap f g) f ^ (n + 1) := by
        simp only [pow_succ]
        ring
      _ = algebraMap R (Overlap f g) q * algebraMap R (Overlap f g) f *
            algebraMap R (Overlap f g) g ^ (m + 1) +
          algebraMap R (Overlap f g) s * algebraMap R (Overlap f g) g *
            algebraMap R (Overlap f g) f ^ (n + 1) := by rw [hq', hs']
      _ = algebraMap R (Overlap f g)
            (f ^ (n + 1) * (s * g) + g ^ (m + 1) * (q * f)) := by
        simp only [map_add, map_mul, map_pow]
        ring
  obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq (f * g) hc
  refine ⟨n + k, m + k, s * g ^ (k + 1), q * f ^ (k + 1), ?_⟩
  calc
    p * f ^ (n + k) * g ^ (m + k) =
        (f * g) ^ k * (p * f ^ n * g ^ m) := by
      simp only [pow_add, mul_pow]
      ring
    _ = (f * g) ^ k * (f ^ (n + 1) * (s * g) + g ^ (m + 1) * (q * f)) := hk
    _ = f ^ (n + k + 1) * (s * g ^ (k + 1)) +
          g ^ (m + k + 1) * (q * f ^ (k + 1)) := by
      simp only [pow_add, pow_one, mul_pow]
      ring

/-- The exact kernel of the simple-pole boundary for a weakly regular pair. -/
theorem ker_boundary (f g : R) (hf : IsSMulRegular R f)
    (hg : IsSMulRegular (R ⧸ Ideal.span {f}) g) :
    LinearMap.ker (boundary f g) = Ideal.span ({f, g} : Set R) := by
  apply le_antisymm
  · intro p hp
    have h : representative f g p ∈ boundaries f g :=
      (Submodule.Quotient.mk_eq_zero (boundaries f g)).mp hp
    obtain ⟨n, m, a, b, hab⟩ := cleared_boundary f g p h
    exact cancel_powers f g hf hg n m p a b hab
  · exact span_pair_le_ker f g

theorem boundary_eq_zero_iff (f g : R) (hf : IsSMulRegular R f)
    (hg : IsSMulRegular (R ⧸ Ideal.span {f}) g) (p : R) :
    boundary f g p = 0 ↔ p ∈ Ideal.span ({f, g} : Set R) := by
  change p ∈ LinearMap.ker (boundary f g) ↔ _
  rw [ker_boundary f g hf hg]

/-- The Koszul boundary on the actual quotient, constructed without a
regularity hypothesis. Regularity is used to prove its injectivity. -/
def quotientBoundary (f g : R) :
    R ⧸ Ideal.span ({f, g} : Set R) →ₗ[R] Cech f g :=
  (Ideal.span ({f, g} : Set R)).liftQ (boundary f g) (span_pair_le_ker f g)

@[simp] theorem quotientBoundary_mk (f g p : R) :
    quotientBoundary f g (Ideal.Quotient.mk (Ideal.span ({f, g} : Set R)) p) =
      boundary f g p := rfl

theorem quotientBoundary_injective (f g : R) (hf : IsSMulRegular R f)
    (hg : IsSMulRegular (R ⧸ Ideal.span {f}) g) :
    Function.Injective (quotientBoundary f g) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot _ _ _ (ker_boundary f g hf hg).le

end CycleQ2GeometricKoszulKernel

end
