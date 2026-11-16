import Proposal.GeometricPolynomialDenominator
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# A monic polynomial over the generic function field spreads over a principal open

For a monic polynomial p over Frac(R), the previous coefficient-clearing
lemma supplies d != 0 and q over R with q.map = p * C(d). This file proves
that q.leadingCoeff = d and constructs a monic polynomial over the *actual*
localization R[1/d].

The generic-fiber comparison of that monic localized polynomial, its
separability, and the morphism to the original parameter scheme are distinct
proof obligations. This construction does not assert them. The protected
certificate and its current admission are not modified.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

open Polynomial

namespace CycleQ2MonicPolynomialSpreading

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The cleared numerator has its *actual* leading coefficient equal to
its chosen nonzero denominator. -/
theorem exists_cleared_monic (p : Polynomial (FractionRing R)) (hp : p.Monic) :
    ∃ d : R, d ≠ 0 ∧ ∃ q : Polynomial R,
      q.leadingCoeff = d ∧
      p * C (algebraMap R (FractionRing R) d) =
        q.map (algebraMap R (FractionRing R)) := by
  obtain ⟨d, hd, q, hq⟩ :=
    CycleQ2PolynomialDenominator.exists_cleared_polynomial p
  have hinj : Function.Injective (algebraMap R (FractionRing R)) :=
    IsFractionRing.injective R (FractionRing R)
  have hne : algebraMap R (FractionRing R) d ≠ 0 := by simpa only [map_zero] using hinj.ne hd
  have hu : IsUnit (algebraMap R (FractionRing R) d) :=
    isUnit_iff_ne_zero.mpr hne
  have hlead : q.leadingCoeff = d := by
    apply hinj
    calc
      algebraMap R (FractionRing R) q.leadingCoeff =
          (q.map (algebraMap R (FractionRing R))).leadingCoeff :=
        (leadingCoeff_map_of_injective hinj q).symm
      _ = (p * C (algebraMap R (FractionRing R) d)).leadingCoeff :=
        congrArg Polynomial.leadingCoeff hq.symm
      _ = algebraMap R (FractionRing R) d := by
        rw [leadingCoeff_mul_C_of_isUnit hu, hp.leadingCoeff, one_mul]
  exact ⟨d, hd, q, hlead, hq⟩

/-- The same numerator becomes a monic polynomial over the original
principal localization. No generic-fiber comparison is assumed here. -/
theorem exists_monic_localization (p : Polynomial (FractionRing R)) (hp : p.Monic) :
    ∃ d : R, d ≠ 0 ∧ ∃ f : Polynomial (Localization.Away d), f.Monic := by
  obtain ⟨d, hd, q, hlead, _⟩ := exists_cleared_monic p hp
  have hinj : Function.Injective (algebraMap R (Localization.Away d)) :=
    IsLocalization.injective (Localization.Away d)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hd)
  have hnonzero : algebraMap R (Localization.Away d) d ≠ 0 := by
    simpa only [map_zero] using hinj.ne hd
  refine ⟨d, hd, q.map (algebraMap R (Localization.Away d)) *
    C (IsLocalization.Away.invSelf (S := Localization.Away d) d), ?_⟩
  apply monic_mul_C_of_leadingCoeff_mul_eq_one
  rw [leadingCoeff_map_of_injective hinj q, hlead]
  exact IsLocalization.Away.mul_invSelf (S := Localization.Away d) d

end CycleQ2MonicPolynomialSpreading

end

#print axioms CycleQ2MonicPolynomialSpreading.exists_cleared_monic
#print axioms CycleQ2MonicPolynomialSpreading.exists_monic_localization
