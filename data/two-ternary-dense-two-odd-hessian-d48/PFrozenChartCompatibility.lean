import Proposal.PFrozenChartRational
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Tactic.Ring

/-! # Chain rules on actual QQ rational function fields -/
set_option autoImplicit false
noncomputable section
namespace HodgeTestbed.FrozenChart
open MvPolynomial

@[simp] theorem embed_C {n : ℕ} (r : ℚ) : embed (C r : Poly n) = algebraMap ℚ (RatFun n) r :=
  embed.commutes r

/-- A coordinate check proves a scaled derivative compatibility on every rational function.
Polynomial Leibniz induction and the quotient rule discharge all remaining inputs. -/
theorem compatibility_of_coordinates {n m : ℕ}
    (f : RatFun n →ₐ[ℚ] RatFun m)
    (D : Derivation ℚ (RatFun m) (RatFun m)) (E : Derivation ℚ (RatFun n) (RatFun n))
    (c : RatFun m) (hcoord : ∀ j, D (f (coord j)) = c * f (E (coord j)))
    (z : RatFun n) : D (f z) = c * f (E z) := by
  have hp (p : Poly n) : D (f (embed p)) = c * f (E (embed p)) := by
    induction p using MvPolynomial.induction_on with
    | C r => simp only [embed_C, AlgHom.commutes, Derivation.map_algebraMap, map_zero, mul_zero]
    | add p q hp hq => simp only [map_add, hp, hq]; ring
    | mul_X p j hp =>
      simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add]
      rw [hp, show D (f (embed (X j))) = c * f (E (embed (X j))) from hcoord j]
      ring
  obtain ⟨p, q, _, rfl⟩ := IsFractionRing.div_surjective (Poly n) z
  change D (f (embed p / embed q)) = c * f (E (embed p / embed q))
  simp only [div_eq_mul_inv, map_mul, map_inv₀, Derivation.leibniz,
    Derivation.leibniz_inv, smul_eq_mul, hp, map_neg, map_add, map_pow]
  ring

/-- Rational derivations are determined by the actual polynomial variables. -/
theorem rational_derivation_ext {n : ℕ} (D E : Derivation ℚ (RatFun n) (RatFun n))
    (h : ∀ j, D (coord j) = E (coord j)) : D = E := by
  ext z
  simpa using compatibility_of_coordinates (AlgHom.id ℚ (RatFun n)) D E 1
    (fun j => by simpa using h j) z

/-- The constructed rational partial derivatives really commute. -/
theorem rationalPartial_commute {n : ℕ} (i j : Fin n) :
    Function.Commute (rationalPartial i) (rationalPartial j) := by
  have hh : ⁅rationalPartial i, rationalPartial j⁆ = 0 := by
    apply rational_derivation_ext
    intro k
    simp [Derivation.commutator_apply, partial_coord, apply_ite]
  intro z
  have hz := Derivation.congr_fun hh z
  simpa only [Derivation.commutator_apply, zero_apply, sub_eq_zero] using hz

end HodgeTestbed.FrozenChart
