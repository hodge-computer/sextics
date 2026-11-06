import HodgeComputer.Constructions.RationalFields.ResidueReduction

/-! Extracted from `benediamond`’s accepted two-ternary dense Hessian
construction. The application and its mathematical credit are linked in README.md. -/


/-!
# The actual u=t² reflection-cover transfer

Both affine tuples are ordered (x,r,y,u-or-t,z); index3 is the fourth coordinate.
The derivative rules are the algebraic chain rule for u=t². No inverse of t
appears in the field or its proved contraction/divergence transfer.
-/

set_option autoImplicit false
noncomputable section

namespace HodgeTestbed.Conic

variable {R S : Type*} [Field R] [Field S]
  [Algebra ℚ R] [Algebra ℚ S]

/-- The physical cover field has fourth component q_u and other components 2t*q_i. -/
def coverField (f : R →+* S) (t : S) (q : Fin 5 → R) (i : Fin 5) : S :=
  if i = 3 then f (q i) else 2 * t * f (q i)

/-- Contraction transfer through the actual reflection cover. -/
theorem coverField_contraction (δ : Fin 5 → Derivation ℚ R R)
    (θ : Fin 5 → Derivation ℚ S S) (f : R →+* S) (t : S)
    (hchain : ∀ i x, θ i (f x) = if i = 3 then 2 * t * f (δ i x) else f (δ i x))
    (q : Fin 5 → R) (H : R) :
    fieldAction θ (coverField f t q) (f H) = 2 * t * f (fieldAction δ q H) := by
  simp only [fieldAction_apply, map_sum, map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [coverField, hchain]
  split_ifs <;> ring

/-- Divergence transfer is derived componentwise, including the normal cover derivative. -/
theorem coverField_divergence (δ : Fin 5 → Derivation ℚ R R)
    (θ : Fin 5 → Derivation ℚ S S) (f : R →+* S) (t : S)
    (hchain : ∀ i x, θ i (f x) = if i = 3 then 2 * t * f (δ i x) else f (δ i x))
    (ht : ∀ i, θ i t = if i = 3 then 1 else 0) (q : Fin 5 → R) :
    fieldDivergence θ (coverField f t q) = 2 * t * f (fieldDivergence δ q) := by
  simp only [fieldDivergence, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have htwo : θ i (2 : S) = 0 := (θ i).map_natCast 2
  by_cases hi : i = 3
  · simp only [coverField, if_pos hi, hchain]
  · simp only [coverField, if_neg hi, Derivation.leibniz, smul_eq_mul, htwo, ht,
      hchain, mul_zero, add_zero]

/-- A quotient raw game field transfers to the physical cover with target 2t*A. -/
theorem coverField_game (δ : Fin 5 → Derivation ℚ R R)
    (θ : Fin 5 → Derivation ℚ S S) (f : R →+* S) (t : S)
    (hchain : ∀ i x, θ i (f x) = if i = 3 then 2 * t * f (δ i x) else f (δ i x))
    (ht : ∀ i, θ i t = if i = 3 then 1 else 0) (q : Fin 5 → R) (H A : R)
    (hgame : A - fieldAction δ q H + H * fieldDivergence δ q = 0) :
    2 * t * f A - fieldAction θ (coverField f t q) (f H) +
      f H * fieldDivergence θ (coverField f t q) = 0 := by
  rw [coverField_contraction δ θ f t hchain, coverField_divergence δ θ f t hchain ht]
  have hh := congrArg f hgame
  simp only [map_add, map_sub, map_mul, map_zero] at hh
  linear_combination 2 * t * hh

variable [CharZero S]

/-- The actual quotient target one half becomes the cover coordinate t. -/
theorem coverField_game_half (δ : Fin 5 → Derivation ℚ R R)
    (θ : Fin 5 → Derivation ℚ S S) (f : R →+* S) (t : S)
    (hchain : ∀ i x, θ i (f x) = if i = 3 then 2 * t * f (δ i x) else f (δ i x))
    (ht : ∀ i, θ i t = if i = 3 then 1 else 0) (q : Fin 5 → R) (H : R)
    (hgame : 1 / 2 - fieldAction δ q H + H * fieldDivergence δ q = 0) :
    t - fieldAction θ (coverField f t q) (f H) +
      f H * fieldDivergence θ (coverField f t q) = 0 := by
  have hh := coverField_game δ θ f t hchain ht q H (1 / 2) hgame
  have htgt : 2 * t * f (1 / 2) = t := by
    rw [map_div₀, map_one, map_ofNat]
    ring
  simpa only [htgt] using hh

end HodgeTestbed.Conic
