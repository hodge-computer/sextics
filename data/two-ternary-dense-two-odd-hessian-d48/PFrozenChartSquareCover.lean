import Proposal.PFrozenChartCompatibility
import HodgeComputer.Constructions.RationalFields.ReflectionCover
import Mathlib.Algebra.MvPolynomial.Expand

/-! # Genuine u=t² substitution and its rational derivative rules -/
set_option autoImplicit false
noncomputable section
namespace HodgeTestbed.FrozenChart
open MvPolynomial

/-- Squaring the complementary variables gives the full expansion map, proving injection. -/
theorem squareCoverPoly_injective : Function.Injective squareCoverPoly := by
  let complement : Poly 5 →ₐ[ℚ] Poly 5 := aeval (fun i => if i = 3 then X i else X i ^ 2)
  have hc : complement.comp squareCoverPoly = expand 2 := by
    ext1 i
    change complement (squareCoverPoly (X i)) = expand 2 (X i)
    have hs : squareCoverPoly (X i) = if i = 3 then X 3 ^ 2 else X i := aeval_X _ _
    have ht (j : Fin 5) : complement (X j) = if j = 3 then X j else X j ^ 2 := aeval_X _ _
    rw [hs, expand_X]
    by_cases hi : i = 3 <;> simp [hi, ht]
  intro p q hpq
  apply expand_injective (by decide : 0 < 2)
  rw [← hc]
  exact congrArg complement hpq

theorem embed_injective {n : ℕ} : Function.Injective (embed (n := n)) :=
  IsFractionRing.injective (Poly n) (RatFun n)

@[simp] theorem coord_ne_zero {n : ℕ} (i : Fin n) : coord i ≠ 0 := by
  exact fun h => X_ne_zero i (embed_injective (by simpa [coord] using h))

/-- The actual square-cover homomorphism of QQ rational function fields. -/
def squareCover : RatFun 5 →ₐ[ℚ] RatFun 5 :=
  IsFractionRing.liftAlgHom (g := embed.comp squareCoverPoly)
    (embed_injective.comp squareCoverPoly_injective)

@[simp] theorem squareCover_embed (p : Poly 5) : squareCover (embed p) = embed (squareCoverPoly p) :=
  IsLocalization.lift_eq _ p

@[simp] theorem squareCover_coord (i : Fin 5) :
    squareCover (coord i) = if i = 3 then coord 3 ^ 2 else coord i := by
  rw [coord, squareCover_embed]
  have hs : squareCoverPoly (X i) = if i = 3 then X 3 ^ 2 else X i := aeval_X _ _
  rw [hs]
  split_ifs <;> simp [coord]

/-- The cover's chain rule holds for all rational functions, not only coordinates. -/
theorem squareCover_chain (i : Fin 5) (z : RatFun 5) :
    rationalPartial i (squareCover z) = if i = 3 then
      2 * coord 3 * squareCover (rationalPartial i z) else squareCover (rationalPartial i z) := by
  have hh := compatibility_of_coordinates squareCover (rationalPartial i) (rationalPartial i)
    (if i = 3 then 2 * coord 3 else 1) (fun j => by
      rw [squareCover_coord, partial_coord]
      by_cases hi : i = 3 <;> by_cases hj : j = 3
      · subst i; subst j
        norm_num [Derivation.leibniz_pow, partial_coord, smul_eq_mul]
      · simp [hi, hj, partial_coord, Ne.symm hj]
      · simp [hi, hj, Derivation.leibniz_pow, partial_coord, smul_eq_mul]
      · simp [hi, hj, partial_coord]) z
  simpa only [ite_mul, one_mul] using hh

/-- The cover field's exact divergence formula now has no chart-rule premise. -/
theorem actual_cover_divergence (q : Fin 5 → RatFun 5) :
    Conic.fieldDivergence rationalPartial
      (Conic.coverField squareCover.toRingHom (coord 3) q) =
      2 * coord 3 * squareCover (Conic.fieldDivergence rationalPartial q) :=
  Conic.coverField_divergence rationalPartial rationalPartial squareCover.toRingHom (coord 3)
    squareCover_chain (fun i => partial_coord i 3) q

end HodgeTestbed.FrozenChart
