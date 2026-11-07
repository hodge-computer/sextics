import Proposal.SymmetricBalancedTransport

/-!
# The full five-component weighted current reaches the protected target

A normal component is allowed in addition to the four coefficient
components. Under `u=v^2`, its affine numerator is `2*N_u(v^2)`, while each
coefficient numerator is `4*v*N_i(v^2)`. The complete ordinary game
transforms by the common factor `4*v`; no stronger contraction or
divergence equations are required.

Any nonzero denominator in the coefficient coordinates is automatically
legal by `SymmetricBalancedTransport.base_denominator_legal`. The numerator
components can have arbitrary polynomial dependence on the normal variable.
-/

noncomputable section

namespace SymmetricNormalTransport

open MvPolynomial WeightedPrimitiveTransport SymmetricCertificateTransport
open SymmetricBalancedTransport
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The numerator of the full reflected affine current. -/
def reflectedNumerator (Nu : Poly) (Z : Fin 4 → Poly) : Fin 5 → Poly :=
  mergeNumerators (C 2*squareLift Nu) (fun i => C 4*X 4*squareLift (Z i))

theorem merge_divergence (Nu : Poly) (Z : Fin 4 → Poly) :
    HodgeTestbed.divergence (mergeNumerators Nu Z) =
      pderiv 4 Nu+(∑ i : Fin 4, pderiv i.castSucc (Z i)) := by
  simp [HodgeTestbed.divergence, mergeNumerators, Fin.sum_univ_succ]
  ring

theorem reflected_directional (f Nu : Poly) (Z : Fin 4 → Poly) :
    HodgeTestbed.directional (squareLift f) (reflectedNumerator Nu Z) =
      C 4*X 4*squareLift (HodgeTestbed.directional f (mergeNumerators Nu Z)) := by
  simp only [reflectedNumerator, mergeNumerators_directional,
    normal_squareLift, tangent_squareLift, map_add, map_mul, map_sum]
  have hs : (∑ i : Fin 4, C 4*X 4*squareLift (Z i)*squareLift (pderiv i.castSucc f)) =
      C 4*X 4*(∑ i : Fin 4, squareLift (Z i)*squareLift (pderiv i.castSucc f)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  simp only [map_ofNat]
  ring

theorem reflected_divergence (Nu : Poly) (Z : Fin 4 → Poly) :
    HodgeTestbed.divergence (reflectedNumerator Nu Z) =
      C 4*X 4*squareLift (HodgeTestbed.divergence (mergeNumerators Nu Z)) := by
  have ht (i : Fin 4) :
      pderiv i.castSucc (C 4*X 4*squareLift (Z i)) =
        C 4*X 4*squareLift (pderiv i.castSucc (Z i)) := by
    have hne : (4 : Fin 5) ≠ i.castSucc := (Fin.castSucc_ne_last i).symm
    simp [pderiv_X_of_ne hne, tangent_squareLift]
  simp only [reflectedNumerator, merge_divergence, pderiv_mul, pderiv_C,
    zero_mul, zero_add, normal_squareLift, ht, map_add, map_sum,
    mul_add, Finset.mul_sum]
  simp only [map_ofNat]
  ring

/-- The exact defect, with both base and normal denominator derivatives,
transforms by the source's reflected volume factor. -/
theorem reflected_game_identity (f P D Nu : Poly) (Z : Fin 4 → Poly) :
    HodgeTestbed.clearedDefect (squareLift f) (reflectedSource P)
      (squareLift D) (reflectedNumerator Nu Z) =
      C 4*X 4*squareLift (HodgeTestbed.clearedDefect f P D (mergeNumerators Nu Z)) := by
  simp only [HodgeTestbed.clearedDefect, HodgeTestbed.divergenceNumerator,
    reflectedSource, reflected_directional, reflected_divergence,
    map_add, map_sub, map_mul, map_pow]
  ring

/-- Every full weighted ordinary-game solution with a nonzero base
denominator gives the exact protected symmetric target. -/
theorem certificate_of_weighted_game
    (D Nu : Poly) (Z : Fin 4 → Poly)
    (hD : D ≠ 0) (hbase : (4 : Fin 5) ∉ D.vars)
    (hgame : HodgeTestbed.clearedDefect rawWeighted rawSource D
      (mergeNumerators Nu Z) = 0) :
    HodgeComputer.HasCertificate HodgeSubmission.F 1 HodgeSubmission.A := by
  apply certificate_of_affine_game (squareLift D) (reflectedNumerator Nu Z)
    (by simpa only [squareLift_of_base D hbase] using hD)
    (base_denominator_legal D hD hbase)
  change HodgeTestbed.clearedDefect (squareLift rawWeighted) (reflectedSource rawSource)
    (squareLift D) (reflectedNumerator Nu Z) = 0
  rw [reflected_game_identity, hgame, map_zero, mul_zero]

#print axioms reflected_game_identity
#print axioms certificate_of_weighted_game

end SymmetricNormalTransport
