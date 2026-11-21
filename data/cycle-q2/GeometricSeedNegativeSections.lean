import Proposal.SeedLinkageGluing

/-!
# Negative-degree sections vanish on the original three seed charts

The existing homogeneous gluing theorem supplies an actual polynomial
representative for compatible sections in the original three coordinate
localizations. Its original grading has nonnegative polynomial degree.
Consequently a negative-degree family is zero, for every cubic character.

The degree-minus-four endpoint is intended for the inverse of a supposed
nowhere-vanishing section of the actual image line. Its construction from
emptiness, and the degree-four image/dual-ideal comparison, are separate
steps: this module does not assume or assert that inverse family exists.

Source-only draft: no Lean elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric strategy and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedNegativeSections

open MvPolynomial
open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization
  CycleQ2SeedCechLocalizedBasis CycleQ2SeedCechLinearCoordinates
  CycleQ2SeedQuotientGrading CycleQ2SeedCechGlobalGluing

variable (R : Type*) [CommRing R]

theorem polynomial_eq_zero_of_negative_degree (p : Poly R) (g : LaurentGrade)
    (hp : SignedHomogeneous R p g) (hg : g.1 < 0) : p = 0 := by
  by_contra hn
  obtain ⟨e, he⟩ := exists_coeff_ne_zero hn
  have hdegree := congrArg Prod.fst (hp e he)
  have hnonneg : (0 : ℤ) ≤ (signedGrade (Finsupp.weight fullGrading e)).1 := by
    change (0 : ℤ) ≤ ((Finsupp.weight fullGrading e).1 : ℤ)
    exact Int.natCast_nonneg _
  rw [hdegree] at hnonneg
  exact (not_lt_of_ge hnonneg) hg

/-- This is vanishing in the actual old seed localization rings, not
in a replacement cohomology or formal line-bundle model. -/
theorem compatible_eq_zero_of_negative_degree [Nontrivial R]
    (r ι : R) (q : Sections R r ι) (hq : Compatible R r ι q)
    (g : LaurentGrade)
    (hg : ∀ ab, HasGrade ab g (localizedCoordinates R r ι {0} (q 0) ab))
    (hnegative : g.1 < 0) : ∀ i, q i = 0 := by
  obtain ⟨p, _, hp, hglue⟩ :=
    exists_homogeneous_polynomial_gluing R r ι q hq g hg
  have hz := polynomial_eq_zero_of_negative_degree R p g hp hnegative
  intro i
  simpa only [hz, map_zero] using (hglue i).symm

theorem compatible_degree_neg_four_eq_zero [Nontrivial R]
    (r ι : R) (q : Sections R r ι) (hq : Compatible R r ι q)
    (χ : ZMod 3)
    (hg : ∀ ab, HasGrade ab ((-4 : ℤ), χ)
      (localizedCoordinates R r ι {0} (q 0) ab)) : ∀ i, q i = 0 :=
  compatible_eq_zero_of_negative_degree R r ι q hq ((-4 : ℤ), χ) hg (by norm_num)

#print axioms polynomial_eq_zero_of_negative_degree
#print axioms compatible_eq_zero_of_negative_degree
#print axioms compatible_degree_neg_four_eq_zero

end CycleQ2SeedNegativeSections
end
