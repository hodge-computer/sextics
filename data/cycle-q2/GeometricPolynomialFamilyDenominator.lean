import Proposal.GeometricPolynomialDenominator

/-!
# A common denominator for finitely many rational polynomials

The finite generic parameter over the pencil has multiple polynomial
coordinates: the primitive equation, its derivative Bezout witnesses, and
finitely many Hilbert parameter coordinates. A denominator for just one
polynomial is insufficient for simultaneous spreading.

This module constructs a single nonzero base-ring denominator for an
arbitrary finite family of actual polynomials over Frac(R), plus their
polynomial numerators over R. It generalizes the checked one-polynomial
result, and retains the common denominator in every identity.

It does not claim a finite etale model over a principal open, a Hilbert
morphism, or preservation of cohomology classes. Those remain separate.
-/

set_option autoImplicit false

noncomputable section
open Polynomial

namespace CycleQ2PolynomialFamilyDenominator

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Every polynomial in a finite family can be cleared using the *same*
nonzero denominator, with a real polynomial numerator for each member. -/
theorem exists_finset_common_denominator {ι : Type*}
    (p : ι → Polynomial (FractionRing R)) (s : Finset ι) :
    ∃ d : R, d ≠ 0 ∧
      ∀ i ∈ s, ∃ q : Polynomial R,
        p i * C (algebraMap R (FractionRing R) d) =
          q.map (algebraMap R (FractionRing R)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨1, one_ne_zero, ?_⟩
      simp
  | @insert i s hi ih =>
      obtain ⟨d, hd, hrec⟩ := ih
      obtain ⟨e, he, q, hq⟩ :=
        CycleQ2PolynomialDenominator.exists_cleared_polynomial (p i)
      refine ⟨d * e, mul_ne_zero hd he, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hji | hj
      · subst j
        refine ⟨q * C d, ?_⟩
        calc
          p i * C (algebraMap R (FractionRing R) (d * e)) =
            (p i * C (algebraMap R (FractionRing R) e)) *
              C (algebraMap R (FractionRing R) d) := by
                rw [map_mul, map_mul]
                ac_rfl
          _ = (q.map (algebraMap R (FractionRing R))) *
              C (algebraMap R (FractionRing R) d) := by rw [hq]
          _ = (q * C d).map (algebraMap R (FractionRing R)) := by
                simp only [Polynomial.map_mul, Polynomial.map_C]
      · obtain ⟨q, hq⟩ := hrec j hj
        refine ⟨q * C e, ?_⟩
        calc
          p j * C (algebraMap R (FractionRing R) (d * e)) =
            (p j * C (algebraMap R (FractionRing R) d)) *
              C (algebraMap R (FractionRing R) e) := by
                rw [map_mul, map_mul, mul_assoc]
          _ = (q.map (algebraMap R (FractionRing R))) *
              C (algebraMap R (FractionRing R) e) := by rw [hq]
          _ = (q * C e).map (algebraMap R (FractionRing R)) := by
                simp only [Polynomial.map_mul, Polynomial.map_C]

/-- The finite-indexed form used for any fixed list of parameter equations
and their Bezout witnesses. -/
theorem exists_common_denominator {ι : Type*} [Fintype ι]
    (p : ι → Polynomial (FractionRing R)) :
    ∃ d : R, d ≠ 0 ∧
      ∀ i, ∃ q : Polynomial R,
        p i * C (algebraMap R (FractionRing R) d) =
          q.map (algebraMap R (FractionRing R)) := by
  obtain ⟨d, hd, h⟩ := exists_finset_common_denominator p Finset.univ
  exact ⟨d, hd, fun i => h i (Finset.mem_univ i)⟩

end CycleQ2PolynomialFamilyDenominator

end

#print axioms CycleQ2PolynomialFamilyDenominator.exists_finset_common_denominator
#print axioms CycleQ2PolynomialFamilyDenominator.exists_common_denominator
