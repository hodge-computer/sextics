import Proposal.GeometricSeedSectionNonempty

/-!
# Low-weight polynomials in the literal seed surface quotient

Suppose the three degree-fourteen rows of a section, multiplied by a single
function on the seed cone, give a degree-at-most-three polynomial times the
original three left generators. Each product on the right has degree less
than fourteen. The homogeneous degree comparison kills all three. The regular
linkage factor and the spanning matrix entries then kill the polynomial
itself in the original seed surface quotient.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2LiteralAbelJacobiCubicNonzeroDegree

open CycleQ2IncidenceNormalForm CycleQ2GeometricIncidenceProj
  CycleQ2SegreFactorChartExact CycleQ2SeedFactorHomogeneous
  CycleQ2SeedConeSection CycleQ2SeedSectionNonempty

/-- Saturation by the original coordinate cover cannot create a nonzero
low-degree equation when the section admits this global cone multiplier. -/
theorem low_degree_zero_of_global_multiplier (t : Fin 3 → ℂ) (p : P) (n : ℕ)
    (hp : p.IsWeightedHomogeneous geometricWeight n) (hn : n < 4) (q : A)
    (hq : ∀ a : Fin 3, quotient (rowPolynomial t a) * q =
      quotient p * quotient (polynomialLeft (57 : ℂ) a)) : quotient p = 0 := by
  obtain ⟨q₀, hq₀⟩ := Ideal.Quotient.mk_surjective q
  have hpL (a : Fin 3) : quotient (p * polynomialLeft (57 : ℂ) a) = 0 := by
    apply CycleQ2SectionDegreeGap.lower_class_zero_of_multiple geometricWeight seedIdeal
      seedIdeal_homogeneous (rowPolynomial t a) q₀ (p * polynomialLeft (57 : ℂ) a)
      14 (n + 10) (rowPolynomial_homogeneous t a) (hp.mul (polynomialLeft_degree_ten a)) (by omega)
    change quotient (rowPolynomial t a) * quotient q₀ = quotient (p * polynomialLeft (57 : ℂ) a)
    rw [show quotient q₀ = q from hq₀, map_mul, hq]
  let s : Finset (Fin 3) := {0}
  let hs : s.Nonempty := Finset.singleton_nonempty 0
  let F := factorData s hs
  apply CycleQ2SeedCechGlobalGluing.localization_injective ℂ (57 : ℂ) Complex.I s
  rw [map_zero]
  apply CycleQ2SegreFactorExact.gauge_scalar_unique F.linkage F.regular F.matrix F.left F.right
    F.product F.entries_generate
  intro a
  rw [zero_mul]
  change polynomialToCone s p * (factorData s hs).left a = 0
  rw [left_eq_polynomial s hs a, ← map_mul, polynomialToCone_apply, hpL, map_zero]

end CycleQ2LiteralAbelJacobiCubicNonzeroDegree
end

#print axioms CycleQ2LiteralAbelJacobiCubicNonzeroDegree.low_degree_zero_of_global_multiplier
