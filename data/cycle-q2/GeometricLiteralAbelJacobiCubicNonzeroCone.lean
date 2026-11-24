import Proposal.GeometricSeedConeSection

/-!
# Polynomial multipliers for the section ideal on the original seed cone

Membership of a polynomial in the three local row ideals gives local
multipliers by balancing the section functional on the linkage ideal.
When the three row products determine a scalar on the double overlaps,
these multipliers glue in the original seed quotient.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAbelJacobiCubicNonzeroCone

open CycleQ2SeedConeSection CycleQ2SegreFactorChartExact
  CycleQ2SegreLinkageDuality CycleQ2SeedSectionInverse
  CycleQ2SeedFactorHomogeneous CycleQ2SegreFactorSequence

local instance chartCommRing (s : Finset (Fin 3)) : CommRing (Chart s) := inferInstance
local instance seedCommRing : CommRing A := inferInstance

variable (t : Fin 3 → ℂ) (p : P)

theorem exists_local_multiplier (s : Finset (Fin 3)) (hs : s.Nonempty)
    (hm : polynomialToCone s p ∈ Ideal.span (Set.range (row t s))) :
    ∃ q : Chart s, ∀ a, row t s a * q =
      polynomialToCone s p * polynomialToCone s (polynomialLeft (57 : ℂ) a) := by
  let F := factorData s hs
  let v := fun j => algebraMap ℂ (Chart s) (t j)
  let φ := sectionFunctional F v
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hm
  let q := CycleQ2SectionInverseIdeal.bezoutElement F.leftIdeal (leftElement F) c
  have heval : φ q = polynomialToCone s p := by
    rw [show φ q = _ from CycleQ2SectionInverseIdeal.bezoutElement_eval F.leftIdeal φ _ c]
    simpa only [φ, v, F, sectionFunctional_left, matrixRow_eq] using hc
  refine ⟨q.val, fun a => ?_⟩
  have hrow : φ (leftElement F a) = row t s a :=
    (sectionFunctional_left F v a).trans (matrixRow_eq t s hs a)
  rw [← left_eq_polynomial s hs a, ← hrow, ← heval, mul_comm (φ _) _, mul_comm (φ _) _]
  exact CycleQ2SectionInverseIdeal.balanced F.leftIdeal φ q (leftElement F a)

/-- The three conormal equations agree after either chart restriction. -/
private theorem restricted_products (i : Fin 3) (s : Finset (Fin 3))
    (h : ({i} : Finset (Fin 3)) ⊆ s) (q : Chart {i})
    (hq : ∀ a, row t {i} a * q = polynomialToCone {i} p *
      polynomialToCone {i} (polynomialLeft (57 : ℂ) a)) (a : Fin 3) :
    row t s a * restrict (s := {i}) (u := s) h q = polynomialToCone s p *
      polynomialToCone s (polynomialLeft (57 : ℂ) a) := by
  calc
    row t s a * restrict (s := {i}) (u := s) h q = restrict (s := {i}) (u := s) h (row t {i} a * q) := by
      rw [map_mul, restrict_row]
    _ = restrict (s := {i}) (u := s) h (polynomialToCone {i} p * polynomialToCone {i} (polynomialLeft (57 : ℂ) a)) :=
      congrArg (restrict (s := {i}) (u := s) h) (hq a)
    _ = _ := by rw [map_mul, restrict_polynomial, restrict_polynomial]

private def sections (hrow : ∀ i : Fin 3, polynomialToCone {i} p ∈ Ideal.span (Set.range (row t {i}))) :
    CycleQ2SeedCechGlobalGluing.Sections ℂ (57 : ℂ) Complex.I :=
  fun i => (exists_local_multiplier t p {i} (Finset.singleton_nonempty i) (hrow i)).choose

private theorem sections_spec
    (hrow : ∀ i : Fin 3, polynomialToCone {i} p ∈ Ideal.span (Set.range (row t {i})))
    (i a : Fin 3) : row t {i} a * sections t p hrow i =
      polynomialToCone {i} p * polynomialToCone {i} (polynomialLeft (57 : ℂ) a) :=
  (exists_local_multiplier t p {i} (Finset.singleton_nonempty i) (hrow i)).choose_spec a

/-- Restrictions to the three singleton cone charts suffice. -/
theorem exists_global_multiplier
    (hrow : ∀ i : Fin 3, polynomialToCone {i} p ∈ Ideal.span (Set.range (row t {i})))
    (hfaith : ∀ (i j : Fin 3) (x y : Chart {i,j}),
      (∀ a, row t {i,j} a * x = row t {i,j} a * y) → x = y) :
    ∃ q : A, ∀ a : Fin 3, quotient (rowPolynomial t a) * q =
      quotient p * quotient (polynomialLeft (57 : ℂ) a) := by
  have hcomp : CycleQ2SeedCechGlobalGluing.Compatible ℂ (57 : ℂ) Complex.I (sections t p hrow) := by
    intro i j
    change restrict (show ({i} : Finset (Fin 3)) ⊆ {i,j} by simp) (sections t p hrow i) =
      restrict (show ({j} : Finset (Fin 3)) ⊆ {i,j} by simp) (sections t p hrow j)
    apply hfaith i j
    intro a
    exact (restricted_products t p i {i,j} (by simp) _ (sections_spec t p hrow i) a).trans
      (restricted_products t p j {i,j} (by simp) _ (sections_spec t p hrow j) a).symm
  obtain ⟨z, hz, _⟩ := CycleQ2SeedCechGlobalGluing.existsUnique_gluing
    ℂ (57 : ℂ) Complex.I (sections t p hrow) hcomp
  refine ⟨z, fun a => ?_⟩
  apply CycleQ2SeedCechGlobalGluing.localization_injective ℂ (57 : ℂ) Complex.I {0}
  rw [map_mul, map_mul, hz 0]
  exact sections_spec t p hrow 0 a

end CycleQ2LiteralAbelJacobiCubicNonzeroCone
end

#print axioms CycleQ2LiteralAbelJacobiCubicNonzeroCone.exists_global_multiplier
