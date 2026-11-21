import Proposal.GeometricSeedConeSection
import Proposal.GeometricSectionDegreeGap

/-!
# Nonemptiness of the original specialized seed curve

This is the closed source-level assembly. It has no extra geometric,
regularity, nonunit, compatibility, or grading hypothesis. Assuming the
original specialized curve empty produces a global scalar p in the
unchanged seed ring. Its products with the degree-fourteen rows equal
the original degree-ten left generators. Homogeneous degree extraction
forces every one of those generators to vanish, contradicting the
value-one inverse in a nonzero actual chart.

This avoids asserting that an arbitrary inverse is character-homogeneous.
The only grading argument takes place in the original polynomial quotient.
No target polynomial, residue statement, or certificate is changed.

Prepared for fqlx with OpenAI ChatGPT assistance, 15 November 2026.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedSectionNonempty

open MvPolynomial
open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2GeometricIncidenceProj
  CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree
  CycleQ2SegreFactorChartExact CycleQ2SeedFactorHomogeneous
  CycleQ2SeedSectionInverse CycleQ2SeedConeSection
  CycleQ2SpecializedProjectiveCurve

attribute [local instance] MvPolynomial.weightedGradedAlgebra

def seedIdeal : Ideal P :=
  equationsIdeal (smoothH Complex.I) (smoothF (57 : ℂ) Complex.I)

theorem seedIdeal_homogeneous :
    seedIdeal.IsHomogeneous (weightedHomogeneousSubmodule ℂ geometricWeight) := by
  apply Ideal.homogeneous_span
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · exact ⟨3, homogeneous_of_character (smoothH_homogeneous Complex.I)⟩
  · exact ⟨6, homogeneous_of_character (smoothF_homogeneous (57 : ℂ) Complex.I)⟩

theorem rowPolynomial_homogeneous (t : Fin 3 → ℂ) (a : Fin 3) :
    (rowPolynomial t a).IsWeightedHomogeneous geometricWeight 14 := by
  apply (weightedHomogeneousSubmodule ℂ geometricWeight 14).sum_mem
  intro j _
  exact (homogeneous_of_character (rawSeedMatrix_homogeneous (57 : ℂ) a j)).C_mul (t j)

theorem polynomialLeft_degree_ten (a : Fin 3) :
    (polynomialLeft (57 : ℂ) a).IsWeightedHomogeneous geometricWeight 10 :=
  homogeneous_of_character (polynomialLeft_homogeneous (57 : ℂ) a)

/-- The actual seed quotient is nonzero, using its existing rank-nine basis. -/
theorem seed_nontrivial : Nontrivial A := by
  let b := seedBasis ℂ (57 : ℂ) Complex.I
  exact ⟨b (0, 0), 0, b.ne_zero (0, 0)⟩

/-- The old coordinate localization is faithful, so it is nonzero as well. -/
theorem cone_nontrivial (s : Finset (Fin 3)) : Nontrivial (Chart s) := by
  letI := seed_nontrivial
  have h10 : (1 : Chart s) ≠ 0 := by
    intro h
    have hA : (1 : A) = 0 :=
      CycleQ2SeedCechGlobalGluing.localization_injective ℂ 57 Complex.I s
        (by simpa only [map_one, map_zero] using h)
    exact one_ne_zero hA
  exact ⟨1, 0, h10⟩

/-- The all-polynomial degree comparison rules out the global inverse
forced by emptiness, without any constraint on the degree of that inverse. -/
theorem no_empty_specializedCurve (t : Fin 3 → ℂ)
    [IsEmpty (specializedCurve seed t)] : False := by
  obtain ⟨p, hp⟩ := exists_global_inverse t
  obtain ⟨P0, hP0⟩ := Ideal.Quotient.mk_surjective p
  have hleft (a : Fin 3) : quotient (polynomialLeft (57 : ℂ) a) = 0 := by
    apply CycleQ2SectionDegreeGap.lower_class_zero_of_multiple
      geometricWeight seedIdeal seedIdeal_homogeneous
      (rowPolynomial t a) P0 (polynomialLeft (57 : ℂ) a) 14 10
      (rowPolynomial_homogeneous t a) (polynomialLeft_degree_ten a) (by decide)
    change quotient (rowPolynomial t a) * quotient P0 =
      quotient (polynomialLeft (57 : ℂ) a)
    have hP0' : quotient P0 = p := hP0
    rw [hP0']
    exact hp a
  let s : Finset (Fin 3) := {0}
  have hs : s.Nonempty := Finset.singleton_nonempty 0
  letI := cone_nontrivial s
  have hlocal (a : Fin 3) : (factorData s hs).left a = 0 := by
    rw [left_eq_polynomial, polynomialToCone_apply, hleft a, map_zero]
  have hideal : (factorData s hs).leftIdeal = ⊥ := by
    rw [CycleQ2SeedProjectiveImageTwist.Regrading.leftIdeal_eq_span]
    apply le_antisymm ?_ bot_le
    apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    change (factorData s hs).left a = 0
    exact hlocal a
  have hz : (coneInverse t s hs : Chart s) = 0 := by
    simpa only [hideal, Submodule.mem_bot] using (coneInverse t s hs).property
  have hinverse : coneInverse t s hs = 0 := Subtype.ext hz
  have hone := coneInverse_spec t s hs
  rw [hinverse, map_zero] at hone
  exact zero_ne_one hone

/-- CLOSED SOURCE-LEVEL ENDPOINT: every original fixed complex vector has
nonempty zero locus on the original literal seed surface. -/
theorem seed_specializedCurve_nonempty (t : Fin 3 → ℂ) :
    Nonempty (specializedCurve (seedPoint (57 : ℂ) Complex.I) t) := by
  classical
  by_contra h
  letI : IsEmpty (specializedCurve seed t) := ⟨fun x => h ⟨x⟩⟩
  exact no_empty_specializedCurve t

end CycleQ2SeedSectionNonempty

end

#print axioms CycleQ2SeedSectionNonempty.seed_specializedCurve_nonempty
