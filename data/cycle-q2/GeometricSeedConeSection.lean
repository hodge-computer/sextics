import Proposal.GeometricEmptySectionRows
import Proposal.GeometricSeedSectionInverse

/-!
# The actual empty seed section would have a global inverse in its cone ring

The literal PointSurface at r=57 is identified with the original seed
quotient. On its three original coordinate localizations, emptiness forces
unit row ideals, hence inverse elements in the actual linkage ideals.
Their products with the three rows are the original left generators.
Those equations and the unit row ideals force compatibility under the
original restriction maps. The existing augmented H0 theorem then glues
these elements in the original seed quotient, with no grading premise.

Source-only draft. Not elaborated, compiled, or kernel-replayed.
Prepared for fqlx with OpenAI ChatGPT assistance, 15 November 2026.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedConeSection

open MvPolynomial Matrix
open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations CycleQ2IncidenceMonomials
  CycleQ2IncidenceUniversalChart CycleQ2IncidenceGenericPointSemantics
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2IncidenceImageLine
  CycleQ2GeometricIncidenceProj CycleQ2GeometricSurfaceAdjunction
  CycleQ2GeometricSurfaceCoordinates CycleQ2RegularSeedSection
  CycleQ2UniversalCurveCartier CycleQ2SpecializedProjectiveCurve
  CycleQ2SpecializedSectionIdeal
  CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechLocalizedBasis CycleQ2SegreFactorSequence
  CycleQ2SegreFactorChartExact CycleQ2SeedFactorHomogeneous
  CycleQ2SeedSectionInverse

abbrev seed : ParameterIndex → ℂ := seedPoint (57 : ℂ) Complex.I
abbrev A := SeedRing (57 : ℂ) Complex.I
abbrev P := MvPolynomial (Fin 5) ℂ

def quotient : P →ₐ[ℂ] A :=
  Ideal.Quotient.mkₐ ℂ (equationsIdeal (smoothH Complex.I) (smoothF 57 Complex.I))

/-- This is the identity-on-polynomials comparison of the two actual ideals. -/
def literalToSeed : PointSurface seed ≃ₐ[ℂ] A :=
  literalPointSurfaceEquiv.trans (seedRingEquiv 57)

@[simp] theorem literalToSeed_polynomial (p : P) :
    literalToSeed (Ideal.Quotient.mk (pointEquations seed) p) = quotient p := by
  rw [literalToSeed, AlgEquiv.trans_apply,
    literalPointSurfaceEquiv_polynomial, seedRingEquiv_quotient]
  rfl

/-- At the retained seed every matrix perturbation coefficient is zero. -/
theorem pointMatrixPolynomial_seed (a b : Fin 3) :
    pointMatrixPolynomial seed a b = rawSeedMatrix (57 : ℂ) a b := by
  change incidenceMatrix (57 : ℂ) (fun _ _ _ => 0) a b = _
  rw [incidenceMatrix_zero]

def toCone (s : Finset (Fin 3)) : PointSurface seed →ₐ[ℂ] Chart s :=
  (IsScalarTower.toAlgHom ℂ A (Chart s)).comp literalToSeed.toAlgHom

def polynomialToCone (s : Finset (Fin 3)) : P →ₐ[ℂ] Chart s :=
  (IsScalarTower.toAlgHom ℂ A (Chart s)).comp quotient

@[simp] theorem polynomialToCone_apply (s : Finset (Fin 3)) (p : P) :
    polynomialToCone s p = algebraMap A (Chart s) (quotient p) := rfl

theorem toCone_pivot (s : Finset (Fin 3)) (hs : s.Nonempty)
    (p : CycleQ2SegreCech.Chart) :
    toCone s (basePivot seed p) = (factorData s hs).matrix p.1 p.2 := by
  rw [basePivot_eq_quotient]
  change algebraMap A (Chart s)
    (literalToSeed (Ideal.Quotient.mk (pointEquations seed)
      (pointMatrixPolynomial seed p.1 p.2))) = _
  rw [literalToSeed_polynomial, pointMatrixPolynomial_seed]
  rfl

/-- The original rows, before dividing by any projective coordinate. -/
def rowPolynomial (t : Fin 3 → ℂ) (a : Fin 3) : P :=
  ∑ j, C (t j) * rawSeedMatrix (57 : ℂ) a j

def row (t : Fin 3 → ℂ) (s : Finset (Fin 3)) (a : Fin 3) : Chart s :=
  polynomialToCone s (rowPolynomial t a)

theorem matrixRow_eq (t : Fin 3 → ℂ) (s : Finset (Fin 3)) (hs : s.Nonempty)
    (a : Fin 3) :
    ((factorData s hs).matrix *ᵥ (fun j => algebraMap ℂ (Chart s) (t j))) a =
      row t s a := by
  simp only [Matrix.mulVec, dotProduct, row, rowPolynomial,
    map_sum, map_mul, MvPolynomial.algHom_C]
  apply Finset.sum_congr rfl
  intro j _
  change (factorData s hs).matrix a j * algebraMap ℂ (Chart s) (t j) =
    algebraMap ℂ (Chart s) (t j) * (factorData s hs).matrix a j
  exact mul_comm _ _

theorem toCone_equation (t : Fin 3 → ℂ) (s : Finset (Fin 3))
    (hs : s.Nonempty) (a : Fin 3) :
    toCone s (constantEquation seed t a) = row t s a := by
  rw [constantEquation]
  simp only [map_sum, map_smul, toCone_pivot s hs]
  rw [← matrixRow_eq t s hs a]
  simp only [Matrix.mulVec, dotProduct, Algebra.smul_def]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem left_eq_polynomial (s : Finset (Fin 3)) (hs : s.Nonempty) (a : Fin 3) :
    (factorData s hs).left a = polynomialToCone s (polynomialLeft (57 : ℂ) a) := rfl

def restrict {s u : Finset (Fin 3)} (h : s ⊆ u) : Chart s →+* Chart u :=
  CycleQ2SeedCechRestrictions.restriction ℂ 57 Complex.I h

@[simp] theorem restrict_polynomial {s u : Finset (Fin 3)} (h : s ⊆ u) (p : P) :
    restrict h (polynomialToCone s p) = polynomialToCone u p :=
  CycleQ2SeedCechRestrictions.restriction_algebraMap ℂ 57 Complex.I h (quotient p)

@[simp] theorem restrict_row (t : Fin 3 → ℂ) {s u : Finset (Fin 3)} (h : s ⊆ u)
    (a : Fin 3) : restrict h (row t s a) = row t u a :=
  restrict_polynomial h (rowPolynomial t a)

section Empty

variable (t : Fin 3 → ℂ) [IsEmpty (specializedCurve seed t)]

/-- All primes are covered by the original matrix entries, so actual
emptiness forces a Bezout identity on each original cone coordinate chart. -/
theorem row_span (s : Finset (Fin 3)) (hs : s.Nonempty) :
    Ideal.span (Set.range (row t s)) = ⊤ := by
  have h := CycleQ2EmptySectionRows.row_span_of_isEmpty seed t
    seed_original_equations seed_leading_unit (toCone s) (by
      simpa only [toCone_pivot s hs] using (factorData s hs).entries_generate)
  simpa only [toCone_equation t s hs] using h

theorem exists_cone_inverse (s : Finset (Fin 3)) (hs : s.Nonempty) :
    ∃! x : (factorData s hs).leftIdeal,
      sectionFunctional (factorData s hs)
        (fun j => algebraMap ℂ (Chart s) (t j)) x = 1 := by
  have hmem : (1 : Chart s) ∈ Ideal.span (Set.range (row t s)) := by
    rw [row_span t s hs]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  apply exists_unique_inverse_of_rows (factorData s hs)
    (fun j => algebraMap ℂ (Chart s) (t j)) c
  simpa only [matrixRow_eq t s hs] using hc

def coneInverse (s : Finset (Fin 3)) (hs : s.Nonempty) :
    (factorData s hs).leftIdeal :=
  Classical.choose (exists_cone_inverse t s hs)

theorem coneInverse_spec (s : Finset (Fin 3)) (hs : s.Nonempty) :
    sectionFunctional (factorData s hs)
      (fun j => algebraMap ℂ (Chart s) (t j)) (coneInverse t s hs) = 1 :=
  (Classical.choose_spec (exists_cone_inverse t s hs)).1

/-- Each inverse solves three literal equations in the original localization. -/
theorem row_mul_coneInverse (s : Finset (Fin 3)) (hs : s.Nonempty) (a : Fin 3) :
    row t s a * (coneInverse t s hs : Chart s) =
      polynomialToCone s (polynomialLeft (57 : ℂ) a) := by
  have h := congrArg (fun z : (factorData s hs).leftIdeal => (z : Chart s))
    (CycleQ2SectionInverseIdeal.recover (factorData s hs).leftIdeal
      (sectionFunctional (factorData s hs) (fun j => algebraMap ℂ (Chart s) (t j)))
      (coneInverse t s hs) (coneInverse_spec t s hs) (leftElement (factorData s hs) a))
  change sectionFunctional (factorData s hs)
    (fun j => algebraMap ℂ (Chart s) (t j)) (leftElement (factorData s hs) a) *
      (coneInverse t s hs : Chart s) = (factorData s hs).left a at h
  rw [sectionFunctional_left, matrixRow_eq, left_eq_polynomial] at h
  exact h

/-- The products with spanning rows determine restriction uniquely. No
functional base-change comparison or grading assertion is assumed. -/
theorem coneInverse_restrict {s u : Finset (Fin 3)}
    (hs : s.Nonempty) (hu : u.Nonempty) (h : s ⊆ u) :
    restrict h (coneInverse t s hs : Chart s) = (coneInverse t u hu : Chart u) := by
  apply CycleQ2EmptySectionRows.scalar_eq_of_row_products (row t u)
    (row_span t u hu)
  intro a
  calc
    row t u a * restrict h (coneInverse t s hs : Chart s) =
        restrict h (row t s a * (coneInverse t s hs : Chart s)) := by
      rw [map_mul, restrict_row]
    _ = restrict h (polynomialToCone s (polynomialLeft (57 : ℂ) a)) := by
      rw [row_mul_coneInverse]
    _ = polynomialToCone u (polynomialLeft (57 : ℂ) a) := restrict_polynomial h _
    _ = row t u a * (coneInverse t u hu : Chart u) :=
      (row_mul_coneInverse t u hu a).symm

def inverseSections : CycleQ2SeedCechGlobalGluing.Sections ℂ (57 : ℂ) Complex.I :=
  fun i => (coneInverse t {i} (Finset.singleton_nonempty i) : Chart {i})

theorem inverseSections_compatible :
    CycleQ2SeedCechGlobalGluing.Compatible ℂ (57 : ℂ) Complex.I (inverseSections t) := by
  intro i j
  change restrict (show ({i} : Finset (Fin 3)) ⊆ {i,j} by simp) _ =
    restrict (show ({j} : Finset (Fin 3)) ⊆ {i,j} by simp) _
  rw [coneInverse_restrict t (Finset.singleton_nonempty i) (by simp),
    coneInverse_restrict t (Finset.singleton_nonempty j) (by simp)]

/-- The inverses glue in the original ring, not an enlarged function field. -/
theorem exists_global_inverse :
    ∃ p : A, ∀ a : Fin 3,
      quotient (rowPolynomial t a) * p = quotient (polynomialLeft (57 : ℂ) a) := by
  obtain ⟨p, hp, _⟩ := CycleQ2SeedCechGlobalGluing.existsUnique_gluing
    ℂ (57 : ℂ) Complex.I (inverseSections t) (inverseSections_compatible t)
  refine ⟨p, ?_⟩
  intro a
  apply CycleQ2SeedCechGlobalGluing.localization_injective ℂ (57 : ℂ) Complex.I {0}
  rw [map_mul, hp 0]
  exact row_mul_coneInverse t {0} (Finset.singleton_nonempty 0) a

end Empty
end CycleQ2SeedConeSection

end

#print axioms CycleQ2SeedConeSection.toCone_pivot
#print axioms CycleQ2SeedConeSection.row_span
#print axioms CycleQ2SeedConeSection.coneInverse_restrict
#print axioms CycleQ2SeedConeSection.exists_global_inverse
