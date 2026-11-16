import Proposal.GeometricSeedFermatProj

/-!
# The full invariant-cubic coefficient family of the geometric seed

The parameter ring has one independent variable for every invariant
weighted cubic monomial. The universal equation is the original zero-cubic
seed equation plus the square of that universal cubic. Specializing all
coefficients gives exactly `seedFamily r b`, and every invariant weighted
cubic occurs. In particular zero coefficients give the actual Fermat seed
when `r ^ 3 = 2`, while the coefficients of `smoothB` give the existing
incidence member `smoothF r Complex.I`.

This is the full unnormalized cubic space. The incidence specialization
uses coefficients of `smoothB`, not the existing cubic-section coefficients
of `smoothH`. The latter include the additional subtraction of `i * smoothA`.

Prepared for `fqlx` with OpenAI ChatGPT assistance, following
Ben Diamond's invariant surface-section construction.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedCubicFamily

open MvPolynomial CycleQ2GeometricSeedSmooth
open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
open CycleQ2GeometricIncidenceProj CycleQ2SeedFermatProj

/-- All invariant monomials of weighted degree three. -/
abbrev CubicIndex := FullInvariantIndex 3

/-- Independent affine coefficients for the entire invariant-cubic space. -/
abbrev ParameterRing := MvPolynomial CubicIndex ℂ

/-- The five original weighted variables with universal cubic coefficients. -/
abbrev FamilyPolynomial := MvPolynomial (Fin 5) ParameterRing

def universalCubic : FamilyPolynomial :=
  fullInvariantPolynomial 3 (fun e : CubicIndex => (X e : ParameterRing))

/-- The original seed polynomial family over all invariant-cubic coefficients. -/
def familyEquation (r : ℂ) : FamilyPolynomial :=
  map (algebraMap ℂ ParameterRing) (seedFamily r 0) + universalCubic ^ 2

/-- A complex-valued point of the complete coefficient space. -/
def coefficientEvaluation (c : CubicIndex → ℂ) : ParameterRing →+* ℂ :=
  eval₂Hom (RingHom.id ℂ) c

@[simp] theorem coefficientEvaluation_algebraMap (c : CubicIndex → ℂ) (z : ℂ) :
    coefficientEvaluation c (algebraMap ℂ ParameterRing z) = z := by
  change eval₂Hom (RingHom.id ℂ) c (C z) = z
  simp only [eval₂Hom_C, RingHom.id_apply]

@[simp] theorem coefficientEvaluation_variable (c : CubicIndex → ℂ) (e : CubicIndex) :
    coefficientEvaluation c (X e) = c e :=
  eval₂Hom_X' (RingHom.id ℂ) c e

theorem coefficientEvaluation_comp_algebraMap (c : CubicIndex → ℂ) :
    (coefficientEvaluation c).comp (algebraMap ℂ ParameterRing) = RingHom.id ℂ := by
  ext z
  exact coefficientEvaluation_algebraMap c z

/-- Specialization of the universal cubic preserves every coefficient. -/
theorem coefficientEvaluation_universalCubic (c : CubicIndex → ℂ) :
    map (coefficientEvaluation c) universalCubic = fullInvariantPolynomial 3 c := by
  rw [universalCubic, map_fullInvariantPolynomial]
  congr 1
  funext e
  exact coefficientEvaluation_variable c e

theorem coefficientEvaluation_constantPolynomial (c : CubicIndex → ℂ)
    (p : SeedPolynomial) :
    map (coefficientEvaluation c) (map (algebraMap ℂ ParameterRing) p) = p := by
  rw [map_map, coefficientEvaluation_comp_algebraMap, map_id]

/-- The factorized original family is exactly the zero-cubic member plus `b²`. -/
theorem seedFamily_eq_zero_add_square (r : ℂ) (b : SeedPolynomial) :
    seedFamily r b = seedFamily r 0 + b ^ 2 := by
  rw [seedFamily_expanded, seedFamily_zero]

/-- Every coefficient specialization gives the literal original seed family. -/
theorem specialize_familyEquation (r : ℂ) (c : CubicIndex → ℂ) :
    map (coefficientEvaluation c) (familyEquation r) =
      seedFamily r (fullInvariantPolynomial 3 c) := by
  rw [familyEquation, map_add, map_pow, coefficientEvaluation_constantPolynomial,
    coefficientEvaluation_universalCubic,
    seedFamily_eq_zero_add_square r (fullInvariantPolynomial 3 c)]

/-- Zero coefficients recover the exact existing zero-cubic equation. -/
theorem specialize_zero (r : ℂ) :
    map (coefficientEvaluation (fun _ => 0)) (familyEquation r) = seedFamily r 0 := by
  simpa [fullInvariantPolynomial] using specialize_familyEquation r (fun _ => 0)

/-- The actual coefficients of an invariant cubic; no subset is selected. -/
def coefficientsOf (b : SeedPolynomial) : CubicIndex → ℂ :=
  fun e => b.coeff (fullExponentOf e.val)

theorem coefficientsOf_polynomial (b : SeedPolynomial) (hb : HG b (3, 0)) :
    fullInvariantPolynomial 3 (coefficientsOf b) = b :=
  fullInvariantPolynomial_of_homogeneous hb

/-- Every invariant cubic, including those outside a normalized chart, occurs. -/
theorem specialize_of_homogeneous (r : ℂ) (b : SeedPolynomial) (hb : HG b (3, 0)) :
    map (coefficientEvaluation (coefficientsOf b)) (familyEquation r) = seedFamily r b := by
  rw [specialize_familyEquation, coefficientsOf_polynomial b hb]

/-- The incidence member uses the coefficients of `smoothB` itself. -/
def incidenceCoefficients : CubicIndex → ℂ := coefficientsOf smoothB

theorem incidenceCoefficients_polynomial :
    fullInvariantPolynomial 3 incidenceCoefficients = (smoothB : SeedPolynomial) :=
  coefficientsOf_polynomial smoothB smoothB_homogeneous

/-- The original incidence seed and the Fermat seed belong to this same full family. -/
theorem specialize_incidence (r : ℂ) :
    map (coefficientEvaluation incidenceCoefficients) (familyEquation r) =
      smoothF r Complex.I := by
  rw [specialize_familyEquation, incidenceCoefficients_polynomial,
    seedFamily_at_incidence_seed]

theorem universalCubic_bihomogeneous : HG universalCubic (3, 0) :=
  fullInvariantPolynomial_homogeneous 3 (fun e : CubicIndex => (X e : ParameterRing))

theorem universalCubic_homogeneous :
    universalCubic.IsWeightedHomogeneous geometricWeight 3 := by
  apply homogeneous_of_character
  exact universalCubic_bihomogeneous

theorem constantSeedEquation_homogeneous (r : ℂ) :
    (map (algebraMap ℂ ParameterRing) (seedFamily r 0)).IsWeightedHomogeneous
      geometricWeight 6 := by
  intro e he
  apply seedEquation_homogeneous r
  intro hz
  apply he
  rw [coeff_map, hz, map_zero]

/-- The actual universal defining equation has weighted degree six. -/
theorem familyEquation_homogeneous (r : ℂ) :
    (familyEquation r).IsWeightedHomogeneous geometricWeight 6 := by
  apply (constantSeedEquation_homogeneous r).add
  simpa using universalCubic_homogeneous.pow 2

end CycleQ2SeedCubicFamily

end

#print axioms CycleQ2SeedCubicFamily.specialize_of_homogeneous
#print axioms CycleQ2SeedCubicFamily.specialize_zero
#print axioms CycleQ2SeedCubicFamily.specialize_incidence
#print axioms CycleQ2SeedCubicFamily.familyEquation_homogeneous
