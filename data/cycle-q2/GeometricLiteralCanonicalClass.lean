import Proposal.GeometricCurveRegularPair
import Proposal.GeometricProjectiveCanonicalH1
import Mathlib.Tactic.LinearCombination

/-!
# A nonzero differential-cohomology class at the literal seed

A finite Gaussian coefficient functional kills arbitrary polynomial multiples
of the actual four homogeneous generators at `(r, θ) = (57, 1)`. Its nonzero
value on `x₀³ x₂³ x₃³`, together with the proved denominator regular pair,
detects the existing homogeneous Čech class. The actual Mayer-Vietoris map and
the constructed canonical-sheaf isomorphism then give a nonzero class in the
actual derived first cohomology of the differential sheaf.

The calculation uses 24 coefficients, with no rank oracle or geometric
comparison hypothesis. It does not identify a geometric Serre-duality trace.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricLiteralCanonicalClass

open MvPolynomial CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2SeedTrace CycleQ2SeedCechTheta CycleQ2NormalConnecting
  CycleQ2GeometricKoszulTrace CycleQ2GeometricProjectiveCurve
  CycleQ2GeometricProjectiveCanonical
  CycleQ2GeometricProjectiveCanonicalH1 CycleQ2GeometricDifferentialSheaf

private def exponent (a b c d : ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![a, b, c, d]

private theorem exponent_le_iff (a b c d A B C D : ℕ) :
    exponent a b c d ≤ exponent A B C D ↔ a ≤ A ∧ b ≤ B ∧ c ≤ C ∧ d ≤ D := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3⟩
  · rintro ⟨ha, hb, hc, hd⟩ j
    fin_cases j <;> assumption

private theorem exponent_eq_iff (a b c d A B C D : ℕ) :
    exponent a b c d = exponent A B C D ↔ a = A ∧ b = B ∧ c = C ∧ d = D := by
  constructor
  · intro h
    exact ⟨congrArg (fun e => e 0) h, congrArg (fun e => e 1) h,
      congrArg (fun e => e 2) h, congrArg (fun e => e 3) h⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

private theorem exponent_sub (a b c d A B C D : ℕ) :
    exponent A B C D - exponent a b c d = exponent (A-a) (B-b) (C-c) (D-d) := by
  ext j
  fin_cases j <;> rfl

private def term (a b c d : ℕ) (z : ℂ) : Poly := monomial (exponent a b c d) z

private theorem term_eq (a b c d : ℕ) (z : ℂ) :
    term a b c d z = C z * X 0 ^ a * X 1 ^ b * X 2 ^ c * X 3 ^ d := by
  have he : exponent a b c d = Finsupp.single 0 a + Finsupp.single 1 b +
      Finsupp.single 2 c + Finsupp.single 3 d := by
    ext j
    fin_cases j <;> simp [exponent]
  simp only [term, X_pow_eq_monomial, C_apply, monomial_mul, mul_one, zero_add, he]

private theorem coefficient_mul_term (a b c d A B C D : ℕ) (z : ℂ) (p : Poly) :
    coeff (exponent A B C D) (p * term a b c d z) =
      if a ≤ A ∧ b ≤ B ∧ c ≤ C ∧ d ≤ D then
        coeff (exponent (A-a) (B-b) (C-c) (D-d)) p * z else 0 := by
  simp only [term, coeff_mul_monomial', exponent_le_iff, exponent_sub]

private theorem coefficient_term (a b c d A B C D : ℕ) (z : ℂ) :
    coeff (exponent A B C D) (term a b c d z) =
      if a = A ∧ b = B ∧ c = C ∧ d = D then z else 0 := by
  simp only [term, coeff_monomial, exponent_eq_iff]

/-- The explicit coefficient certificate on the original polynomial ring. -/
def literalTraceLinear : Poly →ₗ[ℂ] ℂ :=
    (57 + 171 * Complex.I) • lcoeff ℂ (exponent 0 0 0 9) +
    (4 * Complex.I) • lcoeff ℂ (exponent 0 0 1 8) +
    (-114 + -114 * Complex.I) • lcoeff ℂ (exponent 0 0 3 6) +
    (-2 + -2 * Complex.I) • lcoeff ℂ (exponent 0 1 2 6) +
    (-4 + 4 * Complex.I) • lcoeff ℂ (exponent 0 5 3 1) +
    (4 + 12 * Complex.I) • lcoeff ℂ (exponent 0 7 2 0) +
    (8 + 8 * Complex.I) • lcoeff ℂ (exponent 0 8 0 1) +
    (-456 + -456 * Complex.I) • lcoeff ℂ (exponent 0 9 0 0) +
    (114 * Complex.I) • lcoeff ℂ (exponent 1 0 1 7) +
    (-2 + -2 * Complex.I) • lcoeff ℂ (exponent 1 0 2 6) +
    (-2 + -2 * Complex.I) • lcoeff ℂ (exponent 1 1 0 7) +
    4 • lcoeff ℂ (exponent 1 1 3 4) +
    (-4 + -4 * Complex.I) • lcoeff ℂ (exponent 1 4 3 1) +
    (228 + 228 * Complex.I) • lcoeff ℂ (exponent 1 5 3 0) +
    (-4 + 4 * Complex.I) • lcoeff ℂ (exponent 1 6 2 0) +
    (-4 + 4 * Complex.I) • lcoeff ℂ (exponent 1 7 0 1) +
    (684 + -684 * Complex.I) • lcoeff ℂ (exponent 1 8 0 0) +
    (-114 + -114 * Complex.I) • lcoeff ℂ (exponent 2 0 2 5) +
    (-228 + 228 * Complex.I) • lcoeff ℂ (exponent 2 4 3 0) +
    (456 + 456 * Complex.I) • lcoeff ℂ (exponent 2 7 0 0) +
    (-114 + -114 * Complex.I) • lcoeff ℂ (exponent 3 0 0 6) +
    228 • lcoeff ℂ (exponent 3 0 3 3) +
    (-228 + -228 * Complex.I) • lcoeff ℂ (exponent 3 3 3 0) +
    (-228 + 228 * Complex.I) • lcoeff ℂ (exponent 3 6 0 0)

private theorem quadric_terms : relation 57 0 =
    term 2 0 0 0 1 + term 0 1 0 1 (-57) := by
  simp [relation, term_eq]
  ring

private theorem cubic_terms : curveH 1 =
    term 0 0 0 3 (1-Complex.I) + term 0 0 3 0 1 +
    term 0 1 1 1 1 + term 1 0 1 1 1 + term 1 2 0 0 1 +
    term 0 3 0 0 (-Complex.I) + term 3 0 0 0 1 := by
  simp [curveH, h, b, term_eq]
  ring

private theorem firstQuartic_terms : firstQuartic 57 = term 0 2 0 2 9747 := by
  have hcoef : (3 : ℂ) * 57 ^ 2 = 9747 := by norm_num
  rw [firstQuartic, hcoef, term_eq]
  simp [CycleQ2SeedCech.curveA, mul_pow, mul_assoc]

private theorem secondQuartic_terms : secondQuartic = term 0 0 4 0 3 := by
  simp [secondQuartic, CycleQ2SeedCech.curveB, term_eq]

/-- The certificate kills every multiple of the actual quadric. -/
theorem literalTraceLinear_mul_quadric (p : Poly) :
    literalTraceLinear (p * relation 57 0) = 0 := by
  rw [quadric_terms, mul_add]
  simp only [literalTraceLinear, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, smul_eq_mul, coeff_add, coefficient_mul_term]
  norm_num
  ring

/-- The certificate kills every multiple of the actual cubic, including
its nonzero `x₀³` deformation term. -/
theorem literalTraceLinear_mul_cubic (p : Poly) :
    literalTraceLinear (p * curveH 1) = 0 := by
  rw [cubic_terms]
  simp only [mul_add, literalTraceLinear, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, smul_eq_mul, coeff_add, coefficient_mul_term]
  norm_num
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem literalTraceLinear_mul_firstQuartic (p : Poly) :
    literalTraceLinear (p * firstQuartic 57) = 0 := by
  rw [firstQuartic_terms]
  norm_num [literalTraceLinear, coefficient_mul_term]

theorem literalTraceLinear_mul_secondQuartic (p : Poly) :
    literalTraceLinear (p * secondQuartic) = 0 := by
  rw [secondQuartic_terms]
  norm_num [literalTraceLinear, coefficient_mul_term]

/-- Arbitrary ideal membership is annihilated, without a degree restriction. -/
theorem literalTraceLinear_zero_of_mem (p : Poly) (hp : p ∈ fourGeneratorIdeal 57 1) :
    literalTraceLinear p = 0 := by
  obtain ⟨a, q₁, hq₁, he₁⟩ := Ideal.mem_span_insert.mp hp
  obtain ⟨b, q₂, hq₂, he₂⟩ := Ideal.mem_span_insert.mp hq₁
  obtain ⟨c, q₃, hq₃, he₃⟩ := Ideal.mem_span_insert.mp hq₂
  obtain ⟨d, he₄⟩ := Ideal.mem_span_singleton'.mp hq₃
  rw [he₁, he₂, he₃, ← he₄]
  simp only [map_add, literalTraceLinear_mul_quadric, literalTraceLinear_mul_cubic,
    literalTraceLinear_mul_firstQuartic, literalTraceLinear_mul_secondQuartic, add_zero]

/-- The paired literal numerator in the four-variable curve ring. -/
def literalNumerator : Poly := X 0 ^ 3 * X 2 ^ 3 * X 3 ^ 3

theorem literalNumerator_homogeneous : literalNumerator.IsHomogeneous 9 :=
  ((isHomogeneous_X ℂ (0 : Fin 4)).pow 3 |>.mul
    ((isHomogeneous_X ℂ (2 : Fin 4)).pow 3)).mul
      ((isHomogeneous_X ℂ (3 : Fin 4)).pow 3)

theorem literalTraceLinear_numerator : literalTraceLinear literalNumerator = 228 := by
  have hp : literalNumerator = term 3 0 3 3 1 := by simp [literalNumerator, term_eq]
  rw [hp]
  norm_num [literalTraceLinear, coefficient_term]

theorem literalNumerator_not_mem : literalNumerator ∉ fourGeneratorIdeal 57 1 := by
  intro hp
  have h := literalTraceLinear_zero_of_mem literalNumerator hp
  rw [literalTraceLinear_numerator] at h
  norm_num at h

/-- The actual homogeneous Čech class at the literal seed. -/
def literalCechClass : DegreeOneCech 57 1 :=
  degreeNineCechClass 57 1 literalNumerator literalNumerator_homogeneous

theorem literalCechClass_ne_zero : literalCechClass ≠ 0 := by
  intro hz
  exact literalNumerator_not_mem
    ((CycleQ2GeometricCurveRegularPair.At.degreeNineCechClass_zero_iff_fourGeneratorIdeal
      57 1 (by norm_num) literalNumerator literalNumerator_homogeneous).mp hz)

local instance literalSheavesHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (projectiveCurve 57 1)) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- The closed canonical isomorphism, forgetting only module structure. -/
def literalCanonicalAdditiveIso : differentialAdditiveSheaf 57 1 ≅ degreeOneSheaf 57 1 :=
  (SheafOfModules.toSheaf (ringSheaf (projectiveCurve 57 1).sheaf)).mapIso
    literalProjectiveCanonicalIso

/-- Functorial transport on actual derived first cohomology. -/
def literalCanonicalH1Equiv : ProjectiveSheafH1 57 1 ≃+ DifferentialSheafH1 57 1 :=
  (((Sheaf.cohomologyPresheafFunctor
      (Opens.grothendieckTopology (projectiveCurve 57 1)) 1).mapIso
        literalCanonicalAdditiveIso).app (op ⊤)).addCommGroupIsoToAddEquiv.symm

/-- A concrete nonzero class in the literal differential-sheaf cohomology. -/
def literalCanonicalClass : DifferentialSheafH1 57 1 :=
  literalCanonicalH1Equiv (degreeOneToProjectiveH1 57 1 (by norm_num) literalCechClass)

theorem literalCanonicalClass_ne_zero : literalCanonicalClass ≠ 0 := by
  intro hz
  apply literalCechClass_ne_zero
  apply degreeOneToProjectiveH1_injective 57 1 (by norm_num)
  apply literalCanonicalH1Equiv.injective
  simpa only [literalCanonicalClass, map_zero] using hz

theorem literalDifferentialSheafH1_nontrivial : Nontrivial (DifferentialSheafH1 57 1) :=
  ⟨⟨literalCanonicalClass, 0, literalCanonicalClass_ne_zero⟩⟩

#print axioms literalTraceLinear_zero_of_mem
#print axioms literalNumerator_not_mem
#print axioms literalCechClass_ne_zero
#print axioms literalCanonicalH1Equiv
#print axioms literalCanonicalClass_ne_zero
#print axioms literalDifferentialSheafH1_nontrivial

end CycleQ2GeometricLiteralCanonicalClass
end

/-!
## A literal cubic in seven cohomology kernels with a nonzero detector

The generic arithmetic identities in the following namespace reproduce the
`Arithmetic` section of `GeometricExplicitTangent.lean`, with the same selected
cubic and seven tests. They are proved here independently so this actual
cohomology calculation uses only the checked projective and polynomial imports.

The classes are obtained from actual homogeneous Čech representatives and the
constructed differential-sheaf isomorphism at `(r, θ) = (57, 1)`. Their geometric
interpretation as a normal-sequence, Noether–Lefschetz, or cylinder differential
is a separate comparison, not a premise or conclusion of this calculation.
-/

noncomputable section
namespace CycleQ2GeometricLiteralDirection

open MvPolynomial
open scoped BigOperators

section Arithmetic
variable {R : Type*} [CommRing R]

def sparseH (ι x0 x1 x2 x3 : R) : R :=
  x0 ^ 3 + x0 * x1 ^ 2 + x0 * x2 * x3 + x1 * x2 * x3 +
    x2 ^ 3 + x3 ^ 3 - ι * (x1 ^ 3 + x3 ^ 3)

def sparseK (ι x0 x1 x2 x3 : R) : R :=
  x0 ^ 3 + x0 * x1 ^ 2 + x0 * x2 * x3 + x1 * x2 * x3 +
    x2 ^ 3 + x3 ^ 3 + ι * (x1 ^ 3 + x3 ^ 3)

def chosenCubic (ι x0 x1 : R) : R := ι * x0 ^ 2 * x1 + (ι - 1) * x0 ^ 3

def reducedTest (x0 x1 x2 x3 : R) : Fin 7 → R :=
  ![-x2 ^ 3, x2 * x3 ^ 2, x1 * x2 ^ 2, x1 ^ 2 * x3,
    x0 * x2 ^ 2, x0 * x1 * x3, x0 ^ 2 * x3]

def reducedRelations (ι x0 x1 x2 x3 : R) : Fin 4 → R :=
  ![x1 ^ 2 * x3 ^ 2, x2 ^ 4, x0 ^ 2 - 57 * x1 * x3,
    sparseH ι x0 x1 x2 x3]

def bezout0 (ι x0 x1 x2 x3 : R) : Fin 4 → R :=
  ![-6498 * ι * x0 ^ 2 * x2 ^ 3 - 6498 * ι * x0 * x1 * x2 ^ 3 - 114 * ι * x0 * x2 ^ 4 - 6498 * ι * x1 ^
      2 * x2 ^ 3 - 57 * ι * x1 * x2 ^ 4 - 114 * ι * x2 ^ 3 * x3 ^ 2 - 57 * x0 * x2 ^ 4,
-ι * x0 ^ 4 * x3 - 2 * ι * x0 ^ 3 * x1 * x3 - ι * x0 ^ 3 * x2 ^ 2 - ι * x0 ^ 2 * x1 ^ 2 * x3 - ι *
      x0 ^ 2 * x1 * x2 ^ 2 - 57 * ι * x0 ^ 2 * x1 * x3 ^ 2 - 57 * ι * x0 * x1 * x2 ^ 2 * x3 - 57 * ι
      * x1 ^ 2 * x2 ^ 2 * x3 + x0 ^ 4 * x3 + x0 ^ 3 * x1 * x3 + x0 ^ 3 * x2 ^ 2 - 57 * x0 ^ 2 * x1 *
      x3 ^ 2 - 57 * x0 * x1 * x2 ^ 2 * x3,
-ι * x0 ^ 4 * x2 ^ 3 - ι * x0 ^ 3 * x1 * x2 ^ 3 - ι * x0 ^ 2 * x1 ^ 2 * x2 ^ 3 - 114 * ι * x0 ^ 2 *
      x1 * x2 ^ 3 * x3 - 114 * ι * x0 * x1 ^ 2 * x2 ^ 3 * x3 - 114 * ι * x1 ^ 3 * x2 ^ 3 * x3 - ι *
      x1 * x2 ^ 3 * x3 ^ 3 + x0 ^ 4 * x2 ^ 3 + x0 ^ 2 * x1 ^ 2 * x2 ^ 3 + x0 * x1 ^ 3 * x2 ^ 3 + 2 *
      x0 * x2 ^ 3 * x3 ^ 3 + x1 ^ 4 * x2 ^ 3 + x1 * x2 ^ 3 * x3 ^ 3,
57 * ι * x0 * x1 * x2 ^ 3 * x3 + 57 * ι * x1 ^ 2 * x2 ^ 3 * x3 + 57 * x0 * x1 * x2 ^ 3 * x3]

def bezout1 (ι x0 x1 x2 x3 : R) : Fin 4 → R :=
  ![ι * x0 ^ 4 * x2 + 57 * ι * x0 ^ 3 * x2 * x3 + 57 * ι * x0 ^ 2 * x1 * x2 * x3 + ι * x0 ^ 2 * x2 ^ 2 *
      x3 + 6498 * ι * x0 ^ 2 * x2 * x3 ^ 2 - 57 * ι * x0 * x1 ^ 2 * x2 * x3 + 171 * ι * x0 * x2 ^ 2
      * x3 ^ 2 + 6498 * ι * x2 ^ 2 * x3 ^ 3 + 57 * ι * x2 * x3 ^ 4 - x0 ^ 4 * x2 - x0 ^ 3 * x1 * x2
      - x0 ^ 2 * x1 ^ 2 * x2 + 57 * x0 ^ 2 * x1 * x2 * x3 + 57 * x0 * x1 ^ 2 * x2 * x3 - 57 * x2 *
      x3 ^ 4,
ι * x0 ^ 3 * x3 ^ 2 + ι * x0 ^ 2 * x1 * x3 ^ 2 + 57 * ι * x0 * x1 * x3 ^ 3 - x0 ^ 3 * x3 ^ 2 + 57 *
      x0 * x1 * x3 ^ 3,
ι * x0 ^ 4 * x2 * x3 ^ 2 + ι * x0 ^ 3 * x1 * x2 * x3 ^ 2 + 114 * ι * x0 ^ 2 * x1 * x2 * x3 ^ 3 + ι *
      x0 ^ 2 * x2 ^ 2 * x3 ^ 3 + 2 * ι * x0 * x1 * x2 ^ 2 * x3 ^ 3 + 114 * ι * x1 * x2 ^ 2 * x3 ^ 4
      + ι * x1 * x2 * x3 ^ 5 - x0 ^ 4 * x2 * x3 ^ 2 - x0 ^ 2 * x2 ^ 2 * x3 ^ 3 - x0 * x1 * x2 ^ 2 *
      x3 ^ 3 - 2 * x0 * x2 * x3 ^ 5 - x1 * x2 * x3 ^ 5,
-57 * ι * x0 * x1 * x2 * x3 ^ 3 - 57 * x0 * x1 * x2 * x3 ^ 3]

def bezout2 (ι x0 x1 x2 x3 : R) : Fin 4 → R :=
  ![6498 * ι * x0 ^ 2 * x1 * x2 ^ 2 + 114 * ι * x0 ^ 2 * x2 ^ 3 + ι * x0 ^ 2 * x2 ^ 2 * x3 + 6498 * ι *
      x0 * x1 ^ 2 * x2 ^ 2 + 228 * ι * x0 * x1 * x2 ^ 3 + 6498 * ι * x1 ^ 3 * x2 ^ 2 + 114 * ι * x1
      ^ 2 * x2 ^ 3 + 57 * ι * x1 * x2 ^ 2 * x3 ^ 2 - x0 ^ 2 * x2 ^ 2 * x3 + 57 * x1 * x2 ^ 2 * x3 ^
      2,
ι * x0 ^ 3 * x1 * x2 + ι * x0 ^ 2 * x1 ^ 2 * x2 + 57 * ι * x0 * x1 ^ 2 * x2 * x3 + 57 * ι * x1 ^ 3 *
      x2 * x3 - x0 ^ 3 * x1 * x2 + 57 * x0 * x1 ^ 2 * x2 * x3,
ι * x0 ^ 4 * x1 * x2 ^ 2 + ι * x0 ^ 3 * x1 ^ 2 * x2 ^ 2 + ι * x0 ^ 2 * x1 ^ 3 * x2 ^ 2 + 114 * ι *
      x0 ^ 2 * x1 ^ 2 * x2 ^ 2 * x3 + ι * x0 ^ 2 * x1 * x2 ^ 3 * x3 + 114 * ι * x0 * x1 ^ 3 * x2 ^ 2
      * x3 + 2 * ι * x0 * x1 ^ 2 * x2 ^ 3 * x3 + 114 * ι * x1 ^ 4 * x2 ^ 2 * x3 + ι * x1 ^ 3 * x2 ^
      3 * x3 - x0 ^ 4 * x1 * x2 ^ 2 - x0 ^ 2 * x1 ^ 3 * x2 ^ 2 - x0 ^ 2 * x1 * x2 ^ 3 * x3 - x0 * x1
      ^ 4 * x2 ^ 2 - x0 * x1 ^ 2 * x2 ^ 3 * x3 - 2 * x0 * x1 * x2 ^ 2 * x3 ^ 3 - x1 ^ 5 * x2 ^ 2,
-57 * ι * x0 * x1 ^ 2 * x2 ^ 2 * x3 - 57 * ι * x1 ^ 3 * x2 ^ 2 * x3 - 57 * x0 * x1 ^ 2 * x2 ^ 2 * x3]

def bezout3 (ι x0 x1 x2 x3 : R) : Fin 4 → R :=
  ![57 * ι * x0 ^ 4 * x1 + ι * x0 ^ 4 * x2 + 57 * ι * x0 ^ 3 * x1 ^ 2 + 2 * ι * x0 ^ 3 * x1 * x2 + 57 *
      ι * x0 ^ 2 * x1 ^ 3 + ι * x0 ^ 2 * x1 ^ 2 * x2 + ι * x0 ^ 2 * x1 * x3 ^ 2 + 57 * ι * x0 * x1 *
      x2 ^ 3 + 57 * ι * x1 ^ 2 * x2 ^ 3 - 57 * x0 ^ 4 * x1 - x0 ^ 4 * x2 - x0 ^ 3 * x1 * x2 - 2 * x0
      ^ 3 * x3 ^ 2 - 57 * x0 ^ 2 * x1 ^ 3 - x0 ^ 2 * x1 * x3 ^ 2 - 57 * x0 * x1 ^ 4 - 57 * x0 * x1 *
      x2 ^ 3 - 57 * x1 ^ 5,
0,
ι * x0 ^ 4 * x1 ^ 2 * x3 + ι * x0 ^ 3 * x1 ^ 3 * x3 + ι * x0 ^ 2 * x1 ^ 4 * x3 + ι * x0 * x1 ^ 2 *
      x2 ^ 3 * x3 + ι * x1 ^ 3 * x2 ^ 3 * x3 - x0 ^ 4 * x1 ^ 2 * x3 - x0 ^ 2 * x1 ^ 4 * x3 - x0 * x1
      ^ 5 * x3 - x0 * x1 ^ 2 * x2 ^ 3 * x3 - x1 ^ 6 * x3,
0]

def bezout4 (ι x0 x1 x2 x3 : R) : Fin 4 → R :=
  ![3249 * ι * x0 ^ 3 * x2 ^ 2 + 6498 * ι * x0 ^ 2 * x1 * x2 ^ 2 + 171 * ι * x0 ^ 2 * x2 ^ 3 + 3249 * ι
      * x0 * x1 ^ 2 * x2 ^ 2 + 114 * ι * x0 * x1 * x2 ^ 3 + 3249 * ι * x0 * x2 ^ 3 * x3 + 114 * ι *
      x0 * x2 ^ 2 * x3 ^ 2 + 3249 * ι * x1 ^ 3 * x2 ^ 2 - 3249 * x0 ^ 3 * x2 ^ 2 - 57 * x0 ^ 2 * x2
      ^ 3 - 3249 * x0 * x1 ^ 2 * x2 ^ 2 - 3249 * x0 * x2 ^ 3 * x3 - 3249 * x1 ^ 3 * x2 ^ 2 - 6498 *
      x2 ^ 2 * x3 ^ 3,
ι * x0 ^ 4 * x2 + ι * x0 ^ 3 * x1 * x2 + 57 * ι * x0 * x1 ^ 2 * x2 * x3 - x0 ^ 4 * x2,
ι * x0 ^ 5 * x2 ^ 2 + ι * x0 ^ 4 * x1 * x2 ^ 2 + ι * x0 ^ 3 * x1 ^ 2 * x2 ^ 2 + 57 * ι * x0 ^ 3 * x1
      * x2 ^ 2 * x3 + ι * x0 ^ 3 * x2 ^ 3 * x3 + 114 * ι * x0 ^ 2 * x1 ^ 2 * x2 ^ 2 * x3 + 2 * ι *
      x0 ^ 2 * x1 * x2 ^ 3 * x3 + 57 * ι * x0 * x1 ^ 3 * x2 ^ 2 * x3 + ι * x0 * x1 ^ 2 * x2 ^ 3 * x3
      + 57 * ι * x0 * x1 * x2 ^ 3 * x3 ^ 2 + ι * x0 * x1 * x2 ^ 2 * x3 ^ 3 + 57 * ι * x1 ^ 4 * x2 ^
      2 * x3 - x0 ^ 5 * x2 ^ 2 - x0 ^ 3 * x1 ^ 2 * x2 ^ 2 - 57 * x0 ^ 3 * x1 * x2 ^ 2 * x3 - x0 ^ 3
      * x2 ^ 3 * x3 - x0 ^ 2 * x1 ^ 3 * x2 ^ 2 - x0 ^ 2 * x1 * x2 ^ 3 * x3 - 2 * x0 ^ 2 * x2 ^ 2 *
      x3 ^ 3 - x0 * x1 ^ 4 * x2 ^ 2 - 57 * x0 * x1 ^ 3 * x2 ^ 2 * x3 - 57 * x0 * x1 * x2 ^ 3 * x3 ^
      2 - x0 * x1 * x2 ^ 2 * x3 ^ 3 - 57 * x1 ^ 4 * x2 ^ 2 * x3 - 114 * x1 * x2 ^ 2 * x3 ^ 4,
-57 * ι * x0 * x1 ^ 2 * x2 ^ 2 * x3]

def bezout5 (ι x0 x1 x2 x3 : R) : Fin 4 → R :=
  ![57 * ι * x0 ^ 5 + 57 * ι * x0 ^ 4 * x1 + 2 * ι * x0 ^ 4 * x2 + 57 * ι * x0 ^ 3 * x1 ^ 2 + ι * x0 ^ 3
      * x1 * x2 + 57 * ι * x0 ^ 3 * x2 * x3 + ι * x0 ^ 3 * x3 ^ 2 + 57 * ι * x0 ^ 2 * x2 ^ 3 + 57 *
      ι * x0 * x1 * x2 ^ 3 - 57 * x0 ^ 5 - x0 ^ 4 * x2 - 57 * x0 ^ 3 * x1 ^ 2 - 57 * x0 ^ 3 * x2 *
      x3 - x0 ^ 3 * x3 ^ 2 - 57 * x0 ^ 2 * x1 ^ 3 - 57 * x0 ^ 2 * x2 ^ 3 - 114 * x0 ^ 2 * x3 ^ 3 -
      57 * x0 * x1 ^ 4,
0,
ι * x0 ^ 5 * x1 * x3 + ι * x0 ^ 4 * x1 ^ 2 * x3 + ι * x0 ^ 3 * x1 ^ 3 * x3 + ι * x0 ^ 3 * x1 * x2 *
      x3 ^ 2 + ι * x0 ^ 2 * x1 * x2 ^ 3 * x3 + ι * x0 * x1 ^ 2 * x2 ^ 3 * x3 - x0 ^ 5 * x1 * x3 - x0
      ^ 3 * x1 ^ 3 * x3 - x0 ^ 3 * x1 * x2 * x3 ^ 2 - x0 ^ 2 * x1 ^ 4 * x3 - x0 ^ 2 * x1 * x2 ^ 3 *
      x3 - 2 * x0 ^ 2 * x1 * x3 ^ 4 - x0 * x1 ^ 5 * x3,
0]

def bezout6 (ι x0 x1 x2 x3 : R) : Fin 4 → R :=
  ![57 * ι * x0 ^ 5 + 57 * ι * x0 ^ 4 * x1 + ι * x0 ^ 4 * x2 + 3249 * ι * x0 ^ 4 * x3 + 114 * ι * x0 ^ 3
      * x2 * x3 + 57 * ι * x0 ^ 2 * x2 ^ 3 + 3249 * ι * x0 ^ 2 * x2 * x3 ^ 2 + 57 * ι * x0 ^ 2 * x3
      ^ 3 + 3249 * ι * x0 * x2 ^ 3 * x3 - 57 * x0 ^ 4 * x1 - 3249 * x0 ^ 4 * x3 - 57 * x0 ^ 3 * x1 ^
      2 - 57 * x0 ^ 3 * x2 * x3 - 57 * x0 ^ 2 * x1 ^ 3 - 3249 * x0 ^ 2 * x2 * x3 ^ 2 - 57 * x0 ^ 2 *
      x3 ^ 3 - 3249 * x0 * x2 ^ 3 * x3 - 6498 * x0 * x3 ^ 4,
0,
ι * x0 ^ 6 * x3 + ι * x0 ^ 5 * x1 * x3 + ι * x0 ^ 4 * x1 ^ 2 * x3 + 57 * ι * x0 ^ 4 * x1 * x3 ^ 2 +
      ι * x0 ^ 4 * x2 * x3 ^ 2 + 2 * ι * x0 ^ 3 * x1 * x2 * x3 ^ 2 + ι * x0 ^ 3 * x2 ^ 3 * x3 + ι *
      x0 ^ 2 * x1 * x2 ^ 3 * x3 + 57 * ι * x0 ^ 2 * x1 * x2 * x3 ^ 3 + ι * x0 ^ 2 * x1 * x3 ^ 4 + 57
      * ι * x0 * x1 * x2 ^ 3 * x3 ^ 2 - x0 ^ 6 * x3 - x0 ^ 4 * x1 ^ 2 * x3 - 57 * x0 ^ 4 * x1 * x3 ^
      2 - x0 ^ 4 * x2 * x3 ^ 2 - x0 ^ 3 * x1 ^ 3 * x3 - x0 ^ 3 * x1 * x2 * x3 ^ 2 - x0 ^ 3 * x2 ^ 3
      * x3 - 2 * x0 ^ 3 * x3 ^ 4 - x0 ^ 2 * x1 ^ 4 * x3 - 57 * x0 ^ 2 * x1 * x2 * x3 ^ 3 - x0 ^ 2 *
      x1 * x3 ^ 4 - 57 * x0 * x1 * x2 ^ 3 * x3 ^ 2 - 114 * x0 * x1 * x3 ^ 5,
0]

def bezout (ι x0 x1 x2 x3 : R) : Fin 7 → Fin 4 → R :=
  ![bezout0 ι x0 x1 x2 x3, bezout1 ι x0 x1 x2 x3, bezout2 ι x0 x1 x2 x3, bezout3 ι x0 x1 x2 x3, bezout4 ι x0 x1 x2 x3, bezout5 ι x0 x1 x2 x3, bezout6 ι x0 x1 x2 x3]

/-- Literal polynomial identities over any commutative ring containing
an element whose square is minus one. -/
theorem obstruction_identity (ι x0 x1 x2 x3 : R) (hι : ι ^ 2 = -1)
    (j : Fin 7) :
    sparseK ι x0 x1 x2 x3 * chosenCubic ι x0 x1 * reducedTest x0 x1 x2 x3 j =
      ∑ a : Fin 4, bezout ι x0 x1 x2 x3 j a * reducedRelations ι x0 x1 x2 x3 a := by
  fin_cases j <;>
    norm_num [bezout, bezout0, bezout1, bezout2, bezout3, bezout4, bezout5, bezout6,
      reducedRelations, sparseK, sparseH, chosenCubic, reducedTest,
      Fin.sum_univ_succ]
  · linear_combination (-x0 ^ 3 * x1 ^ 3 * x2 ^ 3 - x0 ^ 3 * x2 ^ 3 * x3 ^ 3 - x0 ^ 2 * x1 ^ 4 * x2 ^ 3 - x0 ^ 2 * x1 * x2 ^ 3 * x3 ^ 3 + 57 * x0 * x1 ^ 4 * x2 ^ 3 * x3 + 57 * x0 * x1 * x2 ^ 3 * x3 ^ 4 + 57 * x1 ^ 5 * x2 ^ 3 * x3 + 57 * x1 ^ 2 * x2 ^ 3 * x3 ^ 4) * hι
  · linear_combination (x0 ^ 3 * x1 ^ 3 * x2 * x3 ^ 2 + x0 ^ 3 * x2 * x3 ^ 5 + x0 ^ 2 * x1 ^ 4 * x2 * x3 ^ 2 + x0 ^ 2 * x1 * x2 * x3 ^ 5 - 57 * x0 * x1 ^ 4 * x2 * x3 ^ 3 - 57 * x0 * x1 * x2 * x3 ^ 6) * hι
  · linear_combination (x0 ^ 3 * x1 ^ 4 * x2 ^ 2 + x0 ^ 3 * x1 * x2 ^ 2 * x3 ^ 3 + x0 ^ 2 * x1 ^ 5 * x2 ^ 2 + x0 ^ 2 * x1 ^ 2 * x2 ^ 2 * x3 ^ 3 - 57 * x0 * x1 ^ 5 * x2 ^ 2 * x3 - 57 * x0 * x1 ^ 2 * x2 ^ 2 * x3 ^ 4 - 57 * x1 ^ 6 * x2 ^ 2 * x3 - 57 * x1 ^ 3 * x2 ^ 2 * x3 ^ 4) * hι
  · linear_combination (x0 ^ 3 * x1 ^ 5 * x3 + x0 ^ 3 * x1 ^ 2 * x3 ^ 4 + x0 ^ 2 * x1 ^ 6 * x3 + x0 ^ 2 * x1 ^ 3 * x3 ^ 4) * hι
  · linear_combination (x0 ^ 4 * x1 ^ 3 * x2 ^ 2 + x0 ^ 4 * x2 ^ 2 * x3 ^ 3 + x0 ^ 3 * x1 ^ 4 * x2 ^ 2 + x0 ^ 3 * x1 * x2 ^ 2 * x3 ^ 3 - 57 * x0 * x1 ^ 5 * x2 ^ 2 * x3 - 57 * x0 * x1 ^ 2 * x2 ^ 2 * x3 ^ 4) * hι
  · linear_combination (x0 ^ 4 * x1 ^ 4 * x3 + x0 ^ 4 * x1 * x3 ^ 4 + x0 ^ 3 * x1 ^ 5 * x3 + x0 ^ 3 * x1 ^ 2 * x3 ^ 4) * hι
  · linear_combination (x0 ^ 5 * x1 ^ 3 * x3 + x0 ^ 5 * x3 ^ 4 + x0 ^ 4 * x1 ^ 4 * x3 + x0 ^ 4 * x1 * x3 ^ 4) * hι

end Arithmetic

open CycleQ2SeedTrace CycleQ2SeedCechTheta CycleQ2NormalConnecting
  CycleQ2GeometricKoszulTrace CycleQ2GeometricProjectiveCurve
open CycleQ2SeedCech (curveA curveB)

/-- The same literal cubic used in the explicit seed direction. -/
def selectedCubic : Poly := chosenCubic (C Complex.I) (X 0) (X 1)

/-- The plus-sign cubic appearing in the seven literal products. -/
def obstructionCubic : Poly := sparseK (C Complex.I) (X 0) (X 1) (X 2) (X 3)

def testCubic (j : Fin 7) : Poly := reducedTest (X 0) (X 1) (X 2) (X 3) j

def testNumerator (j : Fin 7) : Poly := obstructionCubic * selectedCubic * testCubic j


/-- The identical weighted cubic before substituting the curve equation. -/
def weightedSelectedCubic : WeightedPoly := chosenCubic (C Complex.I) (X 0) (X 1)

/-- The seven literal weighted cubic tests, in their original order. -/
def weightedTestCubic : Fin 7 → WeightedPoly :=
  ![X 2 * X 4, X 2 * X 3 ^ 2, X 1 * X 2 ^ 2, X 1 ^ 2 * X 3,
    X 0 * X 2 ^ 2, X 0 * X 1 * X 3, X 0 ^ 2 * X 3]

theorem substitute_weightedSelectedCubic :
    substitute weightedSelectedCubic = selectedCubic := by
  simp [weightedSelectedCubic, selectedCubic, chosenCubic, substitute]

theorem substitute_weightedTestCubic (j : Fin 7) :
    substitute (weightedTestCubic j) = testCubic j := by
  fin_cases j <;> simp [weightedTestCubic, testCubic, reducedTest, substitute]
  ring

/-- The weighted ambient test before substituting the curve equation for w. -/
def ambientTest : WeightedPoly := X 2 * X 3 ^ 3 * X 4

/-- The minus sign agrees with the fixed-cubic normal-lift numerator. -/
def ambientNumerator : Poly := -(substitute ambientTest) * selectedCubic

theorem selectedCubic_homogeneous : selectedCubic.IsHomogeneous 3 := by
  simpa only [selectedCubic, chosenCubic, map_sub, map_one, mul_assoc] using
    (((isHomogeneous_X_pow (0 : Fin 4) 2).mul (isHomogeneous_X ℂ (1 : Fin 4))).C_mul
      Complex.I).add ((isHomogeneous_X_pow (0 : Fin 4) 3).C_mul (Complex.I - 1))

theorem obstructionCubic_homogeneous : obstructionCubic.IsHomogeneous 3 := by
  have he : obstructionCubic = curveH 1 + C (2 * Complex.I) * (X 1 ^ 3 + X 3 ^ 3) := by
    simp only [obstructionCubic, sparseK, curveH, h, b, map_mul, map_ofNat, map_one]
    ring
  rw [he]
  exact (sparse_curveH_homogeneous 1).add
    (((isHomogeneous_X_pow (1 : Fin 4) 3).add
      (isHomogeneous_X_pow (3 : Fin 4) 3)).C_mul (2 * Complex.I))

theorem testCubic_homogeneous (j : Fin 7) : (testCubic j).IsHomogeneous 3 := by
  fin_cases j
  · exact (isHomogeneous_X_pow (2 : Fin 4) 3).neg
  · exact (isHomogeneous_X ℂ (2 : Fin 4)).mul (isHomogeneous_X_pow (3 : Fin 4) 2)
  · exact (isHomogeneous_X ℂ (1 : Fin 4)).mul (isHomogeneous_X_pow (2 : Fin 4) 2)
  · exact (isHomogeneous_X_pow (1 : Fin 4) 2).mul (isHomogeneous_X ℂ (3 : Fin 4))
  · exact (isHomogeneous_X ℂ (0 : Fin 4)).mul (isHomogeneous_X_pow (2 : Fin 4) 2)
  · exact ((isHomogeneous_X ℂ (0 : Fin 4)).mul
      (isHomogeneous_X ℂ (1 : Fin 4))).mul (isHomogeneous_X ℂ (3 : Fin 4))
  · exact (isHomogeneous_X_pow (0 : Fin 4) 2).mul (isHomogeneous_X ℂ (3 : Fin 4))

theorem testNumerator_homogeneous (j : Fin 7) : (testNumerator j).IsHomogeneous 9 :=
  (obstructionCubic_homogeneous.mul selectedCubic_homogeneous).mul (testCubic_homogeneous j)

theorem substitute_ambientTest : substitute ambientTest = -(X 2 ^ 3 * X 3 ^ 3) := by
  simp [ambientTest, substitute]
  ring

theorem ambientNumerator_eq : ambientNumerator = X 2 ^ 3 * X 3 ^ 3 * selectedCubic := by
  rw [ambientNumerator, substitute_ambientTest, neg_neg]

theorem ambientNumerator_homogeneous : ambientNumerator.IsHomogeneous 9 := by
  rw [ambientNumerator_eq]
  exact ((isHomogeneous_X_pow (2 : Fin 4) 3).mul
    (isHomogeneous_X_pow (3 : Fin 4) 3)).mul selectedCubic_homogeneous

private theorem reducedRelation_mem (a : Fin 4) :
    reducedRelations (C Complex.I) (X 0) (X 1) (X 2) (X 3) a ∈
      fourGeneratorIdeal 57 1 := by
  have hq : relation 57 0 ∈ fourGeneratorIdeal 57 1 := Ideal.subset_span (by simp)
  have hh : curveH 1 ∈ fourGeneratorIdeal 57 1 := Ideal.subset_span (by simp)
  have hg₁ : firstQuartic 57 ∈ fourGeneratorIdeal 57 1 := Ideal.subset_span (by simp)
  have hg₂ : secondQuartic ∈ fourGeneratorIdeal 57 1 := Ideal.subset_span (by simp)
  fin_cases a
  · apply (Ideal.unit_mul_mem_iff_mem _
      ((isUnit_iff_ne_zero.mpr (by norm_num : (9747 : ℂ) ≠ 0)).map (C : ℂ →+* Poly))).mp
    simpa [reducedRelations, firstQuartic, curveA, mul_pow] using hg₁
  · apply (Ideal.unit_mul_mem_iff_mem _
      ((isUnit_iff_ne_zero.mpr (by norm_num : (3 : ℂ) ≠ 0)).map (C : ℂ →+* Poly))).mp
    simpa [reducedRelations, secondQuartic, curveB] using hg₂
  · simpa [reducedRelations, relation, map_ofNat] using hq
  · have he : reducedRelations (C Complex.I) (X 0) (X 1) (X 2) (X 3) 3 = curveH 1 := by
      change sparseH (C Complex.I) (X 0) (X 1) (X 2) (X 3) = curveH 1
      simp only [sparseH, curveH, h, b, map_one]
      ring
    exact he.symm ▸ hh

private theorem smallMonomial_mem :
    (X 0 ^ 2 * X 1 * X 2 ^ 3 * X 3 ^ 3 : Poly) ∈ fourGeneratorIdeal 57 1 := by
  have hq : relation 57 0 ∈ fourGeneratorIdeal 57 1 := Ideal.subset_span (by simp)
  have h₀ := reducedRelation_mem 0
  have hsum := (fourGeneratorIdeal 57 1).add_mem
    ((fourGeneratorIdeal 57 1).mul_mem_left (X 1 * X 2 ^ 3 * X 3 ^ 3) hq)
    ((fourGeneratorIdeal 57 1).mul_mem_left (57 * X 2 ^ 3 * X 3 ^ 2) h₀)
  convert hsum using 1
  simp only [relation, reducedRelations, Matrix.cons_val_zero, map_ofNat]
  ring

/-- The seven products for this one chosen cubic belong to the actual
homogeneous numerator kernel at the literal seed. -/
theorem testNumerator_mem (j : Fin 7) : testNumerator j ∈ fourGeneratorIdeal 57 1 := by
  have hi : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  change sparseK (C Complex.I) (X 0) (X 1) (X 2) (X 3) *
    chosenCubic (C Complex.I) (X 0) (X 1) * reducedTest (X 0) (X 1) (X 2) (X 3) j ∈ _
  rw [obstruction_identity _ _ _ _ _ hi]
  apply Ideal.sum_mem
  intro a ha
  exact Ideal.mul_mem_left _ _ (reducedRelation_mem a)

/-- The exact body of the legacy theta-one plus cubic after substitution. -/
theorem substitute_literalK :
    substitute (originalK + C (1 : ℂ) * X 0 ^ 3) = obstructionCubic := by
  simp [substitute, originalK, originalB, obstructionCubic, sparseK]
  ring

/-- Each old weighted numerator is the numerator of the actual class above. -/
theorem substitute_weightedTestNumerator (j : Fin 7) :
    substitute ((originalK + C (1 : ℂ) * X 0 ^ 3) *
      weightedSelectedCubic * weightedTestCubic j) = testNumerator j := by
  simp only [map_mul, substitute_literalK, substitute_weightedSelectedCubic,
    substitute_weightedTestCubic, testNumerator]

theorem substitute_weightedAmbientNumerator :
    substitute (-ambientTest * weightedSelectedCubic) = ambientNumerator := by
  simp only [map_mul, map_neg, substitute_weightedSelectedCubic, ambientNumerator]


section Cohomology
open CategoryTheory CycleQ2GeometricLiteralCanonicalClass
  CycleQ2GeometricProjectiveCanonicalH1

/-- Every degree-nine numerator gives an actual differential-sheaf H¹ class
at the literal seed through the homogeneous Čech connecting map. -/
def degreeNineCanonicalClass (p : Poly) (hp : p.IsHomogeneous 9) :
    DifferentialSheafH1 57 1 :=
  literalCanonicalH1Equiv
    (degreeOneToProjectiveH1 57 1 (by norm_num) (degreeNineCechClass 57 1 p hp))

/-- Exact kernel of the actual literal degree-nine cohomology class map. -/
theorem degreeNineCanonicalClass_zero_iff (p : Poly) (hp : p.IsHomogeneous 9) :
    degreeNineCanonicalClass p hp = 0 ↔ p ∈ fourGeneratorIdeal 57 1 := by
  constructor
  · intro hz
    apply (CycleQ2GeometricCurveRegularPair.At.degreeNineCechClass_zero_iff_fourGeneratorIdeal
      57 1 (by norm_num) p hp).mp
    apply degreeOneToProjectiveH1_injective 57 1 (by norm_num)
    apply literalCanonicalH1Equiv.injective
    simpa only [degreeNineCanonicalClass, map_zero] using hz
  · intro hm
    simp only [degreeNineCanonicalClass, degreeNineCechClass_zero_of_mem 57 1 p hp hm,
      map_zero]

/-- The ambient paired numerator is detected for the same selected cubic
that occurs in the seven products. -/
theorem ambientNumerator_trace :
    literalTraceLinear ambientNumerator = 228 * (Complex.I - 1) := by
  have he : ambientNumerator =
      Complex.I • (X 0 ^ 2 * X 1 * X 2 ^ 3 * X 3 ^ 3 : Poly) +
        (Complex.I - 1) • literalNumerator := by
    rw [ambientNumerator_eq]
    simp only [selectedCubic, chosenCubic, literalNumerator, smul_eq_C_mul, map_sub, map_one]
    ring
  rw [he, map_add, map_smul, map_smul,
    literalTraceLinear_zero_of_mem _ smallMonomial_mem, literalTraceLinear_numerator]
  simp only [smul_eq_mul, mul_zero, zero_add, mul_comm]

theorem ambientNumerator_trace_ne_zero : literalTraceLinear ambientNumerator ≠ 0 := by
  rw [ambientNumerator_trace]
  intro he
  have hi := congrArg Complex.im he
  norm_num at hi

/-- This class is an actual derived cohomology class, with the same chosen
cubic and the explicit ambient numerator. -/
def selectedAmbientClass : DifferentialSheafH1 57 1 :=
  degreeNineCanonicalClass ambientNumerator ambientNumerator_homogeneous

theorem selectedAmbientClass_ne_zero : selectedAmbientClass ≠ 0 := by
  intro hz
  exact ambientNumerator_trace_ne_zero (literalTraceLinear_zero_of_mem _
    ((degreeNineCanonicalClass_zero_iff ambientNumerator ambientNumerator_homogeneous).mp hz))

/-- The actual differential-cohomology class of a selected cubic test. -/
def selectedTestClass (j : Fin 7) : DifferentialSheafH1 57 1 :=
  degreeNineCanonicalClass (testNumerator j) (testNumerator_homogeneous j)

theorem selectedTestClass_zero (j : Fin 7) : selectedTestClass j = 0 :=
  (degreeNineCanonicalClass_zero_iff (testNumerator j) (testNumerator_homogeneous j)).mpr
    (testNumerator_mem j)

/-- The same explicit cubic satisfies all seven actual cohomology kernel
equations while its explicit ambient paired numerator gives a nonzero class.
No geometric interpretation as a deformation or cylinder differential is
assumed in this statement. -/
theorem selectedCubic_kernel_and_detector :
    (∀ j : Fin 7, selectedTestClass j = 0) ∧ selectedAmbientClass ≠ 0 :=
  ⟨selectedTestClass_zero, selectedAmbientClass_ne_zero⟩

#print axioms substitute_weightedTestNumerator
#print axioms substitute_weightedAmbientNumerator
#print axioms degreeNineCanonicalClass_zero_iff
#print axioms testNumerator_mem
#print axioms ambientNumerator_trace
#print axioms selectedTestClass_zero
#print axioms selectedAmbientClass_ne_zero
#print axioms selectedCubic_kernel_and_detector

end Cohomology

end CycleQ2GeometricLiteralDirection
end
