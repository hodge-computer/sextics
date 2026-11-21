import Proposal.GeometricSeedCubicFamily
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# The actual projective family over all invariant cubic coefficients

The coefficient ring is the full unnormalized invariant-cubic parameter
ring. The original weighted polynomial quotient by the universal seed
equation carries its inherited grading and native projective spectrum.
Its structure morphism uses the original parameter coefficients.

This is a one-equation projective hypersurface family. The earlier
incidence surfaces are cut out by an additional cubic equation and are
different schemes. The zero coefficient specialization and properness
of this family are constructed in the following modules.

Status: source-only proof draft; no Lean elaboration, compilation, or
kernel replay has been run. Prepared for `fqlx` with OpenAI ChatGPT
assistance, following Ben Diamond and the project's geometric argument.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedProjectiveFamily

open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2SeedCubicFamily CycleQ2GeometricIncidenceProj

attribute [local instance] MvPolynomial.weightedGradedAlgebra

def familyIdeal (r : ℂ) : Ideal FamilyPolynomial :=
  Ideal.span {familyEquation r}

abbrev FamilyRing (r : ℂ) := FamilyPolynomial ⧸ familyIdeal r

def familyQuotient (r : ℂ) : FamilyPolynomial →+* FamilyRing r :=
  Ideal.Quotient.mk (familyIdeal r)

def familyCoordinate (r : ℂ) (j : Fin 5) : FamilyRing r :=
  familyQuotient r (X j)

theorem familyIdeal_homogeneous (r : ℂ) :
    (familyIdeal r).IsHomogeneous (PolynomialGrade ParameterRing) := by
  apply Ideal.homogeneous_span
  intro p hp
  obtain rfl := Set.mem_singleton_iff.mp hp
  exact ⟨6, familyEquation_homogeneous r⟩

/-- The degree pieces of the original universal polynomial quotient. -/
abbrev familyGrade (r : ℂ) (n : ℕ) : Submodule ParameterRing (FamilyRing r) :=
  CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.grade
    (PolynomialGrade ParameterRing) (familyIdeal r) n

instance familyGradedRing (r : ℂ) : GradedRing (familyGrade r) :=
  CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.gradedRing
    (PolynomialGrade ParameterRing) (familyIdeal r) (familyIdeal_homogeneous r)

theorem familyQuotient_mem_grade (r : ℂ) {n : ℕ} {p : FamilyPolynomial}
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    familyQuotient r p ∈ familyGrade r n :=
  ⟨p, hp, rfl⟩

theorem familyCoordinate_mem_grade (r : ℂ) (j : Fin 5) :
    familyCoordinate r j ∈ familyGrade r (geometricWeight j) :=
  familyQuotient_mem_grade r (isWeightedHomogeneous_X ParameterRing geometricWeight j)

def parameterCoefficient (r : ℂ) : ParameterRing →+* familyGrade r 0 :=
  algebraMap ParameterRing (familyGrade r 0)

@[simp] theorem parameterCoefficient_coe (r : ℂ) (c : ParameterRing) :
    (parameterCoefficient r c : FamilyRing r) = familyQuotient r (C c) := rfl

def parameterScheme : Scheme := Spec (CommRingCat.of ParameterRing)

/-- The native projective spectrum over the full invariant-cubic base. -/
def family (r : ℂ) : Scheme := Proj (familyGrade r)

/-- The structure morphism to the original coefficient parameter scheme. -/
def familyToParameters (r : ℂ) : family r ⟶ parameterScheme :=
  Proj.toSpecZero (familyGrade r) ≫
    Spec.map (CommRingCat.ofHom (parameterCoefficient r))

theorem familyEquation_zero (r : ℂ) :
    familyQuotient r (familyEquation r) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (by simp)

end CycleQ2SeedProjectiveFamily

end

#print axioms CycleQ2SeedProjectiveFamily.familyIdeal_homogeneous
#print axioms CycleQ2SeedProjectiveFamily.familyGradedRing
#print axioms CycleQ2SeedProjectiveFamily.familyEquation_zero
