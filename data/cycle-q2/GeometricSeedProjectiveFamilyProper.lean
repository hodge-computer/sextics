import Proposal.GeometricSeedProjectiveFamily
import Proposal.GeometricIncidenceProjectiveProper
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.FiniteType

/-!
# Properness of the full invariant-cubic projective family

The family retains the entire invariant-cubic coefficient ring, including
the zero cubic. All five geometric variables have positive weight, so
the original coefficient map onto the degree-zero piece of its actual
one-equation quotient is surjective. Its spectrum map is therefore a
closed immersion and is proper.

The actual cone quotient is generated over the parameter ring by the
five geometric coordinates. The same finite generators suffice over
its native degree-zero subring. Mathlib's properness theorem for
`Proj.toSpecZero`, followed by the original coefficient spectrum map,
therefore proves properness of the unchanged `familyToParameters`.

The theorem applies to every value of `r` and to all scheme-theoretic
base changes. It does not assume or assert smoothness of every fiber.
Prepared for `fqlx` with OpenAI ChatGPT
assistance, following Ben Diamond's invariant-cubic geometric family
and reusing the project's incidence-family properness construction.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedProjectiveFamilyProper

open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2SeedCubicFamily CycleQ2SeedProjectiveFamily

private theorem finiteType_over_zero {R A : Type} [CommSemiring R] [CommSemiring A]
    [Algebra R A] (𝒜 : ℕ → Submodule R A) [GradedRing 𝒜]
    [Algebra.FiniteType R A] : Algebra.FiniteType (𝒜 0) A := by
  letI : IsScalarTower R (𝒜 0) A :=
    ⟨fun a b c => by
      change (a • (b : A)) * c = a • ((b : A) * c)
      exact smul_mul_assoc a (b : A) c⟩
  exact Algebra.FiniteType.of_restrictScalars_finiteType R (𝒜 0) A

/-- Every degree-zero element of the actual family quotient comes from
the original full cubic-parameter coefficient ring. -/
theorem parameterCoefficient_surjective (r : ℂ) :
    Function.Surjective (parameterCoefficient r) := by
  rintro ⟨q, hq⟩
  obtain ⟨p, hp, rfl⟩ := hq
  refine ⟨p.coeff 0, ?_⟩
  apply Subtype.ext
  change Ideal.Quotient.mk (familyIdeal r) (C (p.coeff 0)) =
    Ideal.Quotient.mk (familyIdeal r) p
  exact congrArg (Ideal.Quotient.mk (familyIdeal r))
    (CycleQ2IncidenceProjectiveProper.polynomialGrade_zero_eq_C p hp).symm

theorem parameterCoefficient_spec_closedImmersion (r : ℂ) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (R := ParameterRing) (S := familyGrade r 0) (parameterCoefficient r))) :=
  IsClosedImmersion.spec_of_surjective _ (parameterCoefficient_surjective r)

theorem parameterCoefficient_spec_proper (r : ℂ) :
    IsProper (Spec.map (CommRingCat.ofHom (R := ParameterRing) (S := familyGrade r 0) (parameterCoefficient r))) := by
  letI := parameterCoefficient_spec_closedImmersion r
  infer_instance

/-- The original five-variable quotient is finite type over the
unchanged parameter coefficient ring. -/
theorem familyRing_finiteType_parameters (r : ℂ) :
    Algebra.FiniteType ParameterRing (FamilyRing r) := by
  infer_instance

/-- Extending scalars to the actual degree-zero piece preserves the
finite geometric generators. -/
theorem familyRing_finiteType_zero (r : ℂ) :
    Algebra.FiniteType (familyGrade r 0) (FamilyRing r) := by
  letI := familyRing_finiteType_parameters r
  exact finiteType_over_zero (R := ParameterRing) (A := FamilyRing r) (familyGrade r)


theorem family_toSpecZero_proper (r : ℂ) :
    IsProper (Proj.toSpecZero (familyGrade r)) := by
  letI := familyRing_finiteType_zero r
  infer_instance

/-- Properness of the actual full invariant-cubic projective family
over its original coefficient parameter scheme. -/
theorem familyToParameters_proper (r : ℂ) :
    IsProper (familyToParameters r) := by
  letI := family_toSpecZero_proper r
  letI := parameterCoefficient_spec_proper r
  change IsProper (Proj.toSpecZero (familyGrade r) ≫
    Spec.map (CommRingCat.ofHom (R := ParameterRing) (S := familyGrade r 0) (parameterCoefficient r)))
  infer_instance

/-- Every actual base change of the projective family remains proper,
including its scheme-theoretic coefficient fibers. -/
theorem family_baseChange_proper (r : ℂ) (T : Scheme)
    (f : T ⟶ Spec (CommRingCat.of ParameterRing)) :
    IsProper (Limits.pullback.snd (familyToParameters r) f) := by
  letI := familyToParameters_proper r
  infer_instance

end CycleQ2SeedProjectiveFamilyProper

end

#print axioms CycleQ2SeedProjectiveFamilyProper.parameterCoefficient_surjective
#print axioms CycleQ2SeedProjectiveFamilyProper.familyRing_finiteType_zero
#print axioms CycleQ2SeedProjectiveFamilyProper.familyToParameters_proper
#print axioms CycleQ2SeedProjectiveFamilyProper.family_baseChange_proper
