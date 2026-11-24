import Proposal.GeometricSeedFermatProj
import Proposal.GeometricIncidenceProjectiveProper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.FiniteType

/-!
# Properness of the actual weighted projective seed

All five coordinate weights are positive. The existing degree-zero
polynomial lemma therefore shows that the original coefficient map onto
the cone quotient's degree-zero piece is surjective. Its spectrum map is
a closed immersion and hence proper.

The cone quotient is a finite-type complex algebra. The same finite set
of generators generates it over its actual degree-zero subring, so
Mathlib's properness theorem for the native projective-spectrum map
applies. Composing these two morphisms proves properness of the existing
`threefoldToComplex`, without changing its quotient, grading, or scalar
map. This result holds for every parameter `r`; the Fermat specialization
and its smoothness are not needed for properness.

The geometric seed follows Ben Diamond's
surface-section argument. Prepared for `fqlx` with OpenAI ChatGPT
assistance, reusing the earlier incidence-family properness construction.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedFermatProper

open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2SeedFermatCone CycleQ2SeedFermatProj

/-- Every degree-zero class in the actual cone quotient is represented
by an original complex coefficient. -/
theorem coefficient_surjective (r : ℂ) :
    Function.Surjective (coefficient r) := by
  rintro ⟨q, hq⟩
  obtain ⟨p, hp, rfl⟩ := hq
  refine ⟨p.coeff 0, ?_⟩
  apply Subtype.ext
  change coneQuotient r (C (p.coeff 0)) = coneQuotient r p
  exact congrArg (coneQuotient r)
    (CycleQ2IncidenceProjectiveProper.polynomialGrade_zero_eq_C p hp).symm

/-- The coefficient map used in `threefoldToComplex` gives an actual
closed immersion on spectra. -/
theorem coefficient_spec_closedImmersion (r : ℂ) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (coefficient r))) :=
  IsClosedImmersion.spec_of_surjective _ (coefficient_surjective r)

theorem coefficient_spec_proper (r : ℂ) :
    IsProper (Spec.map (CommRingCat.ofHom (coefficient r))) := by
  letI := coefficient_spec_closedImmersion r
  infer_instance

/-- The unchanged five-variable, one-equation cone is finite type over
the original complex coefficient field. -/
theorem cone_finiteType_coefficients (r : ℂ) :
    Algebra.FiniteType ℂ (ConeRing r) := by
  infer_instance

/-- The same finite generators suffice over the cone's native
degree-zero subring. -/
theorem cone_finiteType_zero (r : ℂ) :
    Algebra.FiniteType (coneGrade r 0) (ConeRing r) := by
  letI : IsScalarTower ℂ (coneGrade r 0) (ConeRing r) :=
    IsScalarTower.of_algebraMap_eq' (R := ℂ)
      (S := coneGrade r 0) (A := ConeRing r) rfl
  letI := cone_finiteType_coefficients r
  exact Algebra.FiniteType.of_restrictScalars_finiteType
    ℂ (coneGrade r 0) (ConeRing r)

/-- Properness over the native degree-zero spectrum. -/
theorem threefold_toSpecZero_proper (r : ℂ) :
    IsProper (Proj.toSpecZero (coneGrade r)) := by
  letI := cone_finiteType_zero r
  infer_instance

/-- The actual weighted projective seed is proper over the original
complex field, for every value of its parameter. -/
theorem threefold_proper (r : ℂ) :
    IsProper (threefoldToComplex r) := by
  letI := threefold_toSpecZero_proper r
  letI := coefficient_spec_proper r
  change IsProper (Proj.toSpecZero (coneGrade r) ≫
    Spec.map (CommRingCat.ofHom (coefficient r)))
  infer_instance

/-- Properness is retained under every actual scheme-theoretic base
change of this structure morphism. -/
theorem threefold_baseChange_proper (r : ℂ) (T : Scheme)
    (f : T ⟶ Spec (CommRingCat.of ℂ)) :
    IsProper (Limits.pullback.snd (threefoldToComplex r) f) := by
  letI := threefold_proper r
  infer_instance

end CycleQ2SeedFermatProper

#print axioms CycleQ2SeedFermatProper.coefficient_surjective
#print axioms CycleQ2SeedFermatProper.cone_finiteType_zero
#print axioms CycleQ2SeedFermatProper.threefold_proper
#print axioms CycleQ2SeedFermatProper.threefold_baseChange_proper

end
