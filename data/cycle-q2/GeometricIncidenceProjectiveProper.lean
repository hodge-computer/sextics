import Proposal.GeometricEtaleIncidenceCurve
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.FiniteType

/-!
# Properness of the actual projective incidence family

The weighted variables have strictly positive degree. Every polynomial of
weighted degree zero is therefore constant, so the coefficient ring maps
surjectively onto the degree-zero part of the actual curve quotient.
The corresponding affine morphism is a closed immersion and is proper.

The actual homogeneous curve ring is a finite-type algebra over the
coefficient ring, hence also over its degree-zero part. Mathlib's properness
theorem for `Proj.toSpecZero` applies to that unchanged graded quotient.
Composing these two proper maps proves properness of the original
`genericCurveToBase`, including the fixed étale-incidence specialization.

No smoothness, fiber-dimension, or properness premise is supplied. The
theorem holds for the full section-parameter family, including singular
fibers.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2IncidenceProjectiveProper

open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2IncidenceNormalForm CycleQ2IncidenceUniversalChart
  CycleQ2IncidenceImageLine CycleQ2GeometricIncidenceProj

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- The given positive weights admit only the constant monomial in
degree zero, over an arbitrary coefficient ring. -/
theorem polynomialGrade_zero_eq_C {R : Type} [CommRing R]
    (p : MvPolynomial (Fin 5) R) (hp : p ∈ PolynomialGrade R 0) :
    p = C (p.coeff 0) := by
  classical
  have hcoeff (e : Fin 5 →₀ ℕ) (he : e ≠ 0) : p.coeff e = 0 := by
    by_contra hn
    have hw : Finsupp.weight geometricWeight e = 0 := hp hn
    rw [geometricWeight_weight] at hw
    have heq : e = 0 := by
      change e 0 + e 1 + e 2 + e 3 + 2 * e 4 = 0 at hw
      have h0 : e (0 : Fin 5) = 0 := by omega
      have h1 : e (1 : Fin 5) = 0 := by omega
      have h2 : e (2 : Fin 5) = 0 := by omega
      have h3 : e (3 : Fin 5) = 0 := by omega
      have h4 : e (4 : Fin 5) = 0 := by omega
      apply Finsupp.ext
      intro i
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
      · exact h3
      · exact h4
    exact he heq
  ext e
  by_cases he : e = 0
  · subst e
    simp
  · simp [coeff_C, Ne.symm he, hcoeff e he]

variable {S : Type} [CommRing S] [Algebra ℂ S]

local instance curveCommRing (y : ParameterIndex → S) : CommRing (GenericCurveRing y) :=
  inferInstance
local instance zeroCommRing (y : ParameterIndex → S) : CommRing (genericCurveGrade y 0) :=
  inferInstance
local instance coefficientModule (y : ParameterIndex → S) :
    Module (SectionBase S) (GenericCurveRing y) := Algebra.toModule
local instance degreeZeroModule (y : ParameterIndex → S) :
    Module (genericCurveGrade y 0) (GenericCurveRing y) := Algebra.toModule
local instance coefficientZeroModule (y : ParameterIndex → S) :
    Module (SectionBase S) (genericCurveGrade y 0) := Algebra.toModule
local instance coefficientSMul (y : ParameterIndex → S) :
    SMul (SectionBase S) (GenericCurveRing y) := (coefficientModule y).toSMul
local instance degreeZeroSMul (y : ParameterIndex → S) :
    SMul (genericCurveGrade y 0) (GenericCurveRing y) := (degreeZeroModule y).toSMul
local instance coefficientZeroSMul (y : ParameterIndex → S) :
    SMul (SectionBase S) (genericCurveGrade y 0) := (coefficientZeroModule y).toSMul

/-- This is exactly the coefficient map appearing in
`genericCurveToBase`; no new map or grading is chosen. -/
def genericCurveZeroHom (y : ParameterIndex → S) :
    SectionBase S →+* genericCurveGrade y 0 :=
  algebraMap (SectionBase S) (genericCurveGrade y 0)

@[simp] theorem genericCurveZeroHom_val (y : ParameterIndex → S) (c : SectionBase S) :
    (genericCurveZeroHom y c : GenericCurveRing y) =
      Ideal.Quotient.mk (genericCurveIdeal y) (C c) := rfl

/-- Every element of the actual quotient's degree-zero part comes from
an original coefficient. This also allows degenerate special fibers. -/
theorem genericCurveZeroHom_surjective (y : ParameterIndex → S) :
    Function.Surjective (genericCurveZeroHom y) := by
  rintro ⟨q, hq⟩
  obtain ⟨p, hp, rfl⟩ := hq
  refine ⟨p.coeff 0, ?_⟩
  apply Subtype.ext
  change Ideal.Quotient.mk (genericCurveIdeal y) (C (p.coeff 0)) =
    Ideal.Quotient.mk (genericCurveIdeal y) p
  exact congrArg (Ideal.Quotient.mk (genericCurveIdeal y))
    (polynomialGrade_zero_eq_C p hp).symm

theorem genericCurveZeroHom_spec_closedImmersion (y : ParameterIndex → S) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (R := SectionBase S) (S := genericCurveGrade y 0) (genericCurveZeroHom y))) :=
  IsClosedImmersion.spec_of_surjective _ (genericCurveZeroHom_surjective y)

theorem genericCurveZeroHom_spec_proper (y : ParameterIndex → S) :
    IsProper (Spec.map (CommRingCat.ofHom
      (R := SectionBase S) (S := genericCurveGrade y 0) (genericCurveZeroHom y))) := by
  letI := genericCurveZeroHom_spec_closedImmersion y
  infer_instance

/-- The original five-variable polynomial quotient is finite type over
its coefficient ring. -/
theorem genericCurve_finiteType_coefficients (y : ParameterIndex → S) :
    Algebra.FiniteType (SectionBase S) (GenericCurveRing y) := by
  infer_instance

/-- Extending the scalar base from coefficients to degree zero preserves
the finite set of polynomial generators. -/
theorem genericCurve_finiteType_zero (y : ParameterIndex → S) :
    Algebra.FiniteType (genericCurveGrade y 0) (GenericCurveRing y) := by
  letI : IsScalarTower (SectionBase S) (genericCurveGrade y 0) (GenericCurveRing y) :=
    IsScalarTower.of_algebraMap_eq' (R := SectionBase S)
      (S := genericCurveGrade y 0) (A := GenericCurveRing y) rfl
  letI := genericCurve_finiteType_coefficients y
  exact Algebra.FiniteType.of_restrictScalars_finiteType
    (SectionBase S) (genericCurveGrade y 0) (GenericCurveRing y)

/-- Properness of the actual projective-spectrum map before passing from
degree zero to the original parameter coefficient ring. -/
theorem genericCurve_toSpecZero_proper (y : ParameterIndex → S) :
    IsProper (Proj.toSpecZero (genericCurveGrade y)) := by
  letI := genericCurve_finiteType_zero y
  infer_instance

/-- The unchanged projective zero locus of `(h,F,M*T)` is proper over the
full original section-parameter base. -/
theorem genericCurveToBase_proper (y : ParameterIndex → S) :
    IsProper (genericCurveToBase y) := by
  letI := genericCurve_toSpecZero_proper y
  letI := genericCurveZeroHom_spec_proper y
  change IsProper (Proj.toSpecZero (genericCurveGrade y) ≫
    Spec.map (CommRingCat.ofHom (R := SectionBase S)
      (S := genericCurveGrade y 0) (genericCurveZeroHom y)))
  infer_instance

/-- Every actual base change of this family is proper, in particular
each residue-field fiber of the section-parameter scheme. -/
theorem genericCurve_baseChange_proper (y : ParameterIndex → S)
    (T : Scheme) (f : T ⟶ Spec (CommRingCat.of (SectionBase S))) :
    IsProper (Limits.pullback.snd (genericCurveToBase y) f) := by
  letI := genericCurveToBase_proper y
  infer_instance

/-- Closed specialization to the constructed universal étale incidence
point. There is no supplied coefficient point or properness assumption. -/
theorem fixed_curveToSectionParameters_proper :
    IsProper CycleQ2EtaleIncidenceCurve.curveToSectionParameters :=
  genericCurveToBase_proper CycleQ2IncidenceEtaleParameter.incidencePoint

theorem fixed_curve_baseChange_proper (T : Scheme)
    (f : T ⟶ CycleQ2EtaleIncidenceCurve.sectionParameterScheme) :
    IsProper (Limits.pullback.snd CycleQ2EtaleIncidenceCurve.curveToSectionParameters f) :=
  genericCurve_baseChange_proper CycleQ2IncidenceEtaleParameter.incidencePoint T f

end CycleQ2IncidenceProjectiveProper

#print axioms CycleQ2IncidenceProjectiveProper.genericCurveZeroHom_surjective
#print axioms CycleQ2IncidenceProjectiveProper.genericCurveToBase_proper
#print axioms CycleQ2IncidenceProjectiveProper.fixed_curveToSectionParameters_proper

end
