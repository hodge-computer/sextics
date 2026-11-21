import Proposal.GeometricIncidenceEtaleParameter
import Proposal.GeometricIncidenceFamilyContainment
import Proposal.GeometricUniversalCurveSection

/-!
# The projective incidence family over the actual étale parameter algebra

Every object in this module is specialized to the constructed universal
`incidencePoint` in the actual `ParameterAlgebra`. No coefficient point,
incidence equations, or trace-point hypothesis is supplied by a caller.
The source is the original projective `(h,F,M*T)` zero locus. It maps to
the original F-only weighted hypersurface over that parameter algebra,
and all structure maps commute on the nose.

The seed identities retain the original full cubic and sextic. The proved
basepoint open supplies the actual matrix pivot needed for local standard
smoothness over the surface. This local statement has relative dimension
two over the surface; it does not replace the remaining theorem that the
projective curve family is smooth of relative dimension one over a
nonempty open of its section-parameter base.

Status: source-only proof draft. Verification is deferred at the user's
request. No new axioms or admissions are used.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2EtaleIncidenceCurve

open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceUniversalChart CycleQ2IncidenceGenericPointSemantics
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2IncidenceImageLine
  CycleQ2GeometricIncidenceProj CycleQ2IncidenceTraceGeometry
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceFamilyContainment

abbrev SectionParameters := SectionBase ParameterAlgebra
abbrev CurveRing := GenericCurveRing incidencePoint

def sectionParameterScheme : Scheme := Spec (CommRingCat.of SectionParameters)
def curve : Scheme := genericCurve incidencePoint
def incidenceSurface : Scheme := surface incidencePoint
def threefold : Scheme := weightedThreefold incidencePoint

def sectionParametersToIncidence : sectionParameterScheme ⟶ parameterScheme :=
  Spec.map (CommRingCat.ofHom (C : ParameterAlgebra →+* SectionParameters))

def curveToSectionParameters : curve ⟶ sectionParameterScheme := genericCurveToBase incidencePoint
def threefoldToIncidence : threefold ⟶ parameterScheme := weightedThreefoldToBase incidencePoint
def curveToThreefold : curve ⟶ threefold := genericCurveToThreefold incidencePoint

def curveToIncidence : curve ⟶ parameterScheme :=
  curveToSectionParameters ≫ sectionParametersToIncidence

def curveToTimeAndSextic : curve ⟶ timeAndSexticBase := curveToIncidence ≫ parameterToBase

theorem curveToThreefold_over_incidence :
    curveToThreefold ≫ threefoldToIncidence = curveToIncidence :=
  genericCurveToThreefold_toBase incidencePoint

theorem curveToThreefold_over_timeAndSextic :
    curveToThreefold ≫ threefoldToIncidence ≫ parameterToBase = curveToTimeAndSextic := by
  rw [← Category.assoc, curveToThreefold_over_incidence]
  rfl

theorem curveToThreefold_preserves_ambient :
    curveToThreefold ≫ weightedThreefoldToAmbient incidencePoint =
      genericCurveToAmbient incidencePoint ≫
        weightedAmbientCoefficientMap (C : ParameterAlgebra →+* SectionParameters) :=
  genericCurveToThreefold_toAmbient incidencePoint

/-- The actual quotient and the original section-ideal model are
identified by explicit inverse polynomial maps. -/
def curveRingEquiv : CurveRing ≃+*
    CycleQ2UniversalCurveSection.SectionQuotient incidencePoint :=
  CycleQ2UniversalCurveSection.genericCurveRingEquiv incidencePoint

theorem curve_defining_equations :
    Ideal.Quotient.mk (genericCurveIdeal incidencePoint)
      (pointEquationH (sectionPoint incidencePoint)) = 0 ∧
    Ideal.Quotient.mk (genericCurveIdeal incidencePoint)
      (pointEquationF (sectionPoint incidencePoint)) = 0 ∧
    ∀ i : Fin 3, Ideal.Quotient.mk (genericCurveIdeal incidencePoint)
      (genericSectionEquation incidencePoint i) = 0 :=
  genericCurve_defining_equations incidencePoint

/-- The universal sextic is fixed along the actual incidence solver and
is extended only through the canonical coefficient map. -/
theorem sextic_eq_universal :
    pointEquationF incidencePoint =
      MvPolynomial.map (algebraMap CycleQ2IncidenceTraceFamily.TraceRing ParameterAlgebra)
        universalSextic :=
  tracePoint_equationF splitting.B sliceCoordinate

theorem curve_universalSextic_zero :
    Ideal.Quotient.mk (genericCurveIdeal incidencePoint)
      (MvPolynomial.map
        ((C : ParameterAlgebra →+* SectionParameters).comp
          (algebraMap CycleQ2IncidenceTraceFamily.TraceRing ParameterAlgebra))
        universalSextic) = 0 :=
  tracePoint_universalSextic_zero splitting.B sliceCoordinate

/-- Seed specialization keeps the full original cubic polynomial. -/
theorem seed_cubic :
    MvPolynomial.map seedMap (pointEquationH incidencePoint) = smoothH Complex.I := by
  rw [pointEquationH, pointMap_familyH, map_fullInvariantPolynomial]
  have hc : seedMap ∘ pointCubic incidencePoint = seedCubicCoefficients Complex.I := by
    funext j
    exact seedMap_incidencePoint (Sum.inl j)
  rw [hc]
  exact seedCubicCoefficients_polynomial Complex.I

/-- Seed specialization keeps the full original sextic polynomial. -/
theorem seed_sextic :
    MvPolynomial.map seedMap (pointEquationF incidencePoint) = smoothF (57 : ℂ) Complex.I := by
  rw [pointEquationF, pointMap_familyF, map_fullInvariantPolynomial]
  have hc : seedMap ∘ pointSextic incidencePoint = seedSexticCoefficients (57 : ℂ) Complex.I := by
    funext j
    exact seedMap_incidencePoint (Sum.inr (Sum.inl j))
  rw [hc]
  exact seedSexticCoefficients_polynomial (57 : ℂ) Complex.I

/-- These are the original incidence equations, now closed at the actual
universal point of the constructed étale parameter scheme. -/
theorem original_incidence_equations (q : CycleQ2IncidenceCoefficientRelations.ColumnIndex) :
    aeval incidencePoint ((CycleQ2IncidencePolynomialRelations.presentation ℂ 57).equation q) = 0 :=
  tracePoint_original_equations splitting.P splitting.B _ sliceCoordinate
    incidence_isTracePoint q

theorem leading_unit :
    IsUnit (aeval incidencePoint (CycleQ2IncidenceUniversalChart.leadingProduct ℂ)) :=
  tracePoint_leading_unit splitting.P splitting.B _ sliceCoordinate incidence_isTracePoint

theorem basepoint_unit :
    IsUnit (aeval incidencePoint CycleQ2IncidenceBasepointOpen.basepointPolynomial) :=
  tracePoint_extra_unit splitting.P splitting.B _ sliceCoordinate incidence_isTracePoint

/-- The actual surface-prime section models are standard smooth of
relative dimension two over their surface base, with no supplied
incidence or basepoint-open hypothesis. -/
theorem section_standardSmooth
    (P : Ideal (PointSurface incidencePoint)) [P.IsPrime]
    (hx : ∃ j, CycleQ2IncidenceBasepointOpen.curveCoordinate (pointMap incidencePoint) j ∉ P) :
    Algebra.IsStandardSmoothOfRelativeDimension 2 (PointPrimeRing incidencePoint P)
      (CycleQ2UniversalCurveSection.MatrixSectionQuotient (primeMatrix incidencePoint P)) :=
  CycleQ2UniversalCurveSection.tracePoint_section_standardSmooth
    splitting.P splitting.B sliceCoordinate incidence_isTracePoint P hx

theorem section_flat
    (P : Ideal (PointSurface incidencePoint)) [P.IsPrime]
    (hx : ∃ j, CycleQ2IncidenceBasepointOpen.curveCoordinate (pointMap incidencePoint) j ∉ P) :
    Module.Flat (PointPrimeRing incidencePoint P)
      (CycleQ2UniversalCurveSection.MatrixSectionQuotient (primeMatrix incidencePoint P)) :=
  CycleQ2UniversalCurveSection.point_section_flat incidencePoint original_incidence_equations
    leading_unit basepoint_unit P hx

end CycleQ2EtaleIncidenceCurve

#print axioms CycleQ2EtaleIncidenceCurve.curveToThreefold_over_incidence
#print axioms CycleQ2EtaleIncidenceCurve.curve_defining_equations
#print axioms CycleQ2EtaleIncidenceCurve.seed_cubic
#print axioms CycleQ2EtaleIncidenceCurve.seed_sextic
#print axioms CycleQ2EtaleIncidenceCurve.section_standardSmooth

end
