import Proposal.GeometricLiteralAmbientProjFiber
import Proposal.GeometricLiteralAmbientSurface
import Proposal.GeometricLiteralIncidenceCylinderMap
import Proposal.GeometricIncidenceChartSeedFiber

/-! The two presentations of the smooth fixed threefold of the time-family
correspondence. Both scheme fibers are identified over ℂ with the same native
weighted projective hypersurface at the trace parameter.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAmbientCylinder

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open CycleQ2IncidencePolynomialJacobianBinding CycleQ2GeometricIncidenceProj
  CycleQ2IncidenceFamilyContainment CycleQ2SeedCubicFamily CycleQ2SeedProjectiveFamily
  CycleQ2LiteralAmbientSmooth CycleQ2LiteralIncidenceCylinderMap CycleQ2IncidenceEtaleParameter
  CycleQ2LiteralIncidenceTimeCurve CycleQ2LiteralIncidenceTimeFamily

attribute [local instance] CycleQ2IncidenceTimeCurve.timeParameterCommRing

abbrev point := seedPoint (57 : ℂ) Complex.I
abbrev Native := weightedThreefold point

abbrev cubicEval := coefficientEvaluation incidenceCoefficients

theorem cubic_section : cubicEval.comp (algebraMap ℂ ParameterRing) = RingHom.id ℂ :=
  RingHom.ext (coefficientEvaluation_algebraMap incidenceCoefficients)

theorem cubicIdeal_map : (familyIdeal 57).map (MvPolynomial.map cubicEval) = sexticIdeal point := by
  rw [familyIdeal, sexticIdeal, Ideal.map_span, Set.image_singleton, specialize_incidence,
    CycleQ2IncidenceChartSeedFiber.literal_pointEquationF]

/-- The fixed fiber of the full invariant-cubic family is the native projective
spectrum of the literal sextic quotient, with its actual grading. -/
def nativeToIncidence : Native ≅ IncidenceFiber 57 :=
  CycleQ2LiteralAmbientProjFiber.fiberIso cubicEval (algebraMap ℂ ParameterRing)
    cubic_section (familyIdeal 57) (sexticIdeal point) cubicIdeal_map

@[reassoc, simp] theorem nativeToIncidence_overComplex :
    nativeToIncidence.hom ≫ incidenceFiberToComplex 57 = weightedThreefoldToBase point :=
  CycleQ2LiteralAmbientProjFiber.fiberIso_hom_fst _ _ _ _ _ _

@[reassoc, simp] theorem nativeToIncidence_snd :
    nativeToIncidence.hom ≫ pullback.snd incidenceParameter (familyToParameters 57) =
      CycleQ2LiteralAmbientProjFiber.projective cubicEval (algebraMap ℂ ParameterRing)
        cubic_section (familyIdeal 57) (sexticIdeal point) cubicIdeal_map :=
  CycleQ2LiteralAmbientProjFiber.fiberIso_hom_snd _ _ _ _ _ _

abbrev sexticEval : CycleQ2IncidenceTimeCurve.SexticRing →+* ℂ :=
  seedMap.comp CycleQ2IncidenceTimeCurve.sexticToParameter

private theorem sextic_section : sexticEval.comp C = RingHom.id ℂ := by
  apply RingHom.ext
  intro a
  exact (congrArg seedMap (CycleQ2GenericTimeDerivation.sexticToParameter_C a)).trans
    (CycleQ2IncidenceSeedFiber.seedMap_complex a)

theorem sexticEquation_map : MvPolynomial.map sexticEval (pointEquationF universalPoint) = pointEquationF point := by
  rw [sexticEval, ← MvPolynomial.map_map, universal_to_incidence, CycleQ2EtaleIncidenceCurve.seed_sextic,
    CycleQ2IncidenceChartSeedFiber.literal_pointEquationF]

private theorem sexticIdeal_map : (sexticIdeal universalPoint).map (MvPolynomial.map sexticEval) =
    sexticIdeal point := by
  rw [sexticIdeal, Ideal.map_span, Set.image_singleton, sexticEquation_map]
  rfl

private theorem spec_sexticEval : Spec.map (CommRingCat.ofHom sexticEval) = seedSextic := by
  rw [seedSextic, seedPointMorphism, CycleQ2IncidenceTimeCurve.parameterToSextics, ← Spec.map_comp]
  rfl

/-- The fixed fiber of the full sextic coefficient family is the very same
native weighted Proj, including its scheme structure. -/
def nativeToUniversal : Native ≅ FixedThreefold :=
  (CycleQ2LiteralAmbientProjFiber.fiberIso sexticEval C sextic_section (sexticIdeal universalPoint)
    (sexticIdeal point) sexticIdeal_map) ≪≫ pullback.congrHom spec_sexticEval rfl

private theorem congr_fst {X Y Z : Scheme} {f₁ f₂ : X ⟶ Z} (h : f₁ = f₂) (g : Y ⟶ Z) :
    (pullback.congrHom h (rfl : g = g)).hom ≫ pullback.fst f₂ g = pullback.fst f₁ g := by
  rw [pullback.congrHom_hom, pullback.lift_fst, Category.comp_id]

private theorem congr_snd {X Y Z : Scheme} {f₁ f₂ : X ⟶ Z} (h : f₁ = f₂) (g : Y ⟶ Z) :
    (pullback.congrHom h (rfl : g = g)).hom ≫ pullback.snd f₂ g = pullback.snd f₁ g := by
  rw [pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]

@[reassoc, simp] theorem nativeToUniversal_overComplex :
    nativeToUniversal.hom ≫ pullback.fst seedSextic universalAmbientToBase =
      weightedThreefoldToBase point := by
  change nativeToUniversal.hom ≫ pullback.fst seedSextic
    (CycleQ2LiteralAmbientProjFiber.toBase (sexticIdeal universalPoint)) = _
  rw [nativeToUniversal, Iso.trans_hom, Category.assoc, congr_fst]
  exact CycleQ2LiteralAmbientProjFiber.fiberIso_hom_fst _ _ _ _ _ _

@[reassoc, simp] theorem nativeToUniversal_snd :
    nativeToUniversal.hom ≫ pullback.snd seedSextic universalAmbientToBase =
      CycleQ2ThreefoldCoefficientMap.morphism sexticEval universalPoint point sexticEquation_map := by
  change nativeToUniversal.hom ≫ pullback.snd seedSextic
    (CycleQ2LiteralAmbientProjFiber.toBase (sexticIdeal universalPoint)) = _
  rw [nativeToUniversal, Iso.trans_hom, Category.assoc, congr_snd]
  exact CycleQ2LiteralAmbientProjFiber.fiberIso_hom_snd _ _ _ _ _ _

/-- Canonical identification between the actual target of the moving curve and
the smooth proper threefold carrying the surface trace and Kodaira–Spencer charts. -/
def fixedIso : FixedThreefold ≅ IncidenceFiber 57 := nativeToUniversal.symm ≪≫ nativeToIncidence

@[reassoc, simp] theorem fixedIso_overComplex : fixedIso.hom ≫ incidenceFiberToComplex 57 =
    pullback.fst seedSextic universalAmbientToBase := by
  apply (cancel_epi nativeToUniversal.hom).mp
  simp [fixedIso]

theorem fixed_proper : IsProper (pullback.fst seedSextic universalAmbientToBase) := by
  rw [← fixedIso_overComplex]
  let := incidenceFiber_proper 57
  infer_instance

theorem fixed_smooth : SmoothOfRelativeDimension 3 (pullback.fst seedSextic universalAmbientToBase) := by
  rw [← fixedIso_overComplex]
  exact IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension 3) literal_fiber_smooth fixedIso.hom

/-- The full proper moving curve, evaluated in the same threefold as the
closed trace surface and the ambient residue calculation. -/
def toSmoothThreefold (t : Fin 3 → ℂ) : Family t ⟶ IncidenceFiber 57 := toFixedThreefold t ≫ fixedIso.hom

@[reassoc, simp] theorem toSmoothThreefold_overComplex (t : Fin 3 → ℂ) :
    toSmoothThreefold t ≫ incidenceFiberToComplex 57 = toCurve t ≫ toComplex := by
  simp [toSmoothThreefold]

/-- The time-family morphism through the smooth model has the original
universal-sextic projection, preserving its given projective coordinates. -/
@[reassoc] theorem toSmoothThreefold_toUniversal (t : Fin 3 → ℂ) :
    toSmoothThreefold t ≫ nativeToIncidence.inv ≫
        CycleQ2ThreefoldCoefficientMap.morphism sexticEval universalPoint point sexticEquation_map =
      toOriginal t ≫ originalToAmbient t := by
  rw [← nativeToUniversal_snd]
  simp only [toSmoothThreefold, fixedIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, toFixedThreefold_original]

end CycleQ2LiteralAmbientCylinder

#print axioms CycleQ2LiteralAmbientCylinder.nativeToIncidence
#print axioms CycleQ2LiteralAmbientCylinder.nativeToUniversal
#print axioms CycleQ2LiteralAmbientCylinder.fixed_smooth
#print axioms CycleQ2LiteralAmbientCylinder.fixed_proper
#print axioms CycleQ2LiteralAmbientCylinder.toSmoothThreefold_overComplex
