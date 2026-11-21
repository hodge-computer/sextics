import Proposal.GeometricLiteralThreefoldOrbitAction
import Proposal.GeometricLiteralAbelJacobiEvaluationFiber
import Proposal.GeometricLiteralAbelJacobiQPullback
import Proposal.GeometricSeedSectionSheafCurveBinding

/-!
# The central fibre of the cylinder projection is the original curve embedding

The composite through the genuine Cartier surface is the specialization
of the time-family morphism to the fixed smooth sextic. The equality holds
on the entire seed scheme and preserves the original polynomial coordinates.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldSeedProjection

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
  CycleQ2LiteralAbelJacobiQPullback CycleQ2LiteralAbelJacobiEvaluationFiber
  CycleQ2LiteralAbelJacobiTimeFamily CycleQ2LiteralAbelJacobiTimeProjection
  CycleQ2LiteralIncidenceTimeCurve CycleQ2LiteralIncidenceCylinderMap CycleQ2LiteralAmbientCylinder
  CycleQ2LiteralThreefoldOrbitAction CycleQ2LiteralAmbientSurface
  CycleQ2RelativeCurveSeedProj CycleQ2RelativeCurveSeedMap CycleQ2RelativeConstantCurveFiber
  CycleQ2GeometricSurfaceAdjunction CycleQ2SeedSectionSheafCurveBinding
  CycleQ2SpecializedProjectiveCurve CycleQ2GeometricIncidenceProj
  CycleQ2IncidenceFamilyContainment CycleQ2IncidenceEtaleParameter CycleQ2IncidenceTimeCurve
  CycleQ2IncidenceChartFiberScheme CycleQ2GeometricCartierNormalLift
  CycleQ2IncidenceSeedFiberCover

attribute [local instance] CycleQ2IncidenceTimeCurve.timeParameterCommRing
  CycleQ2IncidenceSeedFiber.seedAlgebra

private theorem seedSurface_square :
    seedSurfaceToIncidence ≫ surfaceToThreefold incidencePoint ≫
      CycleQ2ThreefoldCoefficientMap.morphism sexticToParameter universalPoint incidencePoint universal_to_incidence =
    literalCartierProjectiveIso.hom ≫ surfaceToNative ≫
      CycleQ2ThreefoldCoefficientMap.morphism sexticEval universalPoint point sexticEquation_map := by
  have e : seedSurfaceGradedMap.comp ((surfaceThreefoldRingMap incidencePoint).comp
        (CycleQ2ThreefoldCoefficientMap.graded sexticToParameter universalPoint incidencePoint universal_to_incidence)) =
      literalFromCartierGraded.comp (toTraceGraded.comp
        (CycleQ2ThreefoldCoefficientMap.graded sexticEval universalPoint point sexticEquation_map)) := by
    apply GradedRingHom.ext
    intro z
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective z
    change seedSurfaceSpecialization (Ideal.Quotient.mk (pointEquations incidencePoint) (MvPolynomial.map sexticToParameter p)) =
      literalFromCartierGraded (surfaceQuotient 57 1 (MvPolynomial.map sexticEval p))
    rw [seedSurfaceSpecialization_mk, literalFromCartierGraded_polynomial, MvPolynomial.map_map]
  change Proj.map _ _ ≫ Proj.map _ _ ≫ Proj.map _ _ = Proj.map _ _ ≫ Proj.map _ _ ≫ Proj.map _ _
  simp only [← Proj.map_comp, e]

private instance : IsClosedImmersion seedSextic := by
  apply isClosedImmersion_of_comp_eq_id (Spec.map (CommRingCat.ofHom
    (MvPolynomial.C : ℂ →+* CycleQ2IncidenceTimeCurve.SexticRing)))
  simp only [seedSextic, seedPointMorphism, parameterToSextics, ← Spec.map_comp, ← Spec.map_id]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact (congrArg seedMap (CycleQ2GenericTimeDerivation.sexticToParameter_C z)).trans
    (CycleQ2IncidenceSeedFiber.seedMap_complex z)

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ) (hV : seedBasePoint ∈ V)

@[reassoc] private theorem seedToTime_original :
    seedToTime t V hV ≫ familyToFull V t ≫ CycleQ2LiteralIncidenceTimeFamily.toOriginal t =
      seedCurveToRelative t := by
  simp only [seedToTime, seedIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc (pullback.snd (seedLift V hV) (projection V t)) (familyToFull V t),
    IsPullback.isoPullback_inv_snd_assoc, CycleQ2LiteralIncidenceTimeFamily.seedIso_toOriginal]

/-- Equality of the two actual scheme morphisms on the entire projective seed curve. -/
@[reassoc] theorem seed_projection :
    seedToTime t V hV ≫ toThreefold V t = curveToSurface t ≫ surfaceToFiber := by
  let incl := pullback.snd seedSextic universalAmbientToBase
  have left : toThreefold V t ≫ fixedIso.inv ≫ incl =
      familyToFull V t ≫ CycleQ2LiteralIncidenceTimeFamily.toOriginal t ≫ originalToAmbient t := by
    change (CycleQ2LiteralAbelJacobiTimeProjection.q V t ≫ fixedIso.hom) ≫ fixedIso.inv ≫ incl = _
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    change (familyToFull V t ≫ toFixedThreefold t) ≫ pullback.snd seedSextic universalAmbientToBase = _
    rw [Category.assoc, toFixedThreefold_original]
  have right : surfaceToFiber ≫ fixedIso.inv ≫ incl = surfaceToNative ≫
      CycleQ2ThreefoldCoefficientMap.morphism sexticEval universalPoint point sexticEquation_map := by
    rw [← surfaceToNative_toIncidence, Category.assoc]
    simp only [fixedIso, Iso.trans_inv, Iso.symm_inv, Category.assoc, Iso.hom_inv_id_assoc,
      incl, nativeToUniversal_snd]
  apply (cancel_mono (fixedIso.inv ≫ incl)).mp
  rw [Category.assoc, Category.assoc, left, right, seedToTime_original_assoc, originalToAmbient,
    ← Category.assoc, seedCurveToRelative_surface_square, Category.assoc, seedSurface_square,
    curveToSurface, Category.assoc]

end CycleQ2LiteralThreefoldSeedProjection
end

#print axioms CycleQ2LiteralThreefoldSeedProjection.seed_projection
