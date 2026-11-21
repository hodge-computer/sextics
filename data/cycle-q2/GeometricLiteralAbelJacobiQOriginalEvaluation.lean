import Proposal.GeometricLiteralAbelJacobiQPairVelocity
import Proposal.GeometricLiteralAbelJacobiEvaluationChart
import Proposal.GeometricLiteralAbelJacobiQEvaluationTransport
import Proposal.GeometricLiteralAbelJacobiQThickSection
import Proposal.GeometricCurvePairEvaluationLocalization

/-!
# Evaluation of the actual test edge in its original affine chart

The affine evaluation of the time family's test edge gives the ordinary
localized contraction on every smaller seed open. This computes the
actual input to the normalized first-order evaluation before gluing.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralAbelJacobiQNativeSeedEvaluation

open CategoryTheory Opposite AlgebraicGeometry CycleQ2GeometricSchemeDifferentialMap
  CycleQ2LiteralAbelJacobiQPairSeed CycleQ2LiteralAbelJacobiQPairSeedSections
  CycleQ2LiteralAbelJacobiQThickSection CycleQ2LiteralAbelJacobiQPairForms
  CycleQ2LiteralAbelJacobiQEvaluationTransport CycleQ2LiteralAbelJacobiQPairCharts
  CycleQ2LiteralAbelJacobiEvaluationFiber CycleQ2LiteralAbelJacobiEvaluationChart
  CycleQ2LiteralAbelJacobiEvaluationSeedForms CycleQ2LiteralAbelJacobiEvaluationAffine
  CycleQ2LiteralAbelJacobiTimeCharts CycleQ2LiteralAbelJacobiEvaluationRestriction
  CycleQ2LiteralAbelJacobiQPullback CycleQ2LiteralThreefoldHodgeCech CycleQ2LiteralAmbientCharts
  CycleQ2LiteralThreefoldTestEdges CycleQ2LiteralThreefoldResidueCoordinates
  CycleQ2LiteralThreefoldPairMotion CycleQ2CurvePairEvaluationLocalization CycleQ2CurvePairEvaluationSections
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralCylinderEvaluation CycleQ2LiteralAbelJacobiMovingNormal
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricAffineDifferentialSheaf CycleQ2GeometricSheafKaehlerMap
  CycleQ2LiteralMovingResidueAdjunction.AffineFrame CycleQ2LiteralMovingResidueCurve
  CycleQ2GeometricSectionDifferentials CycleQ2GeometricAffineOverlap
  CycleQ2LiteralThreefoldCurveTestSections
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceSeedFiberCover

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  familyRing closedRing threefoldRing CycleQ2CurveParameterTangent.chartComplexAlgebra
  familyComplexSMul familyComplexModule familyAlgebra familyComplexTower fixedAlgebra fixedTower
  reductionAlgebra fixedCurveTower familyReductionTower
  reductionPairAlgebra reductionPairTower baseAlgebra baseTower baseATower baseBTower
  ambientThickAlgebra ambientThickTower ambientClosedAlgebra ambientClosedTower ambientPairTower
attribute [local instance 2000] Algebra.toSMul Algebra.toModule
attribute [local instance] curveComplexOn

variable (t : Fin 3 → ℂ) (ht : AlgebraicIndependent ℚ t) (i : Fin 4) (k : Fin 3)

private abbrev closedDenominator := algebraMap (B t i) (A t i) (denominator t i k)

local instance closedLoc : IsLocalization.Away (closedDenominator t i k) (APair t i k) := by
  have e : closedDenominator t i k = toCurve t i (ratio i k) :=
    (IsScalarTower.algebraMap_apply (T i) (B t i) (A t i) (ratio i k)).symm
  rw [e]
  infer_instance

private theorem restrict_one (Z : (Spec (CommRingCat.of (A t i))).Opens)
    (hZ : Z ≤ openAt (closedDenominator t i k))
    (W : (Curve t).Opens) (hpair : W ≤ (pairToSeed t i k).opensRange)
    (l : (seedChart t i) ⁻¹ᵁ W ≤ Z) (ω : KaehlerDifferential ℂ (APair t i k)) :
    onSubopen (X := Spec (CommRingCat.of (A t i))) (affineDifferentialSheaf (A t i)) l
      (oneSection Z (localizedSectionsOn (closedDenominator t i k) (APair t i k) Z hZ)
        (localizedSectionsOn_constants _ _ _ _) ω) =
      (schemeDifferentialMap (seedChart t i) _ _ (seedChart_coefficient t i)).val.app (op W) (seedOne t i k W hpair ω) := by
  rw [seedOne_chart]
  apply sectionLift_restriction
  intro a
  let f := ((Spec (CommRingCat.of (A t i))).presheaf.map (homOfLE l).op).hom.comp
    (localizedSectionsOn (closedDenominator t i k) (APair t i k) Z hZ)
  have e : f = onAffine t i k W hpair := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (toCurve t i (ratio i k)))
    apply RingHom.ext
    intro r
    change (Spec (CommRingCat.of (A t i))).presheaf.map _
      ((Spec (CommRingCat.of (A t i))).presheaf.map _ ((localizedSections (closedDenominator t i k) (APair t i k))
        (algebraMap (A t i) (APair t i k) r))) = onAffine t i k W hpair (algebraMap (A t i) (APair t i k) r)
    rw [localizedSections_original, onAffine_base]
    rfl
  exact RingHom.congr_fun e a

variable (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V)
  (j : Fin 4) (hij : i < j) (U : Threefold.Opens) (hi : U ≤ fixedOpen i) (hj : U ≤ fixedOpen j)
  (W : (Curve t).Opens) (hpair : W ≤ (pairToSeed t i (slot i j hij)).opensRange)
  (l : (seedChart t i) ⁻¹ᵁ W ≤ mapToChart t i ⁻¹ᵁ thickDomain V t hV i U)

/-- Restricting the time-family test edge on the original first-order chart and
evaluating its normalized velocity gives the localized native contraction. -/
theorem affine_native :
    onSubopen (X := Spec (CommRingCat.of (A t i))) (affineDifferentialSheaf (A t i)) l
      ((evaluation (normalizedVelocity t i ht)).val.app (op (thickDomain V t hV i U))
        ((toThickTwoForms V t hV i).val.app (op ((toThreefold V t) ⁻¹ᵁ U)) (testEdgeValue V t i j U hi hj))) =
      (schemeDifferentialMap (seedChart t i) _ _ (seedChart_coefficient t i)).val.app (op W)
        (seedOne t i (slot i j hij) W hpair
          (contractRestrict ((pairVelocity t ht i (slot i j hij)).compAlgebraMap (FixedOverlap i (slot i j hij)))
            (nativeEdge i (slot i j hij)))) := by
  let k := slot i j hij
  let O := thickDomain V t hV i U
  let hU : U ≤ pairOpen i k := by simpa only [k, pairOpen, succAbove_slot] using le_inf hi hj
  let hO := withinDistinguished V t hV i k U hU
  let v := normalizedVelocity t i ht
  let w := pairVelocity t ht i k
  let ω := edgeAt i k (pairMap i k (movingMap t i))
  rw [test_thick V t hV i U j hij hi hj]
  have he := localized_evaluation_on (denominator t i k) (BPair t i k) (APair t i k)
    v w (pairVelocity_original t ht i k) O hO ω
  refine (congrArg (onSubopen (X := Spec (CommRingCat.of (A t i))) (affineDifferentialSheaf (A t i)) l) he).trans ?_
  rw [← pair_contract t i k w]
  exact restrict_one t i k _ _ W hpair l _

end CycleQ2LiteralAbelJacobiQNativeSeedEvaluation
end

#print axioms CycleQ2LiteralAbelJacobiQNativeSeedEvaluation.affine_native
