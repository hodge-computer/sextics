import Proposal.GeometricLiteralAbelJacobiQPairForms
import Proposal.GeometricLiteralAbelJacobiEvaluationRestriction

/-!
# The actual test section on the original distinguished open of the thick chart

Inside a first-order curve chart, the pulled test form is realized by the
canonical homomorphism from its pair localization to functions on the
distinguished open, followed by restriction. This computes the input of
the mixed evaluation on the original affine chart itself.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralAbelJacobiQThickSection

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
  CycleQ2LiteralAbelJacobiQPairCharts CycleQ2LiteralAbelJacobiQPairForms
  CycleQ2LiteralAbelJacobiQAffineForms CycleQ2LiteralAbelJacobiQPullback CycleQ2LiteralAbelJacobiQPullbackSections
  CycleQ2LiteralAbelJacobiTimeCharts CycleQ2LiteralAbelJacobiQChart CycleQ2LiteralAbelJacobiEvaluationRestriction
  CycleQ2LiteralThreefoldHodgeCech CycleQ2LiteralThreefoldTestEdges CycleQ2LiteralThreefoldResidueCoordinates
  CycleQ2LiteralThreefoldResidueChartMaps CycleQ2LiteralThreefoldLiftTransition CycleQ2LiteralAmbientCharts
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralCylinderEvaluation CycleQ2LiteralAbelJacobiMovingNormal
  CycleQ2GeometricAffineDifferentialSheaf CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSchemeDifferentialMap
  CycleQ2GeometricExteriorSheaf CycleQ2ExteriorSectionNaturality CycleQ2ChartExteriorBinding
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceSeedFiberCover

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  familyRing closedRing threefoldRing CycleQ2CurveParameterTangent.chartComplexAlgebra
  familyAlgebra familyComplexTower fixedAlgebra fixedTower reductionAlgebra fixedCurveTower
  sourceFixedAlgebra sourceFixedTower sourceFixedLocalization complexOn

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ) (hV : seedBasePoint ∈ V) (i : Fin 4) (k : Fin 3)
  (U : Threefold.Opens) (hU : U ≤ pairOpen i k)

abbrev thickDomain := (thickChart V t hV i ≫ toThreefold V t) ⁻¹ᵁ U
abbrev denominator := movingMap t i (ratio i k)
abbrev distinguished := PrimeSpectrum.basicOpen (denominator t i k)

include hU in
theorem withinDistinguished : thickDomain V t hV i U ≤ distinguished t i k :=
  ((thickChart V t hV i ≫ toThreefold V t).preimage_mono (hU.trans inf_le_right)).trans
    (thick_preimage_other V t hV i k).le

theorem fullDomain : thickDomain V t hV i (pairOpen i k) = distinguished t i k := by
  have h : (thickChart V t hV i ≫ toThreefold V t) ⁻¹ᵁ fixedOpen i = ⊤ := by
    rw [show thickChart V t hV i ≫ toThreefold V t = _ from thickChart_toSmoothThreefold V t hV i,
      chartInclusion]
    simp only [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top]
  rw [thickDomain, pairOpen, Scheme.Hom.preimage_inf, h, top_inf_eq, thick_preimage_other]

abbrev distinguishedEquiv := IsLocalization.algEquiv (Submonoid.powers (denominator t i k))
  (BPair t i k) (AffineSections (B t i) (distinguished t i k))

def thickSections : BPair t i k →+* AffineSections (B t i) (thickDomain V t hV i U) :=
  (((affineScheme (B t i)).presheaf.map (homOfLE (withinDistinguished V t hV i k U hU)).op).hom).comp
    (distinguishedEquiv t i k).toRingHom

theorem thickSections_base (b : B t i) : thickSections V t hV i k U hU (algebraMap (B t i) (BPair t i k) b) =
    algebraMap (B t i) (AffineSections (B t i) (thickDomain V t hV i U)) b := by
  change (affineScheme (B t i)).presheaf.map _ ((distinguishedEquiv t i k) (algebraMap (B t i) (BPair t i k) b)) = _
  rw [(distinguishedEquiv t i k).commutes]
  rfl

theorem thickSections_complex (z : ℂ) :
    thickSections V t hV i k U hU (algebraMap ℂ (BPair t i k) z) =
      coefficientOn (Spec.structureSheaf (B t i)) (affineCoefficient (B t i)) (thickDomain V t hV i U) z := by
  rw [IsScalarTower.algebraMap_apply ℂ (B t i) (BPair t i k), thickSections_base, affineCoefficientOn]

private abbrev actualMap := ((thickChart V t hV i).app ((toThreefold V t) ⁻¹ᵁ U)).hom.comp
  (overlapRingMap V t i k U hU)

/-- The actual section map on the full native overlap ring is the geometric
source chart localization, even before changing the thick chart to an affine pair. -/
theorem actualMap_pair : actualMap V t hV i k U hU =
    (thickSections V t hV i k U hU).comp (pairMap i k (movingMap t i)).toRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (ratio i k))
  apply RingHom.ext
  intro a
  change (thickChart V t hV i ≫ toThreefold V t).app U
      (((overlapAlgebraMap i k U hU).comp (sourceMap i k)) a) =
    thickSections V t hV i k U hU (pairMap i k (movingMap t i) (sourceMap i k a))
  rw [overlapAlgebraMap_source, pairMap_source, thickSections_base]
  exact chart_app (fixedChart i).symm (movingMap t i).toRingHom _ (thickChart_toSmoothThreefold V t hV i)
    U (hU.trans inf_le_left) a

abbrev realize (w : ⋀[BPair t i k]^2 (KaehlerDifferential ℂ (BPair t i k))) :=
  exteriorSectionLift (Spec.structureSheaf (B t i)) (affineCoefficient (B t i)) (affineDifferentialSheaf (B t i))
    (affineUniversalDifferential (B t i)) (thickDomain V t hV i U)
    (thickSections V t hV i k U hU) (thickSections_complex V t hV i k U hU) 2 w

theorem native_thick (ω : NativeForms i k) :
    (toThickTwoForms V t hV i).val.app (op ((toThreefold V t) ⁻¹ᵁ U))
        ((qForms V t).val.app (op U) (overlapSection i k U hU ω)) =
      realize V t hV i k U hU (exteriorDifferentialMap (pairMap i k (movingMap t i)) 2 ω) := by
  rw [qForms_overlapSection]
  refine (exteriorPull_sectionLift (thickChart V t hV i) (affineCoefficient (B t i)) (familyCoefficient V t)
    (thickChart_coefficient V t hV i) _ _ (overlapRingMap_complex V t i k U hU) 2 ω).trans ?_
  symm
  apply exteriorSectionLift_differentialMap
  intro a
  exact (RingHom.congr_fun (actualMap_pair V t hV i k U hU) a).symm

theorem test_thick (j : Fin 4) (hij : i < j) (hi : U ≤ fixedOpen i) (hj : U ≤ fixedOpen j) :
    (toThickTwoForms V t hV i).val.app (op ((toThreefold V t) ⁻¹ᵁ U)) (testEdgeValue V t i j U hi hj) =
      realize V t hV i (slot i j hij) U (by simpa only [pairOpen, succAbove_slot] using le_inf hi hj)
        (edgeAt i (slot i j hij) (pairMap i (slot i j hij) (movingMap t i))) := by
  refine (congrArg ((toThickTwoForms V t hV i).val.app _) (testEdgeValue_lt V t i j hij U hi hj)).trans ?_
  let h := show U ≤ pairOpen i (slot i j hij) by simpa only [pairOpen, succAbove_slot] using le_inf hi hj
  refine (native_thick V t hV i (slot i j hij) U h (nativeEdge i _)).trans ?_
  exact congrArg (realize V t hV i (slot i j hij) U h) (nativeEdge_restrict i _ _)

end CycleQ2LiteralAbelJacobiQThickSection
end

#print axioms CycleQ2LiteralAbelJacobiQThickSection.test_thick
