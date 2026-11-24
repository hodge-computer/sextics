import Proposal.GeometricLiteralThreefoldLiftTransition
import Proposal.GeometricLiteralAbelJacobiQAffineForms
import Proposal.GeometricLiteralAbelJacobiQChart
import Proposal.GeometricLiteralAbelJacobiEvaluationVelocity

/-!
# Fixed-overlap coordinates on a common open of the actual infinitesimal curve

The pullback of the fixed overlap ring goes to the functions on the given
first-order open. In each of the two ambient charts, evaluating its functions
recovers the actual moving equation map, including the weighted transition.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace CycleQ2LiteralThreefoldGermCoordinates

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
  CycleQ2LiteralAbelJacobiEvaluationGerm CycleQ2LiteralAbelJacobiEvaluationFiber
  CycleQ2LiteralAbelJacobiEvaluationVelocity CycleQ2LiteralAbelJacobiQPullback
  CycleQ2LiteralAbelJacobiQAffineForms CycleQ2LiteralAbelJacobiTimeCharts
  CycleQ2LiteralAbelJacobiQChart CycleQ2LiteralThreefoldHodgeCech CycleQ2LiteralAmbientCharts
  CycleQ2LiteralThreefoldResidueCoordinates CycleQ2LiteralThreefoldResidueChartMaps
  CycleQ2LiteralThreefoldLiftTransition CycleQ2LiteralAbelJacobiContraction
  CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralCylinderEvaluation
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceSeedFiberCover
  CycleQ2FirstOrderCurve CycleQ2FirstOrderCurveCharts CycleQ2FirstOrderCurveSeedFiber
  CycleQ2GeometricAffineChartSections CycleQ2GeometricDifferentialSheaf CycleQ2GeometricAffineDifferentialSheaf

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  familyRing threefoldRing closedRing CycleQ2CurveParameterTangent.chartComplexAlgebra
  familyAlgebra familyComplexTower sourceFixedAlgebra sourceFixedTower germAlgebra complexOn

variable (t : Fin 3 → ℂ) (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V)

abbrev germProjection := germToTime t V hV ≫ toThreefold V t

theorem germProjection_overComplex : germProjection t V hV ≫ structureMap = germStructure t :=
  (Category.assoc _ _ _).trans ((congrArg (germToTime t V hV ≫ ·) (toThreefold_overComplex V t)).trans
    (germToTime_overComplex t V hV))

theorem chart_square (i : Fin 4) : firstOrderChartToCurve t i ≫ germProjection t V hV =
    Spec.map (CommRingCat.ofHom (toFamily t i)) ≫ chartInclusion i := by
  simpa only [thickChart, germToTime, germProjection, toThreefold, Category.assoc] using
    thickChart_toSmoothThreefold V t hV i

theorem within_chart (i : Fin 4) : firstOrderCurveCoordinateOpen t i ≤
    germProjection t V hV ⁻¹ᵁ fixedOpen i := by
  intro x hx
  obtain ⟨y,rfl⟩ := hx
  change (firstOrderChartToCurve t i ≫ germProjection t V hV) y ∈ fixedOpen i
  rw [chart_square]
  exact ((fixedChart i).hom (Spec.map (CommRingCat.ofHom (toFamily t i)) y)).property

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem pull_chart (i : Fin 4) (U : Threefold.Opens) (hU : U ≤ fixedOpen i)
    (G : (firstOrderCurve t).Opens) (hG : G ≤ germProjection t V hV ⁻¹ᵁ U) (a : T i) :
    (firstOrderChartToCurve t i).app G
      ((germProjection t V hV).appLE U G hG (chartAlgebraMap i U hU a)) =
      algebraMap (B t i) (AffineSections (B t i) ((firstOrderChartToCurve t i) ⁻¹ᵁ G)) (toFamily t i a) := by
  let j := firstOrderChartToCurve t i
  let g := germProjection t V hV
  let y := chartAlgebraMap i U hU a
  change j.app G (g.appLE U G hG y) = _
  rw [j.app_eq_appLE]
  refine (ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE j g U G (j ⁻¹ᵁ G) hG le_rfl) y).trans ?_
  exact chart_appLE (fixedChart i).symm (toFamily t i) (j ≫ g) (chart_square t V hV i) U hU _ _ a

variable (i : Fin 4) (k : Fin 3) (G : (firstOrderCurve t).Opens)
  (hi : G ≤ firstOrderCurveCoordinateOpen t i) (hj : G ≤ firstOrderCurveCoordinateOpen t (i.succAbove k))

abbrev overlapOpen := fixedOpen i ⊓ fixedOpen (i.succAbove k)

include hi hj in
theorem within_overlap : G ≤ germProjection t V hV ⁻¹ᵁ overlapOpen i k :=
  le_inf (hi.trans (within_chart t V hV i)) (hj.trans (within_chart t V hV _))

/-- Both ambient charts are evaluated by this one geometric homomorphism. -/
def overlapHom : FixedOverlap i k →ₐ[ℂ] GermRing t G where
  toRingHom := ((germProjection t V hV).appLE _ G (within_overlap t V hV i k G hi hj)).hom.comp
    (overlapAlgebraMap i k (overlapOpen i k) le_rfl).toRingHom
  commutes' c := by
    let g := germProjection t V hV
    let U := overlapOpen i k
    let h := within_overlap t V hV i k G hi hj
    change g.appLE U G h (overlapAlgebraMap i k U le_rfl (algebraMap ℂ _ c)) = _
    rw [(overlapAlgebraMap i k U le_rfl).commutes]
    change (firstOrderCurve t).presheaf.map (homOfLE h).op
      (g.app U (coefficientOn Threefold.sheaf (schemeCoefficient structureMap) U c)) = _
    rw [coefficientOn_app, germProjection_overComplex]
    exact CycleQ2GeometricTwistedDifferential.coefficientOn_restrict (firstOrderCurve t).sheaf (germCoefficient t) h c

theorem source (a : T i) :
    (firstOrderChartToCurve t i).app G (overlapHom t V hV i k G hi hj (sourceMap i k a)) =
      algebraMap (B t i) (AffineSections (B t i) ((firstOrderChartToCurve t i) ⁻¹ᵁ G)) (toFamily t i a) := by
  let U := overlapOpen i k
  change (firstOrderChartToCurve t i).app G ((germProjection t V hV).appLE U G _
    (((overlapAlgebraMap i k U le_rfl).comp (sourceMap i k)) a)) = _
  rw [overlapAlgebraMap_source]
  exact pull_chart t V hV i U inf_le_left G _ a

theorem target (a : T (i.succAbove k)) :
    (firstOrderChartToCurve t (i.succAbove k)).app G (overlapHom t V hV i k G hi hj (fixedTargetMap i k a)) =
      algebraMap (B t (i.succAbove k)) (AffineSections (B t (i.succAbove k))
        ((firstOrderChartToCurve t (i.succAbove k)) ⁻¹ᵁ G)) (toFamily t (i.succAbove k) a) := by
  let U := overlapOpen i k
  change (firstOrderChartToCurve t (i.succAbove k)).app G ((germProjection t V hV).appLE U G _
    (((overlapAlgebraMap i k U le_rfl).comp (fixedTargetMap i k)) a)) = _
  rw [overlapAlgebraMap_target]
  exact pull_chart t V hV _ U inf_le_right G _ a

end CycleQ2LiteralThreefoldGermCoordinates
end

#print axioms CycleQ2LiteralThreefoldGermCoordinates.source
#print axioms CycleQ2LiteralThreefoldGermCoordinates.target
