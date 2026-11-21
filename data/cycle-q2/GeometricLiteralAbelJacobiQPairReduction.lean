import Proposal.GeometricLiteralAbelJacobiQPairCharts
import Proposal.GeometricLiteralAbelJacobiEvaluationFiber
import Proposal.GeometricLiteralThreefoldTestEdges

/-!
# Specialization of the cylinder test form on native pair rings

Reducing the moving curve modulo the parameter sends the inverted
weight-one ratio to its closed value. The resulting map of localizations
specializes the whole overlap point and its native two-form.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralAbelJacobiQPairReduction

open CategoryTheory AlgebraicGeometry CycleQ2LiteralAbelJacobiQPairCharts CycleQ2LiteralAbelJacobiContraction
  CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralCylinderEvaluation
  CycleQ2LiteralThreefoldResidueCoordinates CycleQ2LiteralThreefoldLiftTransition
  CycleQ2LiteralThreefoldResidueChartMaps CycleQ2LiteralThreefoldTestEdges
  CycleQ2ExteriorSectionNaturality

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  familyRing closedRing threefoldRing CycleQ2CurveParameterTangent.chartComplexAlgebra
  familyAlgebra familyComplexTower fixedAlgebra fixedTower reductionAlgebra fixedCurveTower familyReductionTower
  sourceFixedAlgebra sourceFixedTower sourceFixedLocalization

variable (t : Fin 3 → ℂ) (i : Fin 4) (k : Fin 3)

private abbrev beforeLocalization : B t i →ₐ[ℂ] APair t i k :=
  (IsScalarTower.toAlgHom ℂ (A t i) (APair t i k)).comp (IsScalarTower.toAlgHom ℂ (B t i) (A t i))

private theorem reduction_on_fixed (x : T i) : toClosed t i (movingMap t i x) = toCurve t i x :=
  (IsScalarTower.algebraMap_apply (T i) (B t i) (A t i) x).symm

private theorem reducedDenominator_unit :
    IsUnit (beforeLocalization t i k (movingMap t i (ratio i k))) := by
  change IsUnit (algebraMap (A t i) (APair t i k) (toClosed t i (movingMap t i (ratio i k))))
  rw [reduction_on_fixed]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- Reduction modulo the original dual-number parameter on the full pair. -/
def reduce : BPair t i k →ₐ[ℂ] APair t i k :=
  IsLocalization.Away.liftAlgHom (movingMap t i (ratio i k))
    (f := beforeLocalization t i k) (reducedDenominator_unit t i k)

@[simp] theorem reduce_localize (b : B t i) :
    reduce t i k (algebraMap (B t i) (BPair t i k) b) =
      algebraMap (A t i) (APair t i k) (toClosed t i b) :=
  IsLocalization.Away.lift_eq (S := BPair t i k) (g := (beforeLocalization t i k).toRingHom) _ (reducedDenominator_unit t i k) b

/-- Both routes from the threefold overlap agree on its full ring, including the inverse ratio. -/
theorem reduce_pairMap :
    (reduce t i k).comp (pairMap i k (movingMap t i)) = pairMap i k (toCurve t i) := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (ratio i k))
  apply RingHom.ext
  intro x
  change reduce t i k (pairMap i k (movingMap t i) (sourceMap i k x)) =
    pairMap i k (toCurve t i) (sourceMap i k x)
  rw [pairMap_source, pairMap_source, reduce_localize, reduction_on_fixed]

/-- The actual Čech edge computed from first-order lifts specializes as an integral two-form. -/
theorem reduce_testEdge :
    exteriorDifferentialMap (reduce t i k) 2 (edgeAt i k (pairMap i k (movingMap t i))) =
      edgeAt i k (pairMap i k (toCurve t i)) := by
  rw [edgeAt_map, reduce_pairMap]

@[reassoc] theorem reduce_toChart :
    Spec.map (CommRingCat.ofHom (reduce t i k).toRingHom) ≫ pairToChart i k (movingMap t i) =
      pairToChart i k (toCurve t i) ≫ Spec.map (CommRingCat.ofHom (toClosed t i)) := by
  unfold pairToChart
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  exact CommRingCat.hom_ext (RingHom.ext (reduce_localize t i k))

open CycleQ2IncidenceEtaleParameter CycleQ2IncidenceSeedFiberCover
  CycleQ2LiteralAbelJacobiEvaluationFiber CycleQ2LiteralAbelJacobiTimeCharts

/-- The reduction square is the one between the two original pair charts of the time family. -/
@[reassoc] theorem reduce_toTime (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V) :
    Spec.map (CommRingCat.ofHom (reduce t i k).toRingHom) ≫ thickPairChart V t hV i k =
      closedPairChart V t hV i k := by
  rw [thickPairChart, reduce_toChart_assoc, reduction_to_time]

end CycleQ2LiteralAbelJacobiQPairReduction
end

#print axioms CycleQ2LiteralAbelJacobiQPairReduction.reduce_pairMap
#print axioms CycleQ2LiteralAbelJacobiQPairReduction.reduce_testEdge
