import Proposal.GeometricLiteralAbelJacobiQPairCharts
import Proposal.GeometricLiteralAbelJacobiQAffineForms
import Proposal.GeometricLiteralAbelJacobiQTest
import Proposal.GeometricLiteralThreefoldOrbitCech

/-!
# The cylinder test form on the two-chart rings of the actual germ

On each first-order pair and on each closed seed pair the section defining
the pulled test class is the ordinary integral Kähler pullback along the
native homomorphism of localized coordinate rings.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralAbelJacobiQPairForms

open CategoryTheory Opposite AlgebraicGeometry CycleQ2LiteralAbelJacobiQPairCharts
  CycleQ2LiteralAbelJacobiQAffineForms CycleQ2LiteralAbelJacobiQPullback
  CycleQ2LiteralThreefoldHodgeCech CycleQ2LiteralThreefoldTestEdges
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceSeedFiberCover
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralCylinderEvaluation
  CycleQ2LiteralThreefoldResidueChartMaps CycleQ2LiteralThreefoldLiftTransition
  CycleQ2ExteriorSectionNaturality CycleQ2FiniteCechOrbitPullback CycleQ2FiniteInjectiveCech
  CycleQ2LiteralAbelJacobiQTest CycleQ2LiteralThreefoldTestClass CycleQ2LiteralThreefoldOrbitCech
  CycleQ2LiteralAmbientCharts

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  familyRing closedRing threefoldRing CycleQ2CurveParameterTangent.chartComplexAlgebra
  familyAlgebra familyComplexTower fixedAlgebra fixedTower reductionAlgebra fixedCurveTower
  sourceFixedAlgebra sourceFixedTower

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ) (hV : seedBasePoint ∈ V) (i : Fin 4) (k : Fin 3)
  (W : Threefold.Opens) (hW : W ≤ pairOpen i k)

abbrev thickForms := chartForms V t i k (thickPairChart V t hV i k) (pairMap i k (movingMap t i))
  (thickPair_toThreefold V t hV i k)

abbrev closedForms := chartForms V t i k (closedPairChart V t hV i k) (pairMap i k (toCurve t i))
  (closedPair_toThreefold V t hV i k)

/-- The moving germ of the actual test edge, on every subopen of its native pair. -/
theorem thick_q_test :
    (thickForms V t hV i k).val.app (op ((toThreefold V t) ⁻¹ᵁ W))
      ((qForms V t).val.app (op W) (overlapSection i k W hW (nativeEdge i k))) =
    nativeRealize (BPair t i k) ((thickPairChart V t hV i k ≫ toThreefold V t) ⁻¹ᵁ W) 2
      (edgeAt i k (pairMap i k (movingMap t i))) := by
  refine (chart_q_forms V t i k (thickPairChart V t hV i k) (pairMap i k (movingMap t i))
    (thickPair_toThreefold V t hV i k) W hW (nativeEdge i k)).trans ?_
  exact congrArg (nativeRealize (BPair t i k) _ 2) (nativeEdge_restrict i k (pairMap i k (movingMap t i)))

/-- The reduction of the actual pulled test edge on the closed seed pair. -/
theorem closed_q_test :
    (closedForms V t hV i k).val.app (op ((toThreefold V t) ⁻¹ᵁ W))
      ((qForms V t).val.app (op W) (overlapSection i k W hW (nativeEdge i k))) =
    nativeRealize (APair t i k) ((closedPairChart V t hV i k ≫ toThreefold V t) ⁻¹ᵁ W) 2
      (edgeAt i k (pairMap i k (toCurve t i))) := by
  refine (chart_q_forms V t i k (closedPairChart V t hV i k) (pairMap i k (toCurve t i))
    (closedPair_toThreefold V t hV i k) W hW (nativeEdge i k)).trans ?_
  exact congrArg (nativeRealize (APair t i k) _ 2) (nativeEdge_restrict i k (pairMap i k (toCurve t i)))

abbrev testEdgeValue (i j : Fin 4) (W : Threefold.Opens) (hi : W ≤ fixedOpen i) (hj : W ≤ fixedOpen j) :=
  edgeValue (familyHodgeSheaf V t) (cover (toThreefold V t).base fixedOpen) (testCocycle V t)
    i j ((toThreefold V t) ⁻¹ᵁ W) (fun _ hx => hi hx) (fun _ hx => hj hx)

/-- The increasing entries of the cocycle representing the derived pullback
are the images of the same native sections used for the local computation. -/
theorem testEdgeValue_lt (i j : Fin 4) (hij : i < j) (W : Threefold.Opens)
    (hi : W ≤ fixedOpen i) (hj : W ≤ fixedOpen j) :
    testEdgeValue V t i j W hi hj =
      (qForms V t).val.app (op W) (edge nativeEdge i j hij W (le_inf hi hj)) := by
  let f := toThreefold V t
  refine (edgeValue_pullOne f.base (qAdd V t) fixedOpen (hodgeCocycle nativeEdge face).val
    i j (P := W) (W := f ⁻¹ᵁ W) le_rfl hi hj).trans ?_
  rw [hodgeCocycle_edge_lt nativeEdge face i j hij]
  exact CycleQ2GeometricSheafLocalIso.res_self _ _ _

theorem thick_q_cocycle (i j : Fin 4) (hij : i < j) (W : Threefold.Opens)
    (hi : W ≤ fixedOpen i) (hj : W ≤ fixedOpen j) :
    let k := slot i j hij
    (thickForms V t hV i k).val.app (op ((toThreefold V t) ⁻¹ᵁ W))
        (testEdgeValue V t i j W hi hj) =
      nativeRealize (BPair t i k) ((thickPairChart V t hV i k ≫ toThreefold V t) ⁻¹ᵁ W) 2
        (edgeAt i k (pairMap i k (movingMap t i))) := by
  dsimp only
  refine (congrArg ((thickForms V t hV i (slot i j hij)).val.app (op ((toThreefold V t) ⁻¹ᵁ W)))
    (testEdgeValue_lt V t i j hij W hi hj)).trans ?_
  exact thick_q_test V t hV i (slot i j hij) W (by simpa only [pairOpen, succAbove_slot] using le_inf hi hj)

theorem closed_q_cocycle (i j : Fin 4) (hij : i < j) (W : Threefold.Opens)
    (hi : W ≤ fixedOpen i) (hj : W ≤ fixedOpen j) :
    let k := slot i j hij
    (closedForms V t hV i k).val.app (op ((toThreefold V t) ⁻¹ᵁ W))
        (testEdgeValue V t i j W hi hj) =
      nativeRealize (APair t i k) ((closedPairChart V t hV i k ≫ toThreefold V t) ⁻¹ᵁ W) 2
        (edgeAt i k (pairMap i k (toCurve t i))) := by
  dsimp only
  refine (congrArg ((closedForms V t hV i (slot i j hij)).val.app (op ((toThreefold V t) ⁻¹ᵁ W)))
    (testEdgeValue_lt V t i j hij W hi hj)).trans ?_
  exact closed_q_test V t hV i (slot i j hij) W (by simpa only [pairOpen, succAbove_slot] using le_inf hi hj)

end CycleQ2LiteralAbelJacobiQPairForms
end

#print axioms CycleQ2LiteralAbelJacobiQPairForms.thick_q_test
#print axioms CycleQ2LiteralAbelJacobiQPairForms.closed_q_test
#print axioms CycleQ2LiteralAbelJacobiQPairForms.thick_q_cocycle
#print axioms CycleQ2LiteralAbelJacobiQPairForms.closed_q_cocycle
