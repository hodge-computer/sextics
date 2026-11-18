import Proposal.GeometricLiteralThreefoldGermCoordinates
import Proposal.GeometricLiteralThreefoldVertexPoint

/-!
# Reduction of the common first-order overlap to the original central curve

Reducing the moving coefficient homomorphism is the pullback by the
original cylinder projection on the central curve. In either chart its
coordinates are exactly those used by the native moving velocity.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace CycleQ2LiteralThreefoldGermReduction

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial
  CycleQ2LiteralThreefoldGermCoordinates CycleQ2LiteralThreefoldVertexPoint
  CycleQ2LiteralAbelJacobiEvaluationFiber CycleQ2LiteralAbelJacobiEvaluationVelocity
  CycleQ2LiteralThreefoldVertexMotion CycleQ2LiteralAbelJacobiQPullback
  CycleQ2LiteralThreefoldHodgeCech CycleQ2LiteralAmbientCharts
  CycleQ2LiteralThreefoldResidueCoordinates CycleQ2LiteralThreefoldResidueChartMaps
  CycleQ2LiteralThreefoldChartLift CycleQ2LiteralThreefoldLiftTransition
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralProjectiveIntersections
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceSeedFiberCover
  CycleQ2FirstOrderCurve CycleQ2FirstOrderCurveCharts CycleQ2FirstOrderCurveSeedFiber
  CycleQ2GeometricAffineChartSections CycleQ2LiteralMovingResidueAdjunction.AffineFrame
  CycleQ2LiteralThreefoldCurveTestSections

attribute [local instance] sourceFixedAlgebra sourceFixedTower germAlgebra seedSectionAlgebra reductionOn complexOn

private theorem appLE_coincide {X Y : Scheme.{0}} {f g : X ⟶ Y} (e : f = g) (U : Y.Opens)
    (W : X.Opens) (hf : W ≤ f ⁻¹ᵁ U) (hg : W ≤ g ⁻¹ᵁ U) : f.appLE U W hf = g.appLE U W hg := by subst g; rfl

variable (t : Fin 3 → ℂ) (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V)
  (i : Fin 4) (k : Fin 3) (G : (firstOrderCurve t).Opens)
  (hi : G ≤ firstOrderCurveCoordinateOpen t i) (hj : G ≤ firstOrderCurveCoordinateOpen t (i.succAbove k))

private abbrev Z := seedCurveToFirstOrderCurve t ⁻¹ᵁ G
abbrev seedProjection := seedToTime t V hV ≫ toThreefold V t

theorem projection_eq : seedCurveToFirstOrderCurve t ≫ germProjection t V hV = seedProjection t V hV :=
  (Category.assoc _ _ _).symm.trans (congrArg (· ≫ toThreefold V t) (seed_germ_to_time t V hV))

include hi hj in
theorem seed_within : Z t G ≤ seedProjection t V hV ⁻¹ᵁ overlapOpen i k := by
  rw [← projection_eq]
  exact (seedCurveToFirstOrderCurve t).preimage_mono (within_overlap t V hV i k G hi hj)

theorem reduce (x : FixedOverlap i k) :
    (seedCurveToFirstOrderCurve t).app G (overlapHom t V hV i k G hi hj x) =
    (seedProjection t V hV).appLE (overlapOpen i k) (Z t G) (seed_within t V hV i k G hi hj)
      (overlapAlgebraMap i k (overlapOpen i k) le_rfl x) := by
  let j := seedCurveToFirstOrderCurve t
  let g := germProjection t V hV
  let U := overlapOpen i k
  let r := overlapAlgebraMap i k U le_rfl x
  let h := within_overlap t V hV i k G hi hj
  change j.app G (g.appLE U G h r) = _
  rw [j.app_eq_appLE]
  exact (ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE j g U G (j ⁻¹ᵁ G) h le_rfl) r).trans
    (ConcreteCategory.congr_hom (appLE_coincide (projection_eq t V hV) U (Z t G) _ _) r)

theorem source_chart (p : Vertex) (hp : i = p.2.succ) (hW : Z t G ≤ vertexOpen t p)
    (b : MvPolynomial (Option (Fin 3)) ℂ) :
    (seedCurveToFirstOrderCurve t).app G (overlapHom t V hV i k G hi hj (sourceMap i k (q i b))) =
      ambientPoint t p (Z t G) hW (q p.2.succ b) := by
  subst i
  let U := overlapOpen p.2.succ k
  refine (reduce t V hV _ k G hi hj _).trans ?_
  change (seedProjection t V hV).appLE U _ _
    (((overlapAlgebraMap p.2.succ k U le_rfl).comp (sourceMap p.2.succ k)) _) = _
  rw [overlapAlgebraMap_source]
  exact (ambientPoint_on_subopen V t hV p U inf_le_left _ hW _ _).symm

theorem target_chart (p : Vertex) (hp : i.succAbove k = p.2.succ) (hW : Z t G ≤ vertexOpen t p)
    (b : MvPolynomial (Option (Fin 3)) ℂ) :
    (seedCurveToFirstOrderCurve t).app G (overlapHom t V hV i k G hi hj (fixedTargetMap i k (q (i.succAbove k) b))) =
      ambientPoint t p (Z t G) hW (q p.2.succ b) := by
  let U := overlapOpen i k
  have hU : U ≤ fixedOpen p.2.succ := hp ▸ (show U ≤ fixedOpen (i.succAbove k) from inf_le_right)
  refine (reduce t V hV _ k G hi hj _).trans ?_
  change (seedProjection t V hV).appLE U _ _
    (((overlapAlgebraMap i k U le_rfl).comp (fixedTargetMap i k)) _) = _
  rw [overlapAlgebraMap_target]
  have z {j l : Fin 4} (eq : j = l) (a : U ≤ fixedOpen j) (c : U ≤ fixedOpen l) :
      chartAlgebraMap j U a (q j b) = chartAlgebraMap l U c (q l b) := by subst l; rfl
  exact (congrArg ((seedProjection t V hV).appLE U _ _) (z hp inf_le_right hU)).trans
    (ambientPoint_on_subopen V t hV p U hU _ hW _ _).symm

end CycleQ2LiteralThreefoldGermReduction
end

#print axioms CycleQ2LiteralThreefoldGermReduction.source_chart
#print axioms CycleQ2LiteralThreefoldGermReduction.target_chart
