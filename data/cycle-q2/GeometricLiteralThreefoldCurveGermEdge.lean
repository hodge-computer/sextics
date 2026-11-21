import Proposal.GeometricLiteralThreefoldGermReduction
import Proposal.GeometricLiteralThreefoldGermMotion
import Proposal.GeometricLiteralThreefoldNormalizedEdge
import Proposal.GeometricLiteralThreefoldCommonSpeed
import Proposal.GeometricLiteralThreefoldCurveAdaptedValue

/-!
# The corrected ambient edge on a genuine affine of the infinitesimal curve

The two independent original chart speeds both send the parameter section
to one. The normalized mixed-edge identity therefore uses the actual
vertex one-forms of the curve and its actual adapted Kodaira–Spencer edge.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace CycleQ2LiteralThreefoldCurveGermEdge

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
  CycleQ2LiteralThreefoldGermCoordinates CycleQ2LiteralThreefoldGermReduction CycleQ2LiteralThreefoldGermMotion
  CycleQ2LiteralThreefoldCurveAdaptedValue CycleQ2LiteralThreefoldCurveVertexLifts CycleQ2LiteralThreefoldCurveVertexCochain
  CycleQ2LiteralThreefoldCurveTestSections CycleQ2LiteralThreefoldVertexMotion CycleQ2LiteralThreefoldVertexPointBinding
  CycleQ2LiteralThreefoldSurfaceTestLifts CycleQ2LiteralThreefoldChartLift CycleQ2LiteralThreefoldResidueCoordinates
  CycleQ2LiteralThreefoldResidueChartMaps CycleQ2LiteralThreefoldLiftTransition CycleQ2LiteralThreefoldLiftDifference
  CycleQ2LiteralThreefoldTestEdges
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralCylinderEvaluation
  CycleQ2LiteralAbelJacobiEvaluationFiber CycleQ2LiteralAbelJacobiEvaluationVelocity CycleQ2LiteralAbelJacobiEvaluationChart
  CycleQ2LiteralAbelJacobiEvaluationFiberSections CycleQ2LiteralThreefoldCommonSpeed CycleQ2ThreefoldContractionAlongMap
  CycleQ2LiteralMovingResidueAdjunction.AffineFrame CycleQ2LiteralNativeGaugeSections CycleQ2LiteralProjectiveIntersections
  CycleQ2FirstOrderCurve CycleQ2FirstOrderCurveSeedFiber CycleQ2FirstOrderCurveCharts
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceSeedFiberCover CycleQ2SeedSectionSheafCurveBinding
  CycleQ2LiteralProjectiveIntersectionComplex CycleQ2GeometricAffineDifferentialSheaf

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  familyRing closedRing threefoldRing CycleQ2CurveParameterTangent.chartComplexAlgebra
  familyAlgebra familyComplexTower fixedAlgebra fixedTower reductionAlgebra fixedCurveTower familyReductionTower
  curveComplexOn closedComplexAlgebra sourceFixedAlgebra sourceFixedTower germAlgebra seedSectionAlgebra reductionOn
  CycleQ2LiteralAbelJacobiEvaluationFiberVelocity.sectionTower

variable (t : Fin 3 → ℂ) (ht : AlgebraicIndependent ℚ t) (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V)
 (s : Finset Vertex) (u v : Vertex) (hu : u ∈ s) (hv : v ∈ s)
 (G : (firstOrderCurve t).Opens) (huG : G ≤ firstOrderCurveCoordinateOpen t (chartIndex u))
 (hvG : G ≤ firstOrderCurveCoordinateOpen t (chartIndex v))
 (k : Fin 3) (h : (chartIndex u).succAbove k = chartIndex v)

abbrev seedOpen := seedCurveToFirstOrderCurve t ⁻¹ᵁ G
variable (hW : seedOpen t G ≤ (curveToSurface t) ⁻¹ᵁ closedOpen s)

private abbrev within (p : Vertex) (hp : p ∈ s) :=
  withinVertex t s p hp (seedOpen t G) hW

private abbrev g := overlapHom t V hV (chartIndex u) k G huG (h.symm ▸ hvG)
private abbrev ρ := (IsScalarTower.toAlgHom ℂ (GermRing t G) (SeedRing t G)).comp (g t V hV u v G huG hvG k h)

private abbrev velocity (p : Vertex) (hp : G ≤ firstOrderCurveCoordinateOpen t (chartIndex p)) :=
  onOpen t (chartIndex p) (normalizedVelocity t (chartIndex p) ht) G hp

def testContraction : KaehlerDifferential ℂ (SeedRing t G) := by
  let d := g t V hV u v G huG hvG k h
  let f := ρ t V hV u v G huG hvG k h
  letI := d.toRingHom.toAlgebra
  letI := IsScalarTower.of_algHom d
  letI := f.toRingHom.toAlgebra
  letI := IsScalarTower.of_algHom f
  letI : IsScalarTower (FixedOverlap (chartIndex u) k) (GermRing t G) (SeedRing t G) := IsScalarTower.of_algebraMap_eq' rfl
  exact contractRestrict ((velocity t ht G u huG).compAlgebraMap (FixedOverlap (chartIndex u) k)) (nativeEdge (chartIndex u) k)

theorem source_position (r : T (chartIndex u)) :
    ρ t V hV u v G huG hvG k h (sourceMap (chartIndex u) k r) =
      ambientPoint t u (seedOpen t G) (within t s G hW u hu) r := by
  obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective r
  exact source_chart t V hV _ k G huG (h.symm ▸ hvG) u rfl _ z

theorem source_speed (r : T (chartIndex u)) :
    velocity t ht G u huG (g t V hV u v G huG hvG k h (sourceMap (chartIndex u) k r)) =
      ambientMotion t u (seedOpen t G) (within t s G hW u hu) (normalizedVelocity t (chartIndex u) ht) r :=
  onOpen_eq_ambient t u G huG _ _ r _ (CycleQ2LiteralThreefoldGermCoordinates.source t V hV _ k G huG _ r)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem target_speed_reindex {i j : Fin 4} (ij : i = j) (x : GermRing t G)
    (p : MvPolynomial (Option (Fin 3)) ℂ)
    (hx : (firstOrderChartToCurve t i).app G x = algebraMap (B t i) (AffineSections (B t i)
      ((firstOrderChartToCurve t i) ⁻¹ᵁ G)) (toFamily t i (q i p))) :
    (firstOrderChartToCurve t j).app G x = algebraMap (B t j) (AffineSections (B t j)
      ((firstOrderChartToCurve t j) ⁻¹ᵁ G)) (toFamily t j (q j p)) := by subst j; exact hx

theorem target_speed (p : MvPolynomial (Option (Fin 3)) ℂ) :
    velocity t ht G v hvG (g t V hV u v G huG hvG k h (fixedTargetMap (chartIndex u) k (q _ p))) =
      ambientMotion t v (seedOpen t G) (within t s G hW v hv) (normalizedVelocity t (chartIndex v) ht) (q _ p) :=
  onOpen_eq_ambient t v G hvG _ _ (q _ p) _ (target_speed_reindex t G h _ p
    (CycleQ2LiteralThreefoldGermCoordinates.target t V hV _ k G huG _ (q _ p)))

theorem corrected_on_germ (ha : IsAffineOpen G) :
    testContraction t ht V hV u v G huG hvG k h + rawVertex t ht s v hv (seedOpen t G) hW =
      rawVertex t ht s u hu (seedOpen t G) hW + adapted t ht s u v hu hv (seedOpen t G) hW := by
  let W := seedOpen t G
  let f := ambientPoint t u W (within t s G hW u hu)
  let f' := ambientPoint t v W (within t s G hW v hv)
  let d := g t V hV u v G huG hvG k h
  let x := curveLift t s u hu W hW u.1 ⟨u.2,hu⟩
  let y := curveLift t s v hv W hW u.1 ⟨u.2,hu⟩
  let z := curveLift t s v hv W hW v.1 ⟨v.2,hv⟩
  have lx : LiesOver x f := by
    rw [show f = _ from (ambientPoint_eq_native t s ⟨u,hu⟩ u hu W hW).symm]
    exact curveLift_over t s u hu W hW u.1 ⟨u.2,hu⟩
  have ly : LiesOver y f' := by
    rw [show f' = _ from (ambientPoint_eq_native t s ⟨v,hv⟩ v hv W hW).symm]
    exact curveLift_over t s v hv W hW u.1 ⟨u.2,hu⟩
  have lz : LiesOver z f' := by
    rw [show f' = _ from (ambientPoint_eq_native t s ⟨v,hv⟩ v hv W hW).symm]
    exact curveLift_over t s v hv W hW v.1 ⟨v.2,hv⟩
  haveI := seedSections_smooth t G ha ht
  haveI := seedSections_exteriorTwo t G ha ht
  apply CycleQ2LiteralThreefoldNormalizedEdge.corrected (chartIndex u) (chartIndex v) k d f f' h
    (AlgHom.ext (source_position t V hV s u v hu G huG hvG k h hW))
    (fun p => target_chart t V hV _ k G huG (h.symm ▸ hvG) v h (within t s G hW v hv) p) x y z
    (curveLift_normalizes t s v hv W hW u hu u.1 ⟨u.2,hu⟩) lx ly lz (epsilonSection t G)
    (restriction_surjective t G ha) (restriction_kernel t G ha) (velocity t ht G u huG) (velocity t ht G v hvG)
    ((onOpen_epsilon t _ _ (normalizedVelocity_epsilon t _ ht) G huG).trans
      (onOpen_epsilon t _ _ (normalizedVelocity_epsilon t _ ht) G hvG).symm)
  · exact source_speed t ht V hV s u v hu G huG hvG k h hW
  · exact target_speed t ht V hV s u v hv G huG hvG k h hW

end CycleQ2LiteralThreefoldCurveGermEdge
end

#print axioms CycleQ2LiteralThreefoldCurveGermEdge.corrected_on_germ
