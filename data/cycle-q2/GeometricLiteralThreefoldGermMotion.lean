import Proposal.GeometricLiteralThreefoldVertexMotion
import Proposal.GeometricLiteralAbelJacobiEvaluationVelocity

/-!
# The projective germ velocity in original ambient chart coordinates

On every first-order open inside a projective chart, the actual velocity on
functions restricts on the closed curve to the native ambient motion on a
vertex. This comparison applies to every function of the ambient chart.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralThreefoldGermMotion

open CategoryTheory Opposite AlgebraicGeometry CycleQ2LiteralThreefoldVertexMotion
  CycleQ2LiteralThreefoldCurveTestSections CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralAbelJacobiEvaluationFiber CycleQ2LiteralAbelJacobiEvaluationVelocity
  CycleQ2LiteralAbelJacobiEvaluationAffine CycleQ2FirstOrderCurve CycleQ2FirstOrderCurveCharts
  CycleQ2FirstOrderCurveSeedFiber CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAbelJacobiMovingNormal
  CycleQ2LiteralCylinderEvaluation CycleQ2SeedSectionCurveRows CycleQ2SpecializedCurveCoordinateChart
  CycleQ2GeometricAffineDifferentialSheaf CycleQ2GeometricAffineChartSections

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  familyRing closedRing threefoldRing CycleQ2CurveParameterTangent.chartComplexAlgebra
  familyComplexSMul familyComplexModule familyAlgebra familyComplexTower fixedAlgebra fixedTower
  reductionAlgebra fixedCurveTower familyReductionTower curveComplexOn

private theorem velocity_coordinate {B A : Type} [CommRing B] [CommRing A]
    [Algebra ℂ B] [Algebra ℂ A] [Algebra B A] [IsScalarTower ℂ B A]
    (v : Derivation ℂ B A) (U : (Spec (CommRingCat.of B)).Opens) (b : B) :
    velocityOn v U (algebraMap B (AffineSections B U) b) =
      algebraMap A (AffineSections A (reduction B A ⁻¹ᵁ U)) (v b) := by
  have h := velocityOn_restrict v (homOfLE (show U ≤ ⊤ from le_top)) (algebraMap B (AffineSections B ⊤) b)
  rw [velocityOn_top] at h
  exact h

private theorem coordinate_transport {S : Type} [CommRing S] {U V : (Spec (CommRingCat.of S)).Opens}
    (h : U = V) (a : S) :
    (Spec (CommRingCat.of S)).presheaf.map (eqToHom h.symm).op (algebraMap S (AffineSections S U) a) =
      algebraMap S (AffineSections S V) a := by
  subst V
  simp

variable (t : Fin 3 → ℂ) (p : Vertex) (G : (firstOrderCurve t).Opens)
private abbrev i := p.2.succ
private abbrev W := seedCurveToFirstOrderCurve t ⁻¹ᵁ G
private abbrev j := firstOrderChartToCurve t (i p)

variable (hG : G ≤ firstOrderCurveCoordinateOpen t (i p)) (hW : W t G ≤ vertexOpen t p)

private theorem seed_chart_coordinate (a : A t (i p)) :
    (seedChart t (i p)).app (W t G) (seedSections t p (W t G) hW a) =
      algebraMap (A t (i p)) (AffineSections (A t (i p)) ((seedChart t (i p)) ⁻¹ᵁ W t G)) a := by
  let U := specializedCoordinatePatch seed t (i p)
  let e := specializedCoordinateAffineChart seed t (i p)
  let V : Over U := Over.mk (homOfLE (hW.trans (vertexWithin t p)))
  exact (chartSectionIso e V).inv_hom_id_apply _

private theorem closed_coordinate (a : A t (i p)) :
    closedRestriction t (i p) G hG (seedSections t p (W t G) hW a) =
      algebraMap (A t (i p)) (AffineSections (A t (i p)) (reduction (B t (i p)) (A t (i p)) ⁻¹ᵁ
        (j t p) ⁻¹ᵁ G)) a := by
  let he := chartPreimage t (i p) G
  change (Spec (CommRingCat.of (A t (i p)))).presheaf.map (eqToHom he.symm).op
    ((seedChart t (i p)).app (W t G) (seedSections t p (W t G) hW a)) = _
  rw [seed_chart_coordinate t p G hW a]
  exact coordinate_transport he a

/-- A germ function representing an original ambient function has precisely
the derivative given by the native moving curve normal on the vertex. -/
theorem onOpen_eq_ambient (v : Derivation ℂ (B t (i p)) (A t (i p))) (r : T (i p)) (x : GermRing t G)
    (hx : (j t p).app G x = algebraMap (B t (i p)) (AffineSections (B t (i p)) ((j t p) ⁻¹ᵁ G))
      (toFamily t (i p) r)) :
    onOpen t (i p) v G hG x = ambientMotion t p (W t G) hW v r := by
  apply (closedRestriction t (i p) G hG).injective
  rw [closedRestriction_onOpen, hx, velocity_coordinate, ambientMotion_apply, closed_coordinate]

/-- The canonical germ section of the original affine coordinate without any
choice of representative. -/
def germCoordinate (r : T (i p)) : GermRing t G := by
  letI := (j t p).isIso_app G hG
  exact (asIso ((j t p).app G)).inv
    (algebraMap (B t (i p)) (AffineSections (B t (i p)) ((j t p) ⁻¹ᵁ G)) (toFamily t (i p) r))

theorem germCoordinate_app (r : T (i p)) :
    (j t p).app G (germCoordinate t p G hG r) = algebraMap (B t (i p))
      (AffineSections (B t (i p)) ((j t p) ⁻¹ᵁ G)) (toFamily t (i p) r) := by
  let := (j t p).isIso_app G hG
  exact (asIso ((j t p).app G)).inv_hom_id_apply _

theorem coordinate_velocity (v : Derivation ℂ (B t (i p)) (A t (i p))) (r : T (i p)) :
    onOpen t (i p) v G hG (germCoordinate t p G hG r) = ambientMotion t p (W t G) hW v r :=
  onOpen_eq_ambient t p G hG hW v r _ (germCoordinate_app t p G hG r)

end CycleQ2LiteralThreefoldGermMotion
end

#print axioms CycleQ2LiteralThreefoldGermMotion.onOpen_eq_ambient
#print axioms CycleQ2LiteralThreefoldGermMotion.coordinate_velocity
