import Proposal.GeometricLiteralThreefoldCurveVertexCochain
import Proposal.GeometricThreefoldMixedWedge

/-!
# The corrected surface edge against the actual velocity on the curve

The adapted test vector on the central curve is the native surface
Kodaira–Spencer derivation on every function of the fixed threefold.
Vertices in the same weight chart satisfy the correction formula directly.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralThreefoldCurveAdaptedValue

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
  CycleQ2LiteralThreefoldCurveVertexCochain CycleQ2LiteralThreefoldCurveVertexLifts
  CycleQ2LiteralThreefoldCurveTestSections CycleQ2LiteralThreefoldVertexMotion
  CycleQ2LiteralThreefoldVertexPointBinding CycleQ2LiteralThreefoldSurfaceTestLifts
  CycleQ2LiteralThreefoldMixedRestriction CycleQ2LiteralThreefoldChartLift
  CycleQ2LiteralThreefoldLiftDifference CycleQ2LiteralThreefoldLiftTransition
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAbelJacobiEvaluationChart
  CycleQ2LiteralMovingResidueAdjunction.AffineFrame CycleQ2SeedSectionSheafCurveBinding
  CycleQ2LiteralNativeGaugeSections CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralCylinderEvaluation
  CycleQ2LiteralNativeKodairaSpencer CycleQ2LiteralProjectiveIntersectionComplex
  CycleQ2ThreefoldMixedCurveForm

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  familyRing closedRing threefoldRing CycleQ2CurveParameterTangent.chartComplexAlgebra
  familyAlgebra familyComplexTower fixedAlgebra fixedTower reductionAlgebra fixedCurveTower familyReductionTower
  curveComplexOn closedComplexAlgebra

variable (t : Fin 3 → ℂ) (ht : AlgebraicIndependent ℚ t) (s : Finset Vertex)
  (u v : Vertex) (hu : u ∈ s) (hv : v ∈ s) (W : (Curve t).Opens)
  (hW : W ≤ (curveToSurface t) ⁻¹ᵁ closedOpen s)

private abbrev p := ambientPoint t v W (withinVertex t s v hv W hW)
private abbrev uv := curveLift t s v hv W hW u.1 ⟨u.2,hu⟩
private theorem lift_liesOver : LiesOver (uv t s u v hu hv W hW) (p t s v hv W hW) := by
  rw [p, ← ambientPoint_eq_native t s ⟨v,hv⟩ v hv W hW]
  exact curveLift_over t s v hv W hW u.1 ⟨u.2,hu⟩

def ksVector :
    let f := p t s v hv W hW
    letI := f.toRingHom.toAlgebra
    Derivation ℂ (T (chartIndex v)) (CurveRingOn t W) := by
  let f := p t s v hv W hW
  letI := f.toRingHom.toAlgebra
  letI := IsScalarTower.of_algHom f
  exact tangent (uv t s u v hu hv W hW) (uv t s v v hv hv W hW)
    (lift_liesOver t s u v hu hv W hW) (lift_liesOver t s v v hv hv W hW)

theorem ksVector_apply (r : T (chartIndex v)) :
    ksVector t s u v hu hv W hW r = nativeToCurve t s ⟨v,hv⟩ W hW
      (kodairaSpencer s u.1 v.1 ⟨u.2,hu⟩ ⟨v.2,hv⟩ (fixedPoint s v hv r)) :=
  tangent_map_surfaceLift s v hv u.1 v.1 ⟨u.2,hu⟩ ⟨v.2,hv⟩ (nativeToCurve t s ⟨v,hv⟩ W hW) r

def adapted : KaehlerDifferential ℂ (CurveRingOn t W) :=
  vertexForm (p t s v hv W hW) (uv t s u v hu hv W hW) (uv t s v v hv hv W hW)
    (lift_liesOver t s u v hu hv W hW) (lift_liesOver t s v v hv hv W hW)
    (ambientMotion t v W (withinVertex t s v hv W hW) (normalizedVelocity t (chartIndex v) ht))

private theorem vertex_cocycle {C : Type} [CommRing C] [Algebra ℂ C] {i : Fin 4} (f : T i →ₐ[ℂ] C)
    (x y z : Lift i C) (hx : LiesOver x f) (hy : LiesOver y f) (hz : LiesOver z f) :
    letI := f.toRingHom.toAlgebra
    letI := IsScalarTower.of_algHom f
    ∀ ν : Derivation ℂ (T i) C,
      vertexForm f x z hx hz ν = vertexForm f x y hx hy ν + vertexForm f y z hy hz ν := by
  let := f.toRingHom.toAlgebra
  let := IsScalarTower.of_algHom f
  intro ν
  unfold vertexForm
  rw [tangent_cocycle x y z hx hy hz, CycleQ2ThreefoldMixedWedge.mixed_add_left]

private theorem vertex_congr {C : Type} [CommRing C] [Algebra ℂ C] {i : Fin 4}
    (f : T i →ₐ[ℂ] C) (x y z : Lift i C)
    (hx : LiesOver x f) (hy : LiesOver y f) (hz : LiesOver z f) (e : x = y) :
    letI := f.toRingHom.toAlgebra
    letI := IsScalarTower.of_algHom f
    ∀ ν : Derivation ℂ (T i) C, vertexForm f x z hx hz ν = vertexForm f y z hy hz ν := by
  subst y
  intro ν
  rfl

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
theorem same_chart (h : chartIndex u = chartIndex v) :
    rawVertex t ht s v hv W hW = rawVertex t ht s u hu W hW + adapted t ht s u v hu hv W hW := by
  rcases u with ⟨a,i⟩
  rcases v with ⟨b,j⟩
  have e : i = j := Fin.succ_injective _ h
  subst j
  let x := uv t s (a,i) (a,i) hu hu W hW
  let y := uv t s (a,i) (b,i) hu hv W hW
  have e : x = y := same_chart_lift (curveLift_normalizes t s (b,i) hv W hW (a,i) hu a ⟨i,hu⟩)
  have hy : LiesOver x (p t s (b,i) hv W hW) := by
    rw [e]
    exact lift_liesOver t s (a,i) (b,i) hu hv W hW
  have comp := vertex_cocycle (p t s (b,i) hv W hW) (canonical _ _) x
    (uv t s (b,i) (b,i) hv hv W hW) (canonical_liesOver _ _) hy (lift_liesOver t s (b,i) (b,i) hv hv W hW)
    (ambientMotion t (b,i) W (withinVertex t s (b,i) hv W hW) (normalizedVelocity t i.succ ht))
  apply comp.trans
  refine congrArg₂ (· + ·) ?_ ?_
  · rfl
  · exact vertex_congr (p t s (b,i) hv W hW) x y _
      hy (lift_liesOver t s (a,i) (b,i) hu hv W hW)
      (lift_liesOver t s (b,i) (b,i) hv hv W hW) e
      (ambientMotion t (b,i) W (withinVertex t s (b,i) hv W hW) (normalizedVelocity t i.succ ht))

end CycleQ2LiteralThreefoldCurveAdaptedValue
end

#print axioms CycleQ2LiteralThreefoldCurveAdaptedValue.ksVector_apply
#print axioms CycleQ2LiteralThreefoldCurveAdaptedValue.same_chart
