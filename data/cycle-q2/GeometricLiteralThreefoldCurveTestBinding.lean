import Proposal.GeometricLiteralThreefoldCurveTestSections
import Proposal.GeometricLiteralThreefoldSurfaceChartMap
import Proposal.GeometricLiteralThreefoldSurfaceTestTransport
import Proposal.GeometricLiteralThreefoldSeedProjection

/-!
# The native test coordinates on the actual central curve

The normalized surface functions on a common open of the original section
curve equal pullbacks of the affine coordinates of the fixed threefold by
the central fibre of the cylinder projection. This applies to the full
threefold overlap ring, including its inverted coordinate.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

noncomputable section
namespace CycleQ2LiteralThreefoldCurveTestBinding

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial
  CycleQ2LiteralThreefoldCurveTestSections CycleQ2LiteralThreefoldSurfaceChartMap
  CycleQ2LiteralThreefoldSurfaceTestLifts CycleQ2LiteralThreefoldSeedProjection
  CycleQ2LiteralAmbientSurface CycleQ2LiteralAbelJacobiEvaluationFiber
  CycleQ2LiteralAbelJacobiQPullback CycleQ2LiteralThreefoldHodgeCech
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldResidueCoordinates
  CycleQ2LiteralThreefoldResidueChartMaps CycleQ2LiteralThreefoldChartLift CycleQ2LiteralThreefoldLiftTransition
  CycleQ2LiteralAmbientCharts CycleQ2LiteralMovingResidueAdjunction.AffineFrame
  CycleQ2LiteralNativeDifferentialSections CycleQ2SeedSectionSheafCurveBinding
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionComplex
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceSeedFiberCover
  CycleQ2GeometricAffineChartSections

attribute [local instance] closedComplexAlgebra sourceFixedAlgebra sourceFixedTower sourceFixedLocalization
  CycleQ2LiteralThreefoldCurveTestSections.curveComplexOn CycleQ2LiteralThreefoldHodgeCech.complexOn

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ) (hV : seedBasePoint ∈ V)

abbrev seedProjection := seedToTime t V hV ≫ toThreefold V t

private theorem appLE_of_eq {X Y : Scheme.{0}} {f g : X ⟶ Y} (e : f = g)
    (U : Y.Opens) (W : X.Opens) (hf : W ≤ f ⁻¹ᵁ U) (hg : W ≤ g ⁻¹ᵁ U) :
    f.appLE U W hf = g.appLE U W hg := by
  subst g
  rfl

private theorem within_of_eq {X Y : Scheme.{0}} {f g : X ⟶ Y} (e : f = g)
    (U : Y.Opens) (W : X.Opens) (h : W ≤ f ⁻¹ᵁ U) : W ≤ g ⁻¹ᵁ U := by
  subst g
  exact h

theorem native_within (s : Finset Vertex) (hs : s.Nonempty) (v : Vertex) (hv : v ∈ s)
    (W : (Curve t).Opens) (hW : W ≤ (curveToSurface t) ⁻¹ᵁ closedOpen s) :
    W ≤ seedProjection V t hV ⁻¹ᵁ fixedOpen (chartIndex v) := by
  apply within_of_eq (seed_projection V t hV).symm (fixedOpen (chartIndex v)) W
  exact hW.trans ((Opens.map (curveToSurface t).base).map (homOfLE (closedOpen_le_fixedOpen s hs v hv))).le

#print axioms native_within

/-- Every polynomial or regular function in the fixed threefold chart is
evaluated by the actual cylinder projection on the central curve. -/
theorem fixedPoint_curve (s : Finset Vertex) (hs : s.Nonempty) (v : Vertex) (hv : v ∈ s)
    (W : (Curve t).Opens) (hW : W ≤ (curveToSurface t) ⁻¹ᵁ closedOpen s) (z : T (chartIndex v)) :
    nativeToCurve t s hs W hW (fixedPoint s v hv z) = (seedProjection V t hV).appLE
      (fixedOpen (chartIndex v)) W (native_within V t hV s hs v hv W hW)
      (chartAlgebraMap (chartIndex v) (fixedOpen (chartIndex v)) le_rfl z) := by
  let U := fixedOpen (chartIndex v)
  let hf : W ≤ (curveToSurface t ≫ surfaceToFiber) ⁻¹ᵁ U :=
    hW.trans ((Opens.map (curveToSurface t).base).map (homOfLE (closedOpen_le_fixedOpen s hs v hv))).le
  have e := appLE_of_eq (seed_projection V t hV).symm U W hf (native_within V t hV s hs v hv W hW)
  let y := chartAlgebraMap (chartIndex v) U le_rfl z
  have hy : nativeToCurve t s hs W hW (fixedPoint s v hv z) =
      (curveToSurface t ≫ surfaceToFiber).appLE U W hf y :=
    nativeToCurve_chart surfaceToFiber U (fixedChart (chartIndex v)).symm t s hs
      (fixedPoint s v hv).toRingHom (closedOpen_le_fixedOpen s hs v hv) (fixedPoint_over_threefold s hs v hv) W hW z
  exact hy.trans (ConcreteCategory.congr_hom e y)

#print axioms fixedPoint_curve

theorem fixedPoint_curve_subopen (s : Finset Vertex) (hs : s.Nonempty) (v : Vertex) (hv : v ∈ s)
    (U : Threefold.Opens) (hU : U ≤ fixedOpen (chartIndex v)) (W : (Curve t).Opens)
    (hW : W ≤ (curveToSurface t) ⁻¹ᵁ closedOpen s) (hWU : W ≤ seedProjection V t hV ⁻¹ᵁ U)
    (z : T (chartIndex v)) :
    nativeToCurve t s hs W hW (fixedPoint s v hv z) =
      (seedProjection V t hV).appLE U W hWU (chartAlgebraMap (chartIndex v) U hU z) := by
  have hr := chartSection_naturality (fixedChart (chartIndex v)).symm
    (Over.homMk (homOfLE hU) : Over.mk (homOfLE hU) ⟶ Over.mk (𝟙 (fixedOpen (chartIndex v)))) z
  have hn := ConcreteCategory.congr_hom ((seedProjection V t hV).map_appLE hWU (homOfLE hU).op)
    (chartAlgebraMap (chartIndex v) (fixedOpen (chartIndex v)) le_rfl z)
  exact (fixedPoint_curve V t hV s hs v hv W hW z).trans (hn.symm.trans
    (congrArg ((seedProjection V t hV).appLE U W hWU) hr))

/-- The source and target charts give the same pullback on every function in
the native threefold overlap ring. -/
theorem overlapPoint_curve (s : Finset Vertex) (hs : s.Nonempty) (v w : Vertex)
    (hv : v ∈ s) (hw : w ∈ s) (k : Fin 3) (h : (chartIndex v).succAbove k = chartIndex w)
    (U : Threefold.Opens) (hU : U ≤ fixedOpen (chartIndex v) ⊓ fixedOpen ((chartIndex v).succAbove k))
    (W : (Curve t).Opens) (hW : W ≤ (curveToSurface t) ⁻¹ᵁ closedOpen s)
    (hWU : W ≤ seedProjection V t hV ⁻¹ᵁ U) (x : FixedOverlap (chartIndex v) k) :
    nativeToCurve t s hs W hW (fixedOverlapPoint s v w hv hw k h x) =
      (seedProjection V t hV).appLE U W hWU (overlapAlgebraMap (chartIndex v) k U hU x) := by
  let f := (nativeToCurve t s hs W hW).comp (fixedOverlapPoint s v w hv hw k h)
  let g := ((seedProjection V t hV).appLE U W hWU).hom.comp (overlapAlgebraMap (chartIndex v) k U hU).toRingHom
  have e : f.toRingHom = g := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (q (chartIndex v) (X (some k))))
    apply RingHom.ext
    intro z
    change nativeToCurve t s hs W hW (((fixedOverlapPoint s v w hv hw k h).comp (sourceMap (chartIndex v) k)) z) =
      (seedProjection V t hV).appLE U W hWU (((overlapAlgebraMap (chartIndex v) k U hU).comp (sourceMap (chartIndex v) k)) z)
    rw [fixedOverlapPoint_source, overlapAlgebraMap_source]
    exact fixedPoint_curve_subopen V t hV s hs v hv U (hU.trans inf_le_left) W hW hWU z
  exact RingHom.congr_fun e x

end CycleQ2LiteralThreefoldCurveTestBinding
end

#print axioms CycleQ2LiteralThreefoldCurveTestBinding.overlapPoint_curve
