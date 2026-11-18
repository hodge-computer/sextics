import Proposal.GeometricLiteralThreefoldVertexMotion
import Proposal.GeometricLiteralAbelJacobiQChart
import Proposal.GeometricLiteralThreefoldSeedProjection
import Proposal.GeometricLiteralThreefoldHodgeCech

/-!
# The vertex motion lies at the actual projected curve point

The seed-chart position used for the motion on an arbitrary curve subopen
agrees on each function with the pullback by the cylinder projection.
This identifies both scalar actions before forming ambient derivations.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

noncomputable section
namespace CycleQ2LiteralThreefoldVertexPoint

open CategoryTheory Opposite AlgebraicGeometry CycleQ2LiteralAbelJacobiEvaluationFiber
  CycleQ2LiteralAbelJacobiTimeCharts CycleQ2LiteralAbelJacobiQPullback
  CycleQ2LiteralAbelJacobiQChart CycleQ2LiteralAbelJacobiTimeFamily CycleQ2LiteralThreefoldVertexMotion
  CycleQ2LiteralThreefoldSeedProjection CycleQ2LiteralThreefoldHodgeCech CycleQ2LiteralAmbientCharts
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceSeedFiberCover CycleQ2SeedSectionCurveRows
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAbelJacobiMovingNormal
  CycleQ2LiteralMovingResidueAdjunction.AffineFrame CycleQ2LiteralThreefoldCurveTestSections
  CycleQ2GeometricAffineChartSections CycleQ2ChartSectionPullback CycleQ2SeedSectionSheafCurveBinding
  CycleQ2LiteralProjectiveIntersections CycleQ2SpecializedCurveCoordinateChart CycleQ2LiteralAmbientSurface

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2LiteralCylinderEvaluation.closedRing CycleQ2LiteralCylinderEvaluation.threefoldRing
  fixedAlgebra fixedTower curveComplexOn

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ) (hV : seedBasePoint ∈ V)

private abbrev proj := seedToTime t V hV ≫ toThreefold V t

theorem seed_chart_square (i : Fin 4) : seedChart t i ≫ proj V t hV =
    Spec.map (CommRingCat.ofHom (toCurve t i).toRingHom) ≫ chartInclusion i := by
  simpa only [seedChart, proj, seedToTime, closedChart, toThreefold, Category.assoc] using
    closedChart_toSmoothThreefold V t hV i

theorem seed_chart_within (i : Fin 4) : specializedCoordinatePatch seed t i ≤ proj V t hV ⁻¹ᵁ fixedOpen i := by
  rw [← seedChart_opensRange t i]
  intro x hx
  obtain ⟨z,rfl⟩ := hx
  change (seedChart t i ≫ proj V t hV) z ∈ fixedOpen i
  rw [seed_chart_square]
  exact ((fixedChart i).hom (Spec.map (CommRingCat.ofHom (toCurve t i).toRingHom) z)).property

/-- The values of the original ambient functions on every native curve subopen
are the functions pulled back along the actual cylinder projection. -/
theorem ambientPoint_on_subopen (p : Vertex) (U : Threefold.Opens) (hU : U ≤ fixedOpen p.2.succ)
    (W : (Curve t).Opens) (hW : W ≤ vertexOpen t p) (hWU : W ≤ proj V t hV ⁻¹ᵁ U) (r : T p.2.succ) :
    ambientPoint t p W hW r = (proj V t hV).appLE U W hWU (chartAlgebraMap p.2.succ U hU r) := by
  exact (chartSection_pullback (proj V t hV) (fixedChart p.2.succ).symm
    (specializedCoordinateAffineChart seed t p.2.succ) (toCurve t p.2.succ).toRingHom
    (seed_chart_within V t hV _) (by
      simpa only [seedChart, chartInclusion, Iso.symm_inv, Category.assoc] using (seed_chart_square V t hV p.2.succ))
    U hU W (hW.trans (vertexWithin t p)) hWU r).symm

end CycleQ2LiteralThreefoldVertexPoint
end

#print axioms CycleQ2LiteralThreefoldVertexPoint.seed_chart_square
#print axioms CycleQ2LiteralThreefoldVertexPoint.ambientPoint_on_subopen
