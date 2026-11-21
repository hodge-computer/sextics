import Proposal.GeometricLiteralThreefoldCurveTestSections
import Proposal.GeometricFullSurfaceResidueCover
import Proposal.GeometricSeedProjectiveImageChart

/-!
# The Jacobian affine refinement over each native curve vertex

The sixteen explicit coordinate Jacobians cover each original surface
chart. After pullback to the moving curve, every point below a native
vertex therefore admits an affine neighborhood inside one of the
Jacobians for that same weight-one chart.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldCurveJacobianCover

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
  CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSurfaceDehomogenizedCharts
  CycleQ2GeometricSurfaceJacobianCharts CycleQ2CartierProjectiveCover
  CycleQ2GeometricPrincipalChartSections CycleQ2GeometricSurfaceNormalCover
  CycleQ2FullSurfaceJacobianCover CycleQ2LiteralNativeDifferentialSections
  CycleQ2LiteralNativeGaugeSections CycleQ2ProjectiveCartierIdeal
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralThreefoldCurveTestSections
  CycleQ2LiteralMovingResidueAdjunction.AffineFrame CycleQ2SeedSectionSheafCurveBinding

def jacobianOpen (i : Fin 3) (a b : Fin 4) : Surface.Opens :=
  principalOpen (coordinateAffineChart 57 1 i.succ) (augmentedJacobian (equations i)
    (X (variableIndex a)) (X (variableIndex b)))

theorem jacobianOpen_cover (i : Fin 3) :
    (⨆ a, ⨆ b, jacobianOpen i a b) = coordinatePatch 57 1 i.succ.castSucc := by
  apply principalOpen_cover_two (coordinateAffineChart 57 1 i.succ)
  have htop : Ideal.span (Set.range (fun ab : Fin 4 × Fin 4 => augmentedJacobian (equations i)
    (X (variableIndex ab.1)) (X (variableIndex ab.2)))) = ⊤ := augmentedCoordinateIdeal_eq_top i
  have h := PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr htop
  simpa only [iSup_prod] using h

theorem vertex_le_coordinate (v : Vertex) : cover v ≤ coordinatePatch 57 1 v.2.succ.castSucc := by
  rw [cover, refinedOpen_eq]
  apply inf_le_right.trans
  exact (congrArg (fun j : Fin 5 => Proj.basicOpen (CycleQ2CartierSurfaceGrading.surfaceGrade 57 1)
    (CycleQ2GeometricCartierNormalLift.surfaceQuotient 57 1 (X j)))
    (CycleQ2SeedProjectiveImageChart.remainingIndex_eq v.2)).le

/-- A curve subopen contained in a prescribed surface open is its exact
inverse image from a subopen of that same surface chart. -/
theorem exists_surface_refinement (t : Fin 3 → ℂ) (O : Surface.Opens) (W : (Curve t).Opens)
    (h : W ≤ (curveToSurface t) ⁻¹ᵁ O) : ∃ V ≤ O, (curveToSurface t) ⁻¹ᵁ V = W := by
  obtain ⟨U,hU,e⟩ := (curveToSurface t).isClosedEmbedding.isEmbedding.isInducing.isOpen_iff.mp W.isOpen
  let V : Surface.Opens := ⟨U,hU⟩
  have hV : (curveToSurface t) ⁻¹ᵁ V = W := Opens.ext e
  refine ⟨O ⊓ V,inf_le_left,?_⟩
  rw [Scheme.Hom.preimage_inf, hV, inf_eq_right.mpr h]

theorem affine_jacobian_neighborhood (t : Fin 3 → ℂ) (v : Vertex)
    (W : (Curve t).Opens) (hW : W ≤ vertexOpen t v) (p : Curve t) (hp : p ∈ W) :
    ∃ (a b : Fin 4) (U : (Curve t).Opens), IsAffineOpen U ∧ p ∈ U ∧ U ≤ W ∧
      U ≤ (curveToSurface t) ⁻¹ᵁ jacobianOpen v.2 a b := by
  have hx : (curveToSurface t) p ∈ coordinatePatch 57 1 v.2.succ.castSucc := vertex_le_coordinate v (hW hp)
  rw [← jacobianOpen_cover] at hx
  obtain ⟨a,ha⟩ := Opens.mem_iSup.mp hx
  obtain ⟨b,hb⟩ := Opens.mem_iSup.mp ha
  let V := W ⊓ (curveToSurface t) ⁻¹ᵁ jacobianOpen v.2 a b
  have hpV : p ∈ V := ⟨hp,hb⟩
  obtain ⟨U,hU,hpU,hUV⟩ := Opens.isBasis_iff_nbhd.mp (Curve t).isBasis_affineOpens hpV
  exact ⟨a,b,U,hU,hpU,hUV.trans inf_le_left,hUV.trans inf_le_right⟩

end CycleQ2LiteralThreefoldCurveJacobianCover
end

#print axioms CycleQ2LiteralThreefoldCurveJacobianCover.affine_jacobian_neighborhood
