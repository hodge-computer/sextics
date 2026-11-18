import Proposal.GeometricLiteralThreefoldCurveJacobianCover
import Proposal.GeometricLiteralThreefoldVertexMotion
import Proposal.GeometricAffineCechGauge

/-!
# A common affine refinement of the true first-order family and surface

Every point of a native curve pair admits a neighborhood coming from
one affine of the first-order curve, contained in both original moving
charts. Its central fiber lies in one of the actual surface Jacobian
opens of the second vertex. Both speed comparison and the cubic
contraction can be tested on these same neighborhoods.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralThreefoldCurveGermCover

open AlgebraicGeometry CategoryTheory TopologicalSpace CycleQ2GeometricSheafLocalIso
  CycleQ2InjectiveCech CycleQ2FiniteInjectiveCech CycleQ2FiniteCechDescent CycleQ2LiteralAbelJacobiEvaluationFiber
  CycleQ2FirstOrderCurve CycleQ2FirstOrderCurveCharts CycleQ2FirstOrderCurveSeedFiber
  CycleQ2LiteralThreefoldCurveJacobianCover CycleQ2LiteralThreefoldCurveTestSections
  CycleQ2LiteralThreefoldVertexMotion
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralMovingResidueAdjunction.AffineFrame
  CycleQ2SeedSectionSheafCurveBinding

variable (t : Fin 3 → ℂ)

private def germOpen (W : (Curve t).Opens) : (firstOrderCurve t).Opens :=
  ⟨(seedCurveToFirstOrderCurve t) '' (W : Set (Curve t)), (seed_germ_homeomorph t).isOpenMap _ W.isOpen⟩

private theorem germOpen_pre (W : (Curve t).Opens) :
    seedCurveToFirstOrderCurve t ⁻¹ᵁ germOpen t W = W :=
  TopologicalSpace.Opens.ext (Set.preimage_image_eq _ (seed_germ_homeomorph t).bijective.injective)

private theorem vertex_in_germChart (v : Vertex) : vertexOpen t v ≤
    seedCurveToFirstOrderCurve t ⁻¹ᵁ firstOrderCurveCoordinateOpen t v.2.succ := by
  rw [germ_preimage_coordinate]
  exact vertexWithin t v

theorem common_affine_neighborhood (u v : Vertex) (W : (Curve t).Opens)
    (hu : W ≤ vertexOpen t u) (hv : W ≤ vertexOpen t v) (x : Curve t) (hx : x ∈ W) :
    ∃ (a b : Fin 4) (G : (firstOrderCurve t).Opens), IsAffineOpen G ∧
      G ≤ firstOrderCurveCoordinateOpen t u.2.succ ∧ G ≤ firstOrderCurveCoordinateOpen t v.2.succ ∧
      x ∈ seedCurveToFirstOrderCurve t ⁻¹ᵁ G ∧ seedCurveToFirstOrderCurve t ⁻¹ᵁ G ≤ W ∧
      seedCurveToFirstOrderCurve t ⁻¹ᵁ G ≤ (curveToSurface t) ⁻¹ᵁ jacobianOpen v.2 a b := by
  obtain ⟨a,b,Z,_,hxZ,hZW,hZJ⟩ := affine_jacobian_neighborhood t v W hv x hx
  let i := seedCurveToFirstOrderCurve t
  let O := (germOpen t Z ⊓ firstOrderCurveCoordinateOpen t u.2.succ) ⊓ firstOrderCurveCoordinateOpen t v.2.succ
  have hxO : i x ∈ O := ⟨⟨⟨x,hxZ,rfl⟩,vertex_in_germChart t u (hu hx)⟩,vertex_in_germChart t v (hv hx)⟩
  obtain ⟨G,hG,hxG,hGO⟩ := Opens.isBasis_iff_nbhd.mp (firstOrderCurve t).isBasis_affineOpens hxO
  have hGZ : i ⁻¹ᵁ G ≤ Z := by
    rw [← germOpen_pre t Z]
    exact i.preimage_mono (hGO.trans (inf_le_left.trans inf_le_left))
  exact ⟨a,b,G,hG,hGO.trans (inf_le_left.trans inf_le_right),hGO.trans inf_le_right,hxG,
    hGZ.trans hZW,hGZ.trans hZJ⟩

/-- A signed vertex correction can be checked in affine first-order
coordinates for the two vertices and in the simultaneous surface Jacobian
coordinates before taking its global curve class. -/
theorem signed_edges_on_germ (F : AbSheaf (Curve t)) (c b : One F (vertexOpen t))
    (p : Zero F (vertexOpen t)) (u v : Vertex)
    (h : ∀ (m n : Fin 4) (G : (firstOrderCurve t).Opens), IsAffineOpen G →
      G ≤ firstOrderCurveCoordinateOpen t u.2.succ → G ≤ firstOrderCurveCoordinateOpen t v.2.succ →
      ∀ (hu : seedCurveToFirstOrderCurve t ⁻¹ᵁ G ≤ vertexOpen t u)
        (hv : seedCurveToFirstOrderCurve t ⁻¹ᵁ G ≤ vertexOpen t v),
        seedCurveToFirstOrderCurve t ⁻¹ᵁ G ≤ (curveToSurface t) ⁻¹ᵁ jacobianOpen v.2 m n →
        edgeValue F (vertexOpen t) c u v _ hu hv + res F hv (p v) =
          res F hu (p u) - edgeValue F (vertexOpen t) b u v _ hu hv)
    (W : (Curve t).Opens) (hu : W ≤ vertexOpen t u) (hv : W ≤ vertexOpen t v) :
    edgeValue F (vertexOpen t) c u v W hu hv + res F hv (p v) =
      res F hu (p u) - edgeValue F (vertexOpen t) b u v W hu hv := by
  apply TopCat.Presheaf.IsSheaf.section_ext F.property
  intro x hx
  obtain ⟨m,n,G,hG,hGu,hGv,hxG,hGW,hGJ⟩ := common_affine_neighborhood t u v W hu hv x hx
  refine ⟨_, hGW, hxG, ?_⟩
  change res F hGW (_ + _) = res F hGW (_ - _)
  rw [map_add, map_sub]
  unfold edgeValue
  simp only [res_comp]
  exact h m n G hG hGu hGv (hGW.trans hu) (hGW.trans hv) hGJ

end CycleQ2LiteralThreefoldCurveGermCover
end

#print axioms CycleQ2LiteralThreefoldCurveGermCover.common_affine_neighborhood
