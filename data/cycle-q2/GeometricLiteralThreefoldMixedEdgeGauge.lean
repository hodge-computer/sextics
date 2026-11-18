import Proposal.GeometricLiteralThreefoldMixedLiftChange
import Proposal.GeometricThreefoldMixedWedge

/-!
# The evaluated native edge with its source and target vertex corrections

After contraction with a velocity along the actual threefold overlap,
the native edge differs from the adapted edge by the one-forms on
the two original vertices in their own projective coordinates.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldMixedEdgeGauge

open CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldChartLift
  CycleQ2LiteralThreefoldLiftDifference CycleQ2LiteralThreefoldResidueCoordinates
  CycleQ2LiteralThreefoldResidueChartMaps CycleQ2LiteralThreefoldLiftTransition
  CycleQ2LiteralThreefoldTriangleLifts CycleQ2LiteralThreefoldTestEdges
  CycleQ2LiteralThreefoldMixedLiftChange CycleQ2LiteralThreefoldSurfaceNormal
  CycleQ2ThreefoldMixedCurveForm

variable {C : Type} [CommRing C] [Algebra ℂ C]
  (i : Fin 4) (k : Fin 3) [Algebra (FixedOverlap i k) C] [IsScalarTower ℂ (FixedOverlap i k) C]

private abbrev ρ : FixedOverlap i k →ₐ[ℂ] C := IsScalarTower.toAlgHom ℂ _ _

private theorem vertex_cocycle {U : Type} [CommRing U] [Algebra ℂ U] [Algebra U C] [IsScalarTower ℂ U C]
    {j : Fin 4} (f : T j →ₐ[ℂ] U) (x y z : Lift j C) (hx : LiesOver x ((IsScalarTower.toAlgHom ℂ U C).comp f))
    (hy : LiesOver y ((IsScalarTower.toAlgHom ℂ U C).comp f))
    (hz : LiesOver z ((IsScalarTower.toAlgHom ℂ U C).comp f)) (ν : Derivation ℂ U C) :
    vertexMixed f x z hx hz ν = vertexMixed f x y hx hy ν + vertexMixed f y z hy hz ν := by
  let := f.toRingHom.toAlgebra
  let : IsScalarTower ℂ (T j) U := IsScalarTower.of_algHom f
  let := ((IsScalarTower.toAlgHom ℂ U C).comp f).toRingHom.toAlgebra
  let : IsScalarTower ℂ (T j) C := IsScalarTower.of_algHom ((IsScalarTower.toAlgHom ℂ U C).comp f)
  let : IsScalarTower (T j) U C := IsScalarTower.of_algebraMap_eq' rfl
  change mixed (tangent x z hx hz) _ _ = mixed (tangent x y hx hy) _ _ + mixed (tangent y z hy hz) _ _
  rw [tangent_cocycle x y z, CycleQ2ThreefoldMixedWedge.mixed_add_left]

theorem nativeEdge_mixed_change_of_lifts
    (z : Lift i C) (z' w : Lift (i.succAbove k) C) (hn : Normalizes z z')
    (hz : LiesOver z ((ρ i k).comp (sourceMap i k))) (hz' : LiesOver z' ((ρ i k).comp (fixedTargetMap i k)))
    (hw : LiesOver w ((ρ i k).comp (fixedTargetMap i k))) (ν : Derivation ℂ (FixedOverlap i k) C) :
    let a := sourceMap i k
    let b := fixedTargetMap i k
    contractRestrict ν (nativeEdge i k) +
      vertexMixed b (canonical _ ((ρ i k).comp b)) w (canonical_liesOver _ _) hw ν =
      vertexMixed a (canonical i ((ρ i k).comp a)) z (canonical_liesOver _ _) hz ν +
        vertexMixed b z' w hz' hw ν := by
  dsimp only
  rw [nativeEdge_vertexMixed]
  rw [← vertex_cocycle, vertex_cocycle _ _ z' w]
  rw [vertexMixed_normalizes i k (canonical_liesOver _ _) hz (normalizedLift_fst i k (ρ i k)) hz'
    (normalizedLift_normalizes i k (ρ i k)) hn ν]

end CycleQ2LiteralThreefoldMixedEdgeGauge
end

#print axioms CycleQ2LiteralThreefoldMixedEdgeGauge.nativeEdge_mixed_change_of_lifts
