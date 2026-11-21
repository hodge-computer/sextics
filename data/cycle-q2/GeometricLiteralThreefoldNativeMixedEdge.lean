import Proposal.GeometricLiteralThreefoldTestGauge
import Proposal.GeometricThreefoldMixedCurveForm
import Proposal.GeometricLiteralThreefoldSurfaceNormal

/-!
# The ambient test edge evaluated along a moving curve

The two-form defined by the difference of the original chart lifts can
be contracted on the overlap before any restriction to the closed surface.
The result equals the mixed evaluation of the oriented threefold volume
on the edge vector and the original curve vector.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

noncomputable section
namespace CycleQ2LiteralThreefoldNativeMixedEdge

open CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldChartLift
  CycleQ2LiteralThreefoldLiftDifference CycleQ2LiteralThreefoldTangentCoordinates
  CycleQ2LiteralThreefoldChartEvaluation CycleQ2LiteralThreefoldResidueChartMaps
  CycleQ2LiteralThreefoldResidueCoordinates CycleQ2LiteralThreefoldLiftTransition
  CycleQ2LiteralThreefoldTestEdges CycleQ2LiteralThreefoldTestGauge CycleQ2ThreefoldContractionAlongMap
  CycleQ2ThreefoldMixedCurveForm CycleQ2LiteralThreefoldSurfaceNormal

variable {U C : Type} [CommRing U] [CommRing C] [Algebra ℂ U] [Algebra ℂ C]

private theorem jetValue_eq_along {i : Fin 4} (v : T i →ₐ[ℂ] Jet U) (f : T i →ₐ[ℂ] U)
    (h : ∀ r, (v r).fst = f r) :
    jetValue i v = along 2 f (CycleQ2TangentPointDifferential.covector f v h) (orientedVolume i) := by
  have hf : (TrivSqZeroExt.fstHom ℂ U U).comp v = f := AlgHom.ext h
  subst f
  rfl

theorem value_as_along {i : Fin 4} (f : T i →ₐ[ℂ] U) (x y : Lift i U)
    (hx : LiesOver x f) (hy : LiesOver y f) :
    value x y (fun a => (hx a).trans (hy a).symm) =
      along 2 f (liftCovector f x y hx hy) (orientedVolume i) := by
  unfold value liftCovector
  exact jetValue_eq_along _ _ _

variable [Algebra U C] [IsScalarTower ℂ U C] [Module.Projective C (KaehlerDifferential ℂ C)]

section Value
variable {i : Fin 4} [Algebra (T i) U] [Algebra (T i) C] [IsScalarTower ℂ (T i) U]
  [IsScalarTower ℂ (T i) C] [IsScalarTower (T i) U C]

/-- On any ambient chart overlap the original two-form retains the transverse
argument. Both vectors on the right are along the map to the curve. -/
theorem value_mixed (x y : Lift i U)
    (hx : LiesOver x (IsScalarTower.toAlgHom ℂ (T i) U)) (hy : LiesOver y (IsScalarTower.toAlgHom ℂ (T i) U))
    (v : Derivation ℂ U C) :
    contractRestrict v (value x y (fun a => (hx a).trans (hy a).symm)) =
      mixed (covectorAlong (liftCovector (IsScalarTower.toAlgHom ℂ (T i) U) x y hx hy)) (v.compAlgebraMap (T i))
        (orientedVolume i) := by
  rw [value_as_along _ x y hx hy, two_step_covector]

end Value

/-- The actual edge, including arbitrary further pullback of its two-form to
another overlap ring before contraction on the curve. -/
theorem edgeAt_mixed (i : Fin 4) (k : Fin 3) (g : FixedOverlap i k →ₐ[ℂ] U)
    (v : Derivation ℂ U C) :
    let m := i.succAbove k
    let f := g.comp (fixedTargetMap i k)
    letI := f.toRingHom.toAlgebra
    letI : IsScalarTower ℂ (T m) U := IsScalarTower.of_algHom f
    letI := ((IsScalarTower.toAlgHom ℂ U C).comp f).toRingHom.toAlgebra
    letI : IsScalarTower ℂ (T m) C := IsScalarTower.of_algHom ((IsScalarTower.toAlgHom ℂ U C).comp f)
    letI : IsScalarTower (T m) U C := IsScalarTower.of_algebraMap_eq' rfl
    let x := normalizedLift i k g
    let y := canonical m f
    let hx : LiesOver x f := normalizedLift_fst i k g
    let hy : LiesOver y f := canonical_liesOver _ _
    contractRestrict v (edgeAt i k g) =
      mixed (covectorAlong (liftCovector f x y hx hy)) (v.compAlgebraMap (T m)) (orientedVolume m) := by
  dsimp only
  let f := g.comp (fixedTargetMap i k)
  let := f.toRingHom.toAlgebra
  let : IsScalarTower ℂ (T (i.succAbove k)) U := IsScalarTower.of_algHom f
  let := ((IsScalarTower.toAlgHom ℂ U C).comp f).toRingHom.toAlgebra
  let : IsScalarTower ℂ (T (i.succAbove k)) C := IsScalarTower.of_algHom ((IsScalarTower.toAlgHom ℂ U C).comp f)
  let : IsScalarTower (T (i.succAbove k)) U C := IsScalarTower.of_algebraMap_eq' rfl
  exact value_mixed (normalizedLift i k g) (canonical _ f) (normalizedLift_fst i k g) (canonical_liesOver _ _) v

/-- Restrict the native ambient two-form itself and then contract with the moving normal. -/
theorem nativeEdge_restrict_mixed (i : Fin 4) (k : Fin 3) (g : FixedOverlap i k →ₐ[ℂ] U)
    (v : Derivation ℂ U C) :
    let m := i.succAbove k
    let f := g.comp (fixedTargetMap i k)
    letI := f.toRingHom.toAlgebra
    letI : IsScalarTower ℂ (T m) U := IsScalarTower.of_algHom f
    letI := ((IsScalarTower.toAlgHom ℂ U C).comp f).toRingHom.toAlgebra
    letI : IsScalarTower ℂ (T m) C := IsScalarTower.of_algHom ((IsScalarTower.toAlgHom ℂ U C).comp f)
    letI : IsScalarTower (T m) U C := IsScalarTower.of_algebraMap_eq' rfl
    let x := normalizedLift i k g
    let y := canonical m f
    let hx : LiesOver x f := normalizedLift_fst i k g
    let hy : LiesOver y f := canonical_liesOver _ _
    contractRestrict v (CycleQ2ExteriorSectionNaturality.exteriorDifferentialMap g 2 (nativeEdge i k)) =
      mixed (covectorAlong (liftCovector f x y hx hy)) (v.compAlgebraMap (T m)) (orientedVolume m) := by
  dsimp only
  rw [nativeEdge_restrict]
  exact edgeAt_mixed i k g v

end CycleQ2LiteralThreefoldNativeMixedEdge
end

#print axioms CycleQ2LiteralThreefoldNativeMixedEdge.value_mixed
#print axioms CycleQ2LiteralThreefoldNativeMixedEdge.edgeAt_mixed
#print axioms CycleQ2LiteralThreefoldNativeMixedEdge.nativeEdge_restrict_mixed
