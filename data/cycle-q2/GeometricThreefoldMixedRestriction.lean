import Proposal.GeometricThreefoldMixedWedge
import Proposal.GeometricLiteralThreefoldMixedChartChange

/-!
# Restricting both ambient vectors on arbitrary curve opens

The explicit two-vector contraction of a decomposable three-form commutes
with pullback of its three one-form factors. The oriented ambient charts
therefore give the same mixed one-form over any coefficient ring.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2ThreefoldMixedRestriction

open CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldChartLift
  CycleQ2LiteralThreefoldLiftDifference CycleQ2LiteralThreefoldTangentCoordinates
  CycleQ2LiteralThreefoldResidueChartMaps CycleQ2LiteralThreefoldResidueCoordinates
  CycleQ2LiteralThreefoldLiftTransition CycleQ2ThreefoldContractionAlongMap
  CycleQ2ThreefoldMixedCurveForm CycleQ2LiteralThreefoldSurfaceNormal
  CycleQ2GeometricAffineOverlap CycleQ2ExteriorSectionNaturality CycleQ2ThreefoldCurveEvaluation
  CycleQ2LiteralThreefoldSurfaceAdjunction

section Tower

variable {R U C : Type} [CommRing R] [CommRing U] [CommRing C]
  [Algebra ℂ R] [Algebra ℂ U] [Algebra ℂ C] [Algebra R U] [Algebra R C] [Algebra U C]
  [IsScalarTower ℂ R U] [IsScalarTower ℂ R C] [IsScalarTower ℂ U C] [IsScalarTower R U C]

private abbrev inclusion (R U : Type) [CommRing R] [CommRing U] [Algebra ℂ R] [Algebra ℂ U]
    [Algebra R U] [IsScalarTower ℂ R U] := IsScalarTower.toAlgHom ℂ R U


open CycleQ2ThreefoldMixedWedge CycleQ2EtaleExteriorMapBinding

/-- Both tangent slots may be restricted along the same source map before contraction. -/
theorem mixed_precomp (k v : Derivation ℂ U C) (ω : Forms R 3) :
    mixed (k.compAlgebraMap R) (v.compAlgebraMap R) ω =
      mixed k v (exteriorDifferentialMap (inclusion R U) 3 ω) := by
  have hω : ω ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 3)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hω using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m,rfl⟩ := hz
    rw [exteriorDifferentialMap_wedge, mixed_wedge, mixed_wedge]
    have hmap (α : KaehlerDifferential ℂ R) :
        KaehlerDifferential.map ℂ ℂ U C (KaehlerDifferential.map ℂ ℂ R U α) =
          KaehlerDifferential.map ℂ ℂ R C α :=
      CycleQ2NormalAdjunctionNaturality.differentialRestriction_tower R U C α
    simp only [inclusion, differentialMap_algebraMap, lift_map, pairValue,
      Fin.removeNth, Function.comp_apply, hmap]
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx =>
    rw [map_smulₛₗ, map_smulₛₗ, map_smulₛₗ, hx, IsScalarTower.algebraMap_apply R U C]
    rfl

end Tower

open CycleQ2LiteralThreefoldMixedChartChange (chartMixed)

section Chart
variable {U C : Type} [CommRing U] [CommRing C] [Algebra ℂ U] [Algebra ℂ C]
  [Algebra U C] [IsScalarTower ℂ U C]

private abbrev base := (IsScalarTower.toAlgHom ℂ U C)

theorem chartMixed_eq {i : Fin 4}
    (a : T i →ₐ[ℂ] U) (k v : Derivation ℂ U C) :
    chartMixed a k v = mixed k v (exteriorDifferentialMap a 3 (orientedVolume i)) := by
  let := a.toRingHom.toAlgebra
  let : IsScalarTower ℂ (T i) U := IsScalarTower.of_algHom a
  let := ((base (U := U) (C := C)).comp a).toRingHom.toAlgebra
  let : IsScalarTower ℂ (T i) C := IsScalarTower.of_algHom ((base (U := U) (C := C)).comp a)
  let : IsScalarTower (T i) U C := IsScalarTower.of_algebraMap_eq' rfl
  exact mixed_precomp k v (orientedVolume i)

end Chart

open CycleQ2LiteralThreefoldResidueGluing MvPolynomial
attribute [local instance] sourceFixedAlgebra sourceFixedTower sourceFixedLocalization

variable {C : Type} [CommRing C] [Algebra ℂ C] (i : Fin 4) (k : Fin 3)
  [Algebra (FixedOverlap i k) C] [IsScalarTower ℂ (FixedOverlap i k) C]

/-- The two oriented chart volumes give the same curve form on every native
threefold overlap with the two ambient vectors represented there. -/
theorem chartMixed_change
    (x v : Derivation ℂ (FixedOverlap i k) C) :
    chartMixed (fixedTargetMap i k) x v = chartMixed (sourceMap i k) x v := by
  rw [chartMixed_eq, chartMixed_eq]
  apply congrArg (mixed x v)
  unfold orientedVolume
  simp only [map_smulₛₗ, map_pow, map_neg, map_one]
  exact fixedChartVolume_overlap i k

end CycleQ2ThreefoldMixedRestriction
end

#print axioms CycleQ2ThreefoldMixedRestriction.mixed_precomp
#print axioms CycleQ2ThreefoldMixedRestriction.chartMixed_change
