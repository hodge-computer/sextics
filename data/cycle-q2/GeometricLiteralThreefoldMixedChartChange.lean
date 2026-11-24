import Proposal.GeometricLiteralThreefoldNativeMixedEdge
import Mathlib.RingTheory.Etale.Kaehler

/-!
# Mixed evaluation in the two projective threefold charts

Both tangent arguments are retained on the native ambient overlap. A moving
normal along one chart extends uniquely to its principal localization. The
mixed one-form computed from the oriented volume is independent of which
of the two projective coordinate systems represents the ambient arguments.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

noncomputable section
namespace CycleQ2LiteralThreefoldMixedChartChange

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

/-- Scalar-valued derivations with values on any further curve ring extend
uniquely across a localization of the ambient coordinate ring. -/
theorem existsUnique_localized_vector (m : Submonoid R) [IsLocalization m U] (v : Derivation ℂ R C) :
    ∃! u : Derivation ℂ U C, u.compAlgebraMap R = v := by
  let := Algebra.FormallyEtale.of_isLocalization (Rₘ := U) m
  let l := (v.liftKaehlerDifferential.liftBaseChange U).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℂ R U).symm.toLinearMap
  let u := l.compDer (KaehlerDifferential.D ℂ U)
  have hu : u.compAlgebraMap R = v := by
    ext r
    change v.liftKaehlerDifferential.liftBaseChange U
      ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℂ R U).symm
        (KaehlerDifferential.D ℂ U (algebraMap R U r))) = v r
    rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
      LinearMap.liftBaseChange_tmul, one_smul, Derivation.liftKaehlerDifferential_comp_D]
  refine ⟨u, hu, fun u' hu' => ?_⟩
  have he : u'.liftKaehlerDifferential = u.liftKaehlerDifferential := by
    apply LinearMap.ext_on_range (KaehlerDifferential.span_range_map_derivation_of_isLocalization ℂ R U m)
    intro r
    change u'.liftKaehlerDifferential (KaehlerDifferential.map ℂ ℂ R U (KaehlerDifferential.D ℂ R r)) =
      u.liftKaehlerDifferential (KaehlerDifferential.map ℂ ℂ R U (KaehlerDifferential.D ℂ R r))
    rw [KaehlerDifferential.map_D, Derivation.liftKaehlerDifferential_comp_D,
      Derivation.liftKaehlerDifferential_comp_D]
    exact congrArg (fun d : Derivation ℂ R C => d r) (hu'.trans hu.symm)
  exact (KaehlerDifferential.linearMapEquivDerivation ℂ U (M := C)).symm.injective he

private theorem evaluate_pullback {n : ℕ} (d : Fin n → Derivation ℂ U C) (ω : Forms R n) :
    evaluate d (exteriorDifferentialMap (inclusion R U) n ω) =
      evaluate (fun i => (d i).compAlgebraMap R) ω := by
  have hω : ω ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R n)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hω using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨α,rfl⟩ := hz
    rw [exteriorDifferentialMap_wedge, evaluate_wedge, evaluate_wedge]
    apply congrArg Matrix.det
    ext i j
    exact (congrArg (d j).liftKaehlerDifferential
      (CycleQ2EtaleExteriorMapBinding.differentialMap_algebraMap (B := U) (α i))).trans (lift_map (d j) (α i))
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx =>
    rw [map_smulₛₗ, map_smulₛₗ, map_smulₛₗ, hx, IsScalarTower.algebraMap_apply R U C]
    rfl

/-- Changing the source of both vectors before double contraction is
pullback of the original three-form followed by the same double contraction. -/
theorem mixed_precomp [Module.Projective C (KaehlerDifferential ℂ C)]
    (k v : Derivation ℂ U C) (ω : Forms R 3) :
    mixed (k.compAlgebraMap R) (v.compAlgebraMap R) ω =
      mixed k v (exteriorDifferentialMap (inclusion R U) 3 ω) := by
  apply curve_form_ext
  intro y
  rw [evaluate_mixed, evaluate_mixed, evaluate_pullback]
  apply congrArg (fun d => evaluate d ω)
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact (comp_tower (U := U) y).symm

end Tower

section Chart
variable {U C : Type} [CommRing U] [CommRing C] [Algebra ℂ U] [Algebra ℂ C]
  [Algebra U C] [IsScalarTower ℂ U C]

private abbrev base := (IsScalarTower.toAlgHom ℂ U C)

/-- The mixed form in a fixed chart with both arguments represented on a common overlap. -/
def chartMixed {i : Fin 4} (a : T i →ₐ[ℂ] U) (k v : Derivation ℂ U C) : KaehlerDifferential ℂ C := by
  letI := a.toRingHom.toAlgebra
  letI : IsScalarTower ℂ (T i) U := IsScalarTower.of_algHom a
  letI := ((base (U := U) (C := C)).comp a).toRingHom.toAlgebra
  letI : IsScalarTower ℂ (T i) C := IsScalarTower.of_algHom ((base (U := U) (C := C)).comp a)
  letI : IsScalarTower (T i) U C := IsScalarTower.of_algebraMap_eq' rfl
  exact mixed (k.compAlgebraMap (T i)) (v.compAlgebraMap (T i)) (orientedVolume i)

theorem chartMixed_eq [Module.Projective C (KaehlerDifferential ℂ C)] {i : Fin 4}
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

/-- The original normal vector has a unique representative on the projective intersection. -/
theorem existsUnique_overlap_vector [Algebra (T i) C] [IsScalarTower ℂ (T i) C]
    [IsScalarTower (T i) (FixedOverlap i k) C] (v : Derivation ℂ (T i) C) :
    ∃! u : Derivation ℂ (FixedOverlap i k) C, u.compAlgebraMap (T i) = v :=
  existsUnique_localized_vector (Submonoid.powers (q i (X (some k)))) v

/-- The two oriented chart volumes give the same curve form on every native
threefold overlap with the two ambient vectors represented there. -/
theorem chartMixed_change [Module.Projective C (KaehlerDifferential ℂ C)]
    (x v : Derivation ℂ (FixedOverlap i k) C) :
    chartMixed (fixedTargetMap i k) x v = chartMixed (sourceMap i k) x v := by
  rw [chartMixed_eq, chartMixed_eq]
  apply congrArg (mixed x v)
  unfold orientedVolume
  simp only [map_smulₛₗ, map_pow, map_neg, map_one]
  exact fixedChartVolume_overlap i k

end CycleQ2LiteralThreefoldMixedChartChange
end

#print axioms CycleQ2LiteralThreefoldMixedChartChange.existsUnique_overlap_vector
#print axioms CycleQ2LiteralThreefoldMixedChartChange.chartMixed_change
