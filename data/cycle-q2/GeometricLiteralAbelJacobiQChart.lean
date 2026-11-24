import Proposal.GeometricLiteralAbelJacobiQChartSource
import Proposal.GeometricLiteralAbelJacobiQChartTarget

/-!
# The actual affine pullback of the second cylinder projection

After identifying the fixed coefficient fibre with the smooth incidence
threefold, the affine map of the original germ is the polynomial map used
to compute its conormal. Reduction yields the original seed chart map.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralAbelJacobiQChart

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
  CycleQ2LiteralAbelJacobiTimeCharts CycleQ2LiteralAbelJacobiTimeProjection
  CycleQ2LiteralAbelJacobiQChartSource CycleQ2LiteralAbelJacobiQChartTarget
  CycleQ2LiteralAbelJacobiQCoordinates CycleQ2LiteralIncidenceTimeCurve
  CycleQ2LiteralIncidenceCylinderMap CycleQ2LiteralAmbientCylinder
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceTimeCurve CycleQ2IncidenceChartFiberScheme
  CycleQ2IncidenceSeedFiberCover CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralCylinderEvaluation
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2IncidenceImageLine

attribute [local instance] CycleQ2IncidenceTimeCurve.timeParameterCommRing
  CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower

private instance : IsClosedImmersion seedSextic := by
  have eq : Spec.map (CommRingCat.ofHom sexticEval) = seedSextic := by
    rw [seedSextic, seedPointMorphism, parameterToSextics, ← Spec.map_comp]
    rfl
  rw [← eq]
  apply IsClosedImmersion.spec_of_surjective
  intro z
  refine ⟨C z, ?_⟩
  change seedMap (sexticToParameter (C z)) = z
  rw [CycleQ2GenericTimeDerivation.sexticToParameter_C, CycleQ2IncidenceSeedFiber.seedMap_complex]

private theorem target_overUniversal (i : Fin 4) :
    nativeChartInclusion i ≫ nativeToUniversal.hom ≫ pullback.snd seedSextic universalAmbientToBase =
      Spec.map (CommRingCat.ofHom (universalToT i)) ≫ sexticInclusion universalPoint i := by
  rw [nativeToUniversal_snd]
  change (Spec.map (CommRingCat.ofHom (nativeToT i)) ≫ sexticInclusion point i) ≫ _ = _
  rw [Category.assoc, coefficient_inclusion, ← Spec.map_comp_assoc]
  rfl

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ) (hV : seedBasePoint ∈ V) (i : Fin 4)

private theorem thickChart_toFixed : thickChart V t hV i ≫ q V t =
    Spec.map (CommRingCat.ofHom (toFamily t i)) ≫ nativeChartInclusion i ≫ nativeToUniversal.hom := by
  apply (cancel_mono (pullback.snd seedSextic universalAmbientToBase)).mp
  simp only [Category.assoc, target_overUniversal, thickChart_coordinates]

private theorem closedChart_toFixed : closedChart V t hV i ≫ q V t =
    Spec.map (CommRingCat.ofHom (toCurve t i).toRingHom) ≫ nativeChartInclusion i ≫ nativeToUniversal.hom := by
  apply (cancel_mono (pullback.snd seedSextic universalAmbientToBase)).mp
  simp only [Category.assoc, target_overUniversal, closedChart_coordinates]

/-- On the actual infinitesimal chart the geometric projection is evaluation on the original
moving equations in the fixed sextic. -/
@[reassoc] theorem thickChart_toSmoothThreefold : thickChart V t hV i ≫ q V t ≫ fixedIso.hom =
    Spec.map (CommRingCat.ofHom (toFamily t i)) ≫ CycleQ2LiteralAmbientCharts.chartInclusion i := by
  rw [← Category.assoc, thickChart_toFixed, fixedIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc, nativeChartInclusion_toIncidence]

/-- On the closed chart it is restriction along the actual affine seed curve embedding. -/
@[reassoc] theorem closedChart_toSmoothThreefold : closedChart V t hV i ≫ q V t ≫ fixedIso.hom =
    Spec.map (CommRingCat.ofHom (toCurve t i).toRingHom) ≫ CycleQ2LiteralAmbientCharts.chartInclusion i := by
  rw [← Category.assoc, closedChart_toFixed, fixedIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc, nativeChartInclusion_toIncidence]

end CycleQ2LiteralAbelJacobiQChart
end

#print axioms CycleQ2LiteralAbelJacobiQChart.thickChart_toSmoothThreefold
#print axioms CycleQ2LiteralAbelJacobiQChart.closedChart_toSmoothThreefold
