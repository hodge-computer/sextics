import Proposal.GeometricLiteralAbelJacobiEvaluationVelocity
import Proposal.GeometricLiteralAbelJacobiEvaluationFiberVelocity

/-!
# Agreement on actual affine open sections in two original charts

Each chart's sheaf velocity restricts to a derivation of the same ring
of sections of the infinitesimal germ, with values in the same ring of
sections of its closed curve. Their contractions agree on every two-form
on each affine open contained in both chart ranges.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralAbelJacobiEvaluationOverlapSections

open CategoryTheory Opposite AlgebraicGeometry
open scoped DualNumber
open CycleQ2FirstOrderCurve CycleQ2FirstOrderCurveCharts CycleQ2FirstOrderCurveSeedFiber
  CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralAbelJacobiContraction
  CycleQ2LiteralAbelJacobiEvaluationOverlap CycleQ2LiteralAbelJacobiEvaluationVelocity
  CycleQ2LiteralAbelJacobiEvaluationFiberSections CycleQ2LiteralAbelJacobiEvaluationFiberSectionsContraction

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  CycleQ2LiteralCylinderEvaluation.familyRing
  CycleQ2LiteralCylinderEvaluation.closedRing
  CycleQ2CurveParameterTangent.chartComplexAlgebra
  CycleQ2LiteralCylinderEvaluation.familyComplexSMul
  CycleQ2LiteralCylinderEvaluation.familyComplexModule
  CycleQ2LiteralCylinderEvaluation.reductionAlgebra
  CycleQ2LiteralCylinderEvaluation.familyReductionTower
  CycleQ2LiteralAbelJacobiEvaluationVelocity.chartReductionModule
  CycleQ2LiteralAbelJacobiEvaluationVelocity.germAlgebra
  CycleQ2LiteralAbelJacobiEvaluationVelocity.seedSectionAlgebra
  CycleQ2LiteralAbelJacobiEvaluationVelocity.reductionOn
  CycleQ2LiteralAbelJacobiEvaluationFiberVelocity.sectionTower

variable (t : Fin 3 → ℂ) (W : (firstOrderCurve t).Opens)

/-- The two actual restricted velocities give the same map on all two-forms of every affine overlap open. -/
theorem onOpen_pair (ht : AlgebraicIndependent ℚ t) (hW : IsAffineOpen W) (i j : Fin 4)
    (hi : W ≤ firstOrderCurveCoordinateOpen t i) (hj : W ≤ firstOrderCurveCoordinateOpen t j)
    (v : Derivation ℂ (B t i) (A t i)) (w : Derivation ℂ (B t j) (A t j))
    (hv : v (algebraMap ℂ[ε] (B t i) ε) = 1) (hw : w (algebraMap ℂ[ε] (B t j) ε) = 1) :
    contractRestrict (onOpen t i v W hi) = contractRestrict (onOpen t j w W hj) :=
  CycleQ2LiteralAbelJacobiEvaluationFiberVelocity.contraction_unique t W hW ht _ _
    (onOpen_epsilon t i v hv W hi) (onOpen_epsilon t j w hw W hj)

open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSectionDifferentials
  CycleQ2LiteralMovingResidueAdjunction.AffineFrame CycleQ2SpecializedProjectiveCurve

/-- The universal projective curve differential of the restriction of a germ function. -/
abbrev seedDifferential (a : GermRing t W) :=
  (universalDifferential (specializedCurve CycleQ2SeedConeSection.seed t).sheaf (curveCoefficient t)).d
    (X := op (seedCurveToFirstOrderCurve t ⁻¹ᵁ W)) ((seedCurveToFirstOrderCurve t).app W a)

/-- Cartan evaluation of two exact germ forms agrees in the native differential sheaf
of the original seed curve, for every affine open contained in both chart ranges. -/
theorem onOpen_cartan (ht : AlgebraicIndependent ℚ t) (hW : IsAffineOpen W) (i j : Fin 4)
    (hi : W ≤ firstOrderCurveCoordinateOpen t i) (hj : W ≤ firstOrderCurveCoordinateOpen t j)
    (v : Derivation ℂ (B t i) (A t i)) (w : Derivation ℂ (B t j) (A t j))
    (hv : v (algebraMap ℂ[ε] (B t i) ε) = 1) (hw : w (algebraMap ℂ[ε] (B t j) ε) = 1)
    (a b : GermRing t W) :
    onOpen t i v W hi a • seedDifferential t W b - onOpen t i v W hi b • seedDifferential t W a =
      onOpen t j w W hj a • seedDifferential t W b - onOpen t j w W hj b • seedDifferential t W a := by
  have h := LinearMap.congr_fun (onOpen_pair t W ht hW i j hi hj v w hv hw)
    (exteriorPower.ιMulti (GermRing t W) 2
      ![KaehlerDifferential.D ℂ (GermRing t W) a, KaehlerDifferential.D ℂ (GermRing t W) b])
  simp only [contractRestrict_wedge, Derivation.liftKaehlerDifferential_comp_D, KaehlerDifferential.map_D] at h
  have he := congrArg (toSheaf (specializedCurve CycleQ2SeedConeSection.seed t).sheaf (curveCoefficient t)
    (seedCurveToFirstOrderCurve t ⁻¹ᵁ W)) h
  have hD (x : GermRing t W) :
      toSheaf (specializedCurve CycleQ2SeedConeSection.seed t).sheaf (curveCoefficient t)
          (seedCurveToFirstOrderCurve t ⁻¹ᵁ W)
          (KaehlerDifferential.D ℂ (SeedRing t W) (algebraMap (GermRing t W) (SeedRing t W) x)) =
        seedDifferential t W x :=
    toSheaf_D (specializedCurve CycleQ2SeedConeSection.seed t).sheaf (curveCoefficient t)
      (seedCurveToFirstOrderCurve t ⁻¹ᵁ W) ((seedCurveToFirstOrderCurve t).app W x)
  simpa only [map_sub, map_smul, hD] using he

end CycleQ2LiteralAbelJacobiEvaluationOverlapSections
end

#print axioms CycleQ2LiteralAbelJacobiEvaluationOverlapSections.onOpen_pair

#print axioms CycleQ2LiteralAbelJacobiEvaluationOverlapSections.onOpen_cartan
