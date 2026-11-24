import Proposal.GeometricLiteralAbelJacobiQPullback
import Proposal.GeometricLiteralAbelJacobiQChart

/-!
# Restricting the time family's two-forms to its infinitesimal charts

The absolute complex differential sheaf of the smooth family pulls back
along each original infinitesimal incidence chart. Its complex coefficients
are those of the original flat dual-number algebra, including on all subopens.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralAbelJacobiEvaluationRestriction

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
  CycleQ2LiteralAbelJacobiTimeFamily CycleQ2LiteralAbelJacobiTimeCharts
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceChartFiberScheme CycleQ2IncidenceSeedFiberCover
  CycleQ2LiteralIncidenceTimeCurve CycleQ2LiteralAbelJacobiMovingNormal
  CycleQ2LiteralCylinderEvaluation CycleQ2LiteralAbelJacobiQPullback
  CycleQ2GeometricAffineChartSections CycleQ2GeometricAffineDifferentialSheaf
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricExteriorSheaf
  CycleQ2GeometricSchemeDifferentialMap

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  CycleQ2CurveParameterTangent.chartComplexAlgebra

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ) (hV : seedBasePoint ∈ V) (i : Fin 4)

theorem thickChart_overComplex :
    thickChart V t hV i ≫ projection V t ≫ (timeOpen V).ι ≫ toComplex =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (B t i))) := by
  rw [thickChart_toBase_assoc, tangentLift_fac_assoc]
  change Spec.map _ ≫ (pullback.lift _ _ _ ≫ pullback.fst _ _) = _
  rw [pullback.lift_fst, structureDual, ← Spec.map_comp]
  apply congrArg Spec.map
  ext c
  exact (chartMap_constant t i c).symm

theorem thickChart_coefficient (U : (family V t).Opens) (c : ℂ) :
    (thickChart V t hV i).app U (coefficientOn (family V t).sheaf (familyCoefficient V t) U c) =
      coefficientOn (Spec.structureSheaf (B t i)) (affineCoefficient (B t i)) ((thickChart V t hV i) ⁻¹ᵁ U) c := by
  refine (coefficientOn_app (thickChart V t hV i) (projection V t ≫ (timeOpen V).ι ≫ toComplex) U c).trans ?_
  apply congrArg (fun φ => coefficientOn (Spec.structureSheaf (B t i)) φ _ c)
  exact (congrArg schemeCoefficient (thickChart_overComplex V t hV i)).trans
    (congrArg CommRingCat.Hom.hom (affineCoefficient_structureMorphism (B t i)).symm)

abbrev thickTwoForms :=
  exteriorSheaf (Spec.structureSheaf (B t i)) (affineDifferentialSheaf (B t i)).val 2

/-- The genuine scheme pullback to the thick chart before taking its normalized tangent coefficient. -/
def toThickTwoForms :
    familyTwoForms V t ⟶ (Scheme.Modules.pushforward (thickChart V t hV i)).obj (thickTwoForms t i) :=
  exteriorPull (thickChart V t hV i)
    (schemeDifferentialMap (thickChart V t hV i) _ _ (thickChart_coefficient V t hV i)) 2

theorem toThickTwoForms_section (U : (family V t).Opens)
    (x : ⋀[Γ(family V t,U)]^2 ((familyDifferentials V t).val.obj (op U))) :
    (toThickTwoForms V t hV i).val.app (op U)
        (exteriorSection (family V t).sheaf (familyDifferentials V t).val 2 U x) =
      exteriorSection (Spec.structureSheaf (B t i)) (affineDifferentialSheaf (B t i)).val 2
        ((thickChart V t hV i) ⁻¹ᵁ U)
        (exteriorMap ((thickChart V t hV i).app U).hom
          (onSections _ (schemeDifferentialMap (thickChart V t hV i) _ _
            (thickChart_coefficient V t hV i)) U) 2 x) :=
  exteriorPull_section _ _ _ _ _

end CycleQ2LiteralAbelJacobiEvaluationRestriction
end

#print axioms CycleQ2LiteralAbelJacobiEvaluationRestriction.toThickTwoForms
#print axioms CycleQ2LiteralAbelJacobiEvaluationRestriction.toThickTwoForms_section
