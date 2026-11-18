import Proposal.GeometricLiteralAbelJacobiEvaluationRestriction
import Proposal.GeometricLiteralAbelJacobiEvaluationFiber
import Proposal.GeometricExteriorPullComposition

/-!
# The restriction of absolute two-forms to the original first-order germ

The two steps of restriction, from the smooth time family to its retained
tangent germ and from that germ to any of its four affine charts, agree
with the direct differential pullback on all local two-forms.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralAbelJacobiEvaluationGerm

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
  CycleQ2LiteralAbelJacobiEvaluationRestriction CycleQ2LiteralAbelJacobiEvaluationFiber
  CycleQ2LiteralAbelJacobiTimeFamily CycleQ2LiteralAbelJacobiTimeCharts
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceChartFiberScheme CycleQ2IncidenceSeedFiberCover
  CycleQ2FirstOrderCurve CycleQ2FirstOrderCurveCharts CycleQ2LiteralCylinderEvaluation
  CycleQ2LiteralIncidenceTimeCurve CycleQ2LiteralAbelJacobiMovingNormal
  CycleQ2LiteralAbelJacobiQPullback CycleQ2ExteriorPullComposition
  CycleQ2GeometricAffineChartSections CycleQ2GeometricAffineDifferentialSheaf

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  CycleQ2CurveParameterTangent.chartComplexAlgebra

variable (t : Fin 3 → ℂ)

abbrev germStructure := firstOrderCurveToBase t ≫ structureDual
abbrev germCoefficient := schemeCoefficient (germStructure t)
abbrev germTwoForms := forms (firstOrderCurve t) (germCoefficient t) 2

theorem germToTime_overComplex (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V) :
    germToTime t V hV ≫ projection V t ≫ (timeOpen V).ι ≫ toComplex = germStructure t := by
  unfold germToTime germStructure
  rw [Category.assoc, ← pullback.condition_assoc, firstOrderIso_toBase_assoc, tangentLift_fac_assoc, timeTangent, toComplex, pullback.lift_fst]

theorem germChart_overComplex (i : Fin 4) :
    firstOrderChartToCurve t i ≫ germStructure t =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (B t i))) := by
  rw [germStructure, firstOrderChartToCurve_overBase_assoc, structureDual, ← Spec.map_comp]
  apply congrArg Spec.map
  ext c
  exact (chartMap_constant t i c).symm

theorem germChart_compatible (i : Fin 4) :
    compatible (firstOrderChartToCurve t i) (affineCoefficient (B t i)) (germCoefficient t) := by
  intro U c
  refine (coefficientOn_app (firstOrderChartToCurve t i) (germStructure t) U c).trans ?_
  apply congrArg (fun φ => CycleQ2GeometricDifferentialSheaf.coefficientOn (Spec.structureSheaf (B t i)) φ _ c)
  exact (congrArg schemeCoefficient (germChart_overComplex t i)).trans
    (congrArg CommRingCat.Hom.hom (affineCoefficient_structureMorphism (B t i)).symm)

abbrev germToChart (i : Fin 4) :=
  schemeExteriorPull (firstOrderChartToCurve t i) _ _ (germChart_compatible t i) 2

variable (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V)

abbrev toGerm :=
  schemeExteriorPull (germToTime t V hV) (germCoefficient t) (familyCoefficient V t)
    (compatible_over _ _ _ (germToTime_overComplex t V hV)) 2

/-- Direct and iterated restriction agree on every sheafified two-form. -/
theorem toChart_apply (i : Fin 4) (U : (family V t).Opens) (ω : (familyTwoForms V t).val.obj (op U)) :
    (toThickTwoForms V t hV i).val.app (op U) ω =
      (germToChart t i).val.app (op ((germToTime t V hV) ⁻¹ᵁ U))
        ((toGerm t V hV).val.app (op U) ω) :=
  schemeExteriorPull_comp_apply (firstOrderChartToCurve t i) (germToTime t V hV) _ _ _
    (germChart_compatible t i) (compatible_over _ _ _ (germToTime_overComplex t V hV)) 2 U ω

end CycleQ2LiteralAbelJacobiEvaluationGerm
end

#print axioms CycleQ2LiteralAbelJacobiEvaluationGerm.toChart_apply
