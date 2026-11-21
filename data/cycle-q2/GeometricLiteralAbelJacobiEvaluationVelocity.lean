import Proposal.GeometricLiteralAbelJacobiEvaluationAffine
import Proposal.GeometricLiteralAbelJacobiEvaluationGerm
import Proposal.GeometricLiteralAbelJacobiEvaluationSeedForms
import Proposal.GeometricLiteralAbelJacobiEvaluationVelocityAlgebra
import Proposal.GeometricLiteralAbelJacobiEvaluationVelocitySquare
import Proposal.GeometricLiteralAbelJacobiEvaluationVelocityEpsilon

/-!
# Time velocities on opens of the first-order moving curve

Each affine time velocity defines a complex derivation on every subopen of
its projective chart. Its values belong to the structure sheaf of the given
seed curve. Restricting an open preserves the derivation and its normalization
on the actual dual-number parameter.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralAbelJacobiEvaluationVelocity

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
  CycleQ2FirstOrderCurve CycleQ2FirstOrderCurveSeedFiber CycleQ2FirstOrderCurveCharts
  CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralCylinderEvaluation
  CycleQ2LiteralAbelJacobiEvaluationAffine CycleQ2LiteralAbelJacobiEvaluationFiber
  CycleQ2LiteralAbelJacobiEvaluationGerm CycleQ2LiteralAbelJacobiEvaluationSeedForms
  CycleQ2LiteralAbelJacobiEvaluationVelocityEpsilon CycleQ2LiteralIncidenceTimeCurve
  CycleQ2GeometricAffineDifferentialSheaf CycleQ2GeometricDifferentialSheaf
  CycleQ2GeometricSectionDifferentials CycleQ2ExteriorPullComposition
  CycleQ2SeedSectionCurveRows CycleQ2SeedSectionSheafCurveBinding CycleQ2SpecializedProjectiveCurve
  CycleQ2LiteralMovingResidueAdjunction.AffineFrame
open scoped DualNumber

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

variable (t : Fin 3 → ℂ)

abbrev GermRing (W : (firstOrderCurve t).Opens) := Γ(firstOrderCurve t, W)
abbrev SeedRing (W : (firstOrderCurve t).Opens) :=
  Γ(specializedCurve seed t, seedCurveToFirstOrderCurve t ⁻¹ᵁ W)

local instance germAlgebra (W : (firstOrderCurve t).Opens) : Algebra ℂ (GermRing t W) :=
  sectionAlgebra (firstOrderCurve t).sheaf (germCoefficient t) W

local instance seedSectionAlgebra (W : (firstOrderCurve t).Opens) : Algebra ℂ (SeedRing t W) :=
  sectionAlgebra (specializedCurve seed t).sheaf (curveCoefficient t) _

local instance reductionOn (W : (firstOrderCurve t).Opens) : Algebra (GermRing t W) (SeedRing t W) :=
  ((seedCurveToFirstOrderCurve t).app W).hom.toAlgebra

theorem reduction_compatible :
    compatible (seedCurveToFirstOrderCurve t) (curveCoefficient t) (germCoefficient t) := by
  apply compatible_over
  rw [curve_structure, germStructure, ← Category.assoc, seedCurveToFirstOrderCurve_overBase,
    Category.assoc]
  have hc : CycleQ2IncidenceFirstOrder.firstOrderClosedPoint ≫ structureDual = 𝟙 _ := by
    rw [CycleQ2IncidenceFirstOrder.firstOrderClosedPoint, structureDual, ← Spec.map_comp, ← Spec.map_id]
    rfl
  rw [hc, Category.comp_id]

variable (i : Fin 4)

local instance chartReductionModule : Module (B t i) (A t i) :=
  (CycleQ2LiteralCylinderEvaluation.reductionAlgebra t i).toModule

private theorem velocityOn_constant (v : Derivation ℂ (B t i) (A t i))
    (W : (firstOrderCurve t).Opens) (c : ℂ) :
    velocityOn v ((firstOrderChartToCurve t i) ⁻¹ᵁ W)
      ((firstOrderChartToCurve t i).app W
        (coefficientOn (firstOrderCurve t).sheaf (germCoefficient t) W c)) = 0 := by
  rw [germChart_compatible t i W c]
  exact (velocity v).d_app (X := op ((firstOrderChartToCurve t i) ⁻¹ᵁ W)) c

private theorem affine_normalized {B A : Type} [CommRing B] [CommRing A] [Algebra ℂ B]
    [Algebra ℂ A] [Algebra B A] [IsScalarTower ℂ B A]
    (v : Derivation ℂ B A) (a : B) (hv : v a = 1) (U : (Spec (CommRingCat.of B)).Opens) :
    velocityOn v U (algebraMap B (AffineSections B U) a) = 1 := by
  have h := velocityOn_restrict v (homOfLE (show U ≤ ⊤ from le_top))
    (algebraMap B (AffineSections B ⊤) a)
  rw [velocityOn_top, hv, map_one, map_one] at h
  exact h

private theorem velocityOn_epsilon (v : Derivation ℂ (B t i) (A t i))
    (hv : v (algebraMap ℂ[ε] (B t i) ε) = 1) (W : (firstOrderCurve t).Opens) :
    velocityOn v ((firstOrderChartToCurve t i) ⁻¹ᵁ W)
      ((firstOrderChartToCurve t i).app W (epsilonSection t W)) = 1 := by
  exact (congrArg (velocityOn v ((firstOrderChartToCurve t i) ⁻¹ᵁ W))
    (epsilonSection_chart t i W)).trans (affine_normalized v _ hv _)

private theorem withinChart {W : (firstOrderCurve t).Opens} (hW : W ≤ firstOrderCurveCoordinateOpen t i) :
    seedCurveToFirstOrderCurve t ⁻¹ᵁ W ≤ (seedChart t i).opensRange :=
  ((seedCurveToFirstOrderCurve t).preimage_mono hW).trans
    ((germ_preimage_coordinate t i).trans (seedChart_opensRange t i).symm).le

abbrev closedRestriction (W : (firstOrderCurve t).Opens) (hW : W ≤ firstOrderCurveCoordinateOpen t i) :=
  CycleQ2LiteralAbelJacobiEvaluationVelocitySquare.closedRestriction
    (seedChart t i) (seedCurveToFirstOrderCurve t) (reduction (B t i) (A t i))
    (firstOrderChartToCurve t i) (seedChart_to_germ t i) W (withinChart t i hW)

variable (v : Derivation ℂ (B t i) (A t i))

/-- The chart velocity acts on actual sections of the projective thickening
and takes values in actual sections of its seed. -/
def onOpen (W : (firstOrderCurve t).Opens) (hW : W ≤ firstOrderCurveCoordinateOpen t i) :
    Derivation ℂ (GermRing t W) (SeedRing t W) := by
  let j := firstOrderChartToCurve t i
  let s := reduction (B t i) (A t i)
  let d : Γ(Spec (CommRingCat.of (B t i)), j ⁻¹ᵁ W) →+
      Γ(Spec (CommRingCat.of (A t i)), s ⁻¹ᵁ j ⁻¹ᵁ W) := (velocity v).d (X := op (j ⁻¹ᵁ W))
  refine CycleQ2LiteralAbelJacobiEvaluationVelocityAlgebra.descend (j.app W).hom
    (s.app (j ⁻¹ᵁ W)).hom (closedRestriction t i W hW) d ?_ ?_ ?_ ?_
  · exact CycleQ2LiteralAbelJacobiEvaluationVelocitySquare.closedRestriction_app _ _ _ _ _ W _
  · exact reduction_compatible t W
  · intro x y
    exact (velocity v).d_mul x y
  · exact velocityOn_constant t i v W

theorem closedRestriction_onOpen (W : (firstOrderCurve t).Opens) (hW : W ≤ firstOrderCurveCoordinateOpen t i)
    (x : GermRing t W) :
    closedRestriction t i W hW (onOpen t i v W hW x) =
      velocityOn v ((firstOrderChartToCurve t i) ⁻¹ᵁ W) ((firstOrderChartToCurve t i).app W x) :=
  (closedRestriction t i W hW).apply_symm_apply _

theorem chartPreimage (W : (firstOrderCurve t).Opens) :
    (seedChart t i) ⁻¹ᵁ (seedCurveToFirstOrderCurve t) ⁻¹ᵁ W =
      (reduction (B t i) (A t i)) ⁻¹ᵁ (firstOrderChartToCurve t i) ⁻¹ᵁ W :=
  CycleQ2LiteralAbelJacobiEvaluationVelocitySquare.square_preimage _ _ _ _ (seedChart_to_germ t i) W

theorem seedChart_app_onOpen (W : (firstOrderCurve t).Opens) (hW : W ≤ firstOrderCurveCoordinateOpen t i)
    (x : GermRing t W) :
    (seedChart t i).app ((seedCurveToFirstOrderCurve t) ⁻¹ᵁ W) (onOpen t i v W hW x) =
      (Spec (CommRingCat.of (A t i))).presheaf.map (eqToHom (chartPreimage t i W)).op
        (velocityOn v ((firstOrderChartToCurve t i) ⁻¹ᵁ W) ((firstOrderChartToCurve t i).app W x)) := by
  let f := (Spec (CommRingCat.of (A t i))).presheaf.mapIso (eqToIso (chartPreimage t i W).symm).op
  have ha : f.hom ((seedChart t i).app _ (onOpen t i v W hW x)) = _ :=
    closedRestriction_onOpen t i v W hW x
  rw [← ha]
  exact (Iso.hom_inv_id_apply f _).symm

set_option maxHeartbeats 1200000 in
theorem onOpen_restrict {W V : (firstOrderCurve t).Opens} (hWV : W ≤ V)
    (hV : V ≤ firstOrderCurveCoordinateOpen t i) (x : GermRing t V) :
    onOpen t i v W (hWV.trans hV) ((firstOrderCurve t).presheaf.map (homOfLE hWV).op x) =
      (specializedCurve seed t).presheaf.map
        ((Opens.map (seedCurveToFirstOrderCurve t).base).map (homOfLE hWV)).op (onOpen t i v V hV x) := by
  apply (closedRestriction t i W (hWV.trans hV)).injective
  have hr := CycleQ2LiteralAbelJacobiEvaluationVelocitySquare.closedRestriction_restrict
    (seedChart t i) (seedCurveToFirstOrderCurve t) (reduction (B t i) (A t i))
    (firstOrderChartToCurve t i) (seedChart_to_germ t i) hWV (withinChart t i hV) (onOpen t i v V hV x)
  let j := firstOrderChartToCurve t i
  let s := reduction (B t i) (A t i)
  have hx : j.app W ((firstOrderCurve t).presheaf.map (homOfLE hWV).op x) =
      (Spec (CommRingCat.of (B t i))).presheaf.map
        ((Opens.map j.base).map (homOfLE hWV)).op (j.app V x) :=
    ConcreteCategory.congr_hom (j.naturality (homOfLE hWV).op) x
  refine (closedRestriction_onOpen t i v W _ _).trans
    (((congrArg (velocityOn v (j ⁻¹ᵁ W)) hx).trans
      (velocityOn_restrict v ((Opens.map j.base).map (homOfLE hWV)) (j.app V x))).trans ?_)
  exact (congrArg ((Spec (CommRingCat.of (A t i))).presheaf.map
    (homOfLE (s.preimage_mono (j.preimage_mono hWV))).op)
    (closedRestriction_onOpen t i v V hV x).symm).trans hr.symm

theorem onOpen_epsilon (hv : v (algebraMap ℂ[ε] (B t i) ε) = 1)
    (W : (firstOrderCurve t).Opens) (hW : W ≤ firstOrderCurveCoordinateOpen t i) :
    onOpen t i v W hW (epsilonSection t W) = 1 := by
  apply (closedRestriction t i W hW).injective
  rw [closedRestriction_onOpen, map_one]
  exact velocityOn_epsilon t i v hv W

end CycleQ2LiteralAbelJacobiEvaluationVelocity
end

#print axioms CycleQ2LiteralAbelJacobiEvaluationVelocity.onOpen_epsilon
#print axioms CycleQ2LiteralAbelJacobiEvaluationVelocity.onOpen_restrict
