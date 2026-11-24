import Proposal.GeometricLiteralAbelJacobiTimeProjection
import Proposal.GeometricFirstOrderCurveCharts
import Proposal.GeometricRelativeCurveSeedChart

/-!
# The two cylinder projections on the actual pointed affine charts

Each original infinitesimal chart maps into the open time family. Its base map
is the retained tangent, and its composition with the fixed sextic projection
uses the original affine polynomial chart of the incidence family. At the
closed point the corresponding chart uses the original seed specialization.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralAbelJacobiTimeCharts

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceChartFiberScheme CycleQ2IncidenceSeedFiberCover
  CycleQ2LiteralIncidenceTimeCurve CycleQ2LiteralIncidenceCylinderMap
  CycleQ2LiteralAbelJacobiTimeProjection CycleQ2LiteralAbelJacobiTimeFamily
  CycleQ2FirstOrderCurve CycleQ2FirstOrderCurveCharts CycleQ2FirstOrderTensorReduction
  CycleQ2FirstOrderChartFlatness CycleQ2FirstOrderChartReduction CycleQ2RelativeCurveChart
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2SpecializedCurveCoordinateChart
  CycleQ2RelativeCurveSeedChart CycleQ2RelativeCurveChartFiber CycleQ2RelativeCurveChartScheme
  CycleQ2RelativeCurveSeedProj CycleQ2RelativeCurveSeedFiberIso

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ) (hV : seedBasePoint ∈ V) (i : Fin 4)

def thickChart : Spec (CommRingCat.of (FirstOrderCurveChart t i)) ⟶ family V t :=
  firstOrderChartToCurve t i ≫ (firstOrderIso V t hV).hom ≫ pullback.snd _ _

def closedChart : Spec (CommRingCat.of (AffineCurveChart (seedPoint (57 : ℂ) Complex.I) t i)) ⟶ family V t :=
  (specializedCoordinateAffineChart (seedPoint (57 : ℂ) Complex.I) t i).inv ≫
    (specializedCoordinatePatch (seedPoint (57 : ℂ) Complex.I) t i).ι ≫
    (seedIso V t hV).hom ≫ pullback.snd _ _

@[reassoc] theorem thickChart_toBase : thickChart V t hV i ≫ projection V t =
    Spec.map (CommRingCat.ofHom (algebraMap (DualNumber ℂ) (FirstOrderCurveChart t i))) ≫ tangentLift V hV := by
  simp only [thickChart, Category.assoc, ← pullback.condition, firstOrderIso_toBase_assoc,
    firstOrderChartToCurve_overBase_assoc]

@[reassoc] theorem thickChart_q_original : thickChart V t hV i ≫ q V t ≫
      pullback.snd seedSextic universalAmbientToBase =
    tensorChartToOriginal (AffineCurveChart incidencePoint t i) ≫ originalCurveChart t i ≫ originalToAmbient t := by
  simp only [thickChart, Category.assoc, firstOrder_to_q_assoc, toFixedThreefold_original,
    CycleQ2LiteralIncidenceTimeFamily.firstOrderIso_toOriginal_assoc, firstOrderChartToCurve_original_assoc]

@[reassoc] theorem closedChart_q_original : closedChart V t hV i ≫ q V t ≫
      pullback.snd seedSextic universalAmbientToBase =
    Spec.map (CommRingCat.ofHom (curveChartSpecialization t i)) ≫ originalCurveChart t i ≫ originalToAmbient t := by
  simp only [closedChart, Category.assoc, seed_to_q_assoc, toFixedThreefold_original,
    CycleQ2LiteralIncidenceTimeFamily.seedIso_toOriginal_assoc, seedCurveToRelative_on_coordinateChart_assoc,
    originalCurveChart]

end CycleQ2LiteralAbelJacobiTimeCharts
end

#print axioms CycleQ2LiteralAbelJacobiTimeCharts.thickChart_q_original
#print axioms CycleQ2LiteralAbelJacobiTimeCharts.closedChart_q_original
