import Proposal.GeometricLiteralAbelJacobiTimeCharts
import Proposal.GeometricLiteralAbelJacobiQCoordinates

/-!
# The affine coordinate map of the geometric second projection

On the actual seed and infinitesimal curve charts, the universal sextic
coordinates of the second projection evaluate by the original homogeneous
coordinate maps. The formulas use the entire degree-zero coordinate rings.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section

namespace CycleQ2LiteralAbelJacobiQChartSource

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
  CycleQ2LiteralAbelJacobiQCoordinates CycleQ2LiteralAbelJacobiTimeCharts
  CycleQ2LiteralAbelJacobiTimeProjection CycleQ2LiteralAbelJacobiTimeFamily
  CycleQ2IncidenceNormalForm CycleQ2IncidenceEtaleParameter CycleQ2IncidenceImageLine
  CycleQ2IncidenceUniversalChart CycleQ2IncidenceFamilyContainment CycleQ2GeometricIncidenceProj
  CycleQ2IncidenceDehomogenizedChart CycleQ2RelativeConstantCurve CycleQ2RelativeCurveChart
  CycleQ2RelativeCurveChartScheme CycleQ2IncidenceChartFiberScheme CycleQ2IncidenceSeedFiberCover
  CycleQ2IncidenceTimeCurve CycleQ2LiteralIncidenceTimeCurve CycleQ2LiteralIncidenceCylinderMap
  CycleQ2FirstOrderCurveCharts CycleQ2FirstOrderChartFlatness CycleQ2FirstOrderTensorReduction
  CycleQ2LiteralCylinderEvaluation CycleQ2LiteralAbelJacobiMovingNormal
  CycleQ2RelativeCurveChartFiber CycleQ2FirstOrderChartReduction

attribute [local instance] CycleQ2RelativeCurveChartScheme.relativeCurveCommRing
  CycleQ2RelativeCurveChartScheme.curveCoordinateCommRing CycleQ2RelativeCurveChartScheme.affineCurveChartCommRing
  CycleQ2RelativeCurveChart.pointSurfaceCommRing CycleQ2RelativeCurveChart.coordinateRingCommRing
  CycleQ2RelativeCurveChart.dehomogenizedCommRing CycleQ2IncidenceTimeCurve.timeParameterCommRing
  CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower

section ChangeCoefficients

variable {R S : Type} [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S]

def sexticInclusion (y : ParameterIndex → R) (i : Fin 4) :
    Spec (CommRingCat.of (SexticChart y i)) ⟶ weightedThreefold y :=
  Proj.awayι (sexticGrade y) (sexticX y i) (sexticX_mem y i) (by decide)

@[reassoc] theorem coefficient_inclusion (φ : R →+* S) (y : ParameterIndex → R) (u : ParameterIndex → S)
    (hF : map φ (pointEquationF y) = pointEquationF u) (i : Fin 4) :
    sexticInclusion u i ≫ CycleQ2ThreefoldCoefficientMap.morphism φ y u hF =
      Spec.map (CommRingCat.ofHom (coefficientChart φ y u hF i)) ≫ sexticInclusion y i :=
  CycleQ2GradedAwaySpecialization.awayι_comp_map_of_eq _
    (CycleQ2ThreefoldCoefficientMap.irrelevant_le φ y u hF) _ _ (coefficientX φ y u hF i)
    (by decide) (sexticX_mem y i) (sexticX_mem u i)

def surfaceInclusion (y : ParameterIndex → S) (i : Fin 4) :
    Spec (CommRingCat.of (CoordinateRing y i)) ⟶ surface y :=
  Proj.awayι (surfaceGrade y) (surfaceQuotient y (X i.castSucc))
    (coordinate_mem_grade y i) (by decide)

@[reassoc] theorem surface_inclusion (y : ParameterIndex → S) (i : Fin 4) :
    surfaceInclusion y i ≫ surfaceToThreefold y =
        Spec.map (CommRingCat.ofHom (surfaceChart y i)) ≫ sexticInclusion y i :=
  Proj.awayι_comp_map (surfaceThreefoldRingMap y) (irrelevant_le_map_surfaceThreefoldRingMap y)
    (by decide : 0 < (1 : ℕ)) (sexticX y i) (sexticX_mem y i)

private def curveInclusion (y : ParameterIndex → S) (t : Fin 3 → ℂ) (i : Fin 4) :
    Spec (CommRingCat.of (CurveCoordinateRing y t i)) ⟶ relativeCurve y t :=
  Proj.awayι (relativeCurveGrade y t) (relativeCurveRingMap y t (surfaceQuotient y (X i.castSucc)))
    ((relativeCurveRingMap y t).2 (coordinate_mem_grade y i)) (by decide)

@[reassoc] private theorem relative_inclusion (y : ParameterIndex → S) (t : Fin 3 → ℂ) (i : Fin 4) :
    curveInclusion y t i ≫ relativeCurveToSurface y t =
      Spec.map (CommRingCat.ofHom (coordinateCurveMap y t i).toRingHom) ≫
        surfaceInclusion y i := by
  unfold surfaceInclusion curveInclusion relativeCurveToSurface coordinateCurveMap
  exact Proj.awayι_comp_map (relativeCurveRingMap y t) (irrelevant_le_map_relativeCurveRingMap y t)
    (by decide : 0 < (1 : ℕ)) (surfaceQuotient y (X i.castSucc)) (coordinate_mem_grade y i)

@[reassoc] private theorem curve_chart_factorization (y : ParameterIndex → S) (t : Fin 3 → ℂ) (i : Fin 4) :
    (curveCoordinateAffineChart y t i).inv ≫ (curveCoordinatePatch y t i).ι =
      Spec.map (CommRingCat.ofHom (curveCoordinateChartEquiv y t i).toRingHom) ≫ curveInclusion y t i := by
  exact Category.assoc (Spec.map (CommRingCat.ofHom (curveCoordinateChartEquiv y t i).toRingHom))
    (Proj.basicOpenIsoSpec (relativeCurveGrade y t) _
      ((relativeCurveRingMap y t).2 (coordinate_mem_grade y i)) (by decide : 0 < (1 : ℕ))).inv
    (curveCoordinatePatch y t i).ι

end ChangeCoefficients

variable (t : Fin 3 → ℂ) (i : Fin 4)

private theorem projective_chart_map :
    curveInclusion incidencePoint t i ≫ originalToAmbient t =
      Spec.map (CommRingCat.ofHom (universalToOriginal t i)) ≫ sexticInclusion universalPoint i := by
  rw [originalToAmbient, relative_inclusion_assoc, surface_inclusion_assoc, coefficient_inclusion,
    ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  rfl

@[reassoc] theorem affine_chart_map : originalCurveChart t i ≫ originalToAmbient t =
    Spec.map (CommRingCat.ofHom ((curveCoordinateChartEquiv incidencePoint t i).toRingHom.comp
      (universalToOriginal t i))) ≫ sexticInclusion universalPoint i := by
  rw [originalCurveChart, curve_chart_factorization, Category.assoc, projective_chart_map, ← Spec.map_comp_assoc]
  rfl

variable (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V)

@[reassoc] theorem thickChart_coordinates : thickChart V t hV i ≫ q V t ≫
      pullback.snd seedSextic universalAmbientToBase =
    Spec.map (CommRingCat.ofHom (toFamily t i)) ≫ Spec.map (CommRingCat.ofHom (universalToT i)) ≫
      sexticInclusion universalPoint i := by
  rw [thickChart_q_original, affine_chart_map, tensorChartToOriginal, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  apply congrArg (fun f => Spec.map (CommRingCat.ofHom f) ≫ sexticInclusion universalPoint i)
    (firstOrder_compatibility t i)

@[reassoc] theorem closedChart_coordinates : closedChart V t hV i ≫ q V t ≫
      pullback.snd seedSextic universalAmbientToBase =
    Spec.map (CommRingCat.ofHom (CycleQ2LiteralAbelJacobiContraction.toCurve t i).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (universalToT i)) ≫ sexticInclusion universalPoint i := by
  rw [closedChart_q_original, affine_chart_map, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f) ≫ sexticInclusion universalPoint i)
    (closed_compatibility t i)

end CycleQ2LiteralAbelJacobiQChartSource
end

#print axioms CycleQ2LiteralAbelJacobiQChartSource.thickChart_coordinates
#print axioms CycleQ2LiteralAbelJacobiQChartSource.closedChart_coordinates
