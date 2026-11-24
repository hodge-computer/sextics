import Proposal.GeometricThreefoldCoefficientMap
import Proposal.GeometricLiteralIncidenceTimeFamily

/-!
# The two maps of the moving curve correspondence

The moving projective family over the pointed complex parameter curve maps
to the fixed coefficient fibre of the universal invariant sextic. The map
comes from the coordinates of the original embedded section and the exact
identity of its defining sextic along the fixed-sextic slice.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralIncidenceCylinderMap

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
  CycleQ2IncidenceNormalForm CycleQ2IncidenceUniversalChart CycleQ2IncidenceImageLine
  CycleQ2IncidenceGenericPointSemantics CycleQ2GeometricIncidenceProj
  CycleQ2IncidenceFamilyContainment CycleQ2IncidenceTimeCurve CycleQ2IncidenceEtaleParameter
  CycleQ2RelativeConstantCurve CycleQ2LiteralIncidenceTimeCurve CycleQ2LiteralIncidenceTimeFamily

attribute [local instance] CycleQ2IncidenceTimeCurve.timeParameterCommRing

/-- Only the sextic variables enter the universal hypersurface. -/
def universalPoint : ParameterIndex → CycleQ2IncidenceTimeCurve.SexticRing :=
  Sum.elim (fun _ => 0) (Sum.elim X (fun _ => 0))

theorem universal_to_incidence :
    map sexticToParameter (pointEquationF universalPoint) = pointEquationF incidencePoint := by
  simp only [pointEquationF, pointMap_familyF, map_fullInvariantPolynomial]
  apply congrArg (fullInvariantPolynomial 6)
  funext j
  change sexticToParameter (X j) = incidencePoint (Sum.inr (Sum.inl j))
  rw [sexticToParameter_X, incidence_sextic_fixed]

def universalAmbientToBase := weightedThreefoldToBase universalPoint

/-- The fixed complex fibre with all independent sextic coefficients at
their literal seed values. -/
abbrev FixedThreefold := pullback seedSextic universalAmbientToBase

def originalToAmbient (t : Fin 3 → ℂ) :
    relativeCurve incidencePoint t ⟶ weightedThreefold universalPoint :=
  relativeCurveToSurface incidencePoint t ≫ surfaceToThreefold incidencePoint ≫
    CycleQ2ThreefoldCoefficientMap.morphism sexticToParameter universalPoint incidencePoint
      universal_to_incidence

theorem original_over_coefficients (t : Fin 3 → ℂ) :
    originalToAmbient t ≫ universalAmbientToBase =
      relativeCurveToBase incidencePoint t ≫ parameterToSextics := by
  simp only [originalToAmbient, universalAmbientToBase, relativeCurveToBase,
    Category.assoc, CycleQ2ThreefoldCoefficientMap.morphism_overBase]
  rw [← Category.assoc (surfaceToThreefold incidencePoint), surfaceToThreefold_toBase]
  rfl

/-- The second correspondence projection. The first is the actual proper
section family projection `toCurve t`. -/
def toFixedThreefold (t : Fin 3 → ℂ) : Family t ⟶ FixedThreefold :=
  pullback.lift (toCurve t ≫ toComplex) (toOriginal t ≫ originalToAmbient t) <| by
    rw [Category.assoc, Category.assoc, original_over_coefficients]
    change toCurve t ≫ (pullback.fst seedSextic parameterToSextics ≫ seedSextic) = _
    rw [pullback.condition, ← Category.assoc, ← Category.assoc]
    exact congrArg (fun f => f ≫ parameterToSextics)
      (pullback.condition (f := toIncidence) (g := relativeCurveToBase incidencePoint t))

@[reassoc, simp] theorem toFixedThreefold_overComplex (t : Fin 3 → ℂ) :
    toFixedThreefold t ≫ pullback.fst seedSextic universalAmbientToBase = toCurve t ≫ toComplex :=
  pullback.lift_fst _ _ _

@[reassoc, simp] theorem toFixedThreefold_original (t : Fin 3 → ℂ) :
    toFixedThreefold t ≫ pullback.snd seedSextic universalAmbientToBase =
      toOriginal t ≫ originalToAmbient t := pullback.lift_snd _ _ _

end CycleQ2LiteralIncidenceCylinderMap
end

#print axioms CycleQ2LiteralIncidenceCylinderMap.toFixedThreefold_original
#print axioms CycleQ2LiteralIncidenceCylinderMap.toFixedThreefold_overComplex
