import Proposal.GeometricLiteralNativeCupFrameGauge

/-!
# Naturality of the original frame-gauge comparison

The ordinary correction coefficients commute with the actual product
localization restrictions. Projection gives the native correction and
coordinate-error restriction laws. The original cone transitions,
frame gauge, both actual scalar cups, and the gauge coboundary are
compatible with those same genuine structure-sheaf restrictions.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralNativeGaugeNaturality

open HomogeneousLocalization CycleQ2LiteralProjectiveDeformation CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveIntersectionProjection CycleQ2LiteralProjectiveIntersectionRestrictions
  CycleQ2LiteralProjectiveIntersectionSplittings CycleQ2LiteralProjectiveIntersectionComplex
  CycleQ2LiteralConeIntersectionTransport CycleQ2LiteralIntersectionEpsilonTransport
  CycleQ2LiteralIntersectionSplittingTransport CycleQ2LiteralIntersectionCorrectionTransport
  CycleQ2LiteralNativeHomogeneousFractions CycleQ2LiteralNativeTransitionUnits
  CycleQ2LiteralNativeCartierTransitions CycleQ2LiteralNativeTransitionNaturality
  CycleQ2LiteralNativeFrameGauge CycleQ2LiteralNativeCupFrameGauge CycleQ2GeometricSquareZeroSplittings

attribute [local instance] CycleQ2LiteralIntersectionEpsilonTransport.ordinaryReductionAlgebra
  CycleQ2LiteralIntersectionSplittingTransport.ordinaryComplexReductionTower
  CycleQ2LiteralProjectiveIntersectionKernel.nativeReductionAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.complexReductionTower

def restrictConeUnit {s t : Finset Vertex} (hst : s ⊆ t) : (ThickCone s)ˣ →* (ThickCone t)ˣ :=
  Units.map (thickConeRestriction hst).toMonoidHom

theorem ordinary_reducedUnit_restrict {s t : Finset Vertex} (hst : s ⊆ t) (u : (ThickCone s)ˣ) :
    Units.map (closedConeRestriction hst).toMonoidHom (reducedUnit (C := ClosedCone s) u) =
      reducedUnit (C := ClosedCone t) (restrictConeUnit hst u) := by
  apply Units.ext
  exact (ordinaryReduction_restrict hst (u : ThickCone s)).symm

theorem ordinary_reducedUnit_inverse_restrict {s t : Finset Vertex} (hst : s ⊆ t) (u : (ThickCone s)ˣ) :
    closedConeRestriction hst (↑((reducedUnit (C := ClosedCone s) u)⁻¹) : ClosedCone s) =
      (↑((reducedUnit (C := ClosedCone t) (restrictConeUnit hst u))⁻¹) : ClosedCone t) :=
  congrArg (fun v : (ClosedCone t)ˣ => (↑(v⁻¹) : ClosedCone t)) (ordinary_reducedUnit_restrict hst u)

theorem ordinary_normalizedUnitValue_restrict {s t : Finset Vertex} (hst : s ⊆ t)
    (a : Fin 4) (ha : Admissible s a) (u : (ThickCone s)ˣ) :
    thickConeRestriction hst (normalizedUnitValue (ordinarySplittingAlgHom s a ha) u) =
      normalizedUnitValue (ordinarySplittingAlgHom t a (admissible_mono hst ha)) (restrictConeUnit hst u) := by
  unfold normalizedUnitValue
  rw [map_mul]
  change thickConeRestriction hst (u : ThickCone s) *
    thickConeRestriction hst (ordinarySplitting s a ha _) = _
  rw [ordinarySplitting_restrict, ordinary_reducedUnit_inverse_restrict]
  rfl

theorem ordinaryCorrection_restrict {s t : Finset Vertex} (hst : s ⊆ t)
    (a : Fin 4) (ha : Admissible s a) (u : (ThickCone s)ˣ) :
    closedConeRestriction hst (ordinaryCorrection s a ha u) =
      ordinaryCorrection t a (admissible_mono hst ha) (restrictConeUnit hst u) := by
  apply ordinaryCoefficient_injective t
  rw [← ordinaryCoefficient_restrict, ordinaryCorrection_epsilon, map_sub, map_one,
    ordinary_normalizedUnitValue_restrict, ordinaryCorrection_epsilon]

theorem projectedCorrection_restrict {s t : Finset Vertex} (hst : s ⊆ t)
    (a : Fin 4) (ha : Admissible s a) (u : (ThickCone s)ˣ) :
    closedRestriction hst (closedProjection s (ordinaryCorrection s a ha u)) =
      closedProjection t (ordinaryCorrection t a (admissible_mono hst ha) (restrictConeUnit hst u)) := by
  rw [← closedProjection_restrict, ordinaryCorrection_restrict]

theorem coordinateUnit_restrict {s t : Finset Vertex} (hst : s ⊆ t) (v : Vertex) (hv : v ∈ s) :
    restrictConeUnit hst (coordinateUnit s v hv) = coordinateUnit t v (hst hv) := by
  apply Units.ext
  change thickConeRestriction hst (coordinateUnit s v hv : ThickCone s) = (coordinateUnit t v (hst hv) : ThickCone t)
  rw [coordinateUnit_value, coordinateUnit_value]
  exact thickConeRestriction_base hst (coordinateElement v.2)

theorem valueUnit_restrict {s t : Finset Vertex} (hst : s ⊆ t) (u : (ThickRing s)ˣ) :
    restrictConeUnit hst (valueUnit s u) = valueUnit t (restrictThickUnit hst u) := by
  apply Units.ext
  exact (thickRestriction_val hst (u : ThickRing s)).symm

theorem nativeCorrection_restrict {s t : Finset Vertex} (hst : s ⊆ t)
    (a : Fin 4) (ha : Admissible s a) (u : (ThickRing s)ˣ) :
    closedRestriction hst (nativeCorrection s a ha u) =
      nativeCorrection t a (admissible_mono hst ha) (restrictThickUnit hst u) := by
  rw [nativeCorrection_projected, nativeCorrection_projected, projectedCorrection_restrict, valueUnit_restrict]

theorem coordinateError_restrict {s t : Finset Vertex} (hst : s ⊆ t)
    (a : Fin 4) (ha : Admissible s a) (v : Vertex) (hv : v ∈ s) :
    closedRestriction hst (coordinateError s a ha v hv) =
      coordinateError t a (admissible_mono hst ha) v (hst hv) := by
  change closedRestriction hst (closedProjection s (ordinaryCorrection s a ha (coordinateUnit s v hv))) = _
  rw [projectedCorrection_restrict, coordinateUnit_restrict]
  rfl

theorem coneTransition_restrict {s t : Finset Vertex} (hst : s ⊆ t)
    (v w : Vertex) (hv : v ∈ s) (hw : w ∈ s) :
    restrictConeUnit hst (coneTransition s v w hv hw) = coneTransition t v w (hst hv) (hst hw) := by
  apply mul_left_injective (coordinateUnit t w (hst hw) ^ frameDegree w.1)
  have h := congrArg (restrictConeUnit hst) (nativeTransition_coordinate_formula s v w hv hw)
  rw [map_mul, map_mul, map_pow, map_pow, valueUnit_restrict,
    coordinateUnit_restrict, coordinateUnit_restrict, nativeTransition_restrict] at h
  exact h.symm.trans (nativeTransition_coordinate_formula t v w (hst hv) (hst hw))

theorem frameGauge_restrict {s t : Finset Vertex} (hst : s ⊆ t)
    (v w : Vertex) (hv : v ∈ s) (hw : w ∈ s) :
    closedRestriction hst (frameGauge s v w hv hw) = frameGauge t v w (hst hv) (hst hw) := by
  change closedRestriction hst (frameDegree w.1 • coordinateError s v.1 ⟨v.2,hv⟩ w hw -
    frameDegree v.1 • coordinateError s v.1 ⟨v.2,hv⟩ v hv) = _
  rw [map_sub, map_nsmul, map_nsmul, coordinateError_restrict, coordinateError_restrict]
  rfl

theorem projectedConeCorrection_restrict {s t : Finset Vertex} (hst : s ⊆ t)
    (v w : Vertex) (hv : v ∈ s) (hw : w ∈ s) :
    closedRestriction hst (projectedConeCorrection s v w hv hw) = projectedConeCorrection t v w (hst hv) (hst hw) := by
  change closedRestriction hst (closedProjection s (ordinaryCorrection s v.1 ⟨v.2,hv⟩ (coneTransition s v w hv hw))) = _
  rw [projectedCorrection_restrict, coneTransition_restrict]
  rfl

theorem nativeCup_restrict {s t : Finset Vertex} (hst : s ⊆ t)
    (u v w : Vertex) (hu : u ∈ s) (hv : v ∈ s) (hw : w ∈ s) :
    closedRestriction hst (nativeCup s u v w hu hv hw) = nativeCup t u v w (hst hu) (hst hv) (hst hw) := by
  rw [nativeCup_corrections, map_sub, nativeCorrection_restrict, nativeCorrection_restrict,
    nativeTransition_restrict, nativeCup_corrections]

theorem projectedConeCup_restrict {s t : Finset Vertex} (hst : s ⊆ t)
    (u v w : Vertex) (hu : u ∈ s) (hv : v ∈ s) (hw : w ∈ s) :
    closedRestriction hst (projectedConeCup s u v w hu hv hw) =
      projectedConeCup t u v w (hst hu) (hst hv) (hst hw) := by
  rw [projectedConeCup_corrections, map_sub, projectedCorrection_restrict, projectedCorrection_restrict,
    coneTransition_restrict, projectedConeCup_corrections]

theorem frameGaugeBoundary_restrict {s t : Finset Vertex} (hst : s ⊆ t)
    (u v w : Vertex) (hu : u ∈ s) (hv : v ∈ s) (hw : w ∈ s) :
    closedRestriction hst (frameGaugeBoundary s u v w hu hv hw) =
      frameGaugeBoundary t u v w (hst hu) (hst hv) (hst hw) := by
  change closedRestriction hst (frameGauge s v w hv hw - frameGauge s u w hu hw + frameGauge s u v hu hv) = _
  rw [map_add, map_sub, frameGauge_restrict, frameGauge_restrict, frameGauge_restrict]
  rfl

end CycleQ2LiteralNativeGaugeNaturality

end

#print axioms CycleQ2LiteralNativeGaugeNaturality.ordinaryCorrection_restrict
#print axioms CycleQ2LiteralNativeGaugeNaturality.coneTransition_restrict
#print axioms CycleQ2LiteralNativeGaugeNaturality.nativeCup_restrict
#print axioms CycleQ2LiteralNativeGaugeNaturality.projectedConeCup_restrict
#print axioms CycleQ2LiteralNativeGaugeNaturality.frameGaugeBoundary_restrict
