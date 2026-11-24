import Proposal.GeometricLiteralIntersectionCorrectionTransport

/-!
# The original coordinate frame-gauge correction

The actual native transition lift and the transported original cone unit
satisfy the original coordinate-power identity on every oriented pair.
The genuine unit-correction maps therefore give the precise native
correction = projected cone correction + coordinate frame gauge identity.
Coordinate errors retain the actual ordinary splitting and epsilon kernel.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralNativeFrameGauge

open HomogeneousLocalization CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveIntersectionProjection CycleQ2LiteralProjectiveIntersectionSplittings
  CycleQ2LiteralProjectiveIntersectionComplex CycleQ2LiteralConeIntersectionTransport
  CycleQ2LiteralIntersectionEpsilonTransport CycleQ2LiteralIntersectionSplittingTransport
  CycleQ2LiteralIntersectionCorrectionTransport CycleQ2LiteralNativeHomogeneousFractions
  CycleQ2LiteralNativeTransitionUnits CycleQ2LiteralNativeCartierTransitions
  CycleQ2LiteralCartierLiftedTransitions CycleQ2GeometricSquareZeroSplittings

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

def frameDegree : Fin 4 → ℕ := ![2,2,0,0]

def coneTransition (s : Finset Vertex) (v w : Vertex) (hv : v ∈ s) (hw : w ∈ s) : (ThickCone s)ˣ := by
  rcases v with ⟨a,l⟩
  rcases w with ⟨b,m⟩
  refine CycleQ2FourToFiniteCech.fourCases
    (P := fun a => ∀ b : Fin 4, (a,l) ∈ s → (b,m) ∈ s → (ThickCone s)ˣ)
    ?_ ?_ ?_ ?_ a b hv hw
  · intro b
    refine CycleQ2FourToFiniteCech.fourCases
      (P := fun b => (0,l) ∈ s → (b,m) ∈ s → (ThickCone s)ˣ) ?_ ?_ ?_ ?_ b
    · intro hv hw
      exact 1
    · intro hv hw
      exact transportedUnit s {0,1} (admits_pair s (0,l) (1,m) hv hw) lifted01
    · intro hv hw
      exact transportedUnit s {0,2} (admits_pair s (0,l) (2,m) hv hw) lifted02
    · intro hv hw
      exact transportedUnit s {0,3} (admits_pair s (0,l) (3,m) hv hw) lifted03
  · intro b
    refine CycleQ2FourToFiniteCech.fourCases
      (P := fun b => (1,l) ∈ s → (b,m) ∈ s → (ThickCone s)ˣ) ?_ ?_ ?_ ?_ b
    · intro hv hw
      exact (transportedUnit s {0,1} (admits_pair s (0,m) (1,l) hw hv) lifted01)⁻¹
    · intro hv hw
      exact 1
    · intro hv hw
      exact transportedUnit s {1,2} (admits_pair s (1,l) (2,m) hv hw) lifted12
    · intro hv hw
      exact transportedUnit s {1,3} (admits_pair s (1,l) (3,m) hv hw) lifted13
  · intro b
    refine CycleQ2FourToFiniteCech.fourCases
      (P := fun b => (2,l) ∈ s → (b,m) ∈ s → (ThickCone s)ˣ) ?_ ?_ ?_ ?_ b
    · intro hv hw
      exact (transportedUnit s {0,2} (admits_pair s (0,m) (2,l) hw hv) lifted02)⁻¹
    · intro hv hw
      exact (transportedUnit s {1,2} (admits_pair s (1,m) (2,l) hw hv) lifted12)⁻¹
    · intro hv hw
      exact 1
    · intro hv hw
      exact transportedUnit s {2,3} (admits_pair s (2,l) (3,m) hv hw) lifted23
  · intro b
    refine CycleQ2FourToFiniteCech.fourCases
      (P := fun b => (3,l) ∈ s → (b,m) ∈ s → (ThickCone s)ˣ) ?_ ?_ ?_ ?_ b
    · intro hv hw
      exact (transportedUnit s {0,3} (admits_pair s (0,m) (3,l) hw hv) lifted03)⁻¹
    · intro hv hw
      exact (transportedUnit s {1,3} (admits_pair s (1,m) (3,l) hw hv) lifted13)⁻¹
    · intro hv hw
      exact (transportedUnit s {2,3} (admits_pair s (2,m) (3,l) hw hv) lifted23)⁻¹
    · intro hv hw
      exact 1

theorem inverse_frame_relation {G : Type*} [CommGroup G] (u t x y : G) (h : u * x = t * y) :
    u⁻¹ * y = t⁻¹ * x := by
  apply mul_right_injective u
  calc
    u * (u⁻¹ * y) = y := by rw [← mul_assoc, mul_inv_cancel, one_mul]
    _ = t⁻¹ * (t * y) := (inv_mul_cancel_left t y).symm
    _ = t⁻¹ * (u * x) := congrArg (fun z => t⁻¹ * z) h.symm
    _ = u * (t⁻¹ * x) := by ac_rfl

theorem nativeTransition_coordinate_formula (s : Finset Vertex) (v w : Vertex) (hv : v ∈ s) (hw : w ∈ s) :
    valueUnit s (nativeTransition s v w hv hw) * coordinateUnit s v hv ^ frameDegree v.1 =
      coneTransition s v w hv hw * coordinateUnit s w hw ^ frameDegree w.1 := by
  rcases v with ⟨a,l⟩
  rcases w with ⟨b,m⟩
  fin_cases a <;> fin_cases b
  · change valueUnit s (coordinateRatio s (0,l) (0,m) hv hw ^ 2) * coordinateUnit s (0,l) hv ^ 2 =
      (1) * coordinateUnit s (0,m) hw ^ 2
    rw [map_pow, ← mul_pow, coordinateRatio_mul, one_mul]
  · change valueUnit s (native01 s l m hv hw) * coordinateUnit s (0,l) hv ^ 2 =
      (transportedUnit s {0,1} (admits_pair s (0,l) (1,m) hv hw) lifted01) * coordinateUnit s (1,m) hw ^ 2
    exact native01_mul s l m hv hw
  · change valueUnit s (native02 s l m hv hw) * coordinateUnit s (0,l) hv ^ 2 =
      (transportedUnit s {0,2} (admits_pair s (0,l) (2,m) hv hw) lifted02) * coordinateUnit s (2,m) hw ^ 0
    simpa only [pow_zero, mul_one] using native02_mul s l m hv hw
  · change valueUnit s (native03 s l m hv hw) * coordinateUnit s (0,l) hv ^ 2 =
      (transportedUnit s {0,3} (admits_pair s (0,l) (3,m) hv hw) lifted03) * coordinateUnit s (3,m) hw ^ 0
    simpa only [pow_zero, mul_one] using native03_mul s l m hv hw
  · change valueUnit s ((native01 s m l hw hv)⁻¹) * coordinateUnit s (1,l) hv ^ 2 =
      ((transportedUnit s {0,1} (admits_pair s (0,m) (1,l) hw hv) lifted01)⁻¹) * coordinateUnit s (0,m) hw ^ 2
    rw [map_inv]
    apply inverse_frame_relation
    exact native01_mul s m l hw hv
  · change valueUnit s (coordinateRatio s (1,l) (1,m) hv hw ^ 2) * coordinateUnit s (1,l) hv ^ 2 =
      (1) * coordinateUnit s (1,m) hw ^ 2
    rw [map_pow, ← mul_pow, coordinateRatio_mul, one_mul]
  · change valueUnit s (native12 s l m hv hw) * coordinateUnit s (1,l) hv ^ 2 =
      (transportedUnit s {1,2} (admits_pair s (1,l) (2,m) hv hw) lifted12) * coordinateUnit s (2,m) hw ^ 0
    simpa only [pow_zero, mul_one] using native12_mul s l m hv hw
  · change valueUnit s (native13 s l m hv hw) * coordinateUnit s (1,l) hv ^ 2 =
      (transportedUnit s {1,3} (admits_pair s (1,l) (3,m) hv hw) lifted13) * coordinateUnit s (3,m) hw ^ 0
    simpa only [pow_zero, mul_one] using native13_mul s l m hv hw
  · change valueUnit s ((native02 s m l hw hv)⁻¹) * coordinateUnit s (2,l) hv ^ 0 =
      ((transportedUnit s {0,2} (admits_pair s (0,m) (2,l) hw hv) lifted02)⁻¹) * coordinateUnit s (0,m) hw ^ 2
    rw [map_inv]
    apply inverse_frame_relation
    simpa only [pow_zero, mul_one] using native02_mul s m l hw hv
  · change valueUnit s ((native12 s m l hw hv)⁻¹) * coordinateUnit s (2,l) hv ^ 0 =
      ((transportedUnit s {1,2} (admits_pair s (1,m) (2,l) hw hv) lifted12)⁻¹) * coordinateUnit s (1,m) hw ^ 2
    rw [map_inv]
    apply inverse_frame_relation
    simpa only [pow_zero, mul_one] using native12_mul s m l hw hv
  · change valueUnit s (1) * coordinateUnit s (2,l) hv ^ 0 =
      (1) * coordinateUnit s (2,m) hw ^ 0
    rw [map_one, pow_zero, pow_zero, mul_one]
  · change valueUnit s (native23 s) * coordinateUnit s (2,l) hv ^ 0 =
      (transportedUnit s {2,3} (admits_pair s (2,l) (3,m) hv hw) lifted23) * coordinateUnit s (3,m) hw ^ 0
    simpa only [pow_zero, mul_one] using native23_value s l m hv hw
  · change valueUnit s ((native03 s m l hw hv)⁻¹) * coordinateUnit s (3,l) hv ^ 0 =
      ((transportedUnit s {0,3} (admits_pair s (0,m) (3,l) hw hv) lifted03)⁻¹) * coordinateUnit s (0,m) hw ^ 2
    rw [map_inv]
    apply inverse_frame_relation
    simpa only [pow_zero, mul_one] using native03_mul s m l hw hv
  · change valueUnit s ((native13 s m l hw hv)⁻¹) * coordinateUnit s (3,l) hv ^ 0 =
      ((transportedUnit s {1,3} (admits_pair s (1,m) (3,l) hw hv) lifted13)⁻¹) * coordinateUnit s (1,m) hw ^ 2
    rw [map_inv]
    apply inverse_frame_relation
    simpa only [pow_zero, mul_one] using native13_mul s m l hw hv
  · change valueUnit s ((native23 s)⁻¹) * coordinateUnit s (3,l) hv ^ 0 =
      ((transportedUnit s {2,3} (admits_pair s (2,m) (3,l) hw hv) lifted23)⁻¹) * coordinateUnit s (2,m) hw ^ 0
    rw [map_inv]
    apply inverse_frame_relation
    simpa only [pow_zero, mul_one] using native23_value s m l hw hv
  · change valueUnit s (1) * coordinateUnit s (3,l) hv ^ 0 =
      (1) * coordinateUnit s (3,m) hw ^ 0
    rw [map_one, pow_zero, pow_zero, mul_one]

def coordinateError (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a)
    (v : Vertex) (hv : v ∈ s) : ClosedRing s :=
  closedProjection s (ordinaryCorrection s a ha (coordinateUnit s v hv))

def frameGauge (s : Finset Vertex) (v w : Vertex) (hv : v ∈ s) (hw : w ∈ s) : ClosedRing s :=
  frameDegree w.1 • coordinateError s v.1 ⟨v.2,hv⟩ w hw -
    frameDegree v.1 • coordinateError s v.1 ⟨v.2,hv⟩ v hv

def projectedConeCorrection (s : Finset Vertex) (v w : Vertex) (hv : v ∈ s) (hw : w ∈ s) : ClosedRing s :=
  closedProjection s (ordinaryCorrection s v.1 ⟨v.2,hv⟩ (coneTransition s v w hv hw))

theorem nativeCorrection_coordinate_formula (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a)
    (v w : Vertex) (hv : v ∈ s) (hw : w ∈ s) :
    nativeCorrection s a ha (nativeTransition s v w hv hw) =
      closedProjection s (ordinaryCorrection s a ha (coneTransition s v w hv hw)) +
        (frameDegree w.1 • coordinateError s a ha w hw - frameDegree v.1 • coordinateError s a ha v hv) := by
  have h := congrArg (ordinaryCorrection s a ha)
    (nativeTransition_coordinate_formula s v w hv hw)
  rw [ordinaryCorrection_mul, ordinaryCorrection_mul, ordinaryCorrection_pow, ordinaryCorrection_pow] at h
  have hp := congrArg (closedProjection s) h
  rw [map_add, map_add, map_nsmul, map_nsmul, ← nativeCorrection_projected] at hp
  change nativeCorrection s a ha (nativeTransition s v w hv hw) =
    closedProjection s (ordinaryCorrection s a ha (coneTransition s v w hv hw)) +
      (frameDegree w.1 • closedProjection s (ordinaryCorrection s a ha (coordinateUnit s w hw)) -
        frameDegree v.1 • closedProjection s (ordinaryCorrection s a ha (coordinateUnit s v hv)))
  linear_combination hp

theorem nativeCorrection_frameGauge (s : Finset Vertex) (v w : Vertex) (hv : v ∈ s) (hw : w ∈ s) :
    nativeCorrection s v.1 ⟨v.2,hv⟩ (nativeTransition s v w hv hw) =
      projectedConeCorrection s v w hv hw + frameGauge s v w hv hw :=
  nativeCorrection_coordinate_formula s v.1 ⟨v.2,hv⟩ v w hv hw

theorem coneTransition_sameCartier (s : Finset Vertex) (a : Fin 4) (l m : Fin 3)
    (hv : (a,l) ∈ s) (hw : (a,m) ∈ s) : coneTransition s (a,l) (a,m) hv hw = 1 := by
  fin_cases a <;> rfl

theorem coordinateError_difference (s : Finset Vertex) (a b : Fin 4)
    (ha : Admissible s a) (hb : Admissible s b) (v : Vertex) (hv : v ∈ s) :
    coordinateError s a ha v hv - coordinateError s b hb v hv =
      closedProjection s ((ordinaryKodairaSpencer s a b ha hb).liftKaehlerDifferential
        (logDifferential (K := ℂ) (reducedUnit (C := ClosedCone s) (coordinateUnit s v hv)))) := by
  change closedProjection s (ordinaryCorrection s a ha (coordinateUnit s v hv)) -
    closedProjection s (ordinaryCorrection s b hb (coordinateUnit s v hv)) = _
  rw [← map_sub]
  exact congrArg (closedProjection s) (unitCorrection_change (ordinaryKernelEquiv s)
    (ordinarySplittingAlgHom s a ha) (ordinarySplittingAlgHom s b hb)
    (ordinarySplittingAlgHom_reduction s a ha) (ordinarySplittingAlgHom_reduction s b hb)
    (coordinateUnit s v hv))

end CycleQ2LiteralNativeFrameGauge

end

#print axioms CycleQ2LiteralNativeFrameGauge.nativeTransition_coordinate_formula
#print axioms CycleQ2LiteralNativeFrameGauge.nativeCorrection_frameGauge
#print axioms CycleQ2LiteralNativeFrameGauge.coordinateError_difference
