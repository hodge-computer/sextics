import Proposal.GeometricLiteralIntersectionSplittingTransport

/-!
# Transport and projection of the original transition corrections

The actual unit-correction coefficients use the actual epsilon kernels
and the same original chosen splittings. Transport of an original cone
correction is the ordinary intersection correction of its transported
unit. For a native unit, projection of that ordinary correction is the
native correction. No homogeneous property is assumed for the chosen
ordinary splitting.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralIntersectionCorrectionTransport

open HomogeneousLocalization CycleQ2LiteralGradedDeformation CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveIntersectionKernel CycleQ2LiteralProjectiveIntersectionProjection
  CycleQ2LiteralProjectiveIntersectionRestrictions CycleQ2LiteralProjectiveIntersectionSplittings
  CycleQ2LiteralProjectiveIntersectionComplex CycleQ2LiteralConeIntersectionTransport
  CycleQ2LiteralIntersectionEpsilonTransport CycleQ2LiteralIntersectionSplittingTransport
  CycleQ2LiteralNativeTransitionUnits CycleQ2GeometricSquareZeroSplittings

attribute [local instance] CycleQ2LiteralCartierTransitionBinding.cubicSelfModule
  CycleQ2LiteralCartierTransitionBinding.cubicOppositeModule
  CycleQ2LiteralCartierTransitionBinding.cubicCentralScalar
  CycleQ2LiteralCartierTransitionBinding.cubicSmulCommClass
  CycleQ2GeometricSurfaceFirstOrder.reducedAlgebra
  CycleQ2GeometricKernelLocalization.localReductionAlgebra
  CycleQ2LiteralCartierSplittings.complexReductionTower
  CycleQ2LiteralCartierOverlapSplittings.baseReductionAlgebra
  CycleQ2LiteralIntersectionEpsilonTransport.ordinaryReductionAlgebra
  CycleQ2LiteralIntersectionSplittingTransport.ordinaryComplexReductionTower
  CycleQ2LiteralProjectiveIntersectionKernel.nativeReductionAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.complexReductionTower

def ordinaryCorrection (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) (u : (ThickCone s)ˣ) : ClosedCone s :=
  unitCorrection (ordinaryKernelEquiv s) (ordinarySplittingAlgHom s a ha)
    (ordinarySplittingAlgHom_reduction s a ha) u

def nativeCorrection (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) (u : (ThickRing s)ˣ) : ClosedRing s :=
  unitCorrection (epsilonKernelEquiv s) (projectiveSplittingAlgHom s a ha)
    (projectiveSplittingAlgHom_reduction s a ha) u

theorem ordinaryCorrection_epsilon (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) (u : (ThickCone s)ˣ) :
    ordinaryCoefficient s (ordinaryCorrection s a ha u) = normalizedUnitValue (ordinarySplittingAlgHom s a ha) u - 1 :=
  epsilon_unitCorrection (ordinaryKernelEquiv s) (ordinarySplittingAlgHom s a ha)
    (ordinarySplittingAlgHom_reduction s a ha) u

theorem nativeCorrection_epsilon (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) (u : (ThickRing s)ˣ) :
    epsilonCoefficient s (nativeCorrection s a ha u) = normalizedUnitValue (projectiveSplittingAlgHom s a ha) u - 1 :=
  epsilon_unitCorrection (epsilonKernelEquiv s) (projectiveSplittingAlgHom s a ha)
    (projectiveSplittingAlgHom_reduction s a ha) u

theorem ordinaryCorrection_mul (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) (u v : (ThickCone s)ˣ) :
    ordinaryCorrection s a ha (u * v) = ordinaryCorrection s a ha u + ordinaryCorrection s a ha v :=
  unitCorrection_mul (ordinaryKernelEquiv s) (ordinarySplittingAlgHom s a ha)
    (ordinarySplittingAlgHom_reduction s a ha) u v

theorem ordinaryCorrection_pow (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) (u : (ThickCone s)ˣ) (n : ℕ) :
    ordinaryCorrection s a ha (u ^ n) = n • ordinaryCorrection s a ha u := by
  induction n with
  | zero =>
    rw [pow_zero, zero_nsmul]
    exact unitCorrection_one (ordinaryKernelEquiv s) (ordinarySplittingAlgHom s a ha)
      (ordinarySplittingAlgHom_reduction s a ha)
  | succ n ih =>
    rw [pow_succ, ordinaryCorrection_mul, ih, add_nsmul, one_nsmul]

theorem transported_reducedUnit (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t) (u : (OldThick t)ˣ) :
    Units.map (closedMap s t ht).toMonoidHom (reducedUnit (C := OldClosed t) u) =
      reducedUnit (C := ClosedCone s) (transportedUnit s t ht u) := by
  apply Units.ext
  exact (reduction_thickMap s t ht (u : OldThick t)).symm

theorem transported_reducedUnit_inverse (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t) (u : (OldThick t)ˣ) :
    closedMap s t ht (↑((reducedUnit (C := OldClosed t) u)⁻¹) : OldClosed t) =
      (↑((reducedUnit (C := ClosedCone s) (transportedUnit s t ht u))⁻¹) : ClosedCone s) :=
  congrArg (fun v : (ClosedCone s)ˣ => (↑(v⁻¹) : ClosedCone s)) (transported_reducedUnit s t ht u)

theorem normalizedUnitValue_transport (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t)
    (a : Fin 4) (ha : a ∈ t) (u : (OldThick t)ˣ) :
    thickMap s t ht (normalizedUnitValue (CycleQ2LiteralCartierKodairaSpencer.splittingOn a t ha) u) =
      normalizedUnitValue (ordinarySplittingAlgHom s a (ht a ha)) (transportedUnit s t ht u) := by
  unfold normalizedUnitValue
  rw [map_mul, transported_splitting, transported_reducedUnit_inverse]
  rfl

theorem ordinaryCorrection_transport (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t)
    (a : Fin 4) (ha : a ∈ t) (u : (OldThick t)ˣ) :
    closedMap s t ht (unitCorrection (CycleQ2LiteralCartierSplittings.kernelEquiv t)
      (CycleQ2LiteralCartierKodairaSpencer.splittingOn a t ha)
      (CycleQ2LiteralCartierKodairaSpencer.splittingOn_reduction a t ha) u) =
      ordinaryCorrection s a (ht a ha) (transportedUnit s t ht u) := by
  apply ordinaryCoefficient_injective s
  rw [← transported_epsilon, epsilon_unitCorrection, ordinaryCorrection_epsilon,
    map_sub, map_one, normalizedUnitValue_transport]

def closedValueUnit (s : Finset Vertex) : (ClosedRing s)ˣ →* (ClosedCone s)ˣ :=
  Units.map (algebraMap (ClosedRing s) (ClosedCone s)).toMonoidHom

theorem ordinary_reducedUnit_valueUnit (s : Finset Vertex) (u : (ThickRing s)ˣ) :
    reducedUnit (C := ClosedCone s) (valueUnit s u) =
      closedValueUnit s (reducedUnit (C := ClosedRing s) u) := by
  apply Units.ext
  exact ordinaryReduction_val s (u : ThickRing s)

theorem ordinary_reducedUnit_valueUnit_inverse (s : Finset Vertex) (u : (ThickRing s)ˣ) :
    (↑((reducedUnit (C := ClosedCone s) (valueUnit s u))⁻¹) : ClosedCone s) =
      ((↑((reducedUnit (C := ClosedRing s) u)⁻¹) : ClosedRing s)).val := by
  rw [ordinary_reducedUnit_valueUnit]
  rfl

theorem projection_normalizedUnitValue (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) (u : (ThickRing s)ˣ) :
    thickProjection s (normalizedUnitValue (ordinarySplittingAlgHom s a ha) (valueUnit s u)) =
      normalizedUnitValue (projectiveSplittingAlgHom s a ha) u := by
  unfold normalizedUnitValue
  rw [valueUnit_value, ordinary_reducedUnit_valueUnit_inverse]
  exact CycleQ2GradedLocalizationProjection.degreeZero_mul_homogeneous deformationGrade
    (thickProduct_homogeneous s) (u : ThickRing s) _

theorem nativeCorrection_projected (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) (u : (ThickRing s)ˣ) :
    nativeCorrection s a ha u = closedProjection s (ordinaryCorrection s a ha (valueUnit s u)) := by
  apply epsilonCoefficient_injective s
  rw [nativeCorrection_epsilon, ← projection_ordinaryCoefficient, ordinaryCorrection_epsilon,
    map_sub, projection_normalizedUnitValue]
  have h : thickProjection s (1 : ThickCone s) = 1 := by
    simpa only [val_one] using thickProjection_val s 1
  rw [h]

end CycleQ2LiteralIntersectionCorrectionTransport

end

#print axioms CycleQ2LiteralIntersectionCorrectionTransport.ordinaryCorrection_transport
#print axioms CycleQ2LiteralIntersectionCorrectionTransport.projection_normalizedUnitValue
#print axioms CycleQ2LiteralIntersectionCorrectionTransport.nativeCorrection_projected
