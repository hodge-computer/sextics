import Proposal.GeometricLiteralNativeGaugeNaturality
import Proposal.GeometricLiteralCartierCupClass

/-!
# The original four cone cup faces under the actual intersection maps

The closed transport carries the existing original contractionOn to the
ordinary contraction with the transported original unit and the same
chosen splittings. On the actual refined 012 and 013 faces, the cone
cup in the frame-gauge identity is exactly the projection of those
original representatives. The original 023 and 123 entries remain zero.
All maps are the original coordinate-preserving localization maps.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralNativeCupOriginalFaces

open CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionProjection
  CycleQ2LiteralProjectiveIntersectionSplittings CycleQ2LiteralConeIntersectionTransport
  CycleQ2LiteralIntersectionEpsilonTransport CycleQ2LiteralIntersectionSplittingTransport
  CycleQ2LiteralIntersectionCorrectionTransport CycleQ2LiteralNativeTransitionUnits
  CycleQ2LiteralNativeFrameGauge CycleQ2LiteralNativeCupFrameGauge
  CycleQ2LiteralCartierLiftedTransitions CycleQ2GeometricSquareZeroSplittings

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

theorem transported_contractionOn (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t)
    (a b : Fin 4) (ha : a ∈ t) (hb : b ∈ t) (u : (OldThick t)ˣ) :
    closedMap s t ht (CycleQ2LiteralCartierCupClass.contractionOn t a b ha hb u) =
      (ordinaryKodairaSpencer s a b (ht a ha) (ht b hb)).liftKaehlerDifferential
        (logDifferential (K := ℂ) (reducedUnit (C := ClosedCone s) (transportedUnit s t ht u))) := by
  have ho : CycleQ2LiteralCartierCupClass.contractionOn t a b ha hb u =
      unitCorrection (CycleQ2LiteralCartierSplittings.kernelEquiv t)
        (CycleQ2LiteralCartierKodairaSpencer.splittingOn a t ha)
        (CycleQ2LiteralCartierKodairaSpencer.splittingOn_reduction a t ha) u -
      unitCorrection (CycleQ2LiteralCartierSplittings.kernelEquiv t)
        (CycleQ2LiteralCartierKodairaSpencer.splittingOn b t hb)
        (CycleQ2LiteralCartierKodairaSpencer.splittingOn_reduction b t hb) u :=
    (unitCorrection_change (CycleQ2LiteralCartierSplittings.kernelEquiv t)
      (CycleQ2LiteralCartierKodairaSpencer.splittingOn a t ha)
      (CycleQ2LiteralCartierKodairaSpencer.splittingOn b t hb)
      (CycleQ2LiteralCartierKodairaSpencer.splittingOn_reduction a t ha)
      (CycleQ2LiteralCartierKodairaSpencer.splittingOn_reduction b t hb) u).symm
  rw [ho, map_sub, ordinaryCorrection_transport, ordinaryCorrection_transport]
  exact unitCorrection_change (ordinaryKernelEquiv s)
    (ordinarySplittingAlgHom s a (ht a ha)) (ordinarySplittingAlgHom s b (ht b hb))
    (ordinarySplittingAlgHom_reduction s a (ht a ha)) (ordinarySplittingAlgHom_reduction s b (ht b hb))
    (transportedUnit s t ht u)

theorem transportedUnit_restrict_source (s : Finset Vertex) {p t : Finset (Fin 4)}
    (hpt : p ⊆ t) (ht : Admits s t) (u : (OldThick p)ˣ) :
    transportedUnit s t ht (CycleQ2LiteralCartierCochainNaturality.restrictUnit hpt u) =
      transportedUnit s p (admits_subset hpt ht) u := by
  apply Units.ext
  exact thickMap_restrict_source s hpt ht (u : OldThick p)

theorem admits_triple (s : Finset Vertex) (u v w : Vertex) (hu : u ∈ s) (hv : v ∈ s) (hw : w ∈ s) :
    Admits s {u.1,v.1,w.1} := by
  intro a ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl
  · exact ⟨u.2,hu⟩
  · exact ⟨v.2,hv⟩
  · exact ⟨w.2,hw⟩

theorem projectedConeCup_original012 (s : Finset Vertex) (l m n : Fin 3)
    (hu : (0,l) ∈ s) (hv : (1,m) ∈ s) (hw : (2,n) ∈ s) :
    projectedConeCup s (0,l) (1,m) (2,n) hu hv hw =
      closedProjection s (closedMap s {0,1,2} (admits_triple s (0,l) (1,m) (2,n) hu hv hw)
        (CycleQ2LiteralCartierCupClass.contractionOn {0,1,2} 0 1 (by simp) (by simp)
          (CycleQ2LiteralCartierCochainNaturality.restrictUnit (s := {1,2}) (t := {0,1,2}) (by decide) lifted12))) := by
  rw [transported_contractionOn]
  rw [transportedUnit_restrict_source]
  rfl

theorem projectedConeCup_original013 (s : Finset Vertex) (l m n : Fin 3)
    (hu : (0,l) ∈ s) (hv : (1,m) ∈ s) (hw : (3,n) ∈ s) :
    projectedConeCup s (0,l) (1,m) (3,n) hu hv hw =
      closedProjection s (closedMap s {0,1,3} (admits_triple s (0,l) (1,m) (3,n) hu hv hw)
        (CycleQ2LiteralCartierCupClass.contractionOn {0,1,3} 0 1 (by simp) (by simp)
          (CycleQ2LiteralCartierCochainNaturality.restrictUnit (s := {1,3}) (t := {0,1,3}) (by decide) lifted13))) := by
  rw [transported_contractionOn]
  rw [transportedUnit_restrict_source]
  rfl

theorem coneTransition23 (s : Finset Vertex) (m n : Fin 3)
    (hv : (2,m) ∈ s) (hw : (3,n) ∈ s) : coneTransition s (2,m) (3,n) hv hw = 1 := by
  change Units.map (thickMap s {2,3} (admits_pair s (2,m) (3,n) hv hw)).toMonoidHom 1 = 1
  exact map_one _

theorem projectedConeCup_original023 (s : Finset Vertex) (l m n : Fin 3)
    (hu : (0,l) ∈ s) (hv : (2,m) ∈ s) (hw : (3,n) ∈ s) :
    projectedConeCup s (0,l) (2,m) (3,n) hu hv hw = 0 := by
  rw [projectedConeCup_corrections]
  have hz (a : Fin 4) (ha : Admissible s a) : ordinaryCorrection s a ha 1 = 0 :=
    unitCorrection_one (ordinaryKernelEquiv s) (ordinarySplittingAlgHom s a ha)
      (ordinarySplittingAlgHom_reduction s a ha)
  simp only [coneTransition23, hz, map_zero, sub_self]

theorem projectedConeCup_original123 (s : Finset Vertex) (l m n : Fin 3)
    (hu : (1,l) ∈ s) (hv : (2,m) ∈ s) (hw : (3,n) ∈ s) :
    projectedConeCup s (1,l) (2,m) (3,n) hu hv hw = 0 := by
  rw [projectedConeCup_corrections]
  have hz (a : Fin 4) (ha : Admissible s a) : ordinaryCorrection s a ha 1 = 0 :=
    unitCorrection_one (ordinaryKernelEquiv s) (ordinarySplittingAlgHom s a ha)
      (ordinarySplittingAlgHom_reduction s a ha)
  simp only [coneTransition23, hz, map_zero, sub_self]

end CycleQ2LiteralNativeCupOriginalFaces

end

#print axioms CycleQ2LiteralNativeCupOriginalFaces.transported_contractionOn
#print axioms CycleQ2LiteralNativeCupOriginalFaces.projectedConeCup_original012
#print axioms CycleQ2LiteralNativeCupOriginalFaces.projectedConeCup_original013
#print axioms CycleQ2LiteralNativeCupOriginalFaces.projectedConeCup_original023
#print axioms CycleQ2LiteralNativeCupOriginalFaces.projectedConeCup_original123
