import Proposal.GeometricLiteralNativeFrameGauge

/-!
# The native Chern/KS contraction and its original frame gauge

The native scalar cup evaluates the already constructed native splitting
difference on the universal dlog of the actual inverse-ideal transition.
The projected cone cup uses the same original ordinary splitting choices
and the transported original cone transition. Their difference is the
explicit coordinate frame-gauge coboundary. Repeated original Cartier
indices are retained, rather than forced to give zero native cups.

These are actual local representatives. The global differential-sheaf
class comparison remains a further binding through the original sheaves.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralNativeCupFrameGauge

open CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionKernel
  CycleQ2LiteralProjectiveIntersectionProjection CycleQ2LiteralProjectiveIntersectionSplittings
  CycleQ2LiteralProjectiveIntersectionComplex CycleQ2LiteralIntersectionEpsilonTransport
  CycleQ2LiteralIntersectionSplittingTransport CycleQ2LiteralIntersectionCorrectionTransport
  CycleQ2LiteralNativeCartierTransitions CycleQ2LiteralNativeFrameGauge
  CycleQ2GeometricSquareZeroSplittings

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

def nativeCup (s : Finset Vertex) (u v w : Vertex) (hu : u ∈ s) (hv : v ∈ s) (hw : w ∈ s) : ClosedRing s :=
  (CycleQ2LiteralNativeKodairaSpencer.vertexKodairaSpencer s u v hu hv).liftKaehlerDifferential
    (logDifferential (K := ℂ) (transition s v w hv hw))

def projectedConeCup (s : Finset Vertex) (u v w : Vertex) (hu : u ∈ s) (hv : v ∈ s) (hw : w ∈ s) : ClosedRing s :=
  closedProjection s ((ordinaryKodairaSpencer s u.1 v.1 ⟨u.2,hu⟩ ⟨v.2,hv⟩).liftKaehlerDifferential
    (logDifferential (K := ℂ) (reducedUnit (C := ClosedCone s) (coneTransition s v w hv hw))))

def frameGaugeBoundary (s : Finset Vertex) (u v w : Vertex) (hu : u ∈ s) (hv : v ∈ s) (hw : w ∈ s) : ClosedRing s :=
  frameGauge s v w hv hw - frameGauge s u w hu hw + frameGauge s u v hu hv

theorem nativeCup_corrections (s : Finset Vertex) (u v w : Vertex) (hu : u ∈ s) (hv : v ∈ s) (hw : w ∈ s) :
    nativeCup s u v w hu hv hw = nativeCorrection s u.1 ⟨u.2,hu⟩ (nativeTransition s v w hv hw) -
      nativeCorrection s v.1 ⟨v.2,hv⟩ (nativeTransition s v w hv hw) :=
  (unitCorrection_change (epsilonKernelEquiv s)
    (projectiveSplittingAlgHom s u.1 ⟨u.2,hu⟩) (projectiveSplittingAlgHom s v.1 ⟨v.2,hv⟩)
    (projectiveSplittingAlgHom_reduction s u.1 ⟨u.2,hu⟩)
    (projectiveSplittingAlgHom_reduction s v.1 ⟨v.2,hv⟩) (nativeTransition s v w hv hw)).symm

theorem projectedConeCup_corrections (s : Finset Vertex) (u v w : Vertex)
    (hu : u ∈ s) (hv : v ∈ s) (hw : w ∈ s) :
    projectedConeCup s u v w hu hv hw =
      closedProjection s (ordinaryCorrection s u.1 ⟨u.2,hu⟩ (coneTransition s v w hv hw)) -
        closedProjection s (ordinaryCorrection s v.1 ⟨v.2,hv⟩ (coneTransition s v w hv hw)) := by
  rw [← map_sub]
  exact congrArg (closedProjection s) (unitCorrection_change (ordinaryKernelEquiv s)
    (ordinarySplittingAlgHom s u.1 ⟨u.2,hu⟩) (ordinarySplittingAlgHom s v.1 ⟨v.2,hv⟩)
    (ordinarySplittingAlgHom_reduction s u.1 ⟨u.2,hu⟩)
    (ordinarySplittingAlgHom_reduction s v.1 ⟨v.2,hv⟩) (coneTransition s v w hv hw)).symm

theorem frameGaugeBoundary_formula (s : Finset Vertex) (u v w : Vertex)
    (hu : u ∈ s) (hv : v ∈ s) (hw : w ∈ s) :
    frameGaugeBoundary s u v w hu hv hw =
      frameDegree w.1 • (coordinateError s v.1 ⟨v.2,hv⟩ w hw - coordinateError s u.1 ⟨u.2,hu⟩ w hw) +
        frameDegree v.1 • (coordinateError s u.1 ⟨u.2,hu⟩ v hv - coordinateError s v.1 ⟨v.2,hv⟩ v hv) := by
  unfold frameGaugeBoundary frameGauge
  rw [smul_sub, smul_sub]
  abel

theorem nativeCup_eq_projectedConeCup_sub_boundary (s : Finset Vertex) (u v w : Vertex)
    (hu : u ∈ s) (hv : v ∈ s) (hw : w ∈ s) :
    nativeCup s u v w hu hv hw =
      projectedConeCup s u v w hu hv hw - frameGaugeBoundary s u v w hu hv hw := by
  rw [nativeCup_corrections, projectedConeCup_corrections,
    nativeCorrection_coordinate_formula, nativeCorrection_coordinate_formula, frameGaugeBoundary_formula]
  rw [smul_sub, smul_sub]
  abel

theorem projectedConeCup_sameLastCartier (s : Finset Vertex) (u : Vertex) (a : Fin 4) (l m : Fin 3)
    (hu : u ∈ s) (hv : (a,l) ∈ s) (hw : (a,m) ∈ s) :
    projectedConeCup s u (a,l) (a,m) hu hv hw = 0 := by
  rw [projectedConeCup_corrections]
  have hz (b : Fin 4) (hb : Admissible s b) : ordinaryCorrection s b hb 1 = 0 :=
    unitCorrection_one (ordinaryKernelEquiv s) (ordinarySplittingAlgHom s b hb)
      (ordinarySplittingAlgHom_reduction s b hb)
  simp only [coneTransition_sameCartier, hz, map_zero, sub_self]

/-- The old cone last edge is one, but the actual mixed-coordinate native
cup retains this explicit coordinate error. -/
theorem nativeCup_repeated_index (s : Finset Vertex) (l m n : Fin 3)
    (hu : (0,l) ∈ s) (hv : (1,m) ∈ s) (hw : (1,n) ∈ s) :
    nativeCup s (0,l) (1,m) (1,n) hu hv hw =
      2 • ((coordinateError s 0 ⟨l,hu⟩ (1,n) hw - coordinateError s 1 ⟨m,hv⟩ (1,n) hw) -
        (coordinateError s 0 ⟨l,hu⟩ (1,m) hv - coordinateError s 1 ⟨m,hv⟩ (1,m) hv)) := by
  rw [nativeCup_eq_projectedConeCup_sub_boundary, projectedConeCup_sameLastCartier,
    zero_sub, frameGaugeBoundary_formula]
  change -(2 • (coordinateError s 1 ⟨m,hv⟩ (1,n) hw - coordinateError s 0 ⟨l,hu⟩ (1,n) hw) +
    2 • (coordinateError s 0 ⟨l,hu⟩ (1,m) hv - coordinateError s 1 ⟨m,hv⟩ (1,m) hv)) = _
  abel

end CycleQ2LiteralNativeCupFrameGauge

end

#print axioms CycleQ2LiteralNativeCupFrameGauge.nativeCup_eq_projectedConeCup_sub_boundary
#print axioms CycleQ2LiteralNativeCupFrameGauge.nativeCup_repeated_index
