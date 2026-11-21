import Proposal.GeometricSquareZeroCotangentChange
import Proposal.GeometricLiteralNativeCupFrameGauge

/-!
# The original native reduced cotangent sequence and its KS change

Every term uses the original thick and reduced intersection rings,
their actual complex coefficients, the actual reduction, and the same
original singleton splittings. The tensor module is the literal reduced
cotangent module of that deformation. Its original d(epsilon) inclusion
is faithful, and its splitting changes by the already fixed native
Kodaira--Spencer derivation with positive sign.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralNativeCotangent

open scoped TensorProduct
open CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionKernel
  CycleQ2LiteralProjectiveIntersectionSplittings
  CycleQ2LiteralProjectiveIntersectionComplex CycleQ2LiteralNativeKodairaSpencer
  CycleQ2LiteralNativeCartierTransitions CycleQ2LiteralNativeCupFrameGauge
  CycleQ2GeometricSquareZeroSplittings CycleQ2GeometricSquareZeroReducedCotangent
  CycleQ2GeometricSquareZeroCotangentChange

attribute [local instance] CycleQ2LiteralProjectiveIntersectionKernel.nativeReductionAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.complexReductionTower

abbrev NativeCotangent (s : Finset Vertex) :=
  ReducedCotangent (K := ℂ) (E := ThickRing s) (C := ClosedRing s)

theorem epsilon_one (s : Finset Vertex) : epsilon (epsilonKernelEquiv s) 1 = nativeEpsilon s := by
  change epsilonCoefficient s 1 = nativeEpsilon s
  simpa only [map_one,mul_one] using epsilonCoefficient_of_reduction s (1 : ThickRing s)

def nativeEpsilonInclusion (s : Finset Vertex) : ClosedRing s →ₗ[ClosedRing s] NativeCotangent s :=
  epsilonInclusion (K := ℂ) (epsilonKernelEquiv s)

theorem nativeEpsilonInclusion_tmul (s : Finset Vertex) (a : ClosedRing s) :
    nativeEpsilonInclusion s a = a ⊗ₜ[ThickRing s] KaehlerDifferential.D ℂ (ThickRing s) (nativeEpsilon s) := by
  change a • ((1 : ClosedRing s) ⊗ₜ[ThickRing s]
    KaehlerDifferential.D ℂ (ThickRing s) (epsilon (epsilonKernelEquiv s) 1)) = _
  rw [epsilon_one]
  simp only [TensorProduct.smul_tmul',smul_eq_mul,mul_one]

def nativeCotangentReduction (s : Finset Vertex) :
    NativeCotangent s →ₗ[ClosedRing s] KaehlerDifferential ℂ (ClosedRing s) :=
  reductionMap (K := ℂ) (E := ThickRing s) (C := ClosedRing s)

theorem nativeCotangentReduction_D (s : Finset Vertex) (b : ThickRing s) :
    nativeCotangentReduction s ((1 : ClosedRing s) ⊗ₜ[ThickRing s] KaehlerDifferential.D ℂ (ThickRing s) b) =
      KaehlerDifferential.D ℂ (ClosedRing s) (nativeReduction s b) :=
  reductionMap_D b

def nativeCotangentSplitting (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) :
    KaehlerDifferential ℂ (ClosedRing s) →ₗ[ClosedRing s] NativeCotangent s :=
  splittingLift (projectiveSplittingAlgHom s a ha) (projectiveSplittingAlgHom_reduction s a ha)

def nativeCotangentRetraction (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) :
    NativeCotangent s →ₗ[ClosedRing s] ClosedRing s :=
  coefficientRetraction (epsilonKernelEquiv s)
    (projectiveSplittingAlgHom s a ha) (projectiveSplittingAlgHom_reduction s a ha)

def nativeCotangentSplitEquiv (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) :
    NativeCotangent s ≃ₗ[ClosedRing s] KaehlerDifferential ℂ (ClosedRing s) × ClosedRing s :=
  splitEquiv (epsilonKernelEquiv s)
    (projectiveSplittingAlgHom s a ha) (projectiveSplittingAlgHom_reduction s a ha)

theorem nativeEpsilonInclusion_retraction (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a)
    (x : ClosedRing s) : nativeCotangentRetraction s a ha (nativeEpsilonInclusion s x) = x :=
  coefficientRetraction_epsilonInclusion (epsilonKernelEquiv s)
    (projectiveSplittingAlgHom s a ha) (projectiveSplittingAlgHom_reduction s a ha) x

theorem nativeEpsilonInclusion_injective (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) :
    Function.Injective (nativeEpsilonInclusion s) :=
  epsilonInclusion_injective (epsilonKernelEquiv s)
    (projectiveSplittingAlgHom s a ha) (projectiveSplittingAlgHom_reduction s a ha)

theorem nativeCotangentReduction_splitting (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) :
    (nativeCotangentReduction s).comp (nativeCotangentSplitting s a ha) = LinearMap.id :=
  reductionMap_splittingLift (projectiveSplittingAlgHom s a ha) (projectiveSplittingAlgHom_reduction s a ha)

theorem nativeCotangentReduction_surjective (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) :
    Function.Surjective (nativeCotangentReduction s) :=
  reductionMap_surjective (projectiveSplittingAlgHom s a ha) (projectiveSplittingAlgHom_reduction s a ha)

theorem nativeCotangentReduction_kernel (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a)
    (z : NativeCotangent s) : nativeCotangentReduction s z = 0 ↔
      ∃ x : ClosedRing s, nativeEpsilonInclusion s x = z :=
  reductionMap_kernel (epsilonKernelEquiv s)
    (projectiveSplittingAlgHom s a ha) (projectiveSplittingAlgHom_reduction s a ha) z

theorem nativeCotangentSplitting_change (s : Finset Vertex) (u v : Vertex)
    (hu : u ∈ s) (hv : v ∈ s) (ω : KaehlerDifferential ℂ (ClosedRing s)) :
    nativeCotangentSplitting s v.1 ⟨v.2,hv⟩ ω - nativeCotangentSplitting s u.1 ⟨u.2,hu⟩ ω =
      nativeEpsilonInclusion s ((vertexKodairaSpencer s u v hu hv).liftKaehlerDifferential ω) :=
  splittingLift_change (epsilonKernelEquiv s)
    (projectiveSplittingAlgHom s u.1 ⟨u.2,hu⟩) (projectiveSplittingAlgHom_reduction s u.1 ⟨u.2,hu⟩)
    (projectiveSplittingAlgHom s v.1 ⟨v.2,hv⟩) (projectiveSplittingAlgHom_reduction s v.1 ⟨v.2,hv⟩) ω

theorem nativeCotangentRetraction_change (s : Finset Vertex) (u v : Vertex)
    (hu : u ∈ s) (hv : v ∈ s) (z : NativeCotangent s) :
    nativeCotangentRetraction s u.1 ⟨u.2,hu⟩ z - nativeCotangentRetraction s v.1 ⟨v.2,hv⟩ z =
      (vertexKodairaSpencer s u v hu hv).liftKaehlerDifferential (nativeCotangentReduction s z) :=
  coefficientRetraction_change (epsilonKernelEquiv s)
    (projectiveSplittingAlgHom s u.1 ⟨u.2,hu⟩) (projectiveSplittingAlgHom_reduction s u.1 ⟨u.2,hu⟩)
    (projectiveSplittingAlgHom s v.1 ⟨v.2,hv⟩) (projectiveSplittingAlgHom_reduction s v.1 ⟨v.2,hv⟩) z

theorem nativeCotangentCoordinates_change (s : Finset Vertex) (u v : Vertex)
    (hu : u ∈ s) (hv : v ∈ s) (z : NativeCotangent s) :
    nativeCotangentSplitEquiv s v.1 ⟨v.2,hv⟩ z =
      ((nativeCotangentSplitEquiv s u.1 ⟨u.2,hu⟩ z).1,
        (nativeCotangentSplitEquiv s u.1 ⟨u.2,hu⟩ z).2 -
          (vertexKodairaSpencer s u v hu hv).liftKaehlerDifferential
            ((nativeCotangentSplitEquiv s u.1 ⟨u.2,hu⟩ z).1)) :=
  splitCoordinates_change (epsilonKernelEquiv s)
    (projectiveSplittingAlgHom s u.1 ⟨u.2,hu⟩) (projectiveSplittingAlgHom_reduction s u.1 ⟨u.2,hu⟩)
    (projectiveSplittingAlgHom s v.1 ⟨v.2,hv⟩) (projectiveSplittingAlgHom_reduction s v.1 ⟨v.2,hv⟩) z

def nativeCotangentTransitionLift (s : Finset Vertex) (u v : Vertex) (hu : u ∈ s) (hv : v ∈ s) :
    NativeCotangent s :=
  nativeCotangentSplitting s u.1 ⟨u.2,hu⟩ (logDifferential (K := ℂ) (transition s u v hu hv))

theorem nativeCotangentTransitionLift_boundary (s : Finset Vertex) (u v w : Vertex)
    (hu : u ∈ s) (hv : v ∈ s) (hw : w ∈ s) :
    nativeCotangentTransitionLift s v w hv hw - nativeCotangentTransitionLift s u w hu hw +
      nativeCotangentTransitionLift s u v hu hv = nativeEpsilonInclusion s (nativeCup s u v w hu hv hw) := by
  have hα : logDifferential (K := ℂ) (transition s u w hu hw) =
      logDifferential (K := ℂ) (transition s u v hu hv) + logDifferential (K := ℂ) (transition s v w hv hw) := by
    rw [← transition_cocycle s u v w hu hv hw,logDifferential_mul]
  change nativeCotangentSplitting s v.1 ⟨v.2,hv⟩ (logDifferential (K := ℂ) (transition s v w hv hw)) -
      nativeCotangentSplitting s u.1 ⟨u.2,hu⟩ (logDifferential (K := ℂ) (transition s u w hu hw)) +
      nativeCotangentSplitting s u.1 ⟨u.2,hu⟩ (logDifferential (K := ℂ) (transition s u v hu hv)) = _
  rw [hα,map_add]
  calc
    _ = nativeCotangentSplitting s v.1 ⟨v.2,hv⟩ (logDifferential (K := ℂ) (transition s v w hv hw)) -
        nativeCotangentSplitting s u.1 ⟨u.2,hu⟩ (logDifferential (K := ℂ) (transition s v w hv hw)) := by abel
    _ = _ := nativeCotangentSplitting_change s u v hu hv _

end CycleQ2LiteralNativeCotangent

end

#print axioms CycleQ2LiteralNativeCotangent.nativeEpsilonInclusion_injective
#print axioms CycleQ2LiteralNativeCotangent.nativeCotangentReduction_kernel
#print axioms CycleQ2LiteralNativeCotangent.nativeCotangentSplitting_change
#print axioms CycleQ2LiteralNativeCotangent.nativeCotangentTransitionLift_boundary
