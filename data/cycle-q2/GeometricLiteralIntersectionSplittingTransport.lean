import Proposal.GeometricLiteralIntersectionEpsilonTransport

/-!
# The same original splittings and derivations after transport

The original cone overlap splitting transports to the ordinary splitting
of the actual product localization. Both are extensions of the same
original singleton choice, as proved on original numerators and then by
localization uniqueness. The actual epsilon normalization identifies the
transported splitting difference, and its degree-zero projection is the
already constructed native complex derivation.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralIntersectionSplittingTransport

open CycleQ2GeometricSeedNormalIdeals CycleQ2LiteralGradedDeformation
  CycleQ2LiteralGradedReduction CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveIntersectionProjection CycleQ2LiteralProjectiveIntersectionRestrictions
  CycleQ2LiteralProjectiveIntersectionSplittings CycleQ2LiteralProjectiveIntersectionComplex
  CycleQ2LiteralConeIntersectionTransport CycleQ2LiteralIntersectionEpsilonTransport
  CycleQ2LiteralCartierTransitionBinding CycleQ2LiteralCartierOverlapSplittings
  CycleQ2GeometricSquareZeroSplittings

attribute [local instance] CycleQ2LiteralCartierTransitionBinding.cubicSelfModule
  CycleQ2LiteralCartierTransitionBinding.cubicOppositeModule
  CycleQ2LiteralCartierTransitionBinding.cubicCentralScalar
  CycleQ2LiteralCartierTransitionBinding.cubicSmulCommClass
  CycleQ2GeometricSurfaceFirstOrder.reducedAlgebra
  CycleQ2GeometricKernelLocalization.localReductionAlgebra
  CycleQ2LiteralCartierSplittings.complexReductionTower
  CycleQ2LiteralCartierOverlapSplittings.baseReductionAlgebra
  CycleQ2LiteralIntersectionEpsilonTransport.ordinaryReductionAlgebra
  CycleQ2LiteralProjectiveIntersectionKernel.nativeReductionAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.complexReductionTower

theorem admits_singleton (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) : Admits s {a} := by
  intro b hb
  have h : b = a := Finset.mem_singleton.mp hb
  exact h ▸ ha

theorem thickMap_singleton (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a)
    (x : OldThick {a}) :
    thickMap s {a} (admits_singleton s a ha) x = originalThickMap s a ha x := by
  have he : (thickMap s {a} (admits_singleton s a ha)).toRingHom = originalThickMap s a ha := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (thickDenominator {a}))
    apply RingHom.ext
    intro z
    change thickMap s {a} (admits_singleton s a ha) _ = originalThickMap s a ha _
    rw [thickMap_base, originalThickMap_base]
    rfl
  exact RingHom.congr_fun he x

theorem closedMap_singleton (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a)
    (x : OldClosed {a}) :
    closedMap s {a} (admits_singleton s a ha) x = originalClosedMap s a ha x := by
  have he : (closedMap s {a} (admits_singleton s a ha)).toRingHom = originalClosedMap s a ha := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (closedDenominator {a}))
    apply RingHom.ext
    intro z
    change closedMap s {a} (admits_singleton s a ha) _ = originalClosedMap s a ha _
    rw [closedMap_base, originalClosedMap_base]
    rfl
  exact RingHom.congr_fun he x

theorem transported_splitting (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t)
    (a : Fin 4) (ha : a ∈ t) (x : OldClosed t) :
    thickMap s t ht (CycleQ2LiteralCartierKodairaSpencer.splittingOn a t ha x) =
      ordinarySplitting s a (ht a ha) (closedMap s t ht x) := by
  have he : (thickMap s t ht).toRingHom.comp
      (CycleQ2LiteralCartierKodairaSpencer.splittingOn a t ha).toRingHom =
      (ordinarySplitting s a (ht a ha)).comp (closedMap s t ht).toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (closedDenominator t))
    apply RingHom.ext
    intro z
    change thickMap s t ht (CycleQ2LiteralCartierKodairaSpencer.splittingOn a t ha _) =
      ordinarySplitting s a (ht a ha) (closedMap s t ht _)
    have hb := overlapSplitting_base (s := {a}) (t := t) (by simp)
      (by simpa only [Finset.singleton_subset_iff] using ha) z
    change CycleQ2LiteralCartierKodairaSpencer.splittingOn a t ha
      (algebraMap ClosedBase (OldClosed t) z) =
      CycleQ2LiteralCartierOverlapSplittings.thickRestriction
        (s := {a}) (t := t) (by simpa only [Finset.singleton_subset_iff] using ha)
        (CycleQ2LiteralCartierSplittings.splitting {a} (by simp)
          (algebraMap ClosedBase (OldClosed {a}) z)) at hb
    rw [hb, thickMap_restrict_source]
    change thickMap s {a} (admits_singleton s a (ht a ha)) _ = _
    rw [thickMap_singleton, closedMap_base]
    change originalThickMap s a (ht a ha)
      (CycleQ2LiteralCartierSplittings.splitting {a} (by simp) (algebraMap ClosedBase (OldClosed {a}) z)) =
      ordinarySplitting s a (ht a ha) (algebraMap (SurfaceRing 57 1) (ClosedCone s) (closedAlgEquiv z))
    rw [ordinarySplitting_base]
    change _ = originalThickMap s a (ht a ha)
      (CycleQ2LiteralCartierSplittings.splitting {a} (by simp)
        (algebraMap ClosedBase (OldClosed {a}) (closedAlgEquiv.symm (closedAlgEquiv z))))
    rw [AlgEquiv.symm_apply_apply]
  exact RingHom.congr_fun he x

theorem ordinaryReduction_complex (s : Finset Vertex) (c : ℂ) :
    ordinaryReduction s (algebraMap ℂ (ThickCone s) c) = algebraMap ℂ (ClosedCone s) c := by
  rw [IsScalarTower.algebraMap_apply ℂ GradedDeformation (ThickCone s),
    CycleQ2LiteralProjectiveIntersectionRestrictions.ordinaryReduction_base, reduction.commutes]
  exact (IsScalarTower.algebraMap_apply ℂ (SurfaceRing 57 1) (ClosedCone s) c).symm

local instance ordinaryComplexReductionTower (s : Finset Vertex) : IsScalarTower ℂ (ThickCone s) (ClosedCone s) :=
  IsScalarTower.of_algebraMap_eq (fun c => (ordinaryReduction_complex s c).symm)

def ordinarySplittingAlgHom (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) :
    ClosedCone s →ₐ[ℂ] ThickCone s where
  __ := ordinarySplitting s a ha
  commutes' := ordinarySplitting_complex s a ha

theorem ordinarySplittingAlgHom_reduction (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a)
    (x : ClosedCone s) : ordinaryReduction s (ordinarySplittingAlgHom s a ha x) = x :=
  ordinarySplitting_reduction s a ha x

def ordinaryKodairaSpencer (s : Finset Vertex) (a b : Fin 4) (ha : Admissible s a) (hb : Admissible s b) :
    Derivation ℂ (ClosedCone s) (ClosedCone s) :=
  difference (ordinaryKernelEquiv s) (ordinarySplittingAlgHom s a ha) (ordinarySplittingAlgHom s b hb)
    (ordinarySplittingAlgHom_reduction s a ha) (ordinarySplittingAlgHom_reduction s b hb)

theorem ordinary_epsilon_kodairaSpencer (s : Finset Vertex) (a b : Fin 4)
    (ha : Admissible s a) (hb : Admissible s b) (x : ClosedCone s) :
    ordinaryCoefficient s (ordinaryKodairaSpencer s a b ha hb x) =
      ordinarySplittingAlgHom s b hb x - ordinarySplittingAlgHom s a ha x :=
  epsilon_difference (ordinaryKernelEquiv s) (ordinarySplittingAlgHom s a ha) (ordinarySplittingAlgHom s b hb)
    (ordinarySplittingAlgHom_reduction s a ha) (ordinarySplittingAlgHom_reduction s b hb) x

theorem transported_kodairaSpencer (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t)
    (a b : Fin 4) (ha : a ∈ t) (hb : b ∈ t) (x : OldClosed t) :
    closedMap s t ht (CycleQ2LiteralCartierKodairaSpencer.kodairaSpencer t a b ha hb x) =
      ordinaryKodairaSpencer s a b (ht a ha) (ht b hb) (closedMap s t ht x) := by
  apply ordinaryCoefficient_injective s
  rw [← transported_epsilon, CycleQ2LiteralCartierKodairaSpencer.epsilon_kodairaSpencer,
    map_sub, transported_splitting, transported_splitting, ordinary_epsilon_kodairaSpencer]
  rfl

theorem projected_ordinaryKodairaSpencer (s : Finset Vertex) (a b : Fin 4)
    (ha : Admissible s a) (hb : Admissible s b) (x : ClosedRing s) :
    CycleQ2LiteralNativeKodairaSpencer.kodairaSpencer s a b ha hb x =
      closedProjection s (ordinaryKodairaSpencer s a b ha hb x.val) := by
  apply CycleQ2LiteralProjectiveIntersectionKernel.epsilonCoefficient_injective s
  rw [CycleQ2LiteralNativeKodairaSpencer.epsilon_kodairaSpencer,
    ← projection_ordinaryCoefficient, ordinary_epsilon_kodairaSpencer, map_sub]
  rfl

end CycleQ2LiteralIntersectionSplittingTransport

end

#print axioms CycleQ2LiteralIntersectionSplittingTransport.transported_splitting
#print axioms CycleQ2LiteralIntersectionSplittingTransport.transported_kodairaSpencer
#print axioms CycleQ2LiteralIntersectionSplittingTransport.projected_ordinaryKodairaSpencer
