import Proposal.GeometricLiteralNativeKodairaSpencer
import Proposal.GeometricLiteralProjectiveVertexRestrictions

/-!
# The original cone overlaps map to the actual projective intersections

Every original Cartier index in the source overlap is represented among
the actual intersection factors. Thus its original denominator becomes
a unit. The maps below extend the fixed-coordinate deformation and
closed-fibre comparisons by the genuine localization universal property.
Reduction and both source and target restrictions commute with them.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralConeIntersectionTransport

open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2GeometricSeedNormalIdeals
  CycleQ2GeometricCartierNormalLift CycleQ2LiteralGradedDeformation
  CycleQ2LiteralGradedDeformationEquiv CycleQ2LiteralGradedReduction
  CycleQ2LiteralProjectiveDeformation CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveIntersectionProjection CycleQ2LiteralProjectiveIntersectionRestrictions
  CycleQ2LiteralProjectiveIntersectionSplittings CycleQ2LiteralCartierTransitionBinding
  CycleQ2LiteralCartierOverlapSplittings

attribute [local instance] CycleQ2LiteralCartierTransitionBinding.cubicSelfModule
  CycleQ2LiteralCartierTransitionBinding.cubicOppositeModule
  CycleQ2LiteralCartierTransitionBinding.cubicCentralScalar
  CycleQ2LiteralCartierTransitionBinding.cubicSmulCommClass
  CycleQ2GeometricSurfaceFirstOrder.reducedAlgebra
  CycleQ2GeometricKernelLocalization.localReductionAlgebra
  CycleQ2LiteralCartierSplittings.complexReductionTower
  CycleQ2LiteralCartierOverlapSplittings.baseReductionAlgebra

abbrev OldThick (t : Finset (Fin 4)) := CycleQ2LiteralCartierSplittings.Thick t
abbrev OldClosed (t : Finset (Fin 4)) := CycleQ2LiteralCartierSplittings.ClosedRing t

def Admits (s : Finset Vertex) (t : Finset (Fin 4)) : Prop :=
  ∀ a ∈ t, Admissible s a

theorem admits_mono {s u : Finset Vertex} (hsu : s ⊆ u) {t : Finset (Fin 4)}
    (ht : Admits s t) : Admits u t := fun a ha => admissible_mono hsu (ht a ha)

theorem admits_subset {s : Finset Vertex} {t u : Finset (Fin 4)} (htu : t ⊆ u)
    (hu : Admits s u) : Admits s t := fun a ha => hu a (htu ha)

theorem admits_pair (s : Finset Vertex) (v w : Vertex) (hv : v ∈ s) (hw : w ∈ s) :
    Admits s {v.1,w.1} := by
  intro a ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · exact ⟨v.2,hv⟩
  · exact ⟨w.2,hw⟩

def thickBaseMap (s : Finset Vertex) : ThickBase →ₐ[ℂ] ThickCone s :=
  (IsScalarTower.toAlgHom ℂ GradedDeformation (ThickCone s)).comp fromOriginal

def closedBaseMap (s : Finset Vertex) : ClosedBase →ₐ[ℂ] ClosedCone s :=
  (IsScalarTower.toAlgHom ℂ (SurfaceRing 57 1) (ClosedCone s)).comp closedAlgEquiv.toAlgHom

theorem thickBaseMap_denominator (s : Finset Vertex) (t : Finset (Fin 4)) :
    thickBaseMap s (thickDenominator t) =
      ∏ a ∈ t, algebraMap GradedDeformation (ThickCone s) (cartierElement a) := by
  change algebraMap GradedDeformation (ThickCone s)
    (fromOriginal (originalPolynomial (CycleQ2LiteralCartierSplittings.polynomialProduct t))) = _
  rw [fromOriginal_polynomial]
  change algebraMap GradedDeformation (ThickCone s)
    (polynomialInGraded (∏ a ∈ t, CycleQ2LiteralCartierSplittings.coverPolynomial a)) = _
  rw [map_prod, map_prod]
  rfl

theorem closedBaseMap_denominator (s : Finset Vertex) (t : Finset (Fin 4)) :
    closedBaseMap s (closedDenominator t) =
      ∏ a ∈ t, algebraMap (SurfaceRing 57 1) (ClosedCone s) (coverElement 57 1 a) := by
  change algebraMap (SurfaceRing 57 1) (ClosedCone s) (closedAlgEquiv (closedDenominator t)) = _
  have h : closedAlgEquiv (closedDenominator t) = coverProduct 57 1 t :=
    CycleQ2LiteralCartierSplittings.denominator_binding t
  rw [h]
  exact map_prod _ _ _

theorem thickBaseMap_denominator_unit (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t) :
    IsUnit (thickBaseMap s (thickDenominator t)) := by
  rw [thickBaseMap_denominator]
  exact IsUnit.prod_iff.mpr (fun a ha =>
    IsLocalization.Away.isUnit_of_dvd (thickProduct s) (thickCartier_dvd (ht a ha)))

theorem closedBaseMap_denominator_unit (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t) :
    IsUnit (closedBaseMap s (closedDenominator t)) := by
  rw [closedBaseMap_denominator]
  exact IsUnit.prod_iff.mpr (fun a ha =>
    IsLocalization.Away.isUnit_of_dvd (closedProduct s) (closedCartier_dvd (ht a ha)))

def thickMap (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t) : OldThick t →ₐ[ℂ] ThickCone s :=
  IsLocalization.Away.liftAlgHom (thickDenominator t) (f := thickBaseMap s)
    (thickBaseMap_denominator_unit s t ht)

def closedMap (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t) : OldClosed t →ₐ[ℂ] ClosedCone s :=
  IsLocalization.Away.liftAlgHom (closedDenominator t) (f := closedBaseMap s)
    (closedBaseMap_denominator_unit s t ht)

theorem thickMap_base (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t) (x : ThickBase) :
    thickMap s t ht (@Algebra.algebraMap ThickBase (OldThick t)
      (inferInstance : CommSemiring ThickBase) (inferInstance : Semiring (OldThick t)) inferInstance x) =
      thickBaseMap s x :=
  IsLocalization.Away.lift_eq (thickDenominator t) (thickBaseMap_denominator_unit s t ht) x

theorem closedMap_base (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t) (x : ClosedBase) :
    closedMap s t ht (algebraMap ClosedBase (OldClosed t) x) = closedBaseMap s x :=
  IsLocalization.Away.lift_eq (closedDenominator t) (closedBaseMap_denominator_unit s t ht) x

theorem thickMap_polynomial (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t) (p : WeightedPoly) :
    thickMap s t ht (CycleQ2LiteralCartierAtiyahFaces.polynomialMap t p) =
      algebraMap GradedDeformation (ThickCone s) (polynomialInGraded p) := by
  change thickMap s t ht (@Algebra.algebraMap ThickBase (OldThick t)
    (inferInstance : CommSemiring ThickBase) (inferInstance : Semiring (OldThick t)) inferInstance
      (originalPolynomial p)) = _
  rw [thickMap_base]
  change algebraMap GradedDeformation (ThickCone s) (fromOriginal (originalPolynomial p)) = _
  rw [fromOriginal_polynomial]

theorem reduction_thickMap (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t) (x : OldThick t) :
    ordinaryReduction s (thickMap s t ht x) = closedMap s t ht (reductionMap t x) := by
  have he : (ordinaryReduction s).comp (thickMap s t ht).toRingHom =
      (closedMap s t ht).toRingHom.comp (reductionMap t).toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (thickDenominator t))
    apply RingHom.ext
    intro z
    change ordinaryReduction s (thickMap s t ht _) = closedMap s t ht (reductionMap t _)
    rw [thickMap_base, reductionMap_base, closedMap_base]
    change ordinaryReduction s (algebraMap GradedDeformation (ThickCone s) (fromOriginal z)) =
      algebraMap (SurfaceRing 57 1) (ClosedCone s)
        (closedAlgEquiv (CycleQ2GeometricSurfaceFirstOrder.reduction equation perturbation z))
    rw [CycleQ2LiteralProjectiveIntersectionRestrictions.ordinaryReduction_base,
      reduction_eq_original, toOriginal_fromOriginal]
  exact RingHom.congr_fun he x

theorem thickMap_restrict_target {s u : Finset Vertex} (hsu : s ⊆ u)
    (t : Finset (Fin 4)) (ht : Admits s t) (x : OldThick t) :
    thickConeRestriction hsu (thickMap s t ht x) = thickMap u t (admits_mono hsu ht) x := by
  have he : (thickConeRestriction hsu).toRingHom.comp (thickMap s t ht).toRingHom =
      (thickMap u t (admits_mono hsu ht)).toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (thickDenominator t))
    apply RingHom.ext
    intro z
    change thickConeRestriction hsu (thickMap s t ht _) = thickMap u t (admits_mono hsu ht) _
    rw [thickMap_base, thickMap_base]
    exact thickConeRestriction_base hsu (fromOriginal z)
  exact RingHom.congr_fun he x

theorem closedMap_restrict_target {s u : Finset Vertex} (hsu : s ⊆ u)
    (t : Finset (Fin 4)) (ht : Admits s t) (x : OldClosed t) :
    closedConeRestriction hsu (closedMap s t ht x) = closedMap u t (admits_mono hsu ht) x := by
  have he : (closedConeRestriction hsu).toRingHom.comp (closedMap s t ht).toRingHom =
      (closedMap u t (admits_mono hsu ht)).toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (closedDenominator t))
    apply RingHom.ext
    intro z
    change closedConeRestriction hsu (closedMap s t ht _) = closedMap u t (admits_mono hsu ht) _
    rw [closedMap_base, closedMap_base]
    exact closedConeRestriction_base hsu (closedAlgEquiv z)
  exact RingHom.congr_fun he x

theorem thickMap_restrict_source (s : Finset Vertex) {t u : Finset (Fin 4)} (htu : t ⊆ u)
    (hu : Admits s u) (x : OldThick t) :
    thickMap s u hu (CycleQ2LiteralCartierOverlapSplittings.thickRestriction htu x) =
      thickMap s t (admits_subset htu hu) x := by
  have he : (thickMap s u hu).toRingHom.comp
      (CycleQ2LiteralCartierOverlapSplittings.thickRestriction htu).toRingHom =
      (thickMap s t (admits_subset htu hu)).toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (thickDenominator t))
    apply RingHom.ext
    intro z
    change thickMap s u hu (CycleQ2LiteralCartierOverlapSplittings.thickRestriction htu _) =
      thickMap s t (admits_subset htu hu) _
    rw [CycleQ2LiteralCartierOverlapSplittings.thickRestriction_base, thickMap_base, thickMap_base]
  exact RingHom.congr_fun he x

theorem closedMap_restrict_source (s : Finset Vertex) {t u : Finset (Fin 4)} (htu : t ⊆ u)
    (hu : Admits s u) (x : OldClosed t) :
    closedMap s u hu (CycleQ2LiteralCartierOverlapSplittings.closedRestriction htu x) =
      closedMap s t (admits_subset htu hu) x := by
  have he : (closedMap s u hu).toRingHom.comp
      (CycleQ2LiteralCartierOverlapSplittings.closedRestriction htu).toRingHom =
      (closedMap s t (admits_subset htu hu)).toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (closedDenominator t))
    apply RingHom.ext
    intro z
    change closedMap s u hu (CycleQ2LiteralCartierOverlapSplittings.closedRestriction htu _) =
      closedMap s t (admits_subset htu hu) _
    rw [CycleQ2LiteralCartierOverlapSplittings.closedRestriction_base, closedMap_base, closedMap_base]
  exact RingHom.congr_fun he x

end CycleQ2LiteralConeIntersectionTransport

end

#print axioms CycleQ2LiteralConeIntersectionTransport.thickMap_polynomial
#print axioms CycleQ2LiteralConeIntersectionTransport.reduction_thickMap
#print axioms CycleQ2LiteralConeIntersectionTransport.thickMap_restrict_source
#print axioms CycleQ2LiteralConeIntersectionTransport.closedMap_restrict_target
