import Proposal.GeometricLiteralProjectiveIntersectionRestrictions

/-!
# The same original singleton splittings on every actual intersection

A Cartier index is admissible when one of its three actual coordinate
charts belongs to the finite intersection. The original chosen singleton
splitting extends to that actual product localization. Its degree-zero
projection gives a genuine native ring splitting of the original reduction.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralProjectiveIntersectionSplittings

open CycleQ2CartierSurfaceGrading CycleQ2ProjectiveCartierIdeal CycleQ2GeometricCartierNormalLift
  CycleQ2GeometricSeedNormalIdeals CycleQ2LiteralGradedDeformation
  CycleQ2LiteralGradedDeformationEquiv CycleQ2LiteralGradedReduction
  CycleQ2LiteralProjectiveDeformation CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveIntersectionKernel
  CycleQ2LiteralProjectiveIntersectionProjection CycleQ2LiteralCartierTransitionBinding
  CycleQ2LiteralCartierSplittings CycleQ2LiteralCartierOverlapSplittings
  CycleQ2GeometricSurfaceFirstOrder

attribute [local instance] CycleQ2LiteralCartierTransitionBinding.cubicSelfModule
  CycleQ2LiteralCartierTransitionBinding.cubicOppositeModule
  CycleQ2LiteralCartierTransitionBinding.cubicCentralScalar
  CycleQ2LiteralCartierTransitionBinding.cubicSmulCommClass
  CycleQ2GeometricSurfaceFirstOrder.reducedAlgebra
  CycleQ2GeometricKernelLocalization.localReductionAlgebra
  CycleQ2LiteralCartierSplittings.complexReductionTower
  CycleQ2LiteralCartierOverlapSplittings.baseReductionAlgebra

/-- A chart of this singleton cofactor index is among the intersection factors. -/
def Admissible (s : Finset Vertex) (a : Fin 4) : Prop := ∃ l : Fin 3, (a,l) ∈ s

theorem admissible_mono {s t : Finset Vertex} (hst : s ⊆ t) {a : Fin 4}
    (ha : Admissible s a) : Admissible t a := by
  obtain ⟨l,hl⟩ := ha
  exact ⟨l,hst hl⟩

theorem thickCartier_dvd {s : Finset Vertex} {a : Fin 4} (ha : Admissible s a) :
    cartierElement a ∣ thickProduct s := by
  obtain ⟨l,hl⟩ := ha
  refine ⟨coordinateElement l * ∏ v ∈ s.erase (a,l), chartDenominator v.1 v.2, ?_⟩
  change (∏ v ∈ s, chartDenominator v.1 v.2) = _
  rw [← Finset.mul_prod_erase s (fun v : Vertex => chartDenominator v.1 v.2) hl]
  exact mul_assoc _ _ _

theorem closedCartier_dvd {s : Finset Vertex} {a : Fin 4} (ha : Admissible s a) :
    coverElement 57 1 a ∣ closedProduct s := by
  obtain ⟨l,hl⟩ := ha
  refine ⟨CycleQ2GeometricSurfaceCoordinates.coordinateElement 57 1 l *
    ∏ v ∈ s.erase (a,l), refinedDenominator 57 1 v.1 v.2, ?_⟩
  change (∏ v ∈ s, refinedDenominator 57 1 v.1 v.2) = _
  rw [← Finset.mul_prod_erase s (fun v : Vertex => refinedDenominator 57 1 v.1 v.2) hl]
  exact mul_assoc _ _ _

def originalThickBaseMap (s : Finset Vertex) (a : Fin 4) (_ha : Admissible s a) : ThickBase →+* ThickCone s :=
  (algebraMap GradedDeformation (ThickCone s)).comp fromOriginal.toRingHom

def originalClosedBaseMap (s : Finset Vertex) (a : Fin 4) (_ha : Admissible s a) : ClosedBase →+* ClosedCone s :=
  (algebraMap (SurfaceRing 57 1) (ClosedCone s)).comp closedAlgEquiv.toRingHom

theorem fromOriginal_denominator (a : Fin 4) :
    fromOriginal (thickDenominator {a}) = cartierElement a := by
  change fromOriginal (originalPolynomial (polynomialProduct {a})) = _
  rw [fromOriginal_polynomial]
  simp only [polynomialProduct, Finset.prod_singleton]
  rfl

theorem closedAlgEquiv_denominator (a : Fin 4) :
    closedAlgEquiv (closedDenominator {a}) = coverElement 57 1 a := by
  exact (denominator_binding {a}).trans (by simp only [coverProduct, Finset.prod_singleton])

theorem originalThickBaseMap_denominator_unit (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) :
    IsUnit (originalThickBaseMap s a ha (thickDenominator {a})) := by
  change IsUnit (algebraMap GradedDeformation (ThickCone s)
    (fromOriginal (thickDenominator {a})))
  rw [fromOriginal_denominator]
  exact IsLocalization.Away.isUnit_of_dvd (thickProduct s) (thickCartier_dvd ha)

theorem originalClosedBaseMap_denominator_unit (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) :
    IsUnit (originalClosedBaseMap s a ha (closedDenominator {a})) := by
  change IsUnit (algebraMap (SurfaceRing 57 1) (ClosedCone s)
    (closedAlgEquiv (closedDenominator {a})))
  rw [closedAlgEquiv_denominator]
  exact IsLocalization.Away.isUnit_of_dvd (closedProduct s) (closedCartier_dvd ha)

def originalThickMap (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) : Thick {a} →+* ThickCone s :=
  IsLocalization.Away.lift (g := originalThickBaseMap s a ha) (thickDenominator {a})
    (originalThickBaseMap_denominator_unit s a ha)

def originalClosedMap (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) : CycleQ2LiteralCartierSplittings.ClosedRing {a} →+* ClosedCone s :=
  IsLocalization.Away.lift (g := originalClosedBaseMap s a ha) (closedDenominator {a})
    (originalClosedBaseMap_denominator_unit s a ha)

theorem originalThickMap_base (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) (z : ThickBase) :
    originalThickMap s a ha (@Algebra.algebraMap ThickBase (Thick {a})
      (inferInstance : CommSemiring ThickBase) (inferInstance : Semiring (Thick {a})) inferInstance z) =
      originalThickBaseMap s a ha z :=
  IsLocalization.Away.lift_eq (thickDenominator {a}) (originalThickBaseMap_denominator_unit s a ha) z

theorem originalClosedMap_base (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) (z : ClosedBase) :
    originalClosedMap s a ha (algebraMap ClosedBase (CycleQ2LiteralCartierSplittings.ClosedRing {a}) z) =
      originalClosedBaseMap s a ha z :=
  IsLocalization.Away.lift_eq (closedDenominator {a}) (originalClosedBaseMap_denominator_unit s a ha) z

theorem ordinaryReduction_base (s : Finset Vertex) (z : GradedDeformation) :
    ordinaryReduction s (algebraMap GradedDeformation (ThickCone s) z) =
      algebraMap (SurfaceRing 57 1) (ClosedCone s) (CycleQ2LiteralGradedReduction.reduction z) :=
  IsLocalization.map_eq _ z

theorem originalThickMap_reduction (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) (z : Thick {a}) :
    ordinaryReduction s (originalThickMap s a ha z) = originalClosedMap s a ha (reductionMap {a} z) := by
  have he : (ordinaryReduction s).comp (originalThickMap s a ha) =
      (originalClosedMap s a ha).comp (reductionMap {a}).toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (thickDenominator {a}))
    apply RingHom.ext
    intro x
    change ordinaryReduction s (originalThickMap s a ha _) = originalClosedMap s a ha (reductionMap {a} _)
    rw [originalThickMap_base, reductionMap_base, originalClosedMap_base]
    change ordinaryReduction s (algebraMap GradedDeformation (ThickCone s) (fromOriginal x)) =
      algebraMap (SurfaceRing 57 1) (ClosedCone s)
        (closedAlgEquiv (CycleQ2GeometricSurfaceFirstOrder.reduction equation perturbation x))
    rw [ordinaryReduction_base, reduction_eq_original, toOriginal_fromOriginal]
  exact RingHom.congr_fun he z

/-- The original singleton splitting, evaluated on original surface
functions and then extended into the coordinate-localized deformation. -/
def splittingBase (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) : SurfaceRing 57 1 →+* ThickCone s :=
  (originalThickMap s a ha).comp ((splitting {a} (by simp)).toRingHom.comp
    ((algebraMap ClosedBase (CycleQ2LiteralCartierSplittings.ClosedRing {a})).comp closedAlgEquiv.symm.toRingHom))

theorem splittingBase_reduction (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) (x : SurfaceRing 57 1) :
    ordinaryReduction s (splittingBase s a ha x) =
      algebraMap (SurfaceRing 57 1) (ClosedCone s) x := by
  change ordinaryReduction s (originalThickMap s a ha
      (splitting {a} (by simp) (algebraMap ClosedBase (CycleQ2LiteralCartierSplittings.ClosedRing {a}) (closedAlgEquiv.symm x)))) = _
  rw [originalThickMap_reduction]
  change originalClosedMap s a ha (algebraMap (Thick {a}) (CycleQ2LiteralCartierSplittings.ClosedRing {a})
    (splitting {a} (by simp) _)) = _
  rw [splitting_reduction, originalClosedMap_base]
  change algebraMap (SurfaceRing 57 1) (ClosedCone s)
    (closedAlgEquiv (closedAlgEquiv.symm x)) = _
  rw [AlgEquiv.apply_symm_apply]

theorem ordinaryReduction_surjective (s : Finset Vertex) :
    Function.Surjective (ordinaryReduction s) := by
  intro x
  obtain ⟨n,p,rfl⟩ := CycleQ2GradedLocalizationProjection.exists_fraction (closedProduct s) x
  obtain ⟨q,hq⟩ := CycleQ2LiteralGradedReduction.reduction_surjective p
  exact ⟨CycleQ2GradedLocalizationProjection.fraction (thickProduct s) n q,
    (ordinaryReduction_fraction s n q).trans (congrArg
      (CycleQ2GradedLocalizationProjection.fraction (closedProduct s) n) hq)⟩

theorem isUnit_of_ordinaryReduction (s : Finset Vertex) (z : ThickCone s)
    (hz : IsUnit (ordinaryReduction s z)) : IsUnit z := by
  obtain ⟨u,hu⟩ := hz
  obtain ⟨b,hb⟩ := ordinaryReduction_surjective s (↑(u⁻¹) : ClosedCone s)
  have hk : ordinaryReduction s (z * b - 1) = 0 := by
    rw [map_sub, map_mul, map_one, hb, ← hu, Units.mul_inv, sub_self]
  have hn : IsNilpotent (z * b - 1) :=
    ⟨2, by rw [pow_two]; exact ordinaryKernel_mul_zero s _ _ hk hk⟩
  have hp : IsUnit (z * b) := by
    have hi := hn.isUnit_add_one
    simpa only [sub_add_cancel] using hi
  exact isUnit_of_mul_isUnit_left hp

theorem splittingBase_denominator_unit (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) :
    IsUnit (splittingBase s a ha (closedProduct s)) := by
  apply isUnit_of_ordinaryReduction s
  rw [splittingBase_reduction]
  exact IsLocalization.Away.algebraMap_isUnit (closedProduct s)

/-- The same chosen cone splitting extended along the actual new denominator. -/
def ordinarySplitting (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) : ClosedCone s →+* ThickCone s :=
  IsLocalization.Away.lift (g := splittingBase s a ha) (closedProduct s)
    (splittingBase_denominator_unit s a ha)

theorem ordinarySplitting_base (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) (x : SurfaceRing 57 1) :
    ordinarySplitting s a ha (algebraMap (SurfaceRing 57 1) (ClosedCone s) x) = splittingBase s a ha x :=
  IsLocalization.Away.lift_eq _ (splittingBase_denominator_unit s a ha) x

theorem ordinarySplitting_reduction (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) (x : ClosedCone s) :
    ordinaryReduction s (ordinarySplitting s a ha x) = x := by
  have he : (ordinaryReduction s).comp (ordinarySplitting s a ha) = RingHom.id (ClosedCone s) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (closedProduct s))
    apply RingHom.ext
    intro z
    change ordinaryReduction s (ordinarySplitting s a ha _) = _
    rw [ordinarySplitting_base, splittingBase_reduction]
    rfl
  exact RingHom.congr_fun he x

theorem projectedSplitting_reduction (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) (x : CycleQ2LiteralProjectiveIntersections.ClosedRing s) :
    nativeReduction s (thickProjection s (ordinarySplitting s a ha x.val)) = x := by
  rw [projection_reduction, ordinarySplitting_reduction, closedProjection_val]

/-- An actual splitting on the genuine homogeneous-localization ring,
constructed from the already chosen original cone splitting. -/
def projectiveSplitting (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) :
    CycleQ2LiteralProjectiveIntersections.ClosedRing s →+* ThickRing s where
  toFun x := thickProjection s (ordinarySplitting s a ha x.val)
  map_zero' := by rw [HomogeneousLocalization.val_zero, map_zero, map_zero]
  map_one' := by
    rw [HomogeneousLocalization.val_one, map_one]
    simpa only [HomogeneousLocalization.val_one] using thickProjection_val s 1
  map_add' x y := by rw [HomogeneousLocalization.val_add, map_add, map_add]
  map_mul' x y := by
    rw [HomogeneousLocalization.val_mul, map_mul]
    apply thickProjection_mul s
    · rw [ordinarySplitting_reduction, projectedSplitting_reduction]
    · rw [ordinarySplitting_reduction, projectedSplitting_reduction]

theorem projectiveSplitting_reduction (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) (x : CycleQ2LiteralProjectiveIntersections.ClosedRing s) :
    nativeReduction s (projectiveSplitting s a ha x) = x := projectedSplitting_reduction s a ha x


open CycleQ2LiteralProjectiveIntersectionRestrictions

/-- The same original singleton map survives every further actual
ordinary localization. The coordinate witness in Admissible is irrelevant. -/
theorem originalThickMap_restrict {s t : Finset Vertex} (hst : s ⊆ t)
    (a : Fin 4) (ha : Admissible s a) (z : Thick {a}) :
    thickConeRestriction hst (originalThickMap s a ha z) =
      originalThickMap t a (admissible_mono hst ha) z := by
  have he : (thickConeRestriction hst).toRingHom.comp (originalThickMap s a ha) =
      originalThickMap t a (admissible_mono hst ha) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (thickDenominator {a}))
    apply RingHom.ext
    intro x
    change thickConeRestriction hst (originalThickMap s a ha _) =
      originalThickMap t a (admissible_mono hst ha) _
    rw [originalThickMap_base, originalThickMap_base]
    exact thickConeRestriction_base hst (fromOriginal x)
  exact RingHom.congr_fun he z

theorem splittingBase_restrict {s t : Finset Vertex} (hst : s ⊆ t)
    (a : Fin 4) (ha : Admissible s a) (x : SurfaceRing 57 1) :
    thickConeRestriction hst (splittingBase s a ha x) =
      splittingBase t a (admissible_mono hst ha) x :=
  originalThickMap_restrict hst a ha _

/-- Uniqueness of localization extends the same singleton splitting,
including on intersections of different coordinate charts. -/
theorem ordinarySplitting_restrict {s t : Finset Vertex} (hst : s ⊆ t)
    (a : Fin 4) (ha : Admissible s a) (x : ClosedCone s) :
    thickConeRestriction hst (ordinarySplitting s a ha x) =
      ordinarySplitting t a (admissible_mono hst ha) (closedConeRestriction hst x) := by
  have he : (thickConeRestriction hst).toRingHom.comp (ordinarySplitting s a ha) =
      (ordinarySplitting t a (admissible_mono hst ha)).comp (closedConeRestriction hst).toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (closedProduct s))
    apply RingHom.ext
    intro z
    change thickConeRestriction hst (ordinarySplitting s a ha _) =
      ordinarySplitting t a (admissible_mono hst ha) (closedConeRestriction hst _)
    rw [ordinarySplitting_base, closedConeRestriction_base, ordinarySplitting_base]
    exact splittingBase_restrict hst a ha z
  exact RingHom.congr_fun he x

/-- These are restrictions of one and the same original singleton
splitting, rather than independently chosen dehomogenized splittings. -/
theorem projectiveSplitting_restrict {s t : Finset Vertex} (hst : s ⊆ t)
    (a : Fin 4) (ha : Admissible s a) (x : CycleQ2LiteralProjectiveIntersections.ClosedRing s) :
    thickRestriction hst (projectiveSplitting s a ha x) =
      projectiveSplitting t a (admissible_mono hst ha) (closedRestriction hst x) := by
  change thickRestriction hst (thickProjection s (ordinarySplitting s a ha x.val)) =
    thickProjection t (ordinarySplitting t a (admissible_mono hst ha) (closedRestriction hst x).val)
  rw [← thickProjection_restrict, ordinarySplitting_restrict, ← closedRestriction_val]

end CycleQ2LiteralProjectiveIntersectionSplittings

end

#print axioms CycleQ2LiteralProjectiveIntersectionSplittings.originalThickMap_reduction
#print axioms CycleQ2LiteralProjectiveIntersectionSplittings.ordinarySplitting_reduction
#print axioms CycleQ2LiteralProjectiveIntersectionSplittings.projectiveSplitting_reduction

#print axioms CycleQ2LiteralProjectiveIntersectionSplittings.projectiveSplitting_restrict
