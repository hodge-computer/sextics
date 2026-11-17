import Proposal.GeometricLiteralProjectiveProjection

/-!
# The chosen original splittings on the native projective charts

Each existing singleton cone splitting is extended along the actual
coordinate localization, after transport through the fixed-coordinate
equivalence of the original deformation. Projecting this extension on
degree-zero inputs gives an actual ring splitting of the native
projective reduction. The chosen singleton splitting is retained.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralProjectiveSplittings

open CycleQ2CartierSurfaceGrading CycleQ2ProjectiveCartierIdeal CycleQ2GeometricCartierNormalLift
  CycleQ2GeometricSeedNormalIdeals CycleQ2LiteralGradedDeformation
  CycleQ2LiteralGradedDeformationEquiv CycleQ2LiteralGradedReduction
  CycleQ2LiteralProjectiveDeformation CycleQ2LiteralProjectiveKernel
  CycleQ2LiteralProjectiveProjection CycleQ2LiteralCartierTransitionBinding
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

def originalThickBaseMap (a : Fin 4) (l : Fin 3) : ThickBase →+* OrdinaryThick a l :=
  (algebraMap GradedDeformation (OrdinaryThick a l)).comp fromOriginal.toRingHom

def originalClosedBaseMap (a : Fin 4) (l : Fin 3) : ClosedBase →+* OrdinaryClosed a l :=
  (algebraMap (SurfaceRing 57 1) (OrdinaryClosed a l)).comp closedAlgEquiv.toRingHom

theorem fromOriginal_denominator (a : Fin 4) :
    fromOriginal (thickDenominator {a}) = cartierElement a := by
  change fromOriginal (originalPolynomial (polynomialProduct {a})) = _
  rw [fromOriginal_polynomial]
  simp only [polynomialProduct, Finset.prod_singleton]
  rfl

theorem closedAlgEquiv_denominator (a : Fin 4) :
    closedAlgEquiv (closedDenominator {a}) = coverElement 57 1 a := by
  exact (denominator_binding {a}).trans (by simp only [coverProduct, Finset.prod_singleton])

theorem originalThickBaseMap_denominator_unit (a : Fin 4) (l : Fin 3) :
    IsUnit (originalThickBaseMap a l (thickDenominator {a})) := by
  change IsUnit (algebraMap GradedDeformation (OrdinaryThick a l)
    (fromOriginal (thickDenominator {a})))
  rw [fromOriginal_denominator]
  exact IsLocalization.Away.isUnit_of_dvd (chartDenominator a l) ⟨coordinateElement l,rfl⟩

theorem originalClosedBaseMap_denominator_unit (a : Fin 4) (l : Fin 3) :
    IsUnit (originalClosedBaseMap a l (closedDenominator {a})) := by
  change IsUnit (algebraMap (SurfaceRing 57 1) (OrdinaryClosed a l)
    (closedAlgEquiv (closedDenominator {a})))
  rw [closedAlgEquiv_denominator]
  exact IsLocalization.Away.isUnit_of_dvd (refinedDenominator 57 1 a l)
    ⟨CycleQ2GeometricSurfaceCoordinates.coordinateElement 57 1 l,rfl⟩

def originalThickMap (a : Fin 4) (l : Fin 3) : Thick {a} →+* OrdinaryThick a l :=
  IsLocalization.Away.lift (g := originalThickBaseMap a l) (thickDenominator {a})
    (originalThickBaseMap_denominator_unit a l)

def originalClosedMap (a : Fin 4) (l : Fin 3) : ClosedRing {a} →+* OrdinaryClosed a l :=
  IsLocalization.Away.lift (g := originalClosedBaseMap a l) (closedDenominator {a})
    (originalClosedBaseMap_denominator_unit a l)

theorem originalThickMap_base (a : Fin 4) (l : Fin 3) (z : ThickBase) :
    originalThickMap a l (@Algebra.algebraMap ThickBase (Thick {a})
      (inferInstance : CommSemiring ThickBase) (inferInstance : Semiring (Thick {a})) inferInstance z) =
      originalThickBaseMap a l z :=
  IsLocalization.Away.lift_eq (thickDenominator {a}) (originalThickBaseMap_denominator_unit a l) z

theorem originalClosedMap_base (a : Fin 4) (l : Fin 3) (z : ClosedBase) :
    originalClosedMap a l (algebraMap ClosedBase (ClosedRing {a}) z) =
      originalClosedBaseMap a l z :=
  IsLocalization.Away.lift_eq (closedDenominator {a}) (originalClosedBaseMap_denominator_unit a l) z

theorem ordinaryReduction_base (a : Fin 4) (l : Fin 3) (z : GradedDeformation) :
    ordinaryReduction a l (algebraMap GradedDeformation (OrdinaryThick a l) z) =
      algebraMap (SurfaceRing 57 1) (OrdinaryClosed a l) (CycleQ2LiteralGradedReduction.reduction z) :=
  IsLocalization.map_eq _ z

theorem originalThickMap_reduction (a : Fin 4) (l : Fin 3) (z : Thick {a}) :
    ordinaryReduction a l (originalThickMap a l z) = originalClosedMap a l (reductionMap {a} z) := by
  have he : (ordinaryReduction a l).comp (originalThickMap a l) =
      (originalClosedMap a l).comp (reductionMap {a}).toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (thickDenominator {a}))
    apply RingHom.ext
    intro x
    change ordinaryReduction a l (originalThickMap a l _) = originalClosedMap a l (reductionMap {a} _)
    rw [originalThickMap_base, reductionMap_base, originalClosedMap_base]
    change ordinaryReduction a l (algebraMap GradedDeformation (OrdinaryThick a l) (fromOriginal x)) =
      algebraMap (SurfaceRing 57 1) (OrdinaryClosed a l)
        (closedAlgEquiv (CycleQ2GeometricSurfaceFirstOrder.reduction equation perturbation x))
    rw [ordinaryReduction_base, reduction_eq_original, toOriginal_fromOriginal]
  exact RingHom.congr_fun he z

/-- The original singleton splitting, evaluated on original surface
functions and then extended into the coordinate-localized deformation. -/
def splittingBase (a : Fin 4) (l : Fin 3) : SurfaceRing 57 1 →+* OrdinaryThick a l :=
  (originalThickMap a l).comp ((splitting {a} (by simp)).toRingHom.comp
    ((algebraMap ClosedBase (ClosedRing {a})).comp closedAlgEquiv.symm.toRingHom))

theorem splittingBase_reduction (a : Fin 4) (l : Fin 3) (x : SurfaceRing 57 1) :
    ordinaryReduction a l (splittingBase a l x) =
      algebraMap (SurfaceRing 57 1) (OrdinaryClosed a l) x := by
  change ordinaryReduction a l (originalThickMap a l
      (splitting {a} (by simp) (algebraMap ClosedBase (ClosedRing {a}) (closedAlgEquiv.symm x)))) = _
  rw [originalThickMap_reduction]
  change originalClosedMap a l (algebraMap (Thick {a}) (ClosedRing {a})
    (splitting {a} (by simp) _)) = _
  rw [splitting_reduction, originalClosedMap_base]
  change algebraMap (SurfaceRing 57 1) (OrdinaryClosed a l)
    (closedAlgEquiv (closedAlgEquiv.symm x)) = _
  rw [AlgEquiv.apply_symm_apply]

theorem ordinaryReduction_surjective (a : Fin 4) (l : Fin 3) :
    Function.Surjective (ordinaryReduction a l) := by
  intro x
  obtain ⟨n,p,rfl⟩ := CycleQ2GradedLocalizationProjection.exists_fraction (refinedDenominator 57 1 a l) x
  obtain ⟨q,hq⟩ := CycleQ2LiteralGradedReduction.reduction_surjective p
  exact ⟨CycleQ2GradedLocalizationProjection.fraction (chartDenominator a l) n q,
    (ordinaryReduction_fraction a l n q).trans (congrArg
      (CycleQ2GradedLocalizationProjection.fraction (refinedDenominator 57 1 a l) n) hq)⟩

theorem isUnit_of_ordinaryReduction (a : Fin 4) (l : Fin 3) (z : OrdinaryThick a l)
    (hz : IsUnit (ordinaryReduction a l z)) : IsUnit z := by
  obtain ⟨u,hu⟩ := hz
  obtain ⟨b,hb⟩ := ordinaryReduction_surjective a l (↑(u⁻¹) : OrdinaryClosed a l)
  have hk : ordinaryReduction a l (z * b - 1) = 0 := by
    rw [map_sub, map_mul, map_one, hb, ← hu, Units.mul_inv, sub_self]
  have hn : IsNilpotent (z * b - 1) :=
    ⟨2, by rw [pow_two]; exact ordinaryKernel_mul_zero a l _ _ hk hk⟩
  have hp : IsUnit (z * b) := by
    have hi := hn.isUnit_add_one
    simpa only [sub_add_cancel] using hi
  exact isUnit_of_mul_isUnit_left hp

theorem splittingBase_denominator_unit (a : Fin 4) (l : Fin 3) :
    IsUnit (splittingBase a l (refinedDenominator 57 1 a l)) := by
  apply isUnit_of_ordinaryReduction a l
  rw [splittingBase_reduction]
  exact IsLocalization.Away.algebraMap_isUnit (refinedDenominator 57 1 a l)

/-- The same chosen cone splitting extended along the actual new denominator. -/
def ordinarySplitting (a : Fin 4) (l : Fin 3) : OrdinaryClosed a l →+* OrdinaryThick a l :=
  IsLocalization.Away.lift (g := splittingBase a l) (refinedDenominator 57 1 a l)
    (splittingBase_denominator_unit a l)

theorem ordinarySplitting_base (a : Fin 4) (l : Fin 3) (x : SurfaceRing 57 1) :
    ordinarySplitting a l (algebraMap (SurfaceRing 57 1) (OrdinaryClosed a l) x) = splittingBase a l x :=
  IsLocalization.Away.lift_eq _ (splittingBase_denominator_unit a l) x

theorem ordinarySplitting_reduction (a : Fin 4) (l : Fin 3) (x : OrdinaryClosed a l) :
    ordinaryReduction a l (ordinarySplitting a l x) = x := by
  have he : (ordinaryReduction a l).comp (ordinarySplitting a l) = RingHom.id (OrdinaryClosed a l) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (refinedDenominator 57 1 a l))
    apply RingHom.ext
    intro z
    change ordinaryReduction a l (ordinarySplitting a l _) = _
    rw [ordinarySplitting_base, splittingBase_reduction]
    rfl
  exact RingHom.congr_fun he x

theorem projectedSplitting_reduction (a : Fin 4) (l : Fin 3) (x : RefinedRing 57 1 a l) :
    chartReduction a l (thickProjection a l (ordinarySplitting a l x.val)) = x := by
  rw [projection_reduction, ordinarySplitting_reduction, closedProjection_val]

/-- An actual splitting on the genuine homogeneous-localization ring,
constructed from the already chosen original cone splitting. -/
def projectiveSplitting (a : Fin 4) (l : Fin 3) :
    RefinedRing 57 1 a l →+* ChartRing a l where
  toFun x := thickProjection a l (ordinarySplitting a l x.val)
  map_zero' := by rw [HomogeneousLocalization.val_zero, map_zero, map_zero]
  map_one' := by
    rw [HomogeneousLocalization.val_one, map_one]
    simpa only [HomogeneousLocalization.val_one] using thickProjection_val a l 1
  map_add' x y := by rw [HomogeneousLocalization.val_add, map_add, map_add]
  map_mul' x y := by
    rw [HomogeneousLocalization.val_mul, map_mul]
    apply thickProjection_mul a l
    · rw [ordinarySplitting_reduction, projectedSplitting_reduction]
    · rw [ordinarySplitting_reduction, projectedSplitting_reduction]

theorem projectiveSplitting_reduction (a : Fin 4) (l : Fin 3) (x : RefinedRing 57 1 a l) :
    chartReduction a l (projectiveSplitting a l x) = x := projectedSplitting_reduction a l x

end CycleQ2LiteralProjectiveSplittings

end

#print axioms CycleQ2LiteralProjectiveSplittings.originalThickMap_reduction
#print axioms CycleQ2LiteralProjectiveSplittings.ordinarySplitting_reduction
#print axioms CycleQ2LiteralProjectiveSplittings.projectiveSplitting_reduction
