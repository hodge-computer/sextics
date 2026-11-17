import Proposal.GeometricLiteralProjectiveSplittings

/-!
# The projected splittings preserve the actual complex coefficients

Both scalar structures are induced by the actual degree-zero coefficient
rings and the actual Proj structure morphisms. The existing chosen cone
splittings, their ordinary extensions, and their native projective
projections preserve these coefficients. Thus the projected splittings
are genuine complex-algebra splittings of the original chart reductions.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralProjectiveComplexSplittings

open CategoryTheory AlgebraicGeometry HomogeneousLocalization
  CycleQ2GeometricSeedNormalIdeals CycleQ2CartierSurfaceGrading CycleQ2ProjectiveCartierIdeal
  CycleQ2LiteralGradedDeformation CycleQ2LiteralGradedDeformationEquiv
  CycleQ2LiteralGradedReduction CycleQ2LiteralProjectiveDeformation
  CycleQ2LiteralProjectiveProjection CycleQ2LiteralProjectiveSplittings
  CycleQ2LiteralCartierOverlapSplittings CycleQ2LiteralCartierSplittings

attribute [local instance] CycleQ2LiteralCartierTransitionBinding.cubicSelfModule
  CycleQ2LiteralCartierTransitionBinding.cubicOppositeModule
  CycleQ2LiteralCartierTransitionBinding.cubicCentralScalar
  CycleQ2LiteralCartierTransitionBinding.cubicSmulCommClass
  CycleQ2GeometricSurfaceFirstOrder.reducedAlgebra
  CycleQ2GeometricKernelLocalization.localReductionAlgebra
  CycleQ2LiteralCartierSplittings.complexReductionTower
  CycleQ2LiteralCartierOverlapSplittings.baseReductionAlgebra

def thickCoefficient (a : Fin 4) (l : Fin 3) : ℂ →+* ChartRing a l :=
  (fromZeroRingHom deformationGrade (Submonoid.powers (chartDenominator a l))).comp
    (algebraMap ℂ (deformationGrade 0))

def closedCoefficient (a : Fin 4) (l : Fin 3) : ℂ →+* RefinedRing 57 1 a l :=
  CycleQ2GeometricSurfaceCoefficients.basicOpenCoefficient 57 1 (refinedDenominator 57 1 a l)

def deformationToComplex : projectiveDeformation ⟶ Spec (CommRingCat.of ℂ) :=
  Proj.toSpecZero deformationGrade ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (deformationGrade 0)))

/-- The chosen deformed coefficients are exactly those of its Proj map. -/
theorem chart_deformationToComplex (a : Fin 4) (l : Fin 3) :
    Proj.awayι deformationGrade (chartDenominator a l) (chartDenominator_homogeneous a l)
        (by omega) ≫ deformationToComplex = Spec.map (CommRingCat.ofHom (thickCoefficient a l)) := by
  rw [deformationToComplex, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  rfl

theorem thickCoefficient_val (a : Fin 4) (l : Fin 3) (c : ℂ) :
    (thickCoefficient a l c).val = algebraMap ℂ (OrdinaryThick a l) c := rfl

theorem closedCoefficient_val (a : Fin 4) (l : Fin 3) (c : ℂ) :
    (closedCoefficient a l c).val = algebraMap ℂ (OrdinaryClosed a l) c := rfl

theorem originalThickMap_complex (a : Fin 4) (l : Fin 3) (c : ℂ) :
    originalThickMap a l (algebraMap ℂ (Thick {a}) c) =
      algebraMap ℂ (OrdinaryThick a l) c := by
  rw [IsScalarTower.algebraMap_apply ℂ ThickBase (Thick {a}), originalThickMap_base]
  change algebraMap GradedDeformation (OrdinaryThick a l)
    (fromOriginal (algebraMap ℂ ThickBase c)) = _
  rw [fromOriginal.commutes]
  exact (IsScalarTower.algebraMap_apply ℂ GradedDeformation (OrdinaryThick a l) c).symm

theorem splittingBase_complex (a : Fin 4) (l : Fin 3) (c : ℂ) :
    CycleQ2LiteralProjectiveSplittings.splittingBase a l (algebraMap ℂ (SurfaceRing 57 1) c) =
      algebraMap ℂ (OrdinaryThick a l) c := by
  change originalThickMap a l (splitting {a} (by simp)
    (algebraMap ClosedBase (ClosedRing {a}) (closedAlgEquiv.symm (algebraMap ℂ (SurfaceRing 57 1) c)))) = _
  rw [closedAlgEquiv.symm.commutes,
    ← IsScalarTower.algebraMap_apply ℂ ClosedBase (ClosedRing {a}),
    (splitting {a} (by simp)).commutes, originalThickMap_complex]

theorem ordinarySplitting_complex (a : Fin 4) (l : Fin 3) (c : ℂ) :
    ordinarySplitting a l (algebraMap ℂ (OrdinaryClosed a l) c) =
      algebraMap ℂ (OrdinaryThick a l) c := by
  rw [IsScalarTower.algebraMap_apply ℂ (SurfaceRing 57 1) (OrdinaryClosed a l),
    ordinarySplitting_base, splittingBase_complex]

/-- The native splitting preserves the coefficients of the actual two
projective structure morphisms, with no scalar structure postulated. -/
theorem projectiveSplitting_complex (a : Fin 4) (l : Fin 3) (c : ℂ) :
    projectiveSplitting a l (closedCoefficient a l c) = thickCoefficient a l c := by
  change thickProjection a l (ordinarySplitting a l (closedCoefficient a l c).val) = _
  rw [closedCoefficient_val, ordinarySplitting_complex, ← thickCoefficient_val]
  exact thickProjection_val a l _

theorem chartReduction_complex (a : Fin 4) (l : Fin 3) (c : ℂ) :
    chartReduction a l (thickCoefficient a l c) = closedCoefficient a l c := by
  apply HomogeneousLocalization.val_injective
  rw [← ordinaryReduction_val, thickCoefficient_val, closedCoefficient_val,
    IsScalarTower.algebraMap_apply ℂ GradedDeformation (OrdinaryThick a l), ordinaryReduction_base,
    CycleQ2LiteralGradedReduction.reduction.commutes]
  exact (IsScalarTower.algebraMap_apply ℂ (SurfaceRing 57 1) (OrdinaryClosed a l) c).symm

local instance thickComplexAlgebra (a : Fin 4) (l : Fin 3) : Algebra ℂ (ChartRing a l) :=
  (thickCoefficient a l).toAlgebra

local instance closedComplexAlgebra (a : Fin 4) (l : Fin 3) : Algebra ℂ (RefinedRing 57 1 a l) :=
  (closedCoefficient a l).toAlgebra

def chartReductionAlgHom (a : Fin 4) (l : Fin 3) : ChartRing a l →ₐ[ℂ] RefinedRing 57 1 a l where
  __ := chartReduction a l
  commutes' := chartReduction_complex a l

def projectiveSplittingAlgHom (a : Fin 4) (l : Fin 3) : RefinedRing 57 1 a l →ₐ[ℂ] ChartRing a l where
  __ := projectiveSplitting a l
  commutes' := projectiveSplitting_complex a l

theorem projectiveSplittingAlgHom_reduction (a : Fin 4) (l : Fin 3) (x : RefinedRing 57 1 a l) :
    chartReductionAlgHom a l (projectiveSplittingAlgHom a l x) = x :=
  projectiveSplitting_reduction a l x

end CycleQ2LiteralProjectiveComplexSplittings

end

#print axioms CycleQ2LiteralProjectiveComplexSplittings.chart_deformationToComplex
#print axioms CycleQ2LiteralProjectiveComplexSplittings.projectiveSplitting_complex
#print axioms CycleQ2LiteralProjectiveComplexSplittings.projectiveSplittingAlgHom_reduction
