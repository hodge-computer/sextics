import Proposal.GeometricLiteralProjectiveIntersectionSplittings

/-!
# Actual complex algebra structures and compatible intersection splittings

All coefficients come from the original degree-zero rings and the actual
Proj structure morphisms. The singleton extensions and their projections
preserve those coefficients on every finite intersection. Both restrictions
and the same chosen native splittings are genuine complex algebra maps.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralProjectiveIntersectionComplex

open CategoryTheory AlgebraicGeometry HomogeneousLocalization CycleQ2GeometricSeedNormalIdeals CycleQ2CartierSurfaceGrading
  CycleQ2LiteralGradedDeformation CycleQ2LiteralGradedDeformationEquiv
  CycleQ2LiteralGradedReduction CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveIntersectionKernel CycleQ2LiteralProjectiveIntersectionProjection
  CycleQ2LiteralProjectiveIntersectionRestrictions CycleQ2LiteralProjectiveIntersectionSplittings
  CycleQ2LiteralCartierOverlapSplittings

attribute [local instance] CycleQ2LiteralCartierTransitionBinding.cubicSelfModule
  CycleQ2LiteralCartierTransitionBinding.cubicOppositeModule
  CycleQ2LiteralCartierTransitionBinding.cubicCentralScalar
  CycleQ2LiteralCartierTransitionBinding.cubicSmulCommClass
  CycleQ2GeometricSurfaceFirstOrder.reducedAlgebra
  CycleQ2GeometricKernelLocalization.localReductionAlgebra
  CycleQ2LiteralCartierSplittings.complexReductionTower
  CycleQ2LiteralCartierOverlapSplittings.baseReductionAlgebra
  CycleQ2LiteralProjectiveIntersectionKernel.nativeReductionAlgebra

def thickCoefficient (s : Finset Vertex) : ℂ →+* ThickRing s :=
  (fromZeroRingHom deformationGrade (Submonoid.powers (thickProduct s))).comp
    (algebraMap ℂ (deformationGrade 0))

def closedCoefficient (s : Finset Vertex) : ℂ →+* CycleQ2LiteralProjectiveIntersections.ClosedRing s :=
  CycleQ2GeometricSurfaceCoefficients.basicOpenCoefficient 57 1 (closedProduct s)

theorem thickCoefficient_scheme (s : Finset Vertex) (hs : s.Nonempty) :
    Proj.awayι deformationGrade (thickProduct s) (thickProduct_homogeneous s) (productDegree_pos hs) ≫
        CycleQ2LiteralProjectiveComplexSplittings.deformationToComplex =
      Spec.map (CommRingCat.ofHom (thickCoefficient s)) := by
  rw [CycleQ2LiteralProjectiveComplexSplittings.deformationToComplex,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  rfl

theorem closedCoefficient_scheme (s : Finset Vertex) (hs : s.Nonempty) :
    Proj.awayι (surfaceGrade 57 1) (closedProduct s) (closedProduct_homogeneous s) (productDegree_pos hs) ≫
        CycleQ2GeometricSurfaceCoefficients.projectiveToComplex 57 1 =
      Spec.map (CommRingCat.ofHom (closedCoefficient s)) :=
  CycleQ2GeometricSurfaceCoefficients.awayι_projectiveToComplex 57 1 (closedProduct s)
    (closedProduct_homogeneous s) (productDegree_pos hs)

theorem thickCoefficient_val (s : Finset Vertex) (c : ℂ) :
    (thickCoefficient s c).val = algebraMap ℂ (ThickCone s) c := rfl

theorem closedCoefficient_val (s : Finset Vertex) (c : ℂ) :
    (closedCoefficient s c).val = algebraMap ℂ (ClosedCone s) c := rfl

theorem originalThickMap_complex (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) (c : ℂ) :
    originalThickMap s a ha (algebraMap ℂ (CycleQ2LiteralCartierSplittings.Thick {a}) c) =
      algebraMap ℂ (ThickCone s) c := by
  rw [IsScalarTower.algebraMap_apply ℂ ThickBase (CycleQ2LiteralCartierSplittings.Thick {a}), originalThickMap_base]
  change algebraMap GradedDeformation (ThickCone s) (fromOriginal (algebraMap ℂ ThickBase c)) = _
  rw [fromOriginal.commutes]
  exact (IsScalarTower.algebraMap_apply ℂ GradedDeformation (ThickCone s) c).symm

theorem splittingBase_complex (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) (c : ℂ) :
    CycleQ2LiteralProjectiveIntersectionSplittings.splittingBase s a ha (algebraMap ℂ (SurfaceRing 57 1) c) =
      algebraMap ℂ (ThickCone s) c := by
  change originalThickMap s a ha (CycleQ2LiteralCartierSplittings.splitting {a} (by simp)
    (algebraMap ClosedBase (CycleQ2LiteralCartierSplittings.ClosedRing {a})
      (closedAlgEquiv.symm (algebraMap ℂ (SurfaceRing 57 1) c)))) = _
  rw [closedAlgEquiv.symm.commutes,
    ← IsScalarTower.algebraMap_apply ℂ ClosedBase (CycleQ2LiteralCartierSplittings.ClosedRing {a}),
    (CycleQ2LiteralCartierSplittings.splitting {a} (by simp)).commutes, originalThickMap_complex]

theorem ordinarySplitting_complex (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) (c : ℂ) :
    ordinarySplitting s a ha (algebraMap ℂ (ClosedCone s) c) = algebraMap ℂ (ThickCone s) c := by
  rw [IsScalarTower.algebraMap_apply ℂ (SurfaceRing 57 1) (ClosedCone s),
    ordinarySplitting_base, splittingBase_complex]

theorem projectiveSplitting_complex (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) (c : ℂ) :
    projectiveSplitting s a ha (closedCoefficient s c) = thickCoefficient s c := by
  change thickProjection s (ordinarySplitting s a ha (closedCoefficient s c).val) = _
  rw [closedCoefficient_val, ordinarySplitting_complex, ← thickCoefficient_val]
  exact thickProjection_val s _

theorem nativeReduction_complex (s : Finset Vertex) (c : ℂ) :
    nativeReduction s (thickCoefficient s c) = closedCoefficient s c := by
  apply HomogeneousLocalization.val_injective
  rw [← ordinaryReduction_val, thickCoefficient_val, closedCoefficient_val,
    IsScalarTower.algebraMap_apply ℂ GradedDeformation (ThickCone s),
    CycleQ2LiteralProjectiveIntersectionSplittings.ordinaryReduction_base,
    CycleQ2LiteralGradedReduction.reduction.commutes]
  exact (IsScalarTower.algebraMap_apply ℂ (SurfaceRing 57 1) (ClosedCone s) c).symm

local instance thickComplexAlgebra (s : Finset Vertex) : Algebra ℂ (ThickRing s) :=
  (thickCoefficient s).toAlgebra

local instance closedComplexAlgebra (s : Finset Vertex) :
    Algebra ℂ (CycleQ2LiteralProjectiveIntersections.ClosedRing s) := (closedCoefficient s).toAlgebra

local instance thickComplexSMul (s : Finset Vertex) : SMul ℂ (ThickRing s) :=
  (thickComplexAlgebra s).toSMul

local instance closedComplexSMul (s : Finset Vertex) :
    SMul ℂ (CycleQ2LiteralProjectiveIntersections.ClosedRing s) := (closedComplexAlgebra s).toSMul

local instance thickComplexModule (s : Finset Vertex) : Module ℂ (ThickRing s) :=
  @Algebra.toModule ℂ (ThickRing s) _ _ (thickComplexAlgebra s)

local instance closedComplexModule (s : Finset Vertex) :
    Module ℂ (CycleQ2LiteralProjectiveIntersections.ClosedRing s) :=
  @Algebra.toModule ℂ (CycleQ2LiteralProjectiveIntersections.ClosedRing s) _ _ (closedComplexAlgebra s)

local instance complexReductionTower (s : Finset Vertex) :
    IsScalarTower ℂ (ThickRing s) (CycleQ2LiteralProjectiveIntersections.ClosedRing s) :=
  IsScalarTower.of_algebraMap_eq (fun c => (nativeReduction_complex s c).symm)

def nativeReductionAlgHom (s : Finset Vertex) :
    ThickRing s →ₐ[ℂ] CycleQ2LiteralProjectiveIntersections.ClosedRing s where
  __ := nativeReduction s
  commutes' := nativeReduction_complex s

def projectiveSplittingAlgHom (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) :
    CycleQ2LiteralProjectiveIntersections.ClosedRing s →ₐ[ℂ] ThickRing s where
  __ := projectiveSplitting s a ha
  commutes' := projectiveSplitting_complex s a ha

theorem projectiveSplittingAlgHom_reduction (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a)
    (x : CycleQ2LiteralProjectiveIntersections.ClosedRing s) :
    nativeReductionAlgHom s (projectiveSplittingAlgHom s a ha x) = x := projectiveSplitting_reduction s a ha x

def thickRestrictionAlgHom {s t : Finset Vertex} (hst : s ⊆ t) : ThickRing s →ₐ[ℂ] ThickRing t where
  __ := CycleQ2LiteralProjectiveIntersectionRestrictions.thickRestriction hst
  commutes' c := HomogeneousLocalization.awayMap_fromZeroRingHom deformationGrade
    (thickProduct_homogeneous (t \ s)) (thickProduct_factor hst) (algebraMap ℂ (deformationGrade 0) c)

def closedRestrictionAlgHom {s t : Finset Vertex} (hst : s ⊆ t) :
    CycleQ2LiteralProjectiveIntersections.ClosedRing s →ₐ[ℂ] CycleQ2LiteralProjectiveIntersections.ClosedRing t where
  __ := CycleQ2LiteralProjectiveIntersectionRestrictions.closedRestriction hst
  commutes' c := HomogeneousLocalization.awayMap_fromZeroRingHom (surfaceGrade 57 1)
    (closedProduct_homogeneous (t \ s)) (closedProduct_factor hst) (algebraMap ℂ (surfaceGrade 57 1 0) c)

theorem projectiveSplittingAlgHom_restrict {s t : Finset Vertex} (hst : s ⊆ t)
    (a : Fin 4) (ha : Admissible s a) (x : CycleQ2LiteralProjectiveIntersections.ClosedRing s) :
    thickRestrictionAlgHom hst (projectiveSplittingAlgHom s a ha x) =
      projectiveSplittingAlgHom t a (admissible_mono hst ha) (closedRestrictionAlgHom hst x) :=
  projectiveSplitting_restrict hst a ha x

end CycleQ2LiteralProjectiveIntersectionComplex

end

#print axioms CycleQ2LiteralProjectiveIntersectionComplex.projectiveSplittingAlgHom_reduction
#print axioms CycleQ2LiteralProjectiveIntersectionComplex.projectiveSplittingAlgHom_restrict
