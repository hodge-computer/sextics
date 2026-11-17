import Proposal.GeometricLiteralProjectiveIntersectionSplittings

/-!
# The original twelve chart splittings restrict to the common intersections

The source rings and splittings are exactly those already constructed
on the original twelve charts. Their actual restriction maps to a finite
intersection commute with reduction, epsilon coefficients, and projection.
The extended singleton splitting is the restriction of the original
projective splitting, using uniqueness of ordinary localization first.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralProjectiveVertexRestrictions

open HomogeneousLocalization CycleQ2GeometricSeedNormalIdeals CycleQ2ProjectiveCartierIdeal
  CycleQ2CartierSurfaceGrading CycleQ2LiteralGradedDeformation
  CycleQ2LiteralGradedDeformationEquiv CycleQ2LiteralGradedReduction
  CycleQ2LiteralProjectiveDeformation CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveIntersectionProjection CycleQ2LiteralProjectiveIntersectionRestrictions
  CycleQ2LiteralProjectiveIntersectionSplittings CycleQ2GradedLocalizationProjection

attribute [local instance] CycleQ2LiteralCartierTransitionBinding.cubicSelfModule
  CycleQ2LiteralCartierTransitionBinding.cubicOppositeModule
  CycleQ2LiteralCartierTransitionBinding.cubicCentralScalar
  CycleQ2LiteralCartierTransitionBinding.cubicSmulCommClass
  CycleQ2GeometricSurfaceFirstOrder.reducedAlgebra
  CycleQ2GeometricKernelLocalization.localReductionAlgebra
  CycleQ2LiteralCartierSplittings.complexReductionTower
  CycleQ2LiteralCartierOverlapSplittings.baseReductionAlgebra

theorem thickVertex_factor (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) :
    thickProduct s = chartDenominator v.1 v.2 * thickProduct (s.erase v) :=
  (Finset.mul_prod_erase s (fun w : Vertex => chartDenominator w.1 w.2) hv).symm

theorem closedVertex_factor (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) :
    closedProduct s = refinedDenominator 57 1 v.1 v.2 * closedProduct (s.erase v) :=
  (Finset.mul_prod_erase s (fun w : Vertex => refinedDenominator 57 1 w.1 w.2) hv).symm

def thickVertexConeRestriction (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) :
    CycleQ2LiteralProjectiveProjection.OrdinaryThick v.1 v.2 →ₐ[GradedDeformation] ThickCone s :=
  CycleQ2GeometricKernelLocalization.thickRestriction GradedDeformation
    ⟨thickProduct (s.erase v),thickVertex_factor s v hv⟩

def closedVertexConeRestriction (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) :
    CycleQ2LiteralProjectiveProjection.OrdinaryClosed v.1 v.2 →ₐ[SurfaceRing 57 1] ClosedCone s :=
  CycleQ2GeometricKernelLocalization.thickRestriction (SurfaceRing 57 1)
    ⟨closedProduct (s.erase v),closedVertex_factor s v hv⟩

def thickVertexRestriction (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) :
    ChartRing v.1 v.2 →+* ThickRing s :=
  HomogeneousLocalization.awayMap deformationGrade (thickProduct_homogeneous (s.erase v)) (thickVertex_factor s v hv)

def closedVertexRestriction (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) :
    RefinedRing 57 1 v.1 v.2 →+* ClosedRing s :=
  HomogeneousLocalization.awayMap (surfaceGrade 57 1) (closedProduct_homogeneous (s.erase v))
    (closedVertex_factor s v hv)

theorem thickVertexRestriction_val (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) (x : ChartRing v.1 v.2) :
    (thickVertexRestriction s v hv x).val = thickVertexConeRestriction s v hv x.val :=
  homogeneousRestriction_val deformationGrade (thickProduct_homogeneous (s.erase v))
    (thickVertex_factor s v hv) (thickVertexConeRestriction s v hv) x

theorem closedVertexRestriction_val (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) (x : RefinedRing 57 1 v.1 v.2) :
    (closedVertexRestriction s v hv x).val = closedVertexConeRestriction s v hv x.val :=
  homogeneousRestriction_val (surfaceGrade 57 1) (closedProduct_homogeneous (s.erase v))
    (closedVertex_factor s v hv) (closedVertexConeRestriction s v hv) x

theorem thickProjection_vertex (s : Finset Vertex) (v : Vertex) (hv : v ∈ s)
    (x : CycleQ2LiteralProjectiveProjection.OrdinaryThick v.1 v.2) :
    thickProjection s (thickVertexConeRestriction s v hv x) =
      thickVertexRestriction s v hv (CycleQ2LiteralProjectiveProjection.thickProjection v.1 v.2 x) :=
  degreeZero_naturality deformationGrade (chartDenominator_homogeneous v.1 v.2)
    (thickProduct_homogeneous (s.erase v)) (thickVertex_factor s v hv)
    (thickProduct_homogeneous s) (thickVertexConeRestriction s v hv) x

theorem ordinaryReduction_vertex (s : Finset Vertex) (v : Vertex) (hv : v ∈ s)
    (x : CycleQ2LiteralProjectiveProjection.OrdinaryThick v.1 v.2) :
    ordinaryReduction s (thickVertexConeRestriction s v hv x) =
      closedVertexConeRestriction s v hv (CycleQ2LiteralProjectiveProjection.ordinaryReduction v.1 v.2 x) := by
  have he : (ordinaryReduction s).comp (thickVertexConeRestriction s v hv).toRingHom =
      (closedVertexConeRestriction s v hv).toRingHom.comp
        (CycleQ2LiteralProjectiveProjection.ordinaryReduction v.1 v.2) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (chartDenominator v.1 v.2))
    apply RingHom.ext
    intro z
    change ordinaryReduction s (thickVertexConeRestriction s v hv _) = closedVertexConeRestriction s v hv _
    rw [(thickVertexConeRestriction s v hv).commutes,
      CycleQ2LiteralProjectiveIntersectionSplittings.ordinaryReduction_base,
      CycleQ2LiteralProjectiveSplittings.ordinaryReduction_base,
      (closedVertexConeRestriction s v hv).commutes]
  exact RingHom.congr_fun he x

theorem nativeReduction_vertex (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) (x : ChartRing v.1 v.2) :
    nativeReduction s (thickVertexRestriction s v hv x) = closedVertexRestriction s v hv (chartReduction v.1 v.2 x) := by
  apply HomogeneousLocalization.val_injective
  rw [← ordinaryReduction_val, thickVertexRestriction_val, ordinaryReduction_vertex,
    CycleQ2LiteralProjectiveProjection.ordinaryReduction_val, closedVertexRestriction_val]

theorem epsilon_vertex (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) :
    thickVertexRestriction s v hv (CycleQ2LiteralProjectiveKernel.chartEpsilon v.1 v.2) =
      CycleQ2LiteralProjectiveIntersectionKernel.nativeEpsilon s :=
  HomogeneousLocalization.awayMap_fromZeroRingHom deformationGrade
    (thickProduct_homogeneous (s.erase v)) (thickVertex_factor s v hv) _

theorem epsilonCoefficient_vertex (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) (x : RefinedRing 57 1 v.1 v.2) :
    thickVertexRestriction s v hv (CycleQ2LiteralProjectiveKernel.epsilonCoefficient v.1 v.2 x) =
      CycleQ2LiteralProjectiveIntersectionKernel.epsilonCoefficient s (closedVertexRestriction s v hv x) := by
  obtain ⟨y,rfl⟩ := chartReduction_surjective v.1 v.2 x
  rw [CycleQ2LiteralProjectiveKernel.epsilonCoefficient_of_reduction, map_mul, epsilon_vertex,
    ← nativeReduction_vertex, CycleQ2LiteralProjectiveIntersectionKernel.epsilonCoefficient_of_reduction]

theorem originalThickMap_vertex (s : Finset Vertex) (v : Vertex) (hv : v ∈ s)
    (x : CycleQ2LiteralCartierSplittings.Thick {v.1}) :
    thickVertexConeRestriction s v hv (CycleQ2LiteralProjectiveSplittings.originalThickMap v.1 v.2 x) =
      originalThickMap s v.1 ⟨v.2,hv⟩ x := by
  have he : (thickVertexConeRestriction s v hv).toRingHom.comp
      (CycleQ2LiteralProjectiveSplittings.originalThickMap v.1 v.2) = originalThickMap s v.1 ⟨v.2,hv⟩ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (CycleQ2LiteralCartierOverlapSplittings.thickDenominator {v.1}))
    apply RingHom.ext
    intro z
    change thickVertexConeRestriction s v hv (CycleQ2LiteralProjectiveSplittings.originalThickMap v.1 v.2 _) =
      originalThickMap s v.1 ⟨v.2,hv⟩ _
    rw [CycleQ2LiteralProjectiveSplittings.originalThickMap_base, originalThickMap_base]
    exact (thickVertexConeRestriction s v hv).commutes (fromOriginal z)
  exact RingHom.congr_fun he x

theorem splittingBase_vertex (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) (x : SurfaceRing 57 1) :
    thickVertexConeRestriction s v hv (CycleQ2LiteralProjectiveSplittings.splittingBase v.1 v.2 x) =
      splittingBase s v.1 ⟨v.2,hv⟩ x := originalThickMap_vertex s v hv _

theorem ordinarySplitting_vertex (s : Finset Vertex) (v : Vertex) (hv : v ∈ s)
    (x : CycleQ2LiteralProjectiveProjection.OrdinaryClosed v.1 v.2) :
    thickVertexConeRestriction s v hv (CycleQ2LiteralProjectiveSplittings.ordinarySplitting v.1 v.2 x) =
      ordinarySplitting s v.1 ⟨v.2,hv⟩ (closedVertexConeRestriction s v hv x) := by
  have he : (thickVertexConeRestriction s v hv).toRingHom.comp
        (CycleQ2LiteralProjectiveSplittings.ordinarySplitting v.1 v.2) =
      (ordinarySplitting s v.1 ⟨v.2,hv⟩).comp (closedVertexConeRestriction s v hv).toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (refinedDenominator 57 1 v.1 v.2))
    apply RingHom.ext
    intro z
    change thickVertexConeRestriction s v hv (CycleQ2LiteralProjectiveSplittings.ordinarySplitting v.1 v.2 _) =
      ordinarySplitting s v.1 ⟨v.2,hv⟩ (closedVertexConeRestriction s v hv _)
    rw [CycleQ2LiteralProjectiveSplittings.ordinarySplitting_base, (closedVertexConeRestriction s v hv).commutes,
      ordinarySplitting_base]
    exact splittingBase_vertex s v hv z
  exact RingHom.congr_fun he x

/-- This identifies the new common-intersection map with the actual
previously checked native chart splitting, retaining its original choice. -/
theorem projectiveSplitting_vertex (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) (x : RefinedRing 57 1 v.1 v.2) :
    thickVertexRestriction s v hv (CycleQ2LiteralProjectiveSplittings.projectiveSplitting v.1 v.2 x) =
      projectiveSplitting s v.1 ⟨v.2,hv⟩ (closedVertexRestriction s v hv x) := by
  change thickVertexRestriction s v hv (CycleQ2LiteralProjectiveProjection.thickProjection v.1 v.2
      (CycleQ2LiteralProjectiveSplittings.ordinarySplitting v.1 v.2 x.val)) =
    thickProjection s (ordinarySplitting s v.1 ⟨v.2,hv⟩ (closedVertexRestriction s v hv x).val)
  rw [← thickProjection_vertex, ordinarySplitting_vertex, ← closedVertexRestriction_val]

end CycleQ2LiteralProjectiveVertexRestrictions

end

#print axioms CycleQ2LiteralProjectiveVertexRestrictions.epsilonCoefficient_vertex
#print axioms CycleQ2LiteralProjectiveVertexRestrictions.projectiveSplitting_vertex
