import Proposal.GeometricLiteralCartierIntersectionFactor
import Proposal.GeometricLiteralCartierProjectedCup

/-!
# The two original projective section projections are the same restriction

The old polynomial-preserving closed-ring equivalence and the actual
intersection transport commute with the genuine ordinary localization
map. The explicit homogeneous complement identifies the native map.
Projection naturality and the actual Proj section restriction then bind
projection after closed transport to restriction of the earlier original
projectSection. No new cohomology model or trace is introduced.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCartierProjectionBinding

open CategoryTheory AlgebraicGeometry HomogeneousLocalization
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
  CycleQ2CartierSurfaceGrading CycleQ2CartierHomogeneousCech CycleQ2CartierProjectiveCover
  CycleQ2GradedLocalizationProjection CycleQ2LiteralGradedReduction
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionProjection
  CycleQ2LiteralProjectiveIntersectionRestrictions CycleQ2LiteralConeIntersectionTransport
  CycleQ2LiteralCartierIntersectionFactor CycleQ2LiteralCartierTransitionBinding
  CycleQ2LiteralCartierOverlapSplittings

attribute [local instance] CycleQ2LiteralCartierTransitionBinding.cubicSelfModule
  CycleQ2LiteralCartierTransitionBinding.cubicOppositeModule
  CycleQ2LiteralCartierTransitionBinding.cubicCentralScalar
  CycleQ2LiteralCartierTransitionBinding.cubicSmulCommClass
  CycleQ2GeometricSurfaceFirstOrder.reducedAlgebra
  CycleQ2GeometricKernelLocalization.localReductionAlgebra
  CycleQ2LiteralCartierSplittings.complexReductionTower
  CycleQ2LiteralCartierOverlapSplittings.baseReductionAlgebra

def originalConeMap (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t) :
    CoverLocal 57 1 t →ₐ[SurfaceRing 57 1] ClosedCone s :=
  CycleQ2GeometricKernelLocalization.thickRestriction (SurfaceRing 57 1)
    ⟨complement s t ht, originalProduct_factor s t ht⟩

theorem originalConeMap_closedRingEquiv (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t)
    (x : OldClosed t) :
    originalConeMap s t ht (CycleQ2LiteralCartierSplittings.closedRingEquiv t x) = closedMap s t ht x := by
  have he : (originalConeMap s t ht).toRingHom.comp
      (CycleQ2LiteralCartierSplittings.closedRingEquiv t).toRingHom = (closedMap s t ht).toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (closedDenominator t))
    apply RingHom.ext
    intro z
    change originalConeMap s t ht (CycleQ2LiteralCartierSplittings.closedRingEquiv t _) = closedMap s t ht _
    rw [CycleQ2LiteralCartierCochainNaturality.closedRingEquiv_base,
      (originalConeMap s t ht).commutes, closedMap_base]
    rfl
  exact RingHom.congr_fun he x

def originalNativeMap (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t) :
    HomogeneousCoverLocal 57 1 t →+* ClosedRing s :=
  HomogeneousLocalization.awayMap (surfaceGrade 57 1) (complement_homogeneous s t ht) (originalProduct_factor s t ht)

theorem originalNativeMap_val (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t)
    (x : HomogeneousCoverLocal 57 1 t) :
    (originalNativeMap s t ht x).val = originalConeMap s t ht x.val :=
  homogeneousRestriction_val (surfaceGrade 57 1) (complement_homogeneous s t ht)
    (originalProduct_factor s t ht) (originalConeMap s t ht) x

theorem projection_closedMap (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t)
    (x : OldClosed t) :
    closedProjection s (closedMap s t ht x) = originalNativeMap s t ht
      (degreeZero (surfaceGrade 57 1) (coverProduct_mem_grade 57 1 t)
        (CycleQ2LiteralCartierSplittings.closedRingEquiv t x)) := by
  rw [← originalConeMap_closedRingEquiv]
  exact degreeZero_naturality (surfaceGrade 57 1) (coverProduct_mem_grade 57 1 t)
    (complement_homogeneous s t ht) (originalProduct_factor s t ht) (closedProduct_homogeneous s)
    (originalConeMap s t ht) _

theorem closedOpen_le_coverPatch (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t) :
    closedOpen s ≤ coverPatch 57 1 t :=
  Proj.basicOpen_mono (surfaceGrade 57 1) (coverProduct 57 1 t) (closedProduct s)
    ⟨complement s t ht, originalProduct_factor s t ht⟩

theorem originalNativeMap_sections (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t)
    (hs : s.Nonempty) (hnt : t.Nonempty) (x : HomogeneousCoverLocal 57 1 t) :
    (projectiveSurface 57 1).presheaf.map (homOfLE (closedOpen_le_coverPatch s t ht)).op
      (coverSectionsEquiv 57 1 t hnt x) = closedSectionsEquiv s hs (originalNativeMap s t ht x) :=
  congrArg (fun k => k x) (Proj.awayMap_awayToSection (surfaceGrade 57 1)
    (complement_homogeneous s t ht) (originalProduct_factor s t ht)).symm

theorem projectSection_closedMap (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t)
    (hs : s.Nonempty) (hnt : t.Nonempty) (x : OldClosed t) :
    closedSectionsEquiv s hs (closedProjection s (closedMap s t ht x)) =
      (projectiveSurface 57 1).presheaf.map (homOfLE (closedOpen_le_coverPatch s t ht)).op
        (CycleQ2LiteralCartierProjectedCup.projectSection t hnt
          (CycleQ2LiteralCartierSplittings.closedRingEquiv t x)) := by
  rw [projection_closedMap]
  exact (originalNativeMap_sections s t ht hs hnt _).symm

end CycleQ2LiteralCartierProjectionBinding

end

#print axioms CycleQ2LiteralCartierProjectionBinding.projection_closedMap
#print axioms CycleQ2LiteralCartierProjectionBinding.projectSection_closedMap
