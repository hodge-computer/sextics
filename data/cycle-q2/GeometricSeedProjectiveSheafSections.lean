import Proposal.GeometricSeedChartModuleRestriction
import Proposal.GeometricSeedOverlapSectionModels

/-!
# The original projective sheaf maps on actual overlap sections

The native sections of the existing projective image and orbit-dual
sheaves are compared with the explicit overlap modules. All four
comparisons are linear over the actual projective overlap section ring.
The source actions are the ordinary structure-sheaf actions restricted
through the actual chart inclusions.

The original projectiveImageDualIso commutes with these comparisons on
every section. Transporting the established matrix-image transition
therefore gives the positive degree-four square for these original
projective sheaf maps. Naturality of transitions on smaller opens,
their triple-overlap descent, and the global internal-Hom identification
remain separate obligations.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedProjectiveSheafSections

open CategoryTheory AlgebraicGeometry
open CycleQ2GeometricSurfaceDehomogenizedCharts
  CycleQ2SeedProjectiveImageChart CycleQ2SeedProjectiveImageTwist
  CycleQ2SeedProjectiveImageCocycle CycleQ2SeedProjectiveImageRestriction
  CycleQ2SeedProjectiveImageCompatibility CycleQ2SeedProjectiveLocalizedDuality
  CycleQ2SeedProjectiveChartOverlaps CycleQ2SeedChartSectionScalars
  CycleQ2SeedChartModuleRestriction CycleQ2SeedOverlapSectionModels

local instance overlapCommRing (i j : Fin 3) : CommRing (OverlapSections i j) :=
  inferInstance

def leftImageSectionModule (i j : Fin 3) :
    Module (OverlapSections i j) Γ(projectiveImageSheaf i, leftNativeOverlap i j) :=
  chartRestrictedModule (coordinateAffineChart 57 1 i.succ)
    (leftChartOver i j) (affineImageSheaf i)

def leftDualSectionModule (i j : Fin 3) :
    Module (OverlapSections i j) Γ(projectiveOrbitDualSheaf i, leftNativeOverlap i j) :=
  chartRestrictedModule (coordinateAffineChart 57 1 i.succ)
    (leftChartOver i j) (affineOrbitDualSheaf i)

def rightImageSectionModule (i j : Fin 3) :
    Module (OverlapSections i j) Γ(projectiveImageSheaf j, rightNativeOverlap i j) :=
  chartRestrictedModule (coordinateAffineChart 57 1 j.succ)
    (rightChartOver i j) (affineImageSheaf j)

def rightDualSectionModule (i j : Fin 3) :
    Module (OverlapSections i j) Γ(projectiveOrbitDualSheaf j, rightNativeOverlap i j) :=
  chartRestrictedModule (coordinateAffineChart 57 1 j.succ)
    (rightChartOver i j) (affineOrbitDualSheaf j)

def leftProjectiveImageEquiv (i j : Fin 3) :
    letI := leftImageSectionModule i j
    Γ(projectiveImageSheaf i, leftNativeOverlap i j) ≃ₗ[OverlapSections i j]
      Regrading.Image (leftData i j) := by
  letI := leftImageSectionModule i j
  letI : Module (OverlapSections i j) Γ(affineImageSheaf i, leftChartOpen i j) :=
    chartSectionsModule (coordinateAffineChart 57 1 i.succ)
      (leftChartOver i j) (affineImageSheaf i)
  let e : Γ(projectiveImageSheaf i, leftNativeOverlap i j) ≃ₗ[OverlapSections i j]
      Γ(affineImageSheaf i, leftChartOpen i j) :=
    chartRestrictionEquiv (coordinateAffineChart 57 1 i.succ)
      (leftChartOver i j) (affineImageSheaf i)
  exact e.trans (leftImageModel i j)

def leftProjectiveDualEquiv (i j : Fin 3) :
    letI := leftDualSectionModule i j
    Γ(projectiveOrbitDualSheaf i, leftNativeOverlap i j) ≃ₗ[OverlapSections i j]
      LeftOverlapDual i j := by
  letI := leftDualSectionModule i j
  letI : Module (OverlapSections i j) Γ(affineOrbitDualSheaf i, leftChartOpen i j) :=
    chartSectionsModule (coordinateAffineChart 57 1 i.succ)
      (leftChartOver i j) (affineOrbitDualSheaf i)
  let e : Γ(projectiveOrbitDualSheaf i, leftNativeOverlap i j) ≃ₗ[OverlapSections i j]
      Γ(affineOrbitDualSheaf i, leftChartOpen i j) :=
    chartRestrictionEquiv (coordinateAffineChart 57 1 i.succ)
      (leftChartOver i j) (affineOrbitDualSheaf i)
  exact e.trans (leftDualModel i j)

def rightProjectiveImageEquiv (i j : Fin 3) :
    letI := rightImageSectionModule i j
    Γ(projectiveImageSheaf j, rightNativeOverlap i j) ≃ₗ[OverlapSections i j]
      Regrading.Image (rightData i j) := by
  letI := rightImageSectionModule i j
  letI : Module (OverlapSections i j) Γ(affineImageSheaf j, rightChartOpen i j) :=
    chartSectionsModule (coordinateAffineChart 57 1 j.succ)
      (rightChartOver i j) (affineImageSheaf j)
  let e : Γ(projectiveImageSheaf j, rightNativeOverlap i j) ≃ₗ[OverlapSections i j]
      Γ(affineImageSheaf j, rightChartOpen i j) :=
    chartRestrictionEquiv (coordinateAffineChart 57 1 j.succ)
      (rightChartOver i j) (affineImageSheaf j)
  exact e.trans (rightImageModel i j)

def rightProjectiveDualEquiv (i j : Fin 3) :
    letI := rightDualSectionModule i j
    Γ(projectiveOrbitDualSheaf j, rightNativeOverlap i j) ≃ₗ[OverlapSections i j]
      RightOverlapDual i j := by
  letI := rightDualSectionModule i j
  letI : Module (OverlapSections i j) Γ(affineOrbitDualSheaf j, rightChartOpen i j) :=
    chartSectionsModule (coordinateAffineChart 57 1 j.succ)
      (rightChartOver i j) (affineOrbitDualSheaf j)
  let e : Γ(projectiveOrbitDualSheaf j, rightNativeOverlap i j) ≃ₗ[OverlapSections i j]
      Γ(affineOrbitDualSheaf j, rightChartOpen i j) :=
    chartRestrictionEquiv (coordinateAffineChart 57 1 j.succ)
      (rightChartOver i j) (affineOrbitDualSheaf j)
  exact e.trans (rightDualModel i j)

/-- The actual left projective sheaf isomorphism has the proved literal
overlap duality as its model, on every native overlap section. -/
theorem leftProjective_naturality (i j : Fin 3)
    (s : Γ(projectiveImageSheaf i, leftNativeOverlap i j)) :
    leftProjectiveDualEquiv i j
        ((projectiveImageDualIso i).hom.app (leftNativeOverlap i j) s) =
      Regrading.imageDual (leftData i j) (leftProjectiveImageEquiv i j s) := by
  have h := chartRestrictionEquiv_naturality
    (coordinateAffineChart 57 1 i.succ) (leftChartOver i j) (affineImageDualIso i).hom s
  exact (congrArg (leftDualModel i j) h).trans
    (leftModel_naturality i j (chartRestrictionEquiv
      (coordinateAffineChart 57 1 i.succ) (leftChartOver i j) (affineImageSheaf i) s))

/-- The corresponding right-chart square uses the same ordered intersection. -/
theorem rightProjective_naturality (i j : Fin 3)
    (s : Γ(projectiveImageSheaf j, rightNativeOverlap i j)) :
    rightProjectiveDualEquiv i j
        ((projectiveImageDualIso j).hom.app (rightNativeOverlap i j) s) =
      Regrading.imageDual (rightData i j) (rightProjectiveImageEquiv i j s) := by
  have h := chartRestrictionEquiv_naturality
    (coordinateAffineChart 57 1 j.succ) (rightChartOver i j) (affineImageDualIso j).hom s
  exact (congrArg (rightDualModel i j) h).trans
    (rightModel_naturality i j (chartRestrictionEquiv
      (coordinateAffineChart 57 1 j.succ) (rightChartOver i j) (affineImageSheaf j) s))

/-- Transport the established matrix-image transition to native projective
sections. No sheaf descent or triple-overlap compatibility is asserted here. -/
def imageSectionTransition (i j : Fin 3) :
    letI := leftImageSectionModule i j
    letI := rightImageSectionModule i j
    Γ(projectiveImageSheaf i, leftNativeOverlap i j) ≃ₗ[OverlapSections i j]
      Γ(projectiveImageSheaf j, rightNativeOverlap i j) := by
  letI := leftImageSectionModule i j
  letI := rightImageSectionModule i j
  exact ((leftProjectiveImageEquiv i j).trans (imageTransition i j)).trans
    (rightProjectiveImageEquiv i j).symm

theorem imageSectionTransition_model (i j : Fin 3)
    (s : Γ(projectiveImageSheaf i, leftNativeOverlap i j)) :
    rightProjectiveImageEquiv i j (imageSectionTransition i j s) =
      imageTransition i j (leftProjectiveImageEquiv i j s) := by
  change rightProjectiveImageEquiv i j
      ((rightProjectiveImageEquiv i j).symm
        (imageTransition i j (leftProjectiveImageEquiv i j s))) = _
  exact LinearEquiv.apply_symm_apply _ _

/-- The original projective sheaf maps satisfy the positive degree-four
square on every native overlap section, as equality of entire functionals. -/
theorem projectiveImageDual_compatibility (i j : Fin 3)
    (s : Γ(projectiveImageSheaf i, leftNativeOverlap i j)) :
    rightProjectiveDualEquiv i j
        ((projectiveImageDualIso j).hom.app (rightNativeOverlap i j)
          (imageSectionTransition i j s)) =
      (ratioUnit i j : OverlapSections i j) ^ 4 •
        ((leftProjectiveDualEquiv i j
          ((projectiveImageDualIso i).hom.app (leftNativeOverlap i j) s)).comp
          (idealIdentification i j).symm.toLinearMap) := by
  rw [rightProjective_naturality, imageSectionTransition_model,
    imageDual_compatibility, leftProjective_naturality]

#print axioms leftProjectiveImageEquiv
#print axioms leftProjectiveDualEquiv
#print axioms rightProjectiveImageEquiv
#print axioms rightProjectiveDualEquiv
#print axioms leftProjective_naturality
#print axioms rightProjective_naturality
#print axioms projectiveImageDual_compatibility

end CycleQ2SeedProjectiveSheafSections
end
