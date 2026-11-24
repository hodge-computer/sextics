import Proposal.GeometricSeedAffineOpenSections
import Proposal.GeometricSeedAffineReconstruction
import Proposal.GeometricSeedProjectiveAffineOverlap
import Proposal.GeometricSeedOverlapTransitionModels

/-!
# Native sheaf comparisons for the actual projective overlap

The canonical affine-overlap top-section equivalence is composed with
the four previously fixed projective section models. This preserves the
native action of the actual overlap ring. Quasi-coherent reconstruction
then identifies the original restricted projective sheaves with the
associated sheaves of their literal image and ideal-dual modules.

Both comparison squares retain the restrictions of the original
projectiveImageDualIso. Their equality on global sections follows from
the two existing naturality squares, and the canonical counit lifts that
equality to the entire native sheaf square. No transition cocycle or
global internal-Hom identification is asserted by this module.

Source-only draft: no Lean elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedProjectiveOverlapComparisons

open CategoryTheory AlgebraicGeometry
open CycleQ2SurfaceCoordinateSections CycleQ2SeedProjectiveImageChart
  CycleQ2SeedProjectiveImageTwist CycleQ2SeedProjectiveImageRestriction
  CycleQ2SeedProjectiveLocalizedDuality CycleQ2SeedProjectiveSheafSections
  CycleQ2SeedAffineOpenSections CycleQ2SeedAffineReconstruction
  CycleQ2SeedProjectiveAffineOverlap CycleQ2SeedOverlapTransitionModels

def leftImageGlobalEquiv (i j : Fin 3) :
    globalSections (leftImageOverlap i j) ≃ₗ[OverlapSections i j]
      Regrading.Image (leftData i j) := by
  letI := leftImageSectionModule i j
  exact (topSectionEquiv (overlap_isAffineOpen i j)
    (pair_le_left 57 1 i.succ j.succ) (projectiveImageSheaf i)).trans
      (leftProjectiveImageEquiv i j)

def rightImageGlobalEquiv (i j : Fin 3) :
    globalSections (rightImageOverlap i j) ≃ₗ[OverlapSections i j]
      Regrading.Image (rightData i j) := by
  letI := rightImageSectionModule i j
  exact (topSectionEquiv (overlap_isAffineOpen i j)
    (pair_le_right 57 1 i.succ j.succ) (projectiveImageSheaf j)).trans
      (rightProjectiveImageEquiv i j)

def leftDualGlobalEquiv (i j : Fin 3) :
    globalSections (leftDualOverlap i j) ≃ₗ[OverlapSections i j]
      LeftOverlapDual i j := by
  letI := leftDualSectionModule i j
  exact (topSectionEquiv (overlap_isAffineOpen i j)
    (pair_le_left 57 1 i.succ j.succ) (projectiveOrbitDualSheaf i)).trans
      (leftProjectiveDualEquiv i j)

def rightDualGlobalEquiv (i j : Fin 3) :
    globalSections (rightDualOverlap i j) ≃ₗ[OverlapSections i j]
      RightOverlapDual i j := by
  letI := rightDualSectionModule i j
  exact (topSectionEquiv (overlap_isAffineOpen i j)
    (pair_le_right 57 1 i.succ j.succ) (projectiveOrbitDualSheaf j)).trans
      (rightProjectiveDualEquiv i j)

/-- The original left vertical morphism has the fixed literal model on
native global sections of the canonical affine overlap. -/
theorem leftGlobal_naturality (i j : Fin 3)
    (s : globalSections (leftImageOverlap i j)) :
    leftDualGlobalEquiv i j
        (((moduleSpecΓFunctor (R := OverlapSections i j)).map
          (leftOverlapDuality i j).hom).hom s) =
      Regrading.imageDual (leftData i j) (leftImageGlobalEquiv i j s) := by
  change leftProjectiveDualEquiv i j
      (topSectionEquiv (overlap_isAffineOpen i j)
        (pair_le_left 57 1 i.succ j.succ) (projectiveOrbitDualSheaf i)
        (((moduleSpecΓFunctor (R := OverlapSections i j)).map
          ((Scheme.Modules.restrictFunctor (overlapMap (overlap_isAffineOpen i j)
            (pair_le_left 57 1 i.succ j.succ))).map
              (projectiveImageDualIso i).hom)).hom s)) =
    Regrading.imageDual (leftData i j)
      (leftProjectiveImageEquiv i j
        (topSectionEquiv (overlap_isAffineOpen i j)
          (pair_le_left 57 1 i.succ j.succ) (projectiveImageSheaf i) s))
  rw [topSectionEquiv_naturality]
  exact leftProjective_naturality i j _

/-- The right comparison retains the same ordered projective overlap. -/
theorem rightGlobal_naturality (i j : Fin 3)
    (s : globalSections (rightImageOverlap i j)) :
    rightDualGlobalEquiv i j
        (((moduleSpecΓFunctor (R := OverlapSections i j)).map
          (rightOverlapDuality i j).hom).hom s) =
      Regrading.imageDual (rightData i j) (rightImageGlobalEquiv i j s) := by
  change rightProjectiveDualEquiv i j
      (topSectionEquiv (overlap_isAffineOpen i j)
        (pair_le_right 57 1 i.succ j.succ) (projectiveOrbitDualSheaf j)
        (((moduleSpecΓFunctor (R := OverlapSections i j)).map
          ((Scheme.Modules.restrictFunctor (overlapMap (overlap_isAffineOpen i j)
            (pair_le_right 57 1 i.succ j.succ))).map
              (projectiveImageDualIso j).hom)).hom s)) =
    Regrading.imageDual (rightData i j)
      (rightProjectiveImageEquiv i j
        (topSectionEquiv (overlap_isAffineOpen i j)
          (pair_le_right 57 1 i.succ j.succ) (projectiveImageSheaf j) s))
  rw [topSectionEquiv_naturality]
  exact rightProjective_naturality i j _

def leftImageComparison (i j : Fin 3) :
    leftImageOverlap i j ≅ leftImageModelSheaf i j :=
  comparisonIso (leftImageOverlap i j) (leftImageGlobalEquiv i j).toModuleIso

def rightImageComparison (i j : Fin 3) :
    rightImageOverlap i j ≅ rightImageModelSheaf i j :=
  comparisonIso (rightImageOverlap i j) (rightImageGlobalEquiv i j).toModuleIso

def leftDualComparison (i j : Fin 3) :
    leftDualOverlap i j ≅ leftDualModelSheaf i j :=
  comparisonIso (leftDualOverlap i j) (leftDualGlobalEquiv i j).toModuleIso

def rightDualComparison (i j : Fin 3) :
    rightDualOverlap i j ≅ rightDualModelSheaf i j :=
  comparisonIso (rightDualOverlap i j) (rightDualGlobalEquiv i j).toModuleIso

/-- The entire left sheaf square identifies the original vertical map. -/
theorem leftComparison_naturality (i j : Fin 3) :
    (leftOverlapDuality i j).hom ≫ (leftDualComparison i j).hom =
      (leftImageComparison i j).hom ≫ (leftModelDuality i j).hom := by
  apply comparisonIso_naturality (leftOverlapDuality i j).hom
    (leftImageGlobalEquiv i j).toModuleIso (leftDualGlobalEquiv i j).toModuleIso
    (Regrading.imageDual (leftData i j)).toModuleIso.hom
  apply ModuleCat.hom_ext
  exact LinearMap.ext (fun s => leftGlobal_naturality i j s)

/-- The entire right sheaf square uses the original right vertical map. -/
theorem rightComparison_naturality (i j : Fin 3) :
    (rightOverlapDuality i j).hom ≫ (rightDualComparison i j).hom =
      (rightImageComparison i j).hom ≫ (rightModelDuality i j).hom := by
  apply comparisonIso_naturality (rightOverlapDuality i j).hom
    (rightImageGlobalEquiv i j).toModuleIso (rightDualGlobalEquiv i j).toModuleIso
    (Regrading.imageDual (rightData i j)).toModuleIso.hom
  apply ModuleCat.hom_ext
  exact LinearMap.ext (fun s => rightGlobal_naturality i j s)

#print axioms leftImageGlobalEquiv
#print axioms rightImageGlobalEquiv
#print axioms leftDualGlobalEquiv
#print axioms rightDualGlobalEquiv
#print axioms leftGlobal_naturality
#print axioms rightGlobal_naturality
#print axioms leftComparison_naturality
#print axioms rightComparison_naturality

end CycleQ2SeedProjectiveOverlapComparisons
end
