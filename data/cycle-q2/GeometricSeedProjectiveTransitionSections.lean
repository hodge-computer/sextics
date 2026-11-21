import Proposal.GeometricSeedAffineComparisonSections
import Proposal.GeometricSeedProjectiveSheafTransitions

/-!
# The native sheaf transitions recover the prescribed overlap sections

The image and dual sheaf transitions have exactly the native global-section
maps specified by the earlier literal module models. In particular the
image vectors retain the fourteenth-power coordinate multiplier, while
the entire ideal functional retains the positive fourth-power multiplier.

The image sheaf transition also recovers the previously constructed
imageSectionTransition on the original native projective sections.
These identities concern one fixed ordered pair overlap; they do not
supply the triple-overlap descent or a global internal-Hom comparison.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedProjectiveTransitionSections

open CategoryTheory AlgebraicGeometry
open CycleQ2SurfaceCoordinateSections CycleQ2SeedProjectiveImageChart
  CycleQ2SeedProjectiveImageTwist CycleQ2SeedProjectiveImageRestriction
  CycleQ2SeedProjectiveImageCompatibility CycleQ2SeedProjectiveLocalizedDuality
  CycleQ2SeedProjectiveSheafSections CycleQ2SeedAffineOpenSections
  CycleQ2SeedAffineReconstruction CycleQ2SeedAffineComparisonSections
  CycleQ2SeedProjectiveAffineOverlap CycleQ2SeedOverlapTransitionModels
  CycleQ2SeedProjectiveOverlapComparisons CycleQ2SeedProjectiveSheafTransitions

theorem imageOverlapTransition_model (i j : Fin 3)
    (s : globalSections (R := CommRingCat.of (OverlapSections i j)) (leftImageOverlap i j)) :
    rightImageGlobalEquiv i j
        (((moduleSpecΓFunctor (R := OverlapSections i j)).map
          (imageOverlapTransition i j).hom).hom s) =
      imageTransition i j (leftImageGlobalEquiv i j s) := by
  letI := leftImageOverlap_isQuasicoherent i j
  letI := rightImageOverlap_isQuasicoherent i j
  have h := conjugatedTransition_map (R := CommRingCat.of (OverlapSections i j))
      (E := ModuleCat.of (OverlapSections i j) (Regrading.Image (leftData i j)))
      (F := ModuleCat.of (OverlapSections i j) (Regrading.Image (rightData i j)))
      (leftImageOverlap i j) (rightImageOverlap i j)
      (leftImageGlobalEquiv i j).toModuleIso (rightImageGlobalEquiv i j).toModuleIso
      (imageTransition i j).toModuleIso
  exact ConcreteCategory.congr_hom h s

theorem dualOverlapTransition_model (i j : Fin 3)
    (s : globalSections (R := CommRingCat.of (OverlapSections i j)) (leftDualOverlap i j)) :
    rightDualGlobalEquiv i j
        (((moduleSpecΓFunctor (R := OverlapSections i j)).map
          (dualOverlapTransition i j).hom).hom s) =
      dualTransition i j (leftDualGlobalEquiv i j s) := by
  letI := leftDualOverlap_isQuasicoherent i j
  letI := rightDualOverlap_isQuasicoherent i j
  have h := conjugatedTransition_map (R := CommRingCat.of (OverlapSections i j))
      (E := ModuleCat.of (OverlapSections i j) (LeftOverlapDual i j))
      (F := ModuleCat.of (OverlapSections i j) (RightOverlapDual i j))
      (leftDualOverlap i j) (rightDualOverlap i j)
      (leftDualGlobalEquiv i j).toModuleIso (rightDualGlobalEquiv i j).toModuleIso
      (dualTransition i j).toModuleIso
  exact ConcreteCategory.congr_hom h s

/-- The native image transition keeps the literal degree-fourteen vector change. -/
theorem imageOverlapTransition_val (i j : Fin 3)
    (s : globalSections (R := CommRingCat.of (OverlapSections i j)) (leftImageOverlap i j)) :
    (rightImageGlobalEquiv i j
      (((moduleSpecΓFunctor (R := OverlapSections i j)).map
        (imageOverlapTransition i j).hom).hom s)).val =
      (ratioUnit i j : OverlapSections i j) ^ 14 • (leftImageGlobalEquiv i j s).val := by
  rw [imageOverlapTransition_model, imageTransition_val]

/-- The native dual transition keeps the full functional and its positive twist. -/
theorem dualOverlapTransition_twist (i j : Fin 3)
    (s : globalSections (R := CommRingCat.of (OverlapSections i j)) (leftDualOverlap i j)) :
    rightDualGlobalEquiv i j
        (((moduleSpecΓFunctor (R := OverlapSections i j)).map
          (dualOverlapTransition i j).hom).hom s) =
      (ratioUnit i j : OverlapSections i j) ^ 4 •
        (leftDualGlobalEquiv i j s).comp (idealIdentification i j).symm.toLinearMap := by
  rw [dualOverlapTransition_model, dualTransition_apply]

/-- The sheaf transition induces the existing transition on original chart sections. -/
theorem originalSectionTransition_recovered (i j : Fin 3)
    (s : globalSections (R := CommRingCat.of (OverlapSections i j)) (leftImageOverlap i j)) :
    topSectionEquiv (overlap_isAffineOpen i j)
        (pair_le_right 57 1 i.succ j.succ) (projectiveImageSheaf j)
        (((moduleSpecΓFunctor (R := OverlapSections i j)).map
          (imageOverlapTransition i j).hom).hom s) =
      imageSectionTransition i j
        (topSectionEquiv (overlap_isAffineOpen i j)
          (pair_le_left 57 1 i.succ j.succ) (projectiveImageSheaf i) s) := by
  apply (rightProjectiveImageEquiv i j).injective
  exact (imageOverlapTransition_model i j s).trans
    (imageSectionTransition_model i j
      (topSectionEquiv (overlap_isAffineOpen i j)
        (pair_le_left 57 1 i.succ j.succ) (projectiveImageSheaf i) s)).symm

#print axioms imageOverlapTransition_model
#print axioms dualOverlapTransition_model
#print axioms imageOverlapTransition_val
#print axioms dualOverlapTransition_twist
#print axioms originalSectionTransition_recovered

end CycleQ2SeedProjectiveTransitionSections
end
