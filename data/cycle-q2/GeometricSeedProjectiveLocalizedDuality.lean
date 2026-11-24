import Proposal.GeometricSeedImageLocalizedDuality
import Proposal.GeometricSeedProjectiveLocalizedModules
import Proposal.GeometricSeedImageDualSheafInputs
import Proposal.GeometricSeedProjectiveImageCompatibility

/-!
# Canonical Hom localization and the actual degree-four overlap square

The finite presentation of the original chart ideal discharges the Hom
localization condition. Its canonical localized dual is thereby identified
with the dual of the actual overlap ideal. Evaluation on original elements
uses the same actual coefficient and ideal maps as the earlier comparison.

The localization of each original image-dual equivalence is exactly the
literal equivalence on the actual overlap. Consequently the degree-four
square holds for these localized original equivalences on every overlap
image vector, as equality of whole ideal functionals.

These are module comparisons. Identification with native associated-sheaf
sections, the global internal Hom, and sheaf gluing are further obligations.
Source-only draft: no Lean elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedProjectiveLocalizedDuality

open AlgebraicGeometry
open CycleQ2SurfaceCoordinateSections CycleQ2SeedProjectiveImageChart
  CycleQ2SeedProjectiveImageTwist CycleQ2SeedProjectiveImageCocycle
  CycleQ2SeedProjectiveImageRestriction CycleQ2SeedProjectiveOverlapLocalization
  CycleQ2SeedProjectiveLocalizedModules CycleQ2SeedProjectiveImageCompatibility
  CycleQ2SeedImageLocalization CycleQ2SeedImageLocalizedDuality
  CycleQ2SeedImageDualSheafInputs

abbrev OverlapSections (i j : Fin 3) := Γ(Surface, OverlapOpen i j)
abbrev LeftOverlapDual (i j : Fin 3) :=
  (leftData i j).leftIdeal →ₗ[OverlapSections i j] OverlapSections i j
abbrev RightOverlapDual (i j : Fin 3) :=
  (rightData i j).leftIdeal →ₗ[OverlapSections i j] OverlapSections i j

/-- The finite-presentation condition is discharged for the actual left ideal. -/
def leftDualCanonicalEquiv (i j : Fin 3) :
    letI := leftSectionAlgebra i j
    LocalizedModule (overlapPowers i j) (OrbitDual i) ≃ₗ[AffineRing i]
      LeftOverlapDual i j := by
  letI := leftSectionAlgebra i j
  letI := leftSection_isLocalization i j
  exact dualCanonicalEquiv (chartFactorData i) (overlapPowers i j)
    (OverlapSections i j)

/-- The right chart uses its own original scalar ring and localizing coordinate. -/
def rightDualCanonicalEquiv (i j : Fin 3) :
    letI := rightSectionAlgebra i j
    LocalizedModule (overlapPowers j i) (OrbitDual j) ≃ₗ[AffineRing j]
      RightOverlapDual i j := by
  letI := rightSectionAlgebra i j
  letI := rightSection_isLocalization i j
  exact dualCanonicalEquiv (chartFactorData j) (overlapPowers j i)
    (OverlapSections i j)

theorem leftDualCanonicalEquiv_original (i j : Fin 3)
    (φ : OrbitDual i) (x : OrbitIdeal i) :
    letI := leftSectionAlgebra i j
    leftDualCanonicalEquiv i j
        (LocalizedModule.mkLinearMap (overlapPowers i j) (OrbitDual i) φ)
        (leftIdealCanonicalEquiv i j
          (LocalizedModule.mkLinearMap (overlapPowers i j) (OrbitIdeal i) x)) =
      chartSectionMap i (OverlapOpen i j) (pair_le_left 57 1 i.succ j.succ) (φ x) := by
  letI := leftSectionAlgebra i j
  letI := leftSection_isLocalization i j
  rw [leftIdealCanonicalEquiv_original]
  change dualCanonicalEquiv (chartFactorData i) (overlapPowers i j)
      (OverlapSections i j)
      (LocalizedModule.mkLinearMap (overlapPowers i j) (OrbitDual i) φ)
      (localizedLeft (chartFactorData i) (overlapPowers i j) (OverlapSections i j) x) = _
  rw [dualCanonicalEquiv_original]
  exact dualLocalizationMap_original (chartFactorData i) (overlapPowers i j)
    (OverlapSections i j) φ x

theorem rightDualCanonicalEquiv_original (i j : Fin 3)
    (φ : OrbitDual j) (x : OrbitIdeal j) :
    letI := rightSectionAlgebra i j
    rightDualCanonicalEquiv i j
        (LocalizedModule.mkLinearMap (overlapPowers j i) (OrbitDual j) φ)
        (rightIdealCanonicalEquiv i j
          (LocalizedModule.mkLinearMap (overlapPowers j i) (OrbitIdeal j) x)) =
      chartSectionMap j (OverlapOpen i j) (pair_le_right 57 1 i.succ j.succ) (φ x) := by
  letI := rightSectionAlgebra i j
  letI := rightSection_isLocalization i j
  rw [rightIdealCanonicalEquiv_original]
  change dualCanonicalEquiv (chartFactorData j) (overlapPowers j i)
      (OverlapSections i j)
      (LocalizedModule.mkLinearMap (overlapPowers j i) (OrbitDual j) φ)
      (localizedLeft (chartFactorData j) (overlapPowers j i) (OverlapSections i j) x) = _
  rw [dualCanonicalEquiv_original]
  exact dualLocalizationMap_original (chartFactorData j) (overlapPowers j i)
    (OverlapSections i j) φ x

/-- Localize the original left-chart equivalence over the actual overlap ring. -/
def leftLocalizedImageDualEquiv (i j : Fin 3) :
    Regrading.Image (leftData i j) ≃ₗ[OverlapSections i j] LeftOverlapDual i j := by
  letI := leftSectionAlgebra i j
  letI := leftSection_isLocalization i j
  exact localizedImageDualEquiv (chartFactorData i) (overlapPowers i j)
    (OverlapSections i j)

/-- Localize the original right-chart equivalence over the same overlap ring. -/
def rightLocalizedImageDualEquiv (i j : Fin 3) :
    Regrading.Image (rightData i j) ≃ₗ[OverlapSections i j] RightOverlapDual i j := by
  letI := rightSectionAlgebra i j
  letI := rightSection_isLocalization i j
  exact localizedImageDualEquiv (chartFactorData j) (overlapPowers j i)
    (OverlapSections i j)

theorem leftLocalizedImageDualEquiv_eq (i j : Fin 3) :
    leftLocalizedImageDualEquiv i j = Regrading.imageDual (leftData i j) := by
  letI := leftSectionAlgebra i j
  letI := leftSection_isLocalization i j
  exact localizedImageDualEquiv_eq (chartFactorData i) (overlapPowers i j)
    (OverlapSections i j)

theorem rightLocalizedImageDualEquiv_eq (i j : Fin 3) :
    rightLocalizedImageDualEquiv i j = Regrading.imageDual (rightData i j) := by
  letI := rightSectionAlgebra i j
  letI := rightSection_isLocalization i j
  exact localizedImageDualEquiv_eq (chartFactorData j) (overlapPowers j i)
    (OverlapSections i j)

/-- The degree-four square is a square of localized original equivalences,
on every overlap vector and as equality on the entire overlap ideal. -/
theorem localizedImageDual_compatibility (i j : Fin 3)
    (z : Regrading.Image (leftData i j)) :
    rightLocalizedImageDualEquiv i j (imageTransition i j z) =
      (ratioUnit i j : OverlapSections i j) ^ 4 •
        ((leftLocalizedImageDualEquiv i j z).comp
          (idealIdentification i j).symm.toLinearMap) := by
  rw [leftLocalizedImageDualEquiv_eq, rightLocalizedImageDualEquiv_eq]
  exact imageDual_compatibility i j z

#print axioms leftDualCanonicalEquiv_original
#print axioms rightDualCanonicalEquiv_original
#print axioms leftLocalizedImageDualEquiv_eq
#print axioms rightLocalizedImageDualEquiv_eq
#print axioms localizedImageDual_compatibility

end CycleQ2SeedProjectiveLocalizedDuality
end
