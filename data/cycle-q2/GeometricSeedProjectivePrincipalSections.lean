import Proposal.GeometricSeedPrincipalSections
import Proposal.GeometricSeedProjectiveLocalizedDuality

/-!
# Native affine principal sections and the explicit overlap duality

On the principal open `D(Xj / Xi)` of the original affine chart, the
native sections of the image and orbit-dual associated sheaves are
identified with the explicit modules in the actual overlap section ring.
The original affine sheaf isomorphism commutes with these comparisons
on every native section. Both chart orders are treated with their own
original scalar rings and their actual overlap coefficient maps.

These comparisons are linear over the original affine rings. Transport
through the projective chart isomorphism, with its structure-sheaf scalar
actions, is still needed before asserting a projective sheaf comparison.
The global internal-Hom and sheaf-gluing obligations also remain.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedProjectivePrincipalSections

open CategoryTheory Opposite AlgebraicGeometry
open CycleQ2SeedProjectiveImageChart CycleQ2SeedProjectiveImageTwist
  CycleQ2SeedProjectiveImageRestriction CycleQ2SeedProjectiveOverlapLocalization
  CycleQ2SeedProjectiveLocalizedModules CycleQ2SeedProjectiveLocalizedDuality
  CycleQ2SeedImageLocalizedModules CycleQ2SeedImageLocalizedDuality
  CycleQ2SeedPrincipalSections

abbrev ImagePrincipalSections (i j : Fin 3) : ModuleCat (AffineRing i) :=
  principalSections (R := CommRingCat.of (AffineRing i))
    (ModuleCat.of (AffineRing i) (ImageModule i)) (overlapCoordinate i j)

abbrev DualPrincipalSections (i j : Fin 3) : ModuleCat (AffineRing i) :=
  principalSections (R := CommRingCat.of (AffineRing i))
    (ModuleCat.of (AffineRing i) (OrbitDual i)) (overlapCoordinate i j)

/-- The section map of the already existing affine sheaf isomorphism. -/
def imageDualSectionsMap (i j : Fin 3) :
    ImagePrincipalSections i j →ₗ[AffineRing i] DualPrincipalSections i j :=
  ((modulesSpecToSheaf.map (affineImageDualIso i).hom).1.app
    (op (PrimeSpectrum.basicOpen (overlapCoordinate i j)))).hom

def leftImageSectionsEquiv (i j : Fin 3) :
    letI := leftSectionAlgebra i j
    ImagePrincipalSections i j ≃ₗ[AffineRing i] Regrading.Image (leftData i j) := by
  letI := leftSectionAlgebra i j
  letI := leftSection_isLocalization i j
  letI := imageLocalizationMap_isLocalized (chartFactorData i)
    (overlapPowers i j) (OverlapSections i j)
  exact CycleQ2SeedPrincipalSections.sectionsEquiv (R := CommRingCat.of (AffineRing i))
    (ModuleCat.of (AffineRing i) (ImageModule i)) (overlapCoordinate i j)
    (imageLocalizationMap (chartFactorData i) (overlapPowers i j) (OverlapSections i j))

def leftDualSectionsEquiv (i j : Fin 3) :
    letI := leftSectionAlgebra i j
    DualPrincipalSections i j ≃ₗ[AffineRing i] LeftOverlapDual i j := by
  letI := leftSectionAlgebra i j
  letI := leftSection_isLocalization i j
  letI := dualLocalizationMap_isLocalized (chartFactorData i)
    (overlapPowers i j) (OverlapSections i j)
  exact CycleQ2SeedPrincipalSections.sectionsEquiv (R := CommRingCat.of (AffineRing i))
    (ModuleCat.of (AffineRing i) (OrbitDual i)) (overlapCoordinate i j)
    (dualLocalizationMap (chartFactorData i) (overlapPowers i j) (OverlapSections i j))

def rightImageSectionsEquiv (i j : Fin 3) :
    letI := rightSectionAlgebra i j
    ImagePrincipalSections j i ≃ₗ[AffineRing j] Regrading.Image (rightData i j) := by
  letI := rightSectionAlgebra i j
  letI := rightSection_isLocalization i j
  letI := imageLocalizationMap_isLocalized (chartFactorData j)
    (overlapPowers j i) (OverlapSections i j)
  exact CycleQ2SeedPrincipalSections.sectionsEquiv (R := CommRingCat.of (AffineRing j))
    (ModuleCat.of (AffineRing j) (ImageModule j)) (overlapCoordinate j i)
    (imageLocalizationMap (chartFactorData j) (overlapPowers j i) (OverlapSections i j))

def rightDualSectionsEquiv (i j : Fin 3) :
    letI := rightSectionAlgebra i j
    DualPrincipalSections j i ≃ₗ[AffineRing j] RightOverlapDual i j := by
  letI := rightSectionAlgebra i j
  letI := rightSection_isLocalization i j
  letI := dualLocalizationMap_isLocalized (chartFactorData j)
    (overlapPowers j i) (OverlapSections i j)
  exact CycleQ2SeedPrincipalSections.sectionsEquiv (R := CommRingCat.of (AffineRing j))
    (ModuleCat.of (AffineRing j) (OrbitDual j)) (overlapCoordinate j i)
    (dualLocalizationMap (chartFactorData j) (overlapPowers j i) (OverlapSections i j))

/-- The existing affine sheaf map agrees with the actual left overlap
duality after comparison of all native principal-open sections. -/
theorem leftSections_naturality (i j : Fin 3) :
    letI := leftSectionAlgebra i j
    (leftDualSectionsEquiv i j).toLinearMap.comp (imageDualSectionsMap i j) =
      ((Regrading.imageDual (leftData i j)).toLinearMap.restrictScalars (AffineRing i)).comp
        (leftImageSectionsEquiv i j).toLinearMap := by
  letI := leftSectionAlgebra i j
  letI := leftSection_isLocalization i j
  letI := imageLocalizationMap_isLocalized (chartFactorData i)
    (overlapPowers i j) (OverlapSections i j)
  letI := dualLocalizationMap_isLocalized (chartFactorData i)
    (overlapPowers i j) (OverlapSections i j)
  rw [← leftLocalizedImageDualEquiv_eq]
  exact sectionsEquiv_naturality (R := CommRingCat.of (AffineRing i))
    (imageDualEquiv i).toModuleIso.hom (overlapCoordinate i j)
    (imageLocalizationMap (chartFactorData i) (overlapPowers i j) (OverlapSections i j))
    (dualLocalizationMap (chartFactorData i) (overlapPowers i j) (OverlapSections i j))

/-- The corresponding square for the right chart, on the same actual overlap. -/
theorem rightSections_naturality (i j : Fin 3) :
    letI := rightSectionAlgebra i j
    (rightDualSectionsEquiv i j).toLinearMap.comp (imageDualSectionsMap j i) =
      ((Regrading.imageDual (rightData i j)).toLinearMap.restrictScalars (AffineRing j)).comp
        (rightImageSectionsEquiv i j).toLinearMap := by
  letI := rightSectionAlgebra i j
  letI := rightSection_isLocalization i j
  letI := imageLocalizationMap_isLocalized (chartFactorData j)
    (overlapPowers j i) (OverlapSections i j)
  letI := dualLocalizationMap_isLocalized (chartFactorData j)
    (overlapPowers j i) (OverlapSections i j)
  rw [← rightLocalizedImageDualEquiv_eq]
  exact sectionsEquiv_naturality (R := CommRingCat.of (AffineRing j))
    (imageDualEquiv j).toModuleIso.hom (overlapCoordinate j i)
    (imageLocalizationMap (chartFactorData j) (overlapPowers j i) (OverlapSections i j))
    (dualLocalizationMap (chartFactorData j) (overlapPowers j i) (OverlapSections i j))

#print axioms leftImageSectionsEquiv
#print axioms leftDualSectionsEquiv
#print axioms rightImageSectionsEquiv
#print axioms rightDualSectionsEquiv
#print axioms leftSections_naturality
#print axioms rightSections_naturality

end CycleQ2SeedProjectivePrincipalSections
end
