import Proposal.GeometricSeedChartSectionScalars
import Proposal.GeometricSeedProjectiveChartOverlaps
import Proposal.GeometricSeedProjectivePrincipalSections

/-!
# Native affine sections as modules over the actual overlap ring

The four comparisons below retain the native affine-ring action on sheaf
sections. Their overlap-ring action is exactly `chartSectionsModule`,
pulled back through the actual chart section-ring isomorphism. The proved
scalar tower and coefficient localization upgrade the existing affine-linear
comparisons to equivalences over the actual projective overlap section ring.

The whole-section squares use the existing affine sheaf isomorphisms.
Transport of the projective restricted sheaves is a separate component.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

namespace CycleQ2SeedOverlapSectionModels

open CategoryTheory Opposite AlgebraicGeometry
open CycleQ2GeometricAffineChartSections CycleQ2GeometricSurfaceDehomogenizedCharts
  CycleQ2SurfaceCoordinateSections CycleQ2SeedProjectiveImageChart
  CycleQ2SeedProjectiveImageTwist CycleQ2SeedProjectiveImageCocycle
  CycleQ2SeedProjectiveImageRestriction CycleQ2SeedProjectiveOverlapLocalization
  CycleQ2SeedProjectiveLocalizedModules CycleQ2SeedProjectiveLocalizedDuality
  CycleQ2SeedChartSectionScalars CycleQ2SeedProjectiveChartOverlaps
  CycleQ2SeedProjectivePrincipalSections

/-- Change equal native opens while retaining the native affine scalar action. -/
def nativeOpenEquiv {R : CommRingCat.{u}} (M : (Spec R).Modules)
    {U V : (Spec R).Opens} (h : U = V) : Γ(M, U) ≃ₗ[R] Γ(M, V) :=
  ((modulesSpecToSheaf.obj M).presheaf.mapIso (eqToIso h.symm).op).toLinearEquiv

theorem nativeOpenEquiv_naturality {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    (φ : M ⟶ N) {U V : (Spec R).Opens} (h : U = V) (x : Γ(M, U)) :
    nativeOpenEquiv N h (φ.app U x) = φ.app V (nativeOpenEquiv M h x) := by
  exact congrArg
    (fun k : (modulesSpecToSheaf.obj M).presheaf.obj (op U) ⟶
        (modulesSpecToSheaf.obj N).presheaf.obj (op V) => k.hom x)
    ((modulesSpecToSheaf.map φ).1.naturality (eqToHom h.symm).op).symm

abbrev leftChartOver (i j : Fin 3) : Over (Patch i) :=
  Over.mk (homOfLE (pair_le_left 57 1 i.succ j.succ))

abbrev rightChartOver (i j : Fin 3) : Over (Patch j) :=
  Over.mk (homOfLE (pair_le_right 57 1 i.succ j.succ))

abbrev leftChartOpen (i j : Fin 3) :=
  (chartOpensEquiv (coordinateAffineChart 57 1 i.succ)).functor.obj (leftChartOver i j)

abbrev rightChartOpen (i j : Fin 3) :=
  (chartOpensEquiv (coordinateAffineChart 57 1 j.succ)).functor.obj (rightChartOver i j)

local instance nativeSectionsModule {A : Type u} [CommRing A]
    (M : (Spec (CommRingCat.of A)).Modules) (U : (Spec (CommRingCat.of A)).Opens) :
    Module A Γ(M, U) :=
  inferInstanceAs (Module A ((modulesSpecToSheaf.obj M).presheaf.obj (op U)))

local instance leftImageOverlapModule (i j : Fin 3) :
    Module (OverlapSections i j) Γ(affineImageSheaf i, leftChartOpen i j) :=
  chartSectionsModule (coordinateAffineChart 57 1 i.succ)
    (leftChartOver i j) (affineImageSheaf i)

local instance leftDualOverlapModule (i j : Fin 3) :
    Module (OverlapSections i j) Γ(affineOrbitDualSheaf i, leftChartOpen i j) :=
  chartSectionsModule (coordinateAffineChart 57 1 i.succ)
    (leftChartOver i j) (affineOrbitDualSheaf i)

local instance rightImageOverlapModule (i j : Fin 3) :
    Module (OverlapSections i j) Γ(affineImageSheaf j, rightChartOpen i j) :=
  chartSectionsModule (coordinateAffineChart 57 1 j.succ)
    (rightChartOver i j) (affineImageSheaf j)

local instance rightDualOverlapModule (i j : Fin 3) :
    Module (OverlapSections i j) Γ(affineOrbitDualSheaf j, rightChartOpen i j) :=
  chartSectionsModule (coordinateAffineChart 57 1 j.succ)
    (rightChartOver i j) (affineOrbitDualSheaf j)

def leftImageModel (i j : Fin 3) :
    letI := chartSectionsModule (coordinateAffineChart 57 1 i.succ)
      (leftChartOver i j) (affineImageSheaf i)
    Γ(affineImageSheaf i, leftChartOpen i j) ≃ₗ[OverlapSections i j]
      Regrading.Image (leftData i j) := by
  letI := leftSectionAlgebra i j
  letI := leftSection_isLocalization i j
  letI := chartSectionsModule (coordinateAffineChart 57 1 i.succ)
    (leftChartOver i j) (affineImageSheaf i)
  letI : IsScalarTower (AffineRing i) (OverlapSections i j)
      Γ(affineImageSheaf i, leftChartOpen i j) :=
    chartSections_isScalarTower (coordinateAffineChart 57 1 i.succ)
      (leftChartOver i j) (affineImageSheaf i)
  exact ((nativeOpenEquiv (affineImageSheaf i) (chartOpensEquiv_left i j)).trans
    (leftImageSectionsEquiv i j)).extendScalarsOfIsLocalization
      (overlapPowers i j) (OverlapSections i j)

def leftDualModel (i j : Fin 3) :
    letI := chartSectionsModule (coordinateAffineChart 57 1 i.succ)
      (leftChartOver i j) (affineOrbitDualSheaf i)
    Γ(affineOrbitDualSheaf i, leftChartOpen i j) ≃ₗ[OverlapSections i j]
      LeftOverlapDual i j := by
  letI := leftSectionAlgebra i j
  letI := leftSection_isLocalization i j
  letI := chartSectionsModule (coordinateAffineChart 57 1 i.succ)
    (leftChartOver i j) (affineOrbitDualSheaf i)
  letI : IsScalarTower (AffineRing i) (OverlapSections i j)
      Γ(affineOrbitDualSheaf i, leftChartOpen i j) :=
    chartSections_isScalarTower (coordinateAffineChart 57 1 i.succ)
      (leftChartOver i j) (affineOrbitDualSheaf i)
  exact ((nativeOpenEquiv (affineOrbitDualSheaf i) (chartOpensEquiv_left i j)).trans
    (leftDualSectionsEquiv i j)).extendScalarsOfIsLocalization
      (overlapPowers i j) (OverlapSections i j)

def rightImageModel (i j : Fin 3) :
    letI := chartSectionsModule (coordinateAffineChart 57 1 j.succ)
      (rightChartOver i j) (affineImageSheaf j)
    Γ(affineImageSheaf j, rightChartOpen i j) ≃ₗ[OverlapSections i j]
      Regrading.Image (rightData i j) := by
  letI := rightSectionAlgebra i j
  letI := rightSection_isLocalization i j
  letI := chartSectionsModule (coordinateAffineChart 57 1 j.succ)
    (rightChartOver i j) (affineImageSheaf j)
  letI : IsScalarTower (AffineRing j) (OverlapSections i j)
      Γ(affineImageSheaf j, rightChartOpen i j) :=
    chartSections_isScalarTower (coordinateAffineChart 57 1 j.succ)
      (rightChartOver i j) (affineImageSheaf j)
  exact ((nativeOpenEquiv (affineImageSheaf j) (chartOpensEquiv_right i j)).trans
    (rightImageSectionsEquiv i j)).extendScalarsOfIsLocalization
      (overlapPowers j i) (OverlapSections i j)

def rightDualModel (i j : Fin 3) :
    letI := chartSectionsModule (coordinateAffineChart 57 1 j.succ)
      (rightChartOver i j) (affineOrbitDualSheaf j)
    Γ(affineOrbitDualSheaf j, rightChartOpen i j) ≃ₗ[OverlapSections i j]
      RightOverlapDual i j := by
  letI := rightSectionAlgebra i j
  letI := rightSection_isLocalization i j
  letI := chartSectionsModule (coordinateAffineChart 57 1 j.succ)
    (rightChartOver i j) (affineOrbitDualSheaf j)
  letI : IsScalarTower (AffineRing j) (OverlapSections i j)
      Γ(affineOrbitDualSheaf j, rightChartOpen i j) :=
    chartSections_isScalarTower (coordinateAffineChart 57 1 j.succ)
      (rightChartOver i j) (affineOrbitDualSheaf j)
  exact ((nativeOpenEquiv (affineOrbitDualSheaf j) (chartOpensEquiv_right i j)).trans
    (rightDualSectionsEquiv i j)).extendScalarsOfIsLocalization
      (overlapPowers j i) (OverlapSections i j)

/-- The actual left affine sheaf map agrees on all native sections with
the literal overlap image-to-ideal-dual map. -/
theorem leftModel_naturality (i j : Fin 3)
    (z : Γ(affineImageSheaf i, leftChartOpen i j)) :
    letI := chartSectionsModule (coordinateAffineChart 57 1 i.succ)
      (leftChartOver i j) (affineImageSheaf i)
    letI := chartSectionsModule (coordinateAffineChart 57 1 i.succ)
      (leftChartOver i j) (affineOrbitDualSheaf i)
    leftDualModel i j ((affineImageDualIso i).hom.app (leftChartOpen i j) z) =
      Regrading.imageDual (leftData i j) (leftImageModel i j z) := by
  letI := leftSectionAlgebra i j
  letI := chartSectionsModule (coordinateAffineChart 57 1 i.succ)
    (leftChartOver i j) (affineImageSheaf i)
  letI := chartSectionsModule (coordinateAffineChart 57 1 i.succ)
    (leftChartOver i j) (affineOrbitDualSheaf i)
  change leftDualSectionsEquiv i j
      (nativeOpenEquiv (affineOrbitDualSheaf i) (chartOpensEquiv_left i j)
        ((affineImageDualIso i).hom.app (leftChartOpen i j) z)) =
    Regrading.imageDual (leftData i j)
      (leftImageSectionsEquiv i j
        (nativeOpenEquiv (affineImageSheaf i) (chartOpensEquiv_left i j) z))
  rw [nativeOpenEquiv_naturality]
  exact LinearMap.congr_fun (leftSections_naturality i j)
    (nativeOpenEquiv (affineImageSheaf i) (chartOpensEquiv_left i j) z)

/-- The right chart uses its own affine coefficients and the same actual overlap. -/
theorem rightModel_naturality (i j : Fin 3)
    (z : Γ(affineImageSheaf j, rightChartOpen i j)) :
    letI := chartSectionsModule (coordinateAffineChart 57 1 j.succ)
      (rightChartOver i j) (affineImageSheaf j)
    letI := chartSectionsModule (coordinateAffineChart 57 1 j.succ)
      (rightChartOver i j) (affineOrbitDualSheaf j)
    rightDualModel i j ((affineImageDualIso j).hom.app (rightChartOpen i j) z) =
      Regrading.imageDual (rightData i j) (rightImageModel i j z) := by
  letI := rightSectionAlgebra i j
  letI := chartSectionsModule (coordinateAffineChart 57 1 j.succ)
    (rightChartOver i j) (affineImageSheaf j)
  letI := chartSectionsModule (coordinateAffineChart 57 1 j.succ)
    (rightChartOver i j) (affineOrbitDualSheaf j)
  change rightDualSectionsEquiv i j
      (nativeOpenEquiv (affineOrbitDualSheaf j) (chartOpensEquiv_right i j)
        ((affineImageDualIso j).hom.app (rightChartOpen i j) z)) =
    Regrading.imageDual (rightData i j)
      (rightImageSectionsEquiv i j
        (nativeOpenEquiv (affineImageSheaf j) (chartOpensEquiv_right i j) z))
  rw [nativeOpenEquiv_naturality]
  exact LinearMap.congr_fun (rightSections_naturality i j)
    (nativeOpenEquiv (affineImageSheaf j) (chartOpensEquiv_right i j) z)

#print axioms nativeOpenEquiv_naturality
#print axioms leftImageModel
#print axioms leftDualModel
#print axioms rightImageModel
#print axioms rightDualModel
#print axioms leftModel_naturality
#print axioms rightModel_naturality

end CycleQ2SeedOverlapSectionModels
end
