import Proposal.GeometricSeedProjectiveImageRestriction
import Mathlib.RingTheory.Localization.Basic

/-!
# Localization of the actual projective overlap section rings

The actual map from the dehomogenized chart `AffineRing i` to sections on
the projective intersection is localization at the normalized coordinate
`Xj / Xi`. This transports the established homogeneous-coordinate
localization through the chart equivalence and the actual section-ring
equivalence. Both algebra structures are tied to the existing maps.

The two section algebras below are explicit definitions, not competing
global instances. No regularity or distinctness hypothesis is required
for the coordinate being inverted. Module and internal-Hom comparisons
are separate from this ring-localization statement.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedProjectiveOverlapLocalization

open AlgebraicGeometry MvPolynomial
open CycleQ2SeedTrace CycleQ2CartierSurfaceGrading CycleQ2CartierProjectiveCover
  CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2GeometricSurfaceOverlap
  CycleQ2SurfaceCoordinateSections CycleQ2SeedProjectiveImageChart
  CycleQ2SeedProjectiveImageCocycle CycleQ2SeedProjectiveImageRestriction
  CycleQ2GeometricSeedNormalIdeals

/-- The equation cutting out the complementary chart divisor on chart `i`. -/
def overlapCoordinate (i j : Fin 3) : AffineRing i :=
  affinePolynomial i (X j.succ.castSucc)

theorem coordinateChartEquiv_overlapCoordinate (i j : Fin 3) :
    coordinateChartEquiv 57 1 i.succ
        (coordinateRatio 57 1 i.succ j.succ.castSucc) =
      overlapCoordinate i j := by
  rw [coordinateRatio, coordinateChartEquiv_homogeneousFraction]
  rfl

/-- Transport localization from the homogeneous chart to its actual
dehomogenized chart ring, retaining the exact coefficient map. -/
theorem coefficient_isLocalization (i j : Fin 3) (x : SurfaceRing 57 1)
    (hx : x = coordinateDen 57 1 i.succ * coordinateDen 57 1 j.succ) :
    letI := (coefficient i j x hx).toAlgebra
    IsLocalization.Away (overlapCoordinate i j)
      (HomogeneousLocalization.Away (surfaceGrade 57 1) x) := by
  letI := (coordinateRestriction 57 1 i.succ j.succ x hx).toAlgebra
  letI := coordinateRestriction_isLocalization 57 1 i.succ j.succ x hx
  letI := (coefficient i j x hx).toAlgebra
  apply IsLocalization.of_ringEquiv_left
    (M₁ := Submonoid.powers (coordinateRatio 57 1 i.succ j.succ.castSucc))
    (M₂ := Submonoid.powers (overlapCoordinate i j))
    (coordinateChartEquiv 57 1 i.succ).symm
  · rw [Submonoid.map_powers]
    apply congrArg Submonoid.powers
    rw [← coordinateChartEquiv_overlapCoordinate, RingEquiv.symm_apply_apply]
  · intro a
    rfl

def leftSectionAlgebra (i j : Fin 3) :
    Algebra (AffineRing i) Γ(Surface, OverlapOpen i j) :=
  (chartSectionMap i (OverlapOpen i j) (pair_le_left 57 1 i.succ j.succ)).toAlgebra

def rightSectionAlgebra (i j : Fin 3) :
    Algebra (AffineRing j) Γ(Surface, OverlapOpen i j) :=
  (chartSectionMap j (OverlapOpen i j) (pair_le_right 57 1 i.succ j.succ)).toAlgebra

/-- The existing section-ring equivalence respects the exact left chart map. -/
def leftSectionsAlgEquiv (i j : Fin 3) :
    letI := (leftCoefficient i j).toAlgebra
    letI := leftSectionAlgebra i j
    OverlapRing i j ≃ₐ[AffineRing i] Γ(Surface, OverlapOpen i j) := by
  letI := (leftCoefficient i j).toAlgebra
  letI := leftSectionAlgebra i j
  exact { sectionsEquiv i j with
    commutes' := fun a => leftCoefficient_toSections i j a }

/-- The existing section-ring equivalence respects the exact right chart map. -/
def rightSectionsAlgEquiv (i j : Fin 3) :
    letI := (rightCoefficient i j).toAlgebra
    letI := rightSectionAlgebra i j
    OverlapRing i j ≃ₐ[AffineRing j] Γ(Surface, OverlapOpen i j) := by
  letI := (rightCoefficient i j).toAlgebra
  letI := rightSectionAlgebra i j
  exact { sectionsEquiv i j with
    commutes' := fun a => rightCoefficient_toSections i j a }

/-- The actual left structure-sheaf map is localization at `Xj / Xi`. -/
theorem leftSection_isLocalization (i j : Fin 3) :
    letI := leftSectionAlgebra i j
    IsLocalization.Away (overlapCoordinate i j) Γ(Surface, OverlapOpen i j) := by
  letI := (leftCoefficient i j).toAlgebra
  letI := coefficient_isLocalization i j (pairDen 57 1 i.succ j.succ) rfl
  letI := leftSectionAlgebra i j
  exact IsLocalization.isLocalization_of_algEquiv
    (Submonoid.powers (overlapCoordinate i j)) (leftSectionsAlgEquiv i j)

/-- The actual right structure-sheaf map is localization at `Xi / Xj`. -/
theorem rightSection_isLocalization (i j : Fin 3) :
    letI := rightSectionAlgebra i j
    IsLocalization.Away (overlapCoordinate j i) Γ(Surface, OverlapOpen i j) := by
  letI := (rightCoefficient i j).toAlgebra
  letI := coefficient_isLocalization j i (pairDen 57 1 i.succ j.succ) (mul_comm _ _)
  letI := rightSectionAlgebra i j
  exact IsLocalization.isLocalization_of_algEquiv
    (Submonoid.powers (overlapCoordinate j i)) (rightSectionsAlgEquiv i j)

#print axioms coefficient_isLocalization
#print axioms leftSectionsAlgEquiv
#print axioms rightSectionsAlgEquiv
#print axioms leftSection_isLocalization
#print axioms rightSection_isLocalization

end CycleQ2SeedProjectiveOverlapLocalization
end
