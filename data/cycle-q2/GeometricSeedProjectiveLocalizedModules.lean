import Proposal.GeometricSeedImageLocalizedModules
import Proposal.GeometricSeedProjectiveOverlapLocalization

/-!
# The original chart modules localized onto the actual projective overlap

The canonical localized orbit ideal and matrix image are identified with
the literal `leftData` and `rightData` modules in the actual overlap
section ring. Each equivalence agrees on original elements with the
existing ideal or coordinatewise image restriction.

The scalar ring of each displayed equivalence is its original affine
chart ring. The coefficient localization and linkage regularity are
discharged by the established projective restriction theorems, rather
than supplied as new assumptions. Comparison with the native associated
sheaf and internal Hom remains a separate step.

Source-only draft: no Lean elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. The geometric route and
remaining protected certificate obligation are recorded in solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedProjectiveLocalizedModules

open AlgebraicGeometry
open CycleQ2SurfaceCoordinateSections CycleQ2SeedProjectiveImageChart
  CycleQ2SeedProjectiveImageTwist CycleQ2SeedProjectiveImageCocycle
  CycleQ2SeedProjectiveImageRestriction CycleQ2SeedProjectiveOverlapLocalization
  CycleQ2SeedImageLocalizedModules

abbrev overlapPowers (i j : Fin 3) : Submonoid (AffineRing i) :=
  Submonoid.powers (overlapCoordinate i j)

/-- The canonical localized left-chart ideal is the actual left overlap ideal. -/
def leftIdealCanonicalEquiv (i j : Fin 3) :
    letI := leftSectionAlgebra i j
    LocalizedModule (overlapPowers i j) (OrbitIdeal i) ≃ₗ[AffineRing i]
      (leftData i j).leftIdeal := by
  letI := leftSectionAlgebra i j
  letI := leftSection_isLocalization i j
  exact extendedIdealCanonicalEquiv (overlapPowers i j)
    Γ(Surface, OverlapOpen i j) (OrbitIdeal i)

/-- The canonical localized right-chart ideal is the actual right overlap ideal. -/
def rightIdealCanonicalEquiv (i j : Fin 3) :
    letI := rightSectionAlgebra i j
    LocalizedModule (overlapPowers j i) (OrbitIdeal j) ≃ₗ[AffineRing j]
      (rightData i j).leftIdeal := by
  letI := rightSectionAlgebra i j
  letI := rightSection_isLocalization i j
  exact extendedIdealCanonicalEquiv (overlapPowers j i)
    Γ(Surface, OverlapOpen i j) (OrbitIdeal j)

theorem leftIdealCanonicalEquiv_original (i j : Fin 3) (x : OrbitIdeal i) :
    letI := leftSectionAlgebra i j
    leftIdealCanonicalEquiv i j
        (LocalizedModule.mkLinearMap (overlapPowers i j) (OrbitIdeal i) x) =
      mappedLeft (chartFactorData i)
        (chartSectionMap i (OverlapOpen i j) (pair_le_left 57 1 i.succ j.succ))
        (leftSection_linkage_regular i j) x := by
  letI := leftSectionAlgebra i j
  letI := leftSection_isLocalization i j
  exact (extendedIdealCanonicalEquiv_original (overlapPowers i j)
    Γ(Surface, OverlapOpen i j) (OrbitIdeal i) x).trans
      (extendedLeftMap_eq_localizedLeft (chartFactorData i) (overlapPowers i j)
        Γ(Surface, OverlapOpen i j) x)

theorem rightIdealCanonicalEquiv_original (i j : Fin 3) (x : OrbitIdeal j) :
    letI := rightSectionAlgebra i j
    rightIdealCanonicalEquiv i j
        (LocalizedModule.mkLinearMap (overlapPowers j i) (OrbitIdeal j) x) =
      mappedLeft (chartFactorData j)
        (chartSectionMap j (OverlapOpen i j) (pair_le_right 57 1 i.succ j.succ))
        (rightSection_linkage_regular i j) x := by
  letI := rightSectionAlgebra i j
  letI := rightSection_isLocalization i j
  exact (extendedIdealCanonicalEquiv_original (overlapPowers j i)
    Γ(Surface, OverlapOpen i j) (OrbitIdeal j) x).trans
      (extendedLeftMap_eq_localizedLeft (chartFactorData j) (overlapPowers j i)
        Γ(Surface, OverlapOpen i j) x)

/-- The canonical localized left-chart image is the actual left overlap image. -/
def leftImageCanonicalEquiv (i j : Fin 3) :
    letI := leftSectionAlgebra i j
    LocalizedModule (overlapPowers i j) (ImageModule i) ≃ₗ[AffineRing i]
      Regrading.Image (leftData i j) := by
  letI := leftSectionAlgebra i j
  letI := leftSection_isLocalization i j
  exact imageCanonicalEquiv (chartFactorData i) (overlapPowers i j)
    Γ(Surface, OverlapOpen i j)

/-- The canonical localized right-chart image is the actual right overlap image. -/
def rightImageCanonicalEquiv (i j : Fin 3) :
    letI := rightSectionAlgebra i j
    LocalizedModule (overlapPowers j i) (ImageModule j) ≃ₗ[AffineRing j]
      Regrading.Image (rightData i j) := by
  letI := rightSectionAlgebra i j
  letI := rightSection_isLocalization i j
  exact imageCanonicalEquiv (chartFactorData j) (overlapPowers j i)
    Γ(Surface, OverlapOpen i j)

theorem leftImageCanonicalEquiv_original (i j : Fin 3) (z : ImageModule i) :
    letI := leftSectionAlgebra i j
    leftImageCanonicalEquiv i j
        (LocalizedModule.mkLinearMap (overlapPowers i j) (ImageModule i) z) =
      leftImageRestriction i j z := by
  letI := leftSectionAlgebra i j
  letI := leftSection_isLocalization i j
  exact imageCanonicalEquiv_original (chartFactorData i) (overlapPowers i j)
    Γ(Surface, OverlapOpen i j) z

theorem rightImageCanonicalEquiv_original (i j : Fin 3) (z : ImageModule j) :
    letI := rightSectionAlgebra i j
    rightImageCanonicalEquiv i j
        (LocalizedModule.mkLinearMap (overlapPowers j i) (ImageModule j) z) =
      rightImageRestriction i j z := by
  letI := rightSectionAlgebra i j
  letI := rightSection_isLocalization i j
  exact imageCanonicalEquiv_original (chartFactorData j) (overlapPowers j i)
    Γ(Surface, OverlapOpen i j) z

#print axioms leftIdealCanonicalEquiv_original
#print axioms rightIdealCanonicalEquiv_original
#print axioms leftImageCanonicalEquiv_original
#print axioms rightImageCanonicalEquiv_original

end CycleQ2SeedProjectiveLocalizedModules
end
