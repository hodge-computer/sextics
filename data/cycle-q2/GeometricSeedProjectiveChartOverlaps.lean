import Proposal.GeometricSeedProjectivePrincipalOpens
import Proposal.GeometricAffineChartSections

/-!
# Native chart opens for the actual projective intersection

Both native chart opens come from the same ordered projective overlap.
Their images in the corresponding affine spectra are the principal opens
already used for localization. The existing over-site chart equivalences
give those same principal opens.

Source-only draft: no Lean elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedProjectiveChartOverlaps

open CategoryTheory AlgebraicGeometry
open CycleQ2GeometricAffineChartSections CycleQ2GeometricSurfaceDehomogenizedCharts
  CycleQ2GeometricSurfaceOverlap CycleQ2SurfaceCoordinateSections
  CycleQ2SeedProjectiveImageChart CycleQ2SeedProjectiveImageCocycle
  CycleQ2SeedProjectiveImageRestriction CycleQ2SeedProjectiveOverlapLocalization
  CycleQ2SeedProjectivePrincipalOpens

def leftNativeOverlap (i j : Fin 3) : (Patch i).toScheme.Opens :=
  (Patch i).ι ⁻¹ᵁ OverlapOpen i j

def rightNativeOverlap (i j : Fin 3) : (Patch j).toScheme.Opens :=
  (Patch j).ι ⁻¹ᵁ OverlapOpen i j

/-- The right chart uses the same ordered projective overlap. -/
theorem ambientChart_preimage_overlap_right (i j : Fin 3) :
    ambientChart j ⁻¹ᵁ OverlapOpen i j =
      PrimeSpectrum.basicOpen (overlapCoordinate j i) := by
  change ambientChart j ⁻¹ᵁ pairOpen 57 1 i.succ j.succ = _
  rw [pairOpen_eq]
  change (ambientChart j ⁻¹ᵁ Patch i) ⊓ (ambientChart j ⁻¹ᵁ Patch j) = _
  simp only [ambientChart_preimage_patch, overlapCoordinate_self,
    PrimeSpectrum.basicOpen_one, inf_top_eq]

theorem leftNativeOverlap_image (i j : Fin 3) :
    (coordinateAffineChart 57 1 i.succ).hom ''ᵁ leftNativeOverlap i j =
      PrimeSpectrum.basicOpen (overlapCoordinate i j) := by
  rw [← Scheme.Hom.inv_preimage]
  change ambientChart i ⁻¹ᵁ OverlapOpen i j = _
  exact ambientChart_preimage_overlap i j

theorem rightNativeOverlap_image (i j : Fin 3) :
    (coordinateAffineChart 57 1 j.succ).hom ''ᵁ rightNativeOverlap i j =
      PrimeSpectrum.basicOpen (overlapCoordinate j i) := by
  rw [← Scheme.Hom.inv_preimage]
  change ambientChart j ⁻¹ᵁ OverlapOpen i j = _
  exact ambientChart_preimage_overlap_right i j

theorem chartOpensEquiv_left (i j : Fin 3) :
    (chartOpensEquiv (coordinateAffineChart 57 1 i.succ)).functor.obj
        (Over.mk (homOfLE (pair_le_left 57 1 i.succ j.succ))) =
      PrimeSpectrum.basicOpen (overlapCoordinate i j) := by
  rw [chartOpensEquiv_obj]
  change ambientChart i ⁻¹ᵁ OverlapOpen i j = _
  exact ambientChart_preimage_overlap i j

theorem chartOpensEquiv_right (i j : Fin 3) :
    (chartOpensEquiv (coordinateAffineChart 57 1 j.succ)).functor.obj
        (Over.mk (homOfLE (pair_le_right 57 1 i.succ j.succ))) =
      PrimeSpectrum.basicOpen (overlapCoordinate j i) := by
  rw [chartOpensEquiv_obj]
  change ambientChart j ⁻¹ᵁ OverlapOpen i j = _
  exact ambientChart_preimage_overlap_right i j

#print axioms ambientChart_preimage_overlap_right
#print axioms leftNativeOverlap_image
#print axioms rightNativeOverlap_image
#print axioms chartOpensEquiv_left
#print axioms chartOpensEquiv_right

end CycleQ2SeedProjectiveChartOverlaps
end
