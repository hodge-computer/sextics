import Proposal.GeometricSeedProjectiveOverlapLocalization

/-!
# The actual projective intersection as an affine principal open

The ambient map is the inverse of the original affine-chart isomorphism
followed by the inclusion of that projective coordinate patch. Pulling
back the other coordinate patch gives the native affine basic open of
`Xj / Xi`. The actual projective intersection has the same preimage.

These identities bind the existing overlap coordinate to the geometry
needed for native principal-open sections. They do not yet transport
the associated-module sheaves through the chart isomorphism.

Source-only draft: no Lean elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the remaining certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedProjectivePrincipalOpens

open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2SeedTrace CycleQ2CartierSurfaceGrading CycleQ2CartierProjectiveCover
  CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2GeometricSurfaceOverlap
  CycleQ2SurfaceCoordinateSections CycleQ2SeedProjectiveImageChart
  CycleQ2SeedProjectiveImageCocycle CycleQ2SeedProjectiveImageRestriction
  CycleQ2SeedProjectiveOverlapLocalization

/-- The original affine chart, regarded as an open immersion into the surface. -/
def ambientChart (i : Fin 3) : Spec (CommRingCat.of (AffineRing i)) ⟶ Surface :=
  (coordinateAffineChart 57 1 i.succ).inv ≫ (Patch i).ι

theorem ambientChart_eq (i : Fin 3) :
    ambientChart i =
      Spec.map (CommRingCat.ofHom (coordinateChartEquiv 57 1 i.succ).toRingHom) ≫
        Proj.awayι (surfaceGrade 57 1) (coordinateDen 57 1 i.succ)
          (coordinate_mem_grade 57 1 i.succ) (by decide) := by
  change
    (Spec.map (CommRingCat.ofHom (coordinateChartEquiv 57 1 i.succ).toRingHom) ≫
        (Proj.basicOpenIsoSpec (surfaceGrade 57 1) (coordinateDen 57 1 i.succ)
          (coordinate_mem_grade 57 1 i.succ) (by decide)).inv) ≫ (Patch i).ι =
      Spec.map (CommRingCat.ofHom (coordinateChartEquiv 57 1 i.succ).toRingHom) ≫
        ((Proj.basicOpenIsoSpec (surfaceGrade 57 1) (coordinateDen 57 1 i.succ)
          (coordinate_mem_grade 57 1 i.succ) (by decide)).inv ≫ (Patch i).ι)
  exact Category.assoc _ _ _

/-- Pullback of the other projective chart is the literal affine basic open. -/
theorem ambientChart_preimage_patch (i j : Fin 3) :
    ambientChart i ⁻¹ᵁ Patch j = PrimeSpectrum.basicOpen (overlapCoordinate i j) := by
  rw [ambientChart_eq]
  change
    Spec.map (CommRingCat.ofHom (coordinateChartEquiv 57 1 i.succ).toRingHom) ⁻¹ᵁ
      (Proj.awayι (surfaceGrade 57 1) (coordinateDen 57 1 i.succ)
          (coordinate_mem_grade 57 1 i.succ) (by decide) ⁻¹ᵁ
        Proj.basicOpen (surfaceGrade 57 1) (coordinateDen 57 1 j.succ)) = _
  rw [Proj.awayι_preimage_basicOpen (𝒜 := surfaceGrade 57 1)
    (coordinate_mem_grade 57 1 i.succ) (by decide)
    (coordinate_mem_grade 57 1 j.succ) (by decide)]
  rw [coordinateLocalizationElement_eq]
  change PrimeSpectrum.basicOpen
      (coordinateChartEquiv 57 1 i.succ (coordinateRatio 57 1 i.succ j.succ.castSucc)) = _
  rw [coordinateChartEquiv_overlapCoordinate]

theorem overlapCoordinate_self (i : Fin 3) : overlapCoordinate i i = 1 := by
  rw [← coordinateChartEquiv_overlapCoordinate i i, coordinateRatio_self, map_one]

/-- The existing projective intersection pulls back to the same native
principal open used to localize the original affine modules. -/
theorem ambientChart_preimage_overlap (i j : Fin 3) :
    ambientChart i ⁻¹ᵁ OverlapOpen i j =
      PrimeSpectrum.basicOpen (overlapCoordinate i j) := by
  change ambientChart i ⁻¹ᵁ pairOpen 57 1 i.succ j.succ = _
  rw [pairOpen_eq]
  change (ambientChart i ⁻¹ᵁ Patch i) ⊓ (ambientChart i ⁻¹ᵁ Patch j) = _
  simp only [ambientChart_preimage_patch, overlapCoordinate_self,
    PrimeSpectrum.basicOpen_one, top_inf_eq]

#print axioms ambientChart_eq
#print axioms ambientChart_preimage_patch
#print axioms ambientChart_preimage_overlap

end CycleQ2SeedProjectivePrincipalOpens
end
