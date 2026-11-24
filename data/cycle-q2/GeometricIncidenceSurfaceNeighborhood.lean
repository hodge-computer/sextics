import Proposal.GeometricIncidenceDimensionOpen
import Proposal.GeometricIncidenceSmoothNeighborhood

/-!
# The retained seed neighborhood is a proper smooth surface family

The entire previously constructed seedSmoothSource lies in the actual
dimension-two open. Factoring its inclusion through that open specifies
the relative dimension of the original source-to-base map. The same
property descends to its genuine target restriction along the open
immersion seedSmoothBase into the original parameter scheme.

The base neighborhood and the family morphism are exactly the previously
constructed ones; no new seed, coefficient algebra, or shrinking premise
is introduced. Flatness and properness are retained from those objects.

Source-only draft: no elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2IncidenceSurfaceNeighborhood

open CategoryTheory AlgebraicGeometry
open CycleQ2IncidenceEtaleParameter CycleQ2GeometricIncidenceProj
  CycleQ2IncidenceSeedFiberCover CycleQ2IncidenceSmoothNeighborhood
  CycleQ2IncidenceDimensionOpen

theorem seedFiber_mem_dimensionOpen (x : surface incidencePoint)
    (hx : surfaceToBase incidencePoint x = seedBasePoint) :
    x ∈ dimensionOpen incidencePoint :=
  goodOpen_le_dimensionOpen incidencePoint (seedFiber_mem_goodOpen x hx)

theorem seedSmoothSource_le_dimensionOpen :
    seedSmoothSource ≤ dimensionOpen incidencePoint :=
  seedSmoothSource_le_goodOpen.trans (goodOpen_le_dimensionOpen incidencePoint)

def sourceToDimensionOpen :
    seedSmoothSource.toScheme ⟶ (dimensionOpen incidencePoint).toScheme :=
  IsOpenImmersion.lift (dimensionOpen incidencePoint).ι seedSmoothSource.ι (by
    rintro x ⟨u, rfl⟩
    exact ⟨⟨u.1, seedSmoothSource_le_dimensionOpen u.2⟩, rfl⟩)

instance sourceToDimensionOpen_isOpenImmersion :
    IsOpenImmersion sourceToDimensionOpen := by
  dsimp only [sourceToDimensionOpen]
  infer_instance

theorem sourceToDimensionOpen_fac :
    sourceToDimensionOpen ≫ (dimensionOpen incidencePoint).ι = seedSmoothSource.ι :=
  IsOpenImmersion.lift_fac _ _ _

theorem seedSmoothSource_smoothOfRelativeDimension :
    AlgebraicGeometry.SmoothOfRelativeDimension 2
      (seedSmoothSource.ι ≫ surfaceToBase incidencePoint) := by
  rw [← sourceToDimensionOpen_fac, Category.assoc]
  exact IsZariskiLocalAtSource.comp
    (dimensionOpen_smoothOfRelativeDimension incidencePoint) sourceToDimensionOpen

/-- Relative dimension two for the genuine restriction of the original
family to the original retained base neighborhood. -/
theorem seedSmoothFamily_smoothOfRelativeDimension :
    AlgebraicGeometry.SmoothOfRelativeDimension 2 seedSmoothFamily := by
  letI : MorphismProperty.IsStableUnderBaseChange
      (@AlgebraicGeometry.SmoothOfRelativeDimension 2) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 2
  change AlgebraicGeometry.SmoothOfRelativeDimension 2
    ((surfaceToBase incidencePoint) ∣_ seedSmoothBase)
  apply MorphismProperty.of_postcomp (W' := @IsOpenImmersion)
    (@AlgebraicGeometry.SmoothOfRelativeDimension 2)
    ((surfaceToBase incidencePoint) ∣_ seedSmoothBase)
    seedSmoothBase.ι (inferInstance : IsOpenImmersion seedSmoothBase.ι)
  simpa only [morphismRestrict_ι, seedSmoothSource] using
    seedSmoothSource_smoothOfRelativeDimension

/-- An actual open containing the retained seed, on which the original
incidence surface family is proper, flat, and smooth of dimension two. -/
theorem exists_seed_surface_neighborhood :
    ∃ V : (Spec (CommRingCat.of ParameterAlgebra)).Opens,
      seedBasePoint ∈ V ∧
      AlgebraicGeometry.SmoothOfRelativeDimension 2
        ((surfaceToBase incidencePoint) ∣_ V) ∧
      AlgebraicGeometry.Flat ((surfaceToBase incidencePoint) ∣_ V) ∧
      IsProper ((surfaceToBase incidencePoint) ∣_ V) :=
  ⟨seedSmoothBase, seed_mem_seedSmoothBase, seedSmoothFamily_smoothOfRelativeDimension,
    seedSmoothFamily_flat, seedSmoothFamily_proper⟩

end CycleQ2IncidenceSurfaceNeighborhood

end

#print axioms CycleQ2IncidenceSurfaceNeighborhood.seedFiber_mem_dimensionOpen
#print axioms CycleQ2IncidenceSurfaceNeighborhood.seedSmoothFamily_smoothOfRelativeDimension
#print axioms CycleQ2IncidenceSurfaceNeighborhood.exists_seed_surface_neighborhood
