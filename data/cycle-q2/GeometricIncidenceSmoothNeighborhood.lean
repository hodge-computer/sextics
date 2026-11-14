import Proposal.GeometricIncidenceSeedFiberCover
import Proposal.GeometricIncidenceProperNeighborhood

/-!
# A proper smooth neighborhood of the original incidence seed

Status: source-only proof draft. No elaboration or kernel replay was run.

The entire actual seed fiber lies in the constructed relative smooth
goodOpen. Properness of the original surface morphism therefore allows
us to remove the closed image of its complement. The resulting base
open contains the original seed point, and its full inverse image lies
in goodOpen.

Factoring that source open through goodOpen proves relative smoothness.
The exact target-restricted original morphism is consequently smooth,
flat, and proper over this base neighborhood. No covering, flatness,
smoothness, or shrinking premise is supplied by the caller.

This does not yet spread the selected regular section or establish the
curve, divisor-class, Abel--Jacobi, or residue-exactness comparisons.
Relative dimension two is not asserted here.

The geometric strategy is due to Ben Diamond and the collaborators cited
in solution.md. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2IncidenceSmoothNeighborhood

open CategoryTheory AlgebraicGeometry
open CycleQ2IncidenceEtaleParameter CycleQ2GeometricIncidenceProj
  CycleQ2IncidenceSmoothSchemeOpens CycleQ2IncidenceSeedFiberCover
  CycleQ2IncidenceSurfaceProper CycleQ2IncidenceProperNeighborhood

attribute [local instance] CycleQ2IncidenceSurfaceProper.fixed_surfaceToBase_proper

/-- Remove the closed image of the complement of the actual smooth open. -/
def seedSmoothBase : (Spec (CommRingCat.of ParameterAlgebra)).Opens :=
  properBaseNeighborhood (surfaceToBase incidencePoint) (goodOpen incidencePoint)

theorem seed_mem_seedSmoothBase : seedBasePoint ∈ seedSmoothBase :=
  (mem_properBaseNeighborhood_iff (surfaceToBase incidencePoint)
    (goodOpen incidencePoint) seedBasePoint).mpr seedFiber_mem_goodOpen

/-- This is the full inverse image of the constructed base open. -/
def seedSmoothSource : (surface incidencePoint).Opens :=
  surfaceToBase incidencePoint ⁻¹ᵁ seedSmoothBase

theorem seedSmoothSource_le_goodOpen : seedSmoothSource ≤ goodOpen incidencePoint :=
  properBaseNeighborhood_preimage_le (surfaceToBase incidencePoint) (goodOpen incidencePoint)

/-- The inclusion of the full inverse image factors through the existing
good open, using the proved inclusion rather than a new premise. -/
def sourceToGoodOpen : seedSmoothSource.toScheme ⟶ (goodOpen incidencePoint).toScheme :=
  IsOpenImmersion.lift (goodOpen incidencePoint).ι seedSmoothSource.ι (by
    rintro x ⟨u, rfl⟩
    exact ⟨⟨u.1, seedSmoothSource_le_goodOpen u.2⟩, rfl⟩)

instance sourceToGoodOpen_isOpenImmersion : IsOpenImmersion sourceToGoodOpen := by
  dsimp only [sourceToGoodOpen]
  infer_instance

theorem sourceToGoodOpen_fac :
    sourceToGoodOpen ≫ (goodOpen incidencePoint).ι = seedSmoothSource.ι :=
  IsOpenImmersion.lift_fac _ _ _

/-- The complete preimage of the base neighborhood is smooth over the
original parameter base. -/
theorem seedSmoothSource_smooth :
    AlgebraicGeometry.Smooth (seedSmoothSource.ι ≫ surfaceToBase incidencePoint) := by
  rw [← sourceToGoodOpen_fac, Category.assoc]
  exact IsZariskiLocalAtSource.comp (goodOpen_smooth incidencePoint) sourceToGoodOpen

theorem seedSmoothSource_flat :
    AlgebraicGeometry.Flat (seedSmoothSource.ι ≫ surfaceToBase incidencePoint) := by
  letI := seedSmoothSource_smooth
  infer_instance

/-- Restriction of the unchanged original family to the actual base open. -/
def seedSmoothFamily : seedSmoothSource.toScheme ⟶ seedSmoothBase.toScheme :=
  (surfaceToBase incidencePoint) ∣_ seedSmoothBase

theorem seedSmoothFamily_smooth : AlgebraicGeometry.Smooth seedSmoothFamily := by
  change AlgebraicGeometry.Smooth ((surfaceToBase incidencePoint) ∣_ seedSmoothBase)
  apply MorphismProperty.of_postcomp (W' := @IsOpenImmersion)
    @AlgebraicGeometry.Smooth ((surfaceToBase incidencePoint) ∣_ seedSmoothBase)
    seedSmoothBase.ι (inferInstance : IsOpenImmersion seedSmoothBase.ι)
  simpa only [morphismRestrict_ι, seedSmoothSource] using seedSmoothSource_smooth

theorem seedSmoothFamily_flat : AlgebraicGeometry.Flat seedSmoothFamily := by
  letI := seedSmoothFamily_smooth
  infer_instance

theorem seedSmoothFamily_proper : IsProper seedSmoothFamily := by
  change IsProper ((surfaceToBase incidencePoint) ∣_ seedSmoothBase)
  infer_instance

/-- A base neighborhood of the original seed with a genuinely proper,
smooth, flat restriction of the original projective surface family. -/
theorem exists_seed_smooth_neighborhood :
    ∃ V : (Spec (CommRingCat.of ParameterAlgebra)).Opens,
      seedBasePoint ∈ V ∧
      AlgebraicGeometry.Smooth ((surfaceToBase incidencePoint) ∣_ V) ∧
      AlgebraicGeometry.Flat ((surfaceToBase incidencePoint) ∣_ V) ∧
      IsProper ((surfaceToBase incidencePoint) ∣_ V) :=
  ⟨seedSmoothBase, seed_mem_seedSmoothBase, seedSmoothFamily_smooth,
    seedSmoothFamily_flat, seedSmoothFamily_proper⟩

end CycleQ2IncidenceSmoothNeighborhood

end

#print axioms CycleQ2IncidenceSmoothNeighborhood.seed_mem_seedSmoothBase
#print axioms CycleQ2IncidenceSmoothNeighborhood.seedSmoothFamily_smooth
#print axioms CycleQ2IncidenceSmoothNeighborhood.seedSmoothFamily_flat
#print axioms CycleQ2IncidenceSmoothNeighborhood.seedSmoothFamily_proper
#print axioms CycleQ2IncidenceSmoothNeighborhood.exists_seed_smooth_neighborhood
