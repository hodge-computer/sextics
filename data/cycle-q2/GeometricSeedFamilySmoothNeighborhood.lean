import Proposal.GeometricSeedFamilyZeroCover
import Proposal.GeometricSeedProjectiveFamilyProper
import Proposal.GeometricSeedFermatDimension
import Proposal.GeometricIncidenceProperNeighborhood

/-!
# A proper smooth family neighborhood containing the zero cubic

The relative Jacobian opens cover every point of the actual projective
family over zero coefficients. Properness allows the closed image of
their complement to be removed from the parameter scheme. The resulting
open contains zero, and its entire inverse image lies in the constructed
smooth open of relative dimension three.

The structure morphism is the genuine restriction of the original full
cubic-parameter family. Its smoothness, relative dimension, flatness,
properness, and retention of zero are all proved from those constructions.
No smooth-fiber-to-smooth-family implication is assumed.

Status: source-only proof draft; no elaboration, compilation, or kernel
replay has been run. The protected residue-exactness theorem remains open.
Prepared for `fqlx` with OpenAI ChatGPT assistance, following Ben Diamond
and the project's geometric construction.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedFamilySmoothNeighborhood

open CategoryTheory AlgebraicGeometry
open CycleQ2SeedProjectiveFamily CycleQ2SeedProjectiveSpecialization
  CycleQ2SeedProjectiveFamilyProper CycleQ2SeedFamilyJacobian
  CycleQ2SeedFamilyZeroCover CycleQ2IncidenceProperNeighborhood

local instance family_proper (r : ℂ) : IsProper (familyToParameters r) :=
  familyToParameters_proper r

/-- The actual zero point of the full coefficient parameter scheme. -/
def zeroBasePoint : parameterScheme :=
  zeroParameterMorphism (default : Spec (CommRingCat.of ℂ))

/-- Remove the proper image of the complement of the relative Jacobian open. -/
def seedSmoothBase (r : ℂ) : parameterScheme.Opens :=
  properBaseNeighborhood (familyToParameters r) (smoothOpen r)

theorem zero_mem_seedSmoothBase (r : ℂ) (hr : r ^ 3 = 2) :
    zeroBasePoint ∈ seedSmoothBase r := by
  apply (mem_properBaseNeighborhood_iff (familyToParameters r)
    (smoothOpen r) zeroBasePoint).mpr
  intro x hx
  exact zeroFiber_mem_smoothOpen r hr (default : Spec (CommRingCat.of ℂ)) x hx

def seedSmoothSource (r : ℂ) : (family r).Opens :=
  familyToParameters r ⁻¹ᵁ seedSmoothBase r

theorem seedSmoothSource_le_smoothOpen (r : ℂ) :
    seedSmoothSource r ≤ smoothOpen r :=
  properBaseNeighborhood_preimage_le (familyToParameters r) (smoothOpen r)

/-- The full preimage of the retained base open factors through the
already constructed relative Jacobian open. -/
def sourceToSmoothOpen (r : ℂ) :
    (seedSmoothSource r).toScheme ⟶ (smoothOpen r).toScheme :=
  IsOpenImmersion.lift (smoothOpen r).ι (seedSmoothSource r).ι (by
    rintro x ⟨u, rfl⟩
    exact ⟨⟨u.1, seedSmoothSource_le_smoothOpen r u.2⟩, rfl⟩)

instance sourceToSmoothOpen_isOpenImmersion (r : ℂ) :
    IsOpenImmersion (sourceToSmoothOpen r) := by
  dsimp only [sourceToSmoothOpen]
  infer_instance

theorem sourceToSmoothOpen_fac (r : ℂ) :
    sourceToSmoothOpen r ≫ (smoothOpen r).ι = (seedSmoothSource r).ι :=
  IsOpenImmersion.lift_fac _ _ _

theorem seedSmoothSource_smoothOfRelativeDimension (r : ℂ) :
    SmoothOfRelativeDimension 3
      ((seedSmoothSource r).ι ≫ familyToParameters r) := by
  rw [← sourceToSmoothOpen_fac, Category.assoc]
  exact IsZariskiLocalAtSource.comp
    (smoothOpen_family_smoothOfRelativeDimension r) (sourceToSmoothOpen r)

/-- The genuine target restriction of the original projective family. -/
def seedSmoothFamily (r : ℂ) :
    (seedSmoothSource r).toScheme ⟶ (seedSmoothBase r).toScheme :=
  (familyToParameters r) ∣_ seedSmoothBase r

theorem seedSmoothFamily_smoothOfRelativeDimension (r : ℂ) :
    SmoothOfRelativeDimension 3 (seedSmoothFamily r) := by
  letI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 3) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 3
  change SmoothOfRelativeDimension 3 ((familyToParameters r) ∣_ seedSmoothBase r)
  apply MorphismProperty.of_postcomp (W' := @IsOpenImmersion)
    (@SmoothOfRelativeDimension 3) ((familyToParameters r) ∣_ seedSmoothBase r)
    (seedSmoothBase r).ι (inferInstance : IsOpenImmersion (seedSmoothBase r).ι)
  simpa only [morphismRestrict_ι, seedSmoothSource] using
    seedSmoothSource_smoothOfRelativeDimension r

theorem seedSmoothFamily_smooth (r : ℂ) : Smooth (seedSmoothFamily r) := by
  letI := seedSmoothFamily_smoothOfRelativeDimension r
  exact SmoothOfRelativeDimension.smooth 3 (seedSmoothFamily r)

theorem seedSmoothFamily_flat (r : ℂ) : Flat (seedSmoothFamily r) := by
  letI := seedSmoothFamily_smooth r
  infer_instance

theorem seedSmoothFamily_proper (r : ℂ) : IsProper (seedSmoothFamily r) := by
  change IsProper ((familyToParameters r) ∣_ seedSmoothBase r)
  infer_instance

/-- An actual parameter neighborhood retaining zero, with the original
family proper, flat, and smooth of relative dimension three. -/
theorem exists_seed_smooth_neighborhood (r : ℂ) (hr : r ^ 3 = 2) :
    ∃ V : parameterScheme.Opens, zeroBasePoint ∈ V ∧
      SmoothOfRelativeDimension 3 ((familyToParameters r) ∣_ V) ∧
      Flat ((familyToParameters r) ∣_ V) ∧ IsProper ((familyToParameters r) ∣_ V) :=
  ⟨seedSmoothBase r, zero_mem_seedSmoothBase r hr,
    seedSmoothFamily_smoothOfRelativeDimension r,
    seedSmoothFamily_flat r, seedSmoothFamily_proper r⟩

/-- The parameter witness and the retained smooth proper neighborhood
exist without a supplied root, covering hypothesis, or shrinking premise. -/
theorem exists_smooth_proper_family_neighborhood :
    ∃ r : ℂ, ∃ V : parameterScheme.Opens, r ^ 3 = 2 ∧ zeroBasePoint ∈ V ∧
      SmoothOfRelativeDimension 3 ((familyToParameters r) ∣_ V) ∧
      Flat ((familyToParameters r) ∣_ V) ∧ IsProper ((familyToParameters r) ∣_ V) := by
  obtain ⟨r, hr, _, _, _⟩ :=
    CycleQ2SeedFermatDimension.exists_nonempty_smoothOfRelativeDimension_proper
  obtain ⟨V, hV, hdim, hflat, hproper⟩ := exists_seed_smooth_neighborhood r hr
  exact ⟨r, V, hr, hV, hdim, hflat, hproper⟩

end CycleQ2SeedFamilySmoothNeighborhood

end

#print axioms CycleQ2SeedFamilySmoothNeighborhood.zero_mem_seedSmoothBase
#print axioms CycleQ2SeedFamilySmoothNeighborhood.seedSmoothFamily_smoothOfRelativeDimension
#print axioms CycleQ2SeedFamilySmoothNeighborhood.exists_smooth_proper_family_neighborhood
