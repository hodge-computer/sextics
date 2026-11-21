import Proposal.GeometricSeedFermatPoint
import Proposal.GeometricSeedFermatProper

/-!
# A nonempty smooth proper weighted projective seed

The original graded quotient now has its smooth structure morphism,
an explicit complex-valued point, and a properness proof for that same
structure morphism. This file assembles those constructions and removes
the need for a supplied cube-root parameter using the previously proved
existence theorem over the actual complex coefficient field.

Status: source-only proof draft. No Lean elaboration, compilation, or
kernel replay has been run. This is one geometric seed construction;
the protected residue-exactness theorem remains open. Prepared for `fqlx`
with OpenAI ChatGPT assistance, following Ben Diamond's geometric route.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2SeedFermatGeometry

open AlgebraicGeometry CycleQ2SeedFermatProj

/-- Nonemptiness, smoothness, and properness concern the same original
weighted projective scheme and the same complex structure morphism. -/
theorem nonempty_smooth_proper (r : ℂ) (hr : r ^ 3 = 2) :
    Nonempty (threefold r) ∧
      Smooth (threefoldToComplex r) ∧ IsProper (threefoldToComplex r) :=
  ⟨CycleQ2SeedFermatPoint.threefold_nonempty r hr,
    CycleQ2SeedFermatProjSmooth.threefold_smooth r hr,
    CycleQ2SeedFermatProper.threefold_proper r⟩

/-- A closed existence statement for the actual nonempty smooth proper
projective seed, without a supplied root or geometric premise. -/
theorem exists_nonempty_smooth_proper :
    ∃ r : ℂ, r ^ 3 = 2 ∧ Nonempty (threefold r) ∧
      Smooth (threefoldToComplex r) ∧ IsProper (threefoldToComplex r) := by
  obtain ⟨r, hr, _⟩ := CycleQ2SeedFermatProjSmooth.exists_threefold_smooth
  exact ⟨r, hr, nonempty_smooth_proper r hr⟩

end CycleQ2SeedFermatGeometry

end

#print axioms CycleQ2SeedFermatGeometry.nonempty_smooth_proper
#print axioms CycleQ2SeedFermatGeometry.exists_nonempty_smooth_proper
