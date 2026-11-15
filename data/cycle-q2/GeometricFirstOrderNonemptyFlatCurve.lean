import Proposal.GeometricSeedSectionNonempty
import Proposal.GeometricFirstOrderFlatCurve

/-!
# The same proper flat first-order curve has a nonempty original closed fiber

The nonemptiness theorem applies to every original section vector, hence
in particular to the vector already chosen for the first-order flatness
construction. The existing seed-fiber isomorphism transports an actual
point. No replacement vector or auxiliary parameter family is used.

Source-only draft. Not elaborated, compiled, or kernel-replayed.
This does not assert an Abel--Jacobi or protected residue comparison.
Prepared for fqlx with OpenAI ChatGPT assistance, 15 November 2026.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2FirstOrderNonemptyFlatCurve

open CategoryTheory AlgebraicGeometry
open CycleQ2IncidencePolynomialJacobianBinding CycleQ2SpecializedProjectiveCurve
  CycleQ2FirstOrderCurve CycleQ2FirstOrderCurveSeedFiber
  CycleQ2FirstOrderFlatCurve CycleQ2SeedSectionNonempty

/-- The closed first-order construction now retains both its original
seed-fiber isomorphism and actual nonemptiness of that fiber. -/
theorem exists_nonempty_proper_flat_firstOrderCurve :
    ∃ t : Fin 3 → ℂ, t ≠ 0 ∧
      AlgebraicGeometry.Flat (firstOrderCurveToBase t) ∧
      IsProper (firstOrderCurveToBase t) ∧
      Nonempty (specializedCurve (seedPoint (57 : ℂ) Complex.I) t ≅
        FirstOrderCurveSeedFiber t) ∧
      Nonempty (specializedCurve (seedPoint (57 : ℂ) Complex.I) t) ∧
      Nonempty (FirstOrderCurveSeedFiber t) := by
  obtain ⟨t, ht, hflat, hproper, ⟨e⟩⟩ := exists_proper_flat_firstOrderCurve
  obtain ⟨x⟩ := seed_specializedCurve_nonempty t
  exact ⟨t, ht, hflat, hproper, ⟨e⟩, ⟨x⟩, ⟨e.hom x⟩⟩

end CycleQ2FirstOrderNonemptyFlatCurve

end

#print axioms CycleQ2FirstOrderNonemptyFlatCurve.exists_nonempty_proper_flat_firstOrderCurve
