import Proposal.GeometricFirstOrderCurveCharts
import Proposal.GeometricFirstOrderCurvePivotCover
import Proposal.GeometricFirstOrderCurveSeedFiber

/-!
# A proper flat first-order deformation of the original fixed-section curve

The finite regular-section choice, original matrix-pivot cover, actual
tensor quotient comparisons, and source descent provide a nonzero
complex section vector for which the original first-order curve is flat
and proper over the dual numbers. Its closed fiber is the existing
specialized projective curve for that very same vector.

All flatness and covering premises are discharged in this existence
statement. The isomorphism witness is not a nonemptiness assertion for
the curve. Nonempty curves, relative dimension one, integration over a
reduced parameter base, and the Abel--Jacobi comparison remain separate
obligations. This theorem does not assert residue vanishing.

Source-only draft: no elaboration, compilation, or kernel replay was run.
Prepared for `fqlx` with OpenAI ChatGPT assistance, following Ben Diamond
and the geometric strategy credited in solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2FirstOrderFlatCurve

open CategoryTheory AlgebraicGeometry
open CycleQ2IncidencePolynomialJacobianBinding CycleQ2SpecializedProjectiveCurve
  CycleQ2FirstOrderCurve CycleQ2FirstOrderCurveCharts
  CycleQ2FirstOrderCurvePivotCover CycleQ2FirstOrderCurveSeedFiber

/-- A single original nonzero complex section gives an actual proper,
flat first-order curve with its unchanged specialized curve as closed fiber. -/
theorem exists_proper_flat_firstOrderCurve :
    ∃ t : Fin 3 → ℂ, t ≠ 0 ∧
      AlgebraicGeometry.Flat (firstOrderCurveToBase t) ∧
      IsProper (firstOrderCurveToBase t) ∧
      Nonempty (specializedCurve (seedPoint (57 : ℂ) Complex.I) t ≅
        FirstOrderCurveSeedFiber t) := by
  obtain ⟨t, ht, hflat⟩ := exists_nonzero_firstOrderCurveCharts_flat
  exact ⟨t, ht, firstOrderCurveToBase_flat_of_affineCharts t hflat,
    firstOrderCurveToBase_proper t, ⟨firstOrderCurveSeedFiberIso t⟩⟩

end CycleQ2FirstOrderFlatCurve

end

#print axioms CycleQ2FirstOrderFlatCurve.exists_proper_flat_firstOrderCurve
