import Proposal.GeometricLiteralOrbitTrace
import Proposal.GeometricLiteralOrbitChernRepresentative
import Proposal.GeometricLiteralOrbitCoordinate
import Proposal.GeometricLiteralCotangentTrace

/-!
# The derived residue of the coordinate orbit

The actual projective pullbacks on the stable coordinate triple represent
the full twisted orbit. The normalized global residue therefore evaluates
the retained cubic on this orbit to three times its original value.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralOrbitCoordinateResidue

open CategoryTheory TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricHomogeneousWeight CycleQ2CanonicalCoordinateH2
  CycleQ2CanonicalResidueNonzero CycleQ2CanonicalCubicDiagram
  CycleQ2IncidenceFirstOrderCanonicalH2 CycleQ2LiteralCotangentTrace
  CycleQ2LiteralOrbitTrace CycleQ2LiteralOrbitCoordinate

theorem trace_coordinate (q : HomogeneousCoordinateTop 57) :
    algebraicTrace (cubicH2 firstOrderWeightedCubic (structureCoordinateClass q)) =
      canonicalSectionTrace (cubicTripleSection firstOrderWeightedCubic q) :=
  (congrArg algebraicTrace (cubicH2_coordinateConnecting firstOrderWeightedCubic q)).trans
    (algebraicTrace_eq _)

theorem weightedTriple_cubic_trace (z : ℂ) (hz : z^3 = 1)
    (hprim : z^2 + z + 1 = 0) (q : HomogeneousCoordinateTop 57) :
    algebraicTrace (cubicH2 firstOrderWeightedCubic (structureCoordinateClass (weightedTriple z hz q))) =
    (3 : ℕ) • algebraicTrace (cubicH2 firstOrderWeightedCubic (structureCoordinateClass q)) := by
  have hw : CycleQ2LiteralOrbitCoordinate.weightedTriple z hz q = orbitSection q :=
    HomogeneousLocalization.val_injective _
      ((CycleQ2LiteralOrbitCoordinate.weightedTriple_val z hz q).trans (orbitSection_val z hz hprim q).symm)
  rw [hw, trace_coordinate, trace_coordinate]
  exact orbitSection_cubic_trace q

end CycleQ2LiteralOrbitCoordinateResidue
end

#print axioms CycleQ2LiteralOrbitCoordinateResidue.weightedTriple_cubic_trace
