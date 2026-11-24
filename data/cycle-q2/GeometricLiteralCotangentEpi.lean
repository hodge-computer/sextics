import Proposal.GeometricLiteralCotangentLocalSplitting
import Proposal.GeometricOpenCoverModuleExactness

/-!
# Epimorphy of the original global cotangent reduction

Morphism equality for scheme modules can be checked after pullback to
an open cover. Applied to the twelve native charts, the local sections
of the cotangent reduction give the global epimorphism.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCotangentEpi

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2CartierSurfaceGrading CycleQ2ProjectiveCartierIdeal
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralAffineCotangent
  CycleQ2LiteralProjectiveCotangent CycleQ2GeometricOpenCoverModuleExactness

theorem closedAffineMap_cover :
    (⨆ i : Vertex, (closedAffineMap {i} (Finset.singleton_nonempty i)).opensRange) = ⊤ := by
  have h (i : Vertex) : (closedAffineMap {i} (Finset.singleton_nonempty i)).opensRange =
      refinedOpen 57 1 i.1 i.2 := by
    change (Proj.awayι _ _ _ _).opensRange = _
    rw [Proj.opensRange_awayι]
    change closedOpen {i} = _
    simp [closedOpen_eq]
  simpa only [h, iSup_prod] using
    (show (⨆ a : Fin 4, ⨆ l : Fin 3, refinedOpen 57 1 a l) = ⊤ from literal_refinedOpen_cover)

theorem cotangentReduction_epi : Epi cotangentReduction := by
  apply epi_of_open_pullbacks (fun i : Vertex => closedAffineMap {i} (Finset.singleton_nonempty i))
    closedAffineMap_cover
  intro i
  let := CycleQ2LiteralCotangentLocalSplitting.chartCotangentReduction_isSplitEpi {i}
    (Finset.singleton_nonempty i)
  infer_instance

end CycleQ2LiteralCotangentEpi

end

#print axioms CycleQ2LiteralCotangentEpi.cotangentReduction_epi
