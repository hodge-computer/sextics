import Proposal.GeometricHodgeStructureVanishing
import Proposal.GeometricHodgeThreefoldLiteral
import Proposal.GeometricSchemeStructureCohomology

/-!
# Vanishing of H-one and H-two of the original threefold's structure sheaf

The full coefficient model is identified with the same fixed incidence
threefold used by the corrected filtered test. Its actual scheme section
maps transport ordinary structure-sheaf cohomology and its vanishing.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralThreefoldStructureVanishing

open AlgebraicGeometry CategoryTheory TopologicalSpace
open CycleQ2GeometricProjectiveHOne (structureAdditiveSheaf)
open CycleQ2LiteralAmbientSmooth (IncidenceFiber)
open CycleQ2GeometricHodgeThreefoldIncidence (literalEval literalIso literal_vertex_unit)
open CycleQ2SchemeStructureCohomology (ordinaryCohomology)
open CycleQ2InjectiveCech (AbSheaf)

local instance (X : TopCat.{0}) : HasExt.{1} (AbSheaf X) := HasExt.standard _

/-- Both intermediate groups vanish on the original incidence threefold. -/
theorem ordinary_vanishing :
    Subsingleton ((structureAdditiveSheaf (IncidenceFiber 57)).H 1) ∧
    Subsingleton ((structureAdditiveSheaf (IncidenceFiber 57)).H 2) := by
  obtain ⟨h1,h2⟩ := CycleQ2HodgeStructureVanishing.ordinary_vanishing literalEval literal_vertex_unit
  constructor
  · letI := h1
    exact (ordinaryCohomology literalIso 1).surjective.subsingleton
  · letI := h2
    exact (ordinaryCohomology literalIso 2).surjective.subsingleton

end CycleQ2LiteralThreefoldStructureVanishing
end

#print axioms CycleQ2LiteralThreefoldStructureVanishing.ordinary_vanishing
