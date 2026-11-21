import Proposal.GeometricLiteralThreefoldStructureVanishing
import Proposal.GeometricLiteralThreefoldHodgeCech

/-!
# Function-valued Cech primitives on the original four affine opens

Ordinary H-two vanishing transfers to the terminal-open Ext group. The
checked four-open comparison then lifts each closed four-face cochain to
an actual six-edge primitive on the fixed threefold's original cover.
This removes the function component of a hypothetical unfiltered boundary.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralThreefoldFunctionPrimitives

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open CycleQ2GeometricProjectiveHOne (structureAdditiveSheaf affineFrameHOne_subsingleton)
open CycleQ2LiteralAmbientCharts (fixedOpen fixedOpen_cover fixedChart)
open CycleQ2LiteralThreefoldHodgeCech (Threefold)
open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2GeometricSheafCohomologyRestriction (terminalCohomologyEquiv)

local instance (X : TopCat.{0}) : HasExt.{1} (AbSheaf X) := HasExt.standard _

abbrev O := structureAdditiveSheaf Threefold

/-- The terminal-open degree-two group is the same zero ordinary group. -/
theorem terminal_two_subsingleton : Subsingleton (O.H' 2 ⊤) := by
  letI := CycleQ2LiteralThreefoldStructureVanishing.ordinary_vanishing.2
  exact (terminalCohomologyEquiv _ O ⊤ isTerminalTop 2).injective.subsingleton

theorem chart_one_subsingleton (i : Fin 4) : Subsingleton (O.H' 1 (fixedOpen i)) :=
  affineFrameHOne_subsingleton (fixedChart i).symm O (Iso.refl _)

/-- Every closed function-valued four-face cochain on the original cover has
an actual primitive on its six original pair intersections. -/
theorem two_primitive (c : CycleQ2CechTwoToDerived.Two O fixedOpen)
    (hc : CycleQ2CechTwoToDerived.d2 O fixedOpen c = 0) :
    ∃ b : CycleQ2CechTwoToDerived.One O fixedOpen,
      CycleQ2CechTwoToDerived.d1 O fixedOpen b = c := by
  letI := terminal_two_subsingleton
  exact CycleQ2CechTwoToDerived.cechTwoClass_eq_zero_implies_boundary fixedOpen
    fixedOpen_cover c hc chart_one_subsingleton (Subsingleton.elim _ _)

end CycleQ2LiteralThreefoldFunctionPrimitives
end

#print axioms CycleQ2LiteralThreefoldFunctionPrimitives.terminal_two_subsingleton
#print axioms CycleQ2LiteralThreefoldFunctionPrimitives.two_primitive
