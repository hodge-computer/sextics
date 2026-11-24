import Proposal.GeometricFiniteCechHOne
import Proposal.GeometricLiteralSheafChernKodairaSpencerCup

/-!
# Actual derived degree-one classes of the original Chern and KS cocycles

The original twelve-open one-cocycles now define genuine derived H-one
classes in the original differential and tangent sheaves. The finite
injective construction proves independence of every local primitive
and global quotient gluing. The cotangent connecting comparison is a
further geometric step, not a premise in these class definitions.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralSheafOneClasses

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2FiniteCechHOne CycleQ2LiteralNativeChernCocycle
  CycleQ2LiteralNativeKodairaSpencerCocycle CycleQ2LiteralNativeGaugeSections

local instance schemeSheavesHasExt (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

def chernDerivedClass : differentialAddSheaf.H' 1 ⊤ :=
  cechOneClass cover cover_covers chernOne chernOne_closed

def kodairaSpencerDerivedClass : tangentAddSheaf.H' 1 ⊤ :=
  cechOneClass cover cover_covers kodairaSpencerOne kodairaSpencerOne_closed

theorem chernDerivedClass_eq_descent (d : OneDescent cover chernOne) :
    chernDerivedClass = oneDescentClass cover d :=
  cechOneClass_eq_descentClass cover cover_covers chernOne chernOne_closed d

theorem kodairaSpencerDerivedClass_eq_descent (d : OneDescent cover kodairaSpencerOne) :
    kodairaSpencerDerivedClass = oneDescentClass cover d :=
  cechOneClass_eq_descentClass cover cover_covers kodairaSpencerOne kodairaSpencerOne_closed d

end CycleQ2LiteralSheafOneClasses

end

#print axioms CycleQ2LiteralSheafOneClasses.chernDerivedClass
#print axioms CycleQ2LiteralSheafOneClasses.kodairaSpencerDerivedClass
#print axioms CycleQ2LiteralSheafOneClasses.chernDerivedClass_eq_descent
