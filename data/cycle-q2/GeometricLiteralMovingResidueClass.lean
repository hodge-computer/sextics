import Proposal.GeometricLiteralMovingResidueBoundary
import Proposal.GeometricLiteralMovingResidueExact
import Proposal.GeometricFiniteCechHOne

/-!
# The residue one-class of the actual moving divisor

The second-vertex pole lifts have regular boundary, so their residues
form a cocycle in the quotient of the pole sheaf by regular two-forms.
These lifts define a derived one-class on the original surface.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralMovingResidueClass

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2InjectiveCech CycleQ2FiniteInjectiveCech CycleQ2FiniteCechDescent
  CycleQ2FiniteCechHOne CycleQ2LiteralNativeChernCocycle
  CycleQ2SeedSectionAffineInjective CycleQ2LiteralMovingResidueExact
  CycleQ2LiteralMovingDivisorChern CycleQ2LiteralMovingResidueBoundary

open CycleQ2CechTwoToDerived (app app_comp app_zero)
open CycleQ2LiteralNativeDifferentialSections (Surface)

local instance schemeSheavesHasExt (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

variable (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)
variable (b : One differentialAddSheaf pivotCover)
variable (hb : IsOneCocycle differentialAddSheaf pivotCover b)

def residueOne : One (residueQuotient t) pivotCover :=
  mapOne pivotCover (residueComplex t).g (poleOne t ht b)

include hb in
theorem residueOne_closed : IsOneCocycle (residueQuotient t) pivotCover (residueOne t ht b) := by
  intro i j k W hi hj hk
  let S := residueComplex t
  have h := congrArg (app S.g W) (poleOne_boundary t ht b hb i j k W hi hj hk)
  have hzero : boundaryValue S.X₃ pivotCover (mapOne pivotCover S.g (poleOne t ht b)) i j k W hi hj hk = 0 := by
    rw [boundaryValue_mapOne]
    change app S.g W (boundaryValue S.X₂ pivotCover (poleOne t ht b) i j k W hi hj hk) =
      app S.g W (app S.f W _) at h
    rw [app_comp, S.zero, app_zero] at h
    exact h
  change edgeValue S.X₃ pivotCover (mapOne pivotCover S.g (poleOne t ht b)) i k W hi hk =
    edgeValue S.X₃ pivotCover (mapOne pivotCover S.g (poleOne t ht b)) i j W hi hj +
    edgeValue S.X₃ pivotCover (mapOne pivotCover S.g (poleOne t ht b)) j k W hj hk
  dsimp only [boundaryValue] at hzero
  linear_combination (norm := abel) -hzero

def residueClass : (residueQuotient t).H' 1 ⊤ :=
  cechOneClass pivotCover pivotCover_covers (residueOne t ht b) (residueOne_closed t ht b hb)

end CycleQ2LiteralMovingResidueClass
end

#print axioms CycleQ2LiteralMovingResidueClass.residueOne_closed
