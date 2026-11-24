import Proposal.GeometricLiteralMovingDivisorHyperplane
import Proposal.GeometricLiteralMovingDivisorRefinement
import Proposal.GeometricLiteralMovingDivisorOrbitProduct

/-!
# The class of the moving curve on the original projective surface

The product of the three translated Cartier equations generates the pivot
ideal on the common refinement. This identifies the positive Chern class
of the actual moving divisor with the three translates of the seed curve
and the fourth hyperplane twist in degree-one sheaf cohomology.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralMovingDivisorOrbitComparison

open CategoryTheory AlgebraicGeometry TopologicalSpace CycleQ2LinkageComponentAlgebra CycleQ2LiteralOrbitAction
  CycleQ2LiteralOrbitChern CycleQ2LiteralHyperplaneCotangent CycleQ2LiteralMovingDivisorChern
  CycleQ2LiteralMovingDivisorRefinement CycleQ2LiteralMovingDivisorHyperplane
  CycleQ2SeedSectionAffineInjective CycleQ2LiteralSheafOneClasses

local instance schemeSheavesHasExt (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

/-- The degree-ten pivot class is the native product class for the actual order-three action. -/
theorem orbitClass_eq_orbitDerivedClass : orbitClass = orbitDerivedClass complexRoot complexRoot_cube := by
  let a := (closedProjectiveAction complexRoot complexRoot_cube).hom
  apply orbitClass_eq_productDerivedClass (𝟙 _) a (a ≫ a)
  intro i
  exact CycleQ2LiteralMovingDivisorOrbitProduct.productGenerator_span
    (frameAt i.1 _ inf_le_left) i.2 inf_le_right

theorem movingClass_eq_orbit_add_hyperplane (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) :
    movingClass t ht = orbitDerivedClass complexRoot complexRoot_cube + hyperplaneClass 4 := by
  rw [movingClass_eq, orbitClass_eq_orbitDerivedClass, coordinateClass_eq_hyperplaneClass]

/-- The original curve and its two genuine scheme pullbacks occur with multiplicity one. -/
theorem movingClass_eq_three_translates (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) :
    let a := (closedProjectiveAction complexRoot complexRoot_cube).hom
    movingClass t ht = chernDerivedClass + translatedClass a +
      translatedClass (a ≫ a) + hyperplaneClass 4 := by
  dsimp only
  rw [movingClass_eq_orbit_add_hyperplane, orbitDerivedClass_eq_sum]

end CycleQ2LiteralMovingDivisorOrbitComparison

end

#print axioms CycleQ2LiteralMovingDivisorOrbitComparison.orbitClass_eq_orbitDerivedClass
#print axioms CycleQ2LiteralMovingDivisorOrbitComparison.movingClass_eq_three_translates
