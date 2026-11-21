import Proposal.GeometricFiniteCechLiftComparison
import Proposal.GeometricLiteralAbelJacobiMovingFaces
import Proposal.GeometricLiteralAbelJacobiRefinedLift
import Proposal.GeometricLiteralMovingResidueClass
import Proposal.GeometricCanonicalCubicDiagram

/-!
# The actual moving residue connecting class

The pole of the contracted Kodaira–Spencer one-cocycle and the cotangent
lift of the moving divisor's Chern cocycle have the same regular faces
after multiplication by the fixed cubic. Comparing these two lifts gives
the identity in derived cohomology on the original surface.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralMovingResidueConnecting

open CategoryTheory TopologicalSpace AlgebraicGeometry
  CycleQ2InjectiveCech CycleQ2FiniteInjectiveCech CycleQ2FiniteCechDescent CycleQ2FiniteCechHOne CycleQ2FiniteCechLiftComparison
  CycleQ2LiteralMovingDivisorChern CycleQ2LiteralCotangentShortExact
  CycleQ2LiteralMovingResidueBoundary CycleQ2LiteralMovingResidueExact
  CycleQ2LiteralMovingResidueClass CycleQ2LiteralAbelJacobiMovingFaces
  CycleQ2LiteralAbelJacobiRefinedLift CycleQ2SeedSectionAffineInjective
  CycleQ2LiteralNativeChernCocycle CycleQ2CanonicalCubicDiagram
  CycleQ2IncidenceFirstOrderCanonicalH2

local instance additiveHasExt : HasExt.{1} (TopCat.Sheaf AddCommGrpCat.{0}
    (CycleQ2LiteralProjectiveCotangent.ClosedSurface : TopCat)) := HasExt.standard _

local instance schemeSheavesHasExt (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

variable (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)

private theorem liftedClass_eq {x y : One differentialAddSheaf pivotCover} (e : x = y)
    (hx : IsOneCocycle differentialAddSheaf pivotCover x)
    (hy : IsOneCocycle differentialAddSheaf pivotCover y) :
    cechOneClass pivotCover pivotCover_covers x hx = cechOneClass pivotCover pivotCover_covers y hy := by
  subst y
  rfl

/-- The residue of the genuine contracted class on the moving divisor
has the cubically weighted cotangent boundary of its own Chern class. -/
theorem residueConnecting_contracted :
    residueConnecting t ht ⊤ (residueClass t ht pivotOne pivotOne_closed) =
      cubicH2 firstOrderWeightedCubic
        ((movingClass t ht).comp cotangentAdditiveShortExact.extClass rfl) := by
  let α := logOne (movingSystem t ht)
  let b := edgeLift pivotCover parentVertex pivot_le_native α
  have h := compare_lifted_boundaries pivotCover pivotCover_covers
    cotangentAdditiveShortExact (residueShortExact t ht) cubicMap b
    (poleOne t ht pivotOne) (movingCup t ht)
    (edgeLift_boundary pivotCover parentVertex pivot_le_native α (logOne_closed _))
    (pole_boundary t ht)
  have he : mapOne pivotCover cotangentAdditiveComplex.g b = α :=
    edgeLift_reduce pivotCover parentVertex pivot_le_native α
  rw [liftedClass_eq he _ (logOne_closed (movingSystem t ht))] at h
  exact h.symm

end CycleQ2LiteralMovingResidueConnecting
end

#print axioms CycleQ2LiteralMovingResidueConnecting.residueConnecting_contracted
