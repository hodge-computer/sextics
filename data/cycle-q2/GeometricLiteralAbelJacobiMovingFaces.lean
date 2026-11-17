import Proposal.GeometricLiteralAbelJacobiRefinedCup
import Proposal.GeometricLiteralMovingResidueBoundary
import Proposal.GeometricLiteralMovingResidueExact
import Proposal.GeometricFiniteCechHOneRefinement

/-!
# Canonical faces of the original moving divisor

On the original pivot cover, the residue pole of the restricted
Kodaira–Spencer one-cocycle has regular boundary equal to the canonical
cubic times the cotangent cup with the moving divisor's own transition
dlog. Both edges use the same pivot indices and the same open.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAbelJacobiMovingFaces

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
  CycleQ2FiniteCechDescent CycleQ2FiniteCechRefinement CycleQ2FiniteCechHOne
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralNativeGaugeSections
  CycleQ2LiteralNativeChernCocycle CycleQ2LiteralMovingDivisorChern
  CycleQ2LiteralAbelJacobiContractedCocycle CycleQ2LiteralAbelJacobiRefinedCup
  CycleQ2LiteralMovingResidueFaces CycleQ2LiteralMovingResidueBoundary
  CycleQ2LiteralMovingResidueExact CycleQ2SeedSectionAffineInjective
  CycleQ2GeometricExteriorSheaf CycleQ2CanonicalResidueDiagram

open CycleQ2LiteralNativeDifferentialSections (Surface DifferentialSheaf sheafLogDifferential)
open CycleQ2CechTwoToDerived (app)

abbrev parentVertex (i : VertexIndex) : Vertex := i.1

theorem pivot_le_native (i : VertexIndex) : pivotCover i ≤ cover (parentVertex i) := inf_le_left

def pivotOne : One differentialAddSheaf pivotCover :=
  restrictOne cover pivotCover parentVertex pivot_le_native contractedOne

theorem pivotOne_closed : IsOneCocycle differentialAddSheaf pivotCover pivotOne :=
  restrictOne_closed cover pivotCover parentVertex pivot_le_native contractedOne contractedOne_closed

theorem pivotOne_value (i j : VertexIndex) (W : Surface.Opens) (hi : W ≤ pivotCover i) (hj : W ≤ pivotCover j) :
    edgeValue differentialAddSheaf pivotCover pivotOne i j W hi hj =
      contractedValue i.1 j.1 W (hi.trans (pivot_le_native i)) (hj.trans (pivot_le_native j)) :=
  (edgeValue_restrictOne cover pivotCover parentVertex pivot_le_native contractedOne i j W hi hj).trans
    (edgeValue_contractedOne _ _ _ _ _)

variable (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)

abbrev movingCup : Two coefficientSheaf pivotCover :=
  scalarCup pivotCover parentVertex pivot_le_native (logOne (movingSystem t ht))

abbrev cubicMap : coefficientSheaf ⟶ CycleQ2CanonicalResidueSheaf.canonicalResidueAdditiveComplex.X₁ :=
  (globalFormAdditiveDiagram tangentCubicForm).τ₁

theorem moving_edge (i j : VertexIndex) (W : Surface.Opens) (hi : W ≤ pivotCover i) (hj : W ≤ pivotCover j) :
    edgeValue differentialAddSheaf pivotCover (logOne (movingSystem t ht)) i j W hi hj =
      sheafLogDifferential W (positiveTransition (frameAt i W hi) (frameAt j W hj)) := by
  rw [logOne_common]
  change sheafLogDifferential W ((movingUnit t ht _ _)⁻¹) = _
  rw [movingUnit_eq]
  rfl

theorem moving_wedge (i j k : VertexIndex) (W : Surface.Opens)
    (hi : W ≤ pivotCover i) (hj : W ≤ pivotCover j) (hk : W ≤ pivotCover k) :
    wedgeSection Surface.sheaf DifferentialSheaf.val 2 W
      ![sheafLogDifferential W (positiveTransition (frameAt j W hj) (frameAt k W hk)),
        edgeValue differentialAddSheaf pivotCover pivotOne i j W hi hj] =
      app cubicMap W (faceValue coefficientSheaf pivotCover (movingCup t ht) i j k W hi hj hk) := by
  rw [← moving_edge t ht j k W hj hk, pivotOne_value]
  exact wedge_face pivotCover parentVertex pivot_le_native (logOne (movingSystem t ht)) i j k W hi hj hk

/-- The pole cochain lies in the actual moving divisor's pole sheaf.
Its full boundary is the image of the cubically weighted scalar faces. -/
theorem pole_boundary (i j k : VertexIndex) (W : Surface.Opens)
    (hi : W ≤ pivotCover i) (hj : W ≤ pivotCover j) (hk : W ≤ pivotCover k) :
    boundaryValue (poleSheaf t) pivotCover (poleOne t ht pivotOne) i j k W hi hj hk =
      app (residueComplex t).f W
        (faceValue (residueComplex t).X₁ pivotCover (mapTwo pivotCover cubicMap (movingCup t ht))
          i j k W hi hj hk) := by
  rw [faceValue_mapTwo]
  exact (poleOne_boundary t ht pivotOne pivotOne_closed i j k W hi hj hk).trans
    (congrArg (app (residueComplex t).f W) (moving_wedge t ht i j k W hi hj hk))

end CycleQ2LiteralAbelJacobiMovingFaces
end

#print axioms CycleQ2LiteralAbelJacobiMovingFaces.pole_boundary
