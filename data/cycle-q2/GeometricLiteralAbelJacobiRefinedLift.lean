import Proposal.GeometricLiteralAbelJacobiRefinedCup
import Proposal.GeometricLiteralAbelJacobiSplittingEvaluation
import Proposal.GeometricLiteralCotangentShortExact

/-!
# The boundary of the cotangent lifts on a refined native atlas

The actual cotangent splitting of the first vertex lifts each differential
edge. The original ambient-test tangent supplies its epsilon boundary.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAbelJacobiRefinedLift

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
  CycleQ2FiniteCechDescent CycleQ2LiteralProjectiveIntersections CycleQ2LiteralNativeGaugeSections
  CycleQ2LiteralNativeDifferentialSections CycleQ2LiteralNativeChernCocycle
  CycleQ2LiteralCotangentShortExact CycleQ2LiteralAbelJacobiRefinedCup

open CycleQ2CechTwoToDerived (app)

variable {I : Type} (U : I → Surface.Opens) (r : I → Vertex)
  (hU : ∀ i, U i ≤ cover (r i)) (α : One differentialAddSheaf U)

def edgeLift : One cotangentAdditiveComplex.X₂ U := fun i j =>
  CycleQ2LiteralAbelJacobiSplittingEvaluation.split (r i) (U i ⊓ U j) (inf_le_left.trans (hU i)) (α i j)

theorem edgeLift_reduce :
    mapOne U cotangentAdditiveComplex.g (edgeLift U r hU α) = α := by
  funext i j
  exact CycleQ2LiteralAbelJacobiSplittingEvaluation.split_reduce (r i) (U i ⊓ U j) _ _

theorem edgeLift_value (i j : I) (W : Surface.Opens) (hi : W ≤ U i) (hj : W ≤ U j) :
    edgeValue cotangentAdditiveComplex.X₂ U (edgeLift U r hU α) i j W hi hj =
      CycleQ2LiteralAbelJacobiSplittingEvaluation.split (r i) W (hi.trans (hU i)) (edgeValue differentialAddSheaf U α i j W hi hj) := by
  exact CycleQ2LiteralAbelJacobiSplittingEvaluation.split_restrict (r i) (le_inf hi hj) (inf_le_left.trans (hU i)) (α i j)

private theorem cancel_edge {A : Type*} [AddCommGroup A] (x y z : A) :
    x - (y + z) + y = x - z := by abel

/-- The boundary of the displayed lifts is the actual epsilon inclusion
of the raw cup on every triple, including repeated vertices. -/
theorem edgeLift_boundary (hα : IsOneCocycle differentialAddSheaf U α)
    (i j k : I) (W : Surface.Opens) (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k) :
    boundaryValue cotangentAdditiveComplex.X₂ U (edgeLift U r hU α) i j k W hi hj hk =
      app cotangentAdditiveComplex.f W
        (faceValue coefficientSheaf U (scalarCup U r hU α) i j k W hi hj hk) := by
  unfold boundaryValue
  rw [edgeLift_value, edgeLift_value, edgeLift_value, scalarCup_face]
  have hc : edgeValue differentialAddSheaf U α i k W hi hk =
      edgeValue differentialAddSheaf U α i j W hi hj + edgeValue differentialAddSheaf U α j k W hj hk :=
    hα i j k W hi hj hk
  rw [hc, map_add]
  exact (cancel_edge _ _ _).trans
    (CycleQ2LiteralAbelJacobiSplittingEvaluation.split_change
      (r i) (r j) W (hi.trans (hU i)) (hj.trans (hU j)) _)

end CycleQ2LiteralAbelJacobiRefinedLift
end

#print axioms CycleQ2LiteralAbelJacobiRefinedLift.edgeLift_boundary
