import Proposal.GeometricLiteralHyperplaneCotangent
import Proposal.GeometricLiteralMovingDivisorCoordinate
import Proposal.GeometricLiteralMovingDivisorChern
import Proposal.GeometricFiniteCechHOneRefinement

/-!
# The coordinate twist of the moving divisor in sheaf cohomology

On every subopen of a pair of the twelve original opens, the actual lifted
hyperplane cocycle restricts to the logarithmic differential of the inverse
seed chart transition raised to the given power.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralMovingDivisorHyperplane

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry Opposite TopologicalSpace
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
  CycleQ2FiniteCechDescent CycleQ2FiniteCechHOne CycleQ2FiniteCechRefinement
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralNativeGaugeSections
  CycleQ2LiteralNativeCupSectionValues CycleQ2LiteralNativeCupDerivedClass
  CycleQ2LiteralNativeChernCocycle CycleQ2LiteralNativeDifferentialSections
  CycleQ2LiteralHyperplaneCotangent CycleQ2LiteralMovingDivisorCoordinate
  CycleQ2LiteralMovingDivisorChern CycleQ2LiteralCotangentShortExact

local instance additiveHasExt : HasExt.{1} (TopCat.Sheaf AddCommGrpCat.{0}
    (CycleQ2LiteralProjectiveCotangent.ClosedSurface : TopCat)) := HasExt.standard _

local instance schemeSheavesHasExt (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

theorem hyperplaneOne_edge (k : ℕ) (u v : Vertex) (W : Surface.Opens)
    (hu : W ≤ cover u) (hv : W ≤ cover v) :
    edgeValue differentialAddSheaf cover (hyperplaneOne k) u v W hu hv =
      sheafLogDifferential W
        ((CycleQ2SeedProjectiveImageCocycle.transitionUnit u.2 v.2 W
          (hu.trans (cover_le_patch u)) (hv.trans (cover_le_patch v)))⁻¹ ^ k) := by
  let s : Finset Vertex := {u,v}
  have hW : W ≤ closedOpen s := common_le_pair u v W hu hv
  let g := CycleQ2LiteralNativeTransitionUnits.coordinateRatio s u v (by simp [s]) (by simp [s])
  unfold edgeValue hyperplaneOne
  rw [res_comp, nativeFormToSheaf_logDifferential]
  change DifferentialSheaf.val.map (homOfLE hW).op (sheafLogDifferential _
    (sectionUnit s (by simp [s]) (CycleQ2LiteralNativeCartierTransitions.reduceUnit s (g ^ k)))) = _
  rw [sheafLogDifferential_restrict, map_pow]
  apply congrArg (sheafLogDifferential W)
  change Units.map _ (Units.map _ (_ ^ k)) = _
  rw [map_pow, map_pow]
  exact congrArg (fun x : Γ(Surface, W)ˣ => x ^ k)
    (restrict_coordinateRatio s (by simp [s]) u v (by simp [s]) (by simp [s]) W hW)

/-- The coordinate Chern class of the pivot frames is the derived class of
the lifted hyperplane cocycle on the original twelve-open cover. -/
theorem coordinateClass_eq_hyperplaneClass (k : ℕ) :
    coordinateClass k = hyperplaneClass k := by
  let h (a : VertexIndex) : pivotCover a ≤ cover a.1 := inf_le_left
  unfold coordinateClass hyperplaneClass
  rw [← cechOneClass_refinement cover pivotCover Prod.fst h cover_covers pivotCover_covers]
  congr 1
  funext a b
  exact (hyperplaneOne_edge k a.1 b.1 _ (inf_le_left.trans (h a))
    (inf_le_right.trans (h b))).symm

/-- The connecting morphism on the moving divisor sees exactly its orbit part. -/
theorem movingClass_connecting (t : Fin 3 → ℂ)
    (ht : ∀ i, CycleQ2SeedSectionAffineInjective.ChartRegular t i) :
    (movingClass t ht).comp cotangentAdditiveShortExact.extClass rfl =
      orbitClass.comp cotangentAdditiveShortExact.extClass rfl := by
  rw [movingClass_eq, coordinateClass_eq_hyperplaneClass, Ext.add_comp,
    hyperplaneClass_connecting_zero, add_zero]

end CycleQ2LiteralMovingDivisorHyperplane

end

#print axioms CycleQ2LiteralMovingDivisorHyperplane.coordinateClass_eq_hyperplaneClass
#print axioms CycleQ2LiteralMovingDivisorHyperplane.movingClass_connecting
