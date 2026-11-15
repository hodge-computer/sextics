import Proposal.GeometricSeedAffineComparisonSections
import Proposal.GeometricSeedImageSheafEmbedding
import Proposal.GeometricSeedProjectiveSheafTransitions

/-!
# A unique native overlap transition with the prescribed image embedding

The fixed canonical comparisons embed the original overlap image sheaves
in the associated rank-three sheaf over the actual overlap ring. These
embeddings are monomorphisms. The established native transition satisfies
the fourteenth-power ambient square and is the unique morphism with that
square. Its global-section embeddings are the fixed literal image vectors.

These embeddings are induced by the already specified overlap comparisons.
Binding their rank-three targets and their maps to one global free sheaf
is still required before using this uniqueness on different pair overlaps.
No triple-overlap cocycle is asserted here.

Source-only draft: no Lean elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedOverlapImageMonomorphism

open CategoryTheory AlgebraicGeometry
open CycleQ2SeedProjectiveImageRestriction CycleQ2SeedProjectiveImageCompatibility
  CycleQ2SeedProjectiveLocalizedDuality CycleQ2SeedAffineComparisonSections
  CycleQ2SeedProjectiveAffineOverlap CycleQ2SeedOverlapTransitionModels
  CycleQ2SeedProjectiveOverlapComparisons CycleQ2SeedProjectiveSheafTransitions
  CycleQ2SeedImageSheafEmbedding

def leftOverlapEmbedding (i j : Fin 3) :
    leftImageOverlap i j ⟶ rankThreeSheaf (OverlapSections i j) :=
  (leftImageComparison i j).hom ≫ leftModelEmbedding i j

def rightOverlapEmbedding (i j : Fin 3) :
    rightImageOverlap i j ⟶ rankThreeSheaf (OverlapSections i j) :=
  (rightImageComparison i j).hom ≫ rightModelEmbedding i j

instance leftOverlapEmbedding_mono (i j : Fin 3) : Mono (leftOverlapEmbedding i j) := by
  unfold leftOverlapEmbedding
  infer_instance

instance rightOverlapEmbedding_mono (i j : Fin 3) : Mono (rightOverlapEmbedding i j) := by
  unfold rightOverlapEmbedding
  infer_instance

/-- The native image transition has the prescribed degree-fourteen ambient square. -/
theorem nativeOverlap_embedding (i j : Fin 3) :
    (imageOverlapTransition i j).hom ≫ rightOverlapEmbedding i j =
      leftOverlapEmbedding i j ≫ scalar14SheafMap (ratioUnit i j) := by
  change ((leftImageComparison i j).hom ≫ (modelImageTransition i j).hom ≫
      (rightImageComparison i j).inv) ≫
        ((rightImageComparison i j).hom ≫ rightModelEmbedding i j) =
    ((leftImageComparison i j).hom ≫ leftModelEmbedding i j) ≫
      scalar14SheafMap (ratioUnit i j)
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [overlapModel_embedding]

/-- Within the fixed overlap model, the embedding square determines the transition. -/
theorem imageOverlapTransition_unique (i j : Fin 3)
    (φ : leftImageOverlap i j ⟶ rightImageOverlap i j)
    (hφ : φ ≫ rightOverlapEmbedding i j =
      leftOverlapEmbedding i j ≫ scalar14SheafMap (ratioUnit i j)) :
    φ = (imageOverlapTransition i j).hom := by
  apply (cancel_mono (rightOverlapEmbedding i j)).mp
  exact hφ.trans (nativeOverlap_embedding i j).symm

/-- The left embedding retains the fixed literal vector on native global sections. -/
theorem leftOverlapEmbedding_global (i j : Fin 3) :
    (moduleSpecΓFunctor (R := OverlapSections i j)).map (leftOverlapEmbedding i j) =
      (leftImageGlobalEquiv i j).toModuleIso.hom ≫ imageInclusion (leftData i j) ≫
        (tilde.isoTop (ModuleCat.of (OverlapSections i j)
          (Fin 3 → OverlapSections i j))).hom := by
  change (moduleSpecΓFunctor (R := OverlapSections i j)).map
      ((leftImageComparison i j).hom ≫ tilde.map (imageInclusion (leftData i j))) = _
  rw [Functor.map_comp, comparisonIso_map, Category.assoc]
  exact congrArg (fun k => (leftImageGlobalEquiv i j).toModuleIso.hom ≫ k)
    (tilde.toOpen_map_app (imageInclusion (leftData i j)) ⊤)

/-- The right embedding uses the same rank-three overlap model and literal vector. -/
theorem rightOverlapEmbedding_global (i j : Fin 3) :
    (moduleSpecΓFunctor (R := OverlapSections i j)).map (rightOverlapEmbedding i j) =
      (rightImageGlobalEquiv i j).toModuleIso.hom ≫ imageInclusion (rightData i j) ≫
        (tilde.isoTop (ModuleCat.of (OverlapSections i j)
          (Fin 3 → OverlapSections i j))).hom := by
  change (moduleSpecΓFunctor (R := OverlapSections i j)).map
      ((rightImageComparison i j).hom ≫ tilde.map (imageInclusion (rightData i j))) = _
  rw [Functor.map_comp, comparisonIso_map, Category.assoc]
  exact congrArg (fun k => (rightImageGlobalEquiv i j).toModuleIso.hom ≫ k)
    (tilde.toOpen_map_app (imageInclusion (rightData i j)) ⊤)

#print axioms leftOverlapEmbedding_mono
#print axioms rightOverlapEmbedding_mono
#print axioms nativeOverlap_embedding
#print axioms imageOverlapTransition_unique
#print axioms leftOverlapEmbedding_global
#print axioms rightOverlapEmbedding_global

end CycleQ2SeedOverlapImageMonomorphism
end
