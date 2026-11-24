import Proposal.GeometricLiteralMovingResidueGluing
import Proposal.GeometricLiteralMovingResidueClass

/-!
# The derived residue class of a surface differential cocycle

The logarithmic residue one-cocycle on the moving pivot cover is the
image of its surface one-cocycle under the residue sheaf morphism.
The equality persists after passage to derived cohomology.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralMovingResidueDifferentialClass

open CategoryTheory CategoryTheory.Abelian Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2InjectiveCech CycleQ2FiniteInjectiveCech CycleQ2FiniteCechDescent
  CycleQ2FiniteCechHOne CycleQ2LiteralNativeChernCocycle
  CycleQ2SeedSectionAffineInjective CycleQ2LiteralMovingDivisorChern
  CycleQ2LiteralMovingResidueGluing CycleQ2LiteralMovingResidueClass

local instance schemeSheavesHasExt (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

variable (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)
variable (b : One differentialAddSheaf pivotCover)

theorem surfaceResidue_mapOne :
    mapOne pivotCover (surfaceResidue t ht) b = residueOne t ht b := by
  funext i j
  exact surfaceResidue_app t ht (frameAt j (pivotCover i ⊓ pivotCover j) inf_le_right) (b i j)

theorem surfaceResidue_class (hb : IsOneCocycle differentialAddSheaf pivotCover b) :
    (cechOneClass pivotCover pivotCover_covers b hb).comp
      (Ext.mk₀ (surfaceResidue t ht)) (Nat.add_zero 1) = residueClass t ht b hb := by
  rw [cechOneClass_naturality]
  unfold residueClass
  congr 1
  exact surfaceResidue_mapOne t ht b

end CycleQ2LiteralMovingResidueDifferentialClass
end

#print axioms CycleQ2LiteralMovingResidueDifferentialClass.surfaceResidue_class
