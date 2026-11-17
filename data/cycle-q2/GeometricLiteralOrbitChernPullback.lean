import Proposal.GeometricLiteralOrbitChern
import Proposal.GeometricFiniteCechOrbitPullback

/-!
# Pullback of the literal degree-one Chern class

The adjoint on the original differential sheaf sends the original Cartier
cocycle to the cocycle of the pulled back curve, with sections on the actual
inverse images of all its open intersections.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralOrbitChernPullback

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSchemeDifferentialMap
  CycleQ2LiteralNativeDifferentialSections CycleQ2LiteralNativeChernCocycle
  CycleQ2LiteralNativeGaugeSections CycleQ2LiteralOrbitChern
  CycleQ2FiniteCechHOne
open CycleQ2FiniteCechOrbitPullback (push pullOne pullOne_closed cover_top)

variable (f : Surface ⟶ Surface) (hc : ∀ (U : Surface.Opens) (c : ℂ),
    f.app U (coefficientOn Surface.sheaf globalCoefficient U c) =
      coefficientOn Surface.sheaf globalCoefficient (f ⁻¹ᵁ U) c)

def differentialAddMap : differentialAddSheaf ⟶ push f.base differentialAddSheaf :=
  (SheafOfModules.toSheaf Surface.ringCatSheaf).map
    (schemeDifferentialMap f globalCoefficient globalCoefficient hc)

theorem pullOne_chern :
    pullOne f.base (differentialAddMap f hc) cover chernOne =
      translatedOne f (translatedCover f) id (fun _ => le_rfl) := by
  funext u v
  exact (translatedOne_eq_differentialMap f hc u v).symm

theorem pullOne_translated (g : Surface ⟶ Surface) :
    pullOne f.base (differentialAddMap f hc) (translatedCover g)
      (translatedOne g (translatedCover g) id (fun _ => le_rfl)) =
        translatedOne (f ≫ g) (translatedCover (f ≫ g)) id (fun _ => le_rfl) := by
  funext u v
  exact (translatedOne_comp g f hc u v).symm

local instance schemeSheavesHasExt (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

theorem class_pullOne_chern :
    cechOneClass _ (cover_top f.base cover cover_covers)
      (pullOne f.base (differentialAddMap f hc) cover chernOne)
      (pullOne_closed f.base _ _ _ chernOne_closed) = translatedClass f := by
  unfold translatedClass
  congr 1
  exact pullOne_chern f hc

theorem class_pullOne_translated (g : Surface ⟶ Surface) :
    cechOneClass _ (cover_top f.base (translatedCover g) (translatedCover_top g))
      (pullOne f.base (differentialAddMap f hc) (translatedCover g)
        (translatedOne g (translatedCover g) id (fun _ => le_rfl)))
      (pullOne_closed f.base _ _ _ (translatedOne_closed g _ id (fun _ => le_rfl))) =
        translatedClass (f ≫ g) := by
  unfold translatedClass
  congr 1
  exact pullOne_translated f hc g

end CycleQ2LiteralOrbitChernPullback

end

#print axioms CycleQ2LiteralOrbitChernPullback.class_pullOne_chern
#print axioms CycleQ2LiteralOrbitChernPullback.class_pullOne_translated
