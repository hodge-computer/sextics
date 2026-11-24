import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Frames of an actual associated sheaf on an open

A locally bijective presentation of a sheaf, together with an isomorphism
of its presenting presheaf to another sheaf, gives the unique actual
sheaf isomorphism extending that presentation. The construction applies
after restriction to the over-site of an open. Its inverse is the original
presheaf frame inverse followed by the original presentation map.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LocalSheafificationFrame

open CategoryTheory Opposite TopologicalSpace

section Presentation

variable {C : Type} [Category C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{0}} {P : PresheafOfModules.{0} R.obj}
  {M N : SheafOfModules.{0} R}
  (η : P ⟶ M.val)
  [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  [PresheafOfModules.IsLocallyInjective J η]
  [PresheafOfModules.IsLocallySurjective J η]
  (e : P ≅ N.val)

/-- Extend the prescribed presheaf coordinate along the actual presentation. -/
def coordinate : M ⟶ N where
  val := (PresheafOfModules.homEquivOfIsLocallyBijective η N.isSheaf).symm e.hom

theorem coordinate_factor : η ≫ (coordinate η e).val = e.hom :=
  (PresheafOfModules.homEquivOfIsLocallyBijective η N.isSheaf).apply_symm_apply e.hom

/-- The frame inverse retains the original presentation map. -/
def vector : N ⟶ M where
  val := e.inv ≫ η

/-- A presheaf frame extends to a genuine isomorphism of the presented sheaf. -/
def isoOfPresentation : M ≅ N where
  hom := coordinate η e
  inv := vector η e
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    apply (PresheafOfModules.homEquivOfIsLocallyBijective η M.isSheaf).injective
    change η ≫ ((coordinate η e).val ≫ (e.inv ≫ η)) = η ≫ 𝟙 M.val
    rw [← Category.assoc, coordinate_factor, Iso.hom_inv_id_assoc, Category.comp_id]
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    change (e.inv ≫ η) ≫ (coordinate η e).val = 𝟙 N.val
    rw [Category.assoc, coordinate_factor, Iso.inv_hom_id]

theorem isoOfPresentation_hom_factor : η ≫ (isoOfPresentation η e).hom.val = e.hom :=
  coordinate_factor η e

theorem isoOfPresentation_inv (V : Cᵒᵖ) (s : N.val.obj V) :
    (isoOfPresentation η e).inv.val.app V s = η.app V (e.inv.app V s) := rfl

theorem isoOfPresentation_hom (V : Cᵒᵖ) (s : P.obj V) :
    (isoOfPresentation η e).hom.val.app V (η.app V s) = e.hom.app V s := by
  exact congrArg (fun f : P ⟶ N.val => f.app V s)
    (isoOfPresentation_hom_factor η e)

end Presentation

section Restriction

variable {T : TopCat.{0}} (R : T.Sheaf RingCat.{0})
  (P : PresheafOfModules.{0} R.obj) (U : Opens T)

/-- Restrict the original presheaf, before sheafification, to the open's over-site. -/
def overPresheaf : PresheafOfModules.{0} (R.over U).obj :=
  (PresheafOfModules.pushforward (F := Over.forget U) (𝟙 (R.over U).obj)).obj P

variable {R P} {M : SheafOfModules.{0} R} (η : P ⟶ M.val)

/-- Restrict the same presentation map to the over-site. -/
def overPresentation : overPresheaf R P U ⟶ (M.over U).val :=
  (PresheafOfModules.pushforward (F := Over.forget U) (𝟙 (R.over U).obj)).map η

instance overPresentation_locallyInjective
    [PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology T) η] :
    PresheafOfModules.IsLocallyInjective ((Opens.grothendieckTopology T).over U)
      (overPresentation U η) := by
  change Presheaf.IsLocallyInjective ((Opens.grothendieckTopology T).over U)
    (Functor.whiskerLeft (Over.forget U).op ((PresheafOfModules.toPresheaf R.obj).map η))
  exact Presheaf.isLocallyInjective_whisker
    ((Opens.grothendieckTopology T).over U) (Opens.grothendieckTopology T)
    (Over.forget U) ((PresheafOfModules.toPresheaf R.obj).map η)

instance overPresentation_locallySurjective
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology T) η] :
    PresheafOfModules.IsLocallySurjective ((Opens.grothendieckTopology T).over U)
      (overPresentation U η) := by
  change Presheaf.IsLocallySurjective ((Opens.grothendieckTopology T).over U)
    (Functor.whiskerLeft (Over.forget U).op ((PresheafOfModules.toPresheaf R.obj).map η))
  exact Presheaf.isLocallySurjective_whisker
    ((Opens.grothendieckTopology T).over U) (Opens.grothendieckTopology T)
    (Over.forget U) ((PresheafOfModules.toPresheaf R.obj).map η)

/-- Any actual presheaf frame on an open extends uniquely to its associated
sheaf on that same open; no global trivialization is required. -/
def overIsoOfPresentation
    [PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology T) η]
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology T) η]
    {N : SheafOfModules.{0} (R.over U)} (e : overPresheaf R P U ≅ N.val) :
    M.over U ≅ N :=
  isoOfPresentation (overPresentation U η) e

end Restriction

#print axioms isoOfPresentation
#print axioms isoOfPresentation_hom
#print axioms overIsoOfPresentation

end CycleQ2LocalSheafificationFrame

end
