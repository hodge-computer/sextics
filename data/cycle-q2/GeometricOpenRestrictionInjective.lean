import Proposal.GeometricAffineCohomology
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Restriction of injective additive sheaves to an open

On a thin site, the presheaf left Kan extension from the slice over `U` is
extension by zero. Its value on an object mapping to `U` is the original
value, and at every other object the indexing category of its colimit is
empty. It therefore preserves monomorphisms, as does its sheafification.
The right adjoint, restriction to the slice, preserves injective objects.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CycleQ2GeometricSheafCohomologyRestriction

open CategoryTheory CategoryTheory.Limits Opposite

variable {C : Type} [Category.{0} C] [Quiver.IsThin C]

private theorem overLan_preservesMonomorphisms (U : C) :
    ((Over.forget U).op.lan (H := AddCommGrpCat.{0})).PreservesMonomorphisms where
  preserves {P Q} f hf := by
    let L := (Over.forget U).op
    let : (Over.forget U).Full :=
      ⟨fun g => ⟨Over.homMk g (Subsingleton.elim _ _), rfl⟩⟩
    apply (NatTrans.mono_iff_mono_app _).2
    intro V
    by_cases h : Nonempty (V.unop ⟶ U)
    · obtain ⟨g⟩ := h
      let W := op (Over.mk g)
      change Mono ((L.lan.map f).app (L.obj W))
      have e := NatTrans.congr_app (L.lanUnit.naturality f) W
      change f.app W ≫ (L.lanUnit.app Q).app W =
        (L.lanUnit.app P).app W ≫ (L.lan.map f).app (L.obj W) at e
      rw [(IsIso.eq_inv_comp _).2 e.symm]
      infer_instance
    · have z : IsZero (colimit (CostructuredArrow.proj L V ⋙ P)) := by
        apply (IsZero.iff_id_eq_zero _).2
        apply colimit.hom_ext
        intro t
        exact (h ⟨t.hom.unop ≫ t.left.unop.hom⟩).elim
      exact (z.of_iso (L.leftKanExtensionObjIsoColimit P V)).mono _

/-- Restriction to the over-site of an object of a thin site preserves
injective sheaves of abelian groups. -/
theorem overPullback_preservesInjectiveObjects (J : GrothendieckTopology C) (U : C) :
    (restrictionFunctor J U).PreservesInjectiveObjects := by
  let := overLan_preservesMonomorphisms U
  let : (Functor.sheafPullbackConstruction.sheafPullback (Over.forget U)
      AddCommGrpCat (J.over U) J).PreservesMonomorphisms := by
    unfold Functor.sheafPullbackConstruction.sheafPullback
    infer_instance
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Over.forget U)
      AddCommGrpCat (J.over U) J)

end CycleQ2GeometricSheafCohomologyRestriction

#print axioms CycleQ2GeometricSheafCohomologyRestriction.overPullback_preservesInjectiveObjects
