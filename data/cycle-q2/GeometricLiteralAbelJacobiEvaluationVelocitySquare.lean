import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Section rings on corresponding opens of a commutative square

An open immersion identifies sections on every open contained in its
image. A commutative square identifies the inverse image of that open
with the iterated inverse image on the other side. The resulting ring
equivalence preserves pullback from the base and restriction to subopens.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false

noncomputable section

namespace CycleQ2LiteralAbelJacobiEvaluationVelocitySquare

open CategoryTheory AlgebraicGeometry

variable {S T Y Z : Scheme}
variable (k : S ⟶ Z) (r : Z ⟶ Y) (s : S ⟶ T) (j : T ⟶ Y)
variable (e : k ≫ r = s ≫ j)

theorem square_preimage (e : k ≫ r = s ≫ j) (W : Y.Opens) :
    k ⁻¹ᵁ r ⁻¹ᵁ W = s ⁻¹ᵁ j ⁻¹ᵁ W :=
  congrArg (fun f : S ⟶ Y => f ⁻¹ᵁ W) e

variable [IsOpenImmersion k]

def closedRestriction (e : k ≫ r = s ≫ j) (W : Y.Opens) (h : r ⁻¹ᵁ W ≤ k.opensRange) :
    Γ(Z, r ⁻¹ᵁ W) ≃+* Γ(S, s ⁻¹ᵁ j ⁻¹ᵁ W) :=
  letI := k.isIso_app (r ⁻¹ᵁ W) h
  (asIso (k.app (r ⁻¹ᵁ W)) ≪≫
    S.presheaf.mapIso (eqToIso (square_preimage k r s j e W).symm).op).commRingCatIsoToRingEquiv

theorem closedRestriction_apply (W : Y.Opens) (h : r ⁻¹ᵁ W ≤ k.opensRange)
    (a : Γ(Z, r ⁻¹ᵁ W)) :
    closedRestriction k r s j e W h a =
      k.appLE (r ⁻¹ᵁ W) (s ⁻¹ᵁ j ⁻¹ᵁ W) (square_preimage k r s j e W).ge a := rfl

private theorem appLE_of_eq {X Y : Scheme} {f g : X ⟶ Y} (he : f = g)
    (U : Y.Opens) (V : X.Opens) (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V hf = g.appLE U V hg := by
  subst g
  rfl

theorem closedRestriction_app (W : Y.Opens) (h : r ⁻¹ᵁ W ≤ k.opensRange)
    (a : Γ(Y, W)) :
    closedRestriction k r s j e W h (r.app W a) = s.app (j ⁻¹ᵁ W) (j.app W a) := by
  rw [closedRestriction_apply]
  refine ConcreteCategory.congr_hom (f := r.app W ≫ k.appLE _ _ (square_preimage k r s j e W).ge)
    (g := j.app W ≫ s.app (j ⁻¹ᵁ W)) ?_ a
  exact (Scheme.Hom.comp_appLE k r W (s ⁻¹ᵁ j ⁻¹ᵁ W)
    (square_preimage k r s j e W).ge).symm.trans
      ((appLE_of_eq e W (s ⁻¹ᵁ j ⁻¹ᵁ W) _ le_rfl).trans
        ((s ≫ j).appLE_eq_app (U := W)))

theorem closedRestriction_restrict {W V : Y.Opens} (hWV : W ≤ V)
    (hV : r ⁻¹ᵁ V ≤ k.opensRange) (a : Γ(Z, r ⁻¹ᵁ V)) :
    closedRestriction k r s j e W ((r.preimage_mono hWV).trans hV)
        (Z.presheaf.map (homOfLE (r.preimage_mono hWV)).op a) =
      S.presheaf.map (homOfLE (s.preimage_mono (j.preimage_mono hWV))).op
        (closedRestriction k r s j e V hV a) := by
  rw [closedRestriction_apply, closedRestriction_apply]
  refine ConcreteCategory.congr_hom
    (f := Z.presheaf.map (homOfLE (r.preimage_mono hWV)).op ≫
      k.appLE _ _ (square_preimage k r s j e W).ge)
    (g := k.appLE _ _ (square_preimage k r s j e V).ge ≫
      S.presheaf.map (homOfLE (s.preimage_mono (j.preimage_mono hWV))).op) ?_ a
  rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem closedRestriction_symm_restrict {W V : Y.Opens} (hWV : W ≤ V)
    (hV : r ⁻¹ᵁ V ≤ k.opensRange) (b : Γ(S, s ⁻¹ᵁ j ⁻¹ᵁ V)) :
    (closedRestriction k r s j e W ((r.preimage_mono hWV).trans hV)).symm
        (S.presheaf.map (homOfLE (s.preimage_mono (j.preimage_mono hWV))).op b) =
      Z.presheaf.map (homOfLE (r.preimage_mono hWV)).op
        ((closedRestriction k r s j e V hV).symm b) := by
  apply (closedRestriction k r s j e W ((r.preimage_mono hWV).trans hV)).injective
  rw [RingEquiv.apply_symm_apply, closedRestriction_restrict k r s j e hWV hV,
    RingEquiv.apply_symm_apply]

#print axioms closedRestriction
#print axioms closedRestriction_app
#print axioms closedRestriction_restrict
#print axioms closedRestriction_symm_restrict

end CycleQ2LiteralAbelJacobiEvaluationVelocitySquare

end
