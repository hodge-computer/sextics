import Proposal.GeometricOpenDifferentialSheaf

/-!
# Canonical scheme cotangent maps and their actual composition

The canonical scheme differential map is adjointed through the genuine
pullback/pushforward adjunction. Composition uses the actual pullback
composition isomorphism and the corresponding pushforward mate. The
identities are proved on the original universal function differentials.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricSchemeCotangentMaps

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSchemeDifferentialMap

section Mates

variable {C D : Type*} [Category C] [Category D]
  {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
  (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)

theorem conjugate_homEquiv (α : L₂ ⟶ L₁) (M : C) (N : D) (f : L₁.obj M ⟶ N) :
    a₂.homEquiv M N (α.app M ≫ f) =
      a₁.homEquiv M N f ≫ (conjugateEquiv a₁ a₂ α).app N := by
  rw [Adjunction.homEquiv_apply, Functor.map_comp, ← Category.assoc,
    ← unit_conjugateEquiv a₁ a₂ α M, Category.assoc,
    ← (conjugateEquiv a₁ a₂ α).naturality f]
  rw [Adjunction.homEquiv_apply, Category.assoc]

end Mates

variable {X Y Z : Scheme.{0}} (j : X ⟶ Y)
  (cX : ℂ →+* Γ(X, ⊤)) (cY : ℂ →+* Γ(Y, ⊤))
  (hc : ∀ (U : Y.Opens) (c : ℂ),
    j.app U (coefficientOn Y.sheaf cY U c) =
      coefficientOn X.sheaf cX (j ⁻¹ᵁ U) c)

def cotangentMap :
    (Scheme.Modules.pullback j).obj (differentialSheaf Y.sheaf cY) ⟶
      differentialSheaf X.sheaf cX :=
  ((Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv
    (differentialSheaf Y.sheaf cY) (differentialSheaf X.sheaf cX)).symm
      (schemeDifferentialMap j cX cY hc)

theorem cotangentMap_adjunct :
    (Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv
        (differentialSheaf Y.sheaf cY) (differentialSheaf X.sheaf cX)
        (cotangentMap j cX cY hc) = schemeDifferentialMap j cX cY hc :=
  ((Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv
    (differentialSheaf Y.sheaf cY) (differentialSheaf X.sheaf cX)).apply_symm_apply _

theorem cotangentMap_unit_D (U : Y.Opens) (a : Γ(Y, U)) :
    (cotangentMap j cX cY hc).val.app (op (j ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
          (differentialSheaf Y.sheaf cY)).val.app (op U)
            ((universalDifferential Y.sheaf cY).d a)) =
      (universalDifferential X.sheaf cX).d (j.app U a) := by
  have h := congrArg (fun f => f.val.app (op U) ((universalDifferential Y.sheaf cY).d a))
    (cotangentMap_adjunct j cX cY hc)
  exact h.trans (schemeDifferentialMap_D j cX cY hc U a)

theorem cotangentMap_congr {k : X ⟶ Y} (h : j = k)
    (hk : ∀ (U : Y.Opens) (c : ℂ),
      k.app U (coefficientOn Y.sheaf cY U c) =
        coefficientOn X.sheaf cX (k ⁻¹ᵁ U) c) :
    (Scheme.Modules.pullbackCongr h).hom.app (differentialSheaf Y.sheaf cY) ≫
        cotangentMap k cX cY hk = cotangentMap j cX cY hc := by
  subst k
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp]

theorem cotangentMap_eq_open [IsOpenImmersion j] :
    cotangentMap j cX cY hc =
      (CycleQ2GeometricOpenDifferentialSheaf.pullbackOpenDifferentialIso j cX cY hc).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv
    (differentialSheaf Y.sheaf cY) (differentialSheaf X.sheaf cX)).injective
  exact (cotangentMap_adjunct j cX cY hc).trans
    (CycleQ2GeometricOpenDifferentialSheaf.pullbackOpenDifferentialIso_adjunct j cX cY hc).symm

section Composition

variable (g : Z ⟶ X) (cZ : ℂ →+* Γ(Z, ⊤))
  (hg : ∀ (U : X.Opens) (c : ℂ),
    g.app U (coefficientOn X.sheaf cX U c) =
      coefficientOn Z.sheaf cZ (g ⁻¹ᵁ U) c)

include hc hg in
theorem compositionCoefficient (U : Y.Opens) (c : ℂ) :
    (g ≫ j).app U (coefficientOn Y.sheaf cY U c) =
      coefficientOn Z.sheaf cZ ((g ≫ j) ⁻¹ᵁ U) c := by
  change g.app (j ⁻¹ᵁ U) (j.app U (coefficientOn Y.sheaf cY U c)) = _
  rw [hc, hg]
  rfl

theorem schemeDifferentialMap_comp :
    schemeDifferentialMap (g ≫ j) cZ cY (compositionCoefficient j cX cY hc g cZ hg) =
      schemeDifferentialMap j cX cY hc ≫
        (Scheme.Modules.pushforward j).map (schemeDifferentialMap g cZ cX hg) ≫
        (Scheme.Modules.pushforwardComp g j).hom.app (differentialSheaf Z.sheaf cZ) := by
  symm
  apply schemeDifferentialMap_unique
  intro U a
  change (schemeDifferentialMap g cZ cX hg).val.app (op (j ⁻¹ᵁ U))
    ((schemeDifferentialMap j cX cY hc).val.app (op U)
      ((universalDifferential Y.sheaf cY).d a)) = _
  rw [schemeDifferentialMap_D, schemeDifferentialMap_D]
  rfl

theorem cotangentMap_comp :
    (Scheme.Modules.pullbackComp g j).inv.app (differentialSheaf Y.sheaf cY) ≫
        (Scheme.Modules.pullback g).map (cotangentMap j cX cY hc) ≫
        cotangentMap g cZ cX hg =
      cotangentMap (g ≫ j) cZ cY (compositionCoefficient j cX cY hc g cZ hg) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (g ≫ j)).homEquiv
    (differentialSheaf Y.sheaf cY) (differentialSheaf Z.sheaf cZ)).injective
  rw [conjugate_homEquiv
      ((Scheme.Modules.pullbackPushforwardAdjunction j).comp
        (Scheme.Modules.pullbackPushforwardAdjunction g))
      (Scheme.Modules.pullbackPushforwardAdjunction (g ≫ j)),
    Scheme.Modules.conjugateEquiv_pullbackComp_inv,
    Adjunction.comp_homEquiv]
  change (Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv
      (differentialSheaf Y.sheaf cY) _
      ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv
        ((Scheme.Modules.pullback j).obj (differentialSheaf Y.sheaf cY))
        (differentialSheaf Z.sheaf cZ)
        ((Scheme.Modules.pullback g).map (cotangentMap j cX cY hc) ≫
          cotangentMap g cZ cX hg)) ≫
        (Scheme.Modules.pushforwardComp g j).hom.app (differentialSheaf Z.sheaf cZ) = _
  rw [Adjunction.homEquiv_naturality_left, cotangentMap_adjunct,
    Adjunction.homEquiv_naturality_right, cotangentMap_adjunct, cotangentMap_adjunct]
  exact (schemeDifferentialMap_comp j cX cY hc g cZ hg).symm

theorem cotangentMap_square {W : Scheme.{0}} (k : W ⟶ Y) (r : Z ⟶ W)
    (cW : ℂ →+* Γ(W, ⊤))
    (hk : ∀ (U : Y.Opens) (c : ℂ),
      k.app U (coefficientOn Y.sheaf cY U c) =
        coefficientOn W.sheaf cW (k ⁻¹ᵁ U) c)
    (hr : ∀ (U : W.Opens) (c : ℂ),
      r.app U (coefficientOn W.sheaf cW U c) =
        coefficientOn Z.sheaf cZ (r ⁻¹ᵁ U) c)
    (h : g ≫ j = r ≫ k) :
    (Scheme.Modules.pullbackComp g j).hom.app (differentialSheaf Y.sheaf cY) ≫
        (Scheme.Modules.pullbackCongr h).hom.app (differentialSheaf Y.sheaf cY) ≫
        (Scheme.Modules.pullbackComp r k).inv.app (differentialSheaf Y.sheaf cY) ≫
        (Scheme.Modules.pullback r).map (cotangentMap k cW cY hk) ≫
        cotangentMap r cZ cW hr =
      (Scheme.Modules.pullback g).map (cotangentMap j cX cY hc) ≫
        cotangentMap g cZ cX hg := by
  rw [cotangentMap_comp k cW cY hk r cZ hr,
    cotangentMap_congr (g ≫ j) cZ cY (compositionCoefficient j cX cY hc g cZ hg) h
      (compositionCoefficient k cW cY hk r cZ hr),
    ← cotangentMap_comp j cX cY hc g cZ hg]
  exact Iso.hom_inv_id_assoc ((Scheme.Modules.pullbackComp g j).app
    (differentialSheaf Y.sheaf cY)) _

end Composition

end CycleQ2GeometricSchemeCotangentMaps

end

#print axioms CycleQ2GeometricSchemeCotangentMaps.cotangentMap_unit_D
#print axioms CycleQ2GeometricSchemeCotangentMaps.schemeDifferentialMap_comp
#print axioms CycleQ2GeometricSchemeCotangentMaps.cotangentMap_comp
#print axioms CycleQ2GeometricSchemeCotangentMaps.cotangentMap_square
