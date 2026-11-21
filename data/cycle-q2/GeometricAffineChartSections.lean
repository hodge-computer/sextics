import Proposal.GeometricAffineDifferentialSheaf
import Mathlib.Topology.Sheaves.Over

/-!
# Actual sections on an affine chart of a scheme

The over-site of an open affine chart is equivalent to the open-set site of
its affine spectrum. The comparison of section rings is the composite of
the actual scheme restriction and the actual inverse chart morphism.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricAffineChartSections

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricAffineDifferentialSheaf

variable {X : Scheme.{0}} {U : X.Opens} {A : Type} [CommRing A]
  (e : U.toScheme ≅ Spec (CommRingCat.of A))

def chartOpensEquiv : Over U ≌ Opens (Spec (CommRingCat.of A)) :=
  U.overEquivalence.trans (Opens.mapMapIso (Scheme.forgetToTop.mapIso e)).symm

theorem chartOpensEquiv_obj (V : Over U) :
    (chartOpensEquiv e).functor.obj V = e.inv ⁻¹ᵁ (U.ι ⁻¹ᵁ V.left) := rfl

instance chartOpensFunctor_continuous :
    (chartOpensEquiv e).functor.IsContinuous
      ((Opens.grothendieckTopology X).over U)
      (Opens.grothendieckTopology (Spec (CommRingCat.of A))) := by
  let : (Opens.map e.inv.base).IsContinuous
      (Opens.grothendieckTopology {x : X // x ∈ U})
      (Opens.grothendieckTopology (Spec (CommRingCat.of A))) :=
    Functor.isContinuous_of_coverPreserving
      (compatiblePreserving_opens_map e.inv.base) (coverPreserving_opens_map e.inv.base)
  exact Functor.isContinuous_comp U.overEquivalence.functor (Opens.map e.inv.base)
    ((Opens.grothendieckTopology X).over U)
    (Opens.grothendieckTopology {x : X // x ∈ U})
    (Opens.grothendieckTopology (Spec (CommRingCat.of A)))

instance chartOpensInverse_continuous :
    (chartOpensEquiv e).inverse.IsContinuous
      (Opens.grothendieckTopology (Spec (CommRingCat.of A)))
      ((Opens.grothendieckTopology X).over U) := by
  let : U.overEquivalence.inverse.IsDenseSubsite
      (Opens.grothendieckTopology {x : X // x ∈ U})
      ((Opens.grothendieckTopology X).over U) :=
    inferInstanceAs (U.overEquivalence.symm.functor.IsDenseSubsite
      (Opens.grothendieckTopology {x : X // x ∈ U})
      ((Opens.grothendieckTopology X).over U))
  let : (Opens.map e.hom.base).IsContinuous
      (Opens.grothendieckTopology (Spec (CommRingCat.of A)))
      (Opens.grothendieckTopology {x : X // x ∈ U}) :=
    Functor.isContinuous_of_coverPreserving
      (compatiblePreserving_opens_map e.hom.base) (coverPreserving_opens_map e.hom.base)
  exact Functor.isContinuous_comp (Opens.map e.hom.base) U.overEquivalence.inverse
    (Opens.grothendieckTopology (Spec (CommRingCat.of A)))
    (Opens.grothendieckTopology {x : X // x ∈ U})
    ((Opens.grothendieckTopology X).over U)

private instance restriction_app_isIso (V : Over U) : IsIso (U.ι.app V.left) :=
  Scheme.Hom.isIso_app U.ι V.left (by
    rw [Scheme.Opens.opensRange_ι]
    exact V.hom.le)

def chartSectionIso (V : Over U) :
    Γ(X, V.left) ≅ Γ(Spec (CommRingCat.of A), (chartOpensEquiv e).functor.obj V) :=
  asIso (U.ι.app V.left) ≪≫ asIso (e.inv.app (U.ι ⁻¹ᵁ V.left))

theorem chartSectionIso_hom (V : Over U) :
    (chartSectionIso e V).hom = U.ι.app V.left ≫ e.inv.app (U.ι ⁻¹ᵁ V.left) := rfl

/-- The actual ring comparisons commute with restriction on every subopen. -/
def chartSectionsIso :
    (Over.forget U).op ⋙ X.presheaf ≅
      (chartOpensEquiv e).functor.op ⋙ (Spec (CommRingCat.of A)).presheaf :=
  NatIso.ofComponents (fun V => chartSectionIso e V.unop) (by
    intro V W f
    change X.presheaf.map f.unop.left.op ≫ U.ι.app W.unop.left ≫
        e.inv.app (U.ι ⁻¹ᵁ W.unop.left) =
      (U.ι.app V.unop.left ≫ e.inv.app (U.ι ⁻¹ᵁ V.unop.left)) ≫
        (Spec (CommRingCat.of A)).presheaf.map
          ((chartOpensEquiv e).functor.map f.unop).op
    rw [← Category.assoc, U.ι.naturality, Category.assoc, e.inv.naturality]
    rfl)

def chartSection (V : Over U) : A →+* Γ(X, V.left) :=
  (chartSectionIso e V).inv.hom.comp
    (algebraMap A (AffineSections A ((chartOpensEquiv e).functor.obj V)))

theorem chartSection_naturality {V W : Over U} (f : V ⟶ W) (a : A) :
    X.presheaf.map f.left.op (chartSection e W a) = chartSection e V a := by
  have h := congrArg (fun k => k
    (algebraMap A (AffineSections A ((chartOpensEquiv e).functor.obj W)) a))
      ((chartSectionsIso e).inv.naturality f.op)
  exact h.symm

@[reassoc] private theorem restriction_topIso :
    U.topIso.hom ≫ U.ι.app U =
      U.toScheme.presheaf.map (homOfLE (show U.ι ⁻¹ᵁ U ≤ ⊤ from le_top)).op := by
  rw [Scheme.Opens.topIso_hom, Scheme.Opens.ι_app,
    Scheme.Opens.toScheme_presheaf_map, ← X.presheaf.map_comp]
  exact congrArg X.presheaf.map (Subsingleton.elim _ _)

/-- The terminal chart section map is the usual global affine coordinate
map followed by the actual chart map and the open restriction isomorphism. -/
theorem chartSection_top :
    CommRingCat.ofHom (chartSection e (Over.mk (𝟙 U))) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ e.hom.appTop ≫ U.topIso.hom := by
  let V : Over U := Over.mk (𝟙 U)
  have he : e.hom.appTop ≫ e.inv.appTop = 𝟙 Γ(Spec (CommRingCat.of A), ⊤) :=
    congrArg (fun k : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of A) => k.appTop)
      e.inv_hom_id
  have hc : ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ e.hom.appTop ≫ U.topIso.hom) ≫
      (chartSectionIso e V).hom =
      CommRingCat.ofHom (algebraMap A (AffineSections A ((chartOpensEquiv e).functor.obj V))) := by
    rw [chartSectionIso_hom]
    simp only [Category.assoc]
    change (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ e.hom.appTop ≫
      U.topIso.hom ≫ U.ι.app U ≫ e.inv.app (U.ι ⁻¹ᵁ U) =
        CommRingCat.ofHom (algebraMap A (AffineSections A (e.inv ⁻¹ᵁ (U.ι ⁻¹ᵁ U))))
    rw [restriction_topIso_assoc, e.inv.naturality,
      ← Category.assoc e.hom.appTop e.inv.appTop, he, Category.id_comp]
    rfl
  apply (cancel_mono (chartSectionIso e V).hom).mp
  change (CommRingCat.ofHom (algebraMap A
    (AffineSections A ((chartOpensEquiv e).functor.obj V))) ≫
      (chartSectionIso e V).inv) ≫ (chartSectionIso e V).hom = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, hc]

def schemeCoefficient (f : X ⟶ Spec (CommRingCat.of ℂ)) : ℂ →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ f.appTop).hom

theorem schemeCoefficient_comp {Y : Scheme.{0}} (g : Y ⟶ X)
    (f : X ⟶ Spec (CommRingCat.of ℂ)) (c : ℂ) :
    schemeCoefficient (g ≫ f) c = g.appTop (schemeCoefficient f c) := rfl

theorem coefficientOn_app {Y : Scheme.{0}} (g : Y ⟶ X)
    (f : X ⟶ Spec (CommRingCat.of ℂ)) (V : X.Opens) (c : ℂ) :
    g.app V (coefficientOn X.sheaf (schemeCoefficient f) V c) =
      coefficientOn Y.sheaf (schemeCoefficient (g ≫ f)) (g ⁻¹ᵁ V) c := by
  change g.app V (X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
    (schemeCoefficient f c)) =
      Y.presheaf.map (homOfLE (show g ⁻¹ᵁ V ≤ ⊤ from le_top)).op
        (g.appTop (schemeCoefficient f c))
  exact congrArg (fun k => k (schemeCoefficient f c))
    (g.naturality (homOfLE (show V ≤ ⊤ from le_top)).op)

variable [Algebra ℂ A]
  (f : X ⟶ Spec (CommRingCat.of ℂ))
  (h : e.inv ≫ U.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))

include h

/-- The actual chart comparison respects the complex coefficients supplied
by the actual scheme structure morphism, on every subopen. -/
theorem chartSectionsIso_coefficient (V : Over U) (c : ℂ) :
    (chartSectionIso e V).hom
        (coefficientOn X.sheaf (schemeCoefficient f) V.left c) =
      coefficientOn (Spec.structureSheaf A) (affineCoefficient A)
        ((chartOpensEquiv e).functor.obj V) c := by
  have hs := coefficientOn_app (e.inv ≫ U.ι) f V.left c
  have hg : (e.inv ≫ U.ι) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ A)) := by
    simpa only [Category.assoc] using h
  have hc : schemeCoefficient (Spec.map (CommRingCat.ofHom (algebraMap ℂ A))) =
      affineCoefficient A :=
    congrArg CommRingCat.Hom.hom (affineCoefficient_structureMorphism A).symm
  rw [hg, hc] at hs
  exact hs

theorem chartSection_complex (V : Over U) (c : ℂ) :
    chartSection e V (algebraMap ℂ A c) =
      coefficientOn X.sheaf (schemeCoefficient f) V.left c := by
  have hs := chartSectionsIso_coefficient e f h V c
  rw [affineCoefficientOn] at hs
  exact (congrArg (chartSectionIso e V).inv hs).symm.trans
    (Iso.hom_inv_id_apply (chartSectionIso e V) _)

end CycleQ2GeometricAffineChartSections

end
