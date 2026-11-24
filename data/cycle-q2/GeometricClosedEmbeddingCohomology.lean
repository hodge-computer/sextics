import Proposal.GeometricClosedEmbeddingSheafExact
import Proposal.GeometricAffineHigherChartRestriction
import Proposal.GeometricCartierDerivedClass

/-!
# Cohomology under a closed embedding

A class on the closed subspace maps to cohomology of the direct image
by applying the exact functor on Ext and precomposing with the universal
section at the top open. This gives an isomorphism in every degree,
compatible with the connecting morphisms of short exact sequences.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2ClosedEmbeddingCohomology

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace Topology
  CycleQ2InjectiveCech CycleQ2CechTwoToDerived CycleQ2ClosedEmbeddingSheafExact

section Ext
universe u u' v v' w w'
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasExt.{w} C] [HasExt.{w'} D]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  {A : C} {B : D} (i : B ⟶ G.obj A)

private def comparison (Y : C) (n : ℕ) : Ext A Y n →+ Ext B (G.obj Y) n :=
  ((Ext.mk₀ i).precomp (G.obj Y) (zero_add n)).comp (G.mapExtAddHom A Y n)

private theorem comparison_apply {Y : C} {n : ℕ} (x : Ext A Y n) :
    comparison G i Y n x = (Ext.mk₀ i).comp (x.mapExactFunctor G) (zero_add n) := rfl

private theorem comparison_comp {Y Z : C} {n m : ℕ} (x : Ext A Y n) (e : Ext Y Z m) :
    comparison G i Z (n+m) (x.comp e rfl) =
      (comparison G i Y n x).comp (e.mapExactFunctor G) rfl := by
  simp only [comparison_apply, Ext.mapExactFunctor_comp]
  exact (Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)).symm

variable [EnoughInjectives C] [G.PreservesInjectiveObjects]

attribute [local instance] Ext.subsingleton_of_injective

/-- Dimension shifting for a fixed map at the source of Ext. The exact-functor
argument follows Nailin Guan's Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
(Apache 2.0). -/
private theorem comparison_bijective (h : ∀ Y : C, Function.Bijective
    (fun f : A ⟶ Y => i ≫ G.map f)) (Y : C) (n : ℕ) :
    Function.Bijective (comparison G i Y n) := by
  induction n generalizing Y with
  | zero =>
    have he : (comparison G i Y 0) ∘ (Ext.mk₀ (X := A) (Y := Y)) =
        (Ext.mk₀ (X := B) (Y := G.obj Y)) ∘ (fun f : A ⟶ Y => i ≫ G.map f) := by
      funext f
      simp only [Function.comp_apply, comparison_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
    exact ((Ext.mk₀_bijective A Y).of_comp_iff _).mp
      (he ▸ (Ext.mk₀_bijective _ _).comp (h Y))
  | succ n ih =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have : Injective (S.map G).X₂ := G.injective_obj_of_injective I.injective
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    apply AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (comparison G i S.X₂ n) (comparison G i S.X₃ n) (comparison G i S.X₁ (n+1))
      _ _ ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' A hS n (n+1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' B (hS.map G) n (n+1) rfl))
      (ih _).surjective (ih _) (fun x => Ext.covariant_sequence_exact₁ _ hS x (by subsingleton) rfl)
      (fun x => Ext.covariant_sequence_exact₁ _ (hS.map G) x (by subsingleton) rfl)
    · ext x
      symm
      change (Ext.mk₀ i).comp ((x.comp (Ext.mk₀ S.g) (add_zero n)).mapExactFunctor G) (zero_add n) =
        ((Ext.mk₀ i).comp (x.mapExactFunctor G) (zero_add n)).comp (Ext.mk₀ (G.map S.g)) (add_zero n)
      rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero]
    · ext x
      symm
      change comparison G i _ _ (x.comp hS.extClass rfl) =
        (comparison G i _ _ x).comp (hS.map G).extClass rfl
      rw [comparison_comp, Ext.mapExactFunctor_extClass]
end Ext

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

private def sourceMap : freeOpen (⊤ : Opens Y) ⟶ (push f).obj (freeOpen (⊤ : Opens X)) :=
  (freeOpenSections _ ⊤).symm (freeOpenSections (freeOpen (⊤ : Opens X)) ⊤ (𝟙 _))

private theorem sourceMap_sectionHom (F : AbSheaf X) (s : Sections F ⊤) :
    sourceMap f ≫ (push f).map ((freeOpenSections F ⊤).symm s) =
      (freeOpenSections ((push f).obj F) ⊤).symm s := by
  apply (freeOpenSections ((push f).obj F) ⊤).injective
  rw [AddEquiv.apply_symm_apply, ← freeOpenSections_postcomp, sourceMap, AddEquiv.apply_symm_apply]
  change app ((freeOpenSections F ⊤).symm s) ⊤
    (freeOpenSections (freeOpen (⊤ : Opens X)) ⊤ (𝟙 _)) = s
  rw [freeOpenSections_postcomp, Category.id_comp, AddEquiv.apply_symm_apply]

private theorem sourceMap_bijective (F : AbSheaf X) :
    Function.Bijective (fun k : freeOpen (⊤ : Opens X) ⟶ F => sourceMap f ≫ (push f).map k) := by
  let e := (freeOpenSections F ⊤).toEquiv.trans (freeOpenSections ((push f).obj F) ⊤).symm.toEquiv
  suffices h : (fun k : freeOpen (⊤ : Opens X) ⟶ F => sourceMap f ≫ (push f).map k) = e by
    rw [h]
    exact e.bijective
  funext k
  exact (congrArg (fun z => sourceMap f ≫ (push f).map z)
    ((freeOpenSections F ⊤).symm_apply_apply k)).symm.trans
    (sourceMap_sectionHom f F (freeOpenSections F ⊤ k))

local instance (T : TopCat.{0}) : HasExt.{1} (AbSheaf T) := HasExt.standard _
local instance (T : TopCat.{0}) : HasExt.{1} (T.Sheaf AddCommGrpCat.{0}) := HasExt.standard _

variable (hf : IsClosedEmbedding f)
include hf

/-- Direct image along a closed embedding identifies cohomology of every additive
sheaf with its cohomology on the closed subspace. -/
def pushHEquiv (F : AbSheaf X) (n : ℕ) : F.H' n ⊤ ≃+ ((push f).obj F).H' n ⊤ := by
  let := push_preservesFiniteColimits f hf
  let := push_preservesInjectiveObjects f
  exact AddEquiv.ofBijective (comparison (push f) (sourceMap f) F n)
    (comparison_bijective (push f) (sourceMap f) (sourceMap_bijective f) F n)

theorem pushShortExact {S : ShortComplex (X.Sheaf AddCommGrpCat.{0})} (hS : S.ShortExact) :
    (S.map (push f)).ShortExact := by
  let := push_preservesFiniteColimits f hf
  exact hS.map_of_exact (push f)

theorem pushHEquiv_connecting {S : ShortComplex (X.Sheaf AddCommGrpCat.{0})} (hS : S.ShortExact)
    (n : ℕ) (x : S.X₃.H' n ⊤) :
    pushHEquiv f hf S.X₁ (n+1) (x.comp hS.extClass rfl) =
      (pushHEquiv f hf S.X₃ n x).comp
        (pushShortExact f hf hS).extClass rfl := by
  let := push_preservesFiniteColimits f hf
  let := push_preservesInjectiveObjects f
  exact (comparison_comp (push f) (sourceMap f) x hS.extClass).trans
    (congrArg (fun k => (pushHEquiv f hf S.X₃ n x).comp k rfl) (Ext.mapExactFunctor_extClass _ _))

end CycleQ2ClosedEmbeddingCohomology
end

#print axioms CycleQ2ClosedEmbeddingCohomology.pushHEquiv
#print axioms CycleQ2ClosedEmbeddingCohomology.pushHEquiv_connecting
