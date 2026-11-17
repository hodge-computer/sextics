import Mathlib.Algebra.FiveLemma
import Proposal.GeometricOpenRestrictionInjective

/-!
# Derived cohomology on an affine chart

Restriction identifies the ambient cohomology evaluated on an open with
ordinary cohomology of the sheaf on that open. On an affine chart with a
frame, vanishing of ordinary structure-sheaf cohomology therefore transfers
to the ambient group in the same degree.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricSheafCohomologyRestriction

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

section ExactFunctor
universe u u' v v' w w'
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasExt.{w} C] [HasExt.{w'} D] [EnoughInjectives C]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [G.PreservesInjectiveObjects]

attribute [local simp] Ext.mapExactFunctor_comp Ext.mapExactFunctor_mk₀ Ext.mapExactFunctor_extClass
attribute [local instance] Ext.subsingleton_of_injective

/-- The fixed-source form of the exact functor comparison for Ext. Only the
maps out of `X` enter the covariant long exact sequence. The dimension-shifting
argument is adapted from Nailin Guan’s `Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective`
(Apache 2.0, copyright 2025 Nailin Guan). -/
theorem mapExt_bijective_of_fixedSource (X : C)
    (hX : ∀ Y : C, Function.Bijective (fun f : X ⟶ Y => G.map f)) (Y : C) (n : ℕ) :
    Function.Bijective (G.mapExtAddHom X Y n) := by
  induction n generalizing Y with
  | zero =>
    simpa [Ext.mapExactFunctor₀] using hX Y
  | succ n ih =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have : Injective (S.map G).X₂ := G.injective_obj_of_injective I.injective
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (G.mapExtAddHom X S.X₂ n) (G.mapExtAddHom X S.X₃ n) (G.mapExtAddHom X S.X₁ (n + 1))
      (by cat_disch) (by cat_disch)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' X hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' (G.obj X) (hS.map G) n (n + 1) rfl))
      (ih _).surjective (ih _)
      (fun x ↦ Ext.covariant_sequence_exact₁ _ hS x (by subsingleton) rfl)
      (fun x ↦ Ext.covariant_sequence_exact₁ _ (hS.map G) x (by subsingleton) rfl)

end ExactFunctor

section Restriction
variable {C : Type} [Category.{0} C] [Quiver.IsThin C]
  (J : GrothendieckTopology C) (U : C)

attribute [local instance] overPullback_preservesInjectiveObjects

local instance : (restrictionFunctor J U).IsLeftAdjoint :=
  ((Over.forget U).sheafAdjunctionCocontinuous AddCommGrpCat (J.over U) J).isLeftAdjoint
local instance : (restrictionFunctor J U).IsRightAdjoint :=
  ((Over.forget U).sheafAdjunctionContinuous AddCommGrpCat (J.over U) J).isRightAdjoint
local instance : (restrictionFunctor J U).Additive where
local instance : HasExt.{1} (Sheaf J AddCommGrpCat.{0}) := HasExt.standard _

/-- Evaluation on an open agrees in every degree with ordinary cohomology
of the restricted sheaf on its over-site. -/
def restrictionHEquiv
    (F : Sheaf J AddCommGrpCat.{0}) (n : ℕ) : F.H' n U ≃+ (F.over U).H n :=
  (AddEquiv.ofBijective ((restrictionFunctor J U).mapExtAddHom (freeAbelianSheaf J U) F n)
    (mapExt_bijective_of_fixedSource (restrictionFunctor J U) (freeAbelianSheaf J U)
      (restriction_hom_bijective J U) F n)).trans
    ((((extFunctor n).mapIso (restrictionSourceIso J U).op).app
      (F.over U)).addCommGroupIsoToAddEquiv.symm)

end Restriction

section Chart
variable {C D : Type} [Category.{0} C] [Category.{0} D] [Quiver.IsThin C]
  (J : GrothendieckTopology C) (U : C) (K : GrothendieckTopology D)
  (e : Over U ≌ D)
  [e.functor.IsContinuous (J.over U) K] [e.inverse.IsContinuous K (J.over U)]
local instance : HasExt.{1} (Sheaf J AddCommGrpCat.{0}) := HasExt.standard _
local instance : HasExt.{1} (Sheaf K AddCommGrpCat.{0}) := HasExt.standard _
local instance : HasExt.{1} (Sheaf (J.over U) AddCommGrpCat.{0}) := HasExt.standard _
local instance : (continuousSheafEquiv (J.over U) K e).functor.Additive where

/-- Ambient sheaf cohomology on a chart, transported to an equivalent site
and a specified isomorphic coefficient sheaf. -/
def chartCohomologyEquiv
    (T : D) (hT : IsTerminal T) (F : Sheaf J AddCommGrpCat.{0})
    (G : Sheaf K AddCommGrpCat.{0})
    (i : F.over U ≅
      (e.functor.sheafPushforwardContinuous AddCommGrpCat (J.over U) K).obj G)
    (n : ℕ) : F.H' n U ≃+ G.H n := by
  let E := continuousSheafEquiv (J.over U) K e
  let j : E.functor.obj (F.over U) ≅ G := E.functor.mapIso i ≪≫ E.counitIso.app G
  refine (restrictionHEquiv J U F n).trans ?_
  refine (AddEquiv.ofBijective (E.functor.mapExtAddHom _ (F.over U) n)
    (mapExt_bijective_of_fixedSource E.functor _
      (fun _ => ⟨E.functor.map_injective, E.functor.map_surjective⟩) (F.over U) n)).trans ?_
  refine ((((extFunctor n).mapIso (constantSourceIso (J.over U) K e T hT).op).app
    (E.functor.obj (F.over U))).addCommGroupIsoToAddEquiv.symm).trans ?_
  exact ((Sheaf.functorH K n).mapIso j).addCommGroupIsoToAddEquiv

end Chart
end CycleQ2GeometricSheafCohomologyRestriction

namespace CycleQ2GeometricProjectiveHOne

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricAffineChartSections CycleQ2GeometricSheafCohomologyRestriction
open CycleQ2GeometricAffineCohomology

local instance (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) :=
  HasExt.standard _

local instance (A : Type) [CommRing A] : HasExt.{1} (AbSheaf A) := HasExt.standard _

/-- A frame on an affine chart transports ordinary affine second cohomology
vanishing to the degree-two cohomology of the ambient sheaf on that open. -/
theorem affineFrameHTwo_subsingleton {X : Scheme.{0}} {U : X.Opens}
    {A : Type} [CommRing A] (e : U.toScheme ≅ Spec (CommRingCat.of A))
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})
    (frame : F.over U ≅ (structureAdditiveSheaf X).over U)
    (hA : Subsingleton ((additiveStructureSheaf A).H 2)) :
    Subsingleton (F.H' 2 U) := by
  let : Subsingleton ((structureAdditiveSheaf (Spec (CommRingCat.of A))).H 2) := hA
  exact Function.Injective.subsingleton
    (chartCohomologyEquiv (Opens.grothendieckTopology X) U
      (Opens.grothendieckTopology (Spec (CommRingCat.of A))) (chartOpensEquiv e)
      ⊤ isTerminalTop F (structureAdditiveSheaf (Spec (CommRingCat.of A)))
      (frame ≪≫ chartStructureOverIso e) 2).injective

#print axioms CycleQ2GeometricSheafCohomologyRestriction.chartCohomologyEquiv
#print axioms affineFrameHTwo_subsingleton
end CycleQ2GeometricProjectiveHOne
end
