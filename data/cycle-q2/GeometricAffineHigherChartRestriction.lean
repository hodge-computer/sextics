import Mathlib.Algebra.FiveLemma
import Proposal.GeometricOpenRestrictionInjective
import Proposal.GeometricCartierDerivedClass
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import Mathlib.Topology.Sheaves.MayerVietoris

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

/-! Positive affine structure-sheaf cohomology is independent of the later
framed differential-form construction. -/

noncomputable section

section
namespace CycleQ2AffineCohomologyLocalVanishing

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry Opposite TopologicalSpace
open CycleQ2InjectiveCech CycleQ2CechTwoToDerived

local notation "AffSheaf" => CycleQ2GeometricAffineCohomology.AbSheaf

local instance (A : Type) [CommRing A] : HasExt.{1} (AffSheaf A) :=
  HasExt.standard _

private theorem restrict_boundary {A : Type} [CommRing A] {S : ShortComplex (AffSheaf A)}
    (hS : S.ShortExact) {U V : Opens (PrimeSpectrum.Top A)} (h : U ≤ V)
    (n : ℕ) (y : S.X₃.H' n V) :
    (S.X₁.cohomologyPresheaf (n+1)).map (homOfLE h).op (Ext.comp y hS.extClass rfl) =
      Ext.comp ((S.X₃.cohomologyPresheaf n).map (homOfLE h).op y) hS.extClass rfl := by
  change (Ext.mk₀ (freeOpenMap h)).comp (Ext.comp y hS.extClass rfl) (zero_add _) =
    ((Ext.mk₀ (freeOpenMap h)).comp y (zero_add _)).comp hS.extClass rfl
  exact (Ext.comp_assoc _ _ _ (zero_add n) rfl (zero_add (n + 1))).symm

private theorem exists_boundary (A : Type) [CommRing A] (F : AffSheaf A)
    (n : ℕ) (x : F.H' (n+1) ⊤) :
    ∃ y : (presentation F).X₃.H' n ⊤,
      Ext.comp y (presentation_shortExact F).extClass rfl = x :=
  Ext.covariant_sequence_exact₁ (freeOpen (X := PrimeSpectrum.Top A) ⊤) (presentation_shortExact F) x
    (Ext.eq_zero_of_injective _) (n₀ := n) rfl

private theorem locally_zero_one (A : Type) [CommRing A] (F : AffSheaf A) (x : F.H' 1 ⊤) :
    ∃ s : Finset A, Ideal.span (s : Set A) = ⊤ ∧
      ∀ a ∈ s, (F.cohomologyPresheaf 1).map (homOfLE
        (show PrimeSpectrum.basicOpen a ≤ ⊤ from le_top)).op x = 0 := by
  classical
  let S := presentation F
  have hS := presentation_shortExact F
  obtain ⟨y, rfl⟩ := exists_boundary A F 0 x
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
  let : Sheaf.IsLocallySurjective S.g :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat S.g).mpr hS.epi_g
  obtain ⟨s, u, hs, hu⟩ := CycleQ2GeometricAffineCohomology.finite_local_lifts S.g
    (freeOpenSections S.X₃ ⊤ f)
  refine ⟨s, hs, ?_⟩
  intro a ha
  let U := PrimeSpectrum.basicOpen a
  let g := (freeOpenSections S.X₂ U).symm (u ⟨a, ha⟩)
  have hf : freeOpenMap (show U ≤ ⊤ from le_top) ≫ f = g ≫ S.g := by
    apply (freeOpenSections S.X₃ U).injective
    erw [freeOpenSections_naturality, ← freeOpenSections_postcomp]
    dsimp only [g]
    erw [AddEquiv.apply_symm_apply]
    exact (hu ⟨a, ha⟩).symm
  erw [restrict_boundary (A := A) hS (U := U) le_top 0 (Ext.mk₀ f)]
  change ((Ext.mk₀ (freeOpenMap (show U ≤ ⊤ from le_top))).comp
    (Ext.mk₀ f) (zero_add 0)).comp hS.extClass rfl = 0
  rw [Ext.mk₀_comp_mk₀ (freeOpenMap (show U ≤ ⊤ from le_top)) f, hf]
  rw [← Ext.mk₀_comp_mk₀_assoc g S.g hS.extClass]
  rw [hS.comp_extClass, Ext.comp_zero]

/-- Every positive-degree derived cohomology class on an affine spectrum
vanishes after restriction to a finite family of distinguished opens which cover it. -/
theorem locally_zero (A : Type) [CommRing A] (F : AffSheaf A)
    (n : ℕ) (x : F.H' (n+1) ⊤) :
    ∃ s : Finset A, Ideal.span (s : Set A) = ⊤ ∧
      ∀ a ∈ s, (F.cohomologyPresheaf (n+1)).map (homOfLE
        (show PrimeSpectrum.basicOpen a ≤ ⊤ from le_top)).op x = 0 := by
  classical
  induction n generalizing F with
  | zero => exact locally_zero_one A F x
  | succ n ih =>
    obtain ⟨y, rfl⟩ := exists_boundary A F (n+1) x
    obtain ⟨s, hs, hu⟩ := ih (presentation F).X₃ y
    refine ⟨s, hs, ?_⟩
    intro a ha
    erw [restrict_boundary (A := A) (presentation_shortExact F)
      (U := PrimeSpectrum.basicOpen a) le_top (n+1) y,
      hu a ha, Ext.zero_comp]
    rfl

end CycleQ2AffineCohomologyLocalVanishing
end

section
namespace CycleQ2GeometricAffineHThree

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
  Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricAffineCohomology CycleQ2GeometricProjectiveHOne
  CycleQ2GeometricSheafCohomologyRestriction

section Empty
variable {X : TopCat.{0}} (F : X.Sheaf AddCommGrpCat.{0})
  [HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})]

/-- Cohomology on the empty open is zero in every degree. -/
private theorem empty_subsingleton (n : ℕ) : Subsingleton (F.H' n ⊥) := by
  let J := Opens.grothendieckTopology X
  let Q := freeAbelianSheaf J ⊥
  have hQ : Subsingleton (Q.obj.obj (op ⊥)) :=
    AddCommGrpCat.subsingleton_of_isZero (TopCat.Sheaf.isTerminalOfEmpty Q).isZero
  have h : 𝟙 Q = 0 := (freeSheafSections J ⊥ Q).injective (hQ.elim _ _)
  apply subsingleton_of_forall_eq 0
  intro x
  have he : x = (Ext.mk₀ (𝟙 Q)).comp x (zero_add n) := (Ext.mk₀_id_comp x).symm
  erw [h, Ext.mk₀_zero, Ext.zero_comp] at he
  exact he
end Empty

variable (A : Type) [CommRing A]
local instance : HasExt.{1} (AbSheaf A) := HasExt.standard _

private abbrev H (n : ℕ) (U : Opens (PrimeSpectrum A)) := (additiveStructureSheaf A).H' n U

section Frame
local instance (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

/-- A trivialization on an affine chart transports affine vanishing in the same degree. -/
theorem frame_subsingleton {X : Scheme.{0}} {U : X.Opens} {B : Type} [CommRing B]
    (e : U.toScheme ≅ Spec (CommRingCat.of B)) (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})
    (frame : F.over U ≅ (structureAdditiveSheaf X).over U) (n : ℕ)
    (hB : Subsingleton ((additiveStructureSheaf B).H n)) : Subsingleton (F.H' n U) := by
  let : Subsingleton ((structureAdditiveSheaf (Spec (CommRingCat.of B))).H n) := hB
  exact Function.Injective.subsingleton
    (chartCohomologyEquiv (Opens.grothendieckTopology X) U
      (Opens.grothendieckTopology (Spec (CommRingCat.of B))) (CycleQ2GeometricAffineChartSections.chartOpensEquiv e)
      ⊤ isTerminalTop F (structureAdditiveSheaf (Spec (CommRingCat.of B)))
      (frame ≪≫ chartStructureOverIso e) n).injective

end Frame

variable (n : ℕ)

/-- Restriction of a global positive-degree class to an ambient open. -/
private abbrev toOpen (U : Opens (PrimeSpectrum A)) :
    H A (n + 1) ⊤ ⟶ H A (n + 1) U :=
  ((additiveStructureSheaf A).cohomologyPresheaf (n + 1)).map (homOfLE le_top).op

private lemma restrict_toOpen {U V : Opens (PrimeSpectrum A)} (i : U ⟶ V) (x : H A (n + 1) ⊤) :
    ((additiveStructureSheaf A).cohomologyPresheaf (n + 1)).map i.op (toOpen A n V x) = toOpen A n U x := by
  erw [← ConcreteCategory.comp_apply, toOpen, ← Functor.map_comp]
  rfl

private lemma downward {U V : Opens (PrimeSpectrum A)} (h : U ≤ V) (x : H A (n + 1) ⊤)
    (hv : toOpen A n V x = 0) : toOpen A n U x = 0 := by
  erw [← restrict_toOpen A n (homOfLE h), hv, map_zero]
  rfl

private lemma sup_vanish
    (prev : ∀ (B : Type) [CommRing B], Subsingleton ((additiveStructureSheaf B).H n))
    (f g : A) (x : H A (n + 1) ⊤)
    (hf : toOpen A n (PrimeSpectrum.basicOpen f) x = 0)
    (hg : toOpen A n (PrimeSpectrum.basicOpen g) x = 0) :
    toOpen A n (PrimeSpectrum.basicOpen f ⊔ PrimeSpectrum.basicOpen g) x = 0 := by
  let D := @PrimeSpectrum.basicOpen A _
  let S := Opens.mayerVietorisSquare (T := PrimeSpectrum.Top A) (D f) (D g)
  let F := additiveStructureSheaf A
  let z := toOpen A n S.X₄ x
  have hpair : S.toBiprod F (n + 1) z = 0 := by
    rw [S.toBiprod_apply]
    have h : ((F.cohomologyPresheaf (n + 1)).map S.f₂₄.op z,
        (F.cohomologyPresheaf (n + 1)).map S.f₃₄.op z) = (0,0) :=
      Prod.ext ((restrict_toOpen A n _ _).trans hf) ((restrict_toOpen A n _ _).trans hg)
    rw [h]
    exact map_zero _
  obtain ⟨b, hb⟩ := (ShortComplex.ab_exact_iff _).mp ((S.sequence_exact F n (n + 1) rfl).exact 2) z hpair
  have hprev : Subsingleton (F.H' n S.X₁) := by
    change Subsingleton (F.H' n (PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen g))
    erw [← PrimeSpectrum.basicOpen_mul]
    let X := Spec (CommRingCat.of A)
    let U : X.Opens := PrimeSpectrum.basicOpen (f * g)
    let R : CommRingCat := Γ(X, U)
    have e : U.toScheme ≅ Spec R := (IsAffineOpen.Spec_basicOpen
      (R := CommRingCat.of A) (f * g)).isoSpec
    exact frame_subsingleton (B := R) e F (Iso.refl _) n (prev R)
  have hb0 : b = 0 := hprev.elim _ _
  exact hb.symm.trans (by rw [hb0, map_zero]; rfl)

private def vanishingIdeal
    (prev : ∀ (B : Type) [CommRing B], Subsingleton ((additiveStructureSheaf B).H n))
    (x : H A (n + 1) ⊤) : Ideal A where
  carrier := {f | toOpen A n (PrimeSpectrum.basicOpen f) x = 0}
  zero_mem' := by
    have h := empty_subsingleton (additiveStructureSheaf A) (n + 1)
    rw [Set.mem_ofPred_eq, PrimeSpectrum.basicOpen_zero]
    exact h.elim _ _
  add_mem' := by
    intro f g hf hg
    refine downward A n (V := PrimeSpectrum.basicOpen f ⊔ PrimeSpectrum.basicOpen g) ?_ x
      (sup_vanish A n prev f g x hf hg)
    intro p hp
    by_contra h
    change ¬ (f ∉ p.asIdeal ∨ g ∉ p.asIdeal) at h
    push Not at h
    exact hp (p.asIdeal.add_mem h.1 h.2)
  smul_mem' := fun a f hf => downward A n (PrimeSpectrum.basicOpen_mul_le_right a f) x hf

private theorem next_affine_subsingleton
    (prev : ∀ (B : Type) [CommRing B], Subsingleton ((additiveStructureSheaf B).H n))
    (localZero : ∀ x : H A (n + 1) ⊤, ∃ s : Finset A, Ideal.span (s : Set A) = ⊤ ∧
      ∀ a ∈ s, toOpen A n (PrimeSpectrum.basicOpen a) x = 0) :
    Subsingleton ((additiveStructureSheaf A).H (n + 1)) := by
  let F := additiveStructureSheaf A
  have htop : Subsingleton (F.H' (n + 1) ⊤) := by
    apply subsingleton_of_forall_eq 0
    intro x
    obtain ⟨s, hspan, hvan⟩ := localZero x
    let I := vanishingIdeal A n prev x
    have hi : I = ⊤ := by
      apply top_unique
      rw [← hspan]
      exact Ideal.span_le.mpr (fun _ ha => hvan _ ha)
    have h1 : 1 ∈ I := hi ▸ Submodule.mem_top
    have hz : toOpen A n (PrimeSpectrum.basicOpen (1 : A)) x = 0 := h1
    erw [PrimeSpectrum.basicOpen_one] at hz
    change ((F.cohomologyPresheaf (n + 1)).map
      (𝟙 (op (⊤ : Opens (PrimeSpectrum.Top A))))) x = 0 at hz
    let G := F.cohomologyPresheaf (n + 1)
    have he := G.map_id (op (⊤ : Opens (PrimeSpectrum.Top A)))
    exact (ConcreteCategory.congr_hom he x).symm.trans hz
  exact Function.Injective.subsingleton
    (terminalCohomologyEquiv (Opens.grothendieckTopology (PrimeSpectrum.Top A)) F
      ⊤ isTerminalTop (n + 1)).symm.injective

/-- Every positive-degree cohomology group of an affine structure sheaf vanishes. -/
theorem affine_H_positive_subsingleton (k : ℕ) :
    ∀ (B : Type) [CommRing B], Subsingleton ((additiveStructureSheaf B).H (k + 1)) := by
  induction k with
  | zero =>
    intro B _
    exact affine_H_one_subsingleton B
  | succ k ih =>
    intro B _
    exact next_affine_subsingleton B (k + 1) ih
      (CycleQ2AffineCohomologyLocalVanishing.locally_zero B (additiveStructureSheaf B) (k + 1))

end CycleQ2GeometricAffineHThree
end

end

#print axioms CycleQ2GeometricAffineHThree.affine_H_positive_subsingleton
