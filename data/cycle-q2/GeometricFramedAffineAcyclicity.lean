import Proposal.GeometricAffineCohomology
import Proposal.GeometricCartierDerivedClass
import Proposal.GeometricAffineHigherChartRestriction
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import Mathlib.Topology.Sheaves.MayerVietoris
import Proposal.GeometricMonicGenericSupport
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

/-! Acyclicity of affine sections of the finite-rank differential-form sheaves.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false

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
private theorem frame_subsingleton {X : Scheme.{0}} {U : X.Opens} {B : Type} [CommRing B]
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

section
namespace CycleQ2AffinePowerSheaf
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open CycleQ2GeometricProjectiveHOne (structureAdditiveSheaf)
open CycleQ2GeometricSheafCohomologyRestriction (freeAbelianSheaf chartCohomologyEquiv restrictionHEquiv)

variable (X : Scheme.{0}) (I : Type)

private abbrev O := structureAdditiveSheaf X

private def powerPre : TopCat.Presheaf AddCommGrpCat.{0} X where
  obj U := AddCommGrpCat.of (I → Γ(X,U.unop))
  map f := AddCommGrpCat.ofHom
    { toFun := fun x i => X.presheaf.map f (x i)
      map_zero' := by funext i; exact map_zero _
      map_add' := by intro x y; funext i; exact map_add _ _ _ }
  map_id U := by
    apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext; intro x; funext i
    exact ConcreteCategory.congr_hom (X.presheaf.map_id U) (x i)
  map_comp f g := by
    apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext; intro x; funext i
    exact ConcreteCategory.congr_hom (X.presheaf.map_comp f g) (x i)

def power : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0} := by
  refine ⟨powerPre X I, ?_⟩
  apply (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget AddCommGrpCat)).mpr
  apply (isSheaf_iff_isSheaf_of_type _ _).mpr
  intro U S hS
  apply CycleQ2SheafForLocalCoordinates.isSheafFor
    (Q := X.presheaf ⋙ forget CommRingCat)
    (fun {_} _ => Equiv.refl _) (fun _ _ _ _ => rfl)
  exact (Presheaf.isSheaf_comp_of_isSheaf _ X.presheaf (forget CommRingCat) X.sheaf.property).isSheafFor S hS

private def proj (i : I) : power X I ⟶ O X where
  hom := { app := fun _ => AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ i)
           naturality := fun _ _ _ => rfl }

private def incl [DecidableEq I] (i : I) : O X ⟶ power X I where
  hom := { app := fun U => AddCommGrpCat.ofHom (AddMonoidHom.single (fun _ : I => Γ(X,U.unop)) i)
           naturality := by
             intro U V f
             apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext; intro x; funext j
             let a : Γ(X,U.unop) := x
             let φ : Γ(X,U.unop) →+* Γ(X,V.unop) := (X.presheaf.map f).hom
             change Pi.single (M := fun _ : I => Γ(X,V.unop)) i (φ a) j =
               φ (Pi.single (M := fun _ : I => Γ(X,U.unop)) i a j)
             by_cases h : j = i
             · subst j; simp only [Pi.single_eq_same]
             · simp only [Pi.single_eq_of_ne h, map_zero] }

private theorem decomposition [Fintype I] [DecidableEq I] :
    ∑ i, proj X I i ≫ incl X I i = 𝟙 (power X I) := by
  apply (sheafToPresheaf _ _).map_injective
  rw [Functor.map_sum]
  apply NatTrans.ext; funext U
  rw [NatTrans.app_sum]
  apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext; intro x; funext j
  have hs (s : Finset I) :
      ((∑ i ∈ s, (proj X I i ≫ incl X I i).hom.app U) x) j =
        ∑ i ∈ s, Pi.single (M := fun _ : I => Γ(X,U.unop)) i (x i) j := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; rfl
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, AddCommGrpCat.hom_add_apply]
      change Pi.single (M := fun _ : I => Γ(X,U.unop)) i (x i) j +
        ((∑ k ∈ s, (proj X I k ≫ incl X I k).hom.app U) x) j = _
      rw [ih]
  exact (hs Finset.univ).trans (Fintype.sum_pi_single (M := fun _ : I => Γ(X,U.unop)) j (fun i => x i))

variable {X}
attribute [local instance] HasExt.standard

private theorem O_vanish {W : X.Opens} (hW : IsAffineOpen W) (k : ℕ) :
    Subsingleton ((O X).H' (k+1) W) := by
  let : Subsingleton ((structureAdditiveSheaf (Spec (CommRingCat.of Γ(X,W)))).H (k+1)) :=
    CycleQ2GeometricAffineHThree.affine_H_positive_subsingleton k Γ(X,W)
  exact (chartCohomologyEquiv (Opens.grothendieckTopology X) W
    (Opens.grothendieckTopology (Spec (CommRingCat.of Γ(X,W))))
    (CycleQ2GeometricAffineChartSections.chartOpensEquiv hW.isoSpec) ⊤ isTerminalTop
    (O X) (structureAdditiveSheaf (Spec (CommRingCat.of Γ(X,W))))
    (CycleQ2GeometricProjectiveHOne.chartStructureOverIso hW.isoSpec) (k+1)).injective.subsingleton

theorem power_vanishing [Fintype I] {W : X.Opens} (hW : IsAffineOpen W) (k : ℕ) :
    Subsingleton ((power X I).H' (k+1) W) := by
  classical
  let H := extFunctorObj (freeAbelianSheaf (Opens.grothendieckTopology X) W) (k+1)
  have hO : IsZero (H.obj (O X)) :=
    AddCommGrpCat.isZero_iff_subsingleton.mpr (O_vanish hW k)
  have h : IsZero (H.obj (power X I)) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    rw [← H.map_id, ← decomposition X I, H.map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [H.map_comp, hO.eq_of_tgt (H.map (proj X I i)) 0, zero_comp]
  exact AddCommGrpCat.isZero_iff_subsingleton.mp h

theorem affine_vanishing [Fintype I] {W : X.Opens} (hW : IsAffineOpen W)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) (e : F.over W ≅ (power X I).over W) (k : ℕ) :
    Subsingleton (F.H' (k+1) W) := by
  let J := Opens.grothendieckTopology X
  let eqv := ((restrictionHEquiv J W F (k+1)).trans
    (((Sheaf.functorH (J.over W) (k+1)).mapIso e).addCommGroupIsoToAddEquiv)).trans
    (restrictionHEquiv J W (power X I) (k+1)).symm
  let := power_vanishing I hW k
  exact eqv.injective.subsingleton

end CycleQ2AffinePowerSheaf
end

namespace CycleQ2FramedOverDescent

open CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]
  (F : C ⥤ D) [F.Full] (J : GrothendieckTopology D) [F.IsCoverDense J] (W : C)

theorem coverDense : (Over.post (X := W) F).IsCoverDense (J.over (F.obj W)) where
  is_cover U := by
    rw [GrothendieckTopology.mem_over_iff]
    apply J.superset_covering _ (F.is_cover_of_isCoverDense J U.left)
    rintro T a ⟨⟨b,l,m,h⟩⟩
    rw [Sieve.overEquiv_iff]
    let q : b ⟶ W := F.preimage (m ≫ U.hom)
    have hq : F.map q = m ≫ U.hom := F.map_preimage _
    let B := Over.mk q
    let t : (Over.post F).obj B ⟶ U := Over.homMk m hq.symm
    let s : Over.mk (a ≫ U.hom) ⟶ (Over.post F).obj B :=
      Over.homMk l (by change l ≫ F.map q = a ≫ U.hom; rw [hq, ← Category.assoc, h])
    exact ⟨⟨B, s, t, Over.OverMorphism.ext h⟩⟩

variable [F.Faithful]
variable {A : Type*} [Category* A]
  {M N : Sheaf (J.over (F.obj W)) A}

/-- A sheaf isomorphism over a basis object determined by basis coordinates and restrictions. -/
def sheafIso (e : (Over.post (X := W) F).op ⋙ M.obj ≅ (Over.post (X := W) F).op ⋙ N.obj) :
    M ≅ N := by
  letI := coverDense F J W
  exact Functor.IsCoverDense.sheafIso e

end CycleQ2FramedOverDescent

section
namespace CycleQ2FramedOpenFormCoefficients
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry TopologicalSpace Opposite Module
open CycleQ2SmoothRelativeFrames CycleQ2IntrinsicFramedAffineSite
open CycleQ2IntrinsicDeRhamSheaves CycleQ2IntrinsicFramedAffineCoordinates
open CycleQ2RelativeAffineOverlap CycleQ2ExactFrameThreeDeRham
open CycleQ2WeightedCoordinateExterior
variable {k : Type} [Field k] [CharZero k] {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) (r : ℕ) [SmoothOfRelativeDimension r p]
  (W : FramedOpen p r) (q : ℕ)

abbrev index := Set.powersetCard (Fin r) q

abbrev overBasis := Over.post (X := W) (inclusion p r)

abbrev basisFormsAt : (Over W)ᵒᵖ ⥤ AddCommGrpCat.{0} :=
  (Over.forget W).op ⋙ forms p r q

abbrev powerOnBasis : (Over W)ᵒᵖ ⥤ AddCommGrpCat.{0} :=
  (overBasis p r W).op ⋙ ((CycleQ2AffinePowerSheaf.power X (index r q)).over W.1).obj

def basisCoefficients : basisFormsAt p r W q ≅ powerOnBasis p r W q := by
  refine NatIso.ofComponents (fun V => ?_) ?_
  · letI : Algebra k Γ(X,V.unop.left.1) := (sectionCoefficients p V.unop.left.1).toAlgebra
    exact AddEquiv.toAddCommGrpIso ((transported p r V.unop.hom).exteriorPower q).equivFun.toAddEquiv
  · intro V T a
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    funext i
    let : Algebra k Γ(X,V.unop.left.1) := (sectionCoefficients p V.unop.left.1).toAlgebra
    let : Algebra k Γ(X,T.unop.left.1) := (sectionCoefficients p T.unop.left.1).toAlgebra
    exact exteriorCoordinates_natural p r V.unop.hom a.unop.left q s i

/-- On a framed affine open the intrinsic exterior sheaf is a finite power of the
 structure sheaf. The coordinates here use restrictions of the frame on `W`. -/
def overIso : (sheafForms p r q).over W.1 ≅
    (CycleQ2AffinePowerSheaf.power X (index r q)).over W.1 := by
  letI : (inclusion p r).IsCoverDense (Opens.grothendieckTopology X) := cover_dense p r
  apply CycleQ2FramedOverDescent.sheafIso (inclusion p r) _ W
  exact Functor.isoWhiskerLeft (Over.forget W).op (onBasisIso p r q) ≪≫ basisCoefficients p r W q

attribute [local instance] HasExt.standard

theorem forms_acyclic (n : ℕ) : Subsingleton ((sheafForms p r q).H' (n+1) W.1) :=
  CycleQ2AffinePowerSheaf.affine_vanishing (index r q) W.2.1 (sheafForms p r q) (overIso p r W q) n

/-- All actual de Rham terms are acyclic for sections on the framed open. -/
theorem term_acyclic (m : ℤ) (n : ℕ) :
    Subsingleton (Ext.{1} (CycleQ2InjectiveCech.freeOpen W.1) ((relativeDeRhamInt p r).X m) (n+1)) := by
  let E := extFunctorObj (CycleQ2InjectiveCech.freeOpen W.1) (n+1)
  cases m with
  | ofNat q =>
    let e : (relativeDeRhamInt p r).X (q : ℤ) ≅ sheafForms p r q :=
      (relativeDeRham p r).extendXIso (ComplexShape.embeddingUpIntGE 0) (Int.zero_add _)
    let : Subsingleton (E.obj (sheafForms p r q)) := forms_acyclic p r W q n
    exact (E.mapIso e).addCommGroupIsoToAddEquiv.injective.subsingleton
  | negSucc q =>
    have hz : IsZero ((relativeDeRhamInt p r).X (Int.negSucc q)) :=
      (relativeDeRham p r).isZero_extend_X (ComplexShape.embeddingUpIntGE 0) _
        (by intro a ha; change (0:ℤ) + a = Int.negSucc q at ha; omega)
    exact AddCommGrpCat.isZero_iff_subsingleton.mp (E.map_isZero hz)

end CycleQ2FramedOpenFormCoefficients
end
