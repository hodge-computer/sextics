import Proposal.GeometricMonicGenericSupport
import Proposal.GeometricSupportedCechRows
import Proposal.GeometricPrincipalPartsDifferentials
import Proposal.GeometricSupportedHypercohomology
import Proposal.GeometricFramedAffineAcyclicity
import Mathlib.RingTheory.Localization.Submodule

/-! Local vanishing below degree four for an adapted pair of equations. The intrinsic form sheaves and the two-open Čech calculation use the same affine restrictions.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false

noncomputable section

section
namespace CycleQ2FramedCechFormRow
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open CycleQ2IntrinsicFramedAffineSite (FramedOpen inclusion forms frame chartComplex)
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRham relativeDeRhamInt sheafForms differential onBasisIso onBasisIso_d)
open CycleQ2FiniteExactAffineAtlas (HasFrame hasFrame_of_affine_le)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2WeightedCoordinateExterior (Form)
open CycleQ2ExactFrameThreeDeRham (exteriorPullback)
open CycleQ2InjectiveCech (Sections freeOpen freeOpenSections freeOpenMap)
open CycleQ2LocalPrincipalGysin (cover union_le)
open CycleQ2SupportedCechExt (overlapBoundary)

variable {k : Type} [Field k] [CharZero k] {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) (r : ℕ) [SmoothOfRelativeDimension r p]

abbrev ordinary (B : FramedOpen p r) (q : ℕ) :=
  letI : Algebra k Γ(X,B.1) := (sectionCoefficients p B.1).toAlgebra
  Form k Γ(X,B.1) q

abbrev term (q : ℕ) := (relativeDeRhamInt p r).X (q : ℤ)

def pull {U V : FramedOpen p r} (h : V ⟶ U) (q : ℕ) :
    ordinary p r U q →+ ordinary p r V q :=
  letI : Algebra k Γ(X,U.1) := (sectionCoefficients p U.1).toAlgebra
  letI : Algebra k Γ(X,V.1) := (sectionCoefficients p V.1).toAlgebra
  (exteriorPullback (CycleQ2RelativeAffineOverlap.restrict p (show V.1 ≤ U.1 from h.le)) q).toAddMonoidHom

def deriv (B : FramedOpen p r) (q : ℕ) : ordinary p r B q →+ ordinary p r B (q+1) :=
  letI : Algebra k Γ(X,B.1) := (sectionCoefficients p B.1).toAlgebra
  (CycleQ2ArbitraryFrameDifferential.d (frame p r B) q).toAddMonoidHom

abbrev delta (q : ℕ) := (relativeDeRhamInt p r).d (q : ℤ) ((q+1 : ℕ) : ℤ)

private def termIso (q : ℕ) : term p r q ≅ sheafForms p r q :=
  (relativeDeRham p r).extendXIso (ComplexShape.embeddingUpIntGE 0) (Int.zero_add _)

private def presentation (q : ℕ) :
    (inclusion p r).op ⋙ (term p r q).obj ≅ forms p r q :=
  Functor.isoWhiskerLeft (inclusion p r).op
    ((sheafToPresheaf _ _).mapIso (termIso p r q)) ≪≫ onBasisIso p r q

def coordinates (B : FramedOpen p r) (q : ℕ) :
    Sections (term p r q) B.1 ≃+ ordinary p r B q :=
  ((presentation p r q).app (op B)).addCommGroupIsoToAddEquiv

theorem coordinates_restrict {U V : FramedOpen p r} (h : V ⟶ U) (q : ℕ)
    (s : Sections (term p r q) U.1) :
    coordinates p r V q ((term p r q).obj.map (homOfLE (show V.1 ≤ U.1 from h.le)).op s) =
      pull p r h q (coordinates p r U q s) :=
  NatTrans.naturality_apply (presentation p r q).hom h.op s

theorem coordinates_d (B : FramedOpen p r) (q : ℕ) (s : Sections (term p r q) B.1) :
    coordinates p r B (q+1) ((delta p r q).hom.app (op B.1) s) =
      deriv p r B q (coordinates p r B q s) := by
  let : Algebra k Γ(X,B.1) := (sectionCoefficients p B.1).toAlgebra
  have hn : (relativeDeRham p r).d q (q+1) = differential p r q := by
    simp only [relativeDeRham, CochainComplex.of_d]
  have hd : delta p r q =
      (termIso p r q).hom ≫ differential p r q ≫ (termIso p r (q+1)).inv :=
    ((relativeDeRham p r).extend_d_eq (ComplexShape.embeddingUpIntGE 0)
      (Int.zero_add (q : ℤ)) (Int.zero_add ((q+1 : ℕ) : ℤ))).trans
      (congrArg (fun d => (termIso p r q).hom ≫ d ≫ (termIso p r (q+1)).inv) hn)
  let E := (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat).mapIso (termIso p r (q+1))
  let a := E.app (op B.1)
  let t := (termIso p r q).hom.hom.app (op B.1) s
  rw [hd]
  change (onBasisIso p r (q+1)).hom.app (op B) (a.hom (a.inv ((differential p r q).hom.app (op B.1) t))) = _
  rw [Iso.inv_hom_id_apply]
  have ht : coordinates p r B q s = (onBasisIso p r q).hom.app (op B) t := rfl
  rw [ht]
  have hh : (onBasisIso p r (q+1)).hom.app (op B) ((differential p r q).hom.app (op B.1) t) =
      (chartComplex p r B).d q (q+1) ((onBasisIso p r q).hom.app (op B) t) :=
    ConcreteCategory.congr_hom (onBasisIso_d p r q B) t
  refine hh.trans ?_
  simp only [chartComplex, CycleQ2FrameDifferentialNaturality.affineComplex, CochainComplex.of_d]
  rfl

variable (W : FramedOpen p r) (f g : Γ(X,W.1))

def singleOpen (f : Γ(X,W.1)) : FramedOpen p r :=
  ⟨X.basicOpen f, W.2.1.basicOpen f,
    hasFrame_of_affine_le p r (X.basicOpen_le f) W.2.1 (W.2.1.basicOpen f) W.2.2⟩

def intersection : FramedOpen p r := by
  refine ⟨(cover f g).X₁, ?_⟩
  change IsAffineOpen (X.basicOpen f ⊓ X.basicOpen g) ∧ HasFrame p r (X.basicOpen f ⊓ X.basicOpen g)
  rw [← X.basicOpen_mul]
  exact (singleOpen p r W (f*g)).2

abbrev first : intersection p r W f g ⟶ singleOpen p r W f := homOfLE (show X.basicOpen f ⊓ X.basicOpen g ≤ X.basicOpen f from inf_le_left)
abbrev second : intersection p r W f g ⟶ singleOpen p r W g := homOfLE (show X.basicOpen f ⊓ X.basicOpen g ≤ X.basicOpen g from inf_le_right)
abbrev toAmbient (t : Γ(X,W.1)) : singleOpen p r W t ⟶ W := homOfLE (X.basicOpen_le t)

def IsBoundary (q : ℕ) (s : ordinary p r (intersection p r W f g) q) : Prop :=
  ∃ (u : ordinary p r (singleOpen p r W f) q) (v : ordinary p r (singleOpen p r W g) q),
    pull p r (first p r W f g) q u - pull p r (second p r W f g) q v = s

theorem mem_boundary_iff (q : ℕ) (s : Sections (term p r q) (cover f g).X₁) :
    s ∈ (overlapBoundary (cover f g) (term p r q)).range ↔
      IsBoundary p r W f g q (coordinates p r (intersection p r W f g) q s) := by
  let A := singleOpen p r W f
  let B := singleOpen p r W g
  let T := intersection p r W f g
  have eqn (u : Sections (term p r q) A.1) (v : Sections (term p r q) B.1) :
      coordinates p r T q (overlapBoundary (cover f g) (term p r q) (u,v)) =
        pull p r (first p r W f g) q (coordinates p r A q u) -
          pull p r (second p r W f g) q (coordinates p r B q v) := by
    rw [← coordinates_restrict, ← coordinates_restrict, ← map_sub]
    rfl
  constructor
  · rintro ⟨⟨u,v⟩,rfl⟩
    exact ⟨_, _, (eqn u v).symm⟩
  · rintro ⟨u,v,h⟩
    obtain ⟨u,rfl⟩ := (coordinates p r A q).surjective u
    obtain ⟨v,rfl⟩ := (coordinates p r B q).surjective v
    exact ⟨(u,v),(coordinates p r T q).injective ((eqn u v).trans h)⟩

theorem closed_mod_boundary_iff (q : ℕ) (s : Sections (term p r q) (cover f g).X₁) :
    (delta p r q).hom.app (op (cover f g).X₁) s ∈
      (overlapBoundary (cover f g) (term p r (q+1))).range ↔
    IsBoundary p r W f g (q+1)
      (deriv p r (intersection p r W f g) q (coordinates p r (intersection p r W f g) q s)) := by
  rw [mem_boundary_iff]
  exact Iff.of_eq (congrArg (IsBoundary p r W f g (q+1)) (coordinates_d p r (intersection p r W f g) q s))

theorem primitive_mod_boundary_iff (q : ℕ) (s : Sections (term p r (q+1)) (cover f g).X₁) :
    (∃ t : Sections (term p r q) (cover f g).X₁,
      s - (delta p r q).hom.app (op (cover f g).X₁) t ∈
        (overlapBoundary (cover f g) (term p r (q+1))).range) ↔
    ∃ t : ordinary p r (intersection p r W f g) q,
      IsBoundary p r W f g (q+1) (coordinates p r (intersection p r W f g) (q+1) s -
        deriv p r (intersection p r W f g) q t) := by
  constructor
  · rintro ⟨t,h⟩
    refine ⟨coordinates p r (intersection p r W f g) q t,?_⟩
    erw [mem_boundary_iff, map_sub (coordinates p r (intersection p r W f g) (q+1))] at h
    exact (congrArg (fun a => IsBoundary p r W f g (q+1) (coordinates p r (intersection p r W f g) (q+1) s - a))
      (coordinates_d p r (intersection p r W f g) q t)) ▸ h
  · rintro ⟨t,h⟩
    obtain ⟨t,rfl⟩ := (coordinates p r (intersection p r W f g) q).surjective t
    refine ⟨t,?_⟩
    erw [mem_boundary_iff, map_sub (coordinates p r (intersection p r W f g) (q+1))]
    exact (congrArg (fun a => IsBoundary p r W f g (q+1) (coordinates p r (intersection p r W f g) (q+1) s - a))
      (coordinates_d p r (intersection p r W f g) q t)).symm ▸ h

/-- In supported degree two it is enough to show every closed ordinary
 zero-form on the intersection lies in the signed restriction image. -/
theorem degree_zero_representative (he :
    ∀ x : ordinary p r (intersection p r W f g) 0,
      IsBoundary p r W f g 1 (deriv p r (intersection p r W f g) 0 x) →
        IsBoundary p r W f g 0 x)
    (s : Sections (term p r 0) (cover f g).X₁)
    (hs : (delta p r 0).hom.app (op (cover f g).X₁) s ∈
      (overlapBoundary (cover f g) (term p r 1)).range) :
    ∃ t : Sections ((relativeDeRhamInt p r).X (-1)) (cover f g).X₁,
      s - ((relativeDeRhamInt p r).d (-1) 0).hom.app (op (cover f g).X₁) t ∈
        (overlapBoundary (cover f g) (term p r 0)).range := by
  refine ⟨0,?_⟩
  rw [map_zero, sub_zero, mem_boundary_iff]
  exact he _ ((closed_mod_boundary_iff p r W f g 0 s).mp hs)

/-- In supported degree three, algebraic exactness modulo the signed
 boundary supplies a primitive in the original sheaf complex. -/
theorem degree_one_representative (he :
    ∀ x : ordinary p r (intersection p r W f g) 1,
      IsBoundary p r W f g 2 (deriv p r (intersection p r W f g) 1 x) →
        ∃ t : ordinary p r (intersection p r W f g) 0,
          IsBoundary p r W f g 1 (x - deriv p r (intersection p r W f g) 0 t))
    (s : Sections (term p r 1) (cover f g).X₁)
    (hs : (delta p r 1).hom.app (op (cover f g).X₁) s ∈
      (overlapBoundary (cover f g) (term p r 2)).range) :
    ∃ t : Sections (term p r 0) (cover f g).X₁,
      s - (delta p r 0).hom.app (op (cover f g).X₁) t ∈
        (overlapBoundary (cover f g) (term p r 1)).range :=
  (primitive_mod_boundary_iff p r W f g 0 s).mpr (he _ ((closed_mod_boundary_iff p r W f g 1 s).mp hs))

/-- The ambient restriction to the two principal opens, in ordinary forms. -/
def pair (q : ℕ) (s : ordinary p r W q) :
    ordinary p r (singleOpen p r W f) q × ordinary p r (singleOpen p r W g) q :=
  (pull p r (toAmbient p r W f) q s, pull p r (toAmbient p r W g) q s)

/-- For an exact augmented algebraic row, the actual intrinsic sheaf restricts
 bijectively onto compatible pairs on the two principal opens. -/
theorem augmented_row_of_ordinary (q : ℕ)
    (hi : Function.Injective (pair p r W f g q))
    (hg : ∀ (u : ordinary p r (singleOpen p r W f) q) (v : ordinary p r (singleOpen p r W g) q),
      pull p r (first p r W f g) q u - pull p r (second p r W f g) q v = 0 →
        ∃ s, pair p r W f g q s = (u,v)) :
    Function.Injective (CycleQ2SupportedCechLower.toPair (cover f g) (union_le f g) (term p r q)) ∧
      ∀ z, overlapBoundary (cover f g) (term p r q) z = 0 →
        ∃ a, CycleQ2SupportedCechLower.toPair (cover f g) (union_le f g) (term p r q) a = z := by
  let A := singleOpen p r W f
  let B := singleOpen p r W g
  let e := (coordinates p r A q).prodCongr (coordinates p r B q)
  let j := CycleQ2SupportedCechLower.toPair (cover f g) (union_le f g) (term p r q)
  have hn (v : Sections (term p r q) W.1) :
      e (j v) = pair p r W f g q (coordinates p r W q v) :=
    Prod.ext (coordinates_restrict p r (toAmbient p r W f) q v)
      (coordinates_restrict p r (toAmbient p r W g) q v)
  constructor
  · intro x y h
    apply (coordinates p r W q).injective
    apply hi
    exact (hn x).symm.trans ((congrArg e h).trans (hn y))
  · rintro ⟨u,v⟩ h
    have hh : pull p r (first p r W f g) q (coordinates p r A q u) -
        pull p r (second p r W f g) q (coordinates p r B q v) = 0 := by
      erw [← coordinates_restrict p r (first p r W f g) q u,
        ← coordinates_restrict p r (second p r W f g) q v,
        ← map_sub (coordinates p r (intersection p r W f g) q)]
      exact (congrArg (coordinates p r (intersection p r W f g) q) h).trans (map_zero _)
    obtain ⟨a,ha⟩ := hg _ _ hh
    obtain ⟨s,rfl⟩ := (coordinates p r W q).surjective a
    exact ⟨s, e.injective ((hn s).trans ha)⟩

end CycleQ2FramedCechFormRow
end

section
namespace CycleQ2FramedCechFormRow
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Module KaehlerDifferential
open CycleQ2IntrinsicFramedAffineSite (FramedOpen frame frame_apply functions)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2RelativeAffineOverlap (restrict)
open CycleQ2FramedAffineSite (restrict_comp)
open CycleQ2LocalPrincipalGysin (cover union_le)
open CycleQ2CechDenominatorTorsion (fromFirst fromSecond)
open CycleQ2ExactFrameThreeDeRham (exteriorPullback)

theorem eq_on_localization {k A B T : Type} [CommRing k] [CommRing A] [CommRing B]
    [CommRing T] [Algebra k A] [Algebra k B] [Algebra k T] [Algebra A B] [Algebra A T]
    [IsScalarTower k A B] [IsScalarTower k A T] (x : A) [IsLocalization.Away x B]
    (a : B →ₐ[k] T) (c : B →ₐ[A] T) (h : ∀ t : A, a (algebraMap A B t) = algebraMap A T t) :
    a = c.restrictScalars k := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers x)
  ext t
  exact (h t).trans (c.commutes t).symm

variable {k : Type} [Field k] [CharZero k] {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) (r : ℕ) [SmoothOfRelativeDimension r p]
  (W : FramedOpen p r) (f g : Γ(X,W.1))

/-- Unique gluing of every degree of ordinary forms over the actual principal
 opens in a framed chart for a regular pair. -/
theorem regular_augmented_nat (hf : IsLeftRegular f)
    (hg : IsLeftRegular (Ideal.Quotient.mk (Ideal.span {f}) g)) (q : ℕ) :
    Function.Injective (CycleQ2SupportedCechLower.toPair (cover f g) (union_le f g) (term p r q)) ∧
      ∀ z, CycleQ2SupportedCechExt.overlapBoundary (cover f g) (term p r q) z = 0 →
        ∃ a, CycleQ2SupportedCechLower.toPair (cover f g) (union_le f g) (term p r q) a = z := by
  let A := Γ(X,W.1)
  let U := Γ(X,(singleOpen p r W f).1)
  let V := Γ(X,(singleOpen p r W g).1)
  let T := Γ(X,(intersection p r W f g).1)
  let hU : (singleOpen p r W f).1 ≤ W.1 := X.basicOpen_le f
  let hV : (singleOpen p r W g).1 ≤ W.1 := X.basicOpen_le g
  let hT : (intersection p r W f g).1 ≤ W.1 := (first p r W f g).le.trans hU
  let : Algebra k A := (sectionCoefficients p W.1).toAlgebra
  let : Algebra k U := (sectionCoefficients p (singleOpen p r W f).1).toAlgebra
  let : Algebra k V := (sectionCoefficients p (singleOpen p r W g).1).toAlgebra
  let : Algebra k T := (sectionCoefficients p (intersection p r W f g).1).toAlgebra
  let : Algebra A U := (restrict p hU).toRingHom.toAlgebra
  let : Algebra A V := (restrict p hV).toRingHom.toAlgebra
  let : Algebra A T := (restrict p hT).toRingHom.toAlgebra
  let : IsScalarTower k A U := IsScalarTower.of_algHom (restrict p hU)
  let : IsScalarTower k A V := IsScalarTower.of_algHom (restrict p hV)
  let : IsScalarTower k A T := IsScalarTower.of_algHom (restrict p hT)
  let : IsLocalization.Away f U := W.2.1.isLocalization_of_eq_basicOpen f (homOfLE hU) rfl
  let : IsLocalization.Away g V := W.2.1.isLocalization_of_eq_basicOpen g (homOfLE hV) rfl
  let : IsLocalization.Away (f*g) T :=
    W.2.1.isLocalization_of_eq_basicOpen (f*g) (homOfLE hT) (X.basicOpen_mul f g).symm
  let a : (intersection p r W f g).1 ≤ (singleOpen p r W f).1 := (first p r W f g).le
  let c : (intersection p r W f g).1 ≤ (singleOpen p r W g).1 := (second p r W f g).le
  have h₁ : restrict p a = (fromFirst (A := U) (T := T) f g).restrictScalars k :=
    eq_on_localization f _ _ (fun t => (AlgHom.congr_fun (restrict_comp p hU a) t).symm)
  have h₂ : restrict p c = (fromSecond (B := V) (T := T) f g).restrictScalars k :=
    eq_on_localization g _ _ (fun t => (AlgHom.congr_fun (restrict_comp p hV c) t).symm)
  obtain ⟨hinj,hlift⟩ := CycleQ2NormalExteriorCech.exterior_row (K := k) (R := A)
    (U := U) (V := V) (T := T) f g (frame p r W) (functions p r W) (frame_apply p r W) hf hg q
  apply augmented_row_of_ordinary
  · intro x y h
    exact hinj (congrArg Prod.fst h)
  · intro α β h
    have hh := sub_eq_zero.mp h
    change exteriorPullback (restrict p a) q α = exteriorPullback (restrict p c) q β at hh
    rw [h₁,h₂] at hh
    obtain ⟨ω,hω,hω'⟩ := hlift α β hh
    exact ⟨ω,Prod.ext hω hω'⟩

end CycleQ2FramedCechFormRow
end

namespace CycleQ2PrincipalChartSupportedVanishing
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2InjectiveCech (Sections AbSheaf freeOpen freeOpenSections)
open CycleQ2IntrinsicFramedAffineSite (FramedOpen)
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRham relativeDeRhamInt)
open CycleQ2LocalPrincipalGysin (cover union_le supportedQuotient)
open CycleQ2SupportedCechExt (overlapBoundary higher_vanishing)
open CycleQ2SupportedCechLower (toPair restriction_bijective supported_zero_vanishing supported_one_vanishing)
variable {k : Type} [Field k] [CharZero k] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k))
    (r : ℕ) [SmoothOfRelativeDimension r p] (W : FramedOpen p r) (x y : Γ(X,W.1))
private abbrev K := relativeDeRhamInt p r
private abbrev C := AbSheaf (show TopCat from X)
local instance : HasDerivedCategory.{1} (C (X := X)) := HasDerivedCategory.standard _
local instance : HasExt.{1} (C (X := X)) := HasExt.standard _

/-- Exactness at the first two terms of the regular two-equation Čech row. -/
abbrev AugmentedRows :=
  (∀ j, Function.Injective (toPair (cover x y) (union_le x y) ((K p r).X j))) ∧
  (∀ j (z : Sections ((K p r).X j) (cover x y).X₂ × Sections ((K p r).X j) (cover x y).X₃),
      overlapBoundary (cover x y) ((K p r).X j) z = 0 → ∃ a, toPair (cover x y) (union_le x y) ((K p r).X j) a = z)

/-- Closed overlap representatives have primitives modulo the signed single-open restrictions. -/
abbrev ExactOnOverlap (n : ℤ) :=
  ∀ s : Sections ((K p r).X n) (cover x y).X₁,
      ((K p r).dFrom n).hom.app (op (cover x y).X₁) s ∈ (overlapBoundary (cover x y) ((K p r).xNext n)).range →
      ∃ t : Sections ((K p r).xPrev n) (cover x y).X₁,
        s - ((K p r).dTo n).hom.app (op (cover x y).X₁) t ∈ (overlapBoundary (cover x y) ((K p r).X n)).range

/-- Vanishing for the actual supported source on a smooth framed affine chart. -/
theorem vanishing (hrows : AugmentedRows p r W x y) (n : ℤ) (hn : ExactOnOverlap p r W x y n) :
    Subsingleton ((DerivedCategory.singleFunctor (C (X := X)) 0).obj (supportedQuotient x y) ⟶
      (DerivedCategory.Q.obj (K p r))⟦n+2⟧) := by
  let T := cover x y
  have hw := CycleQ2FramedOpenFormCoefficients.term_acyclic p r W
  have aff {V : X.Opens} (le : V ≤ W.1) (hv : IsAffineOpen V) (j : ℤ) (m : ℕ) :
      Subsingleton (Ext (freeOpen V) ((K p r).X j) (m+1)) :=
    CycleQ2FramedOpenFormCoefficients.term_acyclic p r ⟨V,hv,
      CycleQ2FiniteExactAffineAtlas.hasFrame_of_affine_le p r le W.2.1 hv W.2.2⟩ j m
  have hu := aff (X.basicOpen_le x) (W.2.1.basicOpen x)
  have hv := aff (X.basicOpen_le y) (W.2.1.basicOpen y)
  have ht : IsAffineOpen T.X₁ := by
    change IsAffineOpen (X.basicOpen x ⊓ X.basicOpen y)
    rw [← X.basicOpen_mul]
    exact W.2.1.basicOpen _
  have hd := aff (V := T.X₁) (T.f₁₂.le.trans (X.basicOpen_le x)) ht
  have hr (j : ℤ) := restriction_bijective T (union_le x y) ((K p r).X j) (hrows.1 j) (hrows.2 j)
  let L : CochainComplex (AbSheaf (show TopCat from X)) ℤ := K p r
  have : L.IsStrictlyGE 0 := by
    change (K p r).IsStrictlyGE 0
    apply ((K p r).isStrictlyGE_iff 0).2
    intro i hi
    exact (relativeDeRham p r).isZero_extend_X (ComplexShape.embeddingUpIntGE 0) i (by
      intro a ha; change (0:ℤ)+a=i at ha; omega)
  refine CycleQ2SupportedSingleRow.vanishing.{1} (supportedQuotient x y) L
    0 ?_ ?_ ?_ n ?_
  · exact fun j => supported_zero_vanishing T (union_le x y) _ (hr j).injective
  · exact fun j => supported_one_vanishing T (union_le x y) _ (hr j).surjective (hw j 0)
  · exact fun j m => higher_vanishing T (union_le x y) _ m (hw j (m+2)) (hu j (m+1)) (hv j (m+1)) (hd j m)
  · exact (CycleQ2SupportedExtComplex.E2_exactAt_iff T (union_le x y) (K p r) n
      (fun j => hw j 0) (fun j => hw j 1) (fun j => hu j 0) (fun j => hv j 0)).mpr hn

/-- Exactness on functions and one-forms on the double principal open suffices
 for all supported dé Rham groups below degree four. -/
theorem below_four (hrows : AugmentedRows p r W x y) (h₀ : ExactOnOverlap p r W x y 0)
    (h₁ : ExactOnOverlap p r W x y 1) (n : ℤ) (hn : n < 4) :
    Subsingleton ((DerivedCategory.singleFunctor (C (X := X)) 0).obj (supportedQuotient x y) ⟶
      (DerivedCategory.Q.obj (K p r))⟦n⟧) := by
  let m := n-2
  have e : n = m+2 := by dsimp [m]; omega
  rw [e]
  apply vanishing p r W x y hrows
  by_cases hm : m < 0
  · have hz : IsZero ((K p r).X m) := (relativeDeRham p r).isZero_extend_X
      (ComplexShape.embeddingUpIntGE 0) m (by intro a ha; change (0:ℤ)+a=m at ha; omega)
    intro s _
    have hs : s = 0 := by
      let V := (cover x y).X₁
      let F : AbSheaf (show TopCat from X) := (K p r).X m
      let e := freeOpenSections (X := (show TopCat from X)) F V
      exact e.symm.injective (hz.eq_of_tgt _ _)
    exact ⟨0,by rw [hs, map_zero, sub_zero]; exact AddSubgroup.zero_mem _⟩
  · have hm01 : m = 0 ∨ m = 1 := by omega
    rcases hm01 with h | h
    · exact h ▸ h₀
    · exact h ▸ h₁

end CycleQ2PrincipalChartSupportedVanishing

namespace CycleQ2FramedCechFormRow
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2IntrinsicFramedAffineSite (FramedOpen)
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRham relativeDeRhamInt)
open CycleQ2LocalPrincipalGysin (cover union_le)
open CycleQ2InjectiveCech (Sections freeOpenSections)
open CycleQ2PrincipalChartSupportedVanishing (AugmentedRows ExactOnOverlap)

variable {k : Type} [Field k] [CharZero k] {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) (r : ℕ) [SmoothOfRelativeDimension r p]
  (W : FramedOpen p r) (f g : Γ(X,W.1))

theorem regular_augmentedRows (hf : IsLeftRegular f)
    (hg : IsLeftRegular (Ideal.Quotient.mk (Ideal.span {f}) g)) : AugmentedRows p r W f g := by
  let K := relativeDeRhamInt p r
  have neg (a : ℕ) (U : X.Opens) : Subsingleton (Sections (K.X (.negSucc a)) U) := by
    have hz : IsZero (K.X (.negSucc a)) := (relativeDeRham p r).isZero_extend_X
      (ComplexShape.embeddingUpIntGE 0) _ (by intro n h; change (0:ℤ)+n=Int.negSucc a at h; omega)
    constructor
    intro x y
    apply (freeOpenSections _ U).symm.injective
    exact hz.eq_of_tgt _ _
  constructor
  · intro j
    cases j with
    | ofNat i => exact (regular_augmented_nat p r W f g hf hg i).1
    | negSucc n => intro x y _; exact (neg n W.1).elim x y
  · intro j
    cases j with
    | ofNat i => exact (regular_augmented_nat p r W f g hf hg i).2
    | negSucc n =>
      intro z _
      refine ⟨0,Prod.ext ?_ ?_⟩
      · exact (neg n (cover f g).X₂).elim _ _
      · exact (neg n (cover f g).X₃).elim _ _

/-- On a Noetherian chart two coordinates of an exact four-frame give
 the required augmented exactness without separate regularity hypotheses. -/
theorem adapted_augmentedRows (W : FramedOpen p 4) [SmoothOfRelativeDimension 4 p]
    [IsNoetherianRing Γ(X,W.1)] (u : Fin 4 → Γ(X,W.1)) :
    letI : Algebra k Γ(X,W.1) := (CycleQ2SmoothRelativeFrames.sectionCoefficients p W.1).toAlgebra
    ∀ (b : Module.Basis (Fin 4) Γ(X,W.1) (KaehlerDifferential k Γ(X,W.1))),
      (∀ i, b i = KaehlerDifferential.D k Γ(X,W.1) (u i)) →
        AugmentedRows p 4 W (u 0) (u 1) := by
  let : Algebra k Γ(X,W.1) := (CycleQ2SmoothRelativeFrames.sectionCoefficients p W.1).toAlgebra
  intro b hu
  obtain ⟨hx,hy⟩ := CycleQ2NormalExteriorCech.exact_frame_regular b u hu 0 1 (by decide)
  exact regular_augmentedRows p 4 W (u 0) (u 1) hx hy

private theorem exactOnOverlap_iff' (i n j : ℤ)
    (hi : (ComplexShape.up ℤ).prev n = i) (hj : (ComplexShape.up ℤ).next n = j) :
    ExactOnOverlap p r W f g n ↔
      ∀ s : Sections ((relativeDeRhamInt p r).X n) (cover f g).X₁,
        ((relativeDeRhamInt p r).d n j).hom.app (op (cover f g).X₁) s ∈
          (CycleQ2SupportedCechExt.overlapBoundary (cover f g) ((relativeDeRhamInt p r).X j)).range →
        ∃ t : Sections ((relativeDeRhamInt p r).X i) (cover f g).X₁,
          s - ((relativeDeRhamInt p r).d i n).hom.app (op (cover f g).X₁) t ∈
            (CycleQ2SupportedCechExt.overlapBoundary (cover f g) ((relativeDeRhamInt p r).X n)).range := by
  subst i; subst j; rfl

theorem exactOnOverlap_zero
    (he : ∀ x : ordinary p r (intersection p r W f g) 0,
      IsBoundary p r W f g 1 (deriv p r (intersection p r W f g) 0 x) →
        IsBoundary p r W f g 0 x) : ExactOnOverlap p r W f g 0 := by
  have hn : (ComplexShape.up ℤ).next 0 = 1 := by simp
  have hp : (ComplexShape.up ℤ).prev 0 = (-1) := by simp
  apply (exactOnOverlap_iff' p r W f g _ _ _ hp hn).mpr
  exact degree_zero_representative p r W f g he

theorem exactOnOverlap_one
    (he : ∀ x : ordinary p r (intersection p r W f g) 1,
      IsBoundary p r W f g 2 (deriv p r (intersection p r W f g) 1 x) →
        ∃ t : ordinary p r (intersection p r W f g) 0,
          IsBoundary p r W f g 1 (x - deriv p r (intersection p r W f g) 0 t)) :
    ExactOnOverlap p r W f g 1 := by
  have hn : (ComplexShape.up ℤ).next 1 = 2 := by simp
  have hp : (ComplexShape.up ℤ).prev 1 = 0 := by simp
  apply (exactOnOverlap_iff' p r W f g _ _ _ hp hn).mpr
  exact degree_one_representative p r W f g he

end CycleQ2FramedCechFormRow

namespace CycleQ2AdaptedChartPurity
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Module KaehlerDifferential
open CycleQ2FramedCechFormRow
open CycleQ2IntrinsicFramedAffineSite (FramedOpen frame frame_apply functions)
open CycleQ2RelativeAffineOverlap (restrict)
open CycleQ2FramedAffineSite (restrict_comp)
open CycleQ2CechDenominatorTorsion (fromFirst fromSecond)
open CycleQ2ExactFrameThreeDeRham (exteriorPullback)
open CycleQ2WeightedCoordinateExterior (Form)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRhamInt)
open CycleQ2LocalPrincipalGysin (supportedQuotient)
open CycleQ2InjectiveCech (AbSheaf)

section
variable {k : Type} [Field k] [CharZero k] [Algebra ℂ k] {X : Scheme.{0}}
variable (p : X ⟶ Spec (CommRingCat.of k))
    (W : FramedOpen p 4)
    (u : Fin 4 → Γ(X,W.1))
    (hu : letI := (sectionCoefficients p W.1).toAlgebra;
      ∃ b : Basis (Fin 4) Γ(X,W.1) Ω[Γ(X,W.1)⁄k], ∀ i, b i = D k Γ(X,W.1) (u i))

private abbrev lowFormRows (f g : Γ(X,W.1)) : Prop :=
  let Z := intersection p 4 W f g
  (∀ s : ordinary p 4 Z 0, IsBoundary p 4 W f g 1 (deriv p 4 Z 0 s) →
    IsBoundary p 4 W f g 0 s) ∧
  (∀ s : ordinary p 4 Z 1, IsBoundary p 4 W f g 2 (deriv p 4 Z 1 s) →
    ∃ t : ordinary p 4 Z 0, IsBoundary p 4 W f g 1 (s - deriv p 4 Z 0 t))

private abbrev restrictionBoundary (f g : Γ(X,W.1)) (q : ℕ)
    (s : ordinary p 4 (intersection p 4 W f g) q) : Prop :=
  let U := singleOpen p 4 W f
  let V := singleOpen p 4 W g
  let T := intersection p 4 W f g
  letI : Algebra k Γ(X,U.1) := (sectionCoefficients p U.1).toAlgebra
  letI : Algebra k Γ(X,V.1) := (sectionCoefficients p V.1).toAlgebra
  letI : Algebra k Γ(X,T.1) := (sectionCoefficients p T.1).toAlgebra
  CycleQ2NormalCechFormBoundary.IsBoundary (restrict p (first p 4 W f g).le)
    (restrict p (second p 4 W f g).le) q s

omit [CharZero k] [Algebra ℂ k] in
private theorem lowRows_of_restrictions (f g : Γ(X,W.1))
    (h : let Z := intersection p 4 W f g
      (∀ s : ordinary p 4 Z 0, restrictionBoundary p W f g 1 (deriv p 4 Z 0 s) →
        restrictionBoundary p W f g 0 s) ∧
      (∀ s : ordinary p 4 Z 1, restrictionBoundary p W f g 2 (deriv p 4 Z 1 s) →
        ∃ t : ordinary p 4 Z 0, restrictionBoundary p W f g 1 (s - deriv p 4 Z 0 t))) :
    lowFormRows p W f g := by
  let Z := intersection p 4 W f g
  have bound (q : ℕ) (s : ordinary p 4 Z q) :
      IsBoundary p 4 W f g q s ↔ restrictionBoundary p W f g q s :=
    exists_congr (fun _ => exists_congr fun _ => eq_comm)
  obtain ⟨hzero,hone⟩ := h
  constructor
  · exact fun s hs => (bound 0 s).mpr (hzero s ((bound 1 _).mp hs))
  · intro s hs
    obtain ⟨z,hz⟩ := hone s ((bound 2 _).mp hs)
    exact ⟨z,(bound 1 _).mpr hz⟩

include hu

set_option maxHeartbeats 500000 in
theorem native_exact : lowFormRows p W (u 0) (u 1) := by
  let f := u 0
  let g := u 1
  let A := Γ(X,W.1)
  let U := Γ(X,(singleOpen p 4 W f).1)
  let V := Γ(X,(singleOpen p 4 W g).1)
  let T := Γ(X,(intersection p 4 W f g).1)
  let hU : (singleOpen p 4 W f).1 ≤ W.1 := X.basicOpen_le f
  let hV : (singleOpen p 4 W g).1 ≤ W.1 := X.basicOpen_le g
  let hT : (intersection p 4 W f g).1 ≤ W.1 := (first p 4 W f g).le.trans hU
  let : Algebra k A := (sectionCoefficients p W.1).toAlgebra
  let : Algebra k U := (sectionCoefficients p (singleOpen p 4 W f).1).toAlgebra
  let : Algebra k V := (sectionCoefficients p (singleOpen p 4 W g).1).toAlgebra
  let : Algebra k T := (sectionCoefficients p (intersection p 4 W f g).1).toAlgebra
  let : Algebra A U := (restrict p hU).toRingHom.toAlgebra
  let : Algebra A V := (restrict p hV).toRingHom.toAlgebra
  let : Algebra A T := (restrict p hT).toRingHom.toAlgebra
  let : IsScalarTower k A U := IsScalarTower.of_algHom (restrict p hU)
  let : IsScalarTower k A V := IsScalarTower.of_algHom (restrict p hV)
  let : IsScalarTower k A T := IsScalarTower.of_algHom (restrict p hT)
  let : IsLocalization.Away f U := W.2.1.isLocalization_of_eq_basicOpen f (homOfLE hU) rfl
  let : IsLocalization.Away g V := W.2.1.isLocalization_of_eq_basicOpen g (homOfLE hV) rfl
  let : IsLocalization.Away (f*g) T :=
    W.2.1.isLocalization_of_eq_basicOpen (f*g) (homOfLE hT) (X.basicOpen_mul f g).symm
  let a : (intersection p 4 W f g).1 ≤ (singleOpen p 4 W f).1 := (first p 4 W f g).le
  let c : (intersection p 4 W f g).1 ≤ (singleOpen p 4 W g).1 := (second p 4 W f g).le
  have h₁ : restrict p a = (fromFirst (A := U) (T := T) f g).restrictScalars k :=
    eq_on_localization f _ _ (fun t => (AlgHom.congr_fun (restrict_comp p hU a) t).symm)
  have h₂ : restrict p c = (fromSecond (B := V) (T := T) f g).restrictScalars k :=
    eq_on_localization g _ _ (fun t => (AlgHom.congr_fun (restrict_comp p hV c) t).symm)
  obtain ⟨b,hb⟩ := hu
  let Z := intersection p 4 W f g
  apply lowRows_of_restrictions p W f g
  dsimp only [restrictionBoundary]
  rw [h₁,h₂]
  exact CycleQ2NormalChartForms.low_degrees (U := U) (V := V) (T := T) b u hb 0 1 (by decide)
    (frame p 4 Z) (functions p 4 Z) (frame_apply p 4 Z)

end

section
variable {k : Type} [Field k] [CharZero k] [Algebra ℂ k] {X : Scheme.{0}}
variable (p : X ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 4 p]
    (W : FramedOpen p 4) [IsNoetherianRing Γ(X,W.1)]
    (u : Fin 4 → Γ(X,W.1))
    (hu : letI := (sectionCoefficients p W.1).toAlgebra;
      ∃ b : Basis (Fin 4) Γ(X,W.1) Ω[Γ(X,W.1)⁄k], ∀ i, b i = D k Γ(X,W.1) (u i))
local instance : HasDerivedCategory.{1} (AbSheaf (show TopCat from X)) := HasDerivedCategory.standard _
include hu

/-- For the complement of the actual two coordinate equations in the ambient
chart, the derived supported de Rham group vanishes in every degree below four. -/
theorem below_four (n : ℤ) (hn : n < 4) : Subsingleton
    ((DerivedCategory.singleFunctor (AbSheaf (show TopCat from X)) 0).obj (supportedQuotient (u 0) (u 1)) ⟶
      (DerivedCategory.Q.obj (relativeDeRhamInt p 4))⟦n⟧) := by
  let : Algebra k Γ(X,W.1) := (sectionCoefficients p W.1).toAlgebra
  obtain ⟨h₀,h₁⟩ := native_exact p W u hu
  obtain ⟨B,hB⟩ := hu
  exact CycleQ2PrincipalChartSupportedVanishing.below_four p 4 W (u 0) (u 1)
    (adapted_augmentedRows p W u B hB) (exactOnOverlap_zero p 4 W (u 0) (u 1) h₀)
    (exactOnOverlap_one p 4 W (u 0) (u 1) h₁) n hn

end

end CycleQ2AdaptedChartPurity

/-! Three normal equations use the top row of the genuine three-open
Čech complex. The omitted faces below are indexed in the order 12, 02,
01; the middle sign is absorbed only when passing to the same boundary
subgroup, not when defining the actual connecting map. -/

namespace CycleQ2FramedTripleCechFormRow

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open CycleQ2IntrinsicFramedAffineSite (FramedOpen)
open CycleQ2FiniteExactAffineAtlas (hasFrame_of_affine_le)
open CycleQ2FramedCechFormRow (ordinary singleOpen intersection pull coordinates
  coordinates_restrict coordinates_d deriv term delta)
open CycleQ2ThreeOpenCechH2 (TripleOpen)
open CycleQ2FinitePrincipalParts (denominator faceDenominator)
open CycleQ2InjectiveCech (Sections)

variable {k : Type} [Field k] [CharZero k] {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) (r : ℕ) [SmoothOfRelativeDimension r p]
  (W : FramedOpen p r) (x : Fin 3 → Γ(X,W.1))

abbrev vertex (i : Fin 3) : X.Opens := X.basicOpen (x i)
abbrev topOpen : X.Opens := TripleOpen (vertex p r W x 0) (vertex p r W x 1) (vertex p r W x 2)

theorem topOpen_eq_basic : topOpen p r W x = X.basicOpen (denominator x) := by
  simp only [topOpen, TripleOpen, vertex, denominator, Fin.prod_univ_three, X.basicOpen_mul]
  simp only [inf_assoc, inf_left_comm, inf_comm, inf_idem]

def top : FramedOpen p r :=
  ⟨topOpen p r W x, by
    rw [topOpen_eq_basic]
    exact (singleOpen p r W (denominator x)).2⟩

def face (i : Fin 3) : FramedOpen p r :=
  ![intersection p r W (x 1) (x 2), intersection p r W (x 0) (x 2),
    intersection p r W (x 0) (x 1)] i

theorem face_eq_basic (i : Fin 3) :
    (face p r W x i).1 = X.basicOpen (faceDenominator x i) := by
  have hu : (Finset.univ : Finset (Fin 3)) = {0,1,2} := by decide
  fin_cases i <;>
    simp [face, intersection, CycleQ2LocalPrincipalGysin.cover, faceDenominator,
      hu, X.basicOpen_mul]

def toFace (i : Fin 3) : top p r W x ⟶ face p r W x i := by
  apply homOfLE
  fin_cases i
  · exact inf_le_right
  · exact inf_le_left
  · exact inf_le_inf (inf_le_left : vertex p r W x 0 ⊓ vertex p r W x 2 ≤ vertex p r W x 0)
      (inf_le_left : vertex p r W x 1 ⊓ vertex p r W x 2 ≤ vertex p r W x 1)

theorem top_le : (top p r W x).1 ≤ W.1 :=
  (inf_le_left.trans inf_le_left).trans (X.basicOpen_le (x 0))

theorem face_le (i : Fin 3) : (face p r W x i).1 ≤ W.1 := by
  rw [face_eq_basic]
  exact X.basicOpen_le _

abbrev unionOpen : X.Opens := (vertex p r W x 0 ⊔ vertex p r W x 1) ⊔ vertex p r W x 2
theorem union_le : unionOpen p r W x ≤ W.1 :=
  sup_le (sup_le (X.basicOpen_le (x 0)) (X.basicOpen_le (x 1))) (X.basicOpen_le (x 2))

abbrev supportedQuotient := CycleQ2RelativeOpenSupport.quotient (union_le p r W x)

/-- A sum of actual omitted-face form restrictions. It is the same
subgroup as the ordered Čech boundary with signs +−+. -/
def IsBoundary (q : ℕ) (ω : ordinary p r (top p r W x) q) : Prop :=
  ∃ α : ∀ i, ordinary p r (face p r W x i) q,
    ω = ∑ i, pull p r (toFace p r W x i) q (α i)

private theorem boundary_coordinates (q : ℕ)
    (a : Sections (term p r q) (vertex p r W x 0 ⊓ vertex p r W x 1))
    (b : Sections (term p r q) (vertex p r W x 0 ⊓ vertex p r W x 2))
    (c : Sections (term p r q) (vertex p r W x 1 ⊓ vertex p r W x 2)) :
    coordinates p r (top p r W x) q
      (CycleQ2ThreeOpenSupportedCechExt.boundary (vertex p r W x 0) (vertex p r W x 1)
        (vertex p r W x 2) (term p r q) (a,b,c)) =
      pull p r (toFace p r W x 0) q (coordinates p r (face p r W x 0) q c) -
        pull p r (toFace p r W x 1) q (coordinates p r (face p r W x 1) q b) +
        pull p r (toFace p r W x 2) q (coordinates p r (face p r W x 2) q a) := by
  rw [← coordinates_restrict, ← coordinates_restrict, ← coordinates_restrict,
    ← map_sub, ← map_add]
  rfl

/-- The native finite sum of face forms represents exactly the range
of the actual three-open section differential. -/
theorem mem_boundary_iff (q : ℕ) (s : Sections (term p r q) (topOpen p r W x)) :
    s ∈ (CycleQ2ThreeOpenSupportedCechExt.boundary (vertex p r W x 0) (vertex p r W x 1)
      (vertex p r W x 2) (term p r q)).range ↔
    IsBoundary p r W x q (coordinates p r (top p r W x) q s) := by
  classical
  constructor
  · rintro ⟨⟨a,b,c⟩,rfl⟩
    refine ⟨Fin.cases (coordinates p r (face p r W x 0) q c)
      (Fin.cases (-coordinates p r (face p r W x 1) q b)
        (Fin.cases (coordinates p r (face p r W x 2) q a) Fin.elim0)),?_⟩
    rw [boundary_coordinates]
    simp only [Fin.sum_univ_three, Fin.cases_zero, Fin.cases_succ, map_neg, sub_eq_add_neg]
  · rintro ⟨α,hα⟩
    let a := (coordinates p r (face p r W x 2) q).symm (α 2)
    let b := (coordinates p r (face p r W x 1) q).symm (-α 1)
    let c := (coordinates p r (face p r W x 0) q).symm (α 0)
    refine ⟨(a,b,c),(coordinates p r (top p r W x) q).injective ?_⟩
    rw [boundary_coordinates, hα]
    simp only [a,b,c,AddEquiv.apply_symm_apply,Fin.sum_univ_three,map_neg,
      sub_neg_eq_add]

theorem closed_mod_boundary_iff (q : ℕ) (s : Sections (term p r q) (topOpen p r W x)) :
    (delta p r q).hom.app (op (topOpen p r W x)) s ∈
      (CycleQ2ThreeOpenSupportedCechExt.boundary (vertex p r W x 0) (vertex p r W x 1)
        (vertex p r W x 2) (term p r (q+1))).range ↔
    IsBoundary p r W x (q+1)
      (deriv p r (top p r W x) q (coordinates p r (top p r W x) q s)) := by
  rw [mem_boundary_iff]
  exact Iff.of_eq (congrArg (IsBoundary p r W x (q+1)) (coordinates_d p r _ q s))

theorem primitive_mod_boundary_iff (q : ℕ)
    (s : Sections (term p r (q+1)) (topOpen p r W x)) :
    (∃ t : Sections (term p r q) (topOpen p r W x),
      s - (delta p r q).hom.app (op (topOpen p r W x)) t ∈
        (CycleQ2ThreeOpenSupportedCechExt.boundary (vertex p r W x 0) (vertex p r W x 1)
          (vertex p r W x 2) (term p r (q+1))).range) ↔
    ∃ t : ordinary p r (top p r W x) q,
      IsBoundary p r W x (q+1) (coordinates p r (top p r W x) (q+1) s -
        deriv p r (top p r W x) q t) := by
  constructor
  · rintro ⟨t,ht⟩
    refine ⟨coordinates p r (top p r W x) q t,?_⟩
    rw [mem_boundary_iff, map_sub, coordinates_d] at ht
    exact ht
  · rintro ⟨t,ht⟩
    obtain ⟨t,rfl⟩ := (coordinates p r (top p r W x) q).surjective t
    refine ⟨t,?_⟩
    rw [mem_boundary_iff, map_sub, coordinates_d]
    exact ht

end CycleQ2FramedTripleCechFormRow

namespace CycleQ2ThreePrincipalChartSupportedVanishing

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf Sections freeOpen freeOpenSections)
open CycleQ2IntrinsicFramedAffineSite (FramedOpen)
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRham relativeDeRhamInt)
open CycleQ2FramedTripleCechFormRow
open CycleQ2ThreeOpenCechH2 (outerSquare)

variable {k : Type} [Field k] [CharZero k] {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) (r : ℕ) [SmoothOfRelativeDimension r p]
  (W : FramedOpen p r) (x : Fin 3 → Γ(X,W.1))
private abbrev K := relativeDeRhamInt p r
private abbrev C := AbSheaf (show TopCat from X)
local instance : HasDerivedCategory.{1} (C (X := X)) := HasDerivedCategory.standard _
local instance : HasExt.{1} (C (X := X)) := HasExt.standard _

/-- The augmented three-open row has the same sections as the ambient
open and has zero first cohomology. These are the concrete remaining
lower-row requirements, separate from the top principal-parts row. -/
abbrev LowerRows : Prop := ∀ j : ℤ,
  Function.Bijective (((K p r).X j).obj.map (homOfLE (union_le p r W x)).op) ∧
    Subsingleton (((K p r).X j).H' 1 (unionOpen p r W x))

abbrev ExactOnOverlap (n : ℤ) : Prop :=
  ∀ s : Sections ((K p r).X n) (topOpen p r W x),
    ((K p r).dFrom n).hom.app (op (topOpen p r W x)) s ∈
      (CycleQ2ThreeOpenSupportedCechExt.boundary (vertex p r W x 0) (vertex p r W x 1)
        (vertex p r W x 2) ((K p r).xNext n)).range →
    ∃ t : Sections ((K p r).xPrev n) (topOpen p r W x),
      s - ((K p r).dTo n).hom.app (op (topOpen p r W x)) t ∈
        (CycleQ2ThreeOpenSupportedCechExt.boundary (vertex p r W x 0) (vertex p r W x 1)
          (vertex p r W x 2) ((K p r).X n)).range

/-- The third row computes actual supported hypercohomology in degree
shifted by three on these exact affine principal charts. -/
theorem vanishing (hrows : LowerRows p r W x) (n : ℤ)
    (hn : ExactOnOverlap p r W x n) :
    Subsingleton ((DerivedCategory.singleFunctor (C (X := X)) 0).obj (supportedQuotient p r W x) ⟶
      (DerivedCategory.Q.obj (K p r))⟦n+3⟧) := by
  have hw := CycleQ2FramedOpenFormCoefficients.term_acyclic p r W
  have hv (i : Fin 3) := CycleQ2FramedOpenFormCoefficients.term_acyclic p r
    (CycleQ2FramedCechFormRow.singleOpen p r W (x i))
  have hf (i : Fin 3) := CycleQ2FramedOpenFormCoefficients.term_acyclic p r (face p r W x i)
  have ht := CycleQ2FramedOpenFormCoefficients.term_acyclic p r (top p r W x)
  let S := outerSquare (vertex p r W x 0) (vertex p r W x 1) (vertex p r W x 2)
  let L : CochainComplex (C (X := X)) ℤ := K p r
  haveI : L.IsStrictlyGE 0 := by
    apply (L.isStrictlyGE_iff 0).2
    intro i hi
    exact (relativeDeRham p r).isZero_extend_X (ComplexShape.embeddingUpIntGE 0) i
      (by intro a ha; change (0:ℤ)+a=i at ha; omega)
  refine CycleQ2SupportedSingleRow.vanishing_three.{1} (supportedQuotient p r W x) L
    0 ?_ ?_ ?_ ?_ n ?_
  · exact fun j => CycleQ2SupportedCechLower.supported_zero_vanishing S (union_le p r W x)
      _ (hrows j).1.injective
  · exact fun j => CycleQ2SupportedCechLower.supported_one_vanishing S (union_le p r W x)
      _ (hrows j).1.surjective (hw j 0)
  · exact fun j => CycleQ2ThreeOpenSupportedCechExt.supported_two_vanishing
      (vertex p r W x 0) (vertex p r W x 1) (vertex p r W x 2) (union_le p r W x) _ (hw j 1) (hrows j).2
  · exact fun j m => CycleQ2ThreeOpenSupportedCechExt.higher_vanishing
      (vertex p r W x 0) (vertex p r W x 1) (vertex p r W x 2) (union_le p r W x) _ m
      (hw j (m+3)) (hv 0 j (m+2)) (hv 1 j (m+2)) (hv 2 j (m+2))
      (hf 2 j (m+1)) (hf 1 j (m+1)) (hf 0 j (m+1)) (ht j m)
  · exact (CycleQ2SupportedExtComplex.E3_exactAt_iff
      (vertex p r W x 0) (vertex p r W x 1) (vertex p r W x 2) (union_le p r W x) (K p r) n
      (fun j => hw j 1) (fun j => hw j 2)
      (fun j => hv 0 j 0) (fun j => hv 1 j 0) (fun j => hv 2 j 0)
      (fun j => hv 0 j 1) (fun j => hv 1 j 1) (fun j => hv 2 j 1)
      (fun j => hf 2 j 0) (fun j => hf 1 j 0) (fun j => hf 0 j 0)).mpr hn

/-- The three low horizontal rows kill all actual supported degrees
below six, including degrees four and five needed to extend the marked
surface class across a boundary with three normal coordinates. -/
theorem below_six (hrows : LowerRows p r W x)
    (h₀ : ExactOnOverlap p r W x 0) (h₁ : ExactOnOverlap p r W x 1)
    (h₂ : ExactOnOverlap p r W x 2) (n : ℤ) (hn : n < 6) :
    Subsingleton ((DerivedCategory.singleFunctor (C (X := X)) 0).obj (supportedQuotient p r W x) ⟶
      (DerivedCategory.Q.obj (K p r))⟦n⟧) := by
  let m := n-3
  have he : n = m+3 := by dsimp [m]; omega
  rw [he]
  apply vanishing p r W x hrows
  by_cases hm : m < 0
  · have hz : IsZero ((K p r).X m) := (relativeDeRham p r).isZero_extend_X
      (ComplexShape.embeddingUpIntGE 0) m
      (by intro a ha; change (0:ℤ)+a=m at ha; omega)
    intro s _
    have hs : s = 0 := (freeOpenSections _ (topOpen p r W x)).symm.injective (hz.eq_of_tgt _ _)
    exact ⟨0,by rw [hs,map_zero,sub_zero]; exact AddSubgroup.zero_mem _⟩
  · have hm012 : m = 0 ∨ m = 1 ∨ m = 2 := by omega
    rcases hm012 with h | h | h
    · exact h ▸ h₀
    · exact h ▸ h₁
    · exact h ▸ h₂

end CycleQ2ThreePrincipalChartSupportedVanishing

#print axioms CycleQ2FramedTripleCechFormRow.mem_boundary_iff
#print axioms CycleQ2ThreePrincipalChartSupportedVanishing.below_six

namespace CycleQ2AdaptedTripleChartPurity

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Module KaehlerDifferential
open CycleQ2IntrinsicFramedAffineSite (FramedOpen frame functions frame_apply)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2FramedCechFormRow (ordinary deriv eq_on_localization)
open CycleQ2FramedTripleCechFormRow
open CycleQ2ThreePrincipalChartSupportedVanishing (LowerRows ExactOnOverlap)
open CycleQ2RelativeAffineOverlap (restrict)
open CycleQ2FramedAffineSite (restrict_comp)
open CycleQ2FinitePrincipalParts (denominator faceDenominator faceToTop)
open CycleQ2WeightedCoordinateExterior (Form)
open CycleQ2ExactFrameThreeDeRham (exteriorPullback)
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRhamInt)
open CycleQ2InjectiveCech (AbSheaf)

variable {k : Type} [Field k] [CharZero k] [Algebra ℂ k] {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) (r : ℕ) [SmoothOfRelativeDimension r p]
  (W : FramedOpen p r) (u : Fin r → Γ(X,W.1)) (normal : Fin 3 → Fin r)
  (hnormal : Function.Injective normal)
  (hu : letI := (sectionCoefficients p W.1).toAlgebra;
    ∃ b : Basis (Fin r) Γ(X,W.1) Ω[Γ(X,W.1)⁄k], ∀ i, b i = D k Γ(X,W.1) (u i))

abbrev equations : Fin 3 → Γ(X,W.1) := u ∘ normal

def LowFormRows (x : Fin 3 → Γ(X,W.1)) : Prop :=
  (∀ ω : ordinary p r (top p r W x) 0,
    IsBoundary p r W x 1 (deriv p r (top p r W x) 0 ω) → IsBoundary p r W x 0 ω) ∧
  (∀ ω : ordinary p r (top p r W x) 1,
    IsBoundary p r W x 2 (deriv p r (top p r W x) 1 ω) →
      ∃ f : ordinary p r (top p r W x) 0,
        IsBoundary p r W x 1 (ω - deriv p r (top p r W x) 0 f)) ∧
  (∀ ω : ordinary p r (top p r W x) 2,
    IsBoundary p r W x 3 (deriv p r (top p r W x) 2 ω) →
      ∃ α : ordinary p r (top p r W x) 1,
        IsBoundary p r W x 2 (ω - deriv p r (top p r W x) 1 α))

include hu hnormal in
/-- The finite principal-parts calculation applies to the actual
section rings of the three pair opens and triple open. Its localization
maps are proved equal to the original scheme restrictions. -/
theorem native_exact : LowFormRows p r W (equations p r W u normal) := by
  let x := equations p r W u normal
  let Z := top p r W x
  let R := Γ(X,W.1)
  let T := Γ(X,Z.1)
  let U (i : Fin 3) := Γ(X,(face p r W x i).1)
  let hT : Z.1 ≤ W.1 := top_le p r W x
  let hU (i : Fin 3) : (face p r W x i).1 ≤ W.1 := face_le p r W x i
  letI : Algebra k R := (sectionCoefficients p W.1).toAlgebra
  letI : Algebra k T := (sectionCoefficients p Z.1).toAlgebra
  letI : ∀ i, Algebra k (U i) := fun i => (sectionCoefficients p (face p r W x i).1).toAlgebra
  letI : Algebra R T := (restrict p hT).toRingHom.toAlgebra
  letI : ∀ i, Algebra R (U i) := fun i => (restrict p (hU i)).toRingHom.toAlgebra
  letI : IsScalarTower k R T := IsScalarTower.of_algHom (restrict p hT)
  letI : ∀ i, IsScalarTower k R (U i) := fun i => IsScalarTower.of_algHom (restrict p (hU i))
  letI : IsLocalization.Away (denominator x) T :=
    W.2.1.isLocalization_of_eq_basicOpen (denominator x) (homOfLE hT) (topOpen_eq_basic p r W x)
  letI : ∀ i, IsLocalization.Away (faceDenominator x i) (U i) := fun i =>
    W.2.1.isLocalization_of_eq_basicOpen (faceDenominator x i) (homOfLE (hU i)) (face_eq_basic p r W x i)
  letI : Algebra ℂ R := ((algebraMap k R).comp (algebraMap ℂ k)).toAlgebra
  letI : Algebra ℂ T := ((algebraMap k T).comp (algebraMap ℂ k)).toAlgebra
  letI : ∀ i, Algebra ℂ (U i) := fun i => ((algebraMap k (U i)).comp (algebraMap ℂ k)).toAlgebra
  letI : IsScalarTower ℂ k R := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower ℂ k T := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower ℂ R T := IsScalarTower.of_algebraMap_eq fun a =>
    IsScalarTower.algebraMap_apply k R T (algebraMap ℂ k a)
  letI : ∀ i, IsScalarTower ℂ R (U i) := fun i => IsScalarTower.of_algebraMap_eq fun a =>
    IsScalarTower.algebraMap_apply k R (U i) (algebraMap ℂ k a)
  have hr (i : Fin 3) : restrict p (toFace p r W x i).le =
      (faceToTop (T := T) U x i).restrictScalars k :=
    eq_on_localization (faceDenominator x i) _ _
      (fun a => (AlgHom.congr_fun (restrict_comp p (hU i) (toFace p r W x i).le) a).symm)
  have hb (q : ℕ) (ω : ordinary p r Z q) : IsBoundary p r W x q ω ↔
      CycleQ2FinitePrincipalFormBoundary.IsBoundary (T := T) U x q ω := by
    change (∃ α : ∀ i, Form k (U i) q,
      ω = ∑ i, exteriorPullback (restrict p (toFace p r W x i).le) q (α i)) ↔ _
    simp only [hr] <;> rfl
  obtain ⟨b,hb₀⟩ := hu
  obtain ⟨h₀,h₁,h₂⟩ := CycleQ2FiniteNormalChartForms.low_degrees (T := T) U b u hb₀ normal
    0 1 2 (fun h => (by decide : (0 : Fin 3) ≠ 1) (hnormal h))
    (fun h => (by decide : (0 : Fin 3) ≠ 2) (hnormal h))
    (fun h => (by decide : (1 : Fin 3) ≠ 2) (hnormal h))
    (frame p r Z) (functions p r Z) (frame_apply p r Z)
  constructor
  · intro ω hω
    exact (hb 0 ω).mpr (h₀ ω ((hb 1 _).mp hω))
  constructor
  · intro ω hω
    obtain ⟨f,hf⟩ := h₁ ω ((hb 2 _).mp hω)
    exact ⟨f,(hb 1 _).mpr hf⟩
  · intro ω hω
    obtain ⟨α,hα⟩ := h₂ ω ((hb 3 _).mp hω)
    exact ⟨α,(hb 2 _).mpr hα⟩

private theorem exactOnOverlap_iff' (x : Fin 3 → Γ(X,W.1)) (i n j : ℤ)
    (hi : (ComplexShape.up ℤ).prev n = i) (hj : (ComplexShape.up ℤ).next n = j) :
    ExactOnOverlap p r W x n ↔
      ∀ s : CycleQ2InjectiveCech.Sections ((relativeDeRhamInt p r).X n) (topOpen p r W x),
        ((relativeDeRhamInt p r).d n j).hom.app (op (topOpen p r W x)) s ∈
          (CycleQ2ThreeOpenSupportedCechExt.boundary (vertex p r W x 0) (vertex p r W x 1)
            (vertex p r W x 2) ((relativeDeRhamInt p r).X j)).range →
        ∃ t : CycleQ2InjectiveCech.Sections ((relativeDeRhamInt p r).X i) (topOpen p r W x),
          s - ((relativeDeRhamInt p r).d i n).hom.app (op (topOpen p r W x)) t ∈
            (CycleQ2ThreeOpenSupportedCechExt.boundary (vertex p r W x 0) (vertex p r W x 1)
              (vertex p r W x 2) ((relativeDeRhamInt p r).X n)).range := by
  subst i
  subst j
  rfl

theorem exactOnOverlap_zero (x : Fin 3 → Γ(X,W.1)) (h : LowFormRows p r W x) :
    ExactOnOverlap p r W x 0 := by
  apply (exactOnOverlap_iff' p r W x (-1) 0 1 (by simp) (by simp)).mpr
  intro s hs
  refine ⟨0,?_⟩
  rw [map_zero,sub_zero,mem_boundary_iff]
  exact h.1 _ ((closed_mod_boundary_iff p r W x 0 s).mp hs)

theorem exactOnOverlap_one (x : Fin 3 → Γ(X,W.1)) (h : LowFormRows p r W x) :
    ExactOnOverlap p r W x 1 := by
  apply (exactOnOverlap_iff' p r W x 0 1 2 (by simp) (by simp)).mpr
  intro s hs
  exact (primitive_mod_boundary_iff p r W x 0 s).mpr
    (h.2.1 _ ((closed_mod_boundary_iff p r W x 1 s).mp hs))

theorem exactOnOverlap_two (x : Fin 3 → Γ(X,W.1)) (h : LowFormRows p r W x) :
    ExactOnOverlap p r W x 2 := by
  apply (exactOnOverlap_iff' p r W x 1 2 3 (by simp) (by simp)).mpr
  intro s hs
  exact (primitive_mod_boundary_iff p r W x 1 s).mpr
    (h.2.2 _ ((closed_mod_boundary_iff p r W x 2 s).mp hs))

local instance : HasDerivedCategory.{1} (AbSheaf (show TopCat from X)) := HasDerivedCategory.standard _

include hu hnormal in
/-- Three distinct exact coordinates kill supported degrees below six
once the actual augmented principal Čech rows are exact. The ordinary
form exactness is supplied by native_exact, not by an added premise. -/
theorem below_six (hrows : LowerRows p r W (equations p r W u normal))
    (n : ℤ) (hn : n < 6) :
    Subsingleton ((DerivedCategory.singleFunctor (AbSheaf (show TopCat from X)) 0).obj
      (supportedQuotient p r W (equations p r W u normal)) ⟶
        (DerivedCategory.Q.obj (relativeDeRhamInt p r))⟦n⟧) := by
  have h := native_exact p r W u normal hnormal hu
  exact CycleQ2ThreePrincipalChartSupportedVanishing.below_six p r W _ hrows
    (exactOnOverlap_zero p r W _ h) (exactOnOverlap_one p r W _ h)
    (exactOnOverlap_two p r W _ h) n hn

end CycleQ2AdaptedTripleChartPurity

#print axioms CycleQ2AdaptedTripleChartPurity.native_exact
#print axioms CycleQ2AdaptedTripleChartPurity.below_six

namespace CycleQ2ThreeOpenAugmentation

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf Sections)
open CycleQ2GeometricConeCech.HZero (sectionsEquiv sectionsEquiv_naturality)
open CycleQ2SupportedCechExt (overlapBoundary)
open CycleQ2ThreeOpenCechH2 (delta_eq_zero_iff delta_surjective delta_right_zero)

variable {X : TopCat.{0}}
local instance : HasExt.{1} (AbSheaf X) := HasExt.standard _
variable (F : AbSheaf X)

abbrev sectionRes {U V : Opens X} (h : U ≤ V) := F.obj.map (homOfLE h).op

theorem sectionRes_comp {U V W : Opens X} (h : U ≤ V) (j : V ≤ W) (s : Sections F W) :
    sectionRes F h (sectionRes F j s) = sectionRes F (h.trans j) s :=
  (ConcreteCategory.congr_hom (F.obj.map_comp (homOfLE j).op (homOfLE h).op) s).symm

variable (S : (Opens.grothendieckTopology X).MayerVietorisSquare)

/-- Ambient sections extend over a union if they extend over its left
open and sections on the right are detected on the intersection. -/
theorem sections_bijective {W : Opens X} (h : S.X₄ ≤ W)
    (hleft : Function.Bijective (sectionRes F (S.f₂₄.le.trans h)))
    (hright : Function.Injective (sectionRes F S.f₁₃.le)) :
    Function.Bijective (sectionRes F h) := by
  constructor
  · intro a b hab
    apply hleft.injective
    simpa only [sectionRes_comp] using congrArg (sectionRes F S.f₂₄.le) hab
  · intro s
    obtain ⟨a,ha⟩ := hleft.surjective (sectionRes F S.f₂₄.le s)
    have hb : sectionRes F (S.f₃₄.le.trans h) a = sectionRes F S.f₃₄.le s := by
      apply hright
      simpa only [sectionRes_comp] using congrArg (sectionRes F S.f₁₂.le) ha
    let P := (sheafCompose _ (forget AddCommGrpCat)).obj F
    have hc := S.sheafCondition_of_sheaf P
    refine ⟨a,hc.ext ?_ ?_⟩
    · simpa only [sectionRes_comp] using ha
    · simpa only [sectionRes_comp] using hb

/-- The first cohomology of a union vanishes when the right open has
zero H¹, its sections cover the intersection, and the left H¹ restricts
injectively to the intersection. -/
theorem H1_union_zero
    (h₃ : Subsingleton (F.H' 1 S.X₃))
    (h₀ : Function.Surjective (sectionRes F S.f₁₃.le))
    (h₁ : Function.Injective ((F.cohomologyPresheaf 1).map S.f₁₂.op)) :
    Subsingleton (F.H' 1 S.X₄) := by
  apply subsingleton_of_forall_eq 0
  intro y
  have hy₃ : (F.cohomologyPresheaf 1).map S.f₃₄.op y = 0 := h₃.elim _ _
  have hy₂ : (F.cohomologyPresheaf 1).map S.f₂₄.op y = 0 := by
    apply h₁
    rw [map_zero]
    calc
      _ = (F.cohomologyPresheaf 1).map S.f₁₃.op
          ((F.cohomologyPresheaf 1).map S.f₃₄.op y) := by
        erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
          ← (F.cohomologyPresheaf 1).map_comp, ← (F.cohomologyPresheaf 1).map_comp]
        rfl
      _ = 0 := by rw [hy₃,map_zero]
  have hz : S.toBiprod F 1 y = 0 := by
    rw [S.toBiprod_apply,hy₂,hy₃]
    exact map_zero _
  obtain ⟨z,hz⟩ := (ShortComplex.ab_exact_iff _).mp
    ((S.sequence_exact F 0 1 rfl).exact 2) y hz
  obtain ⟨a,ha⟩ := h₀ (sectionsEquiv F S.X₁ z)
  let b := (sectionsEquiv F S.X₃).symm a
  have hb : (F.cohomologyPresheaf 0).map S.f₁₃.op b = z := by
    apply (sectionsEquiv F S.X₁).injective
    rw [sectionsEquiv_naturality]
    simpa only [b,AddEquiv.apply_symm_apply] using ha
  rw [← hz, ← hb]
  exact delta_right_zero F S 0 1 rfl b

def sectionConnecting : Sections F S.X₁ →+ F.H' 1 S.X₄ :=
  (S.δ F 0 1 rfl).hom.comp (sectionsEquiv F S.X₁).symm.toAddMonoidHom

theorem sectionConnecting_surjective
    (h₂ : Subsingleton (F.H' 1 S.X₂)) (h₃ : Subsingleton (F.H' 1 S.X₃)) :
    Function.Surjective (sectionConnecting F S) := by
  letI := h₂
  letI := h₃
  exact (delta_surjective F S).comp (sectionsEquiv F S.X₁).symm.surjective

theorem sectionConnecting_eq_zero_iff (s : Sections F S.X₁) :
    sectionConnecting F S s = 0 ↔ s ∈ (overlapBoundary S F).range := by
  change S.δ F 0 1 rfl ((sectionsEquiv F S.X₁).symm s) = 0 ↔ _
  rw [delta_eq_zero_iff]
  constructor
  · rintro ⟨a,b,hab⟩
    refine ⟨(sectionsEquiv F S.X₂ a,sectionsEquiv F S.X₃ b),?_⟩
    have he := congrArg (sectionsEquiv F S.X₁) hab
    rw [map_sub, sectionsEquiv_naturality, sectionsEquiv_naturality,
      AddEquiv.apply_symm_apply] at he
    exact he
  · rintro ⟨⟨a,b⟩,hab⟩
    refine ⟨(sectionsEquiv F S.X₂).symm a,(sectionsEquiv F S.X₃).symm b,?_⟩
    apply (sectionsEquiv F S.X₁).injective
    rw [map_sub, sectionsEquiv_naturality, sectionsEquiv_naturality,
      AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    exact hab

theorem sectionConnecting_restrict {U V U' V' : Opens X} (hU : U' ≤ U) (hV : V' ≤ V)
    (s : Sections F (U ⊓ V)) :
    (F.cohomologyPresheaf 1).map (homOfLE (sup_le_sup hU hV)).op
      (sectionConnecting F (Opens.mayerVietorisSquare U V) s) =
    sectionConnecting F (Opens.mayerVietorisSquare U' V')
      (sectionRes F (inf_le_inf hU hV) s) := by
  change (F.cohomologyPresheaf 1).map (homOfLE (sup_le_sup hU hV)).op
    ((Opens.mayerVietorisSquare U V).δ F 0 1 rfl ((sectionsEquiv F (U ⊓ V)).symm s)) = _
  rw [CycleQ2MayerVietorisRestriction.delta_restriction]
  congr 1
  apply (sectionsEquiv F (U' ⊓ V')).injective
  rw [sectionsEquiv_naturality, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- Actual boundary descent on the two pair covers gives injectivity
on the original H¹ restriction. This is where third-coordinate
saturation enters the augmented three-open Čech calculation. -/
theorem H1_refinement_injective (U V T : Opens X)
    (hU : Subsingleton (F.H' 1 U)) (hV : Subsingleton (F.H' 1 V))
    (hdesc : ∀ s : Sections F (U ⊓ V),
      sectionRes F (inf_le_inf (inf_le_left : U ⊓ T ≤ U) (inf_le_left : V ⊓ T ≤ V)) s ∈
        (overlapBoundary (Opens.mayerVietorisSquare (U ⊓ T) (V ⊓ T)) F).range →
      s ∈ (overlapBoundary (Opens.mayerVietorisSquare U V) F).range) :
    Function.Injective ((F.cohomologyPresheaf 1).map
      (homOfLE (sup_le_sup (inf_le_left : U ⊓ T ≤ U) (inf_le_left : V ⊓ T ≤ V))).op) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro y hy
  obtain ⟨s,rfl⟩ := sectionConnecting_surjective F (Opens.mayerVietorisSquare U V) hU hV y
  rw [sectionConnecting_restrict] at hy
  exact (sectionConnecting_eq_zero_iff F _ s).mpr
    (hdesc s ((sectionConnecting_eq_zero_iff F _ _).mp hy))

end CycleQ2ThreeOpenAugmentation

#print axioms CycleQ2ThreeOpenAugmentation.H1_refinement_injective
#print axioms CycleQ2ThreeOpenAugmentation.H1_union_zero

namespace CycleQ2AdaptedTripleChartLowerRows

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Module KaehlerDifferential
open CycleQ2IntrinsicFramedAffineSite (FramedOpen)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRham relativeDeRhamInt)
open CycleQ2FramedCechFormRow (singleOpen intersection first second ordinary pull coordinates
  coordinates_restrict term eq_on_localization regular_augmentedRows)
open CycleQ2RelativeAffineOverlap (restrict)
open CycleQ2FramedAffineSite (restrict_comp)
open CycleQ2CechDenominatorTorsion (fromFirst fromSecond)
open CycleQ2ThreeOpenAugmentation (sectionRes)
open CycleQ2InjectiveCech (AbSheaf Sections freeOpenSections)
open CycleQ2SupportedCechExt (overlapBoundary)

variable {k : Type} [Field k] [CharZero k] {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) (r : ℕ) [SmoothOfRelativeDimension r p]
  (W : FramedOpen p r) [IsNoetherianRing Γ(X,W.1)]
  (u : Fin r → Γ(X,W.1))
  (hu : letI := (sectionCoefficients p W.1).toAlgebra;
    ∃ b : Basis (Fin r) Γ(X,W.1) Ω[Γ(X,W.1)⁄k], ∀ i, b i = D k Γ(X,W.1) (u i))

local instance : HasExt.{1} (AbSheaf (show TopCat from X)) := HasExt.standard _

include hu in
/-- Sections of every actual de Rham term extend uniquely over the
complement of two distinct coordinates of the original exact frame. -/
theorem pair_sections_bijective (i j : Fin r) (hij : i ≠ j) (m : ℤ) :
    Function.Bijective (sectionRes ((relativeDeRhamInt p r).X m)
      (CycleQ2LocalPrincipalGysin.union_le (u i) (u j))) := by
  letI : Algebra k Γ(X,W.1) := (sectionCoefficients p W.1).toAlgebra
  obtain ⟨b,hb⟩ := hu
  obtain ⟨hf,hg⟩ := CycleQ2NormalExteriorCech.exact_frame_regular b u hb i j hij
  have hr := regular_augmentedRows p r W (u i) (u j) hf hg
  exact CycleQ2SupportedCechLower.restriction_bijective
    (CycleQ2LocalPrincipalGysin.cover (u i) (u j))
    (CycleQ2LocalPrincipalGysin.union_le (u i) (u j)) _ (hr.1 m) (hr.2 m)

include hu in
/-- The same section extension holds on the actual third principal
open. The frame and the two equations are pulled back through its
original scheme restriction, and Noetherianity is preserved by that
localization. -/
theorem pair_sections_bijective_after_localizing
    (i j l : Fin r) (hij : i ≠ j) (m : ℤ) :
    Function.Bijective (sectionRes ((relativeDeRhamInt p r).X m)
      (show (X.basicOpen (u i) ⊔ X.basicOpen (u j)) ⊓ X.basicOpen (u l) ≤
        X.basicOpen (u l) from inf_le_right)) := by
  let H := singleOpen p r W (u l)
  let R := Γ(X,W.1)
  let A := Γ(X,H.1)
  let hH : H.1 ≤ W.1 := X.basicOpen_le (u l)
  letI : Algebra k R := (sectionCoefficients p W.1).toAlgebra
  letI : Algebra k A := (sectionCoefficients p H.1).toAlgebra
  letI : Algebra R A := (restrict p hH).toRingHom.toAlgebra
  letI : IsScalarTower k R A := IsScalarTower.of_algHom (restrict p hH)
  letI : IsLocalization.Away (u l) A :=
    W.2.1.isLocalization_of_eq_basicOpen (u l) (homOfLE hH) rfl
  letI : IsNoetherianRing A :=
    IsLocalization.isNoetherianRing (.powers (u l)) A (inferInstance : IsNoetherianRing R)
  obtain ⟨b,hb⟩ := hu
  let v : Fin r → A := fun a => restrict p hH (u a)
  have hv : ∃ c : Basis (Fin r) A Ω[A⁄k], ∀ a, c a = D k A (v a) := by
    refine ⟨CycleQ2NormalCechKahler.localFrame (T := A) b (.powers (u l)),?_⟩
    intro a
    exact CycleQ2NormalCechFormBoundary.frame_exact b u hb (.powers (u l)) a
  have he : X.basicOpen (v i) ⊔ X.basicOpen (v j) =
      (X.basicOpen (u i) ⊔ X.basicOpen (u j)) ⊓ X.basicOpen (u l) := by
    change X.basicOpen ((X.presheaf.map (homOfLE hH).op) (u i)) ⊔
      X.basicOpen ((X.presheaf.map (homOfLE hH).op) (u j)) = _
    rw [X.basicOpen_res,X.basicOpen_res,← inf_sup_left,inf_comm]
  have hr := pair_sections_bijective p r H v hv i j hij m
  change Function.Bijective (((relativeDeRhamInt p r).X m).obj.map
    (homOfLE (CycleQ2LocalPrincipalGysin.union_le (v i) (v j))).op) at hr
  simpa only [he] using hr

include hu in
/-- A boundary after restricting to the third principal open was
already a boundary on the original two-open cover. This theorem uses
the ordinary-form saturation calculation with the actual six section
rings and their original restriction maps. -/
theorem boundary_descent_nat (normal : Fin 3 → Fin r)
    (h02 : normal 0 ≠ normal 2) (h12 : normal 1 ≠ normal 2) (q : ℕ)
    (s : Sections (term p r q) (X.basicOpen (u (normal 0)) ⊓ X.basicOpen (u (normal 1))))
    (hs : sectionRes (term p r q)
      (inf_le_inf (inf_le_left : X.basicOpen (u (normal 0)) ⊓ X.basicOpen (u (normal 2)) ≤ _)
        (inf_le_left : X.basicOpen (u (normal 1)) ⊓ X.basicOpen (u (normal 2)) ≤ _)) s ∈
      (overlapBoundary (Opens.mayerVietorisSquare
        (X.basicOpen (u (normal 0)) ⊓ X.basicOpen (u (normal 2)))
        (X.basicOpen (u (normal 1)) ⊓ X.basicOpen (u (normal 2)))) (term p r q)).range) :
    s ∈ (overlapBoundary (Opens.mayerVietorisSquare
      (X.basicOpen (u (normal 0))) (X.basicOpen (u (normal 1)))) (term p r q)).range := by
  let f := u (normal 0)
  let g := u (normal 1)
  let h := u (normal 2)
  let A₀ := intersection p r W f g
  let P₀ := intersection p r W f h
  let Q₀ := intersection p r W g h
  let Z₀ := CycleQ2FramedTripleCechFormRow.top p r W (u ∘ normal)
  let U₀ := singleOpen p r W f
  let V₀ := singleOpen p r W g
  let R := Γ(X,W.1)
  let U := Γ(X,U₀.1)
  let V := Γ(X,V₀.1)
  let A := Γ(X,A₀.1)
  let P := Γ(X,P₀.1)
  let Q := Γ(X,Q₀.1)
  let Z := Γ(X,Z₀.1)
  let hU : U₀.1 ≤ W.1 := X.basicOpen_le f
  let hV : V₀.1 ≤ W.1 := X.basicOpen_le g
  let hA : A₀.1 ≤ W.1 := inf_le_left.trans hU
  let hP : P₀.1 ≤ W.1 := inf_le_left.trans hU
  let hQ : Q₀.1 ≤ W.1 := inf_le_left.trans hV
  let hZ : Z₀.1 ≤ W.1 := CycleQ2FramedTripleCechFormRow.top_le p r W (u ∘ normal)
  let aZA : Z₀ ⟶ A₀ := homOfLE (inf_le_inf inf_le_left inf_le_left)
  let aZP : Z₀ ⟶ P₀ := homOfLE inf_le_left
  let aZQ : Z₀ ⟶ Q₀ := homOfLE inf_le_right
  letI : Algebra k R := (sectionCoefficients p W.1).toAlgebra
  letI : Algebra k U := (sectionCoefficients p U₀.1).toAlgebra
  letI : Algebra k V := (sectionCoefficients p V₀.1).toAlgebra
  letI : Algebra k A := (sectionCoefficients p A₀.1).toAlgebra
  letI : Algebra k P := (sectionCoefficients p P₀.1).toAlgebra
  letI : Algebra k Q := (sectionCoefficients p Q₀.1).toAlgebra
  letI : Algebra k Z := (sectionCoefficients p Z₀.1).toAlgebra
  letI : Algebra R U := (restrict p hU).toRingHom.toAlgebra
  letI : Algebra R V := (restrict p hV).toRingHom.toAlgebra
  letI : Algebra R A := (restrict p hA).toRingHom.toAlgebra
  letI : Algebra R P := (restrict p hP).toRingHom.toAlgebra
  letI : Algebra R Q := (restrict p hQ).toRingHom.toAlgebra
  letI : Algebra R Z := (restrict p hZ).toRingHom.toAlgebra
  letI : IsScalarTower k R U := IsScalarTower.of_algHom (restrict p hU)
  letI : IsScalarTower k R V := IsScalarTower.of_algHom (restrict p hV)
  letI : IsScalarTower k R A := IsScalarTower.of_algHom (restrict p hA)
  letI : IsScalarTower k R P := IsScalarTower.of_algHom (restrict p hP)
  letI : IsScalarTower k R Q := IsScalarTower.of_algHom (restrict p hQ)
  letI : IsScalarTower k R Z := IsScalarTower.of_algHom (restrict p hZ)
  letI : IsLocalization.Away f U := W.2.1.isLocalization_of_eq_basicOpen f (homOfLE hU) rfl
  letI : IsLocalization.Away g V := W.2.1.isLocalization_of_eq_basicOpen g (homOfLE hV) rfl
  letI : IsLocalization.Away (f*g) A :=
    W.2.1.isLocalization_of_eq_basicOpen (f*g) (homOfLE hA) (X.basicOpen_mul f g).symm
  letI : IsLocalization.Away (f*h) P :=
    W.2.1.isLocalization_of_eq_basicOpen (f*h) (homOfLE hP) (X.basicOpen_mul f h).symm
  letI : IsLocalization.Away (g*h) Q :=
    W.2.1.isLocalization_of_eq_basicOpen (g*h) (homOfLE hQ) (X.basicOpen_mul g h).symm
  letI : IsLocalization.Away ((f*g)*h) Z :=
    W.2.1.isLocalization_of_eq_basicOpen ((f*g)*h) (homOfLE hZ) (by
      change (X.basicOpen f ⊓ X.basicOpen h) ⊓ (X.basicOpen g ⊓ X.basicOpen h) = _
      simp only [X.basicOpen_mul,inf_assoc,inf_left_comm,inf_comm,inf_idem])
  let α : A →ₐ[R] Z :=
    { toRingHom := (restrict p aZA.le).toRingHom
      commutes' := fun a => (AlgHom.congr_fun (restrict_comp p hA aZA.le) a).symm }
  let β : P →ₐ[R] Z :=
    { toRingHom := (restrict p aZP.le).toRingHom
      commutes' := fun a => (AlgHom.congr_fun (restrict_comp p hP aZP.le) a).symm }
  let γ : Q →ₐ[R] Z :=
    { toRingHom := (restrict p aZQ.le).toRingHom
      commutes' := fun a => (AlgHom.congr_fun (restrict_comp p hQ aZQ.le) a).symm }
  have hfirst : restrict p (first p r W f g).le =
      (fromFirst (A := U) (T := A) f g).restrictScalars k :=
    eq_on_localization f _ _ (fun a =>
      (AlgHom.congr_fun (restrict_comp p hU (first p r W f g).le) a).symm)
  have hsecond : restrict p (second p r W f g).le =
      (fromSecond (B := V) (T := A) f g).restrictScalars k :=
    eq_on_localization g _ _ (fun a =>
      (AlgHom.congr_fun (restrict_comp p hV (second p r W f g).le) a).symm)
  obtain ⟨⟨a,c⟩,hac⟩ := hs
  have he : pull p r aZA q (coordinates p r A₀ q s) =
      pull p r aZP q (coordinates p r P₀ q a) -
        pull p r aZQ q (coordinates p r Q₀ q c) := by
    rw [← coordinates_restrict,← coordinates_restrict,← coordinates_restrict,← map_sub]
    exact congrArg (coordinates p r Z₀ q) hac.symm
  obtain ⟨b,hb⟩ := hu
  have hd := CycleQ2ExactFrameThirdCoordinate.forms_boundary_of_refinement
    (U := U) (V := V) b u hb (normal 0) (normal 1) (normal 2) h02 h12 α β γ q
    (coordinates p r A₀ q s) (coordinates p r P₀ q a) (-coordinates p r Q₀ q c) (by
      change pull p r aZA q _ = pull p r aZP q _ + pull p r aZQ q (-_)
      rw [map_neg,← sub_eq_add_neg]
      exact he)
  rw [← hfirst,← hsecond] at hd
  obtain ⟨a',c',hac'⟩ := hd
  exact (CycleQ2FramedCechFormRow.mem_boundary_iff p r W f g q s).mpr ⟨a',c',hac'.symm⟩

include hu in
theorem boundary_descent (normal : Fin 3 → Fin r)
    (h02 : normal 0 ≠ normal 2) (h12 : normal 1 ≠ normal 2) (m : ℤ)
    (s : Sections ((relativeDeRhamInt p r).X m)
      (X.basicOpen (u (normal 0)) ⊓ X.basicOpen (u (normal 1))))
    (hs : sectionRes ((relativeDeRhamInt p r).X m)
      (inf_le_inf (inf_le_left : X.basicOpen (u (normal 0)) ⊓ X.basicOpen (u (normal 2)) ≤ _)
        (inf_le_left : X.basicOpen (u (normal 1)) ⊓ X.basicOpen (u (normal 2)) ≤ _)) s ∈
      (overlapBoundary (Opens.mayerVietorisSquare
        (X.basicOpen (u (normal 0)) ⊓ X.basicOpen (u (normal 2)))
        (X.basicOpen (u (normal 1)) ⊓ X.basicOpen (u (normal 2))))
          ((relativeDeRhamInt p r).X m)).range) :
    s ∈ (overlapBoundary (Opens.mayerVietorisSquare
      (X.basicOpen (u (normal 0))) (X.basicOpen (u (normal 1))))
        ((relativeDeRhamInt p r).X m)).range := by
  cases m with
  | ofNat q => exact boundary_descent_nat p r W u hu normal h02 h12 q s hs
  | negSucc q =>
    have hz : IsZero ((relativeDeRhamInt p r).X (.negSucc q)) :=
      (relativeDeRham p r).isZero_extend_X (ComplexShape.embeddingUpIntGE 0) _
        (by intro n h; change (0:ℤ)+n=Int.negSucc q at h; omega)
    have hzero : s = 0 := (freeOpenSections _ _).symm.injective (hz.eq_of_tgt _ _)
    rw [hzero]
    exact AddSubgroup.zero_mem _

include hu in
/-- All three lower supported Čech rows vanish for the original three
coordinate opens. No cohomology of their union is assumed: its H¹
vanishing follows from the proved saturation and the actual outer
Mayer–Vietoris sequence. -/
theorem native_lowerRows (normal : Fin 3 → Fin r) (hnormal : Function.Injective normal) :
    CycleQ2ThreePrincipalChartSupportedVanishing.LowerRows p r W (u ∘ normal) := by
  let U := X.basicOpen (u (normal 0))
  let V := X.basicOpen (u (normal 1))
  let T := X.basicOpen (u (normal 2))
  let S := Opens.mayerVietorisSquare (U ⊔ V) T
  have h01 : normal 0 ≠ normal 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (hnormal h)
  have h02 : normal 0 ≠ normal 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (hnormal h)
  have h12 : normal 1 ≠ normal 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (hnormal h)
  have he : (U ⊓ T) ⊔ (V ⊓ T) = (U ⊔ V) ⊓ T := by
    rw [inf_comm U T,inf_comm V T,← inf_sup_left,inf_comm]
  intro m
  let F := (relativeDeRhamInt p r).X m
  have hleft := pair_sections_bijective p r W u hu (normal 0) (normal 1) h01 m
  have hright := pair_sections_bijective_after_localizing p r W u hu
    (normal 0) (normal 1) (normal 2) h01 m
  have hU : Subsingleton (F.H' 1 U) :=
    CycleQ2FramedOpenFormCoefficients.term_acyclic p r (singleOpen p r W (u (normal 0))) m 0
  have hV : Subsingleton (F.H' 1 V) :=
    CycleQ2FramedOpenFormCoefficients.term_acyclic p r (singleOpen p r W (u (normal 1))) m 0
  have hT : Subsingleton (F.H' 1 T) :=
    CycleQ2FramedOpenFormCoefficients.term_acyclic p r (singleOpen p r W (u (normal 2))) m 0
  have hres : Function.Injective ((F.cohomologyPresheaf 1).map S.f₁₂.op) := by
    have hr := CycleQ2ThreeOpenAugmentation.H1_refinement_injective F U V T hU hV
      (fun s hs => boundary_descent p r W u hu normal h02 h12 m s hs)
    simpa only [he] using hr
  exact ⟨CycleQ2ThreeOpenAugmentation.sections_bijective F S
      (CycleQ2FramedTripleCechFormRow.union_le p r W (u ∘ normal)) hleft hright.injective,
    CycleQ2ThreeOpenAugmentation.H1_union_zero F S hT hright.surjective hres⟩

end CycleQ2AdaptedTripleChartLowerRows

namespace CycleQ2AdaptedTripleChartPurity

open AlgebraicGeometry CategoryTheory Module KaehlerDifferential
open CycleQ2IntrinsicFramedAffineSite (FramedOpen)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRhamInt)
open CycleQ2FramedTripleCechFormRow (supportedQuotient)
open CycleQ2InjectiveCech (AbSheaf)

variable {k : Type} [Field k] [CharZero k] [Algebra ℂ k] {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) (r : ℕ) [SmoothOfRelativeDimension r p]
  (W : FramedOpen p r) [IsNoetherianRing Γ(X,W.1)] (u : Fin r → Γ(X,W.1))
  (normal : Fin 3 → Fin r) (hnormal : Function.Injective normal)
  (hu : letI := (sectionCoefficients p W.1).toAlgebra;
    ∃ b : Basis (Fin r) Γ(X,W.1) Ω[Γ(X,W.1)⁄k], ∀ i, b i = D k Γ(X,W.1) (u i))

local instance : HasDerivedCategory.{1} (AbSheaf (show TopCat from X)) := HasDerivedCategory.standard _

include hnormal hu in
/-- Three distinct exact coordinates on a Noetherian smooth affine
chart give actual supported de Rham vanishing below degree six. Both
the augmented Čech rows and the low ordinary-form rows are proved for
the original opens and restrictions. -/
theorem below_six_of_exact_coordinates (n : ℤ) (hn : n < 6) :
    Subsingleton ((DerivedCategory.singleFunctor (AbSheaf (show TopCat from X)) 0).obj
      (supportedQuotient p r W (equations p r W u normal)) ⟶
        (DerivedCategory.Q.obj (relativeDeRhamInt p r))⟦n⟧) :=
  below_six p r W u normal hnormal hu
    (CycleQ2AdaptedTripleChartLowerRows.native_lowerRows p r W u hu normal hnormal) n hn

end CycleQ2AdaptedTripleChartPurity

#print axioms CycleQ2AdaptedTripleChartLowerRows.native_lowerRows
#print axioms CycleQ2AdaptedTripleChartPurity.below_six_of_exact_coordinates
