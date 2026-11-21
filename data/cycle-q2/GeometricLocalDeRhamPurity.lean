import Proposal.GeometricMonicGenericSupport
import Proposal.GeometricSupportedCechRows
import Proposal.GeometricPrincipalPartsDifferentials
import Proposal.GeometricSupportedHypercohomology
import Proposal.GeometricFramedAffineAcyclicity

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
