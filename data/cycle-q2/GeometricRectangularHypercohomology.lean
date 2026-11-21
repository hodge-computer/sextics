import Proposal.GeometricAffineExteriorAcyclicity
import Proposal.GeometricSupportedHypercohomology
import Proposal.GeometricSupportedMayerVietorisDescent

/-! The ordinary two-chart de Rham restriction cone computes the derived classes on the full proper-curve product above an affine target open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/

noncomputable section

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
open CochainComplex HomComplex
namespace CycleQ2RectangularTrace

section Sections
open Pretriangulated
variable {A : Type u} [Category.{v} A] [Abelian A]
  (S : ShortComplex A) (K : CochainComplex A ℤ)

open CycleQ2AffineHypercohomologyComparison (sectionComplex)
abbrev secs (P : A) := (sectionComplex P).obj K
def res {P R : A} (f : P ⟶ R) : secs K R ⟶ secs K P where
  f j := (preadditiveCoyoneda.map f.op).app (K.X j)
  comm' i j _ := ((preadditiveCoyoneda.map f.op).naturality (K.d i j)).symm

def pair : ShortComplex (CochainComplex AddCommGrpCat.{v} ℤ) :=
  ShortComplex.mk (res K S.g) (res K S.f) (by
    ext j a
    let b : S.X₃ ⟶ K.X j := a
    change S.f ≫ S.g ≫ b = (0 : S.X₁ ⟶ K.X j)
    exact (Category.assoc S.f S.g b).symm.trans
      ((congrArg (fun u : S.X₁ ⟶ S.X₃ => u ≫ b) S.zero).trans (CategoryTheory.Limits.zero_comp (f := b))))

theorem pair_exact (I : CochainComplex A ℤ) [∀ i, Injective (I.X i)] (hs : S.ShortExact) :
    (pair S I).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro j
  let := hs.mono_f
  let := hs.epi_g
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.ab_exact_iff _).2
    intro y hy
    exact hs.exact.desc' y hy
  · apply (AddCommGrpCat.mono_iff_injective _).2
    intro x y h
    exact (cancel_epi S.g).mp h
  · apply (AddCommGrpCat.epi_iff_surjective _).2
    intro x
    exact ⟨Injective.factorThru x S.f,Injective.comp_factorThru x S.f⟩

abbrev rectangleCone := mappingCone (pair S K).g

variable [HasDerivedCategory.{w} AddCommGrpCat.{v}]
variable {K} {I : CochainComplex A ℤ} (ρ : K ⟶ I)

private def coneMapIso {M N M' N' : CochainComplex AddCommGrpCat.{v} ℤ}
    (d : M ⟶ N) (d' : M' ⟶ N') (a : M ⟶ M') (b : N ⟶ N')
    (h : d ≫ b = a ≫ d') (ha : QuasiIso a) (hb : QuasiIso b) :
    DerivedCategory.Q.obj (mappingCone d) ≅ DerivedCategory.Q.obj (mappingCone d') := by
  letI : QuasiIso a := ha
  letI : QuasiIso b := hb
  let D := DerivedCategory.Q (C := AddCommGrpCat.{v})
  let t := D.mapTriangle.map (mappingCone.triangleMap d d' a b h)
  have hdist {P R : CochainComplex AddCommGrpCat.{v} ℤ} (g : P ⟶ R) :
      D.mapTriangle.obj (mappingCone.triangle g) ∈ distTriang _ :=
    (DerivedCategory.mem_distTriang_iff _).2 ⟨_,_,_,⟨Iso.refl _⟩⟩
  have ia : IsIso t.hom₁ := inferInstanceAs (IsIso (D.map a))
  have ib : IsIso t.hom₂ := inferInstanceAs (IsIso (D.map b))
  have ht : IsIso t.hom₃ := isIso₃_of_isIso₁₂ t (hdist d) (hdist d') ia ib
  exact @asIso _ _ _ _ t.hom₃ ht

/-- The ordinary two-open restriction difference computes hypercohomology
on the union whenever the resolution induces quasi-isomorphisms on each
chart row. The maps are the two explicit cone maps and the standard rotation. -/
def ordinaryConeIso (hs : S.ShortExact) [∀ i, Injective (I.X i)]
    [h₁ : QuasiIso ((sectionComplex S.X₁).map ρ)] [h₂ : QuasiIso ((sectionComplex S.X₂).map ρ)] :
    DerivedCategory.Q.obj (rectangleCone S K) ≅
      (DerivedCategory.Q.obj (secs I S.X₃))⟦(1:ℤ)⟧ := by
  let R := pair S I
  have hρ : (pair S K).g ≫ (sectionComplex S.X₁).map ρ = (sectionComplex S.X₂).map ρ ≫ R.g := by
    ext n x
    exact Category.assoc S.f x (ρ.f n)
  let a := coneMapIso (pair S K).g R.g ((sectionComplex S.X₂).map ρ) ((sectionComplex S.X₁).map ρ) hρ h₂ h₁
  have hd : QuasiIso (mappingCone.descShortComplex R) :=
    mappingCone.quasiIso_descShortComplex (pair_exact S I hs)
  let b := coneMapIso (mappingCone.inr R.f) R.g (𝟙 _) (mappingCone.descShortComplex R)
    (by simp) (inferInstanceAs (QuasiIso (𝟙 _))) hd
  let e := mappingCone.rotateHomotopyEquiv R.f
  let c := asIso (DerivedCategory.Q.map e.hom)
  exact a ≪≫ b.symm ≪≫ c.symm ≪≫ (DerivedCategory.Q.commShiftIso (1:ℤ)).app R.X₁

end Sections



open AlgebraicGeometry TopologicalSpace
open CycleQ2LaurentProjectiveLine (line)
open CycleQ2ProjectiveLineStructure (structureMap)
open CycleQ2ProductAffineOpen (productOpen isAffineOpen_product)
open CycleQ2GenericSmoothCurveGraph
variable {k : Type} [Field k] {C X : Scheme.{0}} [IsIntegral C]
  (f : C ⟶ line k) (t : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens)
local notation "c" => f ≫ structureMap k

abbrev leftOpen := productOpen c t (CycleQ2FiniteCurveCover.zero k f) U
abbrev rightOpen := productOpen c t (CycleQ2FiniteCurveCover.infinity k f) U
abbrev midOpen := productOpen c t (CycleQ2FiniteCurveCover.torus k f) U
abbrev baseOpen := (pullback.snd c t) ⁻¹ᵁ U

theorem intersection : midOpen f t U = leftOpen f t U ⊓ rightOpen f t U := by
  rw [leftOpen, rightOpen, CycleQ2ProductCechCover.productOpen_inf,
    ← CycleQ2FiniteCurveCover.overlap_eq, inf_idem]

theorem union : leftOpen f t U ⊔ rightOpen f t U = baseOpen f t U := by
  ext x
  have h : pullback.fst c t x ∈ CycleQ2FiniteCurveCover.zero k f ⊔ CycleQ2FiniteCurveCover.infinity k f := by
    rw [CycleQ2FiniteCurveCover.cover_eq]
    trivial
  change ((_ ∈ _ ∧ _ ∈ _) ∨ (_ ∈ _ ∧ _ ∈ _)) ↔ _
  change _ ∨ _ at h
  tauto

def rectangle := Opens.mayerVietorisSquare'
    { X₁ := midOpen f t U
      X₂ := leftOpen f t U
      X₃ := rightOpen f t U
      X₄ := baseOpen f t U
      f₁₂ := homOfLE ((intersection f t U).le.trans inf_le_left)
      f₁₃ := homOfLE ((intersection f t U).le.trans inf_le_right)
      f₂₄ := homOfLE (le_sup_left.trans (union f t U).le)
      f₃₄ := homOfLE (le_sup_right.trans (union f t U).le)
      fac := Subsingleton.elim _ _ }
    (union f t U).symm (intersection f t U)

theorem affine_rows [IsFinite f] (hU : IsAffineOpen U) :
    IsAffineOpen (leftOpen f t U) ∧ IsAffineOpen (rightOpen f t U) ∧ IsAffineOpen (midOpen f t U) :=
  ⟨isAffineOpen_product c t (CycleQ2FiniteCurveCover.zero_affine k f) hU,
   isAffineOpen_product c t (CycleQ2FiniteCurveCover.infinity_affine k f) hU,
   isAffineOpen_product c t (CycleQ2FiniteCurveCover.torus_affine k f) hU⟩

end CycleQ2RectangularTrace

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite HomologicalComplex
open CochainComplex
namespace CycleQ2RectangularTrace

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [HasExt.{w} A] [EnoughInjectives A] (S : ShortComplex A) (hs : S.ShortExact)
  (K : CochainComplex A ℤ)
open CycleQ2AcyclicComplexSections (AcyclicFor)
open CycleQ2AffineHypercohomologyComparison (sectionComplex sections_quasiIso)

def ordinaryClasses (b n : ℤ) [K.IsStrictlyGE b]
    (h₁ : ∀ i, AcyclicFor S.X₁ (K.X i)) (h₂ : ∀ i, AcyclicFor S.X₂ (K.X i)) :
    (rectangleCone S K).homology (n-1) ≃+
      ((DerivedCategory.singleFunctor A 0).obj S.X₃ ⟶ (DerivedCategory.Q.obj K)⟦n⟧) := by
  apply Classical.choice
  let := HasDerivedCategory.standard AddCommGrpCat.{v}
  obtain ⟨I,f,hm,hq,hI,hBI,h₁'⟩ :=
    CycleQ2AffineHypercohomologyComparison.exists_injective_sections_resolution S.X₁ K b h₁
  let : Mono f := hm
  let : QuasiIso f := hq
  let : I.IsStrictlyGE (b-1) := hBI
  let : ∀ i, Injective (I.X i) := hI
  let : I.IsKInjective := CochainComplex.isKInjective_of_injective I (b-1)
  have ha (P : A) (i : ℤ) : AcyclicFor P (I.X i) := fun m => Ext.subsingleton_of_injective P _ m
  let : QuasiIso ((sectionComplex S.X₁).map f) := h₁'
  let : QuasiIso ((sectionComplex S.X₂).map f) := sections_quasiIso _ f (b-1) h₂ (ha _)
  let e := ordinaryConeIso S f hs
  let h := (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v} (n-1)).symm.app (rectangleCone S K) ≪≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{v} (n-1)).mapIso e ≪≫
    (((DerivedCategory.homologyFunctor AddCommGrpCat.{v} 0).shiftIso (1:ℤ) (n-1) n (by omega)).app
      (DerivedCategory.Q.obj (secs I S.X₃))) ≪≫
    (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v} n).app (secs I S.X₃)
  let d := CycleQ2KInjectiveSections.derivedSectionsEquiv S.X₃ I n
  let z := (CategoryTheory.shiftFunctor (DerivedCategory A) n).mapIso ((asIso (DerivedCategory.Q.map f)).symm)
  have z' : ((DerivedCategory.singleFunctor A 0).obj S.X₃ ⟶ (DerivedCategory.Q.obj I)⟦n⟧) ≃+
      ((DerivedCategory.singleFunctor A 0).obj S.X₃ ⟶ (DerivedCategory.Q.obj K)⟦n⟧) :=
    { Iso.homCongr (Iso.refl _) z with map_add' x y := by simp [Iso.homCongr] }
  exact ⟨(h.addCommGroupIsoToAddEquiv.trans d).trans z'⟩
end CycleQ2RectangularTrace

namespace CycleQ2RectangularTrace
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open HomologicalComplex CochainComplex
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRham relativeDeRhamInt)
open CycleQ2InjectiveCech (AbSheaf freeOpen)
open CycleQ2LaurentProjectiveLine (line)
open CycleQ2ProjectiveLineStructure (structureMap)
open CycleQ2ProductCoefficients (productBase)
open CycleQ2AffineExteriorComparison (term_acyclic)
attribute [local instance] HasDerivedCategory.standard HasExt.standard

private theorem acyclic_biprod {A : Type*} [Category A] [Abelian A] [HasExt.{w} A]
    {L R M : A} (hL : CycleQ2AcyclicComplexSections.AcyclicFor L M)
    (hR : CycleQ2AcyclicComplexSections.AcyclicFor R M) : CycleQ2AcyclicComplexSections.AcyclicFor (L ⊞ R) M := by
  intro n
  let := hL n
  let := hR n
  exact (Ext.biprodAddEquiv (X₁ := L) (X₂ := R) (Y := M) (n := n+1)).injective.subsingleton

private theorem deRham_bounded {k : Type} [Field k] [CharZero k] {Y : Scheme.{0}}
    (p : Y ⟶ Spec (CommRingCat.of k)) (r : ℕ) [SmoothOfRelativeDimension r p] :
    (relativeDeRhamInt p r).IsStrictlyGE 0 := by
  apply ((relativeDeRhamInt p r).isStrictlyGE_iff 0).2
  intro i hi
  exact (relativeDeRham p r).isZero_extend_X (ComplexShape.embeddingUpIntGE 0) i
    (by intro a ha; change (0:ℤ) + a = i at ha; omega)

variable {k : Type} [Field k] [CharZero k] {C X Y : Scheme.{0}} [IsIntegral C]
  (f : C ⟶ line k) (t : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens)
  (i : Y ⟶ pullback (f ≫ structureMap k) t) (p : Y ⟶ Spec (CommRingCat.of k)) (r : ℕ)
  [IsFinite f] [IsAffineHom i] [SmoothOfRelativeDimension r p]

/-- The two rectangles inside the chosen model of the product, using the
given map to the categorical pullback. -/
def sourceRectangle := Opens.mayerVietorisSquare'
    ((rectangle f t U).toSquare.map (Opens.map i.base))
    (show i ⁻¹ᵁ baseOpen f t U = i ⁻¹ᵁ leftOpen f t U ⊔ i ⁻¹ᵁ rightOpen f t U from
      congrArg (fun W => i ⁻¹ᵁ W) (union f t U).symm)
    (show i ⁻¹ᵁ midOpen f t U = i ⁻¹ᵁ leftOpen f t U ⊓ i ⁻¹ᵁ rightOpen f t U from
      congrArg (fun W => i ⁻¹ᵁ W) (intersection f t U))

abbrev affineCurveCech := rectangleCone (sourceRectangle f t U i).shortComplex (relativeDeRhamInt p r)

/-- On the actual rectangles over any affine target open, the finite curve
cover computes every derived class by the ordinary Čech cone. -/
def affineRectangleClasses (hU : IsAffineOpen U) (n : ℤ) :
    (affineCurveCech f t U i p r).homology (n-1) ≃+
      ((DerivedCategory.singleFunctor (AbSheaf (show TopCat from Y)) 0).obj
        (freeOpen (i ⁻¹ᵁ baseOpen f t U)) ⟶ (DerivedCategory.Q.obj (relativeDeRhamInt p r))⟦n⟧) := by
  let S := sourceRectangle f t U i
  let K := relativeDeRhamInt p r
  letI : EnoughInjectives (AbSheaf (show TopCat from Y)) := by
    change EnoughInjectives (TopCat.Sheaf AddCommGrpCat.{0} Y)
    infer_instance
  obtain ⟨hl,hr,hm⟩ := affine_rows f t U hU
  apply @ordinaryClasses _ _ _ _ _ _ S.shortComplex S.shortComplex_shortExact K 0 n (deRham_bounded p r)
  · intro j a
    exact term_acyclic p r (hm.preimage i) j a
  · intro j
    exact acyclic_biprod (term_acyclic p r (hl.preimage i) j) (term_acyclic p r (hr.preimage i) j)

private abbrev sing (Y : Scheme.{0}) := DerivedCategory.singleFunctor (AbSheaf (show TopCat from Y)) 0

/-- The ordinary degree-four class underlying a supported class on the whole
product, restricted to the affine target open and expressed in the Čech cone. -/
def supportedRepresentative (hU : IsAffineOpen U) (D : Y.Opens)
    (z : (sing Y).obj (CycleQ2SupportMV.M D ⊤) ⟶ (DerivedCategory.Q.obj (relativeDeRhamInt p r))⟦(4:ℤ)⟧) :
    (affineCurveCech f t U i p r).homology 3 :=
  (affineRectangleClasses f t U i p r hU 4).symm
    ((sing Y).map (CycleQ2InjectiveCech.freeOpenMap (show i ⁻¹ᵁ baseOpen f t U ≤ ⊤ from le_top)) ≫
      (sing Y).map (CycleQ2SupportMV.π D ⊤) ≫ z)

open CycleQ2InjectiveCech (freeOpenMap)
open CycleQ2MayerVietorisRestriction (freeOpenSheaf)

private abbrev targetProjection := i ≫ pullback.snd (f ≫ structureMap k) t

/-- A zero ordinary restriction above any target open gives the zero ordinary
Čech representative on every affine refinement of that open. -/
theorem supportedRepresentative_zero_of_le (hU : IsAffineOpen U) {W : X.Opens} (h : U ≤ W)
    (D : Y.Opens) (z : (sing Y).obj (CycleQ2SupportMV.M D ⊤) ⟶
      (DerivedCategory.Q.obj (relativeDeRhamInt p r))⟦(4:ℤ)⟧)
    (hz : (sing Y).map (freeOpenMap (show targetProjection f t i ⁻¹ᵁ W ≤ ⊤ from le_top)) ≫
      (sing Y).map (CycleQ2SupportMV.π D ⊤) ≫ z = 0) :
    supportedRepresentative f t U i p r hU D z = 0 := by
  let V := i ⁻¹ᵁ baseOpen f t U
  let V' := targetProjection f t i ⁻¹ᵁ W
  have inc : V ≤ V' := fun _ hy => h hy
  have e : freeOpenMap inc ≫ freeOpenMap (show V' ≤ ⊤ from le_top) = freeOpenMap (show V ≤ ⊤ from le_top) :=
    (freeOpenSheaf.map_comp (homOfLE inc) (homOfLE (show V' ≤ ⊤ from le_top))).symm
  have zero : (sing Y).map (freeOpenMap (show V ≤ ⊤ from le_top)) ≫
      (sing Y).map (CycleQ2SupportMV.π D ⊤) ≫ z = 0 := by
    rw [← e,Functor.map_comp,Category.assoc,hz,comp_zero]
  exact ((affineRectangleClasses f t U i p r hU 4).symm.map_eq_zero_iff).mpr zero

/-- A target open containing a field-valued point where the ordinary class
vanishes contains an affine neighborhood of the same point with zero
rectangular degree-four representative. -/
theorem exists_affine_zero {F : Type} [Field F] (x : Spec (CommRingCat.of F) ⟶ X)
    (hx : Set.range x ⊆ (U : Set X)) (D : Y.Opens)
    (z : (sing Y).obj (CycleQ2SupportMV.M D ⊤) ⟶
      (DerivedCategory.Q.obj (relativeDeRhamInt p r))⟦(4:ℤ)⟧)
    (hz : (sing Y).map (freeOpenMap (show targetProjection f t i ⁻¹ᵁ U ≤ ⊤ from le_top)) ≫
      (sing Y).map (CycleQ2SupportMV.π D ⊤) ≫ z = 0) :
    ∃ (V : X.Opens) (hV : IsAffineOpen V), V ≤ U ∧ Set.range x ⊆ (V : Set X) ∧
      supportedRepresentative f t V i p r hV D z = 0 := by
  let s : PrimeSpectrum F := Classical.arbitrary _
  obtain ⟨V,hV,hs,hVU⟩ := exists_isAffineOpen_mem_and_subset (hx ⟨s,rfl⟩)
  refine ⟨V,hV,hVU,?_,supportedRepresentative_zero_of_le f t V i p r hV hVU D z hz⟩
  rintro _ ⟨b,rfl⟩
  exact (congrArg (fun a : PrimeSpectrum F => x a ∈ V) (Subsingleton.elim s b)).mp hs

section RestrictedProduct

private abbrev proj := pullback.snd (f ≫ structureMap k) t
private abbrev model := (proj f t ⁻¹ᵁ U).toScheme

/-- The original geometric ambient described by the proper-product square
as a fiber product over the surviving target open. -/
def restrictedProductIso : model f t U ≅ pullback (f ≫ structureMap k) (U.ι ≫ t) :=
  ((isPullback_morphismRestrict (proj f t) U).flip.paste_horiz
    (IsPullback.of_hasPullback (f ≫ structureMap k) t)).isoPullback

omit [CharZero k] [IsIntegral C] [IsFinite f] in
private theorem projection_eq :
    targetProjection f (U.ι ≫ t) (restrictedProductIso f t U).hom ≫ U.ι =
      (proj f t ⁻¹ᵁ U).ι ≫ proj f t := by
  unfold targetProjection restrictedProductIso
  rw [IsPullback.isoPullback_hom_snd]
  exact morphismRestrict_ι _ _

/-- Apply the vanishing-open conclusion to the original restricted product,
retaining the full image of the specified field-valued point in the ambient target. -/
theorem exists_affine_zero_in_restricted_product {F : Type} [Field F] (x : Spec (CommRingCat.of F) ⟶ X)
    {A : X.Opens} (hA : A ≤ U) (hx : Set.range x ⊆ (A : Set X))
    (P : model f t U ⟶ Spec (CommRingCat.of k)) (d : ℕ) [SmoothOfRelativeDimension d P]
    (D : (model f t U).Opens) (z : (sing (model f t U)).obj (CycleQ2SupportMV.M D ⊤) ⟶
      (DerivedCategory.Q.obj (relativeDeRhamInt P d))⟦(4:ℤ)⟧)
    (hz : (sing (model f t U)).map (freeOpenMap (show ((proj f t ⁻¹ᵁ U).ι ≫ proj f t) ⁻¹ᵁ A ≤ ⊤ from le_top)) ≫
      (sing (model f t U)).map (CycleQ2SupportMV.π D ⊤) ≫ z = 0) :
    ∃ (V : U.toScheme.Opens) (hV : IsAffineOpen V), U.ι ''ᵁ V ≤ A ∧
      Set.range x ⊆ (U.ι ''ᵁ V : Set X) ∧
      supportedRepresentative f (U.ι ≫ t) V (restrictedProductIso f t U).hom P d hV D z = 0 := by
  have hu : Set.range x ⊆ Set.range U.ι := by rw [U.range_ι]; exact hx.trans hA
  let x' := IsOpenImmersion.lift U.ι x hu
  have fac : x' ≫ U.ι = x := IsOpenImmersion.lift_fac _ _ _
  have point (b) : U.ι (x' b) = x b := congrArg (fun g : Spec (CommRingCat.of F) ⟶ X => g b) fac
  have hx' : Set.range x' ⊆ (U.ι ⁻¹ᵁ A : Set U.toScheme) := by
    rintro _ ⟨b,rfl⟩
    change U.ι (x' b) ∈ A
    rw [point]
    exact hx ⟨b,rfl⟩
  let e := (restrictedProductIso f t U).hom
  have ho : targetProjection f (U.ι ≫ t) e ⁻¹ᵁ (U.ι ⁻¹ᵁ A) = ((proj f t ⁻¹ᵁ U).ι ≫ proj f t) ⁻¹ᵁ A := by
    rw [← Scheme.Hom.comp_preimage,projection_eq]
  have hz' : (sing (model f t U)).map (freeOpenMap
      (show targetProjection f (U.ι ≫ t) e ⁻¹ᵁ (U.ι ⁻¹ᵁ A) ≤ ⊤ from le_top)) ≫
      (sing (model f t U)).map (CycleQ2SupportMV.π D ⊤) ≫ z = 0 := by
    rw [ho]
    exact hz
  obtain ⟨V,hV,hVA,hxV,hzV⟩ := exists_affine_zero f (U.ι ≫ t) (U.ι ⁻¹ᵁ A) e P d x' hx' D z hz'
  refine ⟨V,hV,?_,?_,hzV⟩
  · rintro _ ⟨b,hb,rfl⟩
    exact hVA hb
  · rintro _ ⟨b,rfl⟩
    exact ⟨x' b,hxV ⟨b,rfl⟩,point b⟩

end RestrictedProduct

end CycleQ2RectangularTrace

end

#print axioms CycleQ2RectangularTrace.affineRectangleClasses
#print axioms CycleQ2RectangularTrace.exists_affine_zero_in_restricted_product
