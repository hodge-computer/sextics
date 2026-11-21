import Proposal.GeometricAffineExteriorAcyclicity
import Proposal.GeometricSupportedHypercohomology
import Proposal.GeometricSupportedMayerVietorisDescent

/-! The ordinary two-chart de Rham restriction cone computes the derived classes on the full proper-curve product above an affine target open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/

noncomputable section

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
open CochainComplex HomComplex
namespace CycleQ2KInjectiveSections
variable {C : Type u} [Category.{v} C] [Abelian C] {P P' : C} (I : CochainComplex C ℤ)

def precompSections (g : P' ⟶ P) : sections P I ⟶ sections P' I where
  f j := (preadditiveCoyoneda.map g.op).app (I.X j)
  comm' i j _ := ((preadditiveCoyoneda.map g.op).naturality (I.d i j)).symm

private def representative (n : ℤ) (x : (sections P I).cycles n) :
    Cocycle ((CochainComplex.singleFunctor C 0).obj P) I n :=
  (HomComplex.leftHomologyData _ I n).cyclesIso.hom
    (cyclesMap (sectionsIso P I).hom n x)

private lemma representative_coe (n : ℤ) (x : (sections P I).cycles n) :
    (representative I n x).1 = Cochain.fromSingleMk ((sections P I).iCycles n x) (zero_add n) := by
  let h := HomComplex.leftHomologyData ((CochainComplex.singleFunctor C 0).obj P) I n
  let y := cyclesMap (sectionsIso P I).hom n x
  exact (ConcreteCategory.congr_hom h.cyclesIso_hom_comp_i y).trans
    (ConcreteCategory.congr_hom (cyclesMap_i (sectionsIso P I).hom n) x)

private lemma representative_precomp (n : ℤ) (g : P' ⟶ P) (x : (sections P I).cycles n) :
    representative I n (cyclesMap (precompSections I g) n x) =
      (representative I n x).precomp ((CochainComplex.singleFunctor C 0).map g) := by
  apply Subtype.ext
  have h : (sections P' I).iCycles n (cyclesMap (precompSections I g) n x) =
      g ≫ (sections P I).iCycles n x :=
    ConcreteCategory.congr_hom (cyclesMap_i (precompSections I g) n) x
  rw [representative_coe, h]
  exact (Cochain.fromSingleMk_precomp (K := I) g ((sections P I).iCycles n x) (zero_add n)).trans
    (congrArg (fun a => (Cochain.ofHom ((CochainComplex.singleFunctor C 0).map g)).comp a (zero_add n))
      (representative_coe I n x).symm)

variable [HasDerivedCategory.{w} C] [I.IsKInjective]

private lemma derivedSectionsEquiv_π (n : ℤ) (x : (sections P I).cycles n) :
    derivedSectionsEquiv P I n ((sections P I).homologyπ n x) =
      classEquiv P I n (CohomologyClass.mk (representative I n x)) := by
  let h := HomComplex.leftHomologyData ((CochainComplex.singleFunctor C 0).obj P) I n
  apply (classEquiv P I n).congr_arg
  change h.homologyIso.hom (homologyMap (sectionsIso P I).hom n ((sections P I).homologyπ n x)) = _
  have e := ConcreteCategory.congr_hom (homologyπ_naturality (sectionsIso P I).hom n) x
  rw [show homologyMap (sectionsIso P I).hom n ((sections P I).homologyπ n x) = _ from e]
  exact ConcreteCategory.congr_hom h.homologyπ_comp_homologyIso_hom
    (cyclesMap (sectionsIso P I).hom n x)

private lemma classEquiv_precomp (n : ℤ) (g : P' ⟶ P)
    (z : Cocycle ((CochainComplex.singleFunctor C 0).obj P) I n) :
    classEquiv P' I n (CohomologyClass.mk (z.precomp ((CochainComplex.singleFunctor C 0).map g))) =
      (DerivedCategory.singleFunctor C 0).map g ≫ classEquiv P I n (CohomologyClass.mk z) := by
  let f := (CochainComplex.singleFunctor C 0).map g
  let Qh := DerivedCategory.Qh (C := C)
  let T := HomotopyCategory.quotient C (.up ℤ)
  let a := DerivedCategory.quotientCompQhIso C
  let b := a.app (I⟦n⟧) ≪≫ (DerivedCategory.Q.commShiftIso n).app I
  change a.inv.app _ ≫ Qh.map (T.map (Cocycle.equivHomShift.symm (z.precomp f))) ≫ b.hom =
    DerivedCategory.Q.map f ≫ a.inv.app _ ≫ Qh.map (T.map (Cocycle.equivHomShift.symm z)) ≫ b.hom
  rw [Cocycle.equivHomShift_symm_precomp, T.map_comp, Qh.map_comp, Category.assoc,
    DerivedCategory.quotientCompQhIso_inv_naturality_assoc]

/-- Restricting sections by precomposition induces the actual derived morphism from the
corresponding single complex. -/
theorem derivedSectionsEquiv_precomp (g : P' ⟶ P) (n : ℤ) (x : (sections P I).homology n) :
    derivedSectionsEquiv P' I n (homologyMap (precompSections I g) n x) =
      (DerivedCategory.singleFunctor C 0).map g ≫ derivedSectionsEquiv P I n x := by
  obtain ⟨y, rfl⟩ := (AddCommGrpCat.epi_iff_surjective ((sections P I).homologyπ n)).mp inferInstance x
  have h : homologyMap (precompSections I g) n ((sections P I).homologyπ n y) =
      (sections P' I).homologyπ n (cyclesMap (precompSections I g) n y) :=
    ConcreteCategory.congr_hom (homologyπ_naturality (precompSections I g) n) y
  rw [h, derivedSectionsEquiv_π, derivedSectionsEquiv_π, representative_precomp, classEquiv_precomp]

end CycleQ2KInjectiveSections

namespace CycleQ2RectangularTrace

section Sections
open Pretriangulated
variable {A : Type u} [Category.{v} A] [Abelian A]
  (S : ShortComplex A) (K : CochainComplex A ℤ)

open CycleQ2AffineHypercohomologyComparison (sectionComplex)
abbrev secs (P : A) := (sectionComplex P).obj K
abbrev res {P R : A} (f : P ⟶ R) : secs K R ⟶ secs K P :=
  CycleQ2KInjectiveSections.precompSections K f

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

end Sections

section
variable {A : Type u} [Category.{v} A] [Abelian A]
  {S T : ShortComplex A} (u : T ⟶ S) (K : CochainComplex A ℤ)

def pairRestriction : pair S K ⟶ pair T K where
  τ₁ := res K u.τ₃
  τ₂ := res K u.τ₂
  τ₃ := res K u.τ₁
  comm₁₂ := by
    ext j x
    change T.g ≫ u.τ₃ ≫ x = u.τ₂ ≫ S.g ≫ x
    let y : S.X₃ ⟶ K.X j := x
    exact (Category.assoc _ _ y).symm.trans
      ((congrArg (fun a => a ≫ y) u.comm₂₃.symm).trans (Category.assoc _ _ y))
  comm₂₃ := by
    ext j x
    change T.f ≫ u.τ₂ ≫ x = u.τ₁ ≫ S.f ≫ x
    let y : S.X₂ ⟶ K.X j := x
    exact (Category.assoc _ _ y).symm.trans
      ((congrArg (fun a => a ≫ y) u.comm₁₂.symm).trans (Category.assoc _ _ y))

private abbrev gMap {R R' : ShortComplex (CochainComplex AddCommGrpCat.{v} ℤ)} (m : R ⟶ R') :=
  mappingCone.map R.g R'.g m.τ₂ m.τ₃ m.comm₂₃.symm
private abbrev fMap {R R' : ShortComplex (CochainComplex AddCommGrpCat.{v} ℤ)} (m : R ⟶ R') :=
  mappingCone.map R.f R'.f m.τ₁ m.τ₂ m.comm₁₂.symm

def rectangleRestriction : rectangleCone S K ⟶ rectangleCone T K := gMap (pairRestriction u K)

variable {K} {I : CochainComplex A ℤ} (ρ : K ⟶ I)
open CycleQ2AffineHypercohomologyComparison (sectionComplex)

private def pairCoeff (S : ShortComplex A) : pair S K ⟶ pair S I where
  τ₁ := (sectionComplex S.X₃).map ρ
  τ₂ := (sectionComplex S.X₂).map ρ
  τ₃ := (sectionComplex S.X₁).map ρ
  comm₁₂ := by ext j x; exact (Category.assoc _ _ _).symm
  comm₂₃ := by ext j x; exact (Category.assoc _ _ _).symm

private theorem gMap_square {R₁ R₂ R₃ R₄ : ShortComplex (CochainComplex AddCommGrpCat.{v} ℤ)}
    (a : R₁ ⟶ R₂) (b : R₂ ⟶ R₄) (c : R₁ ⟶ R₃) (d : R₃ ⟶ R₄)
    (h : a ≫ b = c ≫ d) : gMap a ≫ gMap b = gMap c ≫ gMap d := by
  unfold gMap
  rw [← mappingCone.map_comp, ← mappingCone.map_comp]
  have h₂ : a.τ₂ ≫ b.τ₂ = c.τ₂ ≫ d.τ₂ := congrArg ShortComplex.Hom.τ₂ h
  have h₃ : a.τ₃ ≫ b.τ₃ = c.τ₃ ≫ d.τ₃ := congrArg ShortComplex.Hom.τ₃ h
  congr 1

private theorem rectangleRestriction_coeff :
    rectangleRestriction u K ≫ gMap (pairCoeff ρ T) =
      gMap (pairCoeff ρ S) ≫ rectangleRestriction u I := by
  apply gMap_square
  ext <;> exact (Category.assoc _ _ _)

section Compatibility
variable {R R' : ShortComplex (CochainComplex AddCommGrpCat.{v} ℤ)} (m : R ⟶ R')

private theorem inr_comm : mappingCone.inr R.f ≫ fMap m = m.τ₂ ≫ mappingCone.inr R'.f :=
  (mappingCone.triangleMap R.f R'.f m.τ₁ m.τ₂ m.comm₁₂.symm).comm₂

private abbrev doubleMap := mappingCone.map (mappingCone.inr R.f) (mappingCone.inr R'.f)
  m.τ₂ (fMap m) (inr_comm m)

private abbrev descMap (R : ShortComplex (CochainComplex AddCommGrpCat.{v} ℤ)) :=
  mappingCone.map (mappingCone.inr R.f) R.g (𝟙 _) (mappingCone.descShortComplex R) (by simp)

private theorem descMap_naturality : doubleMap m ≫ descMap R' = descMap R ≫ gMap m := by
  unfold doubleMap descMap gMap
  rw [← mappingCone.map_comp, ← mappingCone.map_comp]
  have a : m.τ₂ ≫ 𝟙 _ = 𝟙 _ ≫ m.τ₂ := by simp
  have b := mappingCone.descShortComplex_naturality m
  congr 1

private theorem rotateInv_naturality :
    doubleMap m ≫ (mappingCone.rotateHomotopyEquiv R'.f).inv =
      (mappingCone.rotateHomotopyEquiv R.f).inv ≫ m.τ₁⟦(1:ℤ)⟧' := by
  have h := (mappingCone.triangleMap R.f R'.f m.τ₁ m.τ₂ m.comm₁₂.symm).comm₃.symm
  change fMap m ≫ (mappingCone.triangle R'.f).mor₃ =
    (mappingCone.triangle R.f).mor₃ ≫ m.τ₁⟦(1:ℤ)⟧' at h
  let conn (X : ShortComplex (CochainComplex AddCommGrpCat.{v} ℤ)) :
      mappingCone X.f ⟶ X.X₁⟦(1:ℤ)⟧ := (mappingCone.triangle X.f).mor₃
  have rel (X : ShortComplex (CochainComplex AddCommGrpCat.{v} ℤ)) :
      δ (-1) 0 (0 : Cochain X.X₂ (X.X₁⟦(1:ℤ)⟧) (-1)) = Cochain.ofHom (mappingCone.inr X.f ≫ conn X) :=
    (δ_zero _ _).trans ((congrArg Cochain.ofHom (mappingCone.inr_triangleδ X.f)).trans (Cochain.ofHom_zero _ _)).symm
  apply HomologicalComplex.hom_ext
  intro j
  have hl (X : ShortComplex (CochainComplex AddCommGrpCat.{v} ℤ)) :
      (mappingCone.inl (mappingCone.inr X.f)).v (j+1) j (by omega) ≫
        (mappingCone.rotateHomotopyEquiv X.f).inv.f j = 0 :=
    (mappingCone.inl_v_desc_f _ 0 (conn X) (rel X) _ _ _).trans (Cochain.zero_v _ _ _)
  have hr (X : ShortComplex (CochainComplex AddCommGrpCat.{v} ℤ)) :
      (mappingCone.inr (mappingCone.inr X.f)).f j ≫ (mappingCone.rotateHomotopyEquiv X.f).inv.f j =
        (conn X).f j := mappingCone.inr_f_desc_f _ 0 (conn X) (rel X) j
  apply mappingCone.ext_from _ (j+1) j rfl
  · change (mappingCone.inl (mappingCone.inr R.f)).v (j+1) j _ ≫
        (doubleMap m).f j ≫ (mappingCone.rotateHomotopyEquiv R'.f).inv.f j = _
    rw [← Category.assoc]
    change ((mappingCone.inl (mappingCone.inr R.f)).v (j+1) j _ ≫
      (mappingCone.desc _ _ _ _).f j) ≫ _ = _
    rw [mappingCone.inl_v_desc_f]
    simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Category.assoc]
    change _ = (mappingCone.inl (mappingCone.inr R.f)).v (j+1) j _ ≫
      (mappingCone.rotateHomotopyEquiv R.f).inv.f j ≫ _
    rw [hl R', ← Category.assoc, hl R, zero_comp, comp_zero]
  · have hj := congrArg (fun q => HomologicalComplex.Hom.f q j) h
    change (mappingCone.inr (mappingCone.inr R.f)).f j ≫
        (doubleMap m).f j ≫ (mappingCone.rotateHomotopyEquiv R'.f).inv.f j = _
    rw [← Category.assoc]
    change ((mappingCone.inr (mappingCone.inr R.f)).f j ≫
      (mappingCone.desc _ _ _ _).f j) ≫ _ = _
    rw [mappingCone.inr_f_desc_f]
    change ((fMap m).f j ≫ (mappingCone.inr (mappingCone.inr R'.f)).f j) ≫
        (mappingCone.rotateHomotopyEquiv R'.f).inv.f j =
      (mappingCone.inr (mappingCone.inr R.f)).f j ≫ (mappingCone.rotateHomotopyEquiv R.f).inv.f j ≫ _
    rw [Category.assoc, hr R', ← Category.assoc, hr R]
    exact hj
end Compatibility
end

section Sections
open Pretriangulated
variable {A : Type u} [Category.{v} A] [Abelian A] (S : ShortComplex A)
  (K : CochainComplex A ℤ)
open CycleQ2AffineHypercohomologyComparison (sectionComplex)
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

private def coefficientIso (S : ShortComplex A)
    [h₁ : QuasiIso ((sectionComplex S.X₁).map ρ)] [h₂ : QuasiIso ((sectionComplex S.X₂).map ρ)] :
    DerivedCategory.Q.obj (rectangleCone S K) ≅ DerivedCategory.Q.obj (rectangleCone S I) :=
  coneMapIso _ _ (pairCoeff ρ S).τ₂ (pairCoeff ρ S).τ₃ (pairCoeff ρ S).comm₂₃.symm h₂ h₁

private def descentIso (R : ShortComplex (CochainComplex AddCommGrpCat.{v} ℤ)) (hR : R.ShortExact) :
    DerivedCategory.Q.obj (mappingCone (mappingCone.inr R.f)) ≅ DerivedCategory.Q.obj (mappingCone R.g) :=
  coneMapIso _ _ (𝟙 _) (mappingCone.descShortComplex R) (by simp)
    (inferInstanceAs (QuasiIso (𝟙 _))) (mappingCone.quasiIso_descShortComplex hR)

/-- The ordinary two-open restriction difference computes hypercohomology
on the union whenever the resolution induces quasi-isomorphisms on each
chart row. The maps are the two explicit cone maps and the standard rotation. -/
def ordinaryConeIso (hs : S.ShortExact) [∀ i, Injective (I.X i)]
    [QuasiIso ((sectionComplex S.X₁).map ρ)] [QuasiIso ((sectionComplex S.X₂).map ρ)] :
    DerivedCategory.Q.obj (rectangleCone S K) ≅
      (DerivedCategory.Q.obj (secs I S.X₃))⟦(1:ℤ)⟧ :=
  coefficientIso ρ S ≪≫ (descentIso (pair S I) (pair_exact S I hs)).symm ≪≫
    asIso (DerivedCategory.Q.map (mappingCone.rotateHomotopyEquiv (pair S I).f).inv) ≪≫
    (DerivedCategory.Q.commShiftIso (1:ℤ)).app (secs I S.X₃)

/-- Restriction commutes with the comparison to sections of the fixed
resolution on the union, before taking cohomology or selecting a class. -/
theorem ordinaryConeIso_naturality {S T : ShortComplex A} (u : T ⟶ S)
    (hS : S.ShortExact) (hT : T.ShortExact) [∀ i, Injective (I.X i)]
    [QuasiIso ((sectionComplex S.X₁).map ρ)] [QuasiIso ((sectionComplex S.X₂).map ρ)]
    [QuasiIso ((sectionComplex T.X₁).map ρ)] [QuasiIso ((sectionComplex T.X₂).map ρ)] :
    DerivedCategory.Q.map (rectangleRestriction u K) ≫ (ordinaryConeIso T ρ hT).hom =
      (ordinaryConeIso S ρ hS).hom ≫ (DerivedCategory.Q.map (res I u.τ₃))⟦(1:ℤ)⟧' := by
  let D := DerivedCategory.Q (C := AddCommGrpCat.{v})
  let a := coefficientIso ρ S
  let a' := coefficientIso ρ T
  let b := descentIso (pair S I) (pair_exact S I hS)
  let b' := descentIso (pair T I) (pair_exact T I hT)
  let m := pairRestriction u I
  have ha : D.map (rectangleRestriction u K) ≫ a'.hom = a.hom ≫ D.map (gMap m) := by
    change D.map (rectangleRestriction u K) ≫ D.map (gMap (pairCoeff ρ T)) =
      D.map (gMap (pairCoeff ρ S)) ≫ D.map (rectangleRestriction u I)
    exact ((D.map_comp _ _).symm.trans (congrArg (fun q => D.map q) (rectangleRestriction_coeff u ρ))).trans
      (D.map_comp _ _)
  have hb : D.map (doubleMap m) ≫ b'.hom = b.hom ≫ D.map (gMap m) := by
    change D.map (doubleMap m) ≫ D.map (descMap (pair T I)) =
      D.map (descMap (pair S I)) ≫ D.map (gMap m)
    exact ((D.map_comp _ _).symm.trans (congrArg (fun q => D.map q) (descMap_naturality m))).trans
      (D.map_comp _ _)
  have hb' : D.map (gMap m) ≫ b'.inv = b.inv ≫ D.map (doubleMap m) := by
    apply (Iso.comp_inv_eq _).2
    rw [Category.assoc, hb, Iso.inv_hom_id_assoc]
  have hc := congrArg (fun q => D.map q) (rotateInv_naturality m)
  simp only [Functor.map_comp] at hc
  have hd := (D.commShiftIso (1:ℤ)).hom.naturality (res I u.τ₃)
  change D.map (rectangleRestriction u K) ≫ a'.hom ≫ b'.inv ≫ D.map _ ≫ _ =
    (a.hom ≫ b.inv ≫ D.map _ ≫ _) ≫ _
  simp only [Category.assoc]
  rw [reassoc_of% ha, reassoc_of% hb', reassoc_of% hc]
  exact congrArg (fun q => a.hom ≫ b.inv ≫ D.map (mappingCone.rotateHomotopyEquiv (pair S I).f).inv ≫ q) hd

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

/-- The induced comparison with section cohomology of this resolution. -/
def ordinaryHomologyIso {I : CochainComplex A ℤ} (f : K ⟶ I)
    [∀ i, Injective (I.X i)]
    [QuasiIso ((sectionComplex S.X₁).map f)] [QuasiIso ((sectionComplex S.X₂).map f)] (n : ℤ) :
    (rectangleCone S K).homology (n-1) ≅ (secs I S.X₃).homology n := by
  letI := HasDerivedCategory.standard AddCommGrpCat.{v}
  let e := ordinaryConeIso S f hs
  exact (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v} (n-1)).symm.app (rectangleCone S K) ≪≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{v} (n-1)).mapIso e ≪≫
    (((DerivedCategory.homologyFunctor AddCommGrpCat.{v} 0).shiftIso (1:ℤ) (n-1) n (by omega)).app
      (DerivedCategory.Q.obj (secs I S.X₃))) ≪≫
    (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v} n).app (secs I S.X₃)

omit [HasDerivedCategory A] [HasExt A] [EnoughInjectives A] in
/-- The map from an ordinary Čech cohomology class to section cohomology
is natural for every morphism of short exact cover complexes. -/
theorem ordinaryHomologyIso_naturality {S T : ShortComplex A} (u : T ⟶ S)
    (hS : S.ShortExact) (hT : T.ShortExact) {I : CochainComplex A ℤ} (f : K ⟶ I)
    [∀ i, Injective (I.X i)]
    [QuasiIso ((sectionComplex S.X₁).map f)] [QuasiIso ((sectionComplex S.X₂).map f)]
    [QuasiIso ((sectionComplex T.X₁).map f)] [QuasiIso ((sectionComplex T.X₂).map f)] (n : ℤ) :
    homologyMap (rectangleRestriction u K) (n-1) ≫ (ordinaryHomologyIso T hT K f n).hom =
      (ordinaryHomologyIso S hS K f n).hom ≫ homologyMap (res I u.τ₃) n := by
  let := HasDerivedCategory.standard AddCommGrpCat.{v}
  let H := DerivedCategory.homologyFunctor AddCommGrpCat.{v} (n-1)
  let r := rectangleRestriction u K
  let g := res I u.τ₃
  let Q := DerivedCategory.Q (C := AddCommGrpCat.{v})
  let F := DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v} (n-1)
  let B := (DerivedCategory.homologyFunctor AddCommGrpCat.{v} 0).shiftIso (1:ℤ) (n-1) n (by omega)
  let G := DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v} n
  have h₁ := F.inv.naturality r
  change homologyMap r (n-1) ≫ F.inv.app _ = F.inv.app _ ≫ H.map (Q.map r) at h₁
  have h₂ := congrArg (fun q => H.map q) (ordinaryConeIso_naturality f u hS hT)
  simp only [Functor.map_comp] at h₂
  have h₃ := B.hom.naturality (Q.map g)
  have h₄ := G.hom.naturality g
  exact ((CommSq.mk h₁).vert_comp ((CommSq.mk h₂).vert_comp
    ((CommSq.mk h₃).vert_comp (CommSq.mk h₄)))).w

/-- The comparison determined by a specified injective resolution and the
Mayer–Vietoris cone maps. -/
def ordinaryClassesOfResolution {I : CochainComplex A ℤ} (f : K ⟶ I)
    [QuasiIso f] [∀ i, Injective (I.X i)] [I.IsKInjective]
    [QuasiIso ((sectionComplex S.X₁).map f)] [QuasiIso ((sectionComplex S.X₂).map f)] (n : ℤ) :
    (rectangleCone S K).homology (n-1) ≃+
      ((DerivedCategory.singleFunctor A 0).obj S.X₃ ⟶ (DerivedCategory.Q.obj K)⟦n⟧) := by
  let h := ordinaryHomologyIso S hs K f n
  let d := CycleQ2KInjectiveSections.derivedSectionsEquiv S.X₃ I n
  let z := (CategoryTheory.shiftFunctor (DerivedCategory A) n).mapIso ((asIso (DerivedCategory.Q.map f)).symm)
  have z' : ((DerivedCategory.singleFunctor A 0).obj S.X₃ ⟶ (DerivedCategory.Q.obj I)⟦n⟧) ≃+
      ((DerivedCategory.singleFunctor A 0).obj S.X₃ ⟶ (DerivedCategory.Q.obj K)⟦n⟧) :=
    { Iso.homCongr (Iso.refl _) z with map_add' x y := by simp [Iso.homCongr] }
  exact (h.addCommGroupIsoToAddEquiv.trans d).trans z'

omit [HasExt A] [EnoughInjectives A] in
/-- A class calculated on the chosen resolution is sent back along that
resolution's own quasi-isomorphism. -/
theorem ordinaryClassesOfResolution_apply {I : CochainComplex A ℤ} (f : K ⟶ I)
    [QuasiIso f] [∀ i, Injective (I.X i)] [I.IsKInjective]
    [QuasiIso ((sectionComplex S.X₁).map f)] [QuasiIso ((sectionComplex S.X₂).map f)]
    (n : ℤ) (x : (rectangleCone S K).homology (n-1)) :
    ordinaryClassesOfResolution S hs K f n x =
      CycleQ2KInjectiveSections.derivedSectionsEquiv S.X₃ I n
        ((ordinaryHomologyIso S hs K f n).hom x) ≫
          (CategoryTheory.shiftFunctor (DerivedCategory A) n).map (asIso (DerivedCategory.Q.map f)).inv := by
  change 𝟙 _ ≫ _ ≫ _ = _
  exact Category.id_comp _

omit [HasExt A] [EnoughInjectives A] in
/-- Restricting a class in a fixed resolution commutes with its
identification as a derived morphism on the union. -/
theorem ordinaryClassesOfResolution_naturality {S T : ShortComplex A} (u : T ⟶ S)
    (hS : S.ShortExact) (hT : T.ShortExact) {I : CochainComplex A ℤ} (f : K ⟶ I)
    [QuasiIso f] [∀ i, Injective (I.X i)] [I.IsKInjective]
    [QuasiIso ((sectionComplex S.X₁).map f)] [QuasiIso ((sectionComplex S.X₂).map f)]
    [QuasiIso ((sectionComplex T.X₁).map f)] [QuasiIso ((sectionComplex T.X₂).map f)] (n : ℤ)
    (x : (rectangleCone S K).homology (n-1)) :
    ordinaryClassesOfResolution T hT K f n (homologyMap (rectangleRestriction u K) (n-1) x) =
      (DerivedCategory.singleFunctor A 0).map u.τ₃ ≫ ordinaryClassesOfResolution S hS K f n x := by
  rw [ordinaryClassesOfResolution_apply, ordinaryClassesOfResolution_apply]
  have h := ConcreteCategory.congr_hom (ordinaryHomologyIso_naturality K u hS hT f n) x
  change (ordinaryHomologyIso T hT K f n).hom (homologyMap (rectangleRestriction u K) (n-1) x) =
    homologyMap (res I u.τ₃) n ((ordinaryHomologyIso S hS K f n).hom x) at h
  rw [h, CycleQ2KInjectiveSections.derivedSectionsEquiv_precomp, Category.assoc]

private structure SectionsResolution (K : CochainComplex A ℤ) where
  obj : CochainComplex A ℤ
  ι : K ⟶ obj
  quasiIso : QuasiIso ι
  injective : ∀ i, Injective (obj.X i)
  kInjective : obj.IsKInjective
  row (P : A) : (∀ i, AcyclicFor P (K.X i)) → QuasiIso ((sectionComplex P).map ι)

private def sectionsResolution (b : ℤ) [K.IsStrictlyGE b] : SectionsResolution K := by
  let hr := CochainComplex.Plus.modelCategoryQuillen.exists_mono_quasiIso_injective K (b-1) b
  let I := hr.choose
  let f : K ⟶ I := hr.choose_spec.choose
  have hI := hr.choose_spec.choose_spec
  letI : Mono f := hI.1
  letI : QuasiIso f := hI.2.1
  letI : ∀ i, Injective (I.X i) := hI.2.2.1
  letI : I.IsStrictlyGE (b-1) := hI.2.2.2
  exact ⟨I, f, inferInstance, inferInstance, CochainComplex.isKInjective_of_injective I (b-1),
    fun P hp => sections_quasiIso P f (b-1) hp (fun i m => Ext.subsingleton_of_injective P (I.X i) m)⟩

/-- A single resolution of the coefficient complex is used on every cover. -/
def ordinaryClasses (b n : ℤ) [K.IsStrictlyGE b]
    (h₁ : ∀ i, AcyclicFor S.X₁ (K.X i)) (h₂ : ∀ i, AcyclicFor S.X₂ (K.X i)) :
    (rectangleCone S K).homology (n-1) ≃+
      ((DerivedCategory.singleFunctor A 0).obj S.X₃ ⟶ (DerivedCategory.Q.obj K)⟦n⟧) := by
  let R := sectionsResolution K b
  exact @ordinaryClassesOfResolution A _ _ _ S hs K R.obj R.ι R.quasiIso R.injective R.kInjective
    (R.row S.X₁ h₁) (R.row S.X₂ h₂) n

theorem ordinaryClasses_naturality {S T : ShortComplex A} (u : T ⟶ S) (hS : S.ShortExact)
    (hT : T.ShortExact) (b n : ℤ) [K.IsStrictlyGE b]
    (hS₁ : ∀ i, AcyclicFor S.X₁ (K.X i)) (hS₂ : ∀ i, AcyclicFor S.X₂ (K.X i))
    (hT₁ : ∀ i, AcyclicFor T.X₁ (K.X i)) (hT₂ : ∀ i, AcyclicFor T.X₂ (K.X i))
    (x : (rectangleCone S K).homology (n-1)) :
    ordinaryClasses T hT K b n hT₁ hT₂ (homologyMap (rectangleRestriction u K) (n-1) x) =
      (DerivedCategory.singleFunctor A 0).map u.τ₃ ≫ ordinaryClasses S hS K b n hS₁ hS₂ x := by
  let R := sectionsResolution K b
  exact @ordinaryClassesOfResolution_naturality A _ _ _ K S T u hS hT R.obj R.ι R.quasiIso R.injective
    R.kInjective (R.row S.X₁ hS₁) (R.row S.X₂ hS₂) (R.row T.X₁ hT₁) (R.row T.X₂ hT₂) n x

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

section GeometricRestriction
open AlgebraicGeometry TopologicalSpace
open CycleQ2MayerVietorisRestriction (freeOpenSheaf)
open CycleQ2LaurentProjectiveLine (line)
open CycleQ2ProjectiveLineStructure (structureMap)
variable {k : Type} [Field k] {C X Y : Scheme.{0}} [IsIntegral C]
  (f : C ⟶ line k) (t : X ⟶ Spec (CommRingCat.of k)) {U V : X.Opens}
  (i : Y ⟶ pullback (f ≫ structureMap k) t)

/-- The morphism of the actual product Mayer–Vietoris complexes induced by
a restriction of the target open. -/
def sourceRectangleMap (h : U ≤ V) :
    (sourceRectangle f t U i).shortComplex ⟶ (sourceRectangle f t V i).shortComplex where
  τ₁ := freeOpenSheaf.map (homOfLE (show i ⁻¹ᵁ midOpen f t U ≤ i ⁻¹ᵁ midOpen f t V from
    fun _ hx => ⟨hx.1, h hx.2⟩))
  τ₂ := biprod.map (freeOpenSheaf.map (homOfLE (show i ⁻¹ᵁ leftOpen f t U ≤ i ⁻¹ᵁ leftOpen f t V
    from fun _ hx => ⟨hx.1, h hx.2⟩))) (freeOpenSheaf.map (homOfLE
    (show i ⁻¹ᵁ rightOpen f t U ≤ i ⁻¹ᵁ rightOpen f t V from fun _ hx => ⟨hx.1, h hx.2⟩)))
  τ₃ := freeOpenSheaf.map (homOfLE (show i ⁻¹ᵁ baseOpen f t U ≤ i ⁻¹ᵁ baseOpen f t V from
    fun _ hx => h hx))
  comm₁₂ := by
    let K := freeOpenSheaf (X := (show TopCat from Y))
    change K.map _ ≫ biprod.lift (K.map _) (-(K.map _)) =
      biprod.lift (K.map _) (-(K.map _)) ≫ biprod.map (K.map _) (K.map _)
    apply biprod.hom_ext <;> simp [← Functor.map_comp] <;> congr 1
  comm₂₃ := by
    let K := freeOpenSheaf (X := (show TopCat from Y))
    change biprod.map (K.map _) (K.map _) ≫ biprod.desc (K.map _) (K.map _) =
      biprod.desc (K.map _) (K.map _) ≫ K.map _
    apply biprod.hom_ext' <;> simp [← Functor.map_comp] <;> congr 1

end GeometricRestriction

abbrev affineCurveCech := rectangleCone (sourceRectangle f t U i).shortComplex (relativeDeRhamInt p r)

private theorem rectangleAcyclic (hU : IsAffineOpen U) :
    (∀ j, CycleQ2AcyclicComplexSections.AcyclicFor (sourceRectangle f t U i).shortComplex.X₁
      ((relativeDeRhamInt p r).X j)) ∧
    (∀ j, CycleQ2AcyclicComplexSections.AcyclicFor (sourceRectangle f t U i).shortComplex.X₂
      ((relativeDeRhamInt p r).X j)) := by
  have rows := affine_rows f t U hU
  exact ⟨fun j a => term_acyclic p r (rows.2.2.preimage i) j a,
    fun j => acyclic_biprod (term_acyclic p r (rows.1.preimage i) j) (term_acyclic p r (rows.2.1.preimage i) j)⟩

private instance productSheafEnoughInjectives :
    EnoughInjectives (AbSheaf (show TopCat from Y)) := by
  change EnoughInjectives (TopCat.Sheaf AddCommGrpCat.{0} Y)
  infer_instance

/-- On the actual rectangles over any affine target open, the finite curve
cover computes every derived class by the ordinary Čech cone. -/
def affineRectangleClasses (hU : IsAffineOpen U) (n : ℤ) :
    (affineCurveCech f t U i p r).homology (n-1) ≃+
      ((DerivedCategory.singleFunctor (AbSheaf (show TopCat from Y)) 0).obj
        (sourceRectangle f t U i).shortComplex.X₃ ⟶ (DerivedCategory.Q.obj (relativeDeRhamInt p r))⟦n⟧) :=
  @ordinaryClasses _ _ _ _ _ _ (sourceRectangle f t U i).shortComplex
    (sourceRectangle f t U i).shortComplex_shortExact (relativeDeRhamInt p r) 0 n (deRham_bounded p r)
    (rectangleAcyclic f t U i p r hU).1 (rectangleAcyclic f t U i p r hU).2

/-- Simultaneous restriction of the two curve rectangles agrees with
precomposition by the inclusion of the smaller product open. -/
theorem affineRectangleClasses_naturality {V : X.Opens} (h : U ≤ V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (n : ℤ)
    (x : (affineCurveCech f t V i p r).homology (n-1)) :
    affineRectangleClasses f t U i p r hU n
      (homologyMap (rectangleRestriction (sourceRectangleMap f t i h) (relativeDeRhamInt p r)) (n-1) x) =
      (DerivedCategory.singleFunctor (AbSheaf (show TopCat from Y)) 0).map
        (sourceRectangleMap f t i h).τ₃ ≫ affineRectangleClasses f t V i p r hV n x := by
  let := deRham_bounded p r
  have a := rectangleAcyclic f t V i p r hV
  have b := rectangleAcyclic f t U i p r hU
  exact ordinaryClasses_naturality (relativeDeRhamInt p r) (sourceRectangleMap f t i h)
    (sourceRectangle f t V i).shortComplex_shortExact (sourceRectangle f t U i).shortComplex_shortExact
    0 n a.1 a.2 b.1 b.2 x

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

/-- The representative of a fixed supported degree-four class restricts by the
ordinary Čech cone map on the two product rectangles. -/
theorem supportedRepresentative_restrict {V : X.Opens} (h : U ≤ V) (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (D : Y.Opens)
    (z : (sing Y).obj (CycleQ2SupportMV.M D ⊤) ⟶ (DerivedCategory.Q.obj (relativeDeRhamInt p r))⟦(4:ℤ)⟧) :
    homologyMap (rectangleRestriction (sourceRectangleMap f t i h) (relativeDeRhamInt p r)) 3
      (supportedRepresentative f t V i p r hV D z) = supportedRepresentative f t U i p r hU D z := by
  apply (affineRectangleClasses f t U i p r hU 4).injective
  refine (affineRectangleClasses_naturality f t U i p r h hU hV 4
    (supportedRepresentative f t V i p r hV D z)).trans ?_
  simp only [supportedRepresentative, AddEquiv.apply_symm_apply]
  let a := i ⁻¹ᵁ baseOpen f t U
  let b := i ⁻¹ᵁ baseOpen f t V
  have hab : a ≤ b := fun _ hx => h hx
  have e : freeOpenMap hab ≫ freeOpenMap (show b ≤ ⊤ from le_top) =
      freeOpenMap (show a ≤ ⊤ from le_top) :=
    (freeOpenSheaf.map_comp (homOfLE hab) (homOfLE (show b ≤ ⊤ from le_top))).symm
  change (sing Y).map (freeOpenMap hab) ≫ (sing Y).map (freeOpenMap _) ≫ _ =
    (sing Y).map (freeOpenMap _) ≫ _
  rw [← Category.assoc, ← Functor.map_comp, e]

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

/-- A zero rectangular representative can be retained on an exact affine
frame of the target around the same field-valued point. -/
theorem refine_zero_to_frame (n : ℕ) [SmoothOfRelativeDimension n t]
    (hU : IsAffineOpen U) {F : Type} [Field F] (x : Spec (CommRingCat.of F) ⟶ X)
    (hx : Set.range x ⊆ (U : Set X)) (D : Y.Opens)
    (z : (sing Y).obj (CycleQ2SupportMV.M D ⊤) ⟶
      (DerivedCategory.Q.obj (relativeDeRhamInt p r))⟦(4:ℤ)⟧)
    (hz : supportedRepresentative f t U i p r hU D z = 0) :
    ∃ V : CycleQ2IntrinsicFramedAffineSite.FramedOpen t n, V.1 ≤ U ∧
      Set.range x ⊆ (V.1 : Set X) ∧ supportedRepresentative f t V.1 i p r V.2.1 D z = 0 := by
  let s := (default : PrimeSpectrum F)
  obtain ⟨V,hV,hxV,hVU⟩ := (Opens.isBasis_iff_nbhd.mp
    (CycleQ2FiniteExactAffineAtlas.isBasis t n)) (hx ⟨s,rfl⟩)
  refine ⟨⟨V,hV⟩,hVU,?_,supportedRepresentative_zero_of_le f t V i p r hV.1 hVU D z ?_⟩
  · rintro _ ⟨b,rfl⟩
    exact (congrArg (fun a : PrimeSpectrum F => x a ∈ V) (Subsingleton.elim s b)).mp hxV
  · exact ((affineRectangleClasses f t U i p r hU 4).symm.map_eq_zero_iff).mp hz

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

#print axioms CycleQ2RectangularTrace.refine_zero_to_frame

#print axioms CycleQ2RectangularTrace.supportedRepresentative_restrict
