import Proposal.GeometricMonicGenericSupport
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.GroupTheory.QuotientGroup.Basic
import Proposal.GeometricSupportedHypercohomology
import Proposal.GeometricThreeOpenH2Surjectivity

/-! The two-open Čech cokernel computes the second Ext group of the support quotient and identifies its induced differential.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false

noncomputable section

section
namespace CycleQ2SupportedCechExt
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf freeOpen freeOpenMap freeOpenSections Sections)
open CycleQ2RelativeOpenSupport (sequence quotient shortExact)

variable {X : TopCat.{0}}
local instance : HasExt.{1} (AbSheaf X) := HasExt.standard _
variable (S : (Opens.grothendieckTopology X).MayerVietorisSquare)
variable {W : Opens X} (h : S.X₄ ≤ W) (F : AbSheaf X)

def overlapBoundary : (Sections F S.X₂ × Sections F S.X₃) →+ Sections F S.X₁ where
  toFun s := F.obj.map S.f₁₂.op s.1 - F.obj.map S.f₁₃.op s.2
  map_zero' := by simp
  map_add' s t := by simp only [Prod.fst_add,Prod.snd_add,map_add]; abel

private def sectionHom {U : Opens X} (s : Sections F U) := (freeOpenSections F U).symm s

private theorem boundary_sectionHom (s : Sections F S.X₂ × Sections F S.X₃) :
    S.shortComplex.f ≫ biprod.desc (sectionHom F s.1) (sectionHom F s.2) =
      sectionHom F (overlapBoundary S F s) := by
  apply (freeOpenSections F S.X₁).injective
  change freeOpenSections F S.X₁
    (biprod.lift (freeOpenMap S.f₁₂.le) (-(freeOpenMap S.f₁₃.le)) ≫ _) = _
  erw [biprod.lift_desc, Preadditive.neg_comp, map_add, map_neg,
    CycleQ2InjectiveCech.freeOpenSections_naturality F S.f₁₂.le (sectionHom F s.1),
    CycleQ2InjectiveCech.freeOpenSections_naturality F S.f₁₃.le (sectionHom F s.2)]
  simp [sectionHom, overlapBoundary, sub_eq_add_neg]
  rfl

/-- The actual two connecting morphisms send a section on the intersection
 to the Ext group represented by the relative supported source. -/
def doubleConnecting : Sections F S.X₁ →+ Ext (quotient h) F 2 :=
  ((shortExact h).extClass.precomp F (show 1+1=2 by rfl)).comp
    ((S.shortComplex_shortExact.extClass.precomp F (show 1+0=1 by rfl)).comp
      (Ext.addEquiv₀.symm.toAddMonoidHom.comp (freeOpenSections F S.X₁).symm.toAddMonoidHom))

private theorem doubleConnecting_apply (s : Sections F S.X₁) :
    doubleConnecting S h F s = (shortExact h).extClass.comp
      (S.shortComplex_shortExact.extClass.comp (Ext.mk₀ (sectionHom F s)) rfl) rfl := rfl

private theorem middle_subsingleton (n : ℕ) (h₂ : Subsingleton (Ext (freeOpen S.X₂) F n))
    (h₃ : Subsingleton (Ext (freeOpen S.X₃) F n)) : Subsingleton (Ext S.shortComplex.X₂ F n) := by
  constructor
  intro x y
  exact Ext.biprod_ext (h₂.elim _ _) (h₃.elim _ _)

theorem connecting_surjective
    (ha : Subsingleton (Ext (freeOpen W) F 2))
    (hb : Subsingleton (Ext (freeOpen S.X₂) F 1))
    (hc : Subsingleton (Ext (freeOpen S.X₃) F 1)) : Function.Surjective (doubleConnecting S h F) := by
  intro u
  obtain ⟨v,hv⟩ := Ext.contravariant_sequence_exact₃ (shortExact h) F u (ha.elim _ _) (rfl : 1+1=2)
  obtain ⟨p,hp⟩ := Ext.contravariant_sequence_exact₃ S.shortComplex_shortExact F v
    ((middle_subsingleton S F 1 hb hc).elim _ _) (rfl : 1+0=1)
  obtain ⟨p,rfl⟩ := (Ext.mk₀_bijective _ _).surjective p
  refine ⟨freeOpenSections F S.X₁ p, ?_⟩
  erw [doubleConnecting_apply, sectionHom, (freeOpenSections F S.X₁).symm_apply_apply p, hp, hv]

theorem ker_connecting (ha : Subsingleton (Ext (freeOpen W) F 1)) :
    (doubleConnecting S h F).ker = (overlapBoundary S F).range := by
  ext s
  change doubleConnecting S h F s = 0 ↔ ∃ z, overlapBoundary S F z = s
  constructor
  · intro hs
    let p := Ext.mk₀ (sectionHom F s)
    let v := S.shortComplex_shortExact.extClass.comp p (rfl : 1+0=1)
    obtain ⟨b,hb⟩ := Ext.contravariant_sequence_exact₁ (shortExact h) F v rfl hs
    have hv : v = 0 := by rw [← hb, ha.elim b 0]; exact Ext.comp_zero ..
    obtain ⟨a,ha'⟩ := Ext.contravariant_sequence_exact₁ S.shortComplex_shortExact F p rfl hv
    obtain ⟨a,rfl⟩ := (Ext.mk₀_bijective _ _).surjective a
    have hp : S.shortComplex.f ≫ a = sectionHom F s :=
      (Ext.mk₀_bijective _ _).injective ((Ext.mk₀_comp_mk₀ _ _).symm.trans ha')
    let z := (freeOpenSections F S.X₂ (biprod.inl ≫ a), freeOpenSections F S.X₃ (biprod.inr ≫ a))
    refine ⟨z, (freeOpenSections F S.X₁).symm.injective ?_⟩
    change sectionHom F (overlapBoundary S F z) = sectionHom F s
    rw [← boundary_sectionHom, ← hp]
    congr 1
    simp only [sectionHom, z, AddEquiv.symm_apply_apply]
    exact biprod.hom_ext' _ _ (biprod.inl_desc _ _) (biprod.inr_desc _ _)
  · rintro ⟨z,rfl⟩
    erw [doubleConnecting_apply, ← boundary_sectionHom, ← Ext.mk₀_comp_mk₀,
      S.shortComplex_shortExact.extClass_comp_assoc, Ext.comp_zero]

/-- The row comparison intertwines coefficient maps with postcomposition in Ext.
 In particular it respects each differential of the de Rham complex. -/
theorem doubleConnecting_natural {G : AbSheaf X} (d : F ⟶ G) (s : Sections F S.X₁) :
    (doubleConnecting S h F s).comp (Ext.mk₀ d) (add_zero _) =
      doubleConnecting S h G (d.hom.app (op S.X₁) s) := by
  have hz : sectionHom F s ≫ d = sectionHom G (d.hom.app (op S.X₁) s) := by
    apply (freeOpenSections G S.X₁).injective
    rw [← CycleQ2CechTwoToDerived.freeOpenSections_postcomp]
    simp only [sectionHom,AddEquiv.apply_symm_apply]; rfl
  let b := S.shortComplex_shortExact.extClass
  let c := (shortExact h).extClass
  let z := Ext.mk₀ (sectionHom F s)
  let t := Ext.mk₀ d
  change (c.comp (b.comp z rfl) rfl).comp t (add_zero _) = _
  erw [Ext.comp_assoc_of_third_deg_zero c (b.comp z rfl) t rfl,
    Ext.comp_assoc_of_third_deg_zero b z t rfl]
  change c.comp (b.comp ((Ext.mk₀ (sectionHom F s)).comp (Ext.mk₀ d) (add_zero _)) rfl) rfl = _
  erw [Ext.mk₀_comp_mk₀ (sectionHom F s) d, hz]; rfl

theorem higher_vanishing (n : ℕ) (hw : Subsingleton (Ext (freeOpen W) F (n+3)))
    (hf : Subsingleton (Ext (freeOpen S.X₂) F (n+2)))
    (hg : Subsingleton (Ext (freeOpen S.X₃) F (n+2)))
    (hi : Subsingleton (Ext (freeOpen S.X₁) F (n+1))) :
    Subsingleton (Ext (quotient h) F (n+3)) := by
  apply subsingleton_of_forall_eq 0
  intro u
  obtain ⟨v,hv⟩ := Ext.contravariant_sequence_exact₃ (shortExact h) F u (hw.elim _ _)
    (show 1+(n+2)=n+3 by omega)
  obtain ⟨y,hy⟩ := Ext.contravariant_sequence_exact₃ S.shortComplex_shortExact F v
    ((middle_subsingleton S F _ hf hg).elim _ _) (show 1+(n+1)=n+2 by omega)
  have hy0 : y = 0 := hi.elim y 0
  have hv0 : v = 0 := by
    rw [←hy,hy0]
    exact Ext.comp_zero ..
  rw [←hv,hv0]
  exact Ext.comp_zero ..

end CycleQ2SupportedCechExt
end

namespace CycleQ2SupportedCechLower
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf freeOpen freeOpenMap freeOpenSections Sections)
open CycleQ2RelativeOpenSupport (sequence quotient shortExact)
variable {X : TopCat.{0}}
local instance : HasExt.{1} (AbSheaf X) := HasExt.standard _
variable (S : (Opens.grothendieckTopology X).MayerVietorisSquare)
variable {W : Opens X} (h : S.X₄ ≤ W) (F : AbSheaf X)

abbrev restrict {U V : Opens X} (h : U ≤ V) := F.obj.map (homOfLE h).op

def toPair (x : Sections F W) : Sections F S.X₂ × Sections F S.X₃ :=
  (restrict F (S.f₂₄.le.trans h) x, restrict F (S.f₃₄.le.trans h) x)

private theorem pair_restrict (x : Sections F W) :
    (F.obj.map S.f₂₄.op (restrict F h x), F.obj.map S.f₃₄.op (restrict F h x)) =
      toPair S h F x := by
  apply Prod.ext <;> exact (ConcreteCategory.congr_hom (F.obj.map_comp _ _) x).symm

/-- If the augmented row of affine sections is exact in its first two
 terms, the ambient restriction to the open complement is bijective. -/
theorem restriction_bijective (hi : Function.Injective (toPair S h F))
    (he : ∀ u : Sections F S.X₂ × Sections F S.X₃,
      CycleQ2SupportedCechExt.overlapBoundary S F u = 0 → ∃ x, toPair S h F x = u) :
    Function.Bijective (restrict F h) := by
  let P := (sheafCompose _ (forget AddCommGrpCat)).obj F
  have hc := S.sheafCondition_of_sheaf P
  constructor
  · intro x y e
    apply hi
    rw [← pair_restrict, ← pair_restrict, e]
  · intro s
    let u := (F.obj.map S.f₂₄.op s, F.obj.map S.f₃₄.op s)
    have hs : CycleQ2SupportedCechExt.overlapBoundary S F u = 0 := by
      apply sub_eq_zero.mpr
      change F.obj.map S.f₁₂.op (F.obj.map S.f₂₄.op s) = F.obj.map S.f₁₃.op (F.obj.map S.f₃₄.op s)
      erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← F.obj.map_comp, ← F.obj.map_comp]
      rfl
    obtain ⟨x,hx⟩ := he u hs
    rw [← pair_restrict] at hx
    exact ⟨x,hc.ext (congrArg Prod.fst hx) (congrArg Prod.snd hx)⟩

/-- In degree zero, a class is a section on the ambient open vanishing
 on the complement, so injectivity of restriction kills it. -/
theorem supported_zero_vanishing (hi : Function.Injective (restrict F h)) :
    Subsingleton (Ext (quotient h) F 0) := by
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨a,rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
  apply (Ext.mk₀_eq_zero_iff _).mpr
  apply (cancel_epi (sequence h).g).mp
  rw [comp_zero]
  apply (freeOpenSections F W).injective
  erw [map_zero]
  apply hi
  erw [map_zero]
  erw [← CycleQ2InjectiveCech.freeOpenSections_naturality, ← Category.assoc,
    (sequence h).zero, zero_comp, map_zero]

/-- In degree one, restriction surjectivity and ambient positive-degree
 acyclicity kill the next supported Ext group. -/
theorem supported_one_vanishing (hs : Function.Surjective (restrict F h))
    (hw : Subsingleton (Ext (freeOpen W) F 1)) : Subsingleton (Ext (quotient h) F 1) := by
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨y,hy⟩ := Ext.contravariant_sequence_exact₃ (shortExact h) F x (hw.elim _ _) (rfl : 1+0=1)
  obtain ⟨a,rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
  obtain ⟨s,hs⟩ := hs (freeOpenSections F S.X₄ a)
  let b := (freeOpenSections F W).symm s
  have hab : freeOpenMap h ≫ b = a := by
    apply (freeOpenSections F S.X₄).injective
    rw [CycleQ2InjectiveCech.freeOpenSections_naturality]
    exact (congrArg (restrict F h) ((freeOpenSections F W).apply_symm_apply s)).trans hs
  rw [←hy, ←hab]
  erw [← Ext.mk₀_comp_mk₀ (freeOpenMap h) b]
  exact (shortExact h).extClass_comp_assoc _

end CycleQ2SupportedCechLower

namespace CycleQ2SupportedExtComplex
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf Sections freeOpen)
open CycleQ2RelativeOpenSupport (quotient)
open CycleQ2SupportedCechExt
variable {X : TopCat.{0}}
local instance : HasExt.{1} (AbSheaf X) := HasExt.standard _
variable (S : (Opens.grothendieckTopology X).MayerVietorisSquare)
    {W : Opens X} (h : S.X₄ ≤ W) (K : CochainComplex (AbSheaf X) ℤ)

/-- On an augmented affine cover, exactness in the horizontal direction of
 the degree-two supported Ext row is exactly closed-implies-exact on actual
 doubly-localized representatives, with boundaries from the two single opens. -/
theorem E2_exactAt_iff (i : ℤ)
    (hw₁ : ∀ j, Subsingleton (Ext (freeOpen W) (K.X j) 1))
    (hw₂ : ∀ j, Subsingleton (Ext (freeOpen W) (K.X j) 2))
    (hu : ∀ j, Subsingleton (Ext (freeOpen S.X₂) (K.X j) 1))
    (hv : ∀ j, Subsingleton (Ext (freeOpen S.X₃) (K.X j) 1)) :
    (E (quotient h) 2 K).ExactAt i ↔
      ∀ s : Sections (K.X i) S.X₁, (K.dFrom i).hom.app (op S.X₁) s ∈ (overlapBoundary S (K.xNext i)).range →
        ∃ t : Sections (K.xPrev i) S.X₁, s - (K.dTo i).hom.app (op S.X₁) t ∈ (overlapBoundary S (K.X i)).range := by
  have lift (j : ℤ) := connecting_surjective S h (K.X j) (hw₂ j) (hu j) (hv j)
  have ker (j : ℤ) (s : Sections (K.X j) S.X₁) :
      doubleConnecting S h (K.X j) s = 0 ↔ s ∈ (overlapBoundary S (K.X j)).range := by
    change s ∈ (doubleConnecting S h (K.X j)).ker ↔ _
    rw [ker_connecting S h (K.X j) (hw₁ j)]
  rw [HomologicalComplex.ExactAt, ShortComplex.ab_exact_iff]
  change (∀ z : Ext (quotient h) (K.X i) 2, z.comp (Ext.mk₀ (K.dFrom i)) (add_zero 2) = 0 →
    ∃ y : Ext (quotient h) (K.xPrev i) 2, y.comp (Ext.mk₀ (K.dTo i)) (add_zero 2) = z) ↔ _
  constructor
  · intro he s hs
    obtain ⟨y,hy⟩ := he (doubleConnecting S h (K.X i) s) (by rw [doubleConnecting_natural]; exact (ker _ _).mpr hs)
    obtain ⟨t,rfl⟩ := lift _ y
    exact ⟨t,(ker i _).mp (by rw [map_sub, ← doubleConnecting_natural, hy, sub_self])⟩
  · intro he z hz
    obtain ⟨s,rfl⟩ := lift i z
    rw [doubleConnecting_natural] at hz
    obtain ⟨t,ht⟩ := he s ((ker _ _).mp hz)
    refine ⟨doubleConnecting S h _ t, ?_⟩
    rw [doubleConnecting_natural]
    have eq := (ker i _).mpr ht
    rw [map_sub, sub_eq_zero] at eq
    exact eq.symm

end CycleQ2SupportedExtComplex

/-! The corresponding row for three opens in an affine ambient open.
The map is the original three-open Mayer--Vietoris class followed by
the boundary of the actual relative support sequence. -/

namespace CycleQ2ThreeOpenSupportedCechExt

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf freeOpen Sections)
open CycleQ2RelativeOpenSupport (quotient shortExact)
open CycleQ2ThreeOpenCechH2 (TripleOpen outerSquare)

variable {X : TopCat.{0}}
local instance : HasExt.{1} (AbSheaf X) := HasExt.standard _
variable (U V T : Opens X) {W : Opens X} (h : (U ⊔ V) ⊔ T ≤ W) (F : AbSheaf X)

abbrev boundary := CycleQ2ThreeOpenSectionH2.boundary F U V T

/-- Three genuine source connecting maps, with the original +−+
restriction boundary on the three pair intersections. -/
def tripleConnecting : Sections F (TripleOpen U V T) →+ Ext (quotient h) F 3 :=
  ((shortExact h).extClass.precomp F (show 1+2=3 by rfl)).comp
    (CycleQ2ThreeOpenSectionH2.connecting F U V T)

theorem tripleConnecting_apply (s : Sections F (TripleOpen U V T)) :
    tripleConnecting U V T h F s = (shortExact h).extClass.comp
      (CycleQ2ThreeOpenSectionH2.connecting F U V T s) rfl := rfl

theorem tripleConnecting_boundary
    (s : Sections F (U ⊓ V) × Sections F (U ⊓ T) × Sections F (V ⊓ T)) :
    tripleConnecting U V T h F (boundary U V T F s) = 0 := by
  rw [tripleConnecting_apply, CycleQ2ThreeOpenSectionH2.connecting_boundary]
  exact Ext.comp_zero ..

theorem connecting_surjective
    (hw : Subsingleton (Ext (freeOpen W) F 3))
    (hU : Subsingleton (F.H' 2 U)) (hV : Subsingleton (F.H' 2 V))
    (hT : Subsingleton (F.H' 2 T))
    (hUV : Subsingleton (F.H' 1 (U ⊓ V)))
    (hUT : Subsingleton (F.H' 1 (U ⊓ T)))
    (hVT : Subsingleton (F.H' 1 (V ⊓ T))) :
    Function.Surjective (tripleConnecting U V T h F) := by
  letI := hU
  letI := hV
  letI := hT
  letI := hUV
  letI := hUT
  letI := hVT
  intro x
  obtain ⟨y,hy⟩ := Ext.contravariant_sequence_exact₃ (shortExact h) F x
    (hw.elim _ _) (rfl : 1+2=3)
  obtain ⟨s,hs⟩ := CycleQ2ThreeOpenH2Surjectivity.connecting_surjective F U V T y
  refine ⟨s,?_⟩
  rw [tripleConnecting_apply,hs,hy]

theorem ker_connecting
    (hw : Subsingleton (Ext (freeOpen W) F 2))
    (hU : Subsingleton (F.H' 1 U)) (hV : Subsingleton (F.H' 1 V))
    (hT : Subsingleton (F.H' 1 T)) :
    (tripleConnecting U V T h F).ker = (boundary U V T F).range := by
  letI := hU
  letI := hV
  letI := hT
  ext s
  change tripleConnecting U V T h F s = 0 ↔ ∃ z, boundary U V T F z = s
  constructor
  · intro hs
    rw [tripleConnecting_apply] at hs
    obtain ⟨b,hb⟩ := Ext.contravariant_sequence_exact₁ (shortExact h) F
      (CycleQ2ThreeOpenSectionH2.connecting F U V T s) rfl hs
    have hz : CycleQ2ThreeOpenSectionH2.connecting F U V T s = 0 := by
      rw [← hb,hw.elim b 0]
      exact Ext.comp_zero ..
    obtain ⟨a,b,c,hc⟩ := (CycleQ2ThreeOpenSectionH2.connecting_eq_zero_iff F U V T s).mp hz
    exact ⟨(a,b,c),hc⟩
  · rintro ⟨z,rfl⟩
    exact tripleConnecting_boundary U V T h F z

/-- The actual row map commutes with every coefficient morphism,
including each differential of the de Rham complex. -/
theorem tripleConnecting_natural {G : AbSheaf X} (d : F ⟶ G)
    (s : Sections F (TripleOpen U V T)) :
    (tripleConnecting U V T h F s).comp (Ext.mk₀ d) (add_zero 3) =
      tripleConnecting U V T h G (d.hom.app (op (TripleOpen U V T)) s) := by
  have hd := CycleQ2ThreeOpenH2Naturality.connecting_naturality d U V T s
  change (CycleQ2ThreeOpenSectionH2.connecting F U V T s).comp (Ext.mk₀ d)
    (add_zero 2) = CycleQ2ThreeOpenSectionH2.connecting G U V T
      (d.hom.app (op (TripleOpen U V T)) s) at hd
  rw [tripleConnecting_apply, tripleConnecting_apply,
    Ext.comp_assoc_of_third_deg_zero, hd]

abbrev SectionQuotient := Sections F (TripleOpen U V T) ⧸ (boundary U V T F).range

def toSupportedH3 : SectionQuotient U V T F →+ Ext (quotient h) F 3 :=
  QuotientAddGroup.lift (boundary U V T F).range (tripleConnecting U V T h F)
    (by rintro _ ⟨s,rfl⟩; exact tripleConnecting_boundary U V T h F s)

theorem toSupportedH3_injective
    (hw : Subsingleton (Ext (freeOpen W) F 2))
    (hU : Subsingleton (F.H' 1 U)) (hV : Subsingleton (F.H' 1 V))
    (hT : Subsingleton (F.H' 1 T)) : Function.Injective (toSupportedH3 U V T h F) :=
  (QuotientAddGroup.injective_lift_iff _ _ _).2
    (ker_connecting U V T h F hw hU hV hT).symm

theorem toSupportedH3_surjective
    (hw : Subsingleton (Ext (freeOpen W) F 3))
    (hU : Subsingleton (F.H' 2 U)) (hV : Subsingleton (F.H' 2 V))
    (hT : Subsingleton (F.H' 2 T))
    (hUV : Subsingleton (F.H' 1 (U ⊓ V)))
    (hUT : Subsingleton (F.H' 1 (U ⊓ T)))
    (hVT : Subsingleton (F.H' 1 (V ⊓ T))) :
    Function.Surjective (toSupportedH3 U V T h F) := by
  intro y
  obtain ⟨s,hs⟩ := connecting_surjective U V T h F hw hU hV hT hUV hUT hVT y
  exact ⟨QuotientAddGroup.mk s,hs⟩

/-- The native triple-overlap quotient is the actual supported third
Ext group through these original connecting maps. -/
def toSupportedH3Equiv
    (hw₂ : Subsingleton (Ext (freeOpen W) F 2))
    (hw₃ : Subsingleton (Ext (freeOpen W) F 3))
    (hU₁ : Subsingleton (F.H' 1 U)) (hV₁ : Subsingleton (F.H' 1 V))
    (hT₁ : Subsingleton (F.H' 1 T))
    (hU₂ : Subsingleton (F.H' 2 U)) (hV₂ : Subsingleton (F.H' 2 V))
    (hT₂ : Subsingleton (F.H' 2 T))
    (hUV : Subsingleton (F.H' 1 (U ⊓ V)))
    (hUT : Subsingleton (F.H' 1 (U ⊓ T)))
    (hVT : Subsingleton (F.H' 1 (V ⊓ T))) :
    SectionQuotient U V T F ≃+ Ext (quotient h) F 3 :=
  AddEquiv.ofBijective (toSupportedH3 U V T h F)
    ⟨toSupportedH3_injective U V T h F hw₂ hU₁ hV₁ hT₁,
      toSupportedH3_surjective U V T h F hw₃ hU₂ hV₂ hT₂ hUV hUT hVT⟩

private theorem square_vanishing
    (S : (Opens.grothendieckTopology X).MayerVietorisSquare) (n : ℕ)
    (hi : Subsingleton (Ext (freeOpen S.X₁) F n))
    (h₂ : Subsingleton (Ext (freeOpen S.X₂) F (n+1)))
    (h₃ : Subsingleton (Ext (freeOpen S.X₃) F (n+1))) :
    Subsingleton (Ext (freeOpen S.X₄) F (n+1)) := by
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨y,hy⟩ := Ext.contravariant_sequence_exact₃ S.shortComplex_shortExact F x
    ((CycleQ2SupportedCechExt.middle_subsingleton S F (n+1) h₂ h₃).elim _ _)
    (show 1+n=n+1 by omega)
  rw [← hy,hi.elim y 0]
  exact Ext.comp_zero ..

/-- Positive affine cohomology on all faces kills every supported row
above the actual third row. -/
theorem higher_vanishing (n : ℕ)
    (hw : Subsingleton (Ext (freeOpen W) F (n+4)))
    (hU : Subsingleton (F.H' (n+3) U)) (hV : Subsingleton (F.H' (n+3) V))
    (hT : Subsingleton (F.H' (n+3) T))
    (hUV : Subsingleton (F.H' (n+2) (U ⊓ V)))
    (hUT : Subsingleton (F.H' (n+2) (U ⊓ T)))
    (hVT : Subsingleton (F.H' (n+2) (V ⊓ T)))
    (hUVT : Subsingleton (F.H' (n+1) (TripleOpen U V T))) :
    Subsingleton (Ext (quotient h) F (n+4)) := by
  have huv := square_vanishing F (Opens.mayerVietorisSquare U V) (n+2) hUV hU hV
  have hint := square_vanishing F (Opens.mayerVietorisSquare (U ⊓ T) (V ⊓ T))
    (n+1) hUVT hUT hVT
  have hcomp := square_vanishing F (outerSquare U V T) (n+2) hint huv hT
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨y,hy⟩ := Ext.contravariant_sequence_exact₃ (shortExact h) F x (hw.elim _ _)
    (show 1+(n+3)=n+4 by omega)
  rw [← hy,hcomp.elim y 0]
  exact Ext.comp_zero ..

/-- The lower second row vanishes once the genuine first cohomology of
the open complement and the ambient second group vanish. -/
theorem supported_two_vanishing
    (hw : Subsingleton (Ext (freeOpen W) F 2))
    (hc : Subsingleton (F.H' 1 ((U ⊔ V) ⊔ T))) :
    Subsingleton (Ext (quotient h) F 2) := by
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨y,hy⟩ := Ext.contravariant_sequence_exact₃ (shortExact h) F x (hw.elim _ _)
    (rfl : 1+1=2)
  rw [← hy,hc.elim y 0]
  exact Ext.comp_zero ..

end CycleQ2ThreeOpenSupportedCechExt

namespace CycleQ2SupportedExtComplex

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf Sections freeOpen)
open CycleQ2RelativeOpenSupport (quotient)
open CycleQ2ThreeOpenCechH2 (TripleOpen)
open CycleQ2ThreeOpenSupportedCechExt

variable {X : TopCat.{0}}
local instance : HasExt.{1} (AbSheaf X) := HasExt.standard _
variable (U V T : Opens X) {W : Opens X} (h : (U ⊔ V) ⊔ T ≤ W)
  (K : CochainComplex (AbSheaf X) ℤ)

/-- Exactness of the actual third supported Ext row is precisely
closed-implies-exact for triple-overlap forms modulo the three original
pair restrictions. -/
theorem E3_exactAt_iff (i : ℤ)
    (hw₂ : ∀ j, Subsingleton (Ext (freeOpen W) (K.X j) 2))
    (hw₃ : ∀ j, Subsingleton (Ext (freeOpen W) (K.X j) 3))
    (hU₁ : ∀ j, Subsingleton ((K.X j).H' 1 U))
    (hV₁ : ∀ j, Subsingleton ((K.X j).H' 1 V))
    (hT₁ : ∀ j, Subsingleton ((K.X j).H' 1 T))
    (hU₂ : ∀ j, Subsingleton ((K.X j).H' 2 U))
    (hV₂ : ∀ j, Subsingleton ((K.X j).H' 2 V))
    (hT₂ : ∀ j, Subsingleton ((K.X j).H' 2 T))
    (hUV : ∀ j, Subsingleton ((K.X j).H' 1 (U ⊓ V)))
    (hUT : ∀ j, Subsingleton ((K.X j).H' 1 (U ⊓ T)))
    (hVT : ∀ j, Subsingleton ((K.X j).H' 1 (V ⊓ T))) :
    (E (quotient h) 3 K).ExactAt i ↔
      ∀ s : Sections (K.X i) (TripleOpen U V T),
        (K.dFrom i).hom.app (op (TripleOpen U V T)) s ∈
          (boundary U V T (K.xNext i)).range →
        ∃ t : Sections (K.xPrev i) (TripleOpen U V T),
          s - (K.dTo i).hom.app (op (TripleOpen U V T)) t ∈
            (boundary U V T (K.X i)).range := by
  have lift (j : ℤ) := connecting_surjective U V T h (K.X j) (hw₃ j)
    (hU₂ j) (hV₂ j) (hT₂ j) (hUV j) (hUT j) (hVT j)
  have ker (j : ℤ) (s : Sections (K.X j) (TripleOpen U V T)) :
      tripleConnecting U V T h (K.X j) s = 0 ↔
        s ∈ (boundary U V T (K.X j)).range := by
    change s ∈ (tripleConnecting U V T h (K.X j)).ker ↔ _
    rw [ker_connecting U V T h (K.X j) (hw₂ j) (hU₁ j) (hV₁ j) (hT₁ j)]
  rw [HomologicalComplex.ExactAt, ShortComplex.ab_exact_iff]
  change (∀ z : Ext (quotient h) (K.X i) 3,
    z.comp (Ext.mk₀ (K.dFrom i)) (add_zero 3) = 0 →
      ∃ y : Ext (quotient h) (K.xPrev i) 3,
        y.comp (Ext.mk₀ (K.dTo i)) (add_zero 3) = z) ↔ _
  constructor
  · intro he s hs
    obtain ⟨y,hy⟩ := he (tripleConnecting U V T h (K.X i) s) (by
      rw [tripleConnecting_natural]
      exact (ker _ _).mpr hs)
    obtain ⟨t,rfl⟩ := lift _ y
    refine ⟨t,(ker i _).mp ?_⟩
    rw [map_sub, ← tripleConnecting_natural, hy, sub_self]
  · intro he z hz
    obtain ⟨s,rfl⟩ := lift i z
    rw [tripleConnecting_natural] at hz
    obtain ⟨t,ht⟩ := he s ((ker _ _).mp hz)
    refine ⟨tripleConnecting U V T h _ t,?_⟩
    rw [tripleConnecting_natural]
    have ht' := (ker i _).mpr ht
    rw [map_sub, sub_eq_zero] at ht'
    exact ht'.symm

end CycleQ2SupportedExtComplex

#print axioms CycleQ2ThreeOpenSupportedCechExt.toSupportedH3Equiv
#print axioms CycleQ2ThreeOpenSupportedCechExt.higher_vanishing
#print axioms CycleQ2SupportedExtComplex.E3_exactAt_iff
