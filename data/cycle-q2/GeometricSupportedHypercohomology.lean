import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.Factorizations.CM5a
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-! Two injective resolutions reduce low-degree supported hypercohomology to the surviving Ext row.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false

noncomputable section

namespace CycleQ2FourTermHomologyShift
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C : Type*} [Category* C] [Abelian C]
variable {A B D E : CochainComplex C ℤ} (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E)
    (hab : a ≫ b = 0) (hbc : b ≫ c = 0)

/-- If `0 → A → B → D → E → 0` is exact with acyclic `B` and `D`,
 two connecting homomorphisms identify `Hⁿ(E)` with `Hⁿ⁺²(A)`. -/
def homologyShift [Mono a] [Epi c] (h₁ : (ShortComplex.mk a b hab).Exact)
    (h₂ : (ShortComplex.mk b c hbc).Exact) (hB : B.Acyclic) (hD : D.Acyclic) (n : ℤ) :
    E.homology n ≅ A.homology (n+2) := by
  let S := ShortComplex.cokernelSequence a
  have hS : S.ShortExact := {
    exact := ShortComplex.cokernelSequence_exact a
    mono_f := inferInstanceAs (Mono a)
    epi_g := inferInstanceAs (Epi (cokernel.π a)) }
  let i := cokernel.desc a b hab
  have hi : Mono i := h₁.mono_cokernelDesc
  have hic : i ≫ c = 0 := by
    apply (cancel_epi (cokernel.π a)).mp
    simp [i,←Category.assoc,hbc]
  let T := ShortComplex.mk i c hic
  let φ : ShortComplex.mk b c hbc ⟶ T :=
    ShortComplex.homMk (cokernel.π a) (𝟙 D) (𝟙 E) (by simp [T,i]) (by simp [T])
  letI : Epi φ.τ₁ := inferInstanceAs (Epi (cokernel.π a))
  letI : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 D))
  letI : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 E))
  have hT : T.ShortExact := {
    exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp h₂
    mono_f := hi
    epi_g := inferInstanceAs (Epi c) }
  exact hT.δIso n (n+1) (by simp) (hD n).isZero_homology (hD (n+1)).isZero_homology ≪≫
    hS.δIso (n+1) (n+2) (by change n+1+1=n+2; omega) (hB (n+1)).isZero_homology
      (hB (n+2)).isZero_homology

end CycleQ2FourTermHomologyShift

namespace CycleQ2SupportedExtComplex
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] (P : C)

abbrev E (n : ℕ) (K : CochainComplex C ℤ) : CochainComplex AddCommGrpCat.{w} ℤ :=
  ((extFunctorObj P n).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

variable {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
private abbrev ev (i : ℤ) := HomologicalComplex.eval C (ComplexShape.up ℤ) i

private def diff (S : ShortComplex (CochainComplex C ℤ)) (i j : ℤ) : S.map (ev i) ⟶ S.map (ev j) where
  τ₁ := S.X₁.d i j
  τ₂ := S.X₂.d i j
  τ₃ := S.X₃.d i j
  comm₁₂ := (S.f.comm i j).symm
  comm₂₃ := (S.g.comm i j).symm

/-- The connecting map of a short exact sequence in each complex degree,
 with the original differentials on its source and target. -/
def delta (n : ℕ) : E P n S.X₃ ⟶ E P (n+1) S.X₁ where
  f i := AddCommGrpCat.ofHom ((hS.map_of_exact (ev i)).extClass.postcomp P rfl)
  comm' i j _ := by
    ext z
    change Ext P (S.X₃.X i) n at z
    change (z.comp (hS.map_of_exact (ev i)).extClass rfl).comp (Ext.mk₀ (S.X₁.d i j)) (add_zero _) =
      (z.comp (Ext.mk₀ (S.X₃.d i j)) (add_zero _)).comp (hS.map_of_exact (ev j)).extClass rfl
    refine Eq.trans (Ext.comp_assoc_of_third_deg_zero z _ _ rfl) (Eq.trans ?_ (Ext.comp_assoc_of_second_deg_zero z _ _ rfl).symm)
    exact congrArg (fun x : Ext (S.X₃.X i) (S.X₁.X j) 1 => z.comp x rfl)
      ((hS.map_of_exact (ev i)).extClass_naturality (hS.map_of_exact (ev j)) (diff S i j))

/-- Dimension shifting is natural in the cochain degree for a termwise
 injective middle complex. -/
def deltaIso (n : ℕ) (hI : ∀ j, Injective (S.X₂.X j)) : E P (n+1) S.X₃ ≅ E P (n+2) S.X₁ := by
  have iso (i : ℤ) : IsIso ((delta P hS (n+1)).f i) := by
    let Y := S.map (ev i)
    have hY : Y.ShortExact := hS.map_of_exact _
    let _ : Injective Y.X₂ := hI i
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    change Function.Bijective (hY.extClass.postcomp P (rfl : n+1+1 = n+2))
    constructor
    · apply (injective_iff_map_eq_zero _).mpr
      intro z hz
      obtain ⟨a,ha⟩ := Ext.covariant_sequence_exact₃ P hY z rfl hz
      rw [← ha, Ext.eq_zero_of_injective a, Ext.zero_comp]
    · exact fun z => Ext.covariant_sequence_exact₁ P hY z (Ext.eq_zero_of_injective _) rfl
  let _ : IsIso (delta P hS (n+1)) := HomologicalComplex.Hom.isIso_of_components _
  exact asIso (delta P hS (n+1))

end CycleQ2SupportedExtComplex

namespace CycleQ2SupportedCosyzygy
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open CycleQ2SupportedExtComplex
universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] (P : C)

abbrev EFunctor (n : ℕ) := (extFunctorObj P n).mapHomologicalComplex (ComplexShape.up ℤ)
private abbrev ev (j : ℤ) := HomologicalComplex.eval C (ComplexShape.up ℤ) j
variable {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)

/-- The map on sections from a complex of injectives to the first cosyzygy
 is an isomorphism as soon as the first two Ext rows of the kernel vanish. -/
def firstIso (h₀ : ∀ j, Subsingleton (Ext P (S.X₁.X j) 0))
    (h₁ : ∀ j, Subsingleton (Ext P (S.X₁.X j) 1)) : E P 0 S.X₂ ≅ E P 0 S.X₃ := by
  let f := (EFunctor P 0).map S.g
  have (j : ℤ) : IsIso (f.f j) := by
    let H := hS.map_of_exact (ev j)
    have he := Ext.covariant_sequence_exact₂' P H 0
    have hf := Ext.covariant_sequence_exact₃' P H 0 1 rfl
    have hm : Mono (f.f j) := he.mono_g_iff.mpr
      ((AddCommGrpCat.isZero_iff_subsingleton.mpr (h₀ j)).eq_of_src _ _)
    have hp : Epi (f.f j) := hf.epi_f_iff.mpr
      ((AddCommGrpCat.isZero_iff_subsingleton.mpr (h₁ j)).eq_of_tgt _ _)
    exact isIso_of_mono_of_epi _
  letI : IsIso f := HomologicalComplex.Hom.isIso_of_components _
  exact asIso f

/-- The second cosyzygy produces a four-term exact sequence of complexes
 `0 → E⁰(R) → E⁰(J) → E⁰(B) → E¹(R) → 0`. The two middle terms are acyclic
 in the application. -/
def secondShift (hJ : ∀ i, Injective (S.X₂.X i)) (h₂ : (E P 0 S.X₂).Acyclic)
    (h₃ : (E P 0 S.X₃).Acyclic) (n : ℤ) :
    (E P 1 S.X₁).homology n ≅ (E P 0 S.X₁).homology (n+2) := by
  let a := (EFunctor P 0).map S.f
  let b := (EFunctor P 0).map S.g
  let c := delta P hS 0
  have hab : a ≫ b = 0 := by rw [← Functor.map_comp, S.zero, Functor.map_zero]
  have hbc : b ≫ c = 0 := by
    ext j z
    change (z.comp (Ext.mk₀ (S.g.f j)) (add_zero 0)).comp (hS.map_of_exact (ev j)).extClass rfl = 0
    erw [Ext.comp_assoc_of_second_deg_zero, (hS.map_of_exact (ev j)).comp_extClass, Ext.comp_zero]
  letI : Mono a := HomologicalComplex.mono_of_mono_f _ fun j => by
    let : Mono (S.f.f j) := (hS.map_of_exact (ev j)).mono_f
    exact Ext.mono_postcomp_mk₀_of_mono P (S.f.f j)
  letI : Epi c := HomologicalComplex.epi_of_epi_f _ fun j => by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    intro z
    let := hJ j
    exact Ext.covariant_sequence_exact₁ P (hS.map_of_exact (ev j)) z
      ((Ext.subsingleton_of_injective P (S.X₂.X j) 0).elim _ _) rfl
  apply CycleQ2FourTermHomologyShift.homologyShift a b c hab hbc _ _ h₂ h₃ n
  · apply exact_of_degreewise_exact
    exact fun j => Ext.covariant_sequence_exact₂' P (hS.map_of_exact (ev j)) 0
  · apply exact_of_degreewise_exact
    exact fun j => Ext.covariant_sequence_exact₃' P (hS.map_of_exact (ev j)) 0 1 rfl

end CycleQ2SupportedCosyzygy

namespace CycleQ2SupportedTwoResolutions
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open CycleQ2SupportedExtComplex CycleQ2SupportedCosyzygy
universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] [EnoughInjectives C]
variable (P : C) (K : CochainComplex C ℤ) (b : ℤ) [K.IsStrictlyGE b]

omit [HasExt.{w} C] [EnoughInjectives C] in
private theorem bounded_quotient {L M : CochainComplex C ℤ} (f : L ⟶ M) (j : ℤ)
    [M.IsStrictlyGE j] : (cokernel f).IsStrictlyGE j := by
  have H (i : ℤ) : Epi ((cokernel.π f).f i) := inferInstance
  apply ((cokernel f).isStrictlyGE_iff j).2
  intro i hi
  exact IsZero.of_epi_eq_zero _ ((M.isZero_of_isStrictlyGE j i hi).eq_of_src ((cokernel.π f).f i) 0)

/-- Assuming that ordinary sections preserve exactness for bounded-below
 complexes with acyclic terms, construct an injective resolution of `K`
 on which the supported Ext cohomology shift is explicit. -/
theorem exists_resolution_with_shift
    (h₀ : ∀ j, Subsingleton (Ext P (K.X j) 0)) (h₁ : ∀ j, Subsingleton (Ext P (K.X j) 1))
    (hhi : ∀ j n, Subsingleton (Ext P (K.X j) (n+3)))
    (sections_acyclic : ∀ (M : CochainComplex C ℤ) (c : ℤ), M.IsStrictlyGE c → M.Acyclic →
      (∀ i n, Subsingleton (Ext P (M.X i) (n+1))) → (E P 0 M).Acyclic) :
    ∃ (I : CochainComplex C ℤ) (f : K ⟶ I), QuasiIso f ∧
      (∀ i, Injective (I.X i)) ∧ I.IsStrictlyGE (b-1) ∧
      ∀ n : ℤ, Nonempty ((E P 2 K).homology n ≅ (E P 0 I).homology (n+2)) := by
  obtain ⟨I,f,hm,hq,hI,hBI⟩ := CochainComplex.Plus.modelCategoryQuillen.exists_mono_quasiIso_injective K (b-1) b
  let S := ShortComplex.cokernelSequence f
  have hS : S.ShortExact := {
    exact := ShortComplex.cokernelSequence_exact f
    mono_f := hm
    epi_g := inferInstanceAs (Epi (cokernel.π f)) }
  let R := S.X₃
  have hR : R.Acyclic := hS.acyclic_X₃ hq
  have hBR : R.IsStrictlyGE (b-1) := bounded_quotient f (b-1)
  obtain ⟨J,g,gm,gq,hJ,hBJ⟩ := CochainComplex.Plus.modelCategoryQuillen.exists_mono_quasiIso_injective R (b-2) (b-1)
  let T := ShortComplex.cokernelSequence g
  have hT : T.ShortExact := {
    exact := ShortComplex.cokernelSequence_exact g
    mono_f := gm
    epi_g := inferInstanceAs (Epi (cokernel.π g)) }
  have hJac : J.Acyclic := fun i => (quasiIsoAt_iff_exactAt g i (hR i)).mp inferInstance
  have hBac : T.X₃.Acyclic := hT.acyclic_X₃ gq
  have hBB : T.X₃.IsStrictlyGE (b-2) := bounded_quotient g (b-2)
  have hBE (i : ℤ) (n : ℕ) : Subsingleton (Ext P (T.X₃.X i) (n+1)) := by
    let z := (deltaIso P hT n hJ) ≪≫ (deltaIso P hS (n+1) hI)
    let w := (HomologicalComplex.eval _ _ i).mapIso z
    let U : AddCommGrpCat.{w} := (HomologicalComplex.eval _ _ i).obj (E P (n+1+2) S.X₁)
    have : Subsingleton U := hhi i n
    exact @Function.Injective.subsingleton _ _ w.addCommGroupIsoToAddEquiv w.addCommGroupIsoToAddEquiv.injective this
  have hEJ := sections_acyclic J (b-2) hBJ hJac (fun i n => by
    let := hJ i
    exact Ext.subsingleton_of_injective P (J.X i) n)
  have hEB := sections_acyclic T.X₃ (b-2) hBB hBac hBE
  refine ⟨I,f,hq,hI,hBI,fun n => ⟨?_⟩⟩
  exact (homologyFunctor _ _ n).mapIso (deltaIso P hS 0 hI).symm ≪≫
    secondShift P hT hJ hEJ hEB n ≪≫
    (homologyFunctor _ _ (n+2)).mapIso (firstIso P hS h₀ h₁).symm

end CycleQ2SupportedTwoResolutions

namespace CycleQ2SupportedExtComplex
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] (P : C)

/-- Transfer exactness between the two complexes without identifying their
universes of groups. -/
theorem E0_exactAt_iff (K : CochainComplex C ℤ) (i : ℤ) : (E P 0 K).ExactAt i ↔
    (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).ExactAt i := by
  rw [HomologicalComplex.ExactAt, HomologicalComplex.ExactAt, ShortComplex.ab_exact_iff, ShortComplex.ab_exact_iff]
  change (∀ z : Ext P (K.X i) 0, z.comp (Ext.mk₀ (K.dFrom i)) (add_zero 0) = 0 →
    ∃ t : Ext P (K.xPrev i) 0, t.comp (Ext.mk₀ (K.dTo i)) (add_zero 0) = z) ↔
    (∀ f : P ⟶ K.X i, f ≫ K.dFrom i = 0 → ∃ g : P ⟶ K.xPrev i, g ≫ K.dTo i = f)
  constructor
  · intro h f hf
    obtain ⟨t,ht⟩ := h (Ext.mk₀ f) (by rw [Ext.mk₀_comp_mk₀, hf, Ext.mk₀_zero])
    obtain ⟨g,rfl⟩ := (Ext.mk₀_bijective P _).surjective t
    exact ⟨g,(Ext.mk₀_bijective P _).injective ((Ext.mk₀_comp_mk₀ g _).symm.trans ht)⟩
  · intro h z hz
    obtain ⟨f,rfl⟩ := (Ext.mk₀_bijective P _).surjective z
    rw [Ext.mk₀_comp_mk₀, Ext.mk₀_eq_zero_iff] at hz
    obtain ⟨g,hg⟩ := h f hz
    exact ⟨Ext.mk₀ g,(Ext.mk₀_comp_mk₀ g _).trans (congrArg Ext.mk₀ hg)⟩

end CycleQ2SupportedExtComplex

namespace CycleQ2AcyclicComplexSections

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open HomologicalComplex

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- Acyclicity for the covariant functor represented by P. -/
def AcyclicFor (P M : C) : Prop := ∀ n : ℕ, Subsingleton (Ext P M (n + 1))

variable (K : CochainComplex C ℕ)

end CycleQ2AcyclicComplexSections

namespace CycleQ2AffineHypercohomologyComparison
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite HomologicalComplex
open CycleQ2AcyclicComplexSections
universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
private abbrev sections (P : C) := preadditiveCoyoneda.obj (op P)
abbrev sectionComplex (P : C) := (preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)

private theorem acyclic_coker (P : C) {S : ShortComplex C} (hs : S.ShortExact)
    (ha : AcyclicFor P S.X₁) (hb : AcyclicFor P S.X₂) : AcyclicFor P S.X₃ := by
  intro n
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨y,hy⟩ := Ext.covariant_sequence_exact₃ P hs x rfl ((ha (n+1)).elim _ _)
  rw [(hb n).elim y 0, Ext.zero_comp] at hy
  exact hy.symm

private theorem sections_shortExact (P : C) {S : ShortComplex C} (hs : S.ShortExact)
    (ha : AcyclicFor P S.X₁) : (S.map (sections P)).ShortExact := by
  let := hs.mono_f
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.ab_exact_iff _).2
    intro x hx
    have hh : (x : P ⟶ S.X₂) ≫ S.g = 0 := hx
    exact hs.exact.lift' x hh
  · apply (AddCommGrpCat.mono_iff_injective _).2
    intro x y h
    exact (cancel_mono S.f).mp h
  ·
    apply (AddCommGrpCat.epi_iff_surjective _).2
    intro x
    obtain ⟨y,hy⟩ := Ext.covariant_sequence_exact₃ P hs (Ext.mk₀ x) (rfl : 0+1=1)
      ((ha 0).elim _ _)
    obtain ⟨a,rfl⟩ := (Ext.mk₀_bijective P S.X₂).surjective y
    rw [Ext.mk₀_comp_mk₀] at hy
    exact ⟨a, (Ext.mk₀_bijective P S.X₃).injective hy⟩

private def cycleStep (K : CochainComplex C ℤ) (i : ℤ) : ShortComplex C :=
  ShortComplex.mk (K.iCycles i) (K.toCycles i (i+1)) <| by
    apply (cancel_mono (K.iCycles (i+1))).mp
    simp

omit [HasExt.{w} C] in
private theorem cycleStep_shortExact (K : CochainComplex C ℤ) (hK : K.Acyclic) (i : ℤ) :
    (cycleStep K i).ShortExact := by
  let S := cycleStep K i
  have hk : IsLimit (KernelFork.ofι S.f S.zero) := by
    apply Fork.IsLimit.mk _ (fun q => K.liftCycles q.ι (i+1) (by simp) (by
      rw [← toCycles_i, ← Category.assoc]
      change (q.ι ≫ S.g) ≫ K.iCycles (i+1) = 0
      erw [q.condition, comp_zero, zero_comp]))
    · intro q; exact K.liftCycles_i ..
    · intro q m hm
      apply (cancel_mono (K.iCycles i)).mp
      exact hm.trans (K.liftCycles_i ..).symm
  let : Mono S.f := inferInstanceAs (Mono (K.iCycles i))
  have hi : (ComplexShape.up ℤ).prev (i+1) = i := by simp
  have hj : (ComplexShape.up ℤ).next (i+1) = i+1+1 := by simp
  let e := K.cyclesIsoSc' i (i+1) (i+1+1) hi hj
  have he := (K.exactAt_iff' i (i+1) (i+1+1) hi hj).mp (hK (i+1))
  let : Epi (K.toCycles i (i+1) ≫ e.hom) :=
    (K.toCycles_cyclesIsoSc'_hom i (i+1) (i+1+1) hi hj).symm ▸ he.epi_toCycles
  have hh : Epi ((K.toCycles i (i+1) ≫ e.hom) ≫ e.inv) := inferInstance
  let : Epi S.g := by simpa [S, cycleStep] using hh
  exact { exact := S.exact_of_f_is_kernel hk, mono_f := inferInstance, epi_g := inferInstance }

/-- Represented sections preserve exactness of bounded-below exact complexes with acyclic terms. -/
theorem map_bounded_acyclic (P : C) (K : CochainComplex C ℤ) (k : ℤ)
    [K.IsStrictlyGE k] (hK : K.Acyclic) (hterms : ∀ i, AcyclicFor P (K.X i)) :
    ((sectionComplex P).obj K).Acyclic := by
  have hsmall (i : ℤ) (hi : i < k) : AcyclicFor P (K.cycles i) := by
    have hz := IsZero.of_mono_eq_zero (K.iCycles i) ((K.isZero_of_isStrictlyGE k i hi).eq_of_tgt _ _)
    intro n
    apply subsingleton_of_forall_eq 0
    intro x
    calc
      x = x.comp (Ext.mk₀ (𝟙 _)) (add_zero _) := (Ext.comp_mk₀_id x).symm
      _ = 0 := by rw [hz.eq_of_tgt (𝟙 (K.cycles i)) 0, Ext.mk₀_zero, Ext.comp_zero]
  have hlarge (n : ℕ) : AcyclicFor P (K.cycles (k-1 + n)) := by
    induction n with
    | zero => simpa using hsmall (k-1) (by omega)
    | succ n ih =>
      have hh := acyclic_coker P (cycleStep_shortExact K hK (k-1+n)) ih (hterms _)
      convert hh using 1
      simp [cycleStep, add_assoc]
  have hcycles (i : ℤ) : AcyclicFor P (K.cycles i) := by
    by_cases hi : i < k
    · exact hsmall _ hi
    · exact (show k-1+((i-(k-1)).toNat : ℤ) = i by omega) ▸ hlarge (i-(k-1)).toNat
  intro i
  obtain ⟨j,rfl⟩ : ∃ j : ℤ, i = j+1 := ⟨i-1, by omega⟩
  apply (((sectionComplex P).obj K).exactAt_iff' j (j+1) (j+1+1) (by simp) (by simp)).2
  apply (ShortComplex.ab_exact_iff _).2
  intro x hx
  change (x : P ⟶ K.X (j+1)) ≫ K.d (j+1) (j+1+1) = 0 at hx
  let f := K.liftCycles x (j+1+1) (by simp) hx
  have he := K.liftCycles_i x (j+1+1) (by simp) hx
  have h := (sections_shortExact P (cycleStep_shortExact K hK j) (hcycles _)).epi_g
  obtain ⟨y,hy⟩ := (AddCommGrpCat.epi_iff_surjective _).1 h f
  let y' : P ⟶ K.X j := y
  change y' ≫ K.toCycles j (j+1) = f at hy
  refine ⟨y',?_⟩
  change y' ≫ K.d j (j+1) = x
  exact ((congrArg (fun z => y' ≫ z) (K.toCycles_i j (j+1))).symm.trans
    (Category.assoc y' _ _).symm).trans
      ((congrArg (fun z => z ≫ K.iCycles (j+1)) hy).trans he)

end CycleQ2AffineHypercohomologyComparison

section

open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
universe u v w
namespace CycleQ2KInjectiveSections
variable {C : Type u} [Category.{v} C] [Abelian C] (P : C) (I : CochainComplex C ℤ)

abbrev sections := ((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj I

/-- The internal Hom out of a degree-zero object is its ordinary sections complex. -/
def sectionsIso : sections P I ≅ HomComplex ((CochainComplex.singleFunctor C 0).obj P) I :=
  Hom.isoOfComponents (fun i => (Cochain.fromSingleEquiv (X := P) (K := I) (zero_add i)).symm.toAddCommGrpIso) (by
    intro i j _
    apply ConcreteCategory.hom_ext
    intro f
    exact Cochain.δ_fromSingleMk (K := I) f (zero_add i) j j (zero_add j))

private def homAddCongr {D : Type*} [Category* D] [Preadditive D]
    {A B A' B' : D} (a : A ≅ A') (b : B ≅ B') : (A ⟶ B) ≃+ (A' ⟶ B') :=
  { Iso.homCongr a b with
    map_add' x y := by
      change a.inv ≫ (x + y) ≫ b.hom = (a.inv ≫ x ≫ b.hom) + (a.inv ≫ y ≫ b.hom)
      simp only [Preadditive.comp_add, Preadditive.add_comp] }

variable [HasDerivedCategory.{w} C] [I.IsKInjective]

def classEquiv (n : ℤ) :
    CohomologyClass ((CochainComplex.singleFunctor C 0).obj P) I n ≃+
      ((DerivedCategory.singleFunctor C 0).obj P ⟶ (DerivedCategory.Q.obj I)⟦n⟧) := by
  let K := (CochainComplex.singleFunctor C 0).obj P
  let e := CohomologyClass.homAddEquiv (K := K) (L := I) (n := n)
  let e' := AddEquiv.ofBijective DerivedCategory.Qh.mapAddHom
    (IsKInjective.Qh_map_bijective ((HomotopyCategory.quotient _ _).obj K) (I⟦n⟧))
  let a := (DerivedCategory.quotientCompQhIso C).app K
  let b := (DerivedCategory.quotientCompQhIso C).app (I⟦n⟧) ≪≫ (DerivedCategory.Q.commShiftIso n).app I
  exact (e.trans e').trans (homAddCongr a b)

/-- Ordinary section cohomology computes morphisms in the actual derived category
when the target is K-injective. -/
def derivedSectionsEquiv (n : ℤ) :
    (sections P I).homology n ≃+ ((DerivedCategory.singleFunctor C 0).obj P ⟶ (DerivedCategory.Q.obj I)⟦n⟧) :=
  (((homologyFunctor AddCommGrpCat (.up ℤ) n).mapIso (sectionsIso P I)).addCommGroupIsoToAddEquiv.trans
    (HomComplex.homologyAddEquiv _ I n)).trans (classEquiv P I n)

/-- Vanishing of section cohomology implies vanishing of the shifted derived group. -/
theorem derived_subsingleton (n : ℤ) (h : (sections P I).ExactAt n) :
    Subsingleton ((DerivedCategory.singleFunctor C 0).obj P ⟶ (DerivedCategory.Q.obj I)⟦n⟧) := by
  let := AddCommGrpCat.isZero_iff_subsingleton.mp ((exactAt_iff_isZero_homology (sections P I) n).mp h)
  exact (derivedSectionsEquiv P I n).symm.injective.subsingleton

end CycleQ2KInjectiveSections
end

namespace CycleQ2SupportedSingleRow
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits HomologicalComplex Opposite
open CycleQ2SupportedExtComplex CycleQ2SupportedTwoResolutions
universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] [HasDerivedCategory.{w} C]
    [EnoughInjectives C] (P : C) (K : CochainComplex C ℤ)

/-- If every term has supported Ext only in degree two, exactness of the
 horizontal degree-two Ext row at `n` kills the actual derived group in degree `n+2`. -/
theorem vanishing (b : ℤ) [K.IsStrictlyGE b] (h₀ : ∀ j, Subsingleton (Ext P (K.X j) 0))
    (h₁ : ∀ j, Subsingleton (Ext P (K.X j) 1))
    (hhi : ∀ j n, Subsingleton (Ext P (K.X j) (n+3)))
    (n : ℤ) (hn : (E P 2 K).ExactAt n) :
    Subsingleton ((DerivedCategory.singleFunctor C 0).obj P ⟶ (DerivedCategory.Q.obj K)⟦n+2⟧) := by
  obtain ⟨I,f,hq,hI,hBI,c⟩ := exists_resolution_with_shift P K b h₀ h₁ hhi (fun M k hM hAc ht j => by
    let := hM
    exact (E0_exactAt_iff P M j).mpr (CycleQ2AffineHypercohomologyComparison.map_bounded_acyclic P M k hAc ht j))
  obtain ⟨e⟩ := c n
  have hI0 : (E P 0 I).ExactAt (n+2) :=
    (exactAt_iff_isZero_homology _ _).mpr (e.isZero_iff.mp hn.isZero_homology)
  have : I.IsKInjective := CochainComplex.isKInjective_of_injective I (b-1)
  have : Subsingleton ((DerivedCategory.singleFunctor C 0).obj P ⟶ (DerivedCategory.Q.obj I)⟦n+2⟧) :=
    CycleQ2KInjectiveSections.derived_subsingleton P I (n+2) ((E0_exactAt_iff P I _).mp hI0)
  let s := (shiftFunctor (DerivedCategory C) (n+2)).mapIso (asIso (DerivedCategory.Q.map f))
  exact (Iso.homCongr (Iso.refl _) s).injective.subsingleton

end CycleQ2SupportedSingleRow
