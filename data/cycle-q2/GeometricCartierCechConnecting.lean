import Proposal.GeometricCartierDerivedClass

/-! Checked components of the original normalized intrinsic normal class
and its actual Cartier boundary. Every component body is retained verbatim. -/

section CheckedCartierNormalPart01

/-!
# The actual coefficient boundary of a four-open one-cocycle

The degree-one comparison uses one injective presentation.  A genuine
short exact coefficient sequence maps to that presentation by injectivity;
the resulting short-complex morphism identifies its Ext boundary with the
already constructed degree-two Cech comparison.  All cochains and maps are
sections of the original additive sheaves.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2CechOneConnecting

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
open CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2CechTwoToDerived
  CycleQ2CechTwoComparison CycleQ2CechTwoNaturality

variable {X : TopCat.{0}}
local instance sheafHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _
variable {F G : AbSheaf X} (U : Fin 4 → Opens X)

/-- Retained primitive and quotient section in one actual injective presentation. -/
structure OneDescent (c : One F U) where
  primitive : Zero (presentation F).X₂ U
  differential : d0 (presentation F).X₂ U primitive = mapOne U (presentation F).f c
  globalSection : Sections (presentation F).X₃ ⊤
  global_restriction : globalZero U globalSection = mapZero U (presentation F).g primitive

theorem oneDescent_nonempty (hcover : (⨆ i, U i) = ⊤)
    (c : One F U) (hc : d1 F U c = 0) : Nonempty (OneDescent U c) := by
  obtain ⟨q,hq⟩ := one_exact_of_injective U (mapOne U (presentation F).f c) (by
    rw [← mapTwo_d1, hc, mapTwo_zero])
  have hd : d0 (presentation F).X₃ U (mapZero U (presentation F).g q) = 0 := by
    rw [← mapOne_d0, hq, mapOne_comp, (presentation F).zero, mapOne_zeroHom]
  obtain ⟨t,ht⟩ := globalZero_exists U hcover _ hd
  exact ⟨⟨q,hq,t,ht⟩⟩

def oneDescentClass {c : One F U} (d : OneDescent U c) : F.H' 1 ⊤ :=
  (sectionExtZero ⊤ d.globalSection).comp (presentation_shortExact F).extClass rfl

theorem oneDescentClass_zero (hcover : (⨆ i, U i) = ⊤)
    (d : OneDescent U (0 : One F U)) : oneDescentClass U d = 0 := by
  have hd : d0 (presentation F).X₂ U d.primitive = 0 :=
    d.differential.trans (mapOne_zero U (presentation F).f)
  obtain ⟨q,hq⟩ := globalZero_exists U hcover _ hd
  have hg : app (presentation F).g ⊤ q = d.globalSection := by
    apply globalZero_injective U hcover
    rw [← mapZero_globalZero, hq, ← d.global_restriction]
  unfold oneDescentClass
  rw [← hg, sectionExtZero_app, Ext.comp_assoc_of_second_deg_zero,
    ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]

def subtractOneDescents {c c' : One F U} (d : OneDescent U c) (e : OneDescent U c') :
    OneDescent U (c-c') where
  primitive := d.primitive - e.primitive
  differential := by rw [d0_sub, d.differential, e.differential, mapOne_sub]
  globalSection := d.globalSection - e.globalSection
  global_restriction := by
    rw [globalZero_sub, d.global_restriction, e.global_restriction, mapZero_sub]

theorem oneDescentClass_sub {c c' : One F U} (d : OneDescent U c) (e : OneDescent U c') :
    oneDescentClass U (subtractOneDescents U d e) =
      oneDescentClass U d - oneDescentClass U e := by
  change (sectionExtZero ⊤ (d.globalSection-e.globalSection)).comp
      (presentation_shortExact F).extClass rfl =
    (sectionExtZero ⊤ d.globalSection).comp (presentation_shortExact F).extClass rfl -
      (sectionExtZero ⊤ e.globalSection).comp (presentation_shortExact F).extClass rfl
  exact (congrArg
    (fun x : Ext (freeOpen (⊤ : Opens X)) (presentation F).X₃ 0 =>
      x.comp (presentation_shortExact F).extClass rfl)
    (sectionExtZero_sub ⊤ d.globalSection e.globalSection)).trans
      (((presentation_shortExact F).extClass.postcomp (freeOpen (⊤ : Opens X))
        (rfl : 0+1=1)).map_sub _ _)

theorem oneDescentClass_zero_of_cocycle_zero (hcover : (⨆ i, U i) = ⊤)
    {c : One F U} (d : OneDescent U c) (hc : c=0) : oneDescentClass U d = 0 := by
  subst c
  exact oneDescentClass_zero U hcover d

theorem oneDescentClass_independent (hcover : (⨆ i, U i) = ⊤)
    {c : One F U} (d e : OneDescent U c) : oneDescentClass U d = oneDescentClass U e := by
  apply sub_eq_zero.mp
  rw [← oneDescentClass_sub]
  exact oneDescentClass_zero_of_cocycle_zero U hcover _ (sub_self c)

def cechOneClass (hcover : (⨆ i, U i) = ⊤) (c : One F U) (hc : d1 F U c=0) :
    F.H' 1 ⊤ :=
  oneDescentClass U (Classical.choice (oneDescent_nonempty U hcover c hc))

theorem cechOneClass_eq_descentClass (hcover : (⨆ i, U i) = ⊤)
    (c : One F U) (hc : d1 F U c=0) (d : OneDescent U c) :
    cechOneClass U hcover c hc = oneDescentClass U d :=
  oneDescentClass_independent U hcover _ d

/-- Transport along the genuine morphism of injective presentations. -/
def transportOneDescent (f : F ⟶ G) {c : One F U} (d : OneDescent U c) :
    OneDescent U (mapOne U f c) where
  primitive := mapZero U (presentationMap f).τ₂ d.primitive
  differential := by
    rw [← mapOne_d0, d.differential, mapOne_comp,
      ← (presentationMap f).comm₁₂, ← mapOne_comp]
  globalSection := app (presentationMap f).τ₃ ⊤ d.globalSection
  global_restriction := by
    rw [← mapZero_globalZero, d.global_restriction, mapZero_comp,
      ← (presentationMap f).comm₂₃, ← mapZero_comp]

theorem oneDescentClass_naturality (f : F ⟶ G) {c : One F U} (d : OneDescent U c) :
    (oneDescentClass U d).comp (Ext.mk₀ f) (Nat.add_zero 1) =
      oneDescentClass U (transportOneDescent U f d) := by
  simp only [oneDescentClass, transportOneDescent]
  rw [connecting_naturality (presentation_shortExact F) (presentation_shortExact G)
    (presentationMap f), ← sectionExtZero_app]

theorem cechOneClass_naturality (hcover : (⨆ i, U i) = ⊤)
    (f : F ⟶ G) (c : One F U) (hc : d1 F U c=0)
    (hmap : d1 G U (mapOne U f c)=0) :
    (cechOneClass U hcover c hc).comp (Ext.mk₀ f) (Nat.add_zero 1) =
      cechOneClass U hcover (mapOne U f c) hmap := by
  let d := Classical.choice (oneDescent_nonempty U hcover c hc)
  change (oneDescentClass U d).comp (Ext.mk₀ f) (Nat.add_zero 1) = _
  rw [oneDescentClass_naturality]
  exact (cechOneClass_eq_descentClass U hcover _ hmap
    (transportOneDescent U f d)).symm

variable {S : ShortComplex (AbSheaf X)}

/-- Every actual short exact sequence maps to the chosen injective presentation
of its first term, extending its identity. -/
def coefficientPresentationMap (hS : S.ShortExact) : S ⟶ presentation S.X₁ := by
  letI : Mono S.f := hS.mono_f
  let m : S.X₂ ⟶ (presentation S.X₁).X₂ :=
    Injective.factorThru (presentation S.X₁).f S.f
  have hm : S.f ≫ m = (presentation S.X₁).f := Injective.comp_factorThru _ _
  have hz : S.f ≫ (m ≫ (presentation S.X₁).g) = 0 := by
    rw [← Category.assoc, hm, (presentation S.X₁).zero]
  let q : S.X₃ ⟶ (presentation S.X₁).X₃ :=
    hS.gIsCokernel.desc (CokernelCofork.ofπ (m ≫ (presentation S.X₁).g) hz)
  exact
    { τ₁ := 𝟙 _
      τ₂ := m
      τ₃ := q
      comm₁₂ := by simpa only [Category.id_comp] using hm.symm
      comm₂₃ := (hS.gIsCokernel.fac
        (CokernelCofork.ofπ (m ≫ (presentation S.X₁).g) hz)
        WalkingParallelPair.one).symm }

@[simp] theorem coefficientPresentationMap_left (hS : S.ShortExact) :
    (coefficientPresentationMap hS).τ₁ = 𝟙 S.X₁ := rfl

theorem reduction_closed (ν : One S.X₂ U) (b : Two S.X₁ U)
    (hν : d1 S.X₂ U ν = mapTwo U S.f b) :
    d1 S.X₃ U (mapOne U S.g ν) = 0 := by
  rw [← mapTwo_d1, hν, mapTwo_comp, S.zero, mapTwo_zeroHom]

/-- The actual coefficient connecting map applied to a lifted one-cocycle
is the original degree-two Cech class, in the second-minus-first convention. -/
theorem coefficient_connecting (hcover : (⨆ i, U i) = ⊤) (hS : S.ShortExact)
    (ν : One S.X₂ U) (b : Two S.X₁ U) (hb : d2 S.X₁ U b=0)
    (hν : d1 S.X₂ U ν = mapTwo U S.f b) :
    (cechOneClass U hcover (mapOne U S.g ν) (reduction_closed U ν b hν)).comp
        hS.extClass rfl = cechTwoClass U hcover b hb := by
  let m := coefficientPresentationMap hS
  let c := mapOne U S.g ν
  have hc : d1 S.X₃ U c=0 := reduction_closed U ν b hν
  have hmc : d1 (presentation S.X₁).X₃ U (mapOne U m.τ₃ c)=0 := by
    rw [← mapTwo_d1, hc, mapTwo_zero]
  let d := Classical.choice (oneDescent_nonempty U hcover (mapOne U m.τ₃ c) hmc)
  let e : TwoDescent U b :=
    { first := mapOne U m.τ₂ ν
      first_differential := by
        rw [← mapTwo_d1, hν, mapTwo_comp, ← m.comm₁₂]
        change mapTwo U (𝟙 S.X₁ ≫ (presentation S.X₁).f) b = _
        rw [Category.id_comp]
      second := d.primitive
      second_differential := by
        rw [d.differential]
        change mapOne U (presentation (presentation S.X₁).X₃).f
            (mapOne U m.τ₃ (mapOne U S.g ν)) = _
        apply congrArg (mapOne U (presentation (presentation S.X₁).X₃).f)
        rw [mapOne_comp, mapOne_comp, m.comm₂₃]
      globalSection := d.globalSection
      global_restriction := d.global_restriction }
  have hn := connecting_naturality hS (presentation_shortExact S.X₁) m 1
    (cechOneClass U hcover c hc)
  have hleft :
      (cechOneClass U hcover c hc).comp hS.extClass rfl =
        ((cechOneClass U hcover c hc).comp (Ext.mk₀ m.τ₃) (Nat.add_zero 1)).comp
          (presentation_shortExact S.X₁).extClass rfl := by
    simpa only [m, coefficientPresentationMap_left, Ext.comp_mk₀_id] using hn
  change (cechOneClass U hcover c hc).comp hS.extClass rfl = _
  rw [hleft, cechOneClass_naturality U hcover m.τ₃ c hc hmc,
    cechOneClass_eq_descentClass U hcover _ hmc d]
  exact (cechTwoClass_eq_descentClass U hcover b hb e).symm

#print axioms oneDescent_nonempty
#print axioms oneDescentClass_independent
#print axioms cechOneClass_eq_descentClass
#print axioms cechOneClass_naturality
#print axioms coefficientPresentationMap
#print axioms reduction_closed
#print axioms coefficient_connecting

end CycleQ2CechOneConnecting
end

end CheckedCartierNormalPart01
