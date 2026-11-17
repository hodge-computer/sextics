import Proposal.GeometricCechRefinement

/-!
# Actual derived degree-one classes on arbitrary finite covers

A section-valued one-cocycle is mapped into the existing injective
presentation, where finite-cover acyclicity supplies its primitive.
The quotient sections glue in the original sheaf. Their actual Ext
boundary defines the derived class, independently of the primitive.
The construction is natural for genuine morphisms of sheaves.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2FiniteCechHOne

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
  CycleQ2FiniteCechDescent CycleQ2CechTwoNaturality
open CycleQ2CechTwoToDerived (presentation presentation_shortExact presentation_middle_injective
  app app_res app_comp app_zero sectionExtZero)
open CycleQ2CechTwoComparison (sectionExtZero_sub sectionExtZero_app)

variable {X : TopCat.{0}} {ι : Type}
local instance sheafHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _
variable {F G : AbSheaf X} (U : ι → Opens X)

structure OneDescent (c : One F U) where
  primitive : Zero (presentation F).X₂ U
  differential : ∀ i j W hi hj,
    res (presentation F).X₂ hj (primitive j) - res (presentation F).X₂ hi (primitive i) =
      app (presentation F).f W (edgeValue F U c i j W hi hj)
  globalSection : Sections (presentation F).X₃ ⊤
  global_restriction : globalZero U globalSection = mapZero U (presentation F).g primitive

theorem oneDescent_nonempty [Fintype ι] (hcover : (⨆ i, U i) = ⊤)
    (c : One F U) (hc : IsOneCocycle F U c) : Nonempty (OneDescent U c) := by
  obtain ⟨p,hp⟩ := oneCocycle_has_primitive (mapOne U (presentation F).f c)
    (mapOne_closed U (presentation F).f c hc)
  have hp' : ∀ i j W hi hj,
      res (presentation F).X₂ hj (p j) - res (presentation F).X₂ hi (p i) =
        app (presentation F).f W (edgeValue F U c i j W hi hj) := by
    intro i j W hi hj
    exact (hp i j W hi hj).trans (edgeValue_mapOne U (presentation F).f c i j W hi hj)
  have hcompatible : ∀ (i j : ι) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j),
      res (presentation F).X₃ hi (mapZero U (presentation F).g p i) =
        res (presentation F).X₃ hj (mapZero U (presentation F).g p j) := by
    intro i j W hi hj
    have h := congrArg (app (presentation F).g W) (hp' i j W hi hj)
    simp only [map_sub, app_comp, (presentation F).zero, app_zero] at h
    dsimp only [mapZero]
    rw [← app_res, ← app_res]
    exact (sub_eq_zero.mp h).symm
  obtain ⟨t,ht⟩ := globalZero_exists U hcover _ hcompatible
  exact ⟨⟨p,hp',t,ht⟩⟩

def oneDescentClass {c : One F U} (d : OneDescent U c) : F.H' 1 ⊤ :=
  (sectionExtZero ⊤ d.globalSection).comp (presentation_shortExact F).extClass rfl

theorem oneDescentClass_independent (hcover : (⨆ i, U i) = ⊤)
    {c : One F U} (d e : OneDescent U c) : oneDescentClass U d = oneDescentClass U e := by
  have hp : ∀ i j (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j),
      res (presentation F).X₂ hi (d.primitive i - e.primitive i) =
        res (presentation F).X₂ hj (d.primitive j - e.primitive j) := by
    intro i j W hi hj
    have hd := d.differential i j W hi hj
    have he := e.differential i j W hi hj
    rw [map_sub, map_sub]
    linear_combination (norm := abel) he - hd
  obtain ⟨a,ha⟩ := globalZero_exists U hcover (d.primitive-e.primitive) hp
  have hglobal : d.globalSection-e.globalSection = app (presentation F).g ⊤ a := by
    apply globalZero_injective U hcover
    funext i
    have hd := congrFun d.global_restriction i
    have he := congrFun e.global_restriction i
    have hai := congrFun ha i
    change res (presentation F).X₃ le_top (d.globalSection-e.globalSection) =
      res (presentation F).X₃ le_top (app (presentation F).g ⊤ a)
    rw [map_sub, ← app_res]
    change res _ le_top d.globalSection - res _ le_top e.globalSection =
      app (presentation F).g (U i) (globalZero U a i)
    calc
      _ = app (presentation F).g (U i) (d.primitive i) -
          app (presentation F).g (U i) (e.primitive i) :=
        congrArg₂ (fun x y : Sections (presentation F).X₃ (U i) => x-y) hd he
      _ = app (presentation F).g (U i) (d.primitive i-e.primitive i) :=
        (map_sub (app (presentation F).g (U i)) _ _).symm
      _ = _ := congrArg (app (presentation F).g (U i)) hai.symm
  apply sub_eq_zero.mp
  have hsub : oneDescentClass U d-oneDescentClass U e =
      (sectionExtZero ⊤ (d.globalSection-e.globalSection)).comp
        (presentation_shortExact F).extClass rfl := by
    rw [sectionExtZero_sub]
    simp only [oneDescentClass, sub_eq_add_neg, Ext.add_comp, Ext.neg_comp]
  rw [hsub,hglobal,sectionExtZero_app,Ext.comp_assoc_of_second_deg_zero,
    ShortComplex.ShortExact.comp_extClass,Ext.comp_zero]

def cechOneClass [Fintype ι] (hcover : (⨆ i, U i) = ⊤)
    (c : One F U) (hc : IsOneCocycle F U c) : F.H' 1 ⊤ :=
  oneDescentClass U (Classical.choice (oneDescent_nonempty U hcover c hc))

theorem cechOneClass_eq_descentClass [Fintype ι] (hcover : (⨆ i, U i) = ⊤)
    (c : One F U) (hc : IsOneCocycle F U c) (d : OneDescent U c) :
    cechOneClass U hcover c hc = oneDescentClass U d :=
  oneDescentClass_independent U hcover _ d

def transportOneDescent (f : F ⟶ G) {c : One F U} (d : OneDescent U c) :
    OneDescent U (mapOne U f c) where
  primitive := mapZero U (presentationMap f).τ₂ d.primitive
  differential i j W hi hj := by
    change res _ hj (app (presentationMap f).τ₂ (U j) (d.primitive j)) -
      res _ hi (app (presentationMap f).τ₂ (U i) (d.primitive i)) = _
    rw [← app_res,← app_res,← map_sub,d.differential,edgeValue_mapOne,
      app_comp,← (presentationMap f).comm₁₂,app_comp]
  globalSection := app (presentationMap f).τ₃ ⊤ d.globalSection
  global_restriction := by
    funext i
    have hd := congrFun d.global_restriction i
    change res _ le_top (app (presentationMap f).τ₃ ⊤ d.globalSection) =
      app (presentation G).g (U i) (app (presentationMap f).τ₂ (U i) (d.primitive i))
    rw [← app_res]
    change app (presentationMap f).τ₃ (U i) (globalZero U d.globalSection i) = _
    rw [hd]
    change app (presentationMap f).τ₃ (U i) (app (presentation F).g (U i) (d.primitive i)) =
      app (presentation G).g (U i) (app (presentationMap f).τ₂ (U i) (d.primitive i))
    rw [app_comp,← (presentationMap f).comm₂₃,app_comp]

theorem oneDescentClass_naturality (f : F ⟶ G) {c : One F U} (d : OneDescent U c) :
    (oneDescentClass U d).comp (Ext.mk₀ f) (Nat.add_zero 1) =
      oneDescentClass U (transportOneDescent U f d) := by
  simp only [oneDescentClass,transportOneDescent]
  rw [connecting_naturality (presentation_shortExact F) (presentation_shortExact G)
    (presentationMap f),← sectionExtZero_app]

theorem cechOneClass_naturality [Fintype ι] (hcover : (⨆ i, U i) = ⊤)
    (f : F ⟶ G) (c : One F U) (hc : IsOneCocycle F U c) :
    (cechOneClass U hcover c hc).comp (Ext.mk₀ f) (Nat.add_zero 1) =
      cechOneClass U hcover (mapOne U f c) (mapOne_closed U f c hc) := by
  let d := Classical.choice (oneDescent_nonempty U hcover c hc)
  change (oneDescentClass U d).comp (Ext.mk₀ f) (Nat.add_zero 1) = _
  rw [oneDescentClass_naturality]
  exact (cechOneClass_eq_descentClass U hcover _ _ (transportOneDescent U f d)).symm

end CycleQ2FiniteCechHOne

end

#print axioms CycleQ2FiniteCechHOne.oneDescent_nonempty
#print axioms CycleQ2FiniteCechHOne.oneDescentClass_independent
#print axioms CycleQ2FiniteCechHOne.cechOneClass_naturality
