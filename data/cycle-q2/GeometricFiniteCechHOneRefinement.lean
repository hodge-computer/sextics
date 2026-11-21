import Proposal.GeometricFiniteCechHOne

/-!
# Refinement of derived degree-one Čech classes

A local primitive makes the derived class vanish. Restricting injective
descent along an index map retains its global quotient section, so changing
to a common refinement preserves the derived class.

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
  CycleQ2FiniteCechDescent CycleQ2FiniteCechRefinement
open CycleQ2CechTwoToDerived (presentation presentation_shortExact app app_res app_comp app_zero
  sectionExtZero)

variable {X : TopCat.{0}} {ι κ : Type}
local instance refinementSheafHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _
variable {F : AbSheaf X} (U : ι → Opens X)

theorem cechOneClass_eq_zero_of_primitive [Fintype ι] (hcover : (⨆ i, U i) = ⊤)
    (c : One F U) (hc : IsOneCocycle F U c) (p : Zero F U)
    (hp : ∀ i j W hi hj, res F hj (p j) - res F hi (p i) = edgeValue F U c i j W hi hj) :
    cechOneClass U hcover c hc = 0 := by
  let d : OneDescent U c := {
    primitive := mapZero U (presentation F).f p
    differential := by
      intro i j W hi hj
      dsimp only [mapZero]
      rw [← app_res, ← app_res, ← map_sub, hp]
    globalSection := 0
    global_restriction := by
      funext i
      simp only [globalZero, mapZero, map_zero, app_comp, (presentation F).zero, app_zero] }
  rw [cechOneClass_eq_descentClass U hcover c hc d]
  simp only [oneDescentClass, d, sectionExtZero, map_zero, Ext.mk₀_zero, Ext.zero_comp]

variable (V : κ → Opens X) (ρ : κ → ι) (h : ∀ j, V j ≤ U (ρ j))

theorem restrictOne_closed (c : One F U) (hc : IsOneCocycle F U c) :
    IsOneCocycle F V (restrictOne U V ρ h c) := by
  intro i j k W hi hj hk
  simp only [restrictOne, res_comp]
  exact hc (ρ i) (ρ j) (ρ k) W (hi.trans (h i)) (hj.trans (h j)) (hk.trans (h k))

def restrictOneDescent {c : One F U} (d : OneDescent U c) :
    OneDescent V (restrictOne U V ρ h c) where
  primitive := restrictZero U V ρ h d.primitive
  differential i j W hi hj := by
    dsimp only [restrictZero]
    rw [res_comp, res_comp, edgeValue_restrictOne]
    exact d.differential (ρ i) (ρ j) W (hi.trans (h i)) (hj.trans (h j))
  globalSection := d.globalSection
  global_restriction := by
    funext j
    have hd := congrArg (res (presentation F).X₃ (h j)) (congrFun d.global_restriction (ρ j))
    dsimp only [globalZero, mapZero] at hd ⊢
    rw [res_comp, ← app_res] at hd
    exact hd

theorem cechOneClass_refinement [Fintype ι] [Fintype κ]
    (hU : (⨆ i, U i) = ⊤) (hV : (⨆ j, V j) = ⊤) (c : One F U) (hc : IsOneCocycle F U c) :
    cechOneClass V hV (restrictOne U V ρ h c) (restrictOne_closed U V ρ h c hc) =
      cechOneClass U hU c hc := by
  let d := Classical.choice (oneDescent_nonempty U hU c hc)
  rw [cechOneClass_eq_descentClass V hV _ _ (restrictOneDescent U V ρ h d)]
  exact (cechOneClass_eq_descentClass U hU c hc d).symm

end CycleQ2FiniteCechHOne

end

#print axioms CycleQ2FiniteCechHOne.cechOneClass_eq_zero_of_primitive
#print axioms CycleQ2FiniteCechHOne.cechOneClass_refinement
