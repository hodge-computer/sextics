import Proposal.GeometricFiniteCechHOne

/-!
# Additivity of the degree-one class of a finite Čech cocycle

Adding local primitives and their glued quotient sections gives descent
data for the sum. Independence of descent then identifies the class of
the sum with the sum in the actual degree-one sheaf cohomology group.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2FiniteCechOneAdditivity

open CategoryTheory CategoryTheory.Abelian TopologicalSpace
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
  CycleQ2FiniteCechDescent CycleQ2FiniteCechHOne
open CycleQ2CechTwoToDerived (presentation presentation_shortExact app sectionExtZero)
open CycleQ2CechTwoComparison (sectionExtZero_add)

variable {X : TopCat.{0}} {ι : Type} {F : AbSheaf X} (U : ι → Opens X)
local instance sheafHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _

def oneCocycles : AddSubgroup (One F U) where
  carrier := {c | IsOneCocycle F U c}
  zero_mem' := by
    intro i j k W hi hj hk
    simp
  add_mem' := by
    intro c d hc hd i j k W hi hj hk
    simp only [Pi.add_apply, map_add, hc i j k W hi hj hk, hd i j k W hi hj hk]
    abel
  neg_mem' := by
    intro c hc i j k W hi hj hk
    simp only [Pi.neg_apply, map_neg, hc i j k W hi hj hk, neg_add]

private def sumDescent {c e : One F U} (d : OneDescent U c) (f : OneDescent U e) :
    OneDescent U (c + e) where
  primitive := d.primitive + f.primitive
  differential i j W hi hj := by
    simp only [Pi.add_apply, map_add, edgeValue]
    have hd := d.differential i j W hi hj
    have hf := f.differential i j W hi hj
    unfold edgeValue at hd hf
    linear_combination (norm := abel) hd + hf
  globalSection := d.globalSection + f.globalSection
  global_restriction := by
    funext i
    simp only [globalZero, mapZero, Pi.add_apply, map_add]
    exact congrArg₂ (· + ·) (congrFun d.global_restriction i) (congrFun f.global_restriction i)

variable [Fintype ι] (hcover : (⨆ i, U i) = ⊤)

theorem cechOneClass_add (c e : One F U) (hc : IsOneCocycle F U c) (he : IsOneCocycle F U e) :
    cechOneClass U hcover (c + e) ((oneCocycles (F := F) U).add_mem hc he) =
      cechOneClass U hcover c hc + cechOneClass U hcover e he := by
  let d := Classical.choice (oneDescent_nonempty U hcover c hc)
  let f := Classical.choice (oneDescent_nonempty U hcover e he)
  refine (cechOneClass_eq_descentClass U hcover (c + e) _ (sumDescent U d f)).trans ?_
  change (sectionExtZero ⊤ (d.globalSection + f.globalSection)).comp
    (presentation_shortExact F).extClass rfl = oneDescentClass U d + oneDescentClass U f
  rw [sectionExtZero_add, Ext.add_comp]
  rfl

def cechOneClassHom : oneCocycles (F := F) U →+ F.H' 1 ⊤ :=
  AddMonoidHom.mk' (fun c => cechOneClass U hcover c.val c.property)
    (fun c e => cechOneClass_add U hcover c.val e.val c.property e.property)

theorem cechOneClass_zsmul (n : ℤ) (c : One F U) (hc : IsOneCocycle F U c) :
    cechOneClass U hcover (n • c) ((oneCocycles (F := F) U).zsmul_mem hc n) =
      n • cechOneClass U hcover c hc :=
  (cechOneClassHom (F := F) U hcover).map_zsmul n ⟨c, hc⟩

end CycleQ2FiniteCechOneAdditivity

end

#print axioms CycleQ2FiniteCechOneAdditivity.cechOneClass_add
#print axioms CycleQ2FiniteCechOneAdditivity.cechOneClass_zsmul
