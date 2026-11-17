import Proposal.GeometricFiniteCechHOne
import Proposal.GeometricCartierCechConnecting

/-!
# The actual derived boundary of a finite-cover lifted one-cocycle

A genuine short exact sequence maps to the existing injective
presentation of its first sheaf. This identifies its actual Ext
connecting map on a finite-cover degree-one class with the existing
degree-two class of the scalar boundary of the lift.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2FiniteCechConnecting

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
  CycleQ2FiniteCechDescent CycleQ2FiniteCechHOne CycleQ2CechTwoNaturality
open CycleQ2CechTwoToDerived (presentation presentation_shortExact app app_comp)
open CycleQ2CechOneConnecting (coefficientPresentationMap coefficientPresentationMap_left)

variable {X : TopCat.{0}} {ι : Type} [Fintype ι]
local instance sheafHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _
variable (U : ι → Opens X)

theorem cechOneClass_connecting {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact)
    (hcover : (⨆ i, U i) = ⊤) (b : One S.X₂ U) (c : Two S.X₁ U)
    (hn : NormalizedTwo S.X₁ U c) (hc : IsTwoCocycle S.X₁ U c)
    (hb : ∀ i j k W hi hj hk,
      boundaryValue S.X₂ U b i j k W hi hj hk =
        app S.f W (faceValue S.X₁ U c i j k W hi hj hk)) :
    (cechOneClass U hcover (mapOne U S.g b) (primitive_image_closed U S c b hb)).comp
      hS.extClass rfl = cechTwoClass U hcover c hn hc := by
  let m := coefficientPresentationMap hS
  let u := mapOne U S.g b
  have hu : IsOneCocycle S.X₃ U u := primitive_image_closed U S c b hb
  let a := mapOne U m.τ₂ b
  have hm : S.f ≫ m.τ₂ = (presentation S.X₁).f := by
    simpa only [m,coefficientPresentationMap_left,Category.id_comp] using m.comm₁₂.symm
  have ha : ∀ i j k W hi hj hk,
      boundaryValue (presentation S.X₁).X₂ U a i j k W hi hj hk =
        app (presentation S.X₁).f W (faceValue S.X₁ U c i j k W hi hj hk) := by
    intro i j k W hi hj hk
    change boundaryValue (presentation S.X₁).X₂ U (mapOne U m.τ₂ b) i j k W hi hj hk = _
    rw [boundaryValue_mapOne U m.τ₂ b,hb i j k W hi hj hk,app_comp,hm]
  let v := mapOne U m.τ₃ u
  have hv : v = mapOne U (presentation S.X₁).g a := by
    funext i j
    change app m.τ₃ (U i ⊓ U j) (app S.g (U i ⊓ U j) (b i j)) =
      app (presentation S.X₁).g (U i ⊓ U j) (app m.τ₂ (U i ⊓ U j) (b i j))
    rw [app_comp,app_comp,m.comm₂₃]
  have hvclosed : IsOneCocycle (presentation S.X₁).X₃ U v := mapOne_closed U m.τ₃ u hu
  let d := Classical.choice (oneDescent_nonempty U hcover v hvclosed)
  let dd : TwoDescent U c :=
    { first := a
      first_differential := ha
      second := d.primitive
      second_differential i j W hi hj := by
        have he : edgeValue (presentation S.X₁).X₃ U v i j W hi hj =
            app (presentation S.X₁).g W (edgeValue (presentation S.X₁).X₂ U a i j W hi hj) := by
          rw [hv]
          exact edgeValue_mapOne U (presentation S.X₁).g a i j W hi hj
        exact (d.differential i j W hi hj).trans
          (congrArg (app (presentation (presentation S.X₁).X₃).f W) he)
      globalSection := d.globalSection
      global_restriction := d.global_restriction }
  have hnat := connecting_naturality hS (presentation_shortExact S.X₁) m 1
    (cechOneClass U hcover u hu)
  have hleft : (cechOneClass U hcover u hu).comp hS.extClass rfl =
      ((cechOneClass U hcover u hu).comp (Ext.mk₀ m.τ₃) (Nat.add_zero 1)).comp
        (presentation_shortExact S.X₁).extClass rfl := by
    simpa only [m,coefficientPresentationMap_left,Ext.comp_mk₀_id] using hnat
  change (cechOneClass U hcover u hu).comp hS.extClass rfl = _
  calc
    _ = ((cechOneClass U hcover u hu).comp (Ext.mk₀ m.τ₃) (Nat.add_zero 1)).comp
        (presentation_shortExact S.X₁).extClass rfl := hleft
    _ = (cechOneClass U hcover v hvclosed).comp (presentation_shortExact S.X₁).extClass rfl :=
      congrArg (fun x => x.comp (presentation_shortExact S.X₁).extClass rfl)
        (cechOneClass_naturality U hcover m.τ₃ u hu)
    _ = (oneDescentClass U d).comp (presentation_shortExact S.X₁).extClass rfl :=
      congrArg (fun x => x.comp (presentation_shortExact S.X₁).extClass rfl)
        (cechOneClass_eq_descentClass U hcover v hvclosed d)
    _ = descentClass U dd := rfl
    _ = _ := (cechTwoClass_eq_descentClass U hcover c hn hc dd).symm

end CycleQ2FiniteCechConnecting

end

#print axioms CycleQ2FiniteCechConnecting.cechOneClass_connecting
