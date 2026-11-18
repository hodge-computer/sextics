import Proposal.GeometricFiniteCechHOneRefinement
import Proposal.GeometricFiniteCechOneAdditivity

/-!
# Actual degree-one boundary lifts on the original finite cover

If a finite-cover one-cocycle has zero derived class, the global quotient
section in its injective descent lifts globally. Subtracting that lift
from the local injective primitives gives sections of the original
sheaf. Thus equality of derived one-classes gives an actual boundary
for their difference on the same cover, without refining it.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2FiniteCechOneBoundaryLifts
open CategoryTheory Limits CategoryTheory.Abelian Opposite TopologicalSpace
open CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso
open CycleQ2FiniteInjectiveCech CycleQ2FiniteCechDescent CycleQ2FiniteCechHOne
open CycleQ2CechTwoToDerived (presentation presentation_shortExact presentation_left_mono
  sectionExtZero section_lift_of_boundary_zero sections_exact app app_res app_injective)
open CycleQ2FiniteCechOneAdditivity (oneCocycles cechOneClassHom)
variable {X : TopCat.{0}} {ι : Type} [Fintype ι] {F : AbSheaf X}
local instance : HasExt.{1} (AbSheaf X) := HasExt.standard _
variable (U : ι → Opens X) (hU : (⨆ i, U i) = ⊤)

theorem primitive_of_class_zero (c : One F U) (hc : IsOneCocycle F U c)
    (hz : cechOneClass U hU c hc = 0) :
    ∃ p : Zero F U, ∀ i j (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j),
      res F hj (p j) - res F hi (p i) = edgeValue F U c i j W hi hj := by
  let d := Classical.choice (oneDescent_nonempty U hU c hc)
  have hd : (sectionExtZero ⊤ d.globalSection).comp (presentation_shortExact F).extClass rfl = 0 :=
    (cechOneClass_eq_descentClass U hU c hc d).symm.trans hz
  obtain ⟨q,hq⟩ := section_lift_of_boundary_zero (presentation_shortExact F) ⊤ d.globalSection hd
  have hk (i : ι) : app (presentation F).g (U i)
      (d.primitive i - res (presentation F).X₂ le_top q) = 0 := by
    rw [map_sub,app_res,hq]
    exact sub_eq_zero.mpr (congrFun d.global_restriction i).symm
  choose p hp using fun i => sections_exact (presentation_shortExact F) (U i)
    (d.primitive i - res (presentation F).X₂ le_top q) (hk i)
  refine ⟨p,fun i j W hi hj => ?_⟩
  apply app_injective (presentation F).f W
  rw [map_sub,app_res,app_res,hp,hp,map_sub,map_sub,res_comp,res_comp]
  have he := d.differential i j W hi hj
  linear_combination (norm := abel) he

/-- Equality of genuine degree-one classes produces a primitive of the
difference, with every value on the original cover. -/
theorem difference_primitive (c e : One F U) (hc : IsOneCocycle F U c) (he : IsOneCocycle F U e)
    (hclass : cechOneClass U hU c hc = cechOneClass U hU e he) :
    ∃ p : Zero F U, ∀ i j (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j),
      res F hj (p j) - res F hi (p i) =
        edgeValue F U c i j W hi hj - edgeValue F U e i j W hi hj := by
  let a : oneCocycles (F := F) U := ⟨c,hc⟩
  let b : oneCocycles (F := F) U := ⟨e,he⟩
  have hz : cechOneClass U hU (a-b).val (a-b).property = 0 := by
    change cechOneClassHom U hU (a-b) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hclass
  obtain ⟨p,hp⟩ := primitive_of_class_zero U hU (a-b).val (a-b).property hz
  refine ⟨p,fun i j W hi hj => ?_⟩
  simpa only [edgeValue,AddSubgroup.coe_sub,Pi.sub_apply,map_sub] using hp i j W hi hj

end CycleQ2FiniteCechOneBoundaryLifts
end
#print axioms CycleQ2FiniteCechOneBoundaryLifts.primitive_of_class_zero
#print axioms CycleQ2FiniteCechOneBoundaryLifts.difference_primitive
