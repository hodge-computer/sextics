import Proposal.GeometricFiniteCechOneAdditivity
import Proposal.GeometricFiniteCechHOneRefinement
import Proposal.GeometricLiteralThreefoldHodgeCech

/-!
# Comparing the acted and original ambient Čech classes

On the ordered threefold cover it suffices to compare the increasing
edges. A difference of vertex two-forms gives the same class in derived
degree-one cohomology.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralThreefoldOrbitCech

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite
  CycleQ2GeometricSheafLocalIso CycleQ2InjectiveCech CycleQ2FiniteInjectiveCech
  CycleQ2FiniteCechDescent CycleQ2FiniteCechHOne CycleQ2FiniteCechOneAdditivity
  CycleQ2LiteralThreefoldHodgeCech CycleQ2LiteralAmbientCharts

local instance sheafHasExt (X : TopCat.{0}) : HasExt.{1} (AbSheaf X) := HasExt.standard _

theorem class_eq_of_vertex_corrections {X : TopCat.{0}} {F : AbSheaf X}
    {ι : Type} [LinearOrder ι] [Fintype ι] (U : ι → Opens X) (hU : (⨆ i, U i) = ⊤)
    (c d : One F U) (hc : IsOneCocycle F U c) (hd : IsOneCocycle F U d)
    (v : Zero F U)
    (h : ∀ i j, i < j → ∀ (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j),
      edgeValue F U c i j W hi hj + res F hj (v j) =
      res F hi (v i) + edgeValue F U d i j W hi hj) :
    cechOneClass U hU d hd = cechOneClass U hU c hc := by
  let C := oneCocycles (F := F) U
  let a : C := ⟨d, hd⟩
  let b : C := ⟨c, hc⟩
  apply sub_eq_zero.mp
  change cechOneClassHom U hU a - cechOneClassHom U hU b = 0
  rw [← map_sub]
  change cechOneClass U hU (d-c) (C.sub_mem hd hc) = 0
  apply cechOneClass_eq_zero_of_primitive U hU _ _ v
  intro i j W hi hj
  change _ = res F (le_inf hi hj) (d i j - c i j)
  rw [map_sub]
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact (sub_eq_sub_iff_add_eq_add).mpr (by
      simpa only [edgeValue, add_comm, add_left_comm, add_assoc] using h i j hij W hi hj)
  · simp only [oneCocycle_diagonal c hc i W hi, oneCocycle_diagonal d hd i W hi, sub_self]
  · have h₁ := hc i j i W hi hj hi
    have h₂ := hd i j i W hi hj hi
    rw [oneCocycle_diagonal c hc i W hi] at h₁
    rw [oneCocycle_diagonal d hd i W hi] at h₂
    have hp := h j i hji W hj hi
    unfold edgeValue at hp
    linear_combination (norm := abel) h₂ - h₁ - hp

/-- The ordered edges of the ambient cocycle are the exterior forms
of the original smooth hypersurface charts. -/
theorem hodgeCocycle_edge_lt (ω : NativeEdges) (h) (i j : Fin 4) (hij : i < j)
    (W : Threefold.Opens) (hi : W ≤ fixedOpen i) (hj : W ≤ fixedOpen j) :
    edgeValue HodgeSheaf fixedOpen (hodgeCocycle ω h).val i j W hi hj =
      edge ω i j hij W (le_inf hi hj) := by
  have cases4 (t : Fin 4) : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
  rcases cases4 i with rfl | rfl | rfl | rfl <;>
    rcases cases4 j with rfl | rfl | rfl | rfl <;>
    first | exact False.elim ((by decide : ¬ _) hij) |
    simpa only [edgeValue, hodgeCocycle, CartierCechFour.fourEdgeCocycle,
      CartierCechFour.fourEdgeCochain, CartierCechFour.quad_0, CartierCechFour.quad_1,
      CartierCechFour.quad_2, CartierCechFour.quad_3, CartierCechFour.quad_mk_0,
      CartierCechFour.quad_mk_1, CartierCechFour.quad_mk_2, CartierCechFour.quad_mk_3] using edge_restrict ω _ _ hij le_rfl (le_inf hi hj)

end CycleQ2LiteralThreefoldOrbitCech
end

#print axioms CycleQ2LiteralThreefoldOrbitCech.class_eq_of_vertex_corrections
#print axioms CycleQ2LiteralThreefoldOrbitCech.hodgeCocycle_edge_lt
