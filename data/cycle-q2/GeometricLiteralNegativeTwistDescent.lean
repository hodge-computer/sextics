import Proposal.GeometricFiniteCechHOneRefinement

/-!
# Degree-one descent from an affine cover

Local vanishing in degree one lifts any global section of an injective
presentation's quotient on each vertex. The differences of the lifts define
a Čech cocycle representing the prescribed derived class. On the three
coordinate opens only its increasing edges are needed to exhibit a primitive.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralNegativeTwistDescent

open CategoryTheory CategoryTheory.Abelian TopologicalSpace
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
  CycleQ2FiniteCechDescent CycleQ2FiniteCechHOne
open CycleQ2CechTwoToDerived (presentation presentation_shortExact sectionExtZero app app_res app_injective sections_exact
  sections_surjective_of_H_one_subsingleton)

variable {X : TopCat.{0}} {ι : Type} [Fintype ι]
local instance sheafHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _
variable (F : AbSheaf X) (U : ι → Opens X)

/-- Every derived class is represented by a cocycle on a finite cover whose
vertices have vanishing first cohomology. -/
theorem cechOneClass_surjective_of_local_vanishing
    (hcover : (⨆ i, U i) = ⊤) (hlocal : ∀ i, Subsingleton (F.H' 1 (U i)))
    (x : F.H' 1 ⊤) :
    ∃ (c : One F U) (hc : IsOneCocycle F U c), cechOneClass U hcover c hc = x := by
  let S := presentation F
  have hS : S.ShortExact := presentation_shortExact F
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ (freeOpen (⊤ : Opens X)) hS x
    (Ext.eq_zero_of_injective _) rfl
  obtain ⟨φ,rfl⟩ := (Ext.mk₀_bijective _ _).surjective z
  let q := freeOpenSections S.X₃ ⊤ φ
  choose p hp using fun i => sections_surjective_of_H_one_subsingleton hS
    (U i) (hlocal i) (res S.X₃ le_top q)
  have diff (i j : ι) : app S.g (U i ⊓ U j)
      (res S.X₂ inf_le_right (p j) - res S.X₂ inf_le_left (p i)) = 0 := by
    rw [map_sub, app_res, app_res, hp, hp, res_comp, res_comp, sub_self]
  choose c hc using fun i j => sections_exact hS (U i ⊓ U j) _ (diff i j)
  have edge (i j : ι) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j) :
      app S.f W (edgeValue F U c i j W hi hj) =
        res S.X₂ hj (p j) - res S.X₂ hi (p i) := by
    rw [edgeValue, app_res]
    simpa only [map_sub, res_comp] using congrArg (res S.X₂ (le_inf hi hj)) (hc i j)
  have hclosed : IsOneCocycle F U c := by
    intro i j k W hi hj hk
    change edgeValue F U c i k W hi hk = edgeValue F U c i j W hi hj + edgeValue F U c j k W hj hk
    apply app_injective S.f W
    rw [map_add, edge, edge, edge]
    abel
  let d : OneDescent U c := {
    primitive := p
    differential := fun i j W hi hj => (edge i j W hi hj).symm
    globalSection := q
    global_restriction := funext (fun i => (hp i).symm) }
  refine ⟨c,hclosed,(cechOneClass_eq_descentClass U hcover c hclosed d).trans ?_⟩
  change (sectionExtZero ⊤ q).comp hS.extClass rfl = x
  simpa only [q, sectionExtZero, AddEquiv.symm_apply_apply] using hz

/-- For three ordered vertices it suffices to solve the three increasing
edge equations on their full pairwise intersections. -/
theorem hOne_subsingleton_of_three_edges (U : Fin 3 → Opens X)
    (hcover : (⨆ i, U i) = ⊤) (hlocal : ∀ i, Subsingleton (F.H' 1 (U i)))
    (hprimitive : ∀ (c : One F U), IsOneCocycle F U c →
      ∃ p : Zero F U, ∀ i j, i < j →
        res F (inf_le_right : U i ⊓ U j ≤ U j) (p j) -
          res F inf_le_left (p i) = c i j) :
    Subsingleton (F.H' 1 ⊤) := by
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨c,hc,rfl⟩ := cechOneClass_surjective_of_local_vanishing F U hcover hlocal x
  obtain ⟨p,hp⟩ := hprimitive c hc
  apply cechOneClass_eq_zero_of_primitive U hcover c hc p
  have inc (i j : Fin 3) (hij : i < j) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j) :
      res F hj (p j) - res F hi (p i) = edgeValue F U c i j W hi hj := by
    simpa only [map_sub, res_comp, edgeValue] using congrArg (res F (le_inf hi hj)) (hp i j hij)
  intro i j W hi hj
  rcases lt_trichotomy i j with h | rfl | h
  · exact inc i j h W hi hj
  · rw [sub_self]
    exact (oneCocycle_diagonal c hc i W hi).symm
  · have hc' := hc i j i W hi hj hi
    rw [oneCocycle_diagonal c hc i W hi] at hc'
    have he := inc j i h W hj hi
    unfold edgeValue at he ⊢
    linear_combination (norm := abel) hc' - he

end CycleQ2LiteralNegativeTwistDescent

end

#print axioms CycleQ2LiteralNegativeTwistDescent.cechOneClass_surjective_of_local_vanishing
#print axioms CycleQ2LiteralNegativeTwistDescent.hOne_subsingleton_of_three_edges
