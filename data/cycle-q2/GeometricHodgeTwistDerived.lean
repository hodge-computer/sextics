import Proposal.GeometricAffineHTwo
import Proposal.GeometricLiteralNegativeTwistDescent

/-!
# Derived vanishing from explicit finite-cover Čech primitives

Injective presentations reduce the first two derived cohomology groups to
finite-cover Čech boundary equations. In degree two only degree-two
vanishing at the vertices and degree-one vanishing on their pairwise
intersections are needed. This applies to the four-open cover used by
the weighted threefold twists.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2HodgeTwistDerived

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace
open CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
open CycleQ2FiniteCechDescent (Zero)
open CycleQ2CechTwoToDerived (presentation presentation_shortExact sections_surjective_of_H_one_subsingleton
  connecting_one_zero app)
open CycleQ2GeometricSheafCohomologyRestriction (terminalCohomologyEquiv)

variable {X : TopCat.{0}} {ι : Type} [Fintype ι] (F : AbSheaf X) (U : ι → Opens X)
local instance sheafHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _

/-- First cohomology of a finite cover with explicit primitives for every edge cocycle. -/
theorem hOne_of_primitives (hcover : (⨆ i, U i) = ⊤)
    (hvertex : ∀ i, Subsingleton (F.H' 1 (U i)))
    (hprimitive : ∀ c : One F U, IsOneCocycle F U c → ∃ p : Zero F U,
      ∀ i j W hi hj, res F hj (p j) - res F hi (p i) = edgeValue F U c i j W hi hj) :
    Subsingleton (F.H 1) := by
  haveI : Subsingleton (F.H' 1 ⊤) := by
    apply subsingleton_of_forall_eq 0
    intro x
    obtain ⟨c,hc,rfl⟩ := CycleQ2LiteralNegativeTwistDescent.cechOneClass_surjective_of_local_vanishing
      F U hcover hvertex x
    obtain ⟨p,hp⟩ := hprimitive c hc
    exact CycleQ2FiniteCechHOne.cechOneClass_eq_zero_of_primitive U hcover c hc p hp
  exact (terminalCohomologyEquiv (Opens.grothendieckTopology X) F ⊤ isTerminalTop 1).surjective.subsingleton

/-- Degree-two primitives on this cover imply vanishing in ordinary derived cohomology. -/
theorem hTwo_of_primitives (hcover : (⨆ i, U i) = ⊤)
    (hvertex : ∀ i, Subsingleton (F.H' 2 (U i)))
    (hedge : ∀ i j, Subsingleton (F.H' 1 (U i ⊓ U j)))
    (hprimitive : ∀ c : Two F U, IsTwoCocycle F U c → ∃ b : One F U,
      ∀ i j k W hi hj hk, boundaryValue F U b i j k W hi hj hk =
        faceValue F U c i j k W hi hj hk) : Subsingleton (F.H 2) := by
  let S := presentation F
  let T := presentation S.X₃
  apply CycleQ2GeometricAffineHTwo.hTwo_subsingleton_of_global_lift F
  intro z
  have hlocal (i : ι) : Subsingleton (S.X₃.H' 1 (U i)) := by
    apply subsingleton_of_forall_eq 0
    intro y
    apply connecting_one_zero (presentation_shortExact F) (U i) y
    exact @Subsingleton.elim (F.H' 2 (U i)) (hvertex i) _ _
  choose u hu using fun i => sections_surjective_of_H_one_subsingleton
    (presentation_shortExact S.X₃) (U i) (hlocal i) (res T.X₃ le_top z)
  exact CycleQ2GeometricAffineHTwo.lift_of_two_cocycle_primitives F U hcover
    (fun i j => sections_surjective_of_H_one_subsingleton (presentation_shortExact F) _ (hedge i j))
    hprimitive z u hu

end CycleQ2HodgeTwistDerived
end

#print axioms CycleQ2HodgeTwistDerived.hOne_of_primitives
#print axioms CycleQ2HodgeTwistDerived.hTwo_of_primitives
