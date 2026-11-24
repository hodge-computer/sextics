import Proposal.GeometricLiteralCotangentShortExact
import Proposal.GeometricLiteralOrbitBoundary
import Proposal.GeometricLiteralOrbitDerivedPullback

/-!
# Naturality of the original Chern connecting map under the projective action

The literal projective automorphism acts on the cotangent short exact sequence.
Its effect on the connecting class uses its induced map on the normal term.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralOrbitConnectingAction

open CategoryTheory AlgebraicGeometry TopologicalSpace
  CycleQ2LiteralCotangentShortExact CycleQ2LiteralOrbitAction
  CycleQ2LiteralOrbitBoundary CycleQ2LiteralOrbitDerivedPullback
  CycleQ2AutomorphismCohomology CycleQ2AutomorphismGlobalSections

local instance additiveHasExt : HasExt.{1} (TopCat.Sheaf AddCommGrpCat.{0}
    (CycleQ2LiteralProjectiveCotangent.ClosedSurface : TopCat)) := HasExt.standard _
local instance schemeSheavesHasExt (S : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{0}) := HasExt.standard _

local instance topHasExt (X : TopCat.{0}) : HasExt.{1} (CycleQ2InjectiveCech.AbSheaf X) := HasExt.standard _

private theorem pull_connecting_of_components {X : TopCat.{0}} (h : X ≅ X)
    (S : ShortComplex (CycleQ2InjectiveCech.AbSheaf X)) (hS : S.ShortExact)
    (a : S.X₁ ⟶ (pushFunctor h).obj S.X₁)
    (b : S.X₂ ⟶ (pushFunctor h).obj S.X₂)
    (c : S.X₃ ⟶ (pushFunctor h).obj S.X₃)
    (h₁ : S.f ≫ b = a ≫ (pushFunctor h).map S.f)
    (h₂ : S.g ≫ c = b ≫ (pushFunctor h).map S.g)
    (x : S.X₃.H' 1 ⊤) :
    (pullH h c 1 x).comp hS.extClass rfl = pullH h a 2 (x.comp hS.extClass rfl) := by
  let m : S ⟶ S.map (pushFunctor h) := ⟨a,b,c,h₁.symm,h₂.symm⟩
  exact pullH_connecting h hS hS m 1 x

variable (z : ℂ) (hz : z ^ 3 = 1)

private abbrev e := Scheme.forgetToTop.mapIso (closedProjectiveAction z hz)

def boundaryPull : cotangentAdditiveComplex.X₁.H' 2 ⊤ →+ cotangentAdditiveComplex.X₁.H' 2 ⊤ :=
  pullH (e z hz) (additiveNormal z hz) 2

theorem chernPull_connecting (x : cotangentAdditiveComplex.X₃.H' 1 ⊤) :
    (chernPull z hz x).comp cotangentAdditiveShortExact.extClass rfl =
      boundaryPull z hz (x.comp cotangentAdditiveShortExact.extClass rfl) :=
  pull_connecting_of_components (e z hz) cotangentAdditiveComplex cotangentAdditiveShortExact
    (additiveNormal z hz) (additiveMiddle z hz) (additiveDifferential z hz)
    (additive_inclusion_comm z hz) (additive_reduction_comm z hz) x

end CycleQ2LiteralOrbitConnectingAction
end

#print axioms CycleQ2LiteralOrbitConnectingAction.chernPull_connecting
