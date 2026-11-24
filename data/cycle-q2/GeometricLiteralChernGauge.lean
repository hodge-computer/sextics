import Proposal.GeometricLiteralNativeChernCocycle
import Proposal.GeometricFiniteCechHOneRefinement
import Proposal.GeometricFiniteCechOneAdditivity

/-!
# Change of local frames for the Chern class of the literal surface

A unit on each member of a finite cover changes the logarithmic transition
cocycle by the Čech coboundary of its local logarithmic differentials.
The associated derived degree-one classes therefore agree.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralChernGauge

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
  CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech CycleQ2FiniteCechHOne
  CycleQ2FiniteCechOneAdditivity CycleQ2LiteralNativeDifferentialSections
  CycleQ2LiteralNativeChernCocycle CycleQ2InjectiveCech CycleQ2GeometricSectionDifferentials

local instance sheafHasExt (X : TopCat.{0}) : HasExt.{1} (AbSheaf X) := HasExt.standard _

variable {ι : Type} (U : ι → Surface.Opens)

abbrev EdgeUnits := ∀ i j, (SectionRing Surface.sheaf (U i ⊓ U j))ˣ

def logOne (u : EdgeUnits U) : One differentialAddSheaf U :=
  fun i j => sheafLogDifferential (U i ⊓ U j) (u i j)

theorem cechOneClass_eq_of_gauge [Fintype ι] (hU : (⨆ i, U i) = ⊤)
    (u v : EdgeUnits U) (hu : IsOneCocycle differentialAddSheaf U (logOne U u))
    (hv : IsOneCocycle differentialAddSheaf U (logOne U v))
    (g : ∀ i, (SectionRing Surface.sheaf (U i))ˣ)
    (hg : ∀ i j, u i j * restrictSectionUnit (inf_le_right : U i ⊓ U j ≤ U j) (g j) =
      restrictSectionUnit (inf_le_left : U i ⊓ U j ≤ U i) (g i) * v i j) :
    cechOneClass U hU (logOne U u) hu = cechOneClass U hU (logOne U v) hv := by
  let C := oneCocycles (F := differentialAddSheaf) U
  let a : C := ⟨logOne U u, hu⟩
  let b : C := ⟨logOne U v, hv⟩
  let p : CycleQ2FiniteCechDescent.Zero differentialAddSheaf U := fun i => sheafLogDifferential (U i) (g i)
  have hpair (i j : ι) :
      res differentialAddSheaf (inf_le_right : U i ⊓ U j ≤ U j) (p j) -
        res differentialAddSheaf inf_le_left (p i) = (logOne U v) i j - (logOne U u) i j := by
    have h := congrArg (sheafLogDifferential _) (hg i j)
    rw [sheafLogDifferential_mul, sheafLogDifferential_mul] at h
    have hr {i : ι} {W : Surface.Opens} (hle : W ≤ U i) :
        res differentialAddSheaf hle (p i) = sheafLogDifferential W (restrictSectionUnit hle (g i)) :=
      sheafLogDifferential_restrict hle (g i)
    rw [hr, hr]
    dsimp only [logOne]
    linear_combination (norm := abel) h
  have hzero : cechOneClass U hU (logOne U v - logOne U u) (C.sub_mem hv hu) = 0 := by
    apply cechOneClass_eq_zero_of_primitive U hU _ _ p
    intro i j W hi hj
    have h := congrArg (res differentialAddSheaf (le_inf hi hj)) (hpair i j)
    simpa only [map_sub, res_comp, edgeValue, Pi.sub_apply] using h
  have hsub := (cechOneClassHom (F := differentialAddSheaf) U hU).map_sub b a
  change cechOneClass U hU (logOne U v - logOne U u) (C.sub_mem hv hu) =
    cechOneClass U hU (logOne U v) hv - cechOneClass U hU (logOne U u) hu at hsub
  exact (sub_eq_zero.mp (hsub.symm.trans hzero)).symm

end CycleQ2LiteralChernGauge

end

#print axioms CycleQ2LiteralChernGauge.cechOneClass_eq_of_gauge
