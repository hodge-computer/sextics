import Proposal.GeometricClosedEmbeddingCohomology
import Proposal.GeometricAutomorphismCohomology

/-!
# Čech representatives for restriction to a closed subspace

The derived direct-image equivalence for a closed embedding carries
the class of a cocycle on an inverse-image cover to the same sections
on the original cover. This identifies the cohomology class obtained
from the inverse equivalence directly on a curve.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2ClosedEmbeddingCechOne

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace Topology
  CycleQ2InjectiveCech CycleQ2CechTwoToDerived CycleQ2ClosedEmbeddingSheafExact
  CycleQ2ClosedEmbeddingCohomology CycleQ2FiniteCechHOne CycleQ2FiniteInjectiveCech
  CycleQ2FiniteCechDescent CycleQ2AutomorphismCohomology
open CycleQ2FiniteCechOrbitPullback (cover cover_top pullOne pullOne_closed)

local instance (Z : TopCat.{0}) : HasExt.{1} (AbSheaf Z) := HasExt.standard _
local instance (Z : TopCat.{0}) : HasExt.{1} (Z.Sheaf AddCommGrpCat.{0}) := HasExt.standard _

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (hf : IsClosedEmbedding f)

private abbrev directSource : freeOpen (⊤ : Opens Y) ⟶ (push f).obj (freeOpen (⊤ : Opens X)) :=
  (freeOpenSections _ ⊤).symm (freeOpenSections (freeOpen (⊤ : Opens X)) ⊤ (𝟙 _))

theorem pushHEquiv_section (M : AbSheaf X) (s : Sections M ⊤) :
    pushHEquiv f hf M 0 (sectionExtZero ⊤ s) =
      sectionExtZero (F := (push f).obj M) ⊤ s := by
  let := push_preservesFiniteColimits f hf
  let := push_preservesInjectiveObjects f
  change (Ext.mk₀ (directSource f)).comp
    ((Ext.mk₀ ((freeOpenSections M ⊤).symm s)).mapExactFunctor (push f)) (zero_add 0) =
    Ext.mk₀ ((freeOpenSections ((push f).obj M) ⊤).symm s)
  rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
  apply congrArg Ext.mk₀
  apply (freeOpenSections ((push f).obj M) ⊤).injective
  rw [AddEquiv.apply_symm_apply, ← freeOpenSections_postcomp, directSource, AddEquiv.apply_symm_apply]
  change app ((freeOpenSections M ⊤).symm s) ⊤ (freeOpenSections (freeOpen (⊤ : Opens X)) ⊤ (𝟙 _)) = s
  rw [freeOpenSections_postcomp, Category.id_comp, AddEquiv.apply_symm_apply]

/-- On a finite cover of the ambient space the inverse closed-pushforward
equivalence agrees with pulling back the cocycle by the given coefficient map. -/
theorem restrict_cech {ι : Type} [Fintype ι] {F : AbSheaf Y} {G : AbSheaf X}
    (φ : F ⟶ (push f).obj G) (U : ι → Opens Y) (hU : (⨆ i, U i) = ⊤)
    (c : One F U) (hc : IsOneCocycle F U c) :
    (pushHEquiv f hf G 1).symm ((cechOneClass U hU c hc).comp (Ext.mk₀ φ) (add_zero 1)) =
      cechOneClass (cover f U) (cover_top f U hU) (pullOne f φ U c) (pullOne_closed f φ U c hc) := by
  let p := pullOne f φ U c
  let hp := pullOne_closed f φ U c hc
  let V := cover f U
  let d := Classical.choice (oneDescent_nonempty V (cover_top f U hU) p hp)
  apply (pushHEquiv f hf G 1).injective
  rw [AddEquiv.apply_symm_apply, cechOneClass_naturality, cechOneClass_eq_descentClass V (cover_top f U hU) p hp d]
  change cechOneClass U hU _ _ = pushHEquiv f hf G 1
    ((sectionExtZero ⊤ d.globalSection).comp (presentation_shortExact G).extClass rfl)
  rw [pushHEquiv_connecting f hf (presentation_shortExact G) 0, pushHEquiv_section]
  apply cechOneClass_of_lifts U hU (pushShortExact f hf (presentation_shortExact G))
    (mapOne U φ c) (mapOne_closed U φ c hc) d.primitive d.globalSection
  · intro i j W hi hj
    exact d.differential i j ((Opens.map f).obj W) (fun _ hx => hi hx) (fun _ hx => hj hx)
  · exact d.global_restriction

end CycleQ2ClosedEmbeddingCechOne
end

#print axioms CycleQ2ClosedEmbeddingCechOne.restrict_cech
