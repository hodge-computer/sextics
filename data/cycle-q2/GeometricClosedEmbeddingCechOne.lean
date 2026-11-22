import Proposal.GeometricClosedEmbeddingCohomology
import Proposal.GeometricAutomorphismCohomology
import Proposal.GeometricAutomorphismCechTwo

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

/-!
The same comparison in degree two retains both actual injective descent
steps. The first primitive is read in the direct image without changing
its sections; closed-pushforward exactness then transports its Ext boundary.
-/

noncomputable section
namespace CycleQ2ClosedEmbeddingCechTwo

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Topology
open CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
open CycleQ2FiniteCechDescent CycleQ2FiniteCechHOne CycleQ2FiniteCechConnecting
open CycleQ2ClosedEmbeddingSheafExact CycleQ2ClosedEmbeddingCohomology
open CycleQ2CechTwoToDerived (presentation presentation_shortExact app sectionExtZero)
open CycleQ2FiniteCechOrbitPullback (cover cover_top pullTwo pullTwo_normalized pullTwo_closed)
open CycleQ2AutomorphismCechTwo (directImage_normalized directImage_closed cechTwoClass_map)

local instance (Z : TopCat.{0}) : HasExt.{1} (AbSheaf Z) := HasExt.standard _
local instance (Z : TopCat.{0}) : HasExt.{1} (Z.Sheaf AddCommGrpCat.{0}) := HasExt.standard _

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (hf : IsClosedEmbedding f)
variable {ι : Type} [Fintype ι] (U : ι → Opens Y) (hU : (⨆ i, U i) = ⊤)

private theorem push_one {G : AbSheaf X} (c : One G (cover f U))
    (hc : IsOneCocycle G (cover f U) c)
    (hd : IsOneCocycle ((push f).obj G) U c) :
    pushHEquiv f hf G 1 (cechOneClass (cover f U) (cover_top f U hU) c hc) =
      cechOneClass U hU c hd := by
  let V := cover f U
  let d := Classical.choice (oneDescent_nonempty V (cover_top f U hU) c hc)
  rw [cechOneClass_eq_descentClass V (cover_top f U hU) c hc d]
  change pushHEquiv f hf G 1 ((sectionExtZero ⊤ d.globalSection).comp
    (presentation_shortExact G).extClass rfl) = _
  rw [pushHEquiv_connecting f hf (presentation_shortExact G) 0,
    CycleQ2ClosedEmbeddingCechOne.pushHEquiv_section]
  symm
  apply CycleQ2AutomorphismCohomology.cechOneClass_of_lifts U hU
    (pushShortExact f hf (presentation_shortExact G)) c hd d.primitive d.globalSection
  · intro i j W hi hj
    exact d.differential i j ((Opens.map f).obj W)
      (fun _ hx => hi hx) (fun _ hx => hj hx)
  · exact d.global_restriction

private theorem directImage_boundary {S : ShortComplex (AbSheaf X)}
    {b : One S.X₂ (cover f U)} {c : Two S.X₁ (cover f U)}
    (hb : ∀ i j k W hi hj hk,
      boundaryValue S.X₂ (cover f U) b i j k W hi hj hk =
        app S.f W (faceValue S.X₁ (cover f U) c i j k W hi hj hk)) :
    ∀ i j k W hi hj hk,
      boundaryValue ((push f).obj S.X₂) U b i j k W hi hj hk =
        app ((push f).map S.f) W
          (faceValue ((push f).obj S.X₁) U c i j k W hi hj hk) :=
  fun i j k W hi hj hk => hb i j k ((Opens.map f).obj W)
    (fun _ hx => hi hx) (fun _ hx => hj hx) (fun _ hx => hk hx)

/-- Closed direct image sends the actual normalized two-class to the
class of the same sections on the ambient cover. Both connecting maps
are those of the original injective presentations. -/
theorem pushHEquiv_cechTwoClass {G : AbSheaf X} (c : Two G (cover f U))
    (hn : NormalizedTwo G (cover f U) c) (hc : IsTwoCocycle G (cover f U) c) :
    pushHEquiv f hf G 2
        (cechTwoClass (cover f U) (cover_top f U hU) c hn hc) =
      cechTwoClass U hU c (directImage_normalized f U hn) (directImage_closed f U hc) := by
  let V := cover f U
  let S := presentation G
  let P := push f
  let d := Classical.choice (twoDescent_nonempty V (cover_top f U hU) c hn hc)
  have hS : S.ShortExact := presentation_shortExact G
  have hp := pushShortExact f hf hS
  have hb := directImage_boundary f U (S := S) d.first_differential
  have he := cechOneClass_connecting V hS (cover_top f U hU) d.first c hn hc
    d.first_differential
  have he' := cechOneClass_connecting U hp hU d.first c
    (directImage_normalized f U hn) (directImage_closed f U hc) hb
  rw [← he]
  refine (pushHEquiv_connecting f hf hS 1 _).trans ?_
  exact (congrArg (fun x : ((S.map P).X₃).H' 1 ⊤ =>
      x.comp hp.extClass (rfl : 1 + 1 = 2))
    (push_one f hf U hU (mapOne V S.g d.first)
      (primitive_image_closed V S c d.first d.first_differential)
      (primitive_image_closed U (S.map P) c d.first hb))).trans he'

/-- The inverse closed-pushforward equivalence restricts an actual
normalized degree-two class by applying the given coefficient morphism
to its original face sections. -/
theorem restrict_cech {F : AbSheaf Y} {G : AbSheaf X}
    (φ : F ⟶ (push f).obj G) (c : Two F U)
    (hn : NormalizedTwo F U c) (hc : IsTwoCocycle F U c) :
    (pushHEquiv f hf G 2).symm
        ((cechTwoClass U hU c hn hc).comp (Ext.mk₀ φ) (add_zero 2)) =
      cechTwoClass (cover f U) (cover_top f U hU) (pullTwo f φ U c)
        (pullTwo_normalized f φ U c hn) (pullTwo_closed f φ U c hc) := by
  apply (pushHEquiv f hf G 2).injective
  rw [AddEquiv.apply_symm_apply, pushHEquiv_cechTwoClass f hf U hU]
  exact cechTwoClass_map U hU φ c hn hc

end CycleQ2ClosedEmbeddingCechTwo
end

#print axioms CycleQ2ClosedEmbeddingCechTwo.pushHEquiv_cechTwoClass
#print axioms CycleQ2ClosedEmbeddingCechTwo.restrict_cech
