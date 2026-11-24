import Proposal.GeometricCechRefinement

/-!
# Naturality of degree-two finite-cover Čech descent

A morphism of abelian sheaves transports both injective primitives and
the glued global section. This computes the induced morphism on H² for
every normalized two-cocycle on a finite open cover.

Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2FiniteCechTwoNaturality

open CategoryTheory Opposite TopologicalSpace
open CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso
  CycleQ2FiniteInjectiveCech CycleQ2FiniteCechDescent
open CycleQ2CechTwoToDerived (presentation presentation_shortExact app app_comp app_res)
open CycleQ2CechTwoComparison (sectionExtZero_app)
open CycleQ2CechTwoNaturality (presentationMap secondPresentationMap derivedMap
  derivedMap_apply connecting_naturality)

variable {X : TopCat.{0}} {ι : Type} {F G : AbSheaf X} (U : ι → Opens X)
local instance sheafHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _

/-- Transport the two primitives and the final quotient section along the
maps between the chosen injective presentations. -/
def transportDescent (f : F ⟶ G) {c : Two F U} (d : TwoDescent U c) :
    TwoDescent U (mapTwo U f c) where
  first := mapOne U (presentationMap f).τ₂ d.first
  first_differential i j k W hi hj hk := by
    rw [boundaryValue_mapOne, d.first_differential, faceValue_mapTwo, app_comp, app_comp,
      ← (presentationMap f).comm₁₂]
  second := mapZero U (secondPresentationMap f).τ₂ d.second
  second_differential i j W hi hj := by
    dsimp only [mapZero]
    rw [← app_res, ← app_res, ← map_sub, d.second_differential,
      edgeValue_mapOne, app_comp, app_comp, app_comp, app_comp]
    congr 2
    change (presentation F).g ≫ (presentation (presentation F).X₃).f ≫
      (secondPresentationMap f).τ₂ = (presentationMap f).τ₂ ≫ (presentation G).g ≫
      (presentation (presentation G).X₃).f
    rw [← (secondPresentationMap f).comm₁₂]
    change (presentation F).g ≫ (presentationMap f).τ₃ ≫ _ = _
    rw [← Category.assoc, ← (presentationMap f).comm₂₃, Category.assoc]
  globalSection := app (secondPresentationMap f).τ₃ ⊤ d.globalSection
  global_restriction := by
    funext i
    have hi := congrFun d.global_restriction i
    dsimp only [globalZero, mapZero] at hi ⊢
    rw [← app_res, hi, app_comp, app_comp, (secondPresentationMap f).comm₂₃]

theorem descentClass_naturality (f : F ⟶ G) {c : Two F U} (d : TwoDescent U c) :
    derivedMap f (descentClass U d) = descentClass U (transportDescent U f d) := by
  simp only [derivedMap_apply, descentClass, transportDescent]
  rw [connecting_naturality (presentation_shortExact F) (presentation_shortExact G)
      (presentationMap f),
    connecting_naturality (presentation_shortExact (presentation F).X₃)
      (presentation_shortExact (presentation G).X₃) (secondPresentationMap f),
    ← sectionExtZero_app]

/-- Finite-cover normalized Čech descent commutes with the intrinsic H² map. -/
theorem cechTwoClass_naturality [Fintype ι] (hcover : (⨆ i, U i) = ⊤) (f : F ⟶ G)
    (c : Two F U) (hn : NormalizedTwo F U c) (hc : IsTwoCocycle F U c) :
    derivedMap f (cechTwoClass U hcover c hn hc) =
      cechTwoClass U hcover (mapTwo U f c) (mapTwo_normalized U f c hn)
        (mapTwo_closed U f c hc) := by
  let d := Classical.choice (twoDescent_nonempty U hcover c hn hc)
  change derivedMap f (descentClass U d) = _
  rw [descentClass_naturality]
  exact (cechTwoClass_eq_descentClass U hcover _ _ _ (transportDescent U f d)).symm

end CycleQ2FiniteCechTwoNaturality

#print axioms CycleQ2FiniteCechTwoNaturality.cechTwoClass_naturality
