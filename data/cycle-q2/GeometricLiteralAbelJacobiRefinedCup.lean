import Proposal.GeometricLiteralAbelJacobiSurfaceClass
import Proposal.GeometricLiteralAbelJacobiContractedCocycle
import Proposal.GeometricLiteralSheafChernKodairaSpencerCup

/-!
# Cotangent connecting faces for a divisor on a refined native cover

On every common subopen, multiplying the scalar evaluation by the
retained canonical cubic recovers the wedge of the second differential
edge with the one-form of the first Kodaira–Spencer edge.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAbelJacobiRefinedCup

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralNativeGaugeSections
  CycleQ2LiteralNativeDifferentialSections CycleQ2LiteralNativeChernCocycle
  CycleQ2LiteralNativeTangentEvaluation CycleQ2LiteralNativeKodairaSpencerCocycle
  CycleQ2LiteralSheafChernKodairaSpencerCup
  CycleQ2LiteralAbelJacobiContractedCocycle CycleQ2LiteralAbelJacobiSurfaceClass
  CycleQ2GeometricExteriorSheaf CycleQ2CanonicalResidueDiagram

open CycleQ2CechTwoToDerived (app)

variable {I : Type} (U : I → Surface.Opens) (r : I → Vertex)
  (hU : ∀ i, U i ≤ cover (r i)) (α : One differentialAddSheaf U)

def scalarValue (i j k : I) (W : Surface.Opens)
    (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k) : Γ(Surface,W) :=
  evaluateTangent W (kodairaSpencerValue (r i) (r j) W (hi.trans (hU i)) (hj.trans (hU j)))
    (edgeValue differentialAddSheaf U α j k W hj hk)

def scalarCup : Two coefficientSheaf U := fun i j k =>
  scalarValue U r hU α i j k ((U i ⊓ U j) ⊓ U k)
    (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) inf_le_right

theorem scalarCup_face (i j k : I) (W : Surface.Opens)
    (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k) :
    faceValue coefficientSheaf U (scalarCup U r hU α) i j k W hi hj hk =
      scalarValue U r hU α i j k W hi hj hk := by
  let V := (U i ⊓ U j) ⊓ U k
  let h : W ≤ V := le_inf (le_inf hi hj) hk
  let hij₁ : V ≤ U i := inf_le_left.trans inf_le_left
  let hij₂ : V ≤ U j := inf_le_left.trans inf_le_right
  let hjk : V ≤ U k := inf_le_right
  let δ := kodairaSpencerValue (r i) (r j) V (hij₁.trans (hU i)) (hij₂.trans (hU j))
  let γ := edgeValue differentialAddSheaf U α j k V hij₂ hjk
  change res coefficientSheaf h (evaluateTangent V δ γ) = _
  rw [← evaluateTangent_restrict h δ γ]
  have hδ := kodairaSpencerValue_restrict (r i) (r j) h (hij₁.trans (hU i)) (hij₂.trans (hU j))
  have hγ : res differentialAddSheaf h γ = edgeValue differentialAddSheaf U α j k W hj hk :=
    res_comp differentialAddSheaf _ _ _
  exact congrArg₂ (evaluateTangent W · ·) hδ hγ

/-- The original residue formula on any refinement and any differential edge. -/
theorem wedge_face (i j k : I) (W : Surface.Opens) (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k) :
    wedgeSection Surface.sheaf DifferentialSheaf.val 2 W
      ![edgeValue differentialAddSheaf U α j k W hj hk,
        contractedValue (r i) (r j) W (hi.trans (hU i)) (hj.trans (hU j))] =
      (show Γ(Surface,W) from faceValue coefficientSheaf U (scalarCup U r hU α) i j k W hi hj hk) •
        formRestriction tangentCubicForm W := by
  rw [scalarCup_face]
  exact wedge_interior W _ _ _

/-- On the original native atlas, the Cartier dlog wedge is the retained
canonical form multiplied by the original sheaf-valued scalar cup. -/
theorem original_chern_wedge (u v w : Vertex) (W : Surface.Opens) (hu : W ≤ cover u)
    (hv : W ≤ cover v) (hw : W ≤ cover w) :
    wedgeSection Surface.sheaf DifferentialSheaf.val 2 W
      ![chernValue v w W hv hw, contractedValue u v W hu hv] =
        (show Γ(Surface,W) from sheafCupValue u v w W hu hv hw) • formRestriction tangentCubicForm W := by
  unfold sheafCupValue
  rw [edgeValue_kodairaSpencerOne, edgeValue_chernOne]
  exact wedge_interior W _ _ _


end CycleQ2LiteralAbelJacobiRefinedCup
end

#print axioms CycleQ2LiteralAbelJacobiRefinedCup.original_chern_wedge
#print axioms CycleQ2LiteralAbelJacobiRefinedCup.wedge_face
