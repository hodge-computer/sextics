import Proposal.GeometricLiteralNativeKodairaSpencerCocycle

/-!
# The actual Chern/KS sheaf cocycles have the original nonzero scalar cup

The local value is genuine evaluation of the actual tangent-sheaf
Kodaira--Spencer cocycle on the actual differential-sheaf Cartier dlog
cocycle. On every common open this equals the original native scalar
contraction. Its ordered alternating Cech cup therefore represents the
already checked nonzero global class of the original structure sheaf.

This does not assert the remaining Abel--Jacobi, cylinder, supported
variation, or global de Rham comparison.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralSheafChernKodairaSpencerCup

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech CycleQ2FiniteCechDescent
  CycleQ2GeometricIntrinsicNormal CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveIntersectionRestrictions CycleQ2LiteralNativeDifferentialSections
  CycleQ2LiteralNativeChernCocycle CycleQ2LiteralNativeTangentEvaluation
  CycleQ2LiteralNativeKodairaSpencerCocycle CycleQ2LiteralNativeGaugeSections
  CycleQ2LiteralNativeCupSectionValues CycleQ2LiteralNativeCupDerivedClass

local instance schemeSheavesHasExt (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

theorem evaluateTangent_restrict {U V : Surface.Opens} (h : V ≤ U)
    (δ : Sections tangentAddSheaf U) (ω : Sections differentialAddSheaf U) :
    evaluateTangent V (res tangentAddSheaf h δ) (res differentialAddSheaf h ω) =
      res coefficientSheaf h (evaluateTangent U δ ω) :=
  localLinearHomEvaluate_restrict Surface.sheaf DifferentialSheaf structureModule (homOfLE h) δ ω

def sheafCupValue (u v w : Vertex) (W : Surface.Opens)
    (hu : W ≤ cover u) (hv : W ≤ cover v) (hw : W ≤ cover w) : Sections coefficientSheaf W :=
  evaluateTangent W (edgeValue tangentAddSheaf cover kodairaSpencerOne u v W hu hv)
    (edgeValue differentialAddSheaf cover chernOne v w W hv hw)

theorem sheafCupValue_eq_native (u v w : Vertex) (W : Surface.Opens)
    (hu : W ≤ cover u) (hv : W ≤ cover v) (hw : W ≤ cover w) :
    sheafCupValue u v w W hu hv hw = nativeCupValue u v w W hu hv hw := by
  unfold sheafCupValue
  rw [edgeValue_kodairaSpencerOne, edgeValue_chernOne,
    kodairaSpencerValue_common {u,v,w} (by simp) u v (by simp) (by simp) W (common_le_triple u v w W hu hv hw),
    chernValue_common {u,v,w} (by simp) v w (by simp) (by simp) W (common_le_triple u v w W hu hv hw)]
  calc
    _ = res coefficientSheaf (common_le_triple u v w W hu hv hw)
        (evaluateTangent (closedOpen {u,v,w})
          (nativeKodairaSpencerSection {u,v,w} (by simp) u v (by simp) (by simp))
          (nativeChernSection {u,v,w} (by simp) v w (by simp) (by simp))) :=
      evaluateTangent_restrict (common_le_triple u v w W hu hv hw) _ _
    _ = res coefficientSheaf (common_le_triple u v w W hu hv hw)
        (closedSectionsEquiv {u,v,w} (by simp)
          (CycleQ2LiteralNativeCupFrameGauge.nativeCup {u,v,w} u v w (by simp) (by simp) (by simp))) :=
      congrArg (res coefficientSheaf (common_le_triple u v w W hu hv hw))
        (nativeKodairaSpencer_evaluate_chern {u,v,w} (by simp) u v w (by simp) (by simp) (by simp))
    _ = _ := rfl

/-- The ordered alternating cup formed from the two actual sheaf-valued
one-cocycles, using their genuine evaluation pairing. -/
def sheafCupCocycle : Two coefficientSheaf cover := fun u v w =>
  let W := (cover u ⊓ cover v) ⊓ cover w
  let hu : W ≤ cover u := inf_le_left.trans inf_le_left
  let hv : W ≤ cover v := inf_le_left.trans inf_le_right
  let hw : W ≤ cover w := inf_le_right
  if rank u < rank v ∧ rank v < rank w then sheafCupValue u v w W hu hv hw
  else if rank u < rank w ∧ rank w < rank v then -sheafCupValue u w v W hu hw hv
  else if rank v < rank u ∧ rank u < rank w then -sheafCupValue v u w W hv hu hw
  else if rank v < rank w ∧ rank w < rank u then sheafCupValue v w u W hv hw hu
  else if rank w < rank u ∧ rank u < rank v then sheafCupValue w u v W hw hu hv
  else if rank w < rank v ∧ rank v < rank u then -sheafCupValue w v u W hw hv hu
  else 0

theorem sheafCupCocycle_eq_native : sheafCupCocycle = nativeCupCocycle := by
  funext u v w
  simp only [sheafCupCocycle, nativeCupCocycle, sheafCupValue_eq_native]

theorem sheafCupCocycle_normalized : NormalizedTwo coefficientSheaf cover sheafCupCocycle := by
  rw [sheafCupCocycle_eq_native]
  exact nativeCupCocycle_normalized

theorem sheafCupCocycle_closed : IsTwoCocycle coefficientSheaf cover sheafCupCocycle := by
  rw [sheafCupCocycle_eq_native]
  exact nativeCupCocycle_closed

def sheafCupDerivedClass : coefficientSheaf.H' 2 ⊤ :=
  cechTwoClass cover cover_covers sheafCupCocycle sheafCupCocycle_normalized sheafCupCocycle_closed

theorem sheafCupDerivedClass_eq_native : sheafCupDerivedClass = nativeCupDerivedClass := by
  unfold sheafCupDerivedClass nativeCupDerivedClass
  simp only [sheafCupCocycle_eq_native]

theorem sheafCupDerivedClass_eq_original :
    sheafCupDerivedClass = CycleQ2LiteralCartierProjectedCup.projectedDerivedClass :=
  sheafCupDerivedClass_eq_native.trans nativeCupDerivedClass_eq_original

theorem sheafCupDerivedClass_ne_zero : sheafCupDerivedClass ≠ 0 := by
  rw [sheafCupDerivedClass_eq_native]
  exact nativeCupDerivedClass_ne_zero

end CycleQ2LiteralSheafChernKodairaSpencerCup

end

#print axioms CycleQ2LiteralSheafChernKodairaSpencerCup.sheafCupValue_eq_native
#print axioms CycleQ2LiteralSheafChernKodairaSpencerCup.sheafCupDerivedClass_eq_original
#print axioms CycleQ2LiteralSheafChernKodairaSpencerCup.sheafCupDerivedClass_ne_zero
