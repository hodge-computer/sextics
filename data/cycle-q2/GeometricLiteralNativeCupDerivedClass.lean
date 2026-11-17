import Proposal.GeometricLiteralNativeConeSectionFaces

/-!
# The actual native scalar cup represents the original nonzero derived class

The cochain below is defined directly from the actual native contraction
on increasing vertices, with the six alternating extensions and zero
repeated vertices. The proved projection and frame-gauge identities
identify it with the original refined projected cup minus the explicit
gauge boundary. Its actual derived scalar class is therefore the earlier
nonzero class, in the original additive structure sheaf.

Identification with a cup of the actual differential-sheaf Chern and KS
classes remains a further factor comparison.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralNativeCupDerivedClass

open AlgebraicGeometry CategoryTheory TopologicalSpace
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech CycleQ2FiniteCechDescent
  CycleQ2CartierProjectiveCover CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralNativeGaugeSections CycleQ2LiteralGaugeAdjustedCohomology
  CycleQ2LiteralNativeCupSectionValues CycleQ2LiteralNativeConeSectionFaces

local instance schemeSheavesHasExt (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

theorem gaugeAdjustedCup_increasing (u v w : Vertex) (huv : rank u < rank v) (hvw : rank v < rank w)
    (W : Opens (projectiveSurface 57 1)) (hu : W ≤ cover u) (hv : W ≤ cover v) (hw : W ≤ cover w) :
    faceValue coefficientSheaf cover gaugeAdjustedCup u v w W hu hv hw = nativeCupValue u v w W hu hv hw := by
  rw [gaugeAdjustedCup, CycleQ2LiteralGaugeAdjustedCohomology.faceValue_sub, faceValue_gaugeBoundary,
    ← coneCupValue_refined_nondecreasing u v w (rank_first_mono (Nat.le_of_lt huv))
      (rank_first_mono (Nat.le_of_lt hvw)) W hu hv hw,
    gaugeBoundaryValue_increasing u v w huv hvw]
  exact (nativeCupValue_eq_cone_sub_boundary u v w W hu hv hw).symm

/-- Direct alternating extension of the actual native contraction on
increasing vertices of the original twelve-open atlas. -/
def nativeCupCocycle : Two coefficientSheaf cover := fun u v w =>
  let W := (cover u ⊓ cover v) ⊓ cover w
  let hu : W ≤ cover u := inf_le_left.trans inf_le_left
  let hv : W ≤ cover v := inf_le_left.trans inf_le_right
  let hw : W ≤ cover w := inf_le_right
  if rank u < rank v ∧ rank v < rank w then nativeCupValue u v w W hu hv hw
  else if rank u < rank w ∧ rank w < rank v then -nativeCupValue u w v W hu hw hv
  else if rank v < rank u ∧ rank u < rank w then -nativeCupValue v u w W hv hu hw
  else if rank v < rank w ∧ rank w < rank u then nativeCupValue v w u W hv hw hu
  else if rank w < rank u ∧ rank u < rank v then nativeCupValue w u v W hw hu hv
  else if rank w < rank v ∧ rank v < rank u then -nativeCupValue w v u W hw hv hu
  else 0

theorem nativeCupCocycle_increasing (u v w : Vertex) (huv : rank u < rank v) (hvw : rank v < rank w) :
    nativeCupCocycle u v w = nativeCupValue u v w ((cover u ⊓ cover v) ⊓ cover w)
      (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) inf_le_right := by
  dsimp only [nativeCupCocycle]
  rw [if_pos ⟨huv,hvw⟩]

theorem nativeCupCocycle_eq_gaugeAdjusted : nativeCupCocycle = gaugeAdjustedCup := by
  funext u v w
  let W := (cover u ⊓ cover v) ⊓ cover w
  have hu : W ≤ cover u := inf_le_left.trans inf_le_left
  have hv : W ≤ cover v := inf_le_left.trans inf_le_right
  have hw : W ≤ cover w := inf_le_right
  have hself : faceValue coefficientSheaf cover gaugeAdjustedCup u v w W hu hv hw = gaugeAdjustedCup u v w :=
    res_self coefficientSheaf W _
  rw [← hself]
  dsimp only [nativeCupCocycle]
  split_ifs with h012 h021 h102 h120 h201 h210
  · exact (gaugeAdjustedCup_increasing u v w h012.1 h012.2 W hu hv hw).symm
  · rw [gaugeAdjustedCup_normalized.swap23 u v w W hu hv hw,
      gaugeAdjustedCup_increasing u w v h021.1 h021.2 W hu hw hv]
  · rw [gaugeAdjustedCup_normalized.swap12 u v w W hu hv hw,
      gaugeAdjustedCup_increasing v u w h102.1 h102.2 W hv hu hw]
  · rw [gaugeAdjustedCup_normalized.rotate v w u W hv hw hu,
      gaugeAdjustedCup_increasing v w u h120.1 h120.2 W hv hw hu]
  · rw [← gaugeAdjustedCup_normalized.rotate u v w W hu hv hw,
      gaugeAdjustedCup_increasing w u v h201.1 h201.2 W hw hu hv]
  · rw [gaugeAdjustedCup_normalized.swap12 u v w W hu hv hw,
      ← gaugeAdjustedCup_normalized.rotate v u w W hv hu hw,
      gaugeAdjustedCup_increasing w v u h210.1 h210.2 W hw hv hu]
  · have hrep : rank u = rank v ∨ rank v = rank w ∨ rank u = rank w := by omega
    rcases hrep with h | h | h
    · have he := rank_injective h
      subst v
      exact (gaugeAdjustedCup_normalized.repeat12 u w W hu hw).symm
    · have he := rank_injective h
      subst w
      exact (gaugeAdjustedCup_normalized.repeat23 u v W hu hv).symm
    · have he := rank_injective h
      subst w
      exact (gaugeAdjustedCup_normalized.repeat13 u v W hu hv).symm

theorem nativeCupCocycle_normalized : NormalizedTwo coefficientSheaf cover nativeCupCocycle := by
  rw [nativeCupCocycle_eq_gaugeAdjusted]
  exact gaugeAdjustedCup_normalized

theorem nativeCupCocycle_closed : IsTwoCocycle coefficientSheaf cover nativeCupCocycle := by
  rw [nativeCupCocycle_eq_gaugeAdjusted]
  exact gaugeAdjustedCup_closed

def nativeCupDerivedClass : coefficientSheaf.H' 2 ⊤ :=
  cechTwoClass cover cover_covers nativeCupCocycle nativeCupCocycle_normalized nativeCupCocycle_closed

theorem nativeCupDerivedClass_eq_original :
    nativeCupDerivedClass = CycleQ2LiteralCartierProjectedCup.projectedDerivedClass := by
  unfold nativeCupDerivedClass
  simpa only [nativeCupCocycle_eq_gaugeAdjusted] using gaugeAdjustedCup_class

theorem nativeCupDerivedClass_ne_zero : nativeCupDerivedClass ≠ 0 := by
  rw [nativeCupDerivedClass_eq_original]
  exact CycleQ2LiteralCartierProjectedCup.projectedDerivedClass_ne_zero

end CycleQ2LiteralNativeCupDerivedClass

end

#print axioms CycleQ2LiteralNativeCupDerivedClass.nativeCupCocycle_eq_gaugeAdjusted
#print axioms CycleQ2LiteralNativeCupDerivedClass.nativeCupDerivedClass_eq_original
#print axioms CycleQ2LiteralNativeCupDerivedClass.nativeCupDerivedClass_ne_zero
