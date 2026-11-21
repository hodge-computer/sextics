import Proposal.GeometricHodgeTwistRatios
import Proposal.GeometricHodgeAtlasFrames

/-!
# Twists and their homogeneous sections on the moving threefold

The coefficient on the j-th frame changes by (xⱼ/xᵢ)ᵏ in the i-th frame.
The resulting O(k) has a linear trivialization on each actual weight-one
coordinate chart. Homogeneous elements of the original cone give global
sections whose coordinates are the literal normalized Proj fractions.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeThreefoldTwist

open AlgebraicGeometry CategoryTheory Opposite
open CycleQ2GeometricHodgeThreefold (threefold grade cone)
open CycleQ2HodgeAtlasLine CycleQ2HodgeTwistRatios
open CycleQ2GeometricProjectiveCurve.Twisted (res res_self res_comp)
open CycleQ2GenericSexticGradient (CoeffRing)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R)

def cocycle (k : ℤ) : Transition (U φ) where
  unit i j V hi hj := transition φ i j V hi hj ^ k
  self i V hi := by rw [transition_self, one_zpow]
  compose i j l V hi hj hl := by rw [← mul_zpow, transition_comp]
  restrict i j {V W} hi hj hW := by
    rw [map_zpow]
    exact congrArg (fun z : Γ(threefold φ,W)ˣ => z ^ k) (transition_restrict φ i j hi hj hW)

def twist (k : ℤ) := line (cocycle φ k)

def chartFrame (k : ℤ) (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i) :
    Γ(twist φ k,V) ≃ₗ[Γ(threefold φ,V)] Γ(threefold φ,V) := frame (cocycle φ k) i V hi

theorem chartFrame_transition (k : ℤ) (i j : Fin 4) (V : (threefold φ).Opens)
    (hi : V ≤ U φ i) (hj : V ≤ U φ j) (s : Γ(twist φ k,V)) :
    chartFrame φ k i V hi s =
      (transition φ i j V hi hj ^ k : Γ(threefold φ,V)ˣ).val * chartFrame φ k j V hj s :=
  coordinate_transition (cocycle φ k) i j V hi hj s

def homogeneousSection {n : ℕ} (p : cone φ) (hp : p ∈ grade φ n) (V : (threefold φ).Opens) :
    Γ(twist φ (n : ℤ),V) := by
  refine pack (cocycle φ n) V (fun i => normalized φ i p hp (V ⊓ U φ i) inf_le_right) ?_
  intro i j
  let W := triple (U := U φ) V i j
  have h₁ : W ≤ V ⊓ U φ i := inf_le_inf_left V inf_le_left
  have h₂ : W ≤ V ⊓ U φ j := inf_le_inf_left V inf_le_right
  have h₁' : restrictRing (X := threefold φ) h₁
      (normalized φ i p hp (V ⊓ U φ i) inf_le_right) =
      normalized φ i p hp W (inf_le_right.trans inf_le_left) :=
    normalized_restrict φ i p hp inf_le_right h₁
  have h₂' : restrictRing (X := threefold φ) h₂
      (normalized φ j p hp (V ⊓ U φ j) inf_le_right) =
      normalized φ j p hp W (inf_le_right.trans inf_le_right) :=
    normalized_restrict φ j p hp inf_le_right h₂
  change restrictRing (X := threefold φ) h₁ (normalized φ i p hp (V ⊓ U φ i) inf_le_right) =
    ((cocycle φ n).unit i j W (inf_le_right.trans inf_le_left)
      (inf_le_right.trans inf_le_right) : Γ(threefold φ,W)) *
    restrictRing (X := threefold φ) h₂ (normalized φ j p hp (V ⊓ U φ j) inf_le_right)
  rw [h₁', h₂']
  simpa only [cocycle, zpow_natCast, Units.val_pow_eq_pow_val, transition] using
    normalized_change φ i j p hp (triple (U := U φ) V i j) (inf_le_right.trans inf_le_left)
      (inf_le_right.trans inf_le_right)

theorem homogeneousSection_coordinate {n : ℕ} (p : cone φ) (hp : p ∈ grade φ n)
    (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i) :
    chartFrame φ n i V hi (homogeneousSection φ p hp V) = normalized φ i p hp V hi := by
  change res (threefold φ).sheaf _ (component (cocycle φ n) i V (pack _ _ _ _)) = _
  rw [component_pack]
  exact normalized_restrict φ i p hp inf_le_right (le_inf le_rfl hi)

theorem homogeneousSection_restrict {n : ℕ} (p : cone φ) (hp : p ∈ grade φ n)
    {V W : (threefold φ).Opens} (h : W ≤ V) :
    CycleQ2SeedSectionSheafLocal.moduleRes (twist φ n) h (homogeneousSection φ p hp V) =
      homogeneousSection φ p hp W := by
  apply component_injective (cocycle φ n) W
  intro i
  change (projection _ i).app W (CycleQ2SeedSectionSheafLocal.moduleRes _ h _) = _
  rw [← CycleQ2SeedSectionSheafLocal.moduleRes_app]
  change res (threefold φ).sheaf (inf_le_inf_right _ h)
      (component (cocycle φ n) i V (pack _ _ _ _)) =
    component (cocycle φ n) i W (pack _ _ _ _)
  rw [component_pack, component_pack]
  exact normalized_restrict φ i p hp inf_le_right (inf_le_inf_right _ h)

end CycleQ2HodgeThreefoldTwist
end

#print axioms CycleQ2HodgeThreefoldTwist.chartFrame
#print axioms CycleQ2HodgeThreefoldTwist.homogeneousSection_coordinate
