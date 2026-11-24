import Proposal.GeometricHodgeCotangentEulerDlog
import Proposal.GeometricHodgeGlobalConstants

/-!
# The zero-twist frame coefficient is the canonical scalar

The zero-twist frames glue, with the original restriction maps, to an
actual global function. Canonical constancy of that global function
therefore identifies every local frame coefficient with one and the
same scalar from the original structure morphism.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeZeroTwistScalars
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open CycleQ2GeometricHodgeThreefold
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2HodgeThreefoldTwist CycleQ2HodgeTwistRatios
open CycleQ2SeedSectionSheafLocal (moduleRes moduleRes_comp)
open CycleQ2GeometricProjectiveCurve.Twisted (res res_comp)
open CycleQ2HodgeCotangentEulerDlog (frame_restrict)
open CycleQ2GeometricAffineChartSections (schemeCoefficient)
open CycleQ2GeometricDifferentialSheaf (coefficientOn)
variable (φ : CoeffRing →+* ℂ)

def framed (s : Γ(twist φ 0,⊤)) (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i) :
    Γ(threefold φ,V) := chartFrame φ 0 i V hi (moduleRes (twist φ 0) le_top s)

theorem framed_restrict (s : Γ(twist φ 0,⊤)) (i : Fin 4) {V W : (threefold φ).Opens}
    (hi : V ≤ U φ i) (hW : W ≤ V) :
    res (threefold φ).sheaf hW (framed φ s i V hi) = framed φ s i W (hW.trans hi) := by
  unfold framed
  rw [← frame_restrict,moduleRes_comp]

theorem framed_change (s : Γ(twist φ 0,⊤)) (i k : Fin 4) (V : (threefold φ).Opens)
    (hi : V ≤ U φ i) (hk : V ≤ U φ k) : framed φ s i V hi = framed φ s k V hk := by
  have he := chartFrame_transition φ 0 i k V hi hk (moduleRes (twist φ 0) le_top s)
  simpa only [framed,zpow_zero,Units.val_one,one_mul] using he

private theorem exists_function (h : IsUnit (φ vertexCoefficient)) (s : Γ(twist φ 0,⊤)) :
    ∃ t : Γ(threefold φ,⊤), ∀ i : Fin 4,
      res (threefold φ).sheaf (show U φ i ≤ ⊤ from le_top) t = framed φ s i (U φ i) le_rfl := by
  let sf := fun i : Fin 4 => framed φ s i (U φ i) le_rfl
  have hc : TopCat.Presheaf.IsCompatible (threefold φ).sheaf.obj (U φ) sf := by
    intro i j
    change res (threefold φ).sheaf inf_le_left (sf i) = res (threefold φ).sheaf inf_le_right (sf j)
    rw [framed_restrict,framed_restrict]
    exact framed_change φ s i j _ _ _
  obtain ⟨t,ht,_⟩ := (threefold φ).sheaf.existsUnique_gluing' (U φ) ⊤
    (fun _ => homOfLE le_top) (coordinateOpens_cover φ h).ge sf hc
  exact ⟨t,ht⟩

def globalFunction (h : IsUnit (φ vertexCoefficient)) (s : Γ(twist φ 0,⊤)) : Γ(threefold φ,⊤) :=
  Classical.choose (exists_function φ h s)

theorem globalFunction_chart (h : IsUnit (φ vertexCoefficient)) (s : Γ(twist φ 0,⊤)) (i : Fin 4) :
    res (threefold φ).sheaf (show U φ i ≤ ⊤ from le_top) (globalFunction φ h s) = framed φ s i (U φ i) le_rfl :=
  Classical.choose_spec (exists_function φ h s) i

theorem globalFunction_on (h : IsUnit (φ vertexCoefficient)) (s : Γ(twist φ 0,⊤))
    (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i) :
    res (threefold φ).sheaf (show V ≤ ⊤ from le_top) (globalFunction φ h s) = framed φ s i V hi := by
  have he := congrArg (res (threefold φ).sheaf hi) (globalFunction_chart φ h s i)
  rwa [res_comp,framed_restrict] at he

/-- Every zero-twist coefficient uses the canonical structure-map scalar,
with all anchors and all their original subopen restrictions included. -/
theorem exists_canonical_scalar (h : IsUnit (φ vertexCoefficient)) (s : Γ(twist φ 0,⊤)) :
    ∃ c : ℂ, ∀ (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i),
      chartFrame φ 0 i V hi (moduleRes (twist φ 0) le_top s) =
        coefficientOn (threefold φ).sheaf (schemeCoefficient (toBase φ)) V c := by
  obtain ⟨c,hc⟩ := CycleQ2HodgeGlobalConstants.scalar_surjective φ h (globalFunction φ h s)
  refine ⟨c,fun i V hi => ?_⟩
  change framed φ s i V hi = _
  rw [← globalFunction_on φ h s i V hi,← hc]
  rfl

end CycleQ2HodgeZeroTwistScalars
end
#print axioms CycleQ2HodgeZeroTwistScalars.globalFunction_on
#print axioms CycleQ2HodgeZeroTwistScalars.exists_canonical_scalar
