import Proposal.GeometricLiteralThreefoldVolumeVariationPatch
import Proposal.GeometricLiteralThreefoldCartanLift

/-! The first-order coefficient of the canonical volume in an actual Jacobian frame.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldVolumeVariationEvaluation

open CycleQ2LiteralThreefoldKodairaSpencer CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldChartLift
  CycleQ2LiteralThreefoldResidueFrame CycleQ2LiteralThreefoldResidueMinors
  CycleQ2LiteralThreefoldVolumeVariation CycleQ2LiteralThreefoldVolumeVariationPatch
  CycleQ2LiteralThreefoldCartan CycleQ2LiteralThreefoldCartanLift
  CycleQ2LiteralThreefoldLiftDifference CycleQ2LiteralThreefoldLiftTransition
  CycleQ2LiteralThreefoldDeformedVolume

/-- The coefficient of the canonical lifted adjunction form on the actual
ordered coordinate frame, normalized by the coefficient of the fixed residue. -/
theorem canonical_volume_snd {i : Fin 4} {V : Index → P} {H : P}
    (hV : Represents i V) (hH : IsMultiplier i V H) (j : Fin 4)
    (h : IsUnit (patchMap i j (CycleQ2LiteralThreefoldResidueFrame.gradient i j))) :
    (evaluateJetVolume (basis i j) (CycleQ2LiteralThreefoldDeformedVolume.volume (canonical i (patchMap i j)) (patchMap i j)
      (canonical_liesOver i _))).snd =
      ordinaryCoefficient (i := i) (S := Patch i j) j h * patchMap i j (residueCoefficient i V H) := by
  have hdelta : (CycleQ2LiteralThreefoldDeformedVolume.gradient (canonical i (patchMap i j)) j).snd =
      patchMap i j ((gradientJet i (coordIndex j)).snd) := by
    have hm := CycleQ2LiteralThreefoldDeformedVolume.map_gradient (patchMap i j) (canonicalPoint i) j
    unfold canonicalPoint at hm
    rw [mapLift_canonical, AlgHom.comp_id] at hm
    exact congrArg TrivSqZeroExt.snd hm.symm
  have E := evaluate_deformed_volume_snd (i := i) (S := Patch i j) j h (basis i j) (basis_apply i j)
    (canonical i (patchMap i j)) (canonical_liesOver i _)
  rw [E, hdelta]
  change ordinaryCoefficient (i := i) (S := Patch i j) j h * (∑ r, patchPartial i j r _) + _ = _
  rw [canonical_trace hV hH j h]
  unfold ordinaryCoefficient
  ring

/-- On every Jacobian pivot the coefficient recovered from the deformed relative
volume is the restriction of the chart-wide scalar times the original residue form. -/
theorem canonical_volume_form {i : Fin 4} {V : Index → P} {H : P}
    (hV : Represents i V) (hH : IsMultiplier i V H) (j : Fin 4) :
    (evaluateJetVolume (basis i j) (CycleQ2LiteralThreefoldDeformedVolume.volume
      (canonical i (patchMap i j)) (patchMap i j) (canonical_liesOver i _))).snd •
      orderedVolume (basis i j) =
    patchMap i j (residueCoefficient i V H) •
      CycleQ2ExteriorSectionNaturality.exteriorDifferentialMap (patchMap i j) 3
        (CycleQ2LiteralThreefoldChartVolume.chartVolume i) := by
  have h : IsUnit (patchMap i j (CycleQ2LiteralThreefoldResidueFrame.gradient i j)) :=
    IsLocalization.Away.algebraMap_isUnit (S := Patch i j) _
  rw [canonical_volume_snd hV hH j h, fixedVolume_eq (i := i) (S := Patch i j) j h (basis i j) (basis_apply i j),
    smul_smul, mul_comm]

/-- The chart coefficient singled out by the canonical lift, independent of every
choice of polynomial velocity representatives. -/
def chartCoefficient (i : Fin 4) : T i :=
  (existsUnique_residueCoefficient i).exists.choose

theorem chartCoefficient_spec {i : Fin 4} (V : Index → P) (H : P)
    (hV : Represents i V) (hH : IsMultiplier i V H) :
    residueCoefficient i V H = chartCoefficient i :=
  (existsUnique_residueCoefficient i).exists.choose_spec V H hV hH

set_option maxHeartbeats 1200000 in
/-- Normalized first-order variation on an arbitrary Jacobian pivot, without
polynomial representatives or gradient-unit hypotheses in the statement. -/
theorem canonical_chart_variation (i j : Fin 4) :
    (evaluateJetVolume (basis i j) (CycleQ2LiteralThreefoldDeformedVolume.volume
      (canonical i (patchMap i j)) (patchMap i j) (canonical_liesOver i _))).snd •
      orderedVolume (basis i j) =
    patchMap i j (chartCoefficient i) •
      CycleQ2ExteriorSectionNaturality.exteriorDifferentialMap (patchMap i j) 3
        (CycleQ2LiteralThreefoldChartVolume.chartVolume i) := by
  obtain ⟨V, hV⟩ := exists_representatives i
  obtain ⟨H, hH⟩ := exists_multiplier hV
  exact (canonical_volume_form hV hH j).trans (congrArg
    (fun c : T i => patchMap i j c •
      CycleQ2ExteriorSectionNaturality.exteriorDifferentialMap (patchMap i j) 3
        (CycleQ2LiteralThreefoldChartVolume.chartVolume i))
    (chartCoefficient_spec V H hV hH))

end CycleQ2LiteralThreefoldVolumeVariationEvaluation
end
