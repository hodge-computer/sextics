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

/-! The actual test deformation also has a distinguished lift on each
gradient patch: move only the omitted coordinate. Its volume coefficient is
the first normal residue of the same polynomial `test i`. Comparing this
lift with the canonical lift supplies an explicit exterior boundary, rather
than an assumed comparison between the Hodge cocycle and a pole symbol. -/

open MvPolynomial CycleQ2LiteralAbelJacobiEquations

private theorem normalUnit (i j : Fin 4) :
    IsUnit (patchMap i j (CycleQ2LiteralThreefoldResidueFrame.gradient i j)) :=
  IsLocalization.Away.algebraMap_isUnit (S := Patch i j) _

/-- The inverse of the actual omitted-coordinate partial derivative. -/
def normalInverse (i j : Fin 4) : Patch i j :=
  (↑(normalUnit i j).unit⁻¹ : Patch i j)

private theorem normalInverse_mul (i j : Fin 4) :
    normalInverse i j * eval i j (pderiv (coordIndex j) (seedF i)) = 1 :=
  (normalUnit i j).val_inv_mul

private def normalTaylor (i j : Fin 4) : P →ₐ[ℂ] Jet (Patch i j) where
  toFun p := ⟨eval i j p, normalInverse i j * eval i j (test i) *
    eval i j (pderiv (coordIndex j) p)⟩
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp [Derivation.map_one_eq_zero]
  map_add' p r := by
    apply TrivSqZeroExt.ext
    · exact map_add (eval i j) p r
    · change normalInverse i j * eval i j (test i) * eval i j (pderiv (coordIndex j) (p+r)) = _
      rw [map_add, map_add, mul_add]
  map_mul' p r := by
    apply TrivSqZeroExt.ext
    · exact map_mul (eval i j) p r
    · change normalInverse i j * eval i j (test i) * eval i j (pderiv (coordIndex j) (p*r)) =
        eval i j p * (normalInverse i j * eval i j (test i) * eval i j (pderiv (coordIndex j) r)) +
        (normalInverse i j * eval i j (test i) * eval i j (pderiv (coordIndex j) p)) * eval i j r
      rw [pderiv_mul, map_add, map_mul, map_mul]
      ring
  commutes' c := by
    apply TrivSqZeroExt.ext
    · exact (eval i j).commutes c
    · change normalInverse i j * eval i j (test i) * eval i j (pderiv (coordIndex j) (C c)) = 0
      rw [pderiv_C, map_zero, mul_zero]

private theorem aeval_normalTaylor (i j : Fin 4) :
    aeval (fun a => normalTaylor i j (X a)) = normalTaylor i j := by
  apply MvPolynomial.algHom_ext
  intro a
  rw [aeval_X]

/-- A lift of `F - ε A₀` moving only the omitted coordinate, with all three
retained coordinates fixed. The numerator is the existing marked test. -/
def normalLift (i j : Fin 4) : Lift i (Patch i j) where
  x a := normalTaylor i j (X a)
  equation := by
    simp only [aeval_normalTaylor]
    apply TrivSqZeroExt.ext
    · change eval i j (seedF i) = 0 * eval i j (test i)
      rw [zero_mul]
      change patchMap i j (q i (seedF i)) = 0
      rw [show q i (seedF i) = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_singleton _)), map_zero]
    · change normalInverse i j * eval i j (test i) * eval i j (pderiv (coordIndex j) (seedF i)) =
        0 * _ + 1 * eval i j (test i)
      rw [zero_mul, one_mul, zero_add, mul_right_comm, normalInverse_mul, one_mul]

theorem normalLift_liesOver (i j : Fin 4) : LiesOver (normalLift i j) (patchMap i j) :=
  fun _ => rfl

private theorem normalLift_free (i j : Fin 4) (r : Fin 3) :
    ((normalLift i j).x (coordIndex (j.succAbove r))).snd = 0 := by
  change normalInverse i j * eval i j (test i) *
    eval i j (pderiv (coordIndex j) (X (coordIndex (j.succAbove r)))) = 0
  rw [pderiv_X_of_ne (fun h => Fin.succAbove_ne j r (coordIndex.injective h)), map_zero, mul_zero]

private theorem normalLift_gradient (i j : Fin 4) :
    (CycleQ2LiteralThreefoldDeformedVolume.gradient (normalLift i j) j).snd =
      normalInverse i j * eval i j (test i) *
        eval i j (pderiv (coordIndex j) (pderiv (coordIndex j) (seedF i))) -
      eval i j (pderiv (coordIndex j) (test i)) := by
  rw [CycleQ2LiteralThreefoldDeformedVolume.gradient]
  change ((aeval (fun a => normalTaylor i j (X a)) (pderiv (coordIndex j) (seedF i))) -
    (TrivSqZeroExt.inr 1 : Jet (Patch i j)) *
      aeval (fun a => normalTaylor i j (X a)) (pderiv (coordIndex j) (test i))).snd = _
  simp only [aeval_normalTaylor]
  change _ - (0 * _ + 1 * _) = _
  rw [zero_mul, one_mul, zero_add]

/-- The first normal residue of the actual marked numerator, with the
omitted-coordinate sign. Pole index one has factorial normalization `1! = 1`. -/
def normalPoleCoefficient (i j : Fin 4) : Patch i j :=
  (-1 : Patch i j)^j.val *
    ((normalInverse i j)^2 * eval i j (pderiv (coordIndex j) (test i)) -
      (normalInverse i j)^3 * eval i j (test i) *
        eval i j (pderiv (coordIndex j) (pderiv (coordIndex j) (seedF i))))

theorem normalLift_volume_snd (i j : Fin 4) :
    (evaluateJetVolume (basis i j) (CycleQ2LiteralThreefoldDeformedVolume.volume
      (normalLift i j) (patchMap i j) (normalLift_liesOver i j))).snd =
        normalPoleCoefficient i j := by
  have h := evaluate_deformed_volume_snd (i := i) (S := Patch i j) j (normalUnit i j)
    (basis i j) (basis_apply i j) (normalLift i j) (normalLift_liesOver i j)
  simp only [normalLift_free, map_zero, Finset.sum_const_zero, mul_zero, zero_add,
    normalLift_gradient] at h
  rw [h]
  unfold normalPoleCoefficient normalInverse
  ring

/-- The concrete two-form comparing the canonical and normal lifts of the
same test deformation. -/
def normalPrimitive (i j : Fin 4) : CycleQ2LiteralThreefoldCartan.Forms (Patch i j) 2 :=
  CycleQ2LiteralThreefoldResidueContraction.interior 2
    (localizedTangent (Submonoid.powers (CycleQ2LiteralThreefoldResidueFrame.gradient i j))
      (canonical i (patchMap i j)) (normalLift i j)
      (canonical_liesOver i _) (normalLift_liesOver i j)).liftKaehlerDifferential
    (CycleQ2ExteriorSectionNaturality.exteriorDifferentialMap (patchMap i j) 3
      (CycleQ2LiteralThreefoldChartVolume.chartVolume i))

/-- The regular vertex form used in the actual test Čech cocycle differs
from the first normal pole residue by the displayed exterior boundary. -/
theorem canonical_normal_difference (i j : Fin 4) :
    patchMap i j (chartCoefficient i) •
        CycleQ2ExteriorSectionNaturality.exteriorDifferentialMap (patchMap i j) 3
          (CycleQ2LiteralThreefoldChartVolume.chartVolume i) -
      normalPoleCoefficient i j • orderedVolume (basis i j) =
        exteriorD2 (basis i j) (normalPrimitive i j) := by
  have h := patch_actual_volume_difference i j (canonical i (patchMap i j))
    (normalLift i j) (canonical_liesOver i _) (normalLift_liesOver i j)
  simpa only [sub_smul, canonical_chart_variation, normalLift_volume_snd,
    normalPrimitive] using h

end CycleQ2LiteralThreefoldVolumeVariationEvaluation
end

#print axioms CycleQ2LiteralThreefoldVolumeVariationEvaluation.normalLift_volume_snd
#print axioms CycleQ2LiteralThreefoldVolumeVariationEvaluation.canonical_normal_difference
