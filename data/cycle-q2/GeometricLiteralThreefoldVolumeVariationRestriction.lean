import Proposal.GeometricLiteralThreefoldVolumeVariationEvaluation
import Proposal.GeometricLiteralThreefoldDeformedFrame

/-! Restriction of the canonical lift's first variation to a further exact chart.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldVolumeVariationRestriction

open Module CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldChartLift
  CycleQ2LiteralThreefoldResidueFrame CycleQ2LiteralThreefoldResidueMinors
  CycleQ2LiteralThreefoldLiftDifference CycleQ2LiteralThreefoldLiftTransition
  CycleQ2LiteralThreefoldDeformedVolume CycleQ2LiteralThreefoldDeformedFrame
  CycleQ2LiteralThreefoldCartan CycleQ2LiteralThreefoldVolumeVariationPatch
  CycleQ2LiteralThreefoldVolumeVariationEvaluation CycleQ2ExteriorSectionNaturality
  CycleQ2GeometricAffineOverlap CycleQ2GeometricExteriorSheaf

private theorem exterior_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C] (f : A →ₐ[ℂ] B) (g : B →ₐ[ℂ] C)
    (w : CycleQ2LiteralThreefoldCartan.Forms A 3) :
    exteriorDifferentialMap g 3 (exteriorDifferentialMap f 3 w) =
      exteriorDifferentialMap (g.comp f) 3 w :=
  (exteriorMap_composition f.toRingHom g.toRingHom (g.comp f).toRingHom
    (differentialSemilinearMap f) (differentialSemilinearMap g)
    (differentialSemilinearMap (g.comp f)) (fun _ => rfl)
    (fun z => (differentialMap_comp f g z).symm) 3 w).symm

/-- The pulled-back residue coefficient gives the first variation in every
further exact differential frame. The map can in particular be any localization
of the pivot chart. -/
theorem canonical_variation_restrict {S : Type} [CommRing S] [Algebra ℂ S]
    (i j : Fin 4) (g : Patch i j →ₐ[ℂ] S)
    (b : Basis (Fin 3) S (OneForms S)) (u : Fin 3 → S)
    (hu : ∀ k, b k = KaehlerDifferential.D ℂ S (u k)) :
    firstVariation b (volume (canonical i (g.comp (patchMap i j))) (g.comp (patchMap i j))
      (canonical_liesOver i _)) =
    (g.comp (patchMap i j)) (chartCoefficient i) •
      exteriorDifferentialMap (g.comp (patchMap i j)) 3
        (CycleQ2LiteralThreefoldChartVolume.chartVolume i) := by
  let w := volume (canonical i (patchMap i j)) (patchMap i j) (canonical_liesOver i _)
  have hw : mapForms g 3 w =
      volume (canonical i (g.comp (patchMap i j))) (g.comp (patchMap i j))
        (canonical_liesOver i _) := by
    simpa only [mapLift_canonical] using
      map_volume g (canonical i (patchMap i j)) (patchMap i j) (canonical_liesOver i _)
  have hc : firstVariation (basis i j) w = _ := canonical_chart_variation i j
  rw [← hw, firstVariation_map (basis i j) _ (basis_apply i j) g b u hu, hc,
    map_smulₛₗ, exterior_comp]
  rfl

/-- Equivalently one may start with a map from the full chart on which a
chosen partial is a unit. Its factorization through the pivot chart is canonical. -/
theorem canonical_variation_of_unit {S : Type} [CommRing S] [Algebra ℂ S]
    (i j : Fin 4) (f : T i →ₐ[ℂ] S)
    (h : IsUnit (f (CycleQ2LiteralThreefoldResidueFrame.gradient i j)))
    (b : Basis (Fin 3) S (OneForms S)) (u : Fin 3 → S)
    (hu : ∀ k, b k = KaehlerDifferential.D ℂ S (u k)) :
    firstVariation b (volume (canonical i f) f (canonical_liesOver i _)) =
    f (chartCoefficient i) • exteriorDifferentialMap f 3
      (CycleQ2LiteralThreefoldChartVolume.chartVolume i) := by
  let g : Patch i j →ₐ[ℂ] S :=
    IsLocalization.Away.liftAlgHom (CycleQ2LiteralThreefoldResidueFrame.gradient i j) (f := f) h
  have hg : g.comp (patchMap i j) = f := by
    apply AlgHom.ext
    intro a
    exact IsLocalization.Away.lift_eq _ (g := f.toRingHom) h a
  let Q (a : T i →ₐ[ℂ] S) : Prop :=
    firstVariation b (volume (canonical i a) a (canonical_liesOver i _)) =
      a (chartCoefficient i) • exteriorDifferentialMap a 3
        (CycleQ2LiteralThreefoldChartVolume.chartVolume i)
  have hQ : Q (g.comp (patchMap i j)) := canonical_variation_restrict i j g b u hu
  exact Eq.mp (congrArg Q hg) hQ

end CycleQ2LiteralThreefoldVolumeVariationRestriction
end

#print axioms CycleQ2LiteralThreefoldVolumeVariationEvaluation.canonical_chart_variation
#print axioms CycleQ2LiteralThreefoldVolumeVariationRestriction.canonical_variation_restrict
#print axioms CycleQ2LiteralThreefoldVolumeVariationRestriction.canonical_variation_of_unit
