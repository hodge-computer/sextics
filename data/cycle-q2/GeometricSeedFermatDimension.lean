import Proposal.GeometricSeedFermatNormalizedChart
import Proposal.GeometricSeedFermatNormalizedDimension
import Proposal.GeometricSeedFermatGeometry

/-!
# Relative dimension three of the actual weighted projective seed

The normalized quotient is an algebra isomorph of the native homogeneous
localization, and its original structure morphism is smooth of relative
dimension three. Compatibility with the complex coefficient maps transfers
this property to each native Proj chart. The already proved four-chart
cover then gives the same relative dimension for the original projective
structure morphism.

The final existence statement retains the previously constructed explicit
point and properness. No geometric premise replaces a proof. Status:
source-only draft; no Lean elaboration, compilation, or kernel replay has
been run. The protected residue-exactness theorem remains open.
Prepared for `fqlx` with OpenAI ChatGPT assistance, following Ben Diamond's
geometric seed construction.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedFermatDimension

open CategoryTheory AlgebraicGeometry
open CycleQ2SeedFermatProj CycleQ2SeedFermatChartRetract
  CycleQ2SeedFermatProjSmooth CycleQ2SeedFermatNormalized
  CycleQ2SeedFermatNormalizedChart

/-- The literal normalized quotient computes relative dimension for the
native chart with its original complex coefficient map. -/
theorem chart_smoothOfRelativeDimension (r : ℂ) (hr : r ^ 3 = 2) (i : Fin 4) :
    SmoothOfRelativeDimension 3
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (ChartRing r i)))) := by
  let e := normalizedChartEquiv r i
  letI : IsIso (CommRingCat.ofHom e.toRingHom) :=
    e.toRingEquiv.toCommRingCatIso.isIso_hom
  let g : Spec (CommRingCat.of (ChartRing r i)) ⟶
      Spec (CommRingCat.of (NormalizedRing r i)) :=
    Spec.map (CommRingCat.ofHom e.toRingHom)
  have hmap :
      g ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (NormalizedRing r i))) =
        Spec.map (CommRingCat.ofHom (algebraMap ℂ (ChartRing r i))) := by
    dsimp only [g]
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    ext c
    exact e.commutes c
  rw [← hmap]
  exact (MorphismProperty.cancel_left_of_respectsIso
    (P := @SmoothOfRelativeDimension 3) g
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ (NormalizedRing r i))))).mpr
      (CycleQ2SeedFermatNormalizedDimension.normalizedRing_smoothOfRelativeDimension r hr i)

/-- Relative dimension three for the restriction of the original
projective structure morphism to each of its four native charts. -/
theorem coordinateOpen_smoothOfRelativeDimension
    (r : ℂ) (hr : r ^ 3 = 2) (i : Fin 4) :
    SmoothOfRelativeDimension 3
      ((coordinateOpen r i).ι ≫ threefoldToComplex r) := by
  apply (MorphismProperty.cancel_left_of_respectsIso
    (P := @SmoothOfRelativeDimension 3) (coordinateChart r i).inv
    ((coordinateOpen r i).ι ≫ threefoldToComplex r)).mp
  rw [coordinateChart_overComplex]
  exact chart_smoothOfRelativeDimension r hr i

/-- The actual zero-cubic weighted projective seed is smooth of relative
dimension three over the original complex field. -/
theorem threefold_smoothOfRelativeDimension (r : ℂ) (hr : r ^ 3 = 2) :
    SmoothOfRelativeDimension 3 (threefoldToComplex r) := by
  exact IsZariskiLocalAtSource.of_iSup_eq_top
    (P := @SmoothOfRelativeDimension 3) (fun i : Fin 4 => coordinateOpen r i)
    (coordinateOpens_cover r hr) (coordinateOpen_smoothOfRelativeDimension r hr)

/-- A nonempty smooth proper seed of relative dimension three exists,
with its root witness and all geometric properties constructed. -/
theorem exists_nonempty_smoothOfRelativeDimension_proper :
    ∃ r : ℂ, r ^ 3 = 2 ∧ Nonempty (threefold r) ∧
      SmoothOfRelativeDimension 3 (threefoldToComplex r) ∧
      IsProper (threefoldToComplex r) := by
  obtain ⟨r, hr, hnonempty, _, hproper⟩ :=
    CycleQ2SeedFermatGeometry.exists_nonempty_smooth_proper
  exact ⟨r, hr, hnonempty, threefold_smoothOfRelativeDimension r hr, hproper⟩

end CycleQ2SeedFermatDimension

end

#print axioms CycleQ2SeedFermatDimension.chart_smoothOfRelativeDimension
#print axioms CycleQ2SeedFermatDimension.threefold_smoothOfRelativeDimension
#print axioms CycleQ2SeedFermatDimension.exists_nonempty_smoothOfRelativeDimension_proper
