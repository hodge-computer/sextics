import Proposal.GeometricLiteralAmbientCharts
import Proposal.GeometricLiteralThreefoldChartVolume

/-! The smooth gradient opens in the four fixed charts form an affine cover
of the original threefold. Their coordinate rings and localization morphisms
are the ones used to construct the residue frames.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralThreefoldGradientAtlas

open CategoryTheory AlgebraicGeometry
open CycleQ2LiteralAmbientSmooth CycleQ2LiteralAmbientCharts CycleQ2LiteralAbelJacobiContraction
  CycleQ2LiteralThreefoldResidueFrame CycleQ2LiteralThreefoldChartVolume

/-- The image of a principal gradient open in the literal threefold. -/
abbrev gOpen (i j : Fin 4) : (IncidenceFiber 57).Opens :=
  chartInclusion i ''ᵁ PrimeSpectrum.basicOpen (gradient i j)

/-- The affine model of the gradient open on which the residue is a frame. -/
def gradientIso (i j : Fin 4) :
    (gOpen i j).toScheme ≅ Spec (CommRingCat.of (Patch i j)) :=
  ((chartInclusion i).isoImage (PrimeSpectrum.basicOpen (gradient i j))).symm ≪≫
    basicOpenIsoSpecAway (R := CommRingCat.of (T i)) (gradient i j)

private theorem gradientIso_hom_toChart (i j : Fin 4) :
    (gradientIso i j).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap (T i) (Patch i j))) ≫
        chartInclusion i = (gOpen i j).ι := by
  let f := chartInclusion i
  let U := PrimeSpectrum.basicOpen (gradient i j)
  have h := basicOpenIsoSpecAway_hom_SpecMap_assoc (R := CommRingCat.of (T i)) (gradient i j) f
  simp only [gradientIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  exact (congrArg (fun m => (f.isoImage U).inv ≫ m) h).trans (f.isoImage_inv_ι U)

@[reassoc] theorem gradientIso_inv_ι (i j : Fin 4) :
    (gradientIso i j).inv ≫ (gOpen i j).ι =
      Spec.map (CommRingCat.ofHom (algebraMap (T i) (Patch i j))) ≫ chartInclusion i := by
  rw [← gradientIso_hom_toChart i j, Iso.inv_hom_id_assoc]

/-- The four partial derivatives cover the chart because they generate the unit ideal. -/
theorem iSup_gOpen (i : Fin 4) : (⨆ j, gOpen i j) = fixedOpen i := by
  have hc : (⨆ j, PrimeSpectrum.basicOpen (gradient i j)) = ⊤ := by
    apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr
    apply (Ideal.eq_top_iff_one _).mpr
    exact Ideal.mem_span_range_iff_exists_fun.mpr (chartBezout i)
  change (⨆ j, chartInclusion i ''ᵁ PrimeSpectrum.basicOpen (gradient i j)) = _
  rw [← Scheme.Hom.image_iSup, hc, Scheme.Hom.image_top_eq_opensRange]
  exact (Scheme.Hom.opensRange_comp_of_isIso (fixedChart i).hom (fixedOpen i).ι).trans
    (Scheme.Opens.opensRange_ι _)

theorem gOpen_le (i j : Fin 4) : gOpen i j ≤ fixedOpen i :=
  (le_iSup (gOpen i) j).trans (iSup_gOpen i).le

/-- The sixteen gradient opens cover the entire fixed threefold. -/
theorem gOpen_cover : (⨆ i, ⨆ j, gOpen i j) = ⊤ := by
  simpa only [iSup_gOpen] using fixedOpen_cover

end CycleQ2LiteralThreefoldGradientAtlas
end

#print axioms CycleQ2LiteralThreefoldGradientAtlas.gradientIso_inv_ι
#print axioms CycleQ2LiteralThreefoldGradientAtlas.gOpen_cover
