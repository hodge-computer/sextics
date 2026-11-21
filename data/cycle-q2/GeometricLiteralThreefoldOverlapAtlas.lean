import Proposal.GeometricLiteralAmbientChartOverlap
import Proposal.GeometricLiteralAmbientChartTransition

/-! The localization used in the residue transition is the scheme-theoretic
intersection of two of the four fixed affine charts.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralThreefoldOverlapAtlas

open CategoryTheory AlgebraicGeometry
open CycleQ2SeedProjectiveFamily CycleQ2LiteralAmbientSmooth CycleQ2LiteralAmbientCharts
  CycleQ2LiteralAmbientChartOverlap CycleQ2LiteralAbelJacobiContraction
  CycleQ2LiteralThreefoldResidueCoordinates CycleQ2LiteralThreefoldResidueChartMaps

attribute [local instance] sourceFixedAlgebra

private theorem overlap_image (i : Fin 4) (k : Fin 3) :
    chartInclusion i ''ᵁ (chartInclusion i ⁻¹ᵁ fixedOpen (i.succAbove k)) =
      fixedOpen i ⊓ fixedOpen (i.succAbove k) := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
  change ((fixedChart i).hom ≫ (fixedOpen i).ι).opensRange ⊓ _ = _
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]

/-- The ordered localization is the actual intersection of the two opens on the threefold. -/
def overlapIso (i : Fin 4) (k : Fin 3) :
    Spec (CommRingCat.of (FixedOverlap i k)) ≅
      (fixedOpen i ⊓ fixedOpen (i.succAbove k)).toScheme :=
  (fixedOverlapChart i k).symm ≪≫
    (chartInclusion i).isoImage (chartInclusion i ⁻¹ᵁ fixedOpen (i.succAbove k)) ≪≫
    (IncidenceFiber 57).isoOfEq (overlap_image i k)

/-- Composing the overlap isomorphism with inclusion is induced by the
localization map in the source chart. -/
@[reassoc] theorem overlapIso_hom_ι (i : Fin 4) (k : Fin 3) :
    (overlapIso i k).hom ≫ (fixedOpen i ⊓ fixedOpen (i.succAbove k)).ι =
      Spec.map (CommRingCat.ofHom (algebraMap (T i) (FixedOverlap i k))) ≫ chartInclusion i := by
  simp only [overlapIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, Scheme.isoOfEq_hom_ι,
    Scheme.Hom.isoImage_hom_ι]
  rw [← fixedOverlapChart_hom_toChart_assoc i k]
  simp only [Iso.inv_hom_id_assoc]
  rfl

/-- The source restriction, with codomain in the chart itself. -/
@[reassoc] theorem overlapIso_source (i : Fin 4) (k : Fin 3) :
    (overlapIso i k).hom ≫
      (IncidenceFiber 57).homOfLE (U := fixedOpen i ⊓ fixedOpen (i.succAbove k))
        (V := fixedOpen i) inf_le_left =
      Spec.map (CommRingCat.ofHom (algebraMap (T i) (FixedOverlap i k))) ≫ (fixedChart i).hom := by
  apply (cancel_mono (fixedOpen i).ι).mp
  simpa only [Category.assoc, Scheme.homOfLE_ι, chartInclusion] using overlapIso_hom_ι i k

/-- On the target chart the same intersection is induced by the weighted
coordinate change in its full coordinate ring. -/
@[reassoc] theorem overlapIso_hom_ι_target (i : Fin 4) (k : Fin 3) :
    (overlapIso i k).hom ≫ (fixedOpen i ⊓ fixedOpen (i.succAbove k)).ι =
      Spec.map (CommRingCat.ofHom (fixedTargetMap i k).toRingHom) ≫ chartInclusion (i.succAbove k) :=
  (overlapIso_hom_ι i k).trans
    (CycleQ2LiteralAmbientChartTransition.fixedTargetMap_over_threefold i k).symm

/-- The target restriction, with codomain in the chart itself. -/
@[reassoc] theorem overlapIso_target (i : Fin 4) (k : Fin 3) :
    (overlapIso i k).hom ≫
      (IncidenceFiber 57).homOfLE (U := fixedOpen i ⊓ fixedOpen (i.succAbove k))
        (V := fixedOpen (i.succAbove k)) inf_le_right =
      Spec.map (CommRingCat.ofHom (fixedTargetMap i k).toRingHom) ≫
        (fixedChart (i.succAbove k)).hom := by
  apply (cancel_mono (fixedOpen (i.succAbove k)).ι).mp
  simpa only [Category.assoc, Scheme.homOfLE_ι, chartInclusion] using overlapIso_hom_ι_target i k

end CycleQ2LiteralThreefoldOverlapAtlas
end

#print axioms CycleQ2LiteralThreefoldOverlapAtlas.overlapIso_hom_ι
#print axioms CycleQ2LiteralThreefoldOverlapAtlas.overlapIso_source
#print axioms CycleQ2LiteralThreefoldOverlapAtlas.overlapIso_hom_ι_target
#print axioms CycleQ2LiteralThreefoldOverlapAtlas.overlapIso_target
