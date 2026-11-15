import Proposal.GeometricFirstOrderCurve
import Proposal.GeometricFirstOrderChartFlatness
import Proposal.GeometricRelativeCurveChartScheme

/-!
# Actual affine charts covering the first-order curve

The original coordinate charts are pulled back along the original
dual-number parameter map. Their coordinate rings are exactly the
first-order tensor quotients already used in the equation calculations.
The resulting open immersions commute with both the original curve map
and the dual-number structure map.

These four opens cover the whole actual first-order curve: every point
maps to the retained literal incidence seed, where the weight-one cover
has already been proved for all prime points. Flatness on the displayed
tensor algebras therefore implies flatness of this actual curve morphism.
Supplying that algebraic flatness is a separate local equation obligation.

Source-only draft: no elaboration, compilation, or kernel replay was run.
Prepared for `fqlx` with OpenAI ChatGPT assistance, following Ben Diamond
and the geometric strategy credited in solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2FirstOrderCurveCharts

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open CycleQ2IncidenceEtaleParameter CycleQ2IncidenceFirstOrder
  CycleQ2IncidenceSeedFiberCover CycleQ2FirstOrderNeighborhood
  CycleQ2GeometricIncidenceProj CycleQ2RelativeConstantCurve
  CycleQ2RelativeCurveChart CycleQ2RelativeCurveChartScheme
  CycleQ2FirstOrderChartReduction CycleQ2FirstOrderChartFlatness
  CycleQ2FirstOrderCurve

attribute [local instance] firstOrderAlgebra

variable (t : Fin 3 → ℂ) (i : Fin 4)

/-- The original affine coordinate chart followed by its actual open inclusion. -/
def originalCurveChart :
    Spec (CommRingCat.of (AffineCurveChart incidencePoint t i)) ⟶
      relativeCurve incidencePoint t :=
  (curveCoordinateAffineChart incidencePoint t i).inv ≫
    (curveCoordinatePatch incidencePoint t i).ι

instance originalCurveChart_isOpenImmersion :
    IsOpenImmersion (originalCurveChart t i) := by
  dsimp only [originalCurveChart]
  infer_instance

theorem originalCurveChart_overBase :
    originalCurveChart t i ≫ relativeCurveToBase incidencePoint t =
      Spec.map (CommRingCat.ofHom
        (algebraMap ParameterAlgebra (AffineCurveChart incidencePoint t i))) := by
  exact (Category.assoc _ _ _).trans
    (curveCoordinateAffineChart_overBase incidencePoint t i)

theorem originalCurveChart_opensRange :
    (originalCurveChart t i).opensRange = curveCoordinatePatch incidencePoint t i := by
  rw [originalCurveChart, Scheme.Hom.opensRange_comp_of_isIso]
  exact (curveCoordinatePatch incidencePoint t i).opensRange_ι

/-- The exact tensor chart of the original curve maps into its actual base change. -/
def firstOrderChartToCurve :
    Spec (CommRingCat.of (FirstOrderCurveChart t i)) ⟶ firstOrderCurve t :=
  tensorChartToSource (AffineCurveChart incidencePoint t i)
    (relativeCurveToBase incidencePoint t) (firstOrderCurveToOriginalCurve t)
    (firstOrderCurveToBase t) (firstOrderCurve_isPullback t)
    (originalCurveChart t i) (originalCurveChart_overBase t i)

instance firstOrderChartToCurve_isOpenImmersion :
    IsOpenImmersion (firstOrderChartToCurve t i) := by
  dsimp only [firstOrderChartToCurve]
  infer_instance

@[reassoc] theorem firstOrderChartToCurve_overBase :
    firstOrderChartToCurve t i ≫ firstOrderCurveToBase t =
      Spec.map (CommRingCat.ofHom
        (algebraMap (DualNumber ℂ) (FirstOrderCurveChart t i))) :=
  tensorChartToSource_overBase (AffineCurveChart incidencePoint t i)
    (relativeCurveToBase incidencePoint t) (firstOrderCurveToOriginalCurve t)
    (firstOrderCurveToBase t) (firstOrderCurve_isPullback t)
    (originalCurveChart t i) (originalCurveChart_overBase t i)

@[reassoc] theorem firstOrderChartToCurve_original :
    firstOrderChartToCurve t i ≫ firstOrderCurveToOriginalCurve t =
      tensorChartToOriginal (AffineCurveChart incidencePoint t i) ≫
        originalCurveChart t i :=
  tensorChartToSource_original (AffineCurveChart incidencePoint t i)
    (relativeCurveToBase incidencePoint t) (firstOrderCurveToOriginalCurve t)
    (firstOrderCurveToBase t) (firstOrderCurve_isPullback t)
    (originalCurveChart t i) (originalCurveChart_overBase t i)

theorem firstOrderChartToCurve_opensRange :
    (firstOrderChartToCurve t i).opensRange =
      firstOrderCurveToOriginalCurve t ⁻¹ᵁ curveCoordinatePatch incidencePoint t i := by
  rw [firstOrderChartToCurve, tensorChartToSource_opensRange,
    originalCurveChart_opensRange]

def firstOrderCurveCoordinateOpen : (firstOrderCurve t).Opens :=
  (firstOrderChartToCurve t i).opensRange

/-- All first-order points lie above the original seed, so the four actual
weight-one coordinate charts cover the whole curve base change. -/
theorem iSup_firstOrderCurveCoordinateOpen :
    (⨆ i : Fin 4, firstOrderCurveCoordinateOpen t i) = ⊤ := by
  apply top_unique
  intro z _
  let x : surface incidencePoint :=
    relativeCurveToSurface incidencePoint t (firstOrderCurveToOriginalCurve t z)
  have hx : surfaceToBase incidencePoint x = seedBasePoint := by
    have h := congrArg (fun f : firstOrderCurve t ⟶
        Spec (CommRingCat.of ParameterAlgebra) => f z)
      (firstOrderCurveToOriginalCurve_overBase t)
    change surfaceToBase incidencePoint x =
      firstOrderParameterPoint (firstOrderCurveToBase t z) at h
    exact h.trans (firstOrderParameterPoint_apply (firstOrderCurveToBase t z))
  obtain ⟨j, hj⟩ := exists_weightOne_of_over_seed x hx
  apply Opens.mem_iSup.mpr
  refine ⟨j, ?_⟩
  change z ∈ (firstOrderChartToCurve t j).opensRange
  rw [firstOrderChartToCurve_opensRange]
  change firstOrderCurveToOriginalCurve t z ∈ curveCoordinatePatch incidencePoint t j
  rw [curveCoordinatePatch_eq_preimage]
  exact hj

/-- Algebraic flatness on the actual tensor charts descends to the same
proper first-order curve morphism by the proved open covering. -/
theorem firstOrderCurveToBase_flat_of_affineCharts
    (hflat : ∀ i : Fin 4, Module.Flat (DualNumber ℂ) (FirstOrderCurveChart t i)) :
    AlgebraicGeometry.Flat (firstOrderCurveToBase t) := by
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @AlgebraicGeometry.Flat)
    (firstOrderCurveCoordinateOpen t) (iSup_firstOrderCurveCoordinateOpen t)
  intro j
  let f := firstOrderChartToCurve t j
  have hr : Set.range f = Set.range f.opensRange.ι :=
    congrArg Opens.carrier f.opensRange.opensRange_ι.symm
  let e := IsOpenImmersion.isoOfRangeEq f f.opensRange.ι hr
  apply (MorphismProperty.cancel_left_of_respectsIso
    (P := @AlgebraicGeometry.Flat) e.hom
    ((firstOrderCurveCoordinateOpen t j).ι ≫ firstOrderCurveToBase t)).mp
  have he : e.hom ≫ f.opensRange.ι = f :=
    IsOpenImmersion.isoOfRangeEq_hom_fac f f.opensRange.ι hr
  change AlgebraicGeometry.Flat (e.hom ≫ f.opensRange.ι ≫ firstOrderCurveToBase t)
  rw [← Category.assoc, he]
  change AlgebraicGeometry.Flat (firstOrderChartToCurve t j ≫ firstOrderCurveToBase t)
  rw [firstOrderChartToCurve_overBase]
  apply (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Flat)).mpr
  exact RingHom.flat_algebraMap_iff.mpr (hflat j)

end CycleQ2FirstOrderCurveCharts

end

#print axioms CycleQ2FirstOrderCurveCharts.firstOrderChartToCurve_overBase
#print axioms CycleQ2FirstOrderCurveCharts.firstOrderChartToCurve_original
#print axioms CycleQ2FirstOrderCurveCharts.iSup_firstOrderCurveCoordinateOpen
#print axioms CycleQ2FirstOrderCurveCharts.firstOrderCurveToBase_flat_of_affineCharts
