import Proposal.GeometricLiteralProjectiveComplexSplittings

/-!
# The twelve original affine charts cover the actual deformation

Every relevant homogeneous prime of the original graded deformation
contains its actual square-zero epsilon ideal. It therefore descends
through the proved graded reduction to a relevant homogeneous prime of
the original surface. This proves surjectivity of the actual closed-fibre
map on points. Pulling back the existing twelve-open cover then proves
that the twelve genuine deformed charts cover the whole projectivization.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralProjectiveDeformationCover

open TopologicalSpace CategoryTheory AlgebraicGeometry CycleQ2CartierSurfaceGrading
  CycleQ2LiteralGradedDeformation CycleQ2LiteralGradedReduction
  CycleQ2LiteralProjectiveDeformation CycleQ2ProjectiveCartierIdeal
  CycleQ2LiteralProjectiveComplexSplittings

/-- This uses the original epsilon square, hence the original reduction
kernel, rather than an assumed nilpotence statement about a new ideal. -/
theorem reduction_kernel_le_prime (x : ProjectiveSpectrum deformationGrade) :
    RingHom.ker reduction.toRingHom ≤ x.asHomogeneousIdeal.toIdeal := by
  rw [reduction_kernel_principal]
  apply Ideal.span_le.mpr
  rintro z (rfl : z = epsilonElement)
  apply x.isPrime.mem_of_pow_mem 2
  rw [pow_two, epsilonElement_square]
  exact x.asHomogeneousIdeal.toIdeal.zero_mem

theorem mappedPrime_comap (x : ProjectiveSpectrum deformationGrade) :
    (x.asHomogeneousIdeal.map reductionGraded).comap reductionGraded = x.asHomogeneousIdeal := by
  apply HomogeneousIdeal.toIdeal_injective
  change (x.asHomogeneousIdeal.toIdeal.map reduction.toRingHom).comap reduction.toRingHom = _
  rw [Ideal.comap_map_of_surjective reduction.toRingHom reduction_surjective]
  exact sup_eq_left.mpr (reduction_kernel_le_prime x)

/-- A genuine point of the original closed surface, obtained by mapping
the actual homogeneous prime through the actual graded reduction. -/
def reducedPoint (x : ProjectiveSpectrum deformationGrade) : ProjectiveSpectrum (surfaceGrade 57 1) where
  asHomogeneousIdeal := x.asHomogeneousIdeal.map reductionGraded
  isPrime := Ideal.map_isPrime_of_surjective reduction_surjective (reduction_kernel_le_prime x)
  not_irrelevant_le h := by
    apply x.not_irrelevant_le
    change (HomogeneousIdeal.irrelevant deformationGrade).toIdeal ≤ x.asHomogeneousIdeal.toIdeal
    apply (HomogeneousIdeal.toIdeal_irrelevant_le deformationGrade).mpr
    intro n hn z hz
    have hm : reductionGraded z ∈ HomogeneousIdeal.irrelevant (surfaceGrade 57 1) :=
      HomogeneousIdeal.mem_irrelevant_of_mem (surfaceGrade 57 1) hn (reductionGraded.2 hz)
    have hx : z ∈ (x.asHomogeneousIdeal.map reductionGraded).comap reductionGraded := h hm
    rwa [mappedPrime_comap] at hx

theorem closedFiber_reducedPoint (x : ProjectiveSpectrum deformationGrade) :
    closedFiber (reducedPoint x) = x := by
  apply ProjectiveSpectrum.ext
  exact mappedPrime_comap x

theorem closedFiber_surjective : Function.Surjective closedFiber :=
  fun x => ⟨reducedPoint x, closedFiber_reducedPoint x⟩

/-- The actual native deformation charts used for the splittings form
an atlas over the entire original square-zero projectivization. -/
theorem deformation_chartOpen_cover :
    (⨆ a : Fin 4, ⨆ l : Fin 3, chartOpen a l) = ⊤ := by
  apply top_le_iff.mp
  intro x _
  obtain ⟨y,rfl⟩ := closedFiber_surjective x
  have hy : y ∈ (⨆ a : Fin 4, ⨆ l : Fin 3, refinedOpen 57 1 a l) := by
    rw [literal_refinedOpen_cover]
    trivial
  obtain ⟨a,ha⟩ := Opens.mem_iSup.mp hy
  obtain ⟨l,hl⟩ := Opens.mem_iSup.mp ha
  apply Opens.mem_iSup.mpr
  refine ⟨a, Opens.mem_iSup.mpr ⟨l, ?_⟩⟩
  change y ∈ closedFiber ⁻¹ᵁ chartOpen a l
  rw [closedFiber_preimage_chartOpen]
  exact hl

set_option maxHeartbeats 600000 in
/-- The global closed-fibre map respects the original complex structure
morphisms, as witnessed on the actual twelve affine charts. -/
theorem closedFiber_overComplex :
    closedFiber ≫ deformationToComplex =
      CycleQ2GeometricSurfaceCoefficients.projectiveToComplex 57 1 := by
  have hc : IsOpenCover (fun i : Fin 4 × Fin 3 => refinedOpen 57 1 i.1 i.2) :=
    .mk (by simpa only [iSup_prod] using literal_refinedOpen_cover)
  refine Scheme.Cover.hom_ext ((CycleQ2CartierProjectiveCover.projectiveSurface 57 1).openCoverOfIsOpenCover
    (fun i : Fin 4 × Fin 3 => refinedOpen 57 1 i.1 i.2) hc)
    (closedFiber ≫ deformationToComplex) (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex 57 1) ?_
  intro i
  apply (cancel_epi (Proj.basicOpenIsoSpec (surfaceGrade 57 1)
    (refinedDenominator 57 1 i.1 i.2) (refinedDenominator_homogeneous 57 1 i.1 i.2)
    (by omega)).inv).mp
  change Proj.awayι (surfaceGrade 57 1) (refinedDenominator 57 1 i.1 i.2)
      (refinedDenominator_homogeneous 57 1 i.1 i.2) (by omega) ≫
        closedFiber ≫ deformationToComplex =
    Proj.awayι (surfaceGrade 57 1) (refinedDenominator 57 1 i.1 i.2)
      (refinedDenominator_homogeneous 57 1 i.1 i.2) (by omega) ≫
        CycleQ2GeometricSurfaceCoefficients.projectiveToComplex 57 1
  rw [chartReduction_scheme_square_assoc, chart_deformationToComplex,
    CycleQ2GeometricSurfaceCoefficients.awayι_projectiveToComplex, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact chartReduction_complex i.1 i.2 c

end CycleQ2LiteralProjectiveDeformationCover

end

#print axioms CycleQ2LiteralProjectiveDeformationCover.closedFiber_surjective
#print axioms CycleQ2LiteralProjectiveDeformationCover.deformation_chartOpen_cover
#print axioms CycleQ2LiteralProjectiveDeformationCover.closedFiber_overComplex
