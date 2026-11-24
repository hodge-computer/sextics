import Proposal.GeometricSeedSectionCurveRows
import Proposal.GeometricSurfaceCurveCharts

/-!
# The evaluation image is the existing curve's actual chart kernel

The curve is the previously defined specialized projective curve. Its
existing closed immersion is composed with the already constructed
literalCartierProjectiveIso, so its target is exactly the surface carrying
the global evaluation. The original homogeneous quotient and actual Proj
structure map commute on each unchanged coordinate chart.

The resulting chart kernel is the same original row ideal as the image
of globalEvaluation. No replacement zero locus is defined.
Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedSectionSheafCurveBinding

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry MvPolynomial
open CycleQ2GeometricSurfaceAdjunction CycleQ2SeedProjectiveImageCocycle
  CycleQ2SeedSectionSheafImage CycleQ2SeedSectionCurveRows
  CycleQ2SpecializedProjectiveCurve CycleQ2SpecializedCurveCoordinateChart
  CycleQ2RelativeCurveChart

attribute [local instance] CycleQ2SpecializedProjectiveCurve.nativePointSurfaceCommRing
  CycleQ2SpecializedProjectiveCurve.nativeSpecializedCurveCommRing

/-- The existing specialized curve, with its existing target transported
through the original identity-on-polynomials projective isomorphism. -/
def curveToSurface (t : Fin 3 → ℂ) : specializedCurve seed t ⟶ Surface :=
  specializedCurveToSurface seed t ≫ literalCartierProjectiveIso.hom

instance curveToSurface_isClosedImmersion (t : Fin 3 → ℂ) :
    IsClosedImmersion (curveToSurface t) := by
  dsimp only [curveToSurface]
  infer_instance

def curveGradedMap (t : Fin 3 → ℂ) :
    LiteralCartierGrade →+*ᵍ specializedCurveGrade seed t :=
  (specializedCurveRingMap seed t).comp literalFromCartierGraded

theorem curveGradedMap_irrelevant (t : Fin 3 → ℂ) :
    HomogeneousIdeal.irrelevant (specializedCurveGrade seed t) ≤
      (HomogeneousIdeal.irrelevant LiteralCartierGrade).map (curveGradedMap t) :=
  HomogeneousIdeal.irrelevant_le_map_comp
    (f := literalFromCartierGraded) (g := specializedCurveRingMap seed t)
    literalOriginal_irrelevant_le_map
    (irrelevant_le_map_specializedCurveRingMap seed t)

theorem curveToSurface_eq_map (t : Fin 3 → ℂ) :
    curveToSurface t = Proj.map (curveGradedMap t) (curveGradedMap_irrelevant t) :=
  (Proj.map_comp literalFromCartierGraded (specializedCurveRingMap seed t)
    literalOriginal_irrelevant_le_map (irrelevant_le_map_specializedCurveRingMap seed t)).symm

theorem curveGradedMap_coordinate (t : Fin 3 → ℂ) (i : Fin 3) :
    curveGradedMap t
        (CycleQ2GeometricSurfaceOverlap.coordinateDen 57 1 i.succ) =
      specializedCurveRingMap seed t
        (CycleQ2IncidenceDehomogenizedChart.surfaceQuotient seed (X i.succ.castSucc)) := by
  change specializedCurveRingMap seed t
      (literalFromCartierGraded
        (CycleQ2GeometricCartierNormalLift.surfaceQuotient 57 1 (X i.succ.castSucc))) = _
  rw [literalFromCartierGraded_polynomial] <;> rfl

theorem curveToSurface_preimage_patch (t : Fin 3 → ℂ) (i : Fin 3) :
    curveToSurface t ⁻¹ᵁ Patch i = specializedCoordinatePatch seed t i.succ := by
  rw [curveToSurface_eq_map]
  change Proj.map (curveGradedMap t) (curveGradedMap_irrelevant t) ⁻¹ᵁ
    Proj.basicOpen LiteralCartierGrade
      (CycleQ2GeometricSurfaceOverlap.coordinateDen 57 1 i.succ) = _
  rw [Proj.map_preimage_basicOpen, curveGradedMap_coordinate] <;> rfl

/-- The actual quotient map of homogeneous coordinate rings, with its
denominator named by the unchanged specialized curve coordinate. -/
def curveCoordinateMap (t : Fin 3 → ℂ) (i : Fin 3) :
    CycleQ2GeometricSurfaceDehomogenizedCharts.CoordinateRing 57 1 i.succ →+*
      SpecializedCoordinateRing seed t i.succ :=
  CycleQ2GeometricSurfaceCurveCharts.gradedAwayMapTo LiteralCartierGrade
    (specializedCurveGrade seed t) (curveGradedMap t)
    (CycleQ2GeometricSurfaceOverlap.coordinateDen 57 1 i.succ)
    (specializedCurveRingMap seed t
      (CycleQ2IncidenceDehomogenizedChart.surfaceQuotient seed (X i.succ.castSucc)))
    (curveGradedMap_coordinate t i)

theorem curveCoordinateMap_factor (t : Fin 3 → ℂ) (i : Fin 3) :
    curveCoordinateMap t i =
      (specializedCoordinateMap seed t i.succ).toRingHom.comp
        (literalCartierLocalizationEquiv (X i.succ.castSucc)).symm.toRingHom := by
  apply RingHom.ext
  intro z
  have hpoly : literalFromCartierGraded
      (CycleQ2GeometricCartierNormalLift.surfaceQuotient 57 1 (X i.succ.castSucc)) =
      CycleQ2IncidenceDehomogenizedChart.surfaceQuotient seed (X i.succ.castSucc) :=
    literalFromCartierGraded_polynomial (X i.succ.castSucc)
  have hfrom : Submonoid.powers
      (CycleQ2GeometricCartierNormalLift.surfaceQuotient 57 1 (X i.succ.castSucc)) ≤
      (Submonoid.powers
        (CycleQ2IncidenceDehomogenizedChart.surfaceQuotient seed (X i.succ.castSucc))).comap
          literalFromCartierGraded := by
    rintro _ ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    change (CycleQ2IncidenceDehomogenizedChart.surfaceQuotient seed (X i.succ.castSucc)) ^ n =
      literalFromCartierGraded
        ((CycleQ2GeometricCartierNormalLift.surfaceQuotient 57 1 (X i.succ.castSucc)) ^ n)
    rw [map_pow, hpoly]
  have hcurve : Submonoid.powers
      (CycleQ2IncidenceDehomogenizedChart.surfaceQuotient seed (X i.succ.castSucc)) ≤
      (Submonoid.powers (specializedCurveRingMap seed t
        (CycleQ2IncidenceDehomogenizedChart.surfaceQuotient seed (X i.succ.castSucc)))).comap
          (specializedCurveRingMap seed t) := by
    rintro _ ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    exact (map_pow (specializedCurveRingMap seed t) _ n).symm
  change HomogeneousLocalization.map (𝒜 := LiteralCartierGrade)
      (ℬ := specializedCurveGrade seed t)
      ((specializedCurveRingMap seed t).comp literalFromCartierGraded)
      (hfrom.trans (Submonoid.monotone_comap hcurve)) z =
    HomogeneousLocalization.map (𝒜 := LiteralOriginalGrade)
      (ℬ := specializedCurveGrade seed t) (specializedCurveRingMap seed t) hcurve
      (HomogeneousLocalization.map (𝒜 := LiteralCartierGrade) (ℬ := LiteralOriginalGrade)
        literalFromCartierGraded hfrom z)
  exact (HomogeneousLocalization.map_map
    (𝒜 := LiteralCartierGrade) (ℬ := LiteralOriginalGrade) (𝒞 := specializedCurveGrade seed t)
    (f := literalFromCartierGraded)
    (g := specializedCurveRingMap seed t) hfrom hcurve z).symm

def curveCoordinateSectionsEquiv (t : Fin 3 → ℂ) (i : Fin 3) :
    SpecializedCoordinateRing seed t i.succ ≃+*
      Γ(specializedCurve seed t, specializedCoordinatePatch seed t i.succ) :=
  (Proj.basicOpenIsoAway (specializedCurveGrade seed t)
    (specializedCurveRingMap seed t
      (CycleQ2IncidenceDehomogenizedChart.surfaceQuotient seed (X i.succ.castSucc)))
    ((specializedCurveRingMap seed t).2
      (CycleQ2IncidenceDehomogenizedChart.coordinate_mem_grade seed i.succ))
    (by decide)).commRingCatIsoToRingEquiv

def curveChartSectionMap (t : Fin 3 → ℂ) (i : Fin 3) :
    Γ(Surface, Patch i) →+*
      Γ(specializedCurve seed t, specializedCoordinatePatch seed t i.succ) :=
  ((curveToSurface t).appLE (Patch i) (specializedCoordinatePatch seed t i.succ)
    (curveToSurface_preimage_patch t i).symm.le).hom

/-- The structure-map component is the original specialized quotient
map under exactly the section equivalence used to bind the original rows. -/
theorem curveChartSectionMap_coordinate (t : Fin 3 → ℂ) (i : Fin 3)
    (z : CycleQ2IncidenceDehomogenizedChart.CoordinateRing seed i.succ) :
    curveChartSectionMap t i (seedCoordinateSectionsEquiv i z) =
      curveCoordinateSectionsEquiv t i (specializedCoordinateMap seed t i.succ z) := by
  have h := ConcreteCategory.congr_hom
    (CycleQ2GeometricSurfaceCurveCharts.gradedAwayMapTo_section LiteralCartierGrade
      (specializedCurveGrade seed t) (curveGradedMap t) (curveGradedMap_irrelevant t)
      (CycleQ2GeometricSurfaceOverlap.coordinateDen 57 1 i.succ)
      (specializedCurveRingMap seed t
        (CycleQ2IncidenceDehomogenizedChart.surfaceQuotient seed (X i.succ.castSucc)))
      (curveGradedMap_coordinate t i)
      (CycleQ2GeometricSurfaceDehomogenizedCharts.coordinate_mem_grade 57 1 i.succ))
    (literalCartierLocalizationEquiv (X i.succ.castSucc) z)
  simp only [← curveToSurface_eq_map] at h
  change curveChartSectionMap t i (seedCoordinateSectionsEquiv i z) =
    curveCoordinateSectionsEquiv t i (curveCoordinateMap t i
      (literalCartierLocalizationEquiv (X i.succ.castSucc) z)) at h
  rw [curveCoordinateMap_factor] at h
  exact h.trans (congrArg
    (fun w : CycleQ2IncidenceDehomogenizedChart.CoordinateRing seed i.succ =>
      curveCoordinateSectionsEquiv t i (specializedCoordinateMap seed t i.succ w))
    ((literalCartierLocalizationEquiv (X i.succ.castSucc)).symm_apply_apply z))

/-- Renaming the actual preimage open does not change the structure-map kernel. -/
theorem curveChartSectionMap_ker_eq (t : Fin 3 → ℂ) (i : Fin 3) :
    RingHom.ker (curveChartSectionMap t i) =
      RingHom.ker ((curveToSurface t).app (Patch i)).hom := by
  let h : specializedCoordinatePatch seed t i.succ ≤ curveToSurface t ⁻¹ᵁ Patch i :=
    (curveToSurface_preimage_patch t i).symm.le
  have he : homOfLE h = eqToHom (curveToSurface_preimage_patch t i).symm :=
    Subsingleton.elim _ _
  letI : IsIso (homOfLE h) := by rw [he]; infer_instance
  have hinj := (ConcreteCategory.bijective_of_isIso
    ((specializedCurve seed t).presheaf.map (homOfLE h).op)).injective
  ext a
  change (specializedCurve seed t).presheaf.map (homOfLE h).op
      ((curveToSurface t).app (Patch i) a) = 0 ↔
    (curveToSurface t).app (Patch i) a = 0
  constructor
  · intro ha
    apply hinj
    simpa only [map_zero] using ha
  · intro ha
    rw [ha, map_zero]

/-- CLOSED SOURCE-LEVEL ENDPOINT: this is the kernel of the actual
existing curve's structure map on the original surface coordinate open. -/
theorem curve_section_kernel (t : Fin 3 → ℂ) (i : Fin 3) :
    RingHom.ker ((curveToSurface t).app (Patch i)).hom =
      Ideal.span (Set.range (sectionRows t i (Patch i) le_rfl)) := by
  have hk : (RingHom.ker (curveChartSectionMap t i)).comap
      (seedCoordinateSectionsEquiv i).toRingHom = normalizedSectionIdeal seed t i.succ := by
    ext a
    change curveChartSectionMap t i (seedCoordinateSectionsEquiv i a) = 0 ↔ _
    rw [curveChartSectionMap_coordinate,
      (curveCoordinateSectionsEquiv t i).map_eq_zero_iff]
    rw [← specializedCoordinateMap_ker seed t i.succ] <;> rfl
  calc
    _ = RingHom.ker (curveChartSectionMap t i) := (curveChartSectionMap_ker_eq t i).symm
    _ = ((RingHom.ker (curveChartSectionMap t i)).comap
        (seedCoordinateSectionsEquiv i).toRingHom).map
          (seedCoordinateSectionsEquiv i).toRingHom :=
      (Ideal.map_comap_of_surjective (seedCoordinateSectionsEquiv i).toRingHom
        (seedCoordinateSectionsEquiv i).surjective _).symm
    _ = _ := by rw [hk, normalizedSectionIdeal_map_to_sections]

theorem globalEvaluation_range_eq_curve_kernel (t : Fin 3 → ℂ) (i : Fin 3) :
    LinearMap.range (globalEvaluationLinear t (Patch i)) =
      RingHom.ker ((curveToSurface t).app (Patch i)).hom := by
  rw [globalEvaluationLinear_range t i (Patch i) le_rfl, curve_section_kernel]

end CycleQ2SeedSectionSheafCurveBinding

end

#print axioms CycleQ2SeedSectionSheafCurveBinding.curveToSurface_isClosedImmersion
#print axioms CycleQ2SeedSectionSheafCurveBinding.curveChartSectionMap_coordinate
#print axioms CycleQ2SeedSectionSheafCurveBinding.curve_section_kernel
#print axioms CycleQ2SeedSectionSheafCurveBinding.globalEvaluation_range_eq_curve_kernel
