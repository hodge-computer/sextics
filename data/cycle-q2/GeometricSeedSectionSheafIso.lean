import Proposal.GeometricSeedSectionSheafKernel

/-!
# The original twisted ideal is the actual specialized curve ideal

The whole-patch bijections of the canonical kernel factor are upgraded
on the actual affine charts. Both affine module sheaves are recovered by
their native tilde--Gamma counits. For the source this follows from the
proved restriction isomorphism to the original chart ideal. For the
target it follows from open base change for the actual curve morphism.
The affine ring map is literally its map on the original patch sections.

The original regular vector therefore makes the existing kernel factor
an isomorphism on every chart subopen. Unique source lifts glue on the
original three-chart cover, giving an isomorphism of actual global
structure-module sheaves, with hom equal to the original evaluation
factor. No replacement curve or separately chosen ideal is introduced.

Source-only draft: no Lean elaboration or kernel replay was run.
Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedSectionSheafIso

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2SeedProjectiveImageCocycle CycleQ2SeedSectionSheaf
  CycleQ2SeedSectionSheafLocal CycleQ2SeedSectionSheafGlobal
  CycleQ2SeedSectionSheafCurveBinding CycleQ2SeedSectionSheafKernel
  CycleQ2SeedSectionAffineInjective CycleQ2GeometricIntrinsicNormal

/-! ## The exact original affine square -/

theorem patch_isAffineOpen (i : Fin 3) : IsAffineOpen (Patch i) :=
  Proj.isAffineOpen_basicOpen
    (CycleQ2CartierSurfaceGrading.surfaceGrade 57 1)
    (CycleQ2GeometricSurfaceOverlap.coordinateDen 57 1 i.succ)
    (CycleQ2GeometricSurfaceDehomogenizedCharts.coordinate_mem_grade 57 1 i.succ)
    (by decide)

theorem curvePreimage_isAffineOpen (t : Fin 3 → ℂ) (i : Fin 3) :
    IsAffineOpen (curveToSurface t ⁻¹ᵁ Patch i) := by
  rw [curveToSurface_preimage_patch]
  exact CycleQ2SpecializedCurveCoordinateChart.specializedCoordinatePatch_isAffineOpen
    CycleQ2SeedSectionCurveRows.seed t i.succ

/-- The canonical affine chart over the actual original patch section ring. -/
abbrev patchAffineMap (i : Fin 3) : Spec Γ(Surface, Patch i) ⟶ Surface :=
  (patch_isAffineOpen i).fromSpec

/-- The canonical affine chart of the actual curve preimage, not a new
scheme defined from an unrelated row quotient. -/
abbrev curveAffineMap (t : Fin 3 → ℂ) (i : Fin 3) :
    Spec Γ(CycleQ2SpecializedProjectiveCurve.specializedCurve
      CycleQ2SeedSectionCurveRows.seed t, curveToSurface t ⁻¹ᵁ Patch i) ⟶
      CycleQ2SpecializedProjectiveCurve.specializedCurve
        CycleQ2SeedSectionCurveRows.seed t :=
  (curvePreimage_isAffineOpen t i).fromSpec

theorem curveAffineSquare (t : Fin 3 → ℂ) (i : Fin 3) :
    IsPullback (Spec.map ((curveToSurface t).app (Patch i)))
      (curveAffineMap t i) (patchAffineMap i) (curveToSurface t) := by
  apply IsOpenImmersion.isPullback
  · simpa only [Scheme.Hom.appLE_eq_app] using
      (IsAffineOpen.SpecMap_appLE_fromSpec (curveToSurface t)
        (patch_isAffineOpen i) (curvePreimage_isAffineOpen t i) le_rfl).symm
  · rw [IsAffineOpen.opensRange_fromSpec, IsAffineOpen.opensRange_fromSpec]

/-! ## Native affine reconstruction for both endpoints -/

instance chartIdeal_isQuasicoherent (i : Fin 3) :
    (chartIdeal i).IsQuasicoherent := by
  dsimp only [chartIdeal, affineIdeal]
  infer_instance

/-- Restrict the proved original chart identification to its canonical
affine scheme; the right side is still the original tilde ideal. -/
def twistedIdealAffineIso (i : Fin 3) :
    twistedIdeal.restrict (patchAffineMap i) ≅
      (chartIdeal i).restrict (patch_isAffineOpen i).isoSpec.inv :=
  (Scheme.Modules.restrictFunctorComp (patch_isAffineOpen i).isoSpec.inv
    (Patch i).ι).app twistedIdeal ≪≫
      (Scheme.Modules.restrictFunctor (patch_isAffineOpen i).isoSpec.inv).mapIso
        (chartRestrictionIso i)

instance twistedIdealAffine_isQuasicoherent (i : Fin 3) :
    (twistedIdeal.restrict (patchAffineMap i)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec Γ(Surface, Patch i)).ringCatSheaf).prop_of_iso
    (twistedIdealAffineIso i).symm inferInstance

instance twistedIdealAffine_fromTildeΓ_isIso (i : Fin 3) :
    IsIso (twistedIdeal.restrict (patchAffineMap i)).fromTildeΓ := inferInstance

/-- The native kernel ideal on this affine chart is the kernel of the
literal original curve structure map on the original patch sections. -/
def curveIdealAffineIso (t : Fin 3 → ℂ) (i : Fin 3) :
    (curveIdeal t).restrict (patchAffineMap i) ≅
      (show (Spec Γ(Surface, Patch i)).Modules from
        kernelIdealSheaf (Spec.map ((curveToSurface t).app (Patch i)))) :=
  kernelIdealOpenBaseChangeIso (curveToSurface t) (patchAffineMap i)
    (curveAffineMap t i) (Spec.map ((curveToSurface t).app (Patch i)))
    (curveAffineSquare t i)

instance curveIdealAffine_fromTildeΓ_isIso (t : Fin 3 → ℂ) (i : Fin 3) :
    IsIso ((curveIdeal t).restrict (patchAffineMap i)).fromTildeΓ :=
  (isIso_fromTildeΓ_iff_isLocalizing _).mpr
    (isLocalizing_of_iso (modulesSpecToSheaf.mapIso (curveIdealAffineIso t i).symm)
      (affineIdeal_isLocalizing ((curveToSurface t).app (Patch i))))

/-- This is the restriction of the already defined canonical factor. -/
def affineEvaluationToCurveIdeal (t : Fin 3 → ℂ) (i : Fin 3) :
    twistedIdeal.restrict (patchAffineMap i) ⟶
      (curveIdeal t).restrict (patchAffineMap i) :=
  (Scheme.Modules.restrictFunctor (patchAffineMap i)).map (evaluationToCurveIdeal t)

theorem affineEvaluationToCurveIdeal_top_bijective (t : Fin 3 → ℂ)
    (hreg : ∀ i : Fin 3, ChartRegular t i) (i : Fin 3) :
    Function.Bijective ((affineEvaluationToCurveIdeal t i).app ⊤) := by
  change Function.Bijective
    ((evaluationToCurveIdeal t).app (patchAffineMap i ''ᵁ ⊤))
  have htop : patchAffineMap i ''ᵁ ⊤ = Patch i := by
    rw [Scheme.Hom.image_top_eq_opensRange, IsAffineOpen.opensRange_fromSpec]
  rw [htop]
  exact evaluationToCurveIdeal_app_bijective_patch t hreg i

/-- The whole-patch section bijection determines an isomorphism because
both exact affine sheaves have proved native reconstruction counits. -/
theorem affineEvaluationToCurveIdeal_isIso (t : Fin 3 → ℂ)
    (hreg : ∀ i : Fin 3, ChartRegular t i) (i : Fin 3) :
    IsIso (affineEvaluationToCurveIdeal t i) := by
  rw [← isIso_iff_of_reflects_iso _ modulesSpecToSheaf]
  apply isLocalizing_of_isIso_app_top
  · apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact affineEvaluationToCurveIdeal_top_bijective t hreg i
  · exact (isIso_fromTildeΓ_iff_isLocalizing _).mp inferInstance
  · exact (isIso_fromTildeΓ_iff_isLocalizing _).mp inferInstance

/-! ## Actual chart subopens and global source gluing -/

theorem evaluationToCurveIdeal_app_bijective_on_patch (t : Fin 3 → ℂ)
    (hreg : ∀ i : Fin 3, ChartRegular t i) (i : Fin 3)
    (V : Surface.Opens) (hi : V ≤ Patch i) :
    Function.Bijective ((evaluationToCurveIdeal t).app V) := by
  letI := affineEvaluationToCurveIdeal_isIso t hreg i
  have h := ConcreteCategory.bijective_of_isIso
    ((affineEvaluationToCurveIdeal t i).app (patchAffineMap i ⁻¹ᵁ V))
  change Function.Bijective ((evaluationToCurveIdeal t).app
    (patchAffineMap i ''ᵁ (patchAffineMap i ⁻¹ᵁ V))) at h
  have hV : patchAffineMap i ''ᵁ (patchAffineMap i ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
      IsAffineOpen.opensRange_fromSpec, inf_eq_right.mpr hi]
  simpa only [hV] using h

/-- Every actual kernel section lifts globally: its unique lifts on
the original chart intersections agree by the proved injectivity. -/
theorem evaluationToCurveIdeal_app_surjective (t : Fin 3 → ℂ)
    (hreg : ∀ i : Fin 3, ChartRegular t i) (V : Surface.Opens) :
    Function.Surjective ((evaluationToCurveIdeal t).app V) := by
  intro y
  choose s hs using fun i : Fin 3 =>
    (evaluationToCurveIdeal_app_bijective_on_patch t hreg i (V ⊓ Patch i)
      inf_le_right).surjective
        (moduleRes (curveIdeal t) (show V ⊓ Patch i ≤ V from inf_le_left) y)
  have hcompat (i j : Fin 3) :
      moduleRes twistedIdeal
        (show (V ⊓ Patch i) ⊓ (V ⊓ Patch j) ≤ V ⊓ Patch i from inf_le_left) (s i) =
      moduleRes twistedIdeal inf_le_right (s j) := by
    apply evaluationToCurveIdeal_app_injective t hreg _
    rw [← moduleRes_app, ← moduleRes_app, hs i, hs j,
      moduleRes_comp, moduleRes_comp]
  let S : TopCat.Sheaf Ab Surface := ⟨twistedIdeal.presheaf, twistedIdeal.isSheaf⟩
  obtain ⟨x, hx, _⟩ := S.existsUnique_gluing' (fun i : Fin 3 => V ⊓ Patch i) V
    (fun _ => homOfLE inf_le_left) (cover_on V) s hcompat
  refine ⟨x, ?_⟩
  let T : TopCat.Sheaf Ab Surface := ⟨(curveIdeal t).presheaf, (curveIdeal t).isSheaf⟩
  apply T.eq_of_locally_eq' (fun i : Fin 3 => V ⊓ Patch i) V
    (fun _ => homOfLE inf_le_left) (cover_on V)
  intro i
  change moduleRes (curveIdeal t) (show V ⊓ Patch i ≤ V from inf_le_left)
      ((evaluationToCurveIdeal t).app V x) = moduleRes (curveIdeal t) inf_le_left y
  rw [moduleRes_app]
  have hx' : moduleRes twistedIdeal (show V ⊓ Patch i ≤ V from inf_le_left) x = s i :=
    hx i
  rw [hx']
  exact hs i

theorem evaluationToCurveIdeal_isIso (t : Fin 3 → ℂ)
    (hreg : ∀ i : Fin 3, ChartRegular t i) : IsIso (evaluationToCurveIdeal t) :=
  Scheme.Modules.Hom.isIso_iff_isIso_app.mpr fun V =>
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨evaluationToCurveIdeal_app_injective t hreg V,
        evaluationToCurveIdeal_app_surjective t hreg V⟩

/-- CLOSED SOURCE-LEVEL ENDPOINT: the independently defined original
negative-fourth twist is isomorphic to the actual existing curve ideal.
The isomorphism is exactly the original evaluation factored into that
native kernel, for the same original regular parameter vector. -/
def twistedIdealCurveIso (t : Fin 3 → ℂ)
    (hreg : ∀ i : Fin 3, ChartRegular t i) : twistedIdeal ≅ curveIdeal t := by
  letI := evaluationToCurveIdeal_isIso t hreg
  exact asIso (evaluationToCurveIdeal t)

theorem twistedIdealCurveIso_hom (t : Fin 3 → ℂ)
    (hreg : ∀ i : Fin 3, ChartRegular t i) :
    (twistedIdealCurveIso t hreg).hom = evaluationToCurveIdeal t := rfl

theorem twistedIdealCurveIso_hom_ι (t : Fin 3 → ℂ)
    (hreg : ∀ i : Fin 3, ChartRegular t i) :
    (twistedIdealCurveIso t hreg).hom ≫ kernel.ι (curveStructureMap t) =
      globalEvaluation t :=
  evaluationToCurveIdeal_ι t

open CycleQ2FirstOrderCurve CycleQ2FirstOrderCurveSeedFiber
  CycleQ2FirstOrderCurveChartFlat CycleQ2SpecializedProjectiveCurve
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2SeedSectionIdealComparison

attribute [local instance] CycleQ2IncidenceFirstOrder.firstOrderAlgebra

/-- The same original parameter vector simultaneously retains the actual
proper flat nonempty first-order curve, every original regularity witness,
and the genuine global identification with its actual kernel ideal. -/
theorem exists_flat_curve_and_global_ideal_iso_in_principal_open
    (P : MvPolynomial (Fin 3) ℂ) (hP : P ≠ 0) :
    ∃ t : Fin 3 → ℂ, MvPolynomial.eval t P ≠ 0 ∧ t ≠ 0 ∧
      AlgebraicGeometry.Flat (firstOrderCurveToBase t) ∧
      AlgebraicGeometry.IsProper (firstOrderCurveToBase t) ∧
      Nonempty (specializedCurve
        (seedPoint (57 : ℂ) Complex.I) t ≅ FirstOrderCurveSeedFiber t) ∧
      Nonempty (specializedCurve (seedPoint (57 : ℂ) Complex.I) t) ∧
      Nonempty (FirstOrderCurveSeedFiber t) ∧
      (∀ (i : Fin 4) (p : Pivot),
        IsSMulRegular (SeedRefinement i p) (seedRefinedEquation t i p)) ∧
      (∀ i : Fin 3, ChartRegular t i) ∧ Mono (globalEvaluation t) ∧
      Nonempty (twistedIdeal ≅ curveIdeal t) := by
  obtain ⟨t, htP, ht, hflat, hproper, hiso, hseed, hfiber, hfirst, hreg, hmono⟩ :=
    CycleQ2SeedSectionSheafGlobalMono.exists_flat_curve_and_global_monomorphism_in_principal_open
      P hP
  exact ⟨t, htP, ht, hflat, hproper, hiso, hseed, hfiber, hfirst,
    hreg, hmono, ⟨twistedIdealCurveIso t hreg⟩⟩

end CycleQ2SeedSectionSheafIso

end

#print axioms CycleQ2SeedSectionSheafIso.curveAffineSquare
#print axioms CycleQ2SeedSectionSheafIso.curveIdealAffineIso
#print axioms CycleQ2SeedSectionSheafIso.affineEvaluationToCurveIdeal_isIso
#print axioms CycleQ2SeedSectionSheafIso.evaluationToCurveIdeal_isIso
#print axioms CycleQ2SeedSectionSheafIso.twistedIdealCurveIso_hom_ι
#print axioms CycleQ2SeedSectionSheafIso.exists_flat_curve_and_global_ideal_iso_in_principal_open
