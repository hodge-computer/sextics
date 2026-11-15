import Proposal.GeometricSeedSectionSheafCurveBinding
import Proposal.GeometricSeedSectionSheafGlobalMono
import Proposal.GeometricIntrinsicNormal

/-!
# The original evaluation factors through the actual curve ideal

The chart kernel comparison uses the existing specialized curve and its
original closed immersion. Its three original row sections vanish on that
curve. Restriction gives their vanishing on every chart subopen, and the
actual pushed-forward structure sheaf is separated on the original cover.
Consequently the already constructed global evaluation factors through
the native categorical kernel ideal of this particular curve morphism.

For the same regular vector the factor map is a monomorphism. On each
whole original coordinate chart it is surjective on sections, hence gives
an actual linear equivalence there. Upgrading those chart section
equivalences to a sheaf isomorphism also requires the affine comparison;
it is not inferred from global sections of arbitrary sheaves.

Source-only draft: no Lean elaboration or kernel replay was run.
Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedSectionSheafKernel

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2SeedProjectiveImageCocycle CycleQ2SeedSectionSheaf
  CycleQ2SeedSectionSheafEvaluation CycleQ2SeedSectionSheafLocal
  CycleQ2SeedSectionSheafGlobal CycleQ2SeedSectionSheafImage
  CycleQ2SeedSectionSheafCurveBinding CycleQ2SeedSectionAffineInjective
  CycleQ2SeedSectionSheafGlobalMono CycleQ2GeometricIntrinsicNormal

/-- The native kernel ideal of the unchanged specialized curve morphism. -/
def curveIdeal (t : Fin 3 → ℂ) : Surface.Modules :=
  kernelIdealSheaf (curveToSurface t)

/-- The actual structure map of that curve, in the native module category. -/
def curveStructureMap (t : Fin 3 → ℂ) :
    structureModule Surface ⟶
      (show Surface.Modules from imageStructureModule (curveToSurface t)) :=
  schemeStructureMap (curveToSurface t)

theorem sectionRows_restrict (t : Fin 3 → ℂ) (i : Fin 3)
    (V W : Surface.Opens) (hWV : W ≤ V) (hi : V ≤ Patch i) (a : Fin 3) :
    Surface.presheaf.map (homOfLE hWV).op (sectionRows t i V hi a) =
      sectionRows t i W (hWV.trans hi) a :=
  chartSectionMap_restrict i V W hWV hi _

/-- The original row section vanishes under the actual curve structure
map on every original chart subopen. -/
theorem sectionRows_curve_zero (t : Fin 3 → ℂ) (i : Fin 3)
    (V : Surface.Opens) (hi : V ≤ Patch i) (a : Fin 3) :
    (curveStructureMap t).app V (sectionRows t i V hi a) = 0 := by
  have htop : (curveStructureMap t).app (Patch i)
      (sectionRows t i (Patch i) le_rfl a) = 0 := by
    change sectionRows t i (Patch i) le_rfl a ∈
      RingHom.ker ((curveToSurface t).app (Patch i)).hom
    rw [curve_section_kernel]
    exact Ideal.subset_span ⟨a, rfl⟩
  have h := congrArg
    (moduleRes (show Surface.Modules from imageStructureModule (curveToSurface t)) hi) htop
  rw [moduleRes_app, map_zero] at h
  change (curveStructureMap t).app V
    (Surface.presheaf.map (homOfLE hi).op
      (sectionRows t i (Patch i) le_rfl a)) = 0 at h
  rw [sectionRows_restrict] at h
  exact h

theorem evaluation_curve_zero_on_patch (t : Fin 3 → ℂ) (i : Fin 3)
    (V : Surface.Opens) (hi : V ≤ Patch i) (s : Γ(twistedIdeal, V)) :
    (curveStructureMap t).app V ((globalEvaluation t).app V s) = 0 := by
  have himage : globalEvaluationLinear t V s ∈
      Ideal.span (Set.range (sectionRows t i V hi)) := by
    rw [← globalEvaluationLinear_range t i V hi]
    exact ⟨s, rfl⟩
  have hvanish : Ideal.span (Set.range (sectionRows t i V hi)) ≤
      RingHom.ker ((curveToSurface t).app V).hom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact sectionRows_curve_zero t i V hi a
  exact hvanish himage

/-- The vanishing is global because it is checked in the actual
pushed-forward structure sheaf on the unchanged three-chart cover. -/
theorem globalEvaluation_comp_curveStructureMap (t : Fin 3 → ℂ) :
    globalEvaluation t ≫ curveStructureMap t = 0 := by
  apply Scheme.Modules.hom_ext
  intro V
  apply ConcreteCategory.hom_ext
  intro s
  let N : Surface.Modules := imageStructureModule (curveToSurface t)
  let S : TopCat.Sheaf Ab Surface := ⟨N.presheaf, N.isSheaf⟩
  change (curveStructureMap t).app V ((globalEvaluation t).app V s) = 0
  apply S.eq_of_locally_eq' (fun i : Fin 3 => V ⊓ Patch i) V
    (fun _ => homOfLE inf_le_left) (cover_on V)
  intro i
  change moduleRes N (show V ⊓ Patch i ≤ V from inf_le_left)
      ((curveStructureMap t).app V ((globalEvaluation t).app V s)) =
    moduleRes N inf_le_left 0
  rw [map_zero, moduleRes_app, moduleRes_app]
  exact evaluation_curve_zero_on_patch t i (V ⊓ Patch i) inf_le_right _

/-- The canonical factorization through the existing curve's actual kernel. -/
def evaluationToCurveIdeal (t : Fin 3 → ℂ) : twistedIdeal ⟶ curveIdeal t :=
  kernel.lift (curveStructureMap t) (globalEvaluation t)
    (globalEvaluation_comp_curveStructureMap t)

theorem evaluationToCurveIdeal_ι (t : Fin 3 → ℂ) :
    evaluationToCurveIdeal t ≫ kernel.ι (curveStructureMap t) = globalEvaluation t :=
  kernel.lift_ι _ _ _

/-- This factorization has the original functional values in the
original ring of sections; the kernel has not been replaced by an image. -/
theorem evaluationToCurveIdeal_coordinate (t : Fin 3 → ℂ) (V : Surface.Opens)
    (s : Γ(twistedIdeal, V)) :
    (kernelIdealSectionEquiv (curveToSurface t) V
      ((evaluationToCurveIdeal t).app V s) : Γ(Surface, V)) =
      globalEvaluationLinear t V s := by
  rw [kernelIdealSectionEquiv_coe]
  exact congrArg (fun f : twistedIdeal ⟶ structureModule Surface => f.app V s)
    (evaluationToCurveIdeal_ι t)

theorem evaluationToCurveIdeal_app_injective (t : Fin 3 → ℂ)
    (hreg : ∀ i : Fin 3, ChartRegular t i) (V : Surface.Opens) :
    Function.Injective ((evaluationToCurveIdeal t).app V) := by
  intro s r h
  apply globalEvaluation_app_injective t hreg V
  have hc := congrArg
    (fun a => (kernelIdealSectionEquiv (curveToSurface t) V a : Γ(Surface, V))) h
  simpa only [evaluationToCurveIdeal_coordinate] using hc

theorem evaluationToCurveIdeal_mono (t : Fin 3 → ℂ)
    (hreg : ∀ i : Fin 3, ChartRegular t i) : Mono (evaluationToCurveIdeal t) where
  right_cancellation {M} f g h := by
    apply Scheme.Modules.hom_ext
    intro V
    apply ConcreteCategory.hom_ext
    intro s
    apply evaluationToCurveIdeal_app_injective t hreg V
    exact congrArg (fun k : M ⟶ curveIdeal t => k.app V s) h

/-- On each whole original affine patch, every section of the actual
curve ideal has a preimage under the original evaluation. -/
theorem evaluationToCurveIdeal_app_surjective_patch (t : Fin 3 → ℂ) (i : Fin 3) :
    Function.Surjective ((evaluationToCurveIdeal t).app (Patch i)) := by
  intro y
  let a := kernelIdealSectionEquiv (curveToSurface t) (Patch i) y
  have ha : (a : Γ(Surface, Patch i)) ∈
      LinearMap.range (globalEvaluationLinear t (Patch i)) := by
    rw [globalEvaluation_range_eq_curve_kernel]
    exact a.property
  obtain ⟨s, hs⟩ := ha
  refine ⟨s, ?_⟩
  apply (kernelIdealSectionEquiv (curveToSurface t) (Patch i)).injective
  apply Subtype.ext
  rw [evaluationToCurveIdeal_coordinate]
  exact hs

theorem evaluationToCurveIdeal_app_bijective_patch (t : Fin 3 → ℂ)
    (hreg : ∀ i : Fin 3, ChartRegular t i) (i : Fin 3) :
    Function.Bijective ((evaluationToCurveIdeal t).app (Patch i)) :=
  ⟨evaluationToCurveIdeal_app_injective t hreg (Patch i),
    evaluationToCurveIdeal_app_surjective_patch t i⟩

/-- A genuine equivalence of the original whole-patch section modules. -/
def curveIdealPatchSectionsEquiv (t : Fin 3 → ℂ)
    (hreg : ∀ i : Fin 3, ChartRegular t i) (i : Fin 3) :
    Γ(twistedIdeal, Patch i) ≃ₗ[Γ(Surface, Patch i)] Γ(curveIdeal t, Patch i) :=
  LinearEquiv.ofBijective (((evaluationToCurveIdeal t).val.app (op (Patch i))).hom)
    (evaluationToCurveIdeal_app_bijective_patch t hreg i)

end CycleQ2SeedSectionSheafKernel

end

#print axioms CycleQ2SeedSectionSheafKernel.globalEvaluation_comp_curveStructureMap
#print axioms CycleQ2SeedSectionSheafKernel.evaluationToCurveIdeal_coordinate
#print axioms CycleQ2SeedSectionSheafKernel.evaluationToCurveIdeal_mono
#print axioms CycleQ2SeedSectionSheafKernel.curveIdealPatchSectionsEquiv
