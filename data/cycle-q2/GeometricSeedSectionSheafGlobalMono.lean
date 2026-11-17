import Proposal.GeometricSeedSectionAffineInjective
import Proposal.GeometricSeedSectionSheafLocal
import Proposal.GeometricSeedSectionDensity

/-!
# Injectivity of the actual global section evaluation

The actual twisted kernel restricts to the original ideal on every chart.
For the original regular section vector, evaluation of that ideal is
injective on every section module. Sheaf separatedness on the original
three-chart cover therefore proves that the global evaluation is a
monomorphism. No replacement source or supplied global injectivity is
used.

The final endpoint chooses this same vector inside any prescribed
nonempty principal parameter open and retains the original proper flat
nonempty first-order curve and its literal seed-fiber isomorphism.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md
for attribution and the separate remaining residue-exactness theorem.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedSectionSheafGlobalMono

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2SeedProjectiveImageCocycle CycleQ2SeedSectionSheaf
  CycleQ2SeedSectionSheafSections CycleQ2SeedSectionSheafGlobal
  CycleQ2SeedSectionSheafLocal CycleQ2SeedSectionAffineInjective

/-- On a chart, the actual global map is the original injective
functional composed with the original source projection. -/
theorem globalEvaluation_app_injective_on_patch (t : Fin 3 → ℂ)
    (i : Fin 3) (hreg : ChartRegular t i) (V : Surface.Opens)
    (hi : V ≤ Patch i) : Function.Injective ((globalEvaluation t).app V) := by
  letI : CommRing Γ(patchStructure (Patch i), V) :=
    CycleQ2SeedSectionSheafSections.patchSectionsCommRing (Patch i) V
  intro s r h
  apply chartProjection_app_injective i V hi
  apply patchEvaluation_app_injective t i hreg V
  apply (patchSectionsEquiv (Patch i) V hi).injective
  change evaluatedCoordinate t i V hi s = evaluatedCoordinate t i V hi r
  simpa only [globalEvaluation_on_patch t i V hi] using h

/-- The actual structure-sheaf-valued evaluation is injective on every
open, by the original cover and separatedness of its source sheaf. -/
theorem globalEvaluation_app_injective (t : Fin 3 → ℂ)
    (hreg : ∀ i : Fin 3, ChartRegular t i) (V : Surface.Opens) :
    Function.Injective ((globalEvaluation t).app V) := by
  intro s r h
  let S : TopCat.Sheaf Ab Surface := ⟨twistedIdeal.presheaf, twistedIdeal.isSheaf⟩
  apply S.eq_of_locally_eq' (fun i : Fin 3 => V ⊓ Patch i) V
    (fun _ => homOfLE inf_le_left) (cover_on V) s r
  intro i
  change moduleRes twistedIdeal (show V ⊓ Patch i ≤ V from inf_le_left) s =
    moduleRes twistedIdeal inf_le_left r
  apply globalEvaluation_app_injective_on_patch t i (hreg i)
    (V ⊓ Patch i) inf_le_right
  rw [← moduleRes_app, ← moduleRes_app, h]

/-- A genuine categorical monomorphism into the original structure module. -/
theorem globalEvaluation_mono (t : Fin 3 → ℂ)
    (hreg : ∀ i : Fin 3, ChartRegular t i) : Mono (globalEvaluation t) where
  right_cancellation {M} f g h := by
    apply Scheme.Modules.hom_ext
    intro V
    apply ConcreteCategory.hom_ext
    intro s
    apply globalEvaluation_app_injective t hreg V
    exact congrArg (fun k : M ⟶ structureModule Surface => k.app V s) h

open CycleQ2FirstOrderCurve CycleQ2FirstOrderCurveSeedFiber
  CycleQ2FirstOrderCurveChartFlat CycleQ2SpecializedProjectiveCurve
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2SeedSectionIdealComparison

attribute [local instance] CycleQ2IncidenceFirstOrder.firstOrderAlgebra

/-- CLOSED SOURCE-LEVEL ENDPOINT: the same original vector gives the
proper flat nonempty first-order curve and the genuine global ideal
monomorphism, while avoiding any prescribed polynomial zero set. -/
theorem exists_flat_curve_and_global_monomorphism_in_principal_open
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
      (∀ i : Fin 3, ChartRegular t i) ∧ Mono (globalEvaluation t) := by
  obtain ⟨t, htP, ht, hflat, hproper, hiso, hseed, hfiber, hfirst, hlocal⟩ :=
    CycleQ2SeedSectionDensity.exists_nonempty_flat_curve_in_principal_open P hP
  have hreg : ∀ i : Fin 3, ChartRegular t i := fun i p => (hlocal i p).1
  exact ⟨t, htP, ht, hflat, hproper, hiso, hseed, hfiber, hfirst,
    hreg, globalEvaluation_mono t hreg⟩

end CycleQ2SeedSectionSheafGlobalMono

end

#print axioms CycleQ2SeedSectionSheafGlobalMono.globalEvaluation_app_injective
#print axioms CycleQ2SeedSectionSheafGlobalMono.globalEvaluation_mono
#print axioms CycleQ2SeedSectionSheafGlobalMono.exists_flat_curve_and_global_monomorphism_in_principal_open
