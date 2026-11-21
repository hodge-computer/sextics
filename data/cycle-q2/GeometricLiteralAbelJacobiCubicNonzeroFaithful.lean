import Proposal.GeometricSeedConeSection
import Mathlib.RingTheory.LocalProperties.Submodule

/-!
# Faithfulness of the original rows on the seed cone charts

On every coordinate chart the nine original pivots generate the unit ideal.
The original pivot regularity therefore determines a function by its products
with the three selected rows. Clearing the chart denominator first permits
regularity to be used on the original pivot rings themselves.

Prepared for fqlx with OpenAI ChatGPT assistance, following the construction
credited in solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2LiteralAbelJacobiCubicNonzeroFaithful

open CycleQ2IncidenceImageLine CycleQ2RegularSeedSection CycleQ2UniversalCurveCartier
  CycleQ2GeometricIncidenceProj CycleQ2SeedConeSection
  CycleQ2SegreFactorChartExact CycleQ2SeedCechLocalization

attribute [local instance] CycleQ2SeedConeSection.pointSurfaceCommRing
  CycleQ2SeedConeSection.seedCommRing CycleQ2SeedConeSection.chartCommRing

private theorem zero_on_pivots (t : Fin 3 → ℂ)
    (hreg : ∀ p : CycleQ2SegreCech.Chart, IsSMulRegular (CoefficientPivot seed p)
      (algebraMap (PointSurface seed) (CoefficientPivot seed p) (constantEquation seed t p.1)))
    (q : PointSurface seed) (hq : ∀ a, constantEquation seed t a * q = 0)
    (s : Finset (Fin 3)) (hs : s.Nonempty) : toCone s q = 0 := by
  let entry (p : CycleQ2SegreCech.Chart) := toCone s (basePivot seed p)
  have hspan : Ideal.span (Set.range entry) = ⊤ := by
    simpa only [entry, toCone_pivot s hs] using (factorData s hs).entries_generate
  apply Module.eq_zero_of_isLocalized_span (Set.range entry) hspan
    (fun z => Localization.Away z.val) (fun z => Algebra.linearMap (Chart s) (Localization.Away z.val))
  rintro ⟨_, ⟨p, rfl⟩⟩
  let g := (algebraMap (Chart s) (Localization.Away (entry p))).comp (toCone s).toRingHom
  have hu : IsUnit (g (basePivot seed p)) :=
    IsLocalization.Away.algebraMap_isUnit (entry p)
  have hloc : algebraMap (PointSurface seed) (CoefficientPivot seed p) q = 0 := by
    apply (hreg p).right_eq_zero_of_smul
    change algebraMap (PointSurface seed) (CoefficientPivot seed p) (constantEquation seed t p.1) * _ = 0
    rw [← map_mul, hq, map_zero]
  let lift := IsLocalization.Away.lift (S := CoefficientPivot seed p) (basePivot seed p) hu
  change g q = 0
  calc
    g q = lift (algebraMap (PointSurface seed) _ q) :=
      (IsLocalization.Away.lift_eq (S := CoefficientPivot seed p) _ hu q).symm
    _ = 0 := by rw [hloc, map_zero]

/-- The three original row products detect equality, including on every pairwise overlap. -/
theorem row_products_faithful (t : Fin 3 → ℂ)
    (hreg : ∀ p : CycleQ2SegreCech.Chart, IsSMulRegular (CoefficientPivot seed p)
      (algebraMap (PointSurface seed) (CoefficientPivot seed p) (constantEquation seed t p.1)))
    (s : Finset (Fin 3)) (hs : s.Nonempty) (x y : Chart s)
    (h : ∀ a, row t s a * x = row t s a * y) : x = y := by
  let d : A := algebraMap (MvPolynomial (Fin 3) ℂ) A (baseProduct ℂ s)
  obtain ⟨⟨b, m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers d) (x - y)
  let q := literalToSeed.symm b
  have hqmap : toCone s q = algebraMap A (Chart s) b := by
    change algebraMap A (Chart s) (literalToSeed (literalToSeed.symm b)) = _
    rw [AlgEquiv.apply_symm_apply]
  have hq (a : Fin 3) : constantEquation seed t a * q = 0 := by
    apply literalToSeed.injective
    apply CycleQ2SeedCechGlobalGluing.localization_injective ℂ 57 Complex.I s
    change toCone s (constantEquation seed t a * q) = toCone s 0
    rw [map_zero, map_mul, toCone_equation t s hs, hqmap, ← hm, ← mul_assoc,
      mul_sub, h a, sub_self, zero_mul]
  have hzero := zero_on_pivots t hreg q hq s hs
  apply sub_eq_zero.mp
  apply (IsLocalization.map_units (Chart s) m).mul_right_cancel
  simpa only [zero_mul, hm, ← hqmap] using hzero

end CycleQ2LiteralAbelJacobiCubicNonzeroFaithful
end

#print axioms CycleQ2LiteralAbelJacobiCubicNonzeroFaithful.row_products_faithful
