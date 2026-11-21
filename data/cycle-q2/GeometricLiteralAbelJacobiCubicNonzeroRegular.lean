import Proposal.GeometricSeedConeSection
import Proposal.GeometricFirstOrderCurvePivotCover

/-!
# A common regular section for the seed cone and the first-order curve

The nine ordinary matrix pivots and the thirty-six refinements of the
four projective charts each have a unit coefficient in the retained
row of the original matrix. Simultaneous avoidance of their associated
primes supplies one constant vector for the ordinary cone argument and
for flatness of the original first-order curve charts.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAbelJacobiCubicNonzeroRegular

open CycleQ2SeedConeSection CycleQ2IncidenceImageLine
  CycleQ2UniversalCurveCartier CycleQ2RegularSeedSection
  CycleQ2FirstOrderChartReduction CycleQ2FirstOrderCurveChartFlat
  CycleQ2FirstOrderCurvePivotCover

attribute [local instance] CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  CycleQ2FirstOrderTensorReduction.firstOrderTensorCommRing
  CycleQ2FirstOrderChartFlatness.firstOrderTensorModule
  CycleQ2FirstOrderChartFlatness.firstOrderTensorSMul
  CycleQ2RelativeCurveChartFiber.incidenceCurveChartCommRing

private abbrev Pivot := CycleQ2SegreCech.Chart
private abbrev Index := Pivot ⊕ (Fin 4 × Pivot)

private def pivotRing : Index → Type
  | .inl p => CoefficientPivot seed p
  | .inr q => SeedRefinement q.1 q.2

private instance (q : Index) : CommRing (pivotRing q) := by
  cases q <;> dsimp only [pivotRing] <;> infer_instance

private instance (q : Index) : Algebra ℂ (pivotRing q) := by
  cases q <;> dsimp only [pivotRing] <;> infer_instance

private instance (q : Index) : IsNoetherianRing (pivotRing q) := by
  cases q <;> dsimp only [pivotRing] <;> infer_instance

private def coefficient : (q : Index) → Fin 3 → pivotRing q
  | .inl p => localizedMatrix seed p p.1
  | .inr q => seedRefinedCoefficient q.1 q.2

private theorem coefficient_hasUnit (q : Index) : ∃ j, IsUnit (coefficient q j) := by
  cases q with
  | inl p => exact ⟨p.2, localizedMatrix_pivot_isUnit seed p⟩
  | inr q =>
    change ∃ j, IsUnit (seedRefinedCoefficient q.1 q.2 j)
    exact ⟨q.2.2, IsLocalization.Away.algebraMap_isUnit (seedPivot q.1 q.2)⟩

/-- The ordinary nonzerodivisors and all four flat first-order chart rings
belong to the same nonzero complex section vector. -/
theorem exists_regular_flat :
    ∃ t : Fin 3 → ℂ, t ≠ 0 ∧
      (∀ p : CycleQ2SegreCech.Chart, IsSMulRegular (CoefficientPivot seed p)
        (algebraMap (PointSurface seed) (CoefficientPivot seed p) (constantEquation seed t p.1))) ∧
      ∀ i : Fin 4, Module.Flat (DualNumber ℂ) (FirstOrderCurveChart t i) := by
  obtain ⟨t, ht, reg⟩ :=
    CycleQ2SimultaneousRegularSection.exists_nonzero_simultaneous_regular
      (k := ℂ) pivotRing coefficient coefficient_hasUnit
  refine ⟨t, ht, ?_, ?_⟩
  · intro p
    rw [constantEquation_localize]
    exact reg (.inl p)
  · intro i
    apply curveChart_flat_of_refined
    intro p
    apply refinedCurveChart_flat
    rw [seedRefinedEquation_eq_sum]
    exact reg (.inr (i, p))

end CycleQ2LiteralAbelJacobiCubicNonzeroRegular

#print axioms CycleQ2LiteralAbelJacobiCubicNonzeroRegular.exists_regular_flat
