import Proposal.GeometricLiteralMovingDivisorOrbitComparison
import Proposal.GeometricLiteralOrbitChernResidue

/-!
# The normalized residue of the actual moving divisor

All chart-regular choices of the moving curve have the same pairing.
The positive fourth hyperplane twist lifts to the ambient deformation.
The product of the three translated divisor classes contributes exactly
three times the original cubic pairing, with its original sign.
The same section vector can be required to give a proper flat deformation.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralMovingChernTrace

open CategoryTheory TopologicalSpace AlgebraicGeometry
  CycleQ2LiteralMovingDivisorChern CycleQ2LiteralMovingDivisorOrbitComparison
  CycleQ2LiteralMovingDivisorHyperplane CycleQ2LiteralOrbitChernResidue
  CycleQ2LiteralCotangentShortExact CycleQ2LinkageComponentAlgebra
  CycleQ2LiteralSheafOneClasses CycleQ2IncidenceFirstOrderCanonicalH2
  CycleQ2CanonicalCubicDiagram CycleQ2LiteralCotangentTrace
  CycleQ2SeedSectionAffineInjective CycleQ2FirstOrderCurve CycleQ2FirstOrderCurveSeedFiber

local instance additiveHasExt : HasExt.{1} (TopCat.Sheaf AddCommGrpCat.{0}
    (CycleQ2LiteralProjectiveCotangent.ClosedSurface : TopCat)) := HasExt.standard _

local instance schemeSheavesHasExt (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

variable (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)

theorem movingClass_cubic_product :
    cubicH2 firstOrderWeightedCubic
        ((movingClass t ht).comp cotangentAdditiveShortExact.extClass rfl) =
      (3 : ℕ) • cubicH2 firstOrderWeightedCubic
        (chernDerivedClass.comp cotangentAdditiveShortExact.extClass rfl) := by
  rw [movingClass_connecting, orbitClass_eq_orbitDerivedClass]
  exact orbitDerivedClass_cubicH2 complexRoot complexRoot_cube complexRoot_quadratic

theorem movingClass_cubic_trace_ne_zero :
    algebraicTrace (cubicH2 firstOrderWeightedCubic
      ((movingClass t ht).comp cotangentAdditiveShortExact.extClass rfl)) ≠ 0 := by
  rw [movingClass_connecting, orbitClass_eq_orbitDerivedClass]
  exact orbitDerivedClass_cubic_trace_ne_zero complexRoot complexRoot_cube complexRoot_quadratic

theorem exists_flat_moving_curve_with_nonzero_trace
    (P : MvPolynomial (Fin 3) ℂ) (hP : P ≠ 0) :
    ∃ (s : Fin 3 → ℂ) (hs : ∀ i, ChartRegular s i),
      MvPolynomial.eval s P ≠ 0 ∧ s ≠ 0 ∧ Flat (firstOrderCurveToBase s) ∧
      IsProper (firstOrderCurveToBase s) ∧ Nonempty (FirstOrderCurveSeedFiber s) ∧
      algebraicTrace (cubicH2 firstOrderWeightedCubic
        ((movingClass s hs).comp cotangentAdditiveShortExact.extClass rfl)) ≠ 0 := by
  obtain ⟨s, hPs, hs, hf, hp, _, _, hseed, _, hreg, _⟩ :=
    CycleQ2SeedSectionInvertible.exists_flat_curve_and_invertible_ideal_in_principal_open P hP
  exact ⟨s, hreg, hPs, hs, hf, hp, hseed, movingClass_cubic_trace_ne_zero s hreg⟩

end CycleQ2LiteralMovingChernTrace
end

#print axioms CycleQ2LiteralMovingChernTrace.movingClass_cubic_product
#print axioms CycleQ2LiteralMovingChernTrace.exists_flat_moving_curve_with_nonzero_trace
