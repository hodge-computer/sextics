import Proposal.GeometricLiteralAbelJacobiCubicNonzeroChart
import Proposal.GeometricLiteralAbelJacobiCubicNonzeroCone
import Proposal.GeometricLiteralAbelJacobiCubicNonzeroDegree
import Proposal.GeometricLiteralAbelJacobiCubicNonzeroFaithful
import Proposal.GeometricLiteralAbelJacobiCubicNonzeroRegular
import Proposal.GeometricLiteralAbelJacobiCubicNonzeroSeed
import Proposal.GeometricLiteralAbelJacobiRelativeNormal

/-!
# The retained first-order normal is nonzero on the actual moving curve

A regular section of the literal seed matrix defines a curve on which
restrictions detect all surface equations of weight less than four. Vanishing
on its three original coordinate patches gives a cone multiplier. Multiplying
a degree-ten left factor by a polynomial of weight at most three has degree
below fourteen, the weight of the three original rows. The homogeneous
quotient calculation and regular linkage thus give vanishing on the surface.

The retained cubic has nonzero image on the surface. Choose the section using
the joint ordinary and first-order chart regularity conditions. On some chart
of this same nonempty proper flat first-order curve, its normal on the fixed
threefold takes a nonzero value on the class of the seed cubic.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralAbelJacobiCubicNonzero

open CycleQ2IncidenceNormalForm CycleQ2GeometricIncidenceProj CycleQ2IncidenceImageLine
  CycleQ2IncidenceDehomogenizedChart CycleQ2SeedConeSection
  CycleQ2UniversalCurveCartier CycleQ2RegularSeedSection
  CycleQ2IncidenceFirstOrderCanonicalH2 CycleQ2LiteralAbelJacobiEquations
  CycleQ2LiteralAbelJacobiCubicNonzeroChart CycleQ2LiteralAbelJacobiCubicNonzeroCone
  CycleQ2LiteralAbelJacobiCubicNonzeroDegree CycleQ2LiteralAbelJacobiCubicNonzeroFaithful
  CycleQ2LiteralAbelJacobiCubicNonzeroRegular CycleQ2LiteralAbelJacobiCubicNonzeroSeed

/-- Nonzero classes of weight below four remain nonzero on at least one of
three specified original charts of the regular section curve. -/
theorem exists_chart_nonzero (t : Fin 3 → ℂ)
    (hr : ∀ m : CycleQ2SegreCech.Chart, IsSMulRegular (CoefficientPivot seed m)
      (algebraMap (PointSurface seed) (CoefficientPivot seed m) (constantEquation seed t m.1)))
    (p : P) (n : ℕ) (hp : p.IsWeightedHomogeneous geometricWeight n) (hn : n < 4)
    (hneq : quotient p ≠ 0) :
    ∃ j : Fin 3, seedChartMap t j.succ (dehomogenize j.succ p) ≠ 0 := by
  classical
  by_contra! hz
  have hrow := fun j => cone_row_mem t j n p hp (hz j)
  obtain ⟨q, hq⟩ := exists_global_multiplier t p hrow
    (fun i j => row_products_faithful t hr {i,j} (by simp))
  exact hneq (low_degree_zero_of_global_multiplier t p n hp hn q hq)

open AlgebraicGeometry CycleQ2FirstOrderCurve CycleQ2FirstOrderChartReduction
  CycleQ2FirstOrderCurveCharts CycleQ2SpecializedProjectiveCurve
  CycleQ2LiteralAbelJacobiRelativeNormal

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  CycleQ2LiteralAbelJacobiMovingNormal.thickCommRing
  CycleQ2LiteralAbelJacobiContraction.fixedCommRing
  CycleQ2LiteralAbelJacobiContraction.seedChartCommRing
  CycleQ2LiteralAbelJacobiContraction.fixedAlgebra

/-- The actual flat moving curve has a nonzero embedded normal in the fixed
sextic. Its value is witnessed by the original cubic equation itself. -/
theorem exists_nonzero_moving_normal :
    ∃ t : Fin 3 → ℂ, t ≠ 0 ∧
      ∃ hf : ∀ i : Fin 4, Module.Flat (DualNumber ℂ) (FirstOrderCurveChart t i),
        AlgebraicGeometry.Flat (firstOrderCurveToBase t) ∧ IsProper (firstOrderCurveToBase t) ∧
        Nonempty (specializedCurve seed t) ∧ ∃ j : Fin 3,
          @relativeNormal t j.succ (hf j.succ)
            ((idealOnT t j.succ).toCotangent (cubicClass t j.succ)) ≠ 0 := by
  obtain ⟨t, ht, hr, hf⟩ := exists_regular_flat
  obtain ⟨j, hj⟩ := exists_chart_nonzero t hr firstOrderWeightedCubic.val 3
    firstOrderWeightedCubic.property (by decide) seed_cubic_ne_zero
  refine ⟨t, ht, hf, firstOrderCurveToBase_flat_of_affineCharts t hf, firstOrderCurveToBase_proper t,
    CycleQ2SeedSectionNonempty.seed_specializedCurve_nonempty t, j, ?_⟩
  let := hf j.succ
  rw [relativeNormal_cubic]
  exact neg_ne_zero.mpr hj

end CycleQ2LiteralAbelJacobiCubicNonzero
end

#print axioms CycleQ2LiteralAbelJacobiCubicNonzero.exists_chart_nonzero
#print axioms CycleQ2LiteralAbelJacobiCubicNonzero.exists_nonzero_moving_normal
