import Proposal.GeometricLiteralThreefoldFilteredCechQuotient
import Proposal.GeometricLiteralNonzeroSweptRestriction

/-!
# Detection of the filtered threefold test by the original moving curve

The total Cech cocycle retains both its vertex three-forms and its overlap
two-forms. Projection to ordinary H-one of two-forms is detected by the
signed trace of the genuine marked moving curve. This proves nonvanishing
in the actual filtration-two Cech quotient. No comparison with unfiltered
de Rham cohomology or with the protected rational four-form is asserted.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralThreefoldFilteredNonzero

open AlgebraicGeometry CategoryTheory
open CycleQ2LiteralThreefoldFilteredCechQuotient
open CycleQ2LiteralThreefoldTestClass (ambientTestClass)
open CycleQ2LiteralAbelJacobiEvaluationDerived (timeHodge)
open CycleQ2LiteralAbelJacobiQPullbackDerived (qHodge)
open CycleQ2LiteralMovingCurveDifferentialNonzero
open CycleQ2LiteralThreefoldCurvePairing (signed_class)
open CycleQ2IncidenceEtaleParameter (parameterScheme)
open CycleQ2IncidenceSeedFiberCover (seedBasePoint)
open CycleQ2SeedSectionAffineInjective (ChartRegular)

local instance (X : Scheme.{0}) : HasExt.{1} (CycleQ2InjectiveCech.AbSheaf (show TopCat from X)) :=
  HasExt.standard _

variable (t : Fin 3 → ℂ) (hi : AlgebraicIndependent ℚ t) (hr : ∀ i, ChartRegular t i)
  (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V)

/-- The actual curve trace after the genuine sheaf-cohomology projection. -/
def detector : FilteredCechHThree →+ ℂ :=
  (differentialTrace t hr).comp ((timeHodge t hi V hV).comp
    ((qHodge V t).comp hodgeProjection))

theorem detector_testClass :
    detector t hi hr V hV testClass = -differentialTrace t hr (curveClass t) := by
  change differentialTrace t hr (timeHodge t hi V hV (qHodge V t (hodgeProjection testClass))) = _
  rw [hodgeProjection_testClass, signed_class t hi V hV, map_neg]

theorem detector_testClass_ne_zero : detector t hi hr V hV testClass ≠ 0 := by
  rw [detector_testClass]
  exact neg_ne_zero.mpr (differentialTrace_curveClass_ne_zero t hr)

/-- The corrected ambient test is nonzero already in the filtered total Cech quotient. -/
theorem testClass_ne_zero : testClass ≠ 0 := by
  intro h
  exact CycleQ2LiteralNonzeroSweptRestriction.ambient_nonzero
    (hodgeProjection_testClass.symm.trans
      ((congrArg hodgeProjection h).trans hodgeProjection.map_zero))

/-- No four vertex two-forms have the actual total test as their coboundary. -/
theorem testCochain_not_boundary :
    ¬ ∃ v : TotalTwo, boundary v =
      CycleQ2LiteralThreefoldDeRhamTestClass.increasingTestCocycle := by
  rintro ⟨v, hv⟩
  apply testClass_ne_zero
  exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨v, hv⟩

end CycleQ2LiteralThreefoldFilteredNonzero
end

#print axioms CycleQ2LiteralThreefoldFilteredNonzero.detector_testClass
#print axioms CycleQ2LiteralThreefoldFilteredNonzero.testClass_ne_zero
#print axioms CycleQ2LiteralThreefoldFilteredNonzero.testCochain_not_boundary
