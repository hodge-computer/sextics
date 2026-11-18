import Proposal.GeometricLiteralAbelJacobiQPullbackDerived
import Proposal.GeometricLiteralThreefoldTestClass

/-!
# The fixed ambient test cocycle on the moving family

The second projection pulls back the six overlap two-forms for the weighted
sextic test deformation and their four triangle identities.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2LiteralAbelJacobiQTest

open CategoryTheory AlgebraicGeometry CycleQ2LiteralAbelJacobiQPullbackDerived CycleQ2IncidenceEtaleParameter
  CycleQ2LiteralAbelJacobiQPullback CycleQ2LiteralThreefoldHodgeCech
  CycleQ2LiteralThreefoldTestEdges CycleQ2LiteralThreefoldTestClass

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ)

/-- The six ambient overlap sections pulled to the original moving family. -/
abbrev testCocycle := CycleQ2FiniteCechOrbitPullback.pullOne (toThreefold V t).base (qAdd V t)
  CycleQ2LiteralAmbientCharts.fixedOpen (hodgeCocycle nativeEdge face).val

theorem testCocycle_closed : CycleQ2FiniteInjectiveCech.IsOneCocycle (familyHodgeSheaf V t)
    (CycleQ2FiniteCechOrbitPullback.cover (toThreefold V t).base CycleQ2LiteralAmbientCharts.fixedOpen)
    (testCocycle V t) :=
  CycleQ2FiniteCechOrbitPullback.pullOne_closed _ _ _ _ (fun i j k W hi hj hk =>
    ((hodgeCocycle nativeEdge face).condition i j k W hi hj hk).symm)

/-- Derived degree-one class on the time family for the fixed ambient test deformation. -/
def pulledTestClass := pulledHodgeClass V t nativeEdge face

theorem qHodge_ambientTestClass : qHodge V t ambientTestClass = pulledTestClass V t :=
  qHodge_native V t nativeEdge face

end CycleQ2LiteralAbelJacobiQTest
end

#print axioms CycleQ2LiteralAbelJacobiQTest.testCocycle_closed
#print axioms CycleQ2LiteralAbelJacobiQTest.qHodge_ambientTestClass
