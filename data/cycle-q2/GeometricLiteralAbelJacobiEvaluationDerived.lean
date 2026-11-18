import Proposal.GeometricLiteralAbelJacobiEvaluationGlobal
import Proposal.GeometricLiteralAbelJacobiQTest

/-!
# The infinitesimal cylinder map on coherent cohomology

The global tangent evaluation sends the moving family's two-form classes
to ordinary differential classes on its projective seed curve. Applied
to the pullback of the independent ambient threefold class it is computed
on the six original overlap sections of that class.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralAbelJacobiEvaluationDerived

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
  CycleQ2LiteralAbelJacobiEvaluationFiber CycleQ2LiteralAbelJacobiEvaluationGlobal
  CycleQ2LiteralAbelJacobiQPullback CycleQ2LiteralAbelJacobiQPullbackDerived CycleQ2LiteralAbelJacobiQTest
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceChartFiberScheme CycleQ2IncidenceSeedFiberCover
  CycleQ2LiteralMovingResidueCurve CycleQ2LiteralAbelJacobiTimeFamily CycleQ2LiteralThreefoldTestClass
  CycleQ2InjectiveCech CycleQ2FiniteCechOrbitPullback CycleQ2FiniteInjectiveCech CycleQ2FiniteCechHOne CycleQ2LiteralAmbientCharts

local instance (Z : Scheme.{0}) : HasExt.{1} (AbSheaf Z) := HasExt.standard _

variable (t : Fin 3 → ℂ) (ht : AlgebraicIndependent ℚ t)
  (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V)

def evaluationAdd :
    familyHodgeSheaf V t ⟶ push (seedToTime t V hV).base (curveForms t) :=
  (SheafOfModules.toSheaf (family V t).ringCatSheaf).map (timeEvaluation t ht V hV)

def timeHodge : (familyHodgeSheaf V t).H' 1 ⊤ →+ (curveForms t).H' 1 ⊤ :=
  pullH (seedToTime t V hV).base (evaluationAdd t ht V hV) 1

abbrev testCover := cover (seedToTime t V hV).base (cover (toThreefold V t).base fixedOpen)
abbrev testCover_top := cover_top (seedToTime t V hV).base _
  (cover_top (toThreefold V t).base _ fixedOpen_cover)

abbrev evaluatedTest := pullOne (seedToTime t V hV).base (evaluationAdd t ht V hV) _ (testCocycle V t)

theorem evaluatedTest_closed : IsOneCocycle (curveForms t) (testCover t V hV) (evaluatedTest t ht V hV) :=
  pullOne_closed _ _ _ _ (testCocycle_closed V t)

theorem testEvaluation_class :
    timeHodge t ht V hV (qHodge V t ambientTestClass) =
      cechOneClass (testCover t V hV) (testCover_top t V hV) (evaluatedTest t ht V hV)
        (evaluatedTest_closed t ht V hV) := by
  rw [qHodge_ambientTestClass]
  exact pullH_cech (seedToTime t V hV).base (evaluationAdd t ht V hV)
    (cover (toThreefold V t).base fixedOpen) (cover_top _ _ fixedOpen_cover)
    (testCocycle V t) (testCocycle_closed V t)

end CycleQ2LiteralAbelJacobiEvaluationDerived
end

#print axioms CycleQ2LiteralAbelJacobiEvaluationDerived.testEvaluation_class
