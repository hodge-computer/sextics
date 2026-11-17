import Proposal.GeometricFirstOrderTensorReduction
import Proposal.GeometricRelativeCurveChartFiber

/-!
# Original surface and curve charts modulo the actual first-order epsilon

The generic tensor reduction is bound to the retained dehomogenized
surface charts and their actual three-row curve quotients. It sends each
normalized row to the same row at the original literal seed. This fixes
the coefficient map and the equations needed by the infinitesimal
regular-quotient criterion; regularity on principal chart refinements
and flatness of their ambient algebras are separate obligations.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2FirstOrderChartReduction

open scoped DualNumber TensorProduct
open CycleQ2IncidenceUniversalChart CycleQ2IncidenceEtaleParameter
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2IncidenceDehomogenizedChart
  CycleQ2IncidenceChartSeedFiber CycleQ2IncidenceChartFiberScheme
  CycleQ2IncidenceFirstOrder CycleQ2FirstOrderTensorReduction
  CycleQ2DualNumberRegularQuotient CycleQ2RelativeCurveChart
  CycleQ2RelativeCurveChartFiber

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower

local instance incidenceChartCommRing (i : Fin 4) :
    CommRing (DehomogenizedRing incidencePoint i) := inferInstance
local instance seedChartCommRing (i : Fin 4) :
    CommRing (DehomogenizedRing (seedPoint (57 : ℂ) Complex.I) i) := inferInstance
local instance incidenceCurveChartCommRing (t : Fin 3 → ℂ) (i : Fin 4) :
    CommRing (AffineCurveChart incidencePoint t i) := inferInstance
local instance seedCurveChartCommRing (t : Fin 3 → ℂ) (i : Fin 4) :
    CommRing (AffineCurveChart (seedPoint (57 : ℂ) Complex.I) t i) := inferInstance
local instance curveChartSeedFiberCommRing (t : Fin 3 → ℂ) (i : Fin 4) :
    CommRing (CurveChartSeedFiber t i) := inferInstance

abbrev FirstOrderSurfaceChart (i : Fin 4) :=
  FirstOrderTensor (DehomogenizedRing incidencePoint i)

/-- Exact reduction of the actual first-order surface chart. -/
def surfaceChartReductionEquiv (i : Fin 4) :
    (FirstOrderSurfaceChart i ⧸ epsilonIdeal (k := ℂ) (FirstOrderSurfaceChart i)) ≃+*
      DehomogenizedRing (seedPoint (57 : ℂ) Complex.I) i :=
  (epsilonReductionEquiv (DehomogenizedRing incidencePoint i)).toRingEquiv.trans
    (seedChartFiberEquiv i).toRingEquiv

@[simp] theorem surfaceChartReductionEquiv_includeRight
    (i : Fin 4) (a : DehomogenizedRing incidencePoint i) :
    surfaceChartReductionEquiv i
      (Ideal.Quotient.mk (epsilonIdeal (k := ℂ) (FirstOrderSurfaceChart i))
        (1 ⊗ₜ[ParameterAlgebra] a)) = seedChartSpecialization i a := by
  change seedChartFiberEquiv i
    (epsilonReductionEquiv (DehomogenizedRing incidencePoint i)
      (Ideal.Quotient.mk (epsilonIdeal (k := ℂ) (FirstOrderSurfaceChart i))
        (1 ⊗ₜ[ParameterAlgebra] a))) = _
  rw [epsilonReductionEquiv_tmul, TrivSqZeroExt.fst_one]
  rfl

def firstOrderSectionRow (t : Fin 3 → ℂ) (i : Fin 4) (j : Fin 3) :
    FirstOrderSurfaceChart i :=
  1 ⊗ₜ[ParameterAlgebra] affineSectionEquation incidencePoint t i j

/-- The normalized defining rows reduce to the original literal seed
rows, with their fixed complex vector unchanged. -/
theorem firstOrderSectionRow_reduction (t : Fin 3 → ℂ) (i : Fin 4) (j : Fin 3) :
    surfaceChartReductionEquiv i
      (Ideal.Quotient.mk (epsilonIdeal (k := ℂ) (FirstOrderSurfaceChart i))
        (firstOrderSectionRow t i j)) =
      affineSectionEquation (seedPoint (57 : ℂ) Complex.I) t i j := by
  rw [firstOrderSectionRow, surfaceChartReductionEquiv_includeRight,
    seedChartSpecialization_affineSectionEquation]

abbrev FirstOrderCurveChart (t : Fin 3 → ℂ) (i : Fin 4) :=
  FirstOrderTensor (AffineCurveChart incidencePoint t i)

/-- The actual three-row quotient, after first-order base change and
reduction, is the retained seed curve chart quotient. -/
def curveChartReductionEquiv (t : Fin 3 → ℂ) (i : Fin 4) :
    (FirstOrderCurveChart t i ⧸ epsilonIdeal (k := ℂ) (FirstOrderCurveChart t i)) ≃+*
      AffineCurveChart (seedPoint (57 : ℂ) Complex.I) t i :=
  (epsilonReductionEquiv (AffineCurveChart incidencePoint t i)).toRingEquiv.trans
    (curveChartSeedFiberEquiv t i).toRingEquiv

@[simp] theorem curveChartReductionEquiv_includeRight
    (t : Fin 3 → ℂ) (i : Fin 4) (a : AffineCurveChart incidencePoint t i) :
    curveChartReductionEquiv t i
      (Ideal.Quotient.mk (epsilonIdeal (k := ℂ) (FirstOrderCurveChart t i))
        (1 ⊗ₜ[ParameterAlgebra] a)) = curveChartSpecialization t i a := by
  change curveChartSeedFiberEquiv t i
    (epsilonReductionEquiv (AffineCurveChart incidencePoint t i)
      (Ideal.Quotient.mk (epsilonIdeal (k := ℂ) (FirstOrderCurveChart t i))
        (1 ⊗ₜ[ParameterAlgebra] a))) = _
  rw [epsilonReductionEquiv_tmul, TrivSqZeroExt.fst_one]
  rfl

theorem curveChartReductionEquiv_mk (t : Fin 3 → ℂ) (i : Fin 4)
    (a : DehomogenizedRing incidencePoint i) :
    curveChartReductionEquiv t i
      (Ideal.Quotient.mk (epsilonIdeal (k := ℂ) (FirstOrderCurveChart t i))
        (1 ⊗ₜ[ParameterAlgebra] Ideal.Quotient.mk (affineSectionIdeal incidencePoint t i) a)) =
      Ideal.Quotient.mk (affineSectionIdeal (seedPoint (57 : ℂ) Complex.I) t i)
        (seedChartSpecialization i a) := by
  rw [curveChartReductionEquiv_includeRight, curveChartSpecialization_mk]

#print axioms surfaceChartReductionEquiv
#print axioms firstOrderSectionRow_reduction
#print axioms curveChartReductionEquiv
#print axioms curveChartReductionEquiv_mk

end CycleQ2FirstOrderChartReduction
end
