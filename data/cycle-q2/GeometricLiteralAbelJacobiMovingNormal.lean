import Proposal.GeometricLiteralAbelJacobiNormal
import Proposal.GeometricLiteralAbelJacobiEquations
import Proposal.GeometricFirstOrderNonemptyFlatCurve

/-!
# The embedded normal functional of the original moving section curve

On each weight-one chart of the original flat first-order section curve,
the class of the fixed sextic has normal value zero. The class of the
seed cubic has normal value minus the retained incidence cubic. Both
values are functions on the actual specialized curve with the same
section coefficients.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAbelJacobiMovingNormal

open scoped DualNumber
open CycleQ2IncidencePolynomialJacobianBinding CycleQ2RelativeCurveChart
  CycleQ2IncidenceDehomogenizedChart CycleQ2FirstOrderTensorReduction
  CycleQ2DualNumberRegularQuotient CycleQ2FirstOrderChartReduction
  CycleQ2LiteralAbelJacobiNormal CycleQ2LiteralAbelJacobiEquations

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower

variable (t : Fin 3 → ℂ) (i : Fin 4)

abbrev P := ChartPolynomial ℂ
abbrev B := FirstOrderCurveChart t i
abbrev A := AffineCurveChart (seedPoint (57 : ℂ) Complex.I) t i

local instance thickCommRing : CommRing (B t i) := inferInstance
local instance closedCommRing : CommRing (A t i) := inferInstance

local instance thickAlgebra : Algebra P (B t i) := (chartMap t i).toAlgebra
local instance closedAlgebra : Algebra P (A t i) := (seedChartMap t i).toAlgebra

local instance thickSMul : SMul P (B t i) := (thickAlgebra t i).toSMul
local instance thickModule : Module P (B t i) := (thickAlgebra t i).toModule
local instance thickTower : IsScalarTower P (B t i) (B t i) :=
  ⟨fun p a b => by change (chartMap t i p * a) * b = chartMap t i p * (a * b); exact mul_assoc _ _ _⟩

local instance quotientModule : Module P ((B t i) ⧸ epsilonIdeal (k := ℂ) (B t i)) :=
  Submodule.Quotient.module' (epsilonIdeal (k := ℂ) (B t i))

abbrev curveIdeal : Ideal P := RingHom.ker (seedChartMap t i)

theorem seedChartMap_surjective : Function.Surjective (seedChartMap t i) :=
  Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective

/-- The quotient by the embedded curve ideal gives back the original seed chart. -/
def curveQuotientEquiv : (P ⧸ curveIdeal t i) ≃+* A t i :=
  RingHom.quotientKerEquivOfSurjective (seedChartMap_surjective t i)

@[simp] theorem curveQuotientEquiv_mk (p : P) :
    curveQuotientEquiv t i (Ideal.Quotient.mk _ p) = seedChartMap t i p := rfl

theorem curveIdeal_le_comap : curveIdeal t i ≤ closedIdeal (k := ℂ) (B t i) P := by
  intro x hx
  change chartMap t i x ∈ epsilonIdeal (k := ℂ) (B t i)
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply (curveChartReductionEquiv t i).injective
  rw [map_zero]
  exact (chartMap_reduction t i x).trans hx

theorem curveIdeal_eq_comap : curveIdeal t i = closedIdeal (k := ℂ) (B t i) P := by
  apply le_antisymm (curveIdeal_le_comap t i)
  intro x hx
  change chartMap t i x ∈ epsilonIdeal (k := ℂ) (B t i) at hx
  change seedChartMap t i x = 0
  rw [← chartMap_reduction t i x, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

/-- The original quotient identification respects multiplication by every
fixed ambient polynomial. -/
def reductionLinear : ((B t i) ⧸ epsilonIdeal (k := ℂ) (B t i)) →ₗ[P] A t i where
  toFun := curveChartReductionEquiv t i
  map_add' := (curveChartReductionEquiv t i).map_add
  map_smul' r x := by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    change curveChartReductionEquiv t i
      (Ideal.Quotient.mk _ (chartMap t i r * b)) =
        seedChartMap t i r * curveChartReductionEquiv t i (Ideal.Quotient.mk _ b)
    rw [map_mul, map_mul, chartMap_reduction]

/-- A normal section on the conormal module of the original embedded seed curve. -/
def chartNormal [Module.Flat ℂ[ε] (B t i)] :
    (curveIdeal t i).Cotangent →ₗ[P] A t i :=
  (reductionLinear t i).comp ((normal (k := ℂ) (B t i) P).comp
    (Ideal.mapCotangent (curveIdeal t i) (closedIdeal (k := ℂ) (B t i) P)
      (AlgHom.id P P) (curveIdeal_le_comap t i)))

theorem chartNormal_lift [Module.Flat ℂ[ε] (B t i)] (p : curveIdeal t i) (b : B t i)
    (h : chartMap t i p = algebraMap ℂ[ε] (B t i) ε * b) :
    chartNormal t i ((curveIdeal t i).toCotangent p) =
      curveChartReductionEquiv t i (Ideal.Quotient.mk _ b) := by
  let q : closedIdeal (k := ℂ) (B t i) P := ⟨p, curveIdeal_le_comap t i p.property⟩
  exact congrArg (curveChartReductionEquiv t i)
    (normal_on_lift (k := ℂ) (B t i) P q b h)

private theorem member_of_lift (p : P) (b : B t i)
    (h : chartMap t i p = algebraMap ℂ[ε] (B t i) ε * b) :
    p ∈ curveIdeal t i := by
  change seedChartMap t i p = 0
  rw [← chartMap_reduction t i p, h, map_mul, quotient_epsilon_zero, zero_mul, map_zero]

def cubicEquation : curveIdeal t i := ⟨seedH i,
  member_of_lift t i _ (-(chartMap t i (tangentL i)))
    ((chartMap_H t i).trans (mul_neg _ _).symm)⟩

def sexticEquation : curveIdeal t i := ⟨seedF i,
  member_of_lift t i _ 0 ((chartMap_F t i).trans (mul_zero _).symm)⟩

theorem chartNormal_F [Module.Flat ℂ[ε] (B t i)] :
    chartNormal t i ((curveIdeal t i).toCotangent (sexticEquation t i)) = 0 := by
  rw [chartNormal_lift t i (sexticEquation t i) 0 ((chartMap_F t i).trans (mul_zero _).symm), map_zero, map_zero]

theorem chartNormal_H [Module.Flat ℂ[ε] (B t i)] :
    chartNormal t i ((curveIdeal t i).toCotangent (cubicEquation t i)) =
      -(seedChartMap t i (tangentL i)) := by
  rw [chartNormal_lift t i (cubicEquation t i) (-(chartMap t i (tangentL i)))
    ((chartMap_H t i).trans (mul_neg _ _).symm), map_neg, map_neg, chartMap_reduction]

open AlgebraicGeometry CycleQ2FirstOrderCurve CycleQ2FirstOrderCurveCharts
  CycleQ2SpecializedProjectiveCurve CycleQ2FirstOrderCurveSeedFiber

/-- A single nonzero choice yields a proper, flat projective first-order family,
its nonempty seed curve as closed fibre, and the original normal value on every chart. -/
theorem exists_moving_normal :
    ∃ t : Fin 3 → ℂ, t ≠ 0 ∧ AlgebraicGeometry.Flat (firstOrderCurveToBase t) ∧
      IsProper (firstOrderCurveToBase t) ∧
      Nonempty (specializedCurve (seedPoint (57 : ℂ) Complex.I) t) ∧
      Nonempty (CategoryTheory.Iso (specializedCurve (seedPoint (57 : ℂ) Complex.I) t)
        (FirstOrderCurveSeedFiber t)) ∧ ∀ i : Fin 4,
      ∃ ν : (curveIdeal t i).Cotangent →ₗ[P] A t i,
        ν ((curveIdeal t i).toCotangent (sexticEquation t i)) = 0 ∧
        ν ((curveIdeal t i).toCotangent (cubicEquation t i)) =
          -(seedChartMap t i (tangentL i)) := by
  obtain ⟨t, ht, hflat⟩ := CycleQ2FirstOrderCurvePivotCover.exists_nonzero_firstOrderCurveCharts_flat
  refine ⟨t, ht, firstOrderCurveToBase_flat_of_affineCharts t hflat, firstOrderCurveToBase_proper t,
    CycleQ2SeedSectionNonempty.seed_specializedCurve_nonempty t, ⟨firstOrderCurveSeedFiberIso t⟩,
    fun i => ?_⟩
  let := hflat i
  exact ⟨chartNormal t i, chartNormal_F t i, chartNormal_H t i⟩

end CycleQ2LiteralAbelJacobiMovingNormal
end

#print axioms CycleQ2LiteralAbelJacobiMovingNormal.exists_moving_normal
