import Proposal.GeometricCurveCylinderPullback
import Proposal.GeometricCurveParameterTangent

/-!
# Pulling fixed threefold forms to the original moving curve

The two chart maps are induced by the fixed sextic equation and the actual
specialization modulo the dual-number parameter. On this tower contraction
against a parameter tangent gives minus the retained cubic coefficient.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralCylinderEvaluation

open scoped DualNumber
open CycleQ2CurveCylinderPullback CycleQ2LiteralAbelJacobiEquations CycleQ2LiteralAbelJacobiMovingNormal
  CycleQ2LiteralAbelJacobiContraction CycleQ2FirstOrderChartReduction
  CycleQ2DualNumberRegularQuotient

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  CycleQ2LiteralAbelJacobiContraction.fixedAlgebra
  CycleQ2LiteralAbelJacobiContraction.fixedTower

variable (t : Fin 3 → ℂ) (i : Fin 4)

local instance familyRing : CommRing (B t i) := inferInstance
local instance closedRing : CommRing (A t i) := inferInstance
local instance threefoldRing : CommRing (T i) := inferInstance
attribute [local instance] CycleQ2CurveParameterTangent.chartComplexAlgebra

local instance familyComplexSMul : SMul ℂ (B t i) :=
  (CycleQ2CurveParameterTangent.chartComplexAlgebra t i).toSMul
local instance familyComplexModule : Module ℂ (B t i) :=
  (CycleQ2CurveParameterTangent.chartComplexAlgebra t i).toModule

theorem chartMap_constant (c : ℂ) :
    algebraMap ℂ (B t i) c = algebraMap ℂ[ε] (B t i) (algebraMap ℂ ℂ[ε] c) := by
  change chartMap t i (MvPolynomial.C c) = _
  rw [← dualEval_constant, MvPolynomial.map_C, dualEval, MvPolynomial.eval₂Hom_C]

/-- The moving curve lies on the fixed threefold over the entire first order. -/
def toFamily : T i →+* B t i :=
  Ideal.Quotient.lift (fixedIdeal i) (chartMap t i)
    (fun _ hx => ((Ideal.span_singleton_le_iff_mem (RingHom.ker (chartMap t i))).mpr (chartMap_F t i)) hx)

local instance familyAlgebra : Algebra (T i) (B t i) := (toFamily t i).toAlgebra

local instance familyComplexTower : IsScalarTower ℂ (T i) (B t i) :=
  IsScalarTower.of_algebraMap_eq (R := ℂ) (S := T i) (A := B t i) fun _ => rfl

/-- Specialization to the seed curve at the same section coefficients. -/
def toClosed : B t i →+* A t i :=
  (curveChartReductionEquiv t i).toRingHom.comp (Ideal.Quotient.mk _)

local instance reductionAlgebra : Algebra (B t i) (A t i) := (toClosed t i).toAlgebra

local instance fixedCurveTower : IsScalarTower (T i) (B t i) (A t i) := by
  apply IsScalarTower.of_algebraMap_eq (R := T i) (S := B t i) (A := A t i)
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact (chartMap_reduction t i p).symm

local instance familyReductionTower : IsScalarTower ℂ (B t i) (A t i) := by
  apply IsScalarTower.of_algebraMap_eq (R := ℂ) (S := B t i) (A := A t i)
  intro c
  rw [IsScalarTower.algebraMap_apply ℂ (T i) (A t i),
    IsScalarTower.algebraMap_apply ℂ (T i) (B t i),
    IsScalarTower.algebraMap_apply (T i) (B t i) (A t i)]

theorem specialize_epsilon :
    algebraMap (B t i) (A t i) (algebraMap ℂ[ε] (B t i) ε) = 0 := by
  change curveChartReductionEquiv t i (Ideal.Quotient.mk (epsilonIdeal (k := ℂ) (B t i))
    (algebraMap ℂ[ε] (B t i) ε)) = 0
  have h : Ideal.Quotient.mk (epsilonIdeal (k := ℂ) (B t i)) (algebraMap ℂ[ε] (B t i) ε) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [h, map_zero]

/-- Evaluating the pullback of the fixed cubic conormal wedge on the moving
curve produces the retained coefficient on the original closed fibre. -/
theorem evaluate_moving_cubic (v : Derivation ℂ (B t i) (A t i))
    (hv : v (algebraMap ℂ[ε] (B t i) ε) = 1) (β : KaehlerDifferential ℂ (T i)) :
    contractRestrict v (pullTwo (T i) (B t i)
      (exteriorPower.ιMulti (T i) 2 ![KaehlerDifferential.D ℂ (T i) (cubicOnT i), β])) =
      -(seedChartMap t i (tangentL i)) • KaehlerDifferential.map ℂ ℂ (T i) (A t i) β := by
  rw [contract_pullTwo_moving_equation v _ (specialize_epsilon t i) hv _ (chartMap t i (tangentL i))
    (chartMap_H t i)]
  exact congrArg (fun a : A t i => -a • KaehlerDifferential.map ℂ ℂ (T i) (A t i) β)
    (chartMap_reduction t i (tangentL i))

/-- Linear transport from the fibre quotient to the original curve, over
the actual total chart. -/
def specializeFibre : CycleQ2CurveParameterTangent.Fibre (k := ℂ) (B t i) →ₗ[B t i] A t i where
  toFun := curveChartReductionEquiv t i
  map_add' := (curveChartReductionEquiv t i).map_add
  map_smul' b x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change curveChartReductionEquiv t i (Ideal.Quotient.mk _ (b * a)) =
      curveChartReductionEquiv t i (Ideal.Quotient.mk _ b) *
        curveChartReductionEquiv t i (Ideal.Quotient.mk _ a)
    rw [map_mul, map_mul]

/-- On a smooth affine seed chart of the flat family, an actual
parameter tangent realizes the mixed component on every cubic conormal wedge. -/
theorem exists_evaluation [Module.Flat ℂ[ε] (B t i)] [Algebra.FormallySmooth ℂ (A t i)] :
    ∃ v : Derivation ℂ (B t i) (A t i), v (algebraMap ℂ[ε] (B t i) ε) = 1 ∧
      ∀ β : KaehlerDifferential ℂ (T i),
      contractRestrict v (pullTwo (T i) (B t i)
        (exteriorPower.ιMulti (T i) 2 ![KaehlerDifferential.D ℂ (T i) (cubicOnT i), β])) =
        -(seedChartMap t i (tangentL i)) • KaehlerDifferential.map ℂ ℂ (T i) (A t i) β := by
  obtain ⟨d, hd, _, _⟩ := CycleQ2CurveParameterTangent.exists_chart_velocity t i
  let v := (specializeFibre t i).compDer d
  have hv : v (algebraMap ℂ[ε] (B t i) ε) = 1 := by
    change curveChartReductionEquiv t i (d _) = 1
    rw [hd, map_one]
  exact ⟨v, hv, evaluate_moving_cubic t i v hv⟩

end CycleQ2LiteralCylinderEvaluation
end

#print axioms CycleQ2LiteralCylinderEvaluation.evaluate_moving_cubic
#print axioms CycleQ2LiteralCylinderEvaluation.exists_evaluation
