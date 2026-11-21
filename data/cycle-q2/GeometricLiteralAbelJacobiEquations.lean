import Proposal.GeometricFirstOrderChartReduction
import Proposal.GeometricIncidenceFirstOrderCanonicalH2

/-!
# The fixed sextic and the moving cubic on the infinitesimal curve

The constant ambient chart coordinates take values in the original first-order
curve chart. Evaluation sends the seed sextic to zero and the seed cubic to
minus epsilon times the actual pointed incidence cubic. Reduction recovers
the chart of the same specialized section curve.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAbelJacobiEquations

open MvPolynomial
open scoped DualNumber TensorProduct
open CycleQ2IncidenceNormalForm CycleQ2IncidenceUniversalChart
  CycleQ2IncidenceGenericPointSemantics CycleQ2IncidenceImageLine CycleQ2GeometricIncidenceProj
  CycleQ2IncidenceEtaleParameter CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2IncidenceDehomogenizedChart CycleQ2IncidenceChartSeedFiber CycleQ2IncidenceChartFiberScheme
  CycleQ2RelativeCurveChart CycleQ2RelativeCurveChartFiber
  CycleQ2IncidenceFirstOrder CycleQ2FirstOrderTensorReduction CycleQ2FirstOrderChartReduction
  CycleQ2IncidenceFirstOrderTrace CycleQ2IncidenceFirstOrderCanonicalH2

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower

private abbrev seed := seedPoint (57 : ℂ) Complex.I

def seedF (i : Fin 4) := dehomogenize i (pointEquationF seed)
def seedH (i : Fin 4) := dehomogenize i (pointEquationH seed)
def tangentL (i : Fin 4) := dehomogenize i firstOrderWeightedCubic.val

variable (t : Fin 3 → ℂ) (i : Fin 4)

def relativeEval : ChartPolynomial ParameterAlgebra →+* FirstOrderCurveChart t i :=
  (Algebra.TensorProduct.includeRight (R := ParameterAlgebra) (A := ℂ[ε])
    (B := AffineCurveChart incidencePoint t i)).toRingHom.comp
      ((Ideal.Quotient.mk (affineSectionIdeal incidencePoint t i)).comp (dehomogenizedMap incidencePoint i))

def chartMap : ChartPolynomial ℂ →+* FirstOrderCurveChart t i :=
  (relativeEval t i).comp (MvPolynomial.map (algebraMap ℂ ParameterAlgebra))

def seedChartMap : ChartPolynomial ℂ →+* AffineCurveChart seed t i :=
  (Ideal.Quotient.mk (affineSectionIdeal seed t i)).comp (dehomogenizedMap seed i)

theorem chartMap_reduction (p : ChartPolynomial ℂ) :
    curveChartReductionEquiv t i (Ideal.Quotient.mk _ (chartMap t i p)) = seedChartMap t i p := by
  change curveChartReductionEquiv t i (Ideal.Quotient.mk _
    (1 ⊗ₜ[ParameterAlgebra] Ideal.Quotient.mk _ (dehomogenizedMap incidencePoint i
      (MvPolynomial.map (algebraMap ℂ ParameterAlgebra) p)))) = _
  rw [curveChartReductionEquiv_includeRight, curveChartSpecialization_mk,
    seedChartSpecialization_polynomial, MvPolynomial.map_map]
  have hc : seedMap.comp (algebraMap ℂ ParameterAlgebra) = RingHom.id ℂ :=
    RingHom.ext CycleQ2IncidenceSeedFiber.seedMap_complex
  rw [hc, MvPolynomial.map_id]
  rfl

def dualEval : ChartPolynomial ℂ[ε] →+* FirstOrderCurveChart t i :=
  eval₂Hom (algebraMap ℂ[ε] (FirstOrderCurveChart t i)) (fun x => relativeEval t i (X x))

theorem dualEval_parameter (p : ChartPolynomial ParameterAlgebra) :
    dualEval t i (MvPolynomial.map firstOrderMap.toRingHom p) = relativeEval t i p := by
  have h : (dualEval t i).comp (MvPolynomial.map firstOrderMap.toRingHom) = relativeEval t i := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.map_C, dualEval, eval₂Hom_C]
      exact RingHom.congr_fun
        (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
          (R := ParameterAlgebra) (A := ℂ[ε]) (B := AffineCurveChart incidencePoint t i)) a
    · intro x
      simp [dualEval]
  exact RingHom.congr_fun h p

theorem dualEval_constant (p : ChartPolynomial ℂ) :
    dualEval t i (MvPolynomial.map (algebraMap ℂ ℂ[ε]) p) = chartMap t i p := by
  unfold chartMap
  rw [RingHom.comp_apply, ← dualEval_parameter, MvPolynomial.map_map]
  exact congrArg (fun f : ℂ →+* ℂ[ε] => dualEval t i (MvPolynomial.map f p))
    (RingHom.ext fun a => (firstOrderMap.commutes a).symm)

private theorem parameterEquation_zero (j : Fin 2) :
    relativeEval t i (dehomogenizedEquations incidencePoint i j) = 0 := by
  simp only [relativeEval, RingHom.comp_apply, dehomogenizedMap_equation, map_zero]

private theorem sextic_coefficients :
    MvPolynomial.map firstOrderMap.toRingHom (pointEquationF incidencePoint) =
      MvPolynomial.map (algebraMap ℂ ℂ[ε]) (pointEquationF seed) := by
  simp only [pointEquationF, pointMap_familyF, map_fullInvariantPolynomial]
  exact congrArg (fullInvariantPolynomial 6) (funext firstOrderIncidencePoint_sextic)

theorem cubic_coefficients :
    MvPolynomial.map firstOrderMap.toRingHom (pointEquationH incidencePoint) =
      MvPolynomial.map (algebraMap ℂ ℂ[ε]) (pointEquationH seed) +
        C ε * MvPolynomial.map (algebraMap ℂ ℂ[ε]) firstOrderWeightedCubic.val := by
  classical
  simp only [pointEquationH, pointMap_familyH, firstOrderWeightedCubic, map_fullInvariantPolynomial]
  simp only [fullInvariantPolynomial, Finset.mul_sum, C_mul_monomial, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← map_add]
  apply congrArg _
  change firstOrderIncidencePoint (Sum.inl j) = _
  apply TrivSqZeroExt.ext
  · simpa [TrivSqZeroExt.algebraMap_eq_inl, pointCubic, seed] using firstOrderIncidencePoint_seed (Sum.inl j)
  · simp [TrivSqZeroExt.algebraMap_eq_inl, pointCubic, firstOrderDirection, firstOrderIncidencePoint]

theorem chartMap_F : chartMap t i (seedF i) = 0 := by
  have h := parameterEquation_zero t i 0
  change relativeEval t i (dehomogenize i (pointEquationF incidencePoint)) = 0 at h
  rw [← dualEval_parameter, map_dehomogenize, sextic_coefficients, ← map_dehomogenize,
    dualEval_constant] at h
  exact h

theorem chartMap_H : chartMap t i (seedH i) =
    -(algebraMap ℂ[ε] (FirstOrderCurveChart t i) ε * chartMap t i (tangentL i)) := by
  have h := parameterEquation_zero t i 1
  change relativeEval t i (dehomogenize i (pointEquationH incidencePoint)) = 0 at h
  rw [← dualEval_parameter, map_dehomogenize, cubic_coefficients, map_add, map_mul,
    MvPolynomial.algHom_C, ← map_dehomogenize, ← map_dehomogenize, map_add, map_mul,
    dualEval_constant, dualEval_constant] at h
  change _ + dualEval t i (C ε) * _ = 0 at h
  rw [show dualEval t i (C ε) = _ from eval₂Hom_C _ _ _] at h
  exact eq_neg_of_add_eq_zero_left h

end CycleQ2LiteralAbelJacobiEquations

end

#print axioms CycleQ2LiteralAbelJacobiEquations.chartMap_reduction
#print axioms CycleQ2LiteralAbelJacobiEquations.chartMap_F
#print axioms CycleQ2LiteralAbelJacobiEquations.chartMap_H
