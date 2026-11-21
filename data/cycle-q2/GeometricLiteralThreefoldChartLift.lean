import Proposal.GeometricLiteralThreefoldKodairaSpencer
import Proposal.GeometricLiteralAmbientChartJacobian
import Proposal.GeometricLiteralThreefoldResidueCoordinates

/-!
# Lifts of the test deformation across weight-one charts

Each entire affine chart of the fixed threefold admits a lift to the
deformation F − ε B*, by the unit ideal identity for the original four
partial derivatives. Normalizing a lifted point by any other invertible
weight-one coordinate preserves this same first-order equation.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldChartLift

open MvPolynomial CycleQ2GeometricLiteralDirection CycleQ2IncidenceDehomogenizedChart
  CycleQ2GeometricIncidenceProj CycleQ2LiteralAbelJacobiEquations
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAmbientChartJacobian
  CycleQ2LiteralThreefoldResidueCoordinates CycleQ2LiteralThreefoldKodairaSpencer

abbrev Jet (S : Type*) := TrivSqZeroExt S S
abbrev q (i : Fin 4) := Ideal.Quotient.mkₐ ℂ (fixedIdeal i)

theorem test_homogeneous : ambientTest.IsWeightedHomogeneous geometricWeight 6 := by
  exact ((isWeightedHomogeneous_X ℂ geometricWeight (2 : Fin 5)).mul
    ((isWeightedHomogeneous_X ℂ geometricWeight (3 : Fin 5)).pow 3)).mul
      (isWeightedHomogeneous_X ℂ geometricWeight (4 : Fin 5))

private theorem bezout (i : Fin 4) : ∃ c : Index → T i, ∑ j, c j * derivative i j = 1 :=
  Ideal.mem_span_range_iff_exists_fun.mp
    ((Ideal.eq_top_iff_one _).mp (derivatives_span_top i))

/-- A single lift of the normal test on the entire affine chart. -/
def chartDerivative (i : Fin 4) : Derivation ℂ P (T i) :=
  ∑ j, ((q i (test i)) * (bezout i).choose j) •
    ((Algebra.ofId P (T i)).toLinearMap.compDer (pderiv j))

theorem chartDerivative_on_F (i : Fin 4) : chartDerivative i (seedF i) = q i (test i) := by
  let ds := fun j : Index => (q i (test i) * (bezout i).choose j) •
    ((Algebra.ofId P (T i)).toLinearMap.compDer (pderiv j))
  have hs : (∑ j, ds j) (seedF i) = ∑ j, ds j (seedF i) := by
    simpa only [Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply] using
      congrFun (map_sum Derivation.coeFnAddMonoidHom ds Finset.univ) (seedF i)
  rw [show chartDerivative i = ∑ j, ds j by rfl, hs]
  change ∑ j, (q i (test i) * (bezout i).choose j) * derivative i j = _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, (bezout i).choose_spec, mul_one]

variable {S : Type*} [CommRing S] [Algebra ℂ S]

/-- First-order affine coordinates satisfying the original deformed equation. -/
structure Lift (i : Fin 4) (S : Type*) [CommRing S] [Algebra ℂ S] where
  x : Index → Jet S
  equation : aeval x (seedF i) = (TrivSqZeroExt.inr 1 : Jet S) * aeval x (test i)

private def chartTaylor (i : Fin 4) (f : T i →ₐ[ℂ] S) : P →ₐ[ℂ] Jet S where
  toFun p := (f (q i p), f (chartDerivative i p))
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' p r := by apply TrivSqZeroExt.ext <;> simp
  map_mul' p r := by
    apply TrivSqZeroExt.ext
    · simp
    · change f (chartDerivative i (p*r)) = f (q i p) * f (chartDerivative i r) +
        f (chartDerivative i p) * f (q i r)
      rw [Derivation.leibniz]
      change f (q i p * chartDerivative i r + q i r * chartDerivative i p) = _
      simp [mul_comm]
  commutes' c := by
    apply TrivSqZeroExt.ext
    · change f (q i (algebraMap ℂ P c)) = algebraMap ℂ S c
      rw [AlgHom.commutes, AlgHom.commutes]
    · change f (chartDerivative i (algebraMap ℂ P c)) = 0
      rw [Derivation.map_algebraMap, map_zero]

private theorem aeval_chartTaylor (i : Fin 4) (f : T i →ₐ[ℂ] S) :
    aeval (fun a => chartTaylor i f (X a)) = chartTaylor i f := by
  apply MvPolynomial.algHom_ext
  intro a
  rw [aeval_X]

/-- The point of the actual deformation lifting any point of the fixed affine chart. -/
def canonical (i : Fin 4) (f : T i →ₐ[ℂ] S) : Lift i S where
  x a := chartTaylor i f (X a)
  equation := by
    rw [aeval_chartTaylor]
    apply TrivSqZeroExt.ext
    · change f (q i (seedF i)) = 0 * _
      rw [zero_mul, show q i (seedF i) = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_singleton _)), map_zero]
    · change f (chartDerivative i (seedF i)) = 0 * _ + 1 * f (q i (test i))
      rw [chartDerivative_on_F, zero_mul, one_mul, zero_add]

@[simp] theorem canonical_fst (i : Fin 4) (f : T i →ₐ[ℂ] S) (a : Index) :
    ((canonical i f).x a).fst = f (q i (X a)) := rfl

/-- Change to the target chart by the inverse of its actual lifted coordinate. -/
def change {i : Fin 4} (x : Lift i S) (j : Fin 4) (u : Jet S)
    (hu : u * linearValues i x.x j = 1) : Lift j S where
  x := changedCoordinate i j x.x u
  equation := by
    rw [show aeval (changedCoordinate i j x.x u) (seedF j) =
      u^6 * aeval x.x (seedF i) from seedF_change i j x.x u hu,
      x.equation, show aeval (changedCoordinate i j x.x u) (test j) =
      u^6 * aeval x.x (test i) from homogeneous_change i j x.x u hu ambientTest test_homogeneous]
    ring

end CycleQ2LiteralThreefoldChartLift
end

#print axioms CycleQ2LiteralThreefoldChartLift.chartDerivative_on_F
#print axioms CycleQ2LiteralThreefoldChartLift.canonical
#print axioms CycleQ2LiteralThreefoldChartLift.change
