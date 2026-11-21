import Proposal.GeometricIncidenceFirstOrder
import Proposal.GeometricIncidenceCechTrace

/-!
# The actual pointed incidence tangent has a nonzero paired Cech class

The epsilon coefficient of the actual seed/time-derivation parameter
map retains the existing invertible trace after specialization. Its
cubic part is therefore not a rescaling of the original seed cubic.
The same two-entry trace is precisely the already computed derivative
trace on the literal r=57, theta=1 homogeneous Cech quotient. The existing
paired-class theorem then proves that the class of this actual pointed
cubic direction is nonzero.

This identifies a concrete nonzero homogeneous Cech class for the actual
parameter path. It does not identify that class with the Abel--Jacobi
derivative of the new Cartier curve, prove that curve nonempty, or infer
the protected affine residue exactness statement.

Source-only draft: no Lean elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric strategy and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2IncidenceFirstOrderTrace

open Matrix
open CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceUniversalChart CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceSeedFiber
  CycleQ2IncidenceTraceDirection CycleQ2IncidenceProjectiveTrace
  CycleQ2SegreModularDetectorMatrixBinding CycleQ2IncidenceCubicCechTrace
  CycleQ2IncidenceFirstOrder CycleQ2GeometricProjectiveCurve
  CycleQ2GeometricIncidenceCechTrace

def firstOrderDirection (j : ParameterIndex) : ℂ :=
  seedMap (timeDerivation (incidencePoint j))

theorem firstOrderDirection_eq_snd (j : ParameterIndex) :
    firstOrderDirection j = (firstOrderIncidencePoint j).snd := rfl

theorem firstOrderDirection_sextic (j : FullInvariantIndex 6) :
    firstOrderDirection (Sum.inr (Sum.inl j)) = 0 := by
  rw [firstOrderDirection, incidence_sextic_derivative_zero, map_zero]

/-- The existing relative trace unit remains a unit at the exact
retained seed under the exact retained coefficient specialization. -/
theorem firstOrderDirection_trace_isUnit :
    IsUnit (traceWeights ⬝ᵥ firstOrderDirection) := by
  have h := incidence_trace_derivative_isUnit.map seedMap
  simpa only [dotProduct, map_sum, map_mul, Function.comp_apply,
    seedMap_complex, firstOrderDirection] using h

theorem firstOrderDirection_cubic_not_rescaling :
    ¬ ∃ a : ℂ, ∀ j : FullInvariantIndex 3,
      firstOrderDirection (Sum.inl j) =
        a * seedPoint (57 : ℂ) Complex.I (Sum.inl j) := by
  rintro ⟨a, ha⟩
  have hz : traceWeights ⬝ᵥ firstOrderDirection =
      a * (traceWeights ⬝ᵥ seedPoint (57 : ℂ) Complex.I) := by
    simp only [traceWeights_formula, ha]
    ring
  rw [seed_trace_value, mul_zero] at hz
  exact firstOrderDirection_trace_isUnit.ne_zero hz

/-- The nine coefficients use the original checked cubic-column order. -/
def firstOrderCubicDirection (j : Fin 9) : ℂ :=
  firstOrderDirection (Sum.inl (cubicIndex j))

theorem firstOrder_trace_eq_derivativeTrace :
    traceWeights ⬝ᵥ firstOrderDirection =
      CycleQ2SeedCechTheta.derivativeTrace 1 firstOrderCubicDirection := by
  rw [traceWeights_formula, CycleQ2SeedCechTheta.smooth_derivativeTrace_explicit]
  rfl

theorem firstOrder_derivativeTrace_ne_zero :
    CycleQ2SeedCechTheta.derivativeTrace 1 firstOrderCubicDirection ≠ 0 := by
  rw [← firstOrder_trace_eq_derivativeTrace]
  exact firstOrderDirection_trace_isUnit.ne_zero

/-- This is the existing paired homogeneous Cech class on the same
literal curve, now evaluated at the actual pointed parameter tangent. -/
theorem firstOrder_pairedClass_ne_zero :
    pairedDegreeOneClass 57 1 firstOrderCubicDirection ≠ 0 := by
  intro h
  exact firstOrder_derivativeTrace_ne_zero
    ((pairedDegreeOneClass_eq_zero_iff_derivativeTrace_zero firstOrderCubicDirection).mp h)

#print axioms firstOrderDirection_trace_isUnit
#print axioms firstOrderDirection_cubic_not_rescaling
#print axioms firstOrder_derivativeTrace_ne_zero
#print axioms firstOrder_pairedClass_ne_zero

end CycleQ2IncidenceFirstOrderTrace
end
