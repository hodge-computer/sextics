import Proposal.GeometricFormalInputs04
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.Perfect

/-!
# The pencil parameter in the protected affine function field

The fourth coordinate derivation sends the quotient Y₂/X₂ to 1/X₂.
It follows that this quotient is transcendental over ℂ. Evaluation therefore
embeds the rational function field of the pencil into the protected function
field. The three relative directions kill its entire image.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
noncomputable section

namespace CycleQ2ProtectedPencilParameter

open CycleQ2AffineWeightedTransfer Polynomial

/-- A separable minimal polynomial would force the fourth partial to vanish. -/
theorem parameter_transcendental : Transcendental ℂ parameter := by
  intro h
  have hd := (minpoly.irreducible h.isIntegral).separable.aeval_derivative_ne_zero
    (minpoly.aeval ℂ parameter)
  have hD := congrArg (E 3) (minpoly.aeval ℂ parameter)
  rw [Derivation.map_aeval, map_zero, smul_eq_mul, E_parameter_three] at hD
  exact (mul_ne_zero hd (div_ne_zero one_ne_zero u_ne_zero)) hD

theorem polynomialEvaluation_injective :
    Function.Injective (Polynomial.aeval parameter : Polynomial ℂ →ₐ[ℂ] K) :=
  transcendental_iff_injective.mp parameter_transcendental

/-- Evaluation of the pencil coefficients at the original quotient Y₂/X₂. -/
def evaluation : RatFunc ℂ →ₐ[ℂ] K :=
  RatFunc.liftAlgHom (Polynomial.aeval parameter)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ polynomialEvaluation_injective)

/-- The scalar action of the pencil's function field on the protected affine field. -/
def pencilAlgebra : Algebra (RatFunc ℂ) K := evaluation.toRingHom.toAlgebra

theorem evaluation_injective : Function.Injective evaluation := evaluation.injective

@[simp] theorem evaluation_polynomial (p : Polynomial ℂ) :
    evaluation (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) = Polynomial.aeval parameter p :=
  RatFunc.liftRingHom_algebraMap _ _ p

@[simp] theorem evaluation_X : evaluation RatFunc.X = parameter :=
  (evaluation_polynomial Polynomial.X).trans (Polynomial.aeval_X _)

theorem relativeDerivation_evaluation (j : Fin 3) (r : RatFunc ℂ) :
    relativeDerivation j (evaluation r) = 0 := by
  rw [← RatFunc.num_div_denom r, map_div₀, evaluation_polynomial, evaluation_polynomial,
    Derivation.leibniz_div, Derivation.map_aeval, Derivation.map_aeval, relative_parameter]
  simp

end CycleQ2ProtectedPencilParameter
end

#print axioms CycleQ2ProtectedPencilParameter.parameter_transcendental
#print axioms CycleQ2ProtectedPencilParameter.evaluation_X
#print axioms CycleQ2ProtectedPencilParameter.relativeDerivation_evaluation
