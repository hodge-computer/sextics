import Proposal.GeometricGenericWeightedCoordinates

/-!
# Divergence in weighted coordinates on the generic pencil

The weighted radial coordinate is the square of the affine coordinate `u`.
The transfer multiplies the relative divergence and the contraction with the
differential of any density by the ratio of the two affine coordinates.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
noncomputable section

namespace CycleQ2GenericWeightedDivergence

open CycleQ2GenericSpecialization CycleQ2GenericWeightedCoordinates
open scoped BigOperators

/-- The four generic pencil coefficients corresponding to three weighted
relative coefficients. -/
def transferVector (w : Fin 3 → RF) : Fin 4 → RF :=
  ![lambda * w 2 / (2 * u), lambda * w 0, lambda * w 1, lambda ^ 2 * w 2 / (2 * u)]

@[simp] theorem transferVector_zero (w : Fin 3 → RF) :
    transferVector w 0 = lambda * w 2 / (2 * u) := rfl

@[simp] theorem transferVector_one (w : Fin 3 → RF) :
    transferVector w 1 = lambda * w 0 := rfl

@[simp] theorem transferVector_two (w : Fin 3 → RF) :
    transferVector w 2 = lambda * w 1 := rfl

@[simp] theorem transferVector_three (w : Fin 3 → RF) :
    transferVector w 3 = lambda ^ 2 * w 2 / (2 * u) := rfl

set_option maxHeartbeats 1000000 in
/-- The derivatives of the coordinate coefficients cancel in the divergence. -/
theorem transferred_divergence (d : Direction) (w : Fin 3 → RF) :
    (∑ i, tangent d i (transferVector w i)) =
      lambda * ∑ j, relativeDerivation d j (w j) := by
  change (∑ i, E d i (transferVector w i)) = _
  rw [Fin.sum_univ_four, Fin.sum_univ_three]
  simp only [transferVector_zero, transferVector_one, transferVector_two, transferVector_three,
    relativeDerivation_zero, relativeDerivation_one, relativeDerivation_two,
    Derivation.leibniz_div, Derivation.leibniz, Derivation.leibniz_pow,
    E_lambda_zero, E_lambda_one, E_lambda_two, E_lambda_three, E_two, E_u,
    smul_eq_mul, nsmul_eq_mul, Fin.reduceEq, if_true, if_false, Nat.cast_ofNat,
    Nat.reduceSub, pow_one]
  field_simp [u_ne_zero]
  ring

/-- Contraction with the differential of any rational density transforms by
the same factor as the ordinary divergence. -/
theorem contract_factor (d : Direction) (ρ : RF) (w : Fin 3 → RF) :
    (∑ i, transferVector w i * tangent d i ρ) =
      lambda * ∑ j, w j * relativeDerivation d j ρ := by
  change (∑ i, transferVector w i * E d i ρ) = _
  rw [Fin.sum_univ_four, Fin.sum_univ_three]
  simp only [transferVector_zero, transferVector_one, transferVector_two, transferVector_three,
    relativeDerivation_zero, relativeDerivation_one, relativeDerivation_two]
  ring

/-- The density-corrected divergence scales by the same factor. -/
theorem transferred_density_divergence (d : Direction) (ρ : RF) (w : Fin 3 → RF) :
    (∑ i, tangent d i (transferVector w i)) - (∑ i, transferVector w i * tangent d i ρ) / ρ =
      lambda * ((∑ j, relativeDerivation d j (w j)) -
        (∑ j, w j * relativeDerivation d j ρ) / ρ) := by
  rw [transferred_divergence, contract_factor]
  ring

end CycleQ2GenericWeightedDivergence

end

#print axioms CycleQ2GenericWeightedDivergence.transferred_divergence
#print axioms CycleQ2GenericWeightedDivergence.contract_factor
#print axioms CycleQ2GenericWeightedDivergence.transferred_density_divergence
