import Proposal.ProtectedResidueSpecialization

/-!
# Relative weighted coordinates on the generic pencil

On the affine chart the weighted coordinates are the two independent coordinates
`z 2` and `z 3` and the square of `u = z 1`. The ratio `z 4 / u` and the pencil
parameter are constant for each of the three corresponding derivations.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace CycleQ2GenericWeightedCoordinates

open MvPolynomial CycleQ2Bridge CycleQ2GenericSpecialization

def z (i : Fin 5) : RF := polynomialMap 4 (X i)
def u : RF := z 1
def v : RF := z 4
def lambda : RF := v / u

theorem z_ne_zero (i : Fin 5) : z i ≠ 0 :=
  polynomialMap_ne_zero (X_ne_zero i)

theorem u_ne_zero : u ≠ 0 := z_ne_zero 1
theorem v_ne_zero : v ≠ 0 := z_ne_zero 4
theorem lambda_ne_zero : lambda ≠ 0 := div_ne_zero v_ne_zero u_ne_zero

theorem lambda_mul_u : lambda * u = v := div_mul_cancel₀ v u_ne_zero

abbrev E (d : Direction) (i : Fin 4) := tangent d i

theorem E_coordinate (d : Direction) (i j : Fin 4) :
    E d i (z j.succ) = if j = i then 1 else 0 := by
  rw [tangent_apply]
  simp [z, pderiv_X, Pi.single_apply, Fin.succ_ne_zero]

theorem E_normalCoordinate (d : Direction) (i : Fin 4) :
    E d i (z 0) = -familyPartial d i.succ / familyPartial d 0 := by
  rw [tangent_apply]
  simp [z, pderiv_X, Fin.succ_ne_zero, div_eq_mul_inv]

@[simp] theorem E_u (d : Direction) (i : Fin 4) :
    E d i u = if i = 0 then 1 else 0 := by
  simpa [u, eq_comm] using E_coordinate d i 0

@[simp] theorem E_v (d : Direction) (i : Fin 4) :
    E d i v = if i = 3 then 1 else 0 := by
  simpa [v, eq_comm] using E_coordinate d i 3

@[simp] theorem E_two (d : Direction) (i : Fin 4) :
    E d i (2 : RF) = 0 := (E d i).map_natCast 2

@[simp] theorem E_lambda_zero (d : Direction) : E d 0 lambda = -lambda / u := by
  rw [lambda, Derivation.leibniz_div]
  simp only [E_u, E_v, Fin.reduceEq, if_false, if_true, smul_eq_mul, mul_zero,
    zero_sub, mul_one]
  ring

@[simp] theorem E_lambda_one (d : Direction) : E d 1 lambda = 0 := by
  rw [lambda, Derivation.leibniz_div]
  simp only [E_u, E_v, Fin.reduceEq, if_false, smul_eq_mul, mul_zero, sub_self]

@[simp] theorem E_lambda_two (d : Direction) : E d 2 lambda = 0 := by
  rw [lambda, Derivation.leibniz_div]
  simp only [E_u, E_v, Fin.reduceEq, if_false, smul_eq_mul, mul_zero, sub_self]

@[simp] theorem E_lambda_three (d : Direction) : E d 3 lambda = 1 / u := by
  rw [lambda, Derivation.leibniz_div]
  simp only [E_u, E_v, Fin.reduceEq, if_false, if_true, smul_eq_mul, mul_zero,
    sub_zero, mul_one]
  field_simp [u_ne_zero]

/-- Differentiate with respect to the two weight-one coordinates and to the square of `u`. -/
def relativeDerivation (d : Direction) : Fin 3 → Derivation ℂ RF RF :=
  ![E d 1, E d 2, (2 * u)⁻¹ • (E d 0 + lambda • E d 3)]

@[simp] theorem relativeDerivation_zero (d : Direction) (x : RF) :
    relativeDerivation d 0 x = E d 1 x := rfl

@[simp] theorem relativeDerivation_one (d : Direction) (x : RF) :
    relativeDerivation d 1 x = E d 2 x := rfl

@[simp] theorem relativeDerivation_two (d : Direction) (x : RF) :
    relativeDerivation d 2 x = (E d 0 x + lambda * E d 3 x) / (2 * u) := by
  change ((2 * u)⁻¹ • (E d 0 + lambda • E d 3)) x = _
  simp only [Derivation.smul_apply, Derivation.add_apply, smul_eq_mul]
  ring

theorem relative_lambda (d : Direction) (j : Fin 3) :
    relativeDerivation d j lambda = 0 := by
  fin_cases j
  · exact E_lambda_one d
  · exact E_lambda_two d
  · change relativeDerivation d 2 lambda = 0
    rw [relativeDerivation_two, E_lambda_zero, E_lambda_three]
    ring

theorem relative_tau (d : Direction) (j : Fin 3) :
    relativeDerivation d j (parameter d) = 0 := by
  fin_cases j
  · exact tangent_parameter d 1
  · exact tangent_parameter d 2
  · change relativeDerivation d 2 (parameter d) = 0
    simp only [relativeDerivation_two, E, tangent_parameter, mul_zero, add_zero, zero_div]

theorem radial_divergence (d : Direction) :
    E d 0 (1 / (2 * u)) + E d 3 (lambda / (2 * u)) = 0 := by
  simp only [Derivation.leibniz_div, Derivation.leibniz, Derivation.map_one_eq_zero,
    E_two, E_u, E_lambda_three, smul_eq_mul, Fin.reduceEq, if_false, if_true,
    mul_zero, add_zero, mul_one]
  field_simp [u_ne_zero]
  ring

/-- The three independent coordinates with fixed pencil and ratio parameters. -/
def relativeCoordinate : Fin 3 → RF := ![z 2, z 3, u ^ 2]

theorem relativeDerivation_coordinate (d : Direction) (i j : Fin 3) :
    relativeDerivation d i (relativeCoordinate j) = if i = j then 1 else 0 := by
  have h₂ (k : Fin 4) : E d k (z 2) = if (1 : Fin 4) = k then 1 else 0 :=
    E_coordinate d k 1
  have h₃ (k : Fin 4) : E d k (z 3) = if (2 : Fin 4) = k then 1 else 0 :=
    E_coordinate d k 2
  have h₄ (k : Fin 4) : E d k (u ^ 2) = (2 * u) * (if k = 0 then 1 else 0) := by
    rw [pow_two, Derivation.leibniz, E_u, smul_eq_mul]
    ring
  fin_cases i <;> fin_cases j
  · exact (h₂ 1).trans (if_pos rfl)
  · exact (h₃ 1).trans (if_neg (by decide))
  · change E d 1 (u ^ 2) = 0
    norm_num [h₄]
  · exact (h₂ 2).trans (if_neg (by decide))
  · exact (h₃ 2).trans (if_pos rfl)
  · change E d 2 (u ^ 2) = 0
    rw [h₄, if_neg (by decide : (2 : Fin 4) ≠ 0), mul_zero]
  · change relativeDerivation d 2 (z 2) = 0
    rw [relativeDerivation_two, h₂, h₂, if_neg (by decide : (1 : Fin 4) ≠ 0),
      if_neg (by decide : (1 : Fin 4) ≠ 3), mul_zero, add_zero, zero_div]
  · change relativeDerivation d 2 (z 3) = 0
    rw [relativeDerivation_two, h₃, h₃, if_neg (by decide : (2 : Fin 4) ≠ 0),
      if_neg (by decide : (2 : Fin 4) ≠ 3), mul_zero, add_zero, zero_div]
  · change relativeDerivation d 2 (u ^ 2) = 1
    rw [relativeDerivation_two, h₄, h₄, if_pos rfl, if_neg (by decide : (3 : Fin 4) ≠ 0),
      mul_one, mul_zero, mul_zero, add_zero, div_self (mul_ne_zero (by norm_num) u_ne_zero)]

private theorem E_commutes_radial (d : Direction) (i : Fin 4)
    (hu : E d i u = 0) (hl : E d i lambda = 0) :
    Function.Commute (E d i) (relativeDerivation d 2) := by
  intro x
  rw [relativeDerivation_two, relativeDerivation_two]
  have h₂u : E d i (2 * u) = 0 := by
    simp only [Derivation.leibniz, hu, E_two, smul_zero, add_zero]
  rw [Derivation.leibniz_div_const _ _ _ h₂u, map_add, Derivation.leibniz, hl]
  simp only [smul_eq_mul, mul_zero, add_zero]
  rw [tangents_commute d i 0 x, tangents_commute d i 3 x]
  ring

theorem relativeDerivations_commute (d : Direction) (i j : Fin 3) :
    Function.Commute (relativeDerivation d i) (relativeDerivation d j) := by
  have ha := E_commutes_radial d 1 (by simp) (by simp)
  have hb := E_commutes_radial d 2 (by simp) (by simp)
  fin_cases i <;> fin_cases j
  · exact fun _ => rfl
  · exact tangents_commute d 1 2
  · exact ha
  · exact (tangents_commute d 1 2).symm
  · exact fun _ => rfl
  · exact hb
  · exact ha.symm
  · exact hb.symm
  · exact fun _ => rfl

end CycleQ2GenericWeightedCoordinates

end

#print axioms CycleQ2GenericWeightedCoordinates.relative_lambda
#print axioms CycleQ2GenericWeightedCoordinates.relative_tau
#print axioms CycleQ2GenericWeightedCoordinates.radial_divergence
#print axioms CycleQ2GenericWeightedCoordinates.relativeDerivation_coordinate
#print axioms CycleQ2GenericWeightedCoordinates.relativeDerivations_commute
