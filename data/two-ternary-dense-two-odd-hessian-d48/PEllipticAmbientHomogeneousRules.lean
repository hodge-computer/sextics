import Proposal.PEllipticAmbientHomogeneousMap

/-! # All derivative premises for the actual split-to-homogeneous chart -/
set_option autoImplicit false
noncomputable section
namespace HodgeTestbed.EllipticAmbient
open HodgeTestbed.FrozenChart HodgeTestbed.Conic

theorem physicalEuler_coord (j : Fin 5) :
    fieldAction physicalPartial physicalCoordinates (coord j) =
      (![coord 0, coord 1, 0, 0, lambda] : Fin 5 → K) j := by
  fin_cases j <;>
    norm_num [fieldAction_apply, Fin.sum_univ_succ, physicalPartial, physicalCoordinates,
      Matrix.cons_val_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, sub_apply, smul_apply,
      smul_eq_mul, partial_coord, lambda, Fin.ext_iff]
  all_goals field_simp [coord_ne_zero (4 : Fin 5)]
  all_goals ring

theorem homSplit_succ (i : Fin 5) (f : K) :
    rationalPartial i.succ (homSplit f) = (coord (0 : Fin 6))⁻¹ * homSplit (physicalPartial i f) := by
  apply compatibility_of_coordinates homSplit (rationalPartial i.succ) (physicalPartial i)
    ((coord (0 : Fin 6))⁻¹)
  intro j
  fin_cases i <;> fin_cases j <;>
    norm_num [homSplit_coord, homCoordinates, physicalPartial, basePartial, normalPartial,
      sub_apply, smul_apply, Derivation.leibniz_div,
      smul_eq_mul, partial_coord, lambda, Matrix.cons_val_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Fin.ext_iff, map_mul, map_div₀]
  all_goals field_simp [coord_ne_zero (0 : Fin 6), coord_ne_zero (4 : Fin 6)]
  all_goals ring

theorem homSplit_zero (f : K) : rationalPartial 0 (homSplit f) =
    -(coord (0 : Fin 6))⁻¹ * homSplit (fieldAction physicalPartial physicalCoordinates f) := by
  apply compatibility_of_coordinates homSplit (rationalPartial 0)
    (fieldAction physicalPartial physicalCoordinates) (-(coord (0 : Fin 6))⁻¹)
  intro j
  rw [physicalEuler_coord]
  fin_cases j <;>
    norm_num [homSplit_coord, homCoordinates, Derivation.leibniz_div, smul_eq_mul,
      partial_coord, lambda, Matrix.cons_val_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Fin.ext_iff]
  all_goals field_simp [coord_ne_zero (0 : Fin 6), coord_ne_zero (4 : Fin 6)]
  all_goals ring

theorem actual_split_homogeneousChart : HomogeneousChart physicalPartial
    (rationalPartial (n := 6)) homSplit.toRingHom (coord 0) physicalCoordinates where
  a_ne_zero := coord_ne_zero 0
  a_zero := by simp
  a_succ := by intro i; simp
  map_zero := homSplit_zero
  map_succ := homSplit_succ
  coordinate_diagonal := by intro i; simpa using physicalPartial_coordinates i i

theorem frozen_F_homSplit : embed Frozen.F = coord (0 : Fin 6)^6 * homSplit splitF := by
  rw [splitF, p_formula, q_formula]
  simp only [Frozen.F, Frozen.X0, Frozen.X1, Frozen.X2, Frozen.Y0, Frozen.Y1, Frozen.Y2,
    Incidence.P, Incidence.Q, map_mul, map_add, map_pow, map_ofNat, map_one,
    embed_X, lambda, homSplit_coord]
  norm_num [homCoordinates, Matrix.cons_val_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  field_simp [coord_ne_zero (0 : Fin 6), coord_ne_zero (4 : Fin 6)]
  <;> ring

theorem frozen_A_homSplit : embed Frozen.A = coord (0 : Fin 6)^6 * homSplit lambda := by
  simp only [Frozen.A, Frozen.X0, Frozen.Y1, map_mul, map_pow, embed_X, lambda, homSplit_coord]
  norm_num [homCoordinates, Matrix.cons_val_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  field_simp [coord_ne_zero (0 : Fin 6)]
  <;> ring

end HodgeTestbed.EllipticAmbient
