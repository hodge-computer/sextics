import Proposal.PFrozenChartChartMap
import HodgeComputer.Constructions.RationalFields.Homogenization

/-! # Proved X0-chart partial-derivative premises -/
set_option autoImplicit false
noncomputable section
namespace HodgeTestbed.FrozenChart

/-- The affine Euler action on each genuine rational coordinate. -/
theorem affineEuler_coord (j : Fin 5) :
    Conic.fieldAction rationalPartial (coord (n := 5)) (coord j) = coord j := by
  simp [Conic.fieldAction_apply, partial_coord]

/-- The actual X0 derivative of every pulled-back rational function. -/
theorem chart_zero (z : RatFun 5) :
    rationalPartial 0 (chart z) = -(coord (0 : Fin 6))⁻¹ *
      chart (Conic.fieldAction rationalPartial coord z) := by
  apply compatibility_of_coordinates chart (rationalPartial 0)
    (Conic.fieldAction rationalPartial coord) (-(coord (0 : Fin 6))⁻¹)
  intro j
  rw [affineEuler_coord, chart_coord]
  have hj0 : (0 : Fin 6) ≠ j.succ := Ne.symm (Fin.succ_ne_zero j)
  simp [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv,
    partial_coord, smul_eq_mul, hj0]
  ring

/-- Each remaining physical partial obeys the genuine rational chart chain rule. -/
theorem chart_succ (i : Fin 5) (z : RatFun 5) :
    rationalPartial i.succ (chart z) = (coord (0 : Fin 6))⁻¹ * chart (rationalPartial i z) := by
  apply compatibility_of_coordinates chart (rationalPartial i.succ)
    (rationalPartial i) ((coord (0 : Fin 6))⁻¹)
  intro j
  rw [chart_coord, partial_coord]
  simp only [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv,
    partial_coord, smul_eq_mul]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij, Fin.succ_inj]

/-- Every field of HomogeneousChart is discharged for the actual QQ fraction fields. -/
theorem actual_homogeneousChart :
    Conic.HomogeneousChart (rationalPartial (n := 5)) (rationalPartial (n := 6))
      chart.toRingHom (coord 0) coord where
  a_ne_zero := coord_ne_zero 0
  a_zero := by simp
  a_succ := by intro i; simp
  map_zero := chart_zero
  map_succ := chart_succ
  coordinate_diagonal := by intro i; simp

end HodgeTestbed.FrozenChart
