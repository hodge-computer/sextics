import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.NormNum
import HodgeComputer.Constructions.BinaryCubic.RadialIdentity

/-! Extracted from `benediamond`’s accepted two-ternary dense Hessian
construction. The application and its mathematical credit are linked in README.md. -/


/-! # Actual derivation rules for homogeneous coefficient blocks -/
set_option autoImplicit false
noncomputable section
namespace HodgeTestbed.EllipticAmbient.Cubic
variable {R : Type*} [CommRing R] [Algebra ℚ R]

@[simp] theorem deriv_ofNat (D : Derivation ℚ R R) (n : ℕ) [n.AtLeastTwo] :
    D (OfNat.ofNat n : R) = 0 := D.map_natCast n

/-- Radial weights of the coefficient blocks (a,b,c,d). -/
structure Weights (D : Derivation ℚ R R) (v : Data R) : Prop where
  a : D v.a = 0
  b : D v.b = 2*v.b
  c : D v.c = 4*v.c
  d : D v.d = 6*v.d

/-- All actual radial derivative values needed by the scalar cancellation. -/
theorem weighted_derivatives (D : Derivation ℚ R R) (v : Data R) (hw : Weights D v) :
    D (f v) = rf v ∧ D (H v) = rH v ∧ D (delta v) = 12*delta v ∧
    D (h0 v) = 8*h0 v ∧ D (t v) = rt v ∧ D (k v) = rk v ∧ D (l v) = rl v := by
  have ha := hw.a
  have hb := hw.b
  have hc := hw.c
  have hd := hw.d
  simp only [f, H, delta, h0, t, k, l, h4, h6, Hp, fp, kp, tp, lp,
    rf, rH, rt, rk, rl, map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow,
    smul_eq_mul, deriv_ofNat D 2, deriv_ofNat D 3, deriv_ofNat D 4, deriv_ofNat D 6, deriv_ofNat D 9, deriv_ofNat D 18, deriv_ofNat D 27, ha, hb, hc, hd]
  norm_num
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- A derivation annihilating all four coefficient blocks annihilates their covariants. -/
theorem constant_derivatives (D : Derivation ℚ R R) (v : Data R)
    (ha : D v.a = 0) (hb : D v.b = 0) (hc : D v.c = 0) (hd : D v.d = 0) :
    D (f v) = 0 ∧ D (H v) = 0 ∧ D (delta v) = 0 ∧ D (h0 v) = 0 ∧
    D (t v) = 0 ∧ D (k v) = 0 ∧ D (l v) = 0 := by
  simp [f, H, delta, h0, t, k, l, h4, h6, Hp, fp, kp, ha, hb, hc, hd,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, deriv_ofNat D 2, deriv_ofNat D 3, deriv_ofNat D 4, deriv_ofNat D 6, deriv_ofNat D 9, deriv_ofNat D 18, deriv_ofNat D 27]

end HodgeTestbed.EllipticAmbient.Cubic
