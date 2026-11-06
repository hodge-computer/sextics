import Mathlib.Tactic.Ring

/-! Extracted from `benediamond`’s accepted two-ternary dense Hessian
construction. The application and its mathematical credit are linked in README.md. -/


/-! # Division-free cubic covariants used by the explicit scalar formula

These are evaluated at U=1 after homogenizing the coefficients. In particular
f is a+b+c+d, and the prime fields are derivatives with respect to U at 1.
-/
set_option autoImplicit false
noncomputable section
namespace HodgeTestbed.EllipticAmbient.Cubic

variable {R : Type*} [CommRing R]
structure Data (R : Type*) where
  a : R
  b : R
  c : R
  d : R

def f (v : Data R) : R := v.a + v.b + v.c + v.d
def fp (v : Data R) : R := 3*v.a + 2*v.b + v.c
def h4 (v : Data R) : R := v.b^2 - 3*v.a*v.c
def h6 (v : Data R) : R := v.b*v.c - 9*v.a*v.d
def h0 (v : Data R) : R := v.c^2 - 3*v.b*v.d
def H (v : Data R) : R := h4 v + h6 v + h0 v
def Hp (v : Data R) : R := 2*h4 v + h6 v
def delta (v : Data R) : R :=
  v.b^2*v.c^2 - 4*v.a*v.c^3 - 4*v.b^3*v.d - 27*v.a^2*v.d^2 + 18*v.a*v.b*v.c*v.d
def t (v : Data R) : R := 3*Hp v*f v - 2*H v*fp v
def tp (v : Data R) : R :=
  6*h4 v*f v + Hp v*fp v - 2*H v*(6*v.a+2*v.b)
def kp (v : Data R) : R := v.b*v.c^2 - 6*v.b^2*v.d + 9*v.a*v.c*v.d
def k (v : Data R) : R := kp v + 2*v.c^3 - 9*v.b*v.c*v.d + 27*v.a*v.d^2
def l (v : Data R) : R := v.b + 2*v.c + 3*v.d
def lp (v : Data R) : R := 3*v.b + 4*v.c + 3*v.d

def mix (v : Data R) : R :=
  -2*H v^2 - 7*H v*fp v*l v + 3*H v*lp v*f v + 6*Hp v*l v*f v
def pkExpression (v : Data R) : R :=
  -5*H v*fp v*k v - 3*H v*kp v*f v + 9*Hp v*k v*f v

/-- Exact discriminant syzygy, including its factor 27. -/
theorem t_square (v : Data R) : t v^2 = 4*H v^3 - 27*delta v*f v^2 := by
  simp only [t, Hp, H, h4, h6, h0, fp, f, delta]
  ring

theorem k_H (v : Data R) : k v*H v + h0 v*t v = 3*delta v*l v := by
  simp only [k, kp, H, h4, h6, h0, t, Hp, fp, f, delta, l]
  ring

theorem k_derivative_identity (v : Data R) :
    fp v*k v - 3*f v*kp v = 2*h0 v*H v - 3*delta v := by
  simp only [k, kp, H, h4, h6, h0, fp, f, delta]
  ring

theorem l_derivative_identity (v : Data R) :
    H v^2 + H v*fp v*l v - 3*H v*lp v*f v + 3*Hp v*l v*f v =
      -9*h0 v*f v^2 := by
  simp only [H, h4, h6, h0, fp, f, Hp, l, lp]
  ring

theorem t_derivative_minus (v : Data R) :
    H v*fp v*t v + 3*H v*f v*tp v - 6*Hp v*f v*t v =
      -2*H v^3 + 54*delta v*f v^2 := by
  simp only [t, tp, H, h4, h6, h0, fp, f, Hp, delta]
  ring

theorem t_derivative_plus (v : Data R) :
    -5*H v*fp v*t v + 3*H v*f v*tp v + 3*Hp v*f v*t v =
      10*H v^3 - 27*delta v*f v^2 := by
  simp only [t, tp, H, h4, h6, h0, fp, f, Hp, delta]
  ring

/-- The compact mixed identity that cancels the remaining P/Q cross term. -/
theorem mixed_bridge (v : Data R) :
    H v*(10*h0 v*H v^2 + pkExpression v) =
      delta v*(3*mix v + 54*h0 v*f v^2) := by
  simp only [pkExpression, mix, k, kp, H, h4, h6, h0, fp, f, Hp, l, lp, delta]
  ring

end HodgeTestbed.EllipticAmbient.Cubic
