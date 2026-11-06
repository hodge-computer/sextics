import HodgeComputer.Constructions.BinaryCubic.Covariants

/-! Extracted from `benediamond`’s accepted two-ternary dense Hessian
construction. The application and its mathematical credit are linked in README.md. -/


/-! # Factored universal cancellation for the supplied radial scalar formula -/
set_option autoImplicit false
noncomputable section
namespace HodgeTestbed.EllipticAmbient.Cubic
variable {R : Type*} [CommRing R]

def rf (v : Data R) : R := 6*f v - 2*fp v
def rH (v : Data R) : R := 8*H v - 2*Hp v
def rt (v : Data R) : R := 12*t v - 2*tp v
def rk (v : Data R) : R := 12*k v - 2*kp v
def rl (v : Data R) : R := 8*l v - 2*lp v

def G (v w : Data R) : R := H v^3*delta w*f w^2 - H w^3*delta v*f v^2
def U (v w : Data R) : R := h0 v*H v*H w*t w*f v*f w
def V (v w : Data R) : R := k v*H w^3*f v^2 - 3*delta w*f w^2*H v^2*l v

def dPG (v w : Data R) : R :=
  3*H v^2*rH v*delta w*f w^2 - H w^3*delta v*(12*f v^2+2*f v*rf v)
def dQG (v w : Data R) : R :=
  H v^3*delta w*(12*f w^2+2*f w*rf w) - 3*H w^2*rH w*delta v*f v^2
def dPV (v w : Data R) : R :=
  rk v*H w^3*f v^2 + k v*H w^3*(2*f v*rf v) -
  3*delta w*f w^2*(2*H v*rH v*l v+H v^2*rl v)
def dQU (v w : Data R) : R :=
  h0 v*H v*f v*(rH w*t w*f w+H w*rt w*f w+H w*t w*rf w)

/-- This is the cleared scalar operator after the two actual radial derivative rules. -/
def radialScalar (v w : Data R) : R :=
  3*f v*f w*((2*G v w)*(rf v*V v w+f v*dPV v w+2*f v*V v w-f v*dQU v w-2*f v*U v w) -
    f v*V v w*(2*dPG v w)+f v*U v w*(2*dQG v w)) -
  4*f w*(2*G v w)*f v*V v w*rf v +
  2*f v*(2*G v w)*f v*U v w*rf w - 3*f v*f w*(2*G v w)^2

/-- Universal cancellation uses small cubic identities, rather than expanding the
large concrete x,y,r,z polynomial. No scalar-solution premise is supplied. -/
theorem radial_scalar_identity (v w : Data R) : radialScalar v w = 0 := by
  have he : radialScalar v w = 4*f v*f w*(
      -3*H w^6*f v^4*delta v^2 -
      3*H v*H w^3*f v^2*f w^2*delta v*delta w*mix v +
      H w^3*f v^4*delta v*(-H v*h0 v*(H w*fp w*t w+3*H w*f w*tp w-6*Hp w*f w*t w) -
        H w^3*(fp v*k v-3*f v*kp v)) -
      3*H v^4*f w^4*delta w^2*(H v^2+H v*fp v*l v-3*H v*lp v*f v+3*Hp v*l v*f v) +
      H v^2*f v^2*f w^2*delta w*(H v^2*h0 v*(-5*H w*fp w*t w+3*H w*f w*tp w+3*Hp w*f w*t w) +
        H w^3*pkExpression v)) := by
    simp only [radialScalar, G, U, V, dPG, dQG, dPV, dQU, rf, rH, rt, rk, rl, mix, pkExpression]
    ring
  rw [he, t_derivative_minus w, k_derivative_identity v,
    l_derivative_identity v, t_derivative_plus w]
  have hr :
      -3*H w^6*f v^4*delta v^2 -
      3*H v*H w^3*f v^2*f w^2*delta v*delta w*mix v +
      H w^3*f v^4*delta v*(-H v*h0 v*(-2*H w^3+54*delta w*f w^2) -
        H w^3*(2*h0 v*H v-3*delta v)) -
      3*H v^4*f w^4*delta w^2*(-9*h0 v*f v^2) +
      H v^2*f v^2*f w^2*delta w*(H v^2*h0 v*(10*H w^3-27*delta w*f w^2)+H w^3*pkExpression v) =
      H v*H w^3*f v^2*f w^2*delta w*
        (H v*(10*h0 v*H v^2+pkExpression v)-delta v*(3*mix v+54*h0 v*f v^2)) := by ring
  rw [hr, mixed_bridge]
  ring

end HodgeTestbed.EllipticAmbient.Cubic
