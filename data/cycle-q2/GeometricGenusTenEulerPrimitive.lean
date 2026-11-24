import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# A rational primitive on the genus-ten normal-coordinate chart

In the coordinates T and h the difference of the physical second-kind form
and its Euler transport has a twenty-term Laurent primitive. Evaluation on
an arbitrary derivation checks both differential coefficients simultaneously.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 6000
noncomputable section
namespace CycleQ2GenusTenEulerPrimitive
variable {K : Type*} [Field K] [CharZero K]

def v (T h : K) := (h-6+6*T^2)/T
def U (T h : K) := T * (v T h)^3
def hT (T h : K) := -12*T+(2/3)*v T h
def P (T h : K) := -4*T^2*(24*T^2+h+12)/h^3
def XP (T h : K) := -8*T*(48*T^2+h+12)/h^3 +
    hT T h * (8*T^2*(36*T^2+h+18)/h^4)
def BP (T h : K) := -6*T^2/h * XP T h
def G (T h : K) (D : Derivation ℤ K K) :=
  (P T h / 3 + (T+1/T+v T h/3)*BP T h) * D (U T h) -
    U T h * XP T h * D T

def C (T h : K) : K :=
  let t := T^2
  1492992*(t-1)^2*(2*t+1)^3*(3*t-1)/h^5 +
  103680*(t-1)*(2*t+1)*(138*t^3-7*t^2-13*t-10)/h^4 +
  13824*(679*t^4-215*t^3-141*t^2-34*t-19)/h^3 +
  1152*(1427*t^3-201*t^2-36*t+25)/h^2 +
  192*(927*t^2-32*t-7)/h - 16*h/3

def eta (T h : K) (D : Derivation ℤ K K) : K :=
  ((C T h+64)/T+9952*T)*D T + ((1728*T^2-48)/h+288)*D h

def primitive (T h : K) : K :=
  let t := T^2
  (-93312+93312*t+839808*t^2-466560*t^3-1492992*t^4+1119744*t^5)/h^4 +
  (76032+62208*t-269568*t^2-698112*t^3+829440*t^4)/h^3 +
  (-20736-28512*t-114048*t^2+256608*t^3)/h^2 +
  (2160-7776*t+47088*t^2)/h + 5352*t+276*h

section Derivatives
variable (T h : K) (D : Derivation ℤ K K) (h₁ : T ≠ 0) (h₂ : h ≠ 0)
omit [CharZero K] in
private theorem deriv_numeral (n : ℕ) [n.AtLeastTwo] : D (OfNat.ofNat n : K) = 0 := D.map_natCast n

include h₁ in
private theorem dU :
    D (U T h) = (36*T*(v T h)^2-2*(v T h)^3)*D T + 3*(v T h)^2*D h := by
  simp [U, v, Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_div,
    deriv_numeral D, smul_eq_mul, nsmul_eq_mul]
  field_simp [h₁]
  ring

include h₂ in
/-- The coefficients in XP are the literal two partial derivatives of P. -/
theorem dP :
    D (P T h) = (-8*T*(48*T^2+h+12)/h^3)*D T +
      (8*T^2*(36*T^2+h+18)/h^4)*D h := by
  simp [P, Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_div,
    deriv_numeral D, smul_eq_mul, nsmul_eq_mul]
  field_simp [h₂]
  ring

include h₁ h₂ in
/-- Exact equality of the two rational one-forms on the whole torus. -/
theorem exact_euler_difference : eta T h D - G T h D = D (primitive T h) := by
  unfold G
  rw [dU T h D h₁]
  simp only [eta,C,primitive,P,XP,hT,BP,U,v,map_add,map_sub,map_neg,
    Derivation.leibniz_div, Derivation.leibniz_pow,Derivation.leibniz,
    deriv_numeral D,
    nsmul_eq_mul, smul_eq_mul, mul_zero, add_zero, zero_add]
  field_simp [h₁,h₂]
  ring

end Derivatives
section Quartic

/-- The two-modulus genus-ten equation on the b,T torus. -/
def quartic (I J b T : K) := I^6*T^4+b^9*T^2+(I*b^8/2-J*b^9)*T+b^12+b^9
def quarticT (I J b T : K) := 4*I^6*T^3+2*b^9*T+I*b^8/2-J*b^9
def quarticI (I b T : K) := 6*I^5*T^4+b^8*T/2
def quarticB (I J b T : K) :=
  9*b^8*T^2+(4*I*b^7-9*J*b^8)*T+12*b^11+9*b^8

/-- Evaluating the parameter and fibre derivatives at fixed b or fixed I,J
gives the physical rational correction for the one-form T db / b⁴. -/
theorem xi_transport (I J b T : K) (hb : b ≠ 0) (hg : quarticT I J b T ≠ 0)
    (hf : quartic I J b T = 0) :
    let g := quarticT I J b T
    let dJ := b^9*T/g
    let dI := -quarticI I b T/g
    let db := -quarticB I J b T/g
    dJ/b^4 = b^5*T/g ∧
    I*(dI/b^4)+2*T/b^4 = -(I/6)*(b^4*T/g) - 2*b^8/g -
      (2/3)*(db/b^3 - 3*T/b^4) := by
  dsimp only
  constructor
  · field_simp [hb,hg]
  · have h : -I*quarticI I b T - (2/3)*b*quarticB I J b T +
        (I/6)*b^8*T + 2*b^12 = 0 := by
      calc
        _ = -6*quartic I J b T := by unfold quarticI quarticB quartic; ring
        _ = 0 := by rw [hf,mul_zero]
    have e : -I*quarticI I b T =
        (2/3)*b*quarticB I J b T - (I/6)*b^8*T - 2*b^12 := by
      linear_combination h
    calc
      _ = (-I*quarticI I b T)/(quarticT I J b T * b^4) + 2*T/b^4 := by ring
      _ = _ := by
        rw [e]
        field_simp [hb,hg]
        ring

/-- At fixed T the coefficient of Θ = dT/(3b³T) differentiates in both
parameter directions. This uses the equation in the field and an actual
derivation, so the formula applies in any smooth function-field chart. -/
theorem theta_connection (I J b T : K) (D : Derivation ℤ K K)
    (hb : b ≠ 0) (ht : T ≠ 0) (hT : D T = 0) (hf : quartic I J b T = 0) :
    quarticB I J b T * D (1/(3*b^3*T)) =
      (quarticI I b T * D I - b^9*T*D J)/(b^4*T) := by
  have de : quarticB I J b T * D b + quarticI I b T * D I - b^9*T*D J = 0 := by
    have e := congrArg D hf
    simp only [quartic, map_add, map_sub, map_zero, Derivation.leibniz_div,
      Derivation.leibniz_pow, Derivation.leibniz, deriv_numeral D,
      hT, nsmul_eq_mul, smul_eq_mul, mul_zero, zero_add, sub_zero] at e
    unfold quarticB quarticI
    linear_combination e
  have dc : D (1/(3*b^3*T)) = -D b / (b^4*T) := by
    simp only [Derivation.leibniz_div, Derivation.leibniz_pow, Derivation.leibniz,
      Derivation.map_one_eq_zero, deriv_numeral D, hT, nsmul_eq_mul, smul_eq_mul, mul_zero, zero_mul,
      zero_add, add_zero, zero_sub]
    field_simp [hb,ht]
    ring
  rw [dc]
  field_simp [hb,ht]
  linear_combination -de

/-- In the fixed-b chart this Euler relation retains the exact derivative
of T/b³ and the polar Newton differential with numerator b⁵. -/
theorem xi_quasi_euler (I J b T : K) (hb : b ≠ 0) (hg : quarticT I J b T ≠ 0)
    (hf : quartic I J b T = 0) :
    let g := quarticT I J b T
    let dI := -quarticI I b T/g
    let dJ := b^9*T/g
    let db := -quarticB I J b T/g
    (3*T+2*I*dI+3*J*dJ)/b^4 + 2*(db/b^3-3*T/b^4) =
      (3*I/2)*b^4*T/g + 6*b^5/g := by
  dsimp only
  have e : 3*T*quarticT I J b T - 2*I*quarticI I b T + 3*J*b^9*T +
      2*(-3*T*quarticT I J b T-b*quarticB I J b T) - (3*I/2)*b^8*T - 6*b^9 = 0 := by
    calc
      _ = -24*quartic I J b T := by unfold quarticT quarticI quarticB quartic; ring
      _ = 0 := by rw [hf,mul_zero]
  field_simp [hb,hg]
  linear_combination 2*e

end Quartic
end CycleQ2GenusTenEulerPrimitive
end
#print axioms CycleQ2GenusTenEulerPrimitive.exact_euler_difference

#print axioms CycleQ2GenusTenEulerPrimitive.xi_transport

#print axioms CycleQ2GenusTenEulerPrimitive.theta_connection
#print axioms CycleQ2GenusTenEulerPrimitive.xi_quasi_euler
