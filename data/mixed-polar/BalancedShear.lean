import HodgeComputer.Constructions.TransitiveCubic.Cubic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! The mixed-polar reversed edge and balanced xyz first variation reduce
to the maintained transitive cubic over a quadratic coefficient extension.
Only polynomial/field identities are asserted here. -/
noncomputable section
namespace MixedPolarBalancedShear
variable {K : Type*} [Field K] [CharZero K]

def bPrime (a b d f k : K) : K := b+a*k^3+d*k^2+f*k
def dPrime (a d k : K) : K := d+3*a*k

theorem base_shear (a b c d e f k X Y Z : K)
    (hk : 3*a*k^2+2*d*k+f=0) :
    a*(X+k*Y)^3+b*Y^3+c*Z^3+d*(X+k*Y)^2*Y+
      e*Y^2*Z+f*(X+k*Y)*Y^2 =
    TransitiveCubic.cubic a (bPrime a b d f k) c (dPrime a d k) e 0 X Y Z := by
  simp only [TransitiveCubic.cubic, bPrime, dPrime]
  linear_combination X*Y^2*hk

theorem discriminant_identity (a d f k : K)
    (hk : 3*a*k^2+2*d*k+f=0) :
    (dPrime a d k)^2=d^2-3*a*f := by
  simp only [dPrime]
  linear_combination 3*a*hk

/-- The determinant-one lambda shear X -> X-lambda*Z/(2D) cancels
lambda*XYZ.  Its only cubic coefficient jets are eDot=k and fDot=-3a/(2D). -/
theorem first_variation_shear (a D k X Y Z : K) (hD : D ≠ 0) :
    (X+k*Y)*Y*Z-Z/(2*D)*(3*a*X^2+2*D*X*Y) =
      k*Y^2*Z+(-3*a/(2*D))*X^2*Z := by
  field_simp
  ring

/-- On z=1 the modified source differs by a constant multiple of Ux. -/
theorem modified_source (a D k X Y : K) (hD : D ≠ 0) :
    k*Y^2-3*a*X^2/(2*D) =
      (X+k*Y)*Y-(3*a*X^2+2*D*X*Y)/(2*D) := by
  field_simp
  ring

/-- Therefore the complete second-normal source is unchanged, including
both the numerator derivative and the differentiated normal denominator. -/
theorem second_normal_source_unchanged (a D k X Y g : K)
    (hD : D ≠ 0) (hg : g ≠ 0)
    (hgvalue : g=3*a*X^2+2*D*X*Y) :
    (-3*a*X/D-(k*Y^2-3*a*X^2/(2*D))*(6*a*X+2*D*Y)/g)/g =
      (Y-(X+k*Y)*Y*(6*a*X+2*D*Y)/g)/g := by
  field_simp [hD, hg]
  linear_combination -(6*a*X+2*D*Y)*hgvalue

/-- The lambda jet of s4 in the maintained transitive normalization. -/
theorem s4_first_variation (a b c d f k : K)
    (hk : 3*a*k^2+2*d*k+f=0) :
    c*(dPrime a d k)^2*k+(9/2:K)*a*(bPrime a b d f k)*c =
      (9*a*b*c-c*d*f)/2 := by
  simp only [dPrime, bPrime]
  field_simp
  linear_combination c*(9*a*k+d)*hk

/-- The lambda jet of s6 is independent of the chosen quadratic root. -/
theorem s6_first_variation (a c d e k : K) :
    12*a^2*c*e^2*k-4*a*c*(dPrime a d k)*e^2 = -4*a*c*d*e^2 := by
  simp only [dPrime]
  ring

/-- The base invariant identities descend the Jacobian out of the chosen
quadratic root. They are the maintained transitive polynomial invariants. -/
def reverseS4 (a b c d e f : K) : K := c*e*(d^2-3*a*f)
def reverseS6 (a b c d e f : K) : K :=
  c*(27*a^2*b^2*c+4*a^2*e^3-18*a*b*c*d*f+4*a*c*f^3+
    4*b*c*d^3-c*d^2*f^2)

theorem s4_shear_numerator (a b c d e f k : K)
    (hk : 3*a*k^2+2*d*k+f=0) :
    TransitiveCubic.s4Numerator a (bPrime a b d f k) c (dPrime a d k) e 0=
      3*reverseS4 a b c d e f := by
  dsimp [TransitiveCubic.s4Numerator,bPrime,dPrime,reverseS4]
  linear_combination 9*a*c*e*hk

theorem s6_shear_numerator (a b c d e f k : K)
    (hk : 3*a*k^2+2*d*k+f=0) :
    TransitiveCubic.s6Numerator a (bPrime a b d f k) c (dPrime a d k) e 0=
      27*reverseS6 a b c d e f := by
  dsimp [TransitiveCubic.s6Numerator,bPrime,dPrime,reverseS6]
  linear_combination
    27*c^2*(45*a^3*k^4+54*a^2*b*k+60*a^2*d*k^3+39*a^2*f*k^2+
      18*a*b*d+17*a*d^2*k^2+8*a*d*f*k-4*a*f^2+2*d^3*k+d^2*f)*hk

end MixedPolarBalancedShear
#print axioms MixedPolarBalancedShear.base_shear
#print axioms MixedPolarBalancedShear.first_variation_shear
#print axioms MixedPolarBalancedShear.second_normal_source_unchanged
#print axioms MixedPolarBalancedShear.s4_first_variation
#print axioms MixedPolarBalancedShear.s6_first_variation
