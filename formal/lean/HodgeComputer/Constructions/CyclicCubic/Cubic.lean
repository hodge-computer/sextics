import Mathlib.Tactic.Ring

/-! Six-coefficient cyclic cubic invariants, from `hodgepodgeconjecture`’s
cycle-three proof (#165). Classical normalization follows Tom Fisher and
SageMath, as credited in the application explanation. -/
namespace CycleCubic
variable {K : Type*} [CommRing K]
def cubic (a b c d e f x y z : K) : K :=
  a*x^3+b*y^3+c*z^3+d*x^2*y+e*y^2*z+f*z^2*x
/-- The coefficient invariants with c4=-48*s4 and c6=216*s6. -/
def s4 (a b c d e f : K) : K := a*e^2*f+b*d*f^2+c*d^2*e
def s6 (a b c d e f : K) : K :=
  27*a^2*b^2*c^2+4*a^2*c*e^3+4*a*b^2*f^3+6*a*b*c*d*e*f+4*b*c^2*d^3-d^2*e^2*f^2
end CycleCubic
