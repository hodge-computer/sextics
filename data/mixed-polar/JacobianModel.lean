import Mathlib.Tactic.Ring
/-! Target-specific integral model for mixed-polar. Its coefficients are
432 times the degree-four and degree-six Jacobian coefficients. The short
aliases retain the accepted polynomial-family API; the extra argument is
unused because the primitive below treats arbitrary polynomial sources.
The coefficient-incidence construction follows fqlx and hodgepodgeconjecture;
classical cubic invariants follow Fisher/SageMath. Prepared with Codex assistance. -/
namespace MixedPolarJacobian
section Ring
variable {K : Type*} [CommRing K]
def a432 (cOne cTwo r t : K) : K :=
  -54*cOne^3*cTwo*r*t*(r+cTwo^6*t)*(4*cOne*(r+t)-r)
def b432 (cOne cTwo r t : K) : K :=
  -2916*(r+t)^2*(r+cOne^6*t)^2*(r+cTwo^6*t)^2
  -54*cOne^3*cTwo^3*r^2*t*(r+t)^2*(r+cTwo^6*t)
  +324*cOne^4*r*t*(r+t)*(r+cOne^6*t)*(r+cTwo^6*t)^2
  -16*cOne^9*r*t^2*(r+t)*(r+cTwo^6*t)^2
  -54*cOne^3*r^2*t*(r+cOne^6*t)*(r+cTwo^6*t)^2
  +3*cOne^8*r^2*t^2*(r+cTwo^6*t)^2
def a8 (cOne cTwo _α r t : K) : K := a432 cOne cTwo r t
def b256 (cOne cTwo _α r t : K) : K := b432 cOne cTwo r t
def equation (cOne cTwo α r t x y : K) : K :=
  432*y^2-432*x^3-a8 cOne cTwo α r t*x-b256 cOne cTwo α r t
lemma a8_weight (c₁ c₂ α r t s : K) :
    a8 c₁ c₂ α (s*r) (s*t)=s^4*a8 c₁ c₂ α r t := by simp only [a8,a432]; ring
lemma b256_weight (c₁ c₂ α r t s : K) :
    b256 c₁ c₂ α (s*r) (s*t)=s^6*b256 c₁ c₂ α r t := by simp only [b256,b432]; ring
lemma equation_weight (c₁ c₂ α r t x y s : K) :
    equation c₁ c₂ α (s*r) (s*t) (s^2*x) (s^3*y)=s^6*equation c₁ c₂ α r t x y := by
  simp only [equation,a8_weight,b256_weight]; ring
end Ring
end MixedPolarJacobian
