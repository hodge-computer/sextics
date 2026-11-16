import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Proposal.JacobianModel

/-! Exact polynomial Weierstrass coefficients and source scaling for the
balanced mixed-polar cubic. The covariant normalization is the maintained
transitive cubic normalization. These algebraic identities are independent
of the subsequent polynomial-curve existence argument. -/
noncomputable section
namespace MixedPolarScaling
variable {K : Type*} [Field K] [CharZero K]

def reverseS4 (a b c d e f : K) : K := c*e*(d^2-3*a*f)
def reverseS6 (a b c d e f : K) : K :=
  c*(27*a^2*b^2*c+4*a^2*e^3-18*a*b*c*d*f+4*a*c*f^3+
    4*b*c*d^3-c*d^2*f^2)
def dot4 (a b c d e f : K) : K := (9*a*b*c-c*d*f)/2
def dotB (a b c d e f : K) : K := a*c*d*e^2

def a4 (cOne cTwo R T : K) : K :=
  cOne^3*cTwo/8*R*T*(R+cTwo^6*T)*(R-4*cOne*(R+T))
def b6 (cOne cTwo R T : K) : K :=
  -(27/4)*(R+T)^2*(R+cOne^6*T)^2*(R+cTwo^6*T)^2-
  cOne^3*cTwo^3/8*R^2*(R+cTwo^6*T)*(R+T)^2*T+
  3*cOne^4/4*R*(R+T)*(R+cOne^6*T)*(R+cTwo^6*T)^2*T-
  cOne^9/27*R*(R+T)*(R+cTwo^6*T)^2*T^2-
  cOne^3/8*R^2*(R+cOne^6*T)*(R+cTwo^6*T)^2*T+
  cOne^8/144*R^2*(R+cTwo^6*T)^2*T^2
def jacobianSource (cOne cTwo R T X : K) : K :=
  cOne*cTwo*(R+cTwo^6*T)/3456*
    ((108*(R+T)*(R+cOne^6*T)-2*cOne^4*R*T)*X+
      3*cOne^3*cTwo^2*R^2*(R+T)*T)

theorem model_a432 (cOne cTwo R T : K) :
    MixedPolarJacobian.a432 cOne cTwo R T/432=a4 cOne cTwo R T := by
  simp only [MixedPolarJacobian.a432,a4]
  ring

theorem model_b432 (cOne cTwo R T : K) :
    MixedPolarJacobian.b432 cOne cTwo R T/432=b6 cOne cTwo R T := by
  simp only [MixedPolarJacobian.b432,b6]
  ring

theorem a4_scaling (cOne cTwo R v : K) :
    a4 cOne cTwo R (R*v^6)=R^4*
      reverseS4 (1+v^6) (1+cOne^6*v^6) (1+cTwo^6*v^6)
        (cOne*v^2/2) (cOne*cTwo*v^2/2) (cOne^3*v^4/3) := by
  simp only [a4,reverseS4]
  ring

theorem b6_scaling (cOne cTwo R v : K) :
    b6 cOne cTwo R (R*v^6)=-(R^6/4)*
      reverseS6 (1+v^6) (1+cOne^6*v^6) (1+cTwo^6*v^6)
        (cOne*v^2/2) (cOne*cTwo*v^2/2) (cOne^3*v^4/3) := by
  simp only [b6,reverseS6]
  ring

theorem source_scaling (cOne cTwo R v xi : K) :
    jacobianSource cOne cTwo R (R*v^6) (R^2*xi)=
      cOne*cTwo*R^5/144*
        (dot4 (1+v^6) (1+cOne^6*v^6) (1+cTwo^6*v^6)
          (cOne*v^2/2) (cOne*cTwo*v^2/2) (cOne^3*v^4/3)*xi+
        dotB (1+v^6) (1+cOne^6*v^6) (1+cTwo^6*v^6)
          (cOne*v^2/2) (cOne*cTwo*v^2/2) (cOne^3*v^4/3)) := by
  simp only [jacobianSource,dot4,dotB]
  ring

end MixedPolarScaling
#print axioms MixedPolarScaling.a4_scaling
#print axioms MixedPolarScaling.b6_scaling
#print axioms MixedPolarScaling.source_scaling
