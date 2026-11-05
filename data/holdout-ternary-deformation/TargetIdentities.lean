import HodgeTarget
import Proposal.DeformedEquation

/-!
Bind the quotient equation to the protected record, not to a replacement
definition. The cover substitution is the one in fqlx's accepted holdout
construction. Prepared with OpenAI Codex assistance for hodgepodgeconjecture.
-/
noncomputable section
namespace DeformedConic
open MvPolynomial
variable {R : Type*} [Field R] [CharZero R] [Algebra ℂ R]

def physicalEvaluation (a b t y x0 x1 x2 : R) : HodgeComputer.Poly →+* R :=
  MvPolynomial.eval₂Hom (algebraMap ℂ R) ![x0,x1,x2,a*t,y,b*t]

theorem protected_cover_equation (a b t y x0 x1 x2 : R) (hbase : a^6+b^6=1) :
    14*physicalEvaluation a b t y x0 x1 x2 HodgeSubmission.F =
      H a b ![x0,x1,x2,y^2+t^2,y*t] := by
  simp only [physicalEvaluation,HodgeSubmission.F,H,map_add,map_mul,map_pow,
    MvPolynomial.eval₂Hom_X',MvPolynomial.eval₂Hom_C,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val,Matrix.empty_val',map_div₀,map_one,map_ofNat]
  field_simp
  linear_combination 98*t^6*hbase

theorem protected_cover_source (a b t y x0 x1 x2 : R) :
    physicalEvaluation a b t y x0 x1 x2 HodgeSubmission.A=x0^3*(a*t)^3 := by
  simp [physicalEvaluation,HodgeSubmission.A]

theorem protected_pole_order : HodgeSubmission.q=1 := rfl

#print axioms protected_cover_equation
#print axioms protected_cover_source
end DeformedConic
