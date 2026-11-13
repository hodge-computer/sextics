import HodgeComputer.Constructions.PolarCubic.CoefficientExpressions
import Mathlib.Tactic

/-! Integral covariants and first coefficient jets for the reverse-edge cubic.
The first jets use the perturbation `2*k*x*y*z`. Polynomial identities
below are independently certified in `CubicSyzygy` and `CubicDifferential`.
Prepared with OpenAI Codex assistance. -/
set_option linter.unusedVariables false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
namespace PolarCubic
variable {K : Type*} [CommRing K]
noncomputable def cubic (a b c d e f x y z : K) : K :=
  a*x^3+b*y^3+c*z^3+d*x^2*y+e*y^2*z+f*x*y^2
noncomputable def cubicJet (a b c d e f k x y z : K) : K :=
  cubic a b c d e f x y z+2*k*x*y*z
noncomputable def s4Numerator (a b c d e f : K) : K :=
  ((((-(9:K))*a)*(c*(e*f)))+(((3:K)*c)*(d^2*e)))
noncomputable def s6Numerator (a b c d e f : K) : K :=
  (((((729:K)*a^2)*(b^2*c^2))+((((108:K)*a^2)*(c*e^3))+(((-(486:K))*(a*b))*(c^2*(d*f)))))+((((108:K)*a)*(c^2*f^3))+((((108:K)*b)*(c^2*d^3))+(((-(27:K))*c^2)*(d^2*f^2)))))
noncomputable def s4NumeratorK (a b c d e f : K) : K :=
  ((((27:K)*a)*(b*c))+(((-(3:K))*c)*(d*f)))
noncomputable def s6NumeratorK (a b c d e f : K) : K :=
  (((-(216:K))*a)*(c*(d*e^2)))
noncomputable def s4NumeratorJet (a b c d e f k : K) : K :=
  s4Numerator a b c d e f+k*s4NumeratorK a b c d e f
noncomputable def s6NumeratorJet (a b c d e f k : K) : K :=
  s6Numerator a b c d e f+k*s6NumeratorK a b c d e f
noncomputable def s4 {L : Type*} [Field L] (a b c d e f : L) : L :=
  s4Numerator a b c d e f/3
noncomputable def s6 {L : Type*} [Field L] (a b c d e f : L) : L :=
  s6Numerator a b c d e f/27
end PolarCubic

namespace PolarCovariants
variable {K : Type*} [CommRing K]
open PolynomialEncoding.SignedExpressions ExpressionData
noncomputable def coefficientContext (a b c d e f : K) : ℕ → K :=
  fun i => if i=0 then a else if i=1 then b else if i=2 then c else
    if i=3 then d else if i=4 then e else if i=5 then f else 0
noncomputable def HCoeff201 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) HCoeff201Expr
noncomputable def HCoeff120 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) HCoeff120Expr
noncomputable def HCoeff111 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) HCoeff111Expr
noncomputable def HCoeff102 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) HCoeff102Expr
noncomputable def HCoeff030 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) HCoeff030Expr
noncomputable def HCoeff021 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) HCoeff021Expr
noncomputable def HCoeff012 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) HCoeff012Expr
noncomputable def H (a b c d e f x y z : K) : K :=
  (((HCoeff201 a b c d e f*(x^2*z))+((HCoeff120 a b c d e f*(x*y^2))+((HCoeff111 a b c d e f*x)*(y*z))))+(((HCoeff102 a b c d e f*(x*z^2))+(HCoeff030 a b c d e f*y^3))+((HCoeff021 a b c d e f*(y^2*z))+(HCoeff012 a b c d e f*(y*z^2)))))
noncomputable def ThetaCoeff600 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetaCoeff600Expr
noncomputable def ThetaCoeff510 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetaCoeff510Expr
noncomputable def ThetaCoeff501 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetaCoeff501Expr
noncomputable def ThetaCoeff420 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetaCoeff420Expr
noncomputable def ThetaCoeff411 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetaCoeff411Expr
noncomputable def ThetaCoeff402 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetaCoeff402Expr
noncomputable def ThetaCoeff330 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetaCoeff330Expr
noncomputable def ThetaCoeff321 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetaCoeff321Expr
noncomputable def ThetaCoeff312 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetaCoeff312Expr
noncomputable def ThetaCoeff303 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetaCoeff303Expr
noncomputable def ThetaCoeff240 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetaCoeff240Expr
noncomputable def ThetaCoeff231 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetaCoeff231Expr
noncomputable def ThetaCoeff222 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetaCoeff222Expr
noncomputable def ThetaCoeff213 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetaCoeff213Expr
noncomputable def ThetaCoeff204 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetaCoeff204Expr
noncomputable def ThetaCoeff150 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetaCoeff150Expr
noncomputable def ThetaCoeff141 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetaCoeff141Expr
noncomputable def ThetaCoeff132 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetaCoeff132Expr
noncomputable def ThetaCoeff123 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetaCoeff123Expr
noncomputable def ThetaCoeff114 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetaCoeff114Expr
noncomputable def ThetaCoeff105 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetaCoeff105Expr
noncomputable def ThetaCoeff060 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetaCoeff060Expr
noncomputable def ThetaCoeff051 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetaCoeff051Expr
noncomputable def ThetaCoeff042 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetaCoeff042Expr
noncomputable def ThetaCoeff033 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetaCoeff033Expr
noncomputable def ThetaCoeff024 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetaCoeff024Expr
noncomputable def ThetaCoeff015 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetaCoeff015Expr
noncomputable def ThetaCoeff006 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetaCoeff006Expr
noncomputable def Theta (a b c d e f x y z : K) : K :=
  (((((ThetaCoeff600 a b c d e f*x^6)+((ThetaCoeff510 a b c d e f*(x^5*y))+(ThetaCoeff501 a b c d e f*(x^5*z))))+(((ThetaCoeff420 a b c d e f*(x^4*y^2))+((ThetaCoeff411 a b c d e f*x^4)*(y*z)))+((ThetaCoeff402 a b c d e f*(x^4*z^2))+(ThetaCoeff330 a b c d e f*(x^3*y^3)))))+((((ThetaCoeff321 a b c d e f*x^3)*(y^2*z))+(((ThetaCoeff312 a b c d e f*x^3)*(y*z^2))+(ThetaCoeff303 a b c d e f*(x^3*z^3))))+(((ThetaCoeff240 a b c d e f*(x^2*y^4))+((ThetaCoeff231 a b c d e f*x^2)*(y^3*z)))+(((ThetaCoeff222 a b c d e f*x^2)*(y^2*z^2))+((ThetaCoeff213 a b c d e f*x^2)*(y*z^3))))))+((((ThetaCoeff204 a b c d e f*(x^2*z^4))+((ThetaCoeff150 a b c d e f*(x*y^5))+((ThetaCoeff141 a b c d e f*x)*(y^4*z))))+((((ThetaCoeff132 a b c d e f*x)*(y^3*z^2))+((ThetaCoeff123 a b c d e f*x)*(y^2*z^3)))+(((ThetaCoeff114 a b c d e f*x)*(y*z^4))+(ThetaCoeff105 a b c d e f*(x*z^5)))))+(((ThetaCoeff060 a b c d e f*y^6)+((ThetaCoeff051 a b c d e f*(y^5*z))+(ThetaCoeff042 a b c d e f*(y^4*z^2))))+(((ThetaCoeff033 a b c d e f*(y^3*z^3))+(ThetaCoeff024 a b c d e f*(y^2*z^4)))+((ThetaCoeff015 a b c d e f*(y*z^5))+(ThetaCoeff006 a b c d e f*z^6))))))
noncomputable def JCoeff900 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff900Expr
noncomputable def JCoeff810 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff810Expr
noncomputable def JCoeff801 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff801Expr
noncomputable def JCoeff720 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff720Expr
noncomputable def JCoeff711 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff711Expr
noncomputable def JCoeff630 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff630Expr
noncomputable def JCoeff621 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff621Expr
noncomputable def JCoeff612 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff612Expr
noncomputable def JCoeff603 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff603Expr
noncomputable def JCoeff540 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff540Expr
noncomputable def JCoeff531 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff531Expr
noncomputable def JCoeff522 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff522Expr
noncomputable def JCoeff513 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff513Expr
noncomputable def JCoeff504 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff504Expr
noncomputable def JCoeff450 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff450Expr
noncomputable def JCoeff441 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff441Expr
noncomputable def JCoeff432 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff432Expr
noncomputable def JCoeff423 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff423Expr
noncomputable def JCoeff414 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff414Expr
noncomputable def JCoeff405 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff405Expr
noncomputable def JCoeff360 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff360Expr
noncomputable def JCoeff351 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff351Expr
noncomputable def JCoeff342 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff342Expr
noncomputable def JCoeff333 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff333Expr
noncomputable def JCoeff324 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff324Expr
noncomputable def JCoeff315 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff315Expr
noncomputable def JCoeff306 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff306Expr
noncomputable def JCoeff270 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff270Expr
noncomputable def JCoeff261 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff261Expr
noncomputable def JCoeff252 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff252Expr
noncomputable def JCoeff243 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff243Expr
noncomputable def JCoeff234 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff234Expr
noncomputable def JCoeff225 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff225Expr
noncomputable def JCoeff216 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff216Expr
noncomputable def JCoeff180 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff180Expr
noncomputable def JCoeff171 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff171Expr
noncomputable def JCoeff162 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff162Expr
noncomputable def JCoeff153 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff153Expr
noncomputable def JCoeff144 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff144Expr
noncomputable def JCoeff135 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff135Expr
noncomputable def JCoeff126 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff126Expr
noncomputable def JCoeff117 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff117Expr
noncomputable def JCoeff108 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff108Expr
noncomputable def JCoeff090 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff090Expr
noncomputable def JCoeff081 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff081Expr
noncomputable def JCoeff072 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff072Expr
noncomputable def JCoeff063 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff063Expr
noncomputable def JCoeff054 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff054Expr
noncomputable def JCoeff045 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff045Expr
noncomputable def JCoeff036 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff036Expr
noncomputable def JCoeff027 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff027Expr
noncomputable def JCoeff018 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff018Expr
noncomputable def JCoeff009 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JCoeff009Expr
noncomputable def J (a b c d e f x y z : K) : K :=
  ((((((JCoeff900 a b c d e f*x^9)+((JCoeff810 a b c d e f*(x^8*y))+(JCoeff801 a b c d e f*(x^8*z))))+((JCoeff720 a b c d e f*(x^7*y^2))+(((JCoeff711 a b c d e f*x^7)*(y*z))+(JCoeff630 a b c d e f*(x^6*y^3)))))+((((JCoeff621 a b c d e f*x^6)*(y^2*z))+(((JCoeff612 a b c d e f*x^6)*(y*z^2))+(JCoeff603 a b c d e f*(x^6*z^3))))+(((JCoeff540 a b c d e f*(x^5*y^4))+((JCoeff531 a b c d e f*x^5)*(y^3*z)))+(((JCoeff522 a b c d e f*x^5)*(y^2*z^2))+((JCoeff513 a b c d e f*x^5)*(y*z^3))))))+((((JCoeff504 a b c d e f*(x^5*z^4))+((JCoeff450 a b c d e f*(x^4*y^5))+((JCoeff441 a b c d e f*x^4)*(y^4*z))))+(((JCoeff432 a b c d e f*x^4)*(y^3*z^2))+(((JCoeff423 a b c d e f*x^4)*(y^2*z^3))+((JCoeff414 a b c d e f*x^4)*(y*z^4)))))+(((JCoeff405 a b c d e f*(x^4*z^5))+((JCoeff360 a b c d e f*(x^3*y^6))+((JCoeff351 a b c d e f*x^3)*(y^5*z))))+((((JCoeff342 a b c d e f*x^3)*(y^4*z^2))+((JCoeff333 a b c d e f*x^3)*(y^3*z^3)))+(((JCoeff324 a b c d e f*x^3)*(y^2*z^4))+((JCoeff315 a b c d e f*x^3)*(y*z^5)))))))+(((((JCoeff306 a b c d e f*(x^3*z^6))+((JCoeff270 a b c d e f*(x^2*y^7))+((JCoeff261 a b c d e f*x^2)*(y^6*z))))+(((JCoeff252 a b c d e f*x^2)*(y^5*z^2))+(((JCoeff243 a b c d e f*x^2)*(y^4*z^3))+((JCoeff234 a b c d e f*x^2)*(y^3*z^4)))))+((((JCoeff225 a b c d e f*x^2)*(y^2*z^5))+(((JCoeff216 a b c d e f*x^2)*(y*z^6))+(JCoeff180 a b c d e f*(x*y^8))))+((((JCoeff171 a b c d e f*x)*(y^7*z))+((JCoeff162 a b c d e f*x)*(y^6*z^2)))+(((JCoeff153 a b c d e f*x)*(y^5*z^3))+((JCoeff144 a b c d e f*x)*(y^4*z^4))))))+(((((JCoeff135 a b c d e f*x)*(y^3*z^5))+(((JCoeff126 a b c d e f*x)*(y^2*z^6))+((JCoeff117 a b c d e f*x)*(y*z^7))))+(((JCoeff108 a b c d e f*(x*z^8))+(JCoeff090 a b c d e f*y^9))+((JCoeff081 a b c d e f*(y^8*z))+(JCoeff072 a b c d e f*(y^7*z^2)))))+(((JCoeff063 a b c d e f*(y^6*z^3))+((JCoeff054 a b c d e f*(y^5*z^4))+(JCoeff045 a b c d e f*(y^4*z^5))))+(((JCoeff036 a b c d e f*(y^3*z^6))+(JCoeff027 a b c d e f*(y^2*z^7)))+((JCoeff018 a b c d e f*(y*z^8))+(JCoeff009 a b c d e f*z^9)))))))
noncomputable def HkCoeff210 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) HkCoeff210Expr
noncomputable def HkCoeff102 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) HkCoeff102Expr
noncomputable def HkCoeff030 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) HkCoeff030Expr
noncomputable def HkCoeff012 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) HkCoeff012Expr
noncomputable def Hk (a b c d e f x y z : K) : K :=
  (((HkCoeff210 a b c d e f*(x^2*y))+(HkCoeff102 a b c d e f*(x*z^2)))+((HkCoeff030 a b c d e f*y^3)+(HkCoeff012 a b c d e f*(y*z^2))))
noncomputable def ThetakCoeff510 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetakCoeff510Expr
noncomputable def ThetakCoeff501 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetakCoeff501Expr
noncomputable def ThetakCoeff420 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetakCoeff420Expr
noncomputable def ThetakCoeff411 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetakCoeff411Expr
noncomputable def ThetakCoeff402 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetakCoeff402Expr
noncomputable def ThetakCoeff330 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetakCoeff330Expr
noncomputable def ThetakCoeff321 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetakCoeff321Expr
noncomputable def ThetakCoeff312 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetakCoeff312Expr
noncomputable def ThetakCoeff303 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetakCoeff303Expr
noncomputable def ThetakCoeff240 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetakCoeff240Expr
noncomputable def ThetakCoeff231 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetakCoeff231Expr
noncomputable def ThetakCoeff222 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetakCoeff222Expr
noncomputable def ThetakCoeff213 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetakCoeff213Expr
noncomputable def ThetakCoeff204 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetakCoeff204Expr
noncomputable def ThetakCoeff150 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetakCoeff150Expr
noncomputable def ThetakCoeff141 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetakCoeff141Expr
noncomputable def ThetakCoeff132 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetakCoeff132Expr
noncomputable def ThetakCoeff123 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetakCoeff123Expr
noncomputable def ThetakCoeff114 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetakCoeff114Expr
noncomputable def ThetakCoeff105 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetakCoeff105Expr
noncomputable def ThetakCoeff060 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetakCoeff060Expr
noncomputable def ThetakCoeff051 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetakCoeff051Expr
noncomputable def ThetakCoeff042 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetakCoeff042Expr
noncomputable def ThetakCoeff033 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetakCoeff033Expr
noncomputable def ThetakCoeff024 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetakCoeff024Expr
noncomputable def ThetakCoeff015 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetakCoeff015Expr
noncomputable def ThetakCoeff006 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) ThetakCoeff006Expr
noncomputable def Thetak (a b c d e f x y z : K) : K :=
  (((((ThetakCoeff510 a b c d e f*(x^5*y))+((ThetakCoeff501 a b c d e f*(x^5*z))+(ThetakCoeff420 a b c d e f*(x^4*y^2))))+(((ThetakCoeff411 a b c d e f*x^4)*(y*z))+((ThetakCoeff402 a b c d e f*(x^4*z^2))+(ThetakCoeff330 a b c d e f*(x^3*y^3)))))+((((ThetakCoeff321 a b c d e f*x^3)*(y^2*z))+(((ThetakCoeff312 a b c d e f*x^3)*(y*z^2))+(ThetakCoeff303 a b c d e f*(x^3*z^3))))+(((ThetakCoeff240 a b c d e f*(x^2*y^4))+((ThetakCoeff231 a b c d e f*x^2)*(y^3*z)))+(((ThetakCoeff222 a b c d e f*x^2)*(y^2*z^2))+((ThetakCoeff213 a b c d e f*x^2)*(y*z^3))))))+((((ThetakCoeff204 a b c d e f*(x^2*z^4))+((ThetakCoeff150 a b c d e f*(x*y^5))+((ThetakCoeff141 a b c d e f*x)*(y^4*z))))+((((ThetakCoeff132 a b c d e f*x)*(y^3*z^2))+((ThetakCoeff123 a b c d e f*x)*(y^2*z^3)))+(((ThetakCoeff114 a b c d e f*x)*(y*z^4))+(ThetakCoeff105 a b c d e f*(x*z^5)))))+(((ThetakCoeff060 a b c d e f*y^6)+((ThetakCoeff051 a b c d e f*(y^5*z))+(ThetakCoeff042 a b c d e f*(y^4*z^2))))+(((ThetakCoeff033 a b c d e f*(y^3*z^3))+(ThetakCoeff024 a b c d e f*(y^2*z^4)))+((ThetakCoeff015 a b c d e f*(y*z^5))+(ThetakCoeff006 a b c d e f*z^6))))))
noncomputable def JkCoeff900 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff900Expr
noncomputable def JkCoeff810 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff810Expr
noncomputable def JkCoeff801 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff801Expr
noncomputable def JkCoeff720 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff720Expr
noncomputable def JkCoeff711 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff711Expr
noncomputable def JkCoeff702 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff702Expr
noncomputable def JkCoeff630 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff630Expr
noncomputable def JkCoeff621 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff621Expr
noncomputable def JkCoeff612 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff612Expr
noncomputable def JkCoeff603 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff603Expr
noncomputable def JkCoeff540 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff540Expr
noncomputable def JkCoeff531 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff531Expr
noncomputable def JkCoeff522 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff522Expr
noncomputable def JkCoeff513 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff513Expr
noncomputable def JkCoeff504 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff504Expr
noncomputable def JkCoeff450 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff450Expr
noncomputable def JkCoeff441 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff441Expr
noncomputable def JkCoeff432 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff432Expr
noncomputable def JkCoeff423 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff423Expr
noncomputable def JkCoeff414 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff414Expr
noncomputable def JkCoeff405 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff405Expr
noncomputable def JkCoeff360 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff360Expr
noncomputable def JkCoeff351 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff351Expr
noncomputable def JkCoeff342 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff342Expr
noncomputable def JkCoeff333 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff333Expr
noncomputable def JkCoeff324 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff324Expr
noncomputable def JkCoeff315 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff315Expr
noncomputable def JkCoeff306 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff306Expr
noncomputable def JkCoeff270 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff270Expr
noncomputable def JkCoeff261 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff261Expr
noncomputable def JkCoeff252 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff252Expr
noncomputable def JkCoeff243 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff243Expr
noncomputable def JkCoeff234 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff234Expr
noncomputable def JkCoeff225 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff225Expr
noncomputable def JkCoeff216 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff216Expr
noncomputable def JkCoeff207 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff207Expr
noncomputable def JkCoeff180 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff180Expr
noncomputable def JkCoeff171 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff171Expr
noncomputable def JkCoeff162 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff162Expr
noncomputable def JkCoeff153 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff153Expr
noncomputable def JkCoeff144 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff144Expr
noncomputable def JkCoeff135 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff135Expr
noncomputable def JkCoeff126 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff126Expr
noncomputable def JkCoeff117 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff117Expr
noncomputable def JkCoeff108 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff108Expr
noncomputable def JkCoeff090 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff090Expr
noncomputable def JkCoeff081 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff081Expr
noncomputable def JkCoeff072 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff072Expr
noncomputable def JkCoeff063 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff063Expr
noncomputable def JkCoeff054 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff054Expr
noncomputable def JkCoeff045 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff045Expr
noncomputable def JkCoeff036 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff036Expr
noncomputable def JkCoeff027 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff027Expr
noncomputable def JkCoeff018 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff018Expr
noncomputable def JkCoeff009 (a b c d e f : K) : K :=
  ringEval (coefficientContext a b c d e f) JkCoeff009Expr
noncomputable def Jk (a b c d e f x y z : K) : K :=
  ((((((JkCoeff900 a b c d e f*x^9)+((JkCoeff810 a b c d e f*(x^8*y))+(JkCoeff801 a b c d e f*(x^8*z))))+((JkCoeff720 a b c d e f*(x^7*y^2))+(((JkCoeff711 a b c d e f*x^7)*(y*z))+(JkCoeff702 a b c d e f*(x^7*z^2)))))+(((JkCoeff630 a b c d e f*(x^6*y^3))+(((JkCoeff621 a b c d e f*x^6)*(y^2*z))+((JkCoeff612 a b c d e f*x^6)*(y*z^2))))+(((JkCoeff603 a b c d e f*(x^6*z^3))+(JkCoeff540 a b c d e f*(x^5*y^4)))+(((JkCoeff531 a b c d e f*x^5)*(y^3*z))+((JkCoeff522 a b c d e f*x^5)*(y^2*z^2))))))+(((((JkCoeff513 a b c d e f*x^5)*(y*z^3))+((JkCoeff504 a b c d e f*(x^5*z^4))+(JkCoeff450 a b c d e f*(x^4*y^5))))+((((JkCoeff441 a b c d e f*x^4)*(y^4*z))+((JkCoeff432 a b c d e f*x^4)*(y^3*z^2)))+(((JkCoeff423 a b c d e f*x^4)*(y^2*z^3))+((JkCoeff414 a b c d e f*x^4)*(y*z^4)))))+(((JkCoeff405 a b c d e f*(x^4*z^5))+((JkCoeff360 a b c d e f*(x^3*y^6))+((JkCoeff351 a b c d e f*x^3)*(y^5*z))))+((((JkCoeff342 a b c d e f*x^3)*(y^4*z^2))+((JkCoeff333 a b c d e f*x^3)*(y^3*z^3)))+(((JkCoeff324 a b c d e f*x^3)*(y^2*z^4))+((JkCoeff315 a b c d e f*x^3)*(y*z^5)))))))+(((((JkCoeff306 a b c d e f*(x^3*z^6))+((JkCoeff270 a b c d e f*(x^2*y^7))+((JkCoeff261 a b c d e f*x^2)*(y^6*z))))+((((JkCoeff252 a b c d e f*x^2)*(y^5*z^2))+((JkCoeff243 a b c d e f*x^2)*(y^4*z^3)))+(((JkCoeff234 a b c d e f*x^2)*(y^3*z^4))+((JkCoeff225 a b c d e f*x^2)*(y^2*z^5)))))+((((JkCoeff216 a b c d e f*x^2)*(y*z^6))+((JkCoeff207 a b c d e f*(x^2*z^7))+(JkCoeff180 a b c d e f*(x*y^8))))+((((JkCoeff171 a b c d e f*x)*(y^7*z))+((JkCoeff162 a b c d e f*x)*(y^6*z^2)))+(((JkCoeff153 a b c d e f*x)*(y^5*z^3))+((JkCoeff144 a b c d e f*x)*(y^4*z^4))))))+(((((JkCoeff135 a b c d e f*x)*(y^3*z^5))+(((JkCoeff126 a b c d e f*x)*(y^2*z^6))+((JkCoeff117 a b c d e f*x)*(y*z^7))))+(((JkCoeff108 a b c d e f*(x*z^8))+(JkCoeff090 a b c d e f*y^9))+((JkCoeff081 a b c d e f*(y^8*z))+(JkCoeff072 a b c d e f*(y^7*z^2)))))+(((JkCoeff063 a b c d e f*(y^6*z^3))+((JkCoeff054 a b c d e f*(y^5*z^4))+(JkCoeff045 a b c d e f*(y^4*z^5))))+(((JkCoeff036 a b c d e f*(y^3*z^6))+(JkCoeff027 a b c d e f*(y^2*z^7)))+((JkCoeff018 a b c d e f*(y*z^8))+(JkCoeff009 a b c d e f*z^9)))))))
noncomputable def HJet (a b c d e f k x y z : K) : K :=
  H a b c d e f x y z+k*Hk a b c d e f x y z
noncomputable def ThetaJet (a b c d e f k x y z : K) : K :=
  Theta a b c d e f x y z+k*Thetak a b c d e f x y z
noncomputable def JJet (a b c d e f k x y z : K) : K :=
  J a b c d e f x y z+k*Jk a b c d e f x y z
end PolarCovariants
