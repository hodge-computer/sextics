import HodgeComputer.Constructions.CyclicCubic.Covariants
import HodgeComputer.Constructions.HoldoutCover.PolynomialCalculus

/-! The universal relative differential identity on the affine cubic chart.
The integer covariants use the classical Fisher/SageMath normalization credited
in CubicCovariants. These polynomial identities are proved by Lean arithmetic.
Prepared with OpenAI Codex assistance for hodgepodgeconjecture. -/
noncomputable section
namespace CycleCovariants
open MvPolynomial
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [CommRing K]
abbrev Affine (K : Type*) [CommRing K] := MvPolynomial (Fin 2) K
local notation "x" => (X (R := K) (0:Fin 2))
local notation "y" => (X (R := K) (1:Fin 2))
def Hpoly (a b c d e f : K) : Affine K :=
  ((((C (HCoeff300 a b c d e f))*x^(3:ℕ) + (C (HCoeff210 a b c d e f))*x^(2:ℕ)*y) + ((C (HCoeff201 a b c d e f))*x^(2:ℕ) + ((C (HCoeff120 a b c d e f))*x*y^(2:ℕ) + (C (HCoeff111 a b c d e f))*x*y))) + (((C (HCoeff102 a b c d e f))*x + (C (HCoeff030 a b c d e f))*y^(3:ℕ)) + ((C (HCoeff021 a b c d e f))*y^(2:ℕ) + ((C (HCoeff012 a b c d e f))*y + (C (HCoeff003 a b c d e f))*1))))
def Thetapoly (a b c d e f : K) : Affine K :=
  (((((C (ThetaCoeff600 a b c d e f))*x^(6:ℕ) + ((C (ThetaCoeff510 a b c d e f))*x^(5:ℕ)*y + (C (ThetaCoeff501 a b c d e f))*x^(5:ℕ))) + (((C (ThetaCoeff420 a b c d e f))*x^(4:ℕ)*y^(2:ℕ) + (C (ThetaCoeff411 a b c d e f))*x^(4:ℕ)*y) + ((C (ThetaCoeff402 a b c d e f))*x^(4:ℕ) + (C (ThetaCoeff330 a b c d e f))*x^(3:ℕ)*y^(3:ℕ)))) + (((C (ThetaCoeff321 a b c d e f))*x^(3:ℕ)*y^(2:ℕ) + ((C (ThetaCoeff312 a b c d e f))*x^(3:ℕ)*y + (C (ThetaCoeff303 a b c d e f))*x^(3:ℕ))) + (((C (ThetaCoeff240 a b c d e f))*x^(2:ℕ)*y^(4:ℕ) + (C (ThetaCoeff231 a b c d e f))*x^(2:ℕ)*y^(3:ℕ)) + ((C (ThetaCoeff222 a b c d e f))*x^(2:ℕ)*y^(2:ℕ) + (C (ThetaCoeff213 a b c d e f))*x^(2:ℕ)*y)))) + ((((C (ThetaCoeff204 a b c d e f))*x^(2:ℕ) + ((C (ThetaCoeff150 a b c d e f))*x*y^(5:ℕ) + (C (ThetaCoeff141 a b c d e f))*x*y^(4:ℕ))) + (((C (ThetaCoeff132 a b c d e f))*x*y^(3:ℕ) + (C (ThetaCoeff123 a b c d e f))*x*y^(2:ℕ)) + ((C (ThetaCoeff114 a b c d e f))*x*y + (C (ThetaCoeff105 a b c d e f))*x))) + (((C (ThetaCoeff060 a b c d e f))*y^(6:ℕ) + ((C (ThetaCoeff051 a b c d e f))*y^(5:ℕ) + (C (ThetaCoeff042 a b c d e f))*y^(4:ℕ))) + (((C (ThetaCoeff033 a b c d e f))*y^(3:ℕ) + (C (ThetaCoeff024 a b c d e f))*y^(2:ℕ)) + ((C (ThetaCoeff015 a b c d e f))*y + (C (ThetaCoeff006 a b c d e f))*1)))))
def Jpoly (a b c d e f : K) : Affine K :=
  ((((((C (JCoeff900 a b c d e f))*x^(9:ℕ) + ((C (JCoeff810 a b c d e f))*x^(8:ℕ)*y + (C (JCoeff801 a b c d e f))*x^(8:ℕ))) + ((C (JCoeff720 a b c d e f))*x^(7:ℕ)*y^(2:ℕ) + ((C (JCoeff711 a b c d e f))*x^(7:ℕ)*y + (C (JCoeff702 a b c d e f))*x^(7:ℕ)))) + (((C (JCoeff630 a b c d e f))*x^(6:ℕ)*y^(3:ℕ) + ((C (JCoeff621 a b c d e f))*x^(6:ℕ)*y^(2:ℕ) + (C (JCoeff612 a b c d e f))*x^(6:ℕ)*y)) + (((C (JCoeff603 a b c d e f))*x^(6:ℕ) + (C (JCoeff540 a b c d e f))*x^(5:ℕ)*y^(4:ℕ)) + ((C (JCoeff531 a b c d e f))*x^(5:ℕ)*y^(3:ℕ) + (C (JCoeff522 a b c d e f))*x^(5:ℕ)*y^(2:ℕ))))) + ((((C (JCoeff513 a b c d e f))*x^(5:ℕ)*y + ((C (JCoeff504 a b c d e f))*x^(5:ℕ) + (C (JCoeff450 a b c d e f))*x^(4:ℕ)*y^(5:ℕ))) + (((C (JCoeff441 a b c d e f))*x^(4:ℕ)*y^(4:ℕ) + (C (JCoeff432 a b c d e f))*x^(4:ℕ)*y^(3:ℕ)) + ((C (JCoeff423 a b c d e f))*x^(4:ℕ)*y^(2:ℕ) + (C (JCoeff414 a b c d e f))*x^(4:ℕ)*y))) + (((C (JCoeff405 a b c d e f))*x^(4:ℕ) + ((C (JCoeff360 a b c d e f))*x^(3:ℕ)*y^(6:ℕ) + (C (JCoeff351 a b c d e f))*x^(3:ℕ)*y^(5:ℕ))) + (((C (JCoeff342 a b c d e f))*x^(3:ℕ)*y^(4:ℕ) + (C (JCoeff333 a b c d e f))*x^(3:ℕ)*y^(3:ℕ)) + ((C (JCoeff324 a b c d e f))*x^(3:ℕ)*y^(2:ℕ) + (C (JCoeff315 a b c d e f))*x^(3:ℕ)*y))))) + (((((C (JCoeff306 a b c d e f))*x^(3:ℕ) + ((C (JCoeff270 a b c d e f))*x^(2:ℕ)*y^(7:ℕ) + (C (JCoeff261 a b c d e f))*x^(2:ℕ)*y^(6:ℕ))) + (((C (JCoeff252 a b c d e f))*x^(2:ℕ)*y^(5:ℕ) + (C (JCoeff243 a b c d e f))*x^(2:ℕ)*y^(4:ℕ)) + ((C (JCoeff234 a b c d e f))*x^(2:ℕ)*y^(3:ℕ) + (C (JCoeff225 a b c d e f))*x^(2:ℕ)*y^(2:ℕ)))) + (((C (JCoeff216 a b c d e f))*x^(2:ℕ)*y + ((C (JCoeff207 a b c d e f))*x^(2:ℕ) + (C (JCoeff180 a b c d e f))*x*y^(8:ℕ))) + (((C (JCoeff171 a b c d e f))*x*y^(7:ℕ) + (C (JCoeff162 a b c d e f))*x*y^(6:ℕ)) + ((C (JCoeff153 a b c d e f))*x*y^(5:ℕ) + (C (JCoeff144 a b c d e f))*x*y^(4:ℕ))))) + ((((C (JCoeff135 a b c d e f))*x*y^(3:ℕ) + ((C (JCoeff126 a b c d e f))*x*y^(2:ℕ) + (C (JCoeff117 a b c d e f))*x*y)) + (((C (JCoeff108 a b c d e f))*x + (C (JCoeff090 a b c d e f))*y^(9:ℕ)) + ((C (JCoeff081 a b c d e f))*y^(8:ℕ) + (C (JCoeff072 a b c d e f))*y^(7:ℕ)))) + (((C (JCoeff063 a b c d e f))*y^(6:ℕ) + ((C (JCoeff054 a b c d e f))*y^(5:ℕ) + (C (JCoeff045 a b c d e f))*y^(4:ℕ))) + (((C (JCoeff036 a b c d e f))*y^(3:ℕ) + (C (JCoeff027 a b c d e f))*y^(2:ℕ)) + ((C (JCoeff018 a b c d e f))*y + (C (JCoeff009 a b c d e f))*1))))))
def Upoly (a b c d e f : K) : Affine K :=
  C a*x^3+C b*y^3+C c+C d*x^2*y+C e*y^2+C f*x

lemma relative_identity (a b c d e f : K) :
    let u := Upoly a b c d e f
    let h := Hpoly a b c d e f
    let q := Thetapoly a b c d e f
    let j := Jpoly a b c d e f
    h*(pderiv 0 u*pderiv 1 q-pderiv 1 u*pderiv 0 q)-
      2*q*(pderiv 0 u*pderiv 1 h-pderiv 1 u*pderiv 0 h)+3*j=
      u*(pderiv 0 h*pderiv 1 q-pderiv 1 h*pderiv 0 q) := by
  dsimp
  simp only [Upoly,Hpoly,Thetapoly,Jpoly,
    map_add,map_neg,pderiv_mul,pderiv_pow,pderiv_C,pderiv_X,Pi.single_apply]
  norm_num
  simp only [HCoeff300,HCoeff210,HCoeff201,HCoeff120,HCoeff111,HCoeff102,HCoeff030,HCoeff021,HCoeff012,HCoeff003,ThetaCoeff600,ThetaCoeff510,ThetaCoeff501,ThetaCoeff420,ThetaCoeff411,ThetaCoeff402,ThetaCoeff330,ThetaCoeff321,ThetaCoeff312,ThetaCoeff303,ThetaCoeff240,ThetaCoeff231,ThetaCoeff222,ThetaCoeff213,ThetaCoeff204,ThetaCoeff150,ThetaCoeff141,ThetaCoeff132,ThetaCoeff123,ThetaCoeff114,ThetaCoeff105,ThetaCoeff060,ThetaCoeff051,ThetaCoeff042,ThetaCoeff033,ThetaCoeff024,ThetaCoeff015,ThetaCoeff006,JCoeff900,JCoeff810,JCoeff801,JCoeff720,JCoeff711,JCoeff702,JCoeff630,JCoeff621,JCoeff612,JCoeff603,JCoeff540,JCoeff531,JCoeff522,JCoeff513,JCoeff504,JCoeff450,JCoeff441,JCoeff432,JCoeff423,JCoeff414,JCoeff405,JCoeff360,JCoeff351,JCoeff342,JCoeff333,JCoeff324,JCoeff315,JCoeff306,JCoeff270,JCoeff261,JCoeff252,JCoeff243,JCoeff234,JCoeff225,JCoeff216,JCoeff207,JCoeff180,JCoeff171,JCoeff162,JCoeff153,JCoeff144,JCoeff135,JCoeff126,JCoeff117,JCoeff108,JCoeff090,JCoeff081,JCoeff072,JCoeff063,JCoeff054,JCoeff045,JCoeff036,JCoeff027,JCoeff018,JCoeff009,
    map_add,map_neg,map_mul,map_pow,map_sub,map_ofNat]
  ring
#print axioms relative_identity
end CycleCovariants
