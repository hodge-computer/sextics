import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
/-! Scratch arithmetic input for the mixed-polar Jacobian construction.
Generated from its exact paired-sign cubic; no certificate theorem is asserted.
The incidence method credits the accepted constructions of fqlx and
hodgepodgeconjecture. Prepared with OpenAI Codex assistance. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable section
namespace MixedPolarSeed
open Polynomial
abbrev K := ZMod 5
section Ring
variable {R : Type*} [CommRing R]
def a432 (cOne cTwo r t : R) : R :=
  -54*cOne^3*cTwo*r*t*(r+cTwo^6*t)*(4*cOne*(r+t)-r)
def b432 (cOne cTwo r t : R) : R :=
  -2916*(r+t)^2*(r+cOne^6*t)^2*(r+cTwo^6*t)^2
  -54*cOne^3*cTwo^3*r^2*t*(r+t)^2*(r+cTwo^6*t)
  +324*cOne^4*r*t*(r+t)*(r+cOne^6*t)*(r+cTwo^6*t)^2
  -16*cOne^9*r*t^2*(r+t)*(r+cTwo^6*t)^2
  -54*cOne^3*r^2*t*(r+cOne^6*t)*(r+cTwo^6*t)^2
  +3*cOne^8*r^2*t^2*(r+cTwo^6*t)^2
def equation (cOne cTwo r t x y : R) : R :=
  432*y^2-432*x^3-a432 cOne cTwo r t*x-b432 cOne cTwo r t
def a432r (cOne cTwo r t : R) : R :=
  -432*cOne^4*cTwo^7*r*t^2 -216*cOne^4*cTwo^7*t^3 -648*cOne^4*cTwo*r^2*t -432*cOne^4*cTwo*r*t^2 +108*cOne^3*cTwo^7*r*t^2 +162*cOne^3*cTwo*r^2*t
def b432r (cOne cTwo r t : R) : R :=
  -5832*cOne^12*cTwo^12*r*t^4 -5832*cOne^12*cTwo^12*t^5 -17496*cOne^12*cTwo^6*r^2*t^3 -23328*cOne^12*cTwo^6*r*t^4 -5832*cOne^12*cTwo^6*t^5 -11664*cOne^12*r^3*t^2 -17496*cOne^12*r^2*t^3 -5832*cOne^12*r*t^4 +648*cOne^10*cTwo^12*r*t^4 +324*cOne^10*cTwo^12*t^5 +1944*cOne^10*cTwo^6*r^2*t^3 +1296*cOne^10*cTwo^6*r*t^4 +1296*cOne^10*r^3*t^2 +972*cOne^10*r^2*t^3 -140*cOne^9*cTwo^12*r*t^4 -16*cOne^9*cTwo^12*t^5 -420*cOne^9*cTwo^6*r^2*t^3 -64*cOne^9*cTwo^6*r*t^4 -280*cOne^9*r^3*t^2 -48*cOne^9*r^2*t^3 +6*cOne^8*cTwo^12*r*t^4 +18*cOne^8*cTwo^6*r^2*t^3 +12*cOne^8*r^3*t^2 -17496*cOne^6*cTwo^12*r^2*t^3 -23328*cOne^6*cTwo^12*r*t^4 -5832*cOne^6*cTwo^12*t^5 -46656*cOne^6*cTwo^6*r^3*t^2 -69984*cOne^6*cTwo^6*r^2*t^3 -23328*cOne^6*cTwo^6*r*t^4 -29160*cOne^6*r^4*t -46656*cOne^6*r^3*t^2 -17496*cOne^6*r^2*t^3 +972*cOne^4*cTwo^12*r^2*t^3 +648*cOne^4*cTwo^12*r*t^4 +2592*cOne^4*cTwo^6*r^3*t^2 +1944*cOne^4*cTwo^6*r^2*t^3 +1620*cOne^4*r^4*t +1296*cOne^4*r^3*t^2 -162*cOne^3*cTwo^12*r^2*t^3 -216*cOne^3*cTwo^9*r^3*t^2 -324*cOne^3*cTwo^9*r^2*t^3 -108*cOne^3*cTwo^9*r*t^4 -432*cOne^3*cTwo^6*r^3*t^2 -270*cOne^3*cTwo^3*r^4*t -432*cOne^3*cTwo^3*r^3*t^2 -162*cOne^3*cTwo^3*r^2*t^3 -270*cOne^3*r^4*t -11664*cTwo^12*r^3*t^2 -17496*cTwo^12*r^2*t^3 -5832*cTwo^12*r*t^4 -29160*cTwo^6*r^4*t -46656*cTwo^6*r^3*t^2 -17496*cTwo^6*r^2*t^3 -17496*r^5 -29160*r^4*t -11664*r^3*t^2
def gradient (cOne cTwo r t x y : R) : Fin 3 → R :=
  ![-a432r cOne cTwo r t*x-b432r cOne cTwo r t,
    -1296*x^2-a432 cOne cTwo r t,864*y]
end Ring

def r : Polynomial K := 1+4*X+4*X^2
def x : Polynomial K := 4+3*X+2*X^2+2*X^3+4*X^4
def y : Polynomial K := 1+X^2+X^4+X^6

lemma five_zero : (5 : Polynomial K)=0 := by
  simpa only [map_ofNat,map_zero] using congrArg (Polynomial.C : K →+* Polynomial K)
    (by decide : (5 : K)=0)

theorem seed_incidence : equation 1 3 r X x y=0 := by
  have he : equation 1 3 r X x y=5*((-4860) + (854820)*X^1 + (330958367)*X^2 + (6389425240)*X^3 + (52341411773)*X^4 + (231939304952)*X^5 + (601022955604)*X^6 + (927699194000)*X^7 + (837310610336)*X^8 + (408752753344)*X^9 + (84660466784)*X^10 + (887694336)*X^11 + (2383344)*X^12) := by
    dsimp [equation,a432,b432,r,x,y]
    ring
  rw [he,five_zero,zero_mul]

def g0 : Polynomial K := (1) + (2)*X^1 + (4)*X^3 + (1)*X^5 + (4)*X^7 + (2)*X^9 + (4)*X^10
def g1 : Polynomial K := (4) + (2)*X^1 + (4)*X^2 + (3)*X^4 + (4)*X^6 + (3)*X^7 + (4)*X^8
def g2 : Polynomial K := (4) + (4)*X^2 + (4)*X^4 + (4)*X^6
lemma g0_eq : -a432r 1 3 r X*x-b432r 1 3 r X=g0 := by
  have he : (-a432r 1 3 r X*x-b432r 1 3 r X)-g0=5*((3499) + (4335530)*X^1 + (1323339746)*X^2 + (19180124842)*X^3 + (109957475742)*X^4 + (308632315839)*X^5 + (439814562216)*X^6 + (306836062060)*X^7 + (84659062784)*X^8 + (1109615846)*X^9 + (3583180)*X^10) := by
    dsimp [a432r,b432r,a432,r,x,y,g0]
    ring
  rw [five_zero,zero_mul] at he
  exact sub_eq_zero.mp he
lemma g1_eq : -1296*x^2-a432 1 3 r X=g1 := by
  have he : (-1296*x^2-a432 1 3 r X)-g1=5*((-4148) + (-6124)*X^1 + (65674)*X^2 + (660960)*X^3 + (2084745)*X^4 + (2664576)*X^5 + (1149292)*X^6 + (2073)*X^7 + (-4148)*X^8) := by
    dsimp [a432r,b432r,a432,r,x,y,g1]
    ring
  rw [five_zero,zero_mul] at he
  exact sub_eq_zero.mp he
lemma g2_eq : 864*y=g2 := by
  have he : (864*y)-g2=5*((172) + (172)*X^2 + (172)*X^4 + (172)*X^6) := by
    dsimp [a432r,b432r,a432,r,x,y,g2]
    ring
  rw [five_zero,zero_mul] at he
  exact sub_eq_zero.mp he
lemma gradient_seed : gradient 1 3 r X x y=![g0,g1,g2] := by
  funext i
  fin_cases i
  · exact g0_eq
  · exact g1_eq
  · exact g2_eq


def slotCoordinate : Fin 13 → Fin 3 := ![0,0,1,1,1,1,2,2,2,2,2,2,2]
def slotDegree : Fin 13 → ℕ := ![1,2,1,2,3,4,0,1,2,3,4,5,6]
def coefficientJacobian : Matrix (Fin 13) (Fin 13) K := fun i j =>
  ((gradient 1 3 r X x y (slotCoordinate j))*X^(slotDegree j)).coeff i.val
def seedMatrix : Matrix (Fin 13) (Fin 13) K := ![
![0,0,0,0,0,0,4,0,0,0,0,0,0],
![1,0,4,0,0,0,0,4,0,0,0,0,0],
![2,1,2,4,0,0,4,0,4,0,0,0,0],
![0,2,4,2,4,0,0,4,0,4,0,0,0],
![4,0,0,4,2,4,4,0,4,0,4,0,0],
![0,4,3,0,4,2,0,4,0,4,0,4,0],
![1,0,0,3,0,4,4,0,4,0,4,0,4],
![0,1,4,0,3,0,0,4,0,4,0,4,0],
![4,0,3,4,0,3,0,0,4,0,4,0,4],
![0,4,4,3,4,0,0,0,0,4,0,4,0],
![2,0,0,4,3,4,0,0,0,0,4,0,4],
![4,2,0,0,4,3,0,0,0,0,0,4,0],
![0,4,0,0,0,4,0,0,0,0,0,0,4]
]
def inverseJacobian : Matrix (Fin 13) (Fin 13) K := ![
![0,2,2,2,0,2,3,4,0,2,2,2,0],
![3,0,3,2,3,0,1,3,3,0,3,2,3],
![1,1,0,1,4,1,0,2,1,1,0,1,4],
![4,2,0,1,4,0,2,2,4,2,0,1,4],
![0,4,4,0,3,4,3,2,0,4,4,0,3],
![1,1,1,0,1,4,2,0,1,1,1,0,1],
![4,0,0,0,0,0,0,0,0,0,0,0,0],
![4,0,2,1,1,1,3,2,4,1,2,1,1],
![2,4,1,2,2,1,0,3,1,4,2,2,2],
![4,4,0,3,1,4,0,4,4,3,0,4,1],
![4,4,4,0,3,1,4,0,4,4,3,0,4],
![4,2,3,2,1,1,2,0,4,2,3,1,1],
![1,4,1,3,1,1,2,2,1,4,1,3,0]
]
theorem actual_coefficient_matrix : coefficientJacobian=seedMatrix := by
  funext i j
  simp only [coefficientJacobian,gradient_seed]
  fin_cases i <;> fin_cases j <;>
    norm_num [seedMatrix,slotCoordinate,slotDegree,g0,g1,g2,Polynomial.coeff_mul_X_pow',Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Polynomial.coeff_one,Polynomial.coeff_X]

theorem inverse_product : coefficientJacobian*inverseJacobian=1 := by
  rw [actual_coefficient_matrix]
  decide

#print axioms seed_incidence
#print axioms actual_coefficient_matrix
#print axioms inverse_product
end MixedPolarSeed
