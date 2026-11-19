import Proposal.JacobianModel
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum
/-! Exact integral-incidence seed for mixed-biweight. The coefficient method
credits fqlx and the accepted cyclic construction; adapted by fqlx with Codex assistance. -/
noncomputable section
namespace CycleJacobianSeed
open Polynomial
abbrev K := ZMod 5
def r : Polynomial K := 1+X^2
def x : Polynomial K := 3+4*X^2+3*X^4
def y : Polynomial K := 2+3*X^6
def reducedEquation {R : Type*} [CommRing R] (r t x y : R) : R :=
  2*(y^2-x^3-(4*r^3*t+4*r^2*t^2+2*r*t^3)*x-
    (2*r^6+3*r^5*t+3*r^4*t^2+2*r^3*t^3+3*r^2*t^4+4*r*t^5+2*t^6))
lemma five_zero : (5 : Polynomial K)=0 := by
  simpa only [map_ofNat,map_zero] using congrArg (Polynomial.C : K →+* Polynomial K)
    (by decide : (5 : K)=0)
theorem seed_incidence : reducedEquation r X x y=0 := by
  have he : reducedEquation r X x y=5*((-8)*Polynomial.X^12 + (-6)*Polynomial.X^11 + (-54)*Polynomial.X^10 + (-30)*Polynomial.X^9 + (-124)*Polynomial.X^8 + (-60)*Polynomial.X^7 + (-156)*Polynomial.X^6 + (-60)*Polynomial.X^5 + (-124)*Polynomial.X^4 + (-30)*Polynomial.X^3 + (-54)*Polynomial.X^2 + (-6)*Polynomial.X + (-10)) := by
    dsimp [reducedEquation,r,x,y]; ring
  rw [he,five_zero,zero_mul]
theorem specialized_equation (r t x y : Polynomial K) :
    CycleJacobian.equation 1 1 1 r t x y=reducedEquation r t x y := by
  have he : CycleJacobian.equation 1 1 1 r t x y-reducedEquation r t x y=
      5*((7874)*r^6 + (47532)*r^5*t + (119001)*r^4*t^2 + (158421)*r^3*t^3 + (439)*r^3*t*x + (118488)*r^2*t^4 + (1033)*r^2*t^2*x + (47284)*r*t^5 + (584)*r*t^3*x + (7874)*t^6 + (-1166)*x^3 + (1166)*y^2) := by
    dsimp [CycleJacobian.equation,CycleJacobian.a8,CycleJacobian.b256,reducedEquation]; ring
  rw [five_zero,zero_mul] at he
  exact sub_eq_zero.mp he
theorem full_seed_incidence : CycleJacobian.equation 1 1 1 r X x y=0 := by
  rw [specialized_equation]; exact seed_incidence
def coefficientJacobian : Matrix (Fin 13) (Fin 13) K := ![
![0,0,0,0,0,0,3,0,0,0,0,0,0],
![1,0,1,0,0,0,0,3,0,0,0,0,0],
![3,1,2,1,0,0,0,0,3,0,0,0,0],
![3,3,3,2,1,0,0,0,0,3,0,0,0],
![1,3,2,3,2,1,0,0,0,0,3,0,0],
![4,1,0,2,3,2,0,0,0,0,0,3,0],
![1,4,2,0,2,3,2,0,0,0,0,0,3],
![4,1,3,2,0,2,0,2,0,0,0,0,0],
![1,4,2,3,2,0,0,0,2,0,0,0,0],
![3,1,1,2,3,2,0,0,0,2,0,0,0],
![3,3,0,1,2,3,0,0,0,0,2,0,0],
![1,3,0,0,1,2,0,0,0,0,0,2,0],
![0,1,0,0,0,1,0,0,0,0,0,0,2]
]
def inverseJacobian : Matrix (Fin 13) (Fin 13) K := ![
![0,3,2,1,3,0,0,3,2,1,3,0,0],
![3,0,0,3,1,2,3,0,0,3,1,2,3],
![1,3,1,3,3,3,1,3,1,3,3,3,1],
![1,1,0,2,3,2,1,1,0,2,3,2,1],
![1,1,2,3,2,0,1,1,2,3,2,0,1],
![3,1,3,3,3,1,3,1,3,3,3,1,3],
![2,0,0,0,0,0,0,0,0,0,0,0,0],
![3,0,4,2,3,4,3,3,4,2,3,4,3],
![3,3,1,2,2,0,3,3,4,2,2,0,3],
![0,3,3,1,2,2,0,3,3,4,2,2,0],
![2,0,3,3,1,2,2,0,3,3,4,2,2],
![2,2,0,3,3,1,2,2,0,3,3,4,2],
![2,2,1,2,3,1,2,2,1,2,3,1,0]
]
theorem inverse_product : coefficientJacobian*inverseJacobian=1 := by decide
end CycleJacobianSeed
