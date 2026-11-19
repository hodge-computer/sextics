import Proposal.JacobianModel
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum
/-! Exact integral-incidence seed for holdout-moving-branch. The coefficient method
credits fqlx and the accepted cyclic construction; transitive cubic adaptation by fqlx, specialized here for benediamond with Codex assistance. -/
noncomputable section
namespace CycleJacobianSeed
open Polynomial
abbrev K := ZMod 5
def r : Polynomial K := 2*X^2 + 1
def x : Polynomial K := X^4 + 3*X^3 + X^2 + 4*X + 4
def y : Polynomial K := 2*X^6 + 4*X^4 + 3*X^2 + 1
def reducedEquation {R : Type*} [CommRing R] (r t x y : R) : R :=
  r^6 + 2*r^4*t^2 + r^3*t^3 + r^3*t*x + 3*r^2*t^4 + 3*r*t^3*x + t^6 + 3*x^3 + 2*y^2

lemma five_zero : (5 : Polynomial K)=0 := by
  simpa only [map_ofNat,map_zero] using congrArg (Polynomial.C : K →+* Polynomial K)
    (by decide : (5 : K)=0)
theorem seed_incidence : reducedEquation r X x y=0 := by
  have he : reducedEquation r X x y=5*(15*Polynomial.X^12 + 7*Polynomial.X^11 + 74*Polynomial.X^10 + 41*Polynomial.X^9 + 160*Polynomial.X^8 + 142*Polynomial.X^7 + 227*Polynomial.X^6 + 212*Polynomial.X^5 + 268*Polynomial.X^4 + 190*Polynomial.X^3 + 150*Polynomial.X^2 + 116*Polynomial.X + 39) := by
    dsimp [reducedEquation,r,x,y]; ring
  rw [he,five_zero,zero_mul]
theorem specialized_equation (r t x y : Polynomial K) :
    CycleJacobian.equation 1 1 1 r t x y=reducedEquation r t x y := by
  have he : CycleJacobian.equation 1 1 1 r t x y-reducedEquation r t x y=
      5*(150028*r^6 + 944622*r^5*t + 2385509*r^4*t^2 + 3135331*r^3*t^3 - 12701*r^3*t*x + 2294616*r^2*t^4 - 3024*r^2*t^2*x + 900234*r*t^5 + 9525*r*t^3*x + 150028*t^6 - 22227*x^3 + 22226*y^2) := by
    dsimp [CycleJacobian.equation,CycleJacobian.a8,CycleJacobian.b256,reducedEquation]; ring
  rw [five_zero,zero_mul] at he
  exact sub_eq_zero.mp he
theorem full_seed_incidence : CycleJacobian.equation 1 1 1 r X x y=0 := by
  rw [specialized_equation]; exact seed_incidence
def coefficientJacobian : Matrix (Fin 13) (Fin 13) K := ![
![0,0,0,0,0,0,4,0,0,0,0,0,0],
![1,0,4,0,0,0,0,4,0,0,0,0,0],
![2,1,4,4,0,0,2,0,4,0,0,0,0],
![0,2,1,4,4,0,0,2,0,4,0,0,0],
![1,0,2,1,4,4,1,0,2,0,4,0,0],
![3,1,2,2,1,4,0,1,0,2,0,4,0],
![3,3,4,2,2,1,3,0,1,0,2,0,4],
![1,3,4,4,2,2,0,3,0,1,0,2,0],
![4,1,2,4,4,2,0,0,3,0,1,0,2],
![0,4,4,2,4,4,0,0,0,3,0,1,0],
![2,0,0,4,2,4,0,0,0,0,3,0,1],
![2,2,0,0,4,2,0,0,0,0,0,3,0],
![0,2,0,0,0,4,0,0,0,0,0,0,3]
]
def inverseJacobian : Matrix (Fin 13) (Fin 13) K := ![
![0,2,2,1,0,3,2,4,0,2,2,1,0],
![4,0,2,2,1,0,3,2,4,0,2,2,1],
![2,1,2,3,2,4,2,2,2,1,2,3,2],
![2,0,4,1,3,4,2,3,2,0,4,1,3],
![2,2,2,4,0,3,1,2,2,2,2,4,0],
![4,1,2,4,1,1,3,4,4,1,2,4,1],
![4,0,0,0,0,0,0,0,0,0,0,0,0],
![3,0,0,3,3,4,0,2,3,1,0,3,3],
![3,3,4,0,1,3,3,0,0,3,0,0,1],
![2,4,0,2,2,0,0,0,2,1,0,3,2],
![0,2,4,0,2,2,0,0,0,2,1,0,3],
![2,2,0,0,2,0,0,4,2,2,0,2,2],
![2,2,1,0,3,2,4,0,2,2,1,0,0]
]
theorem inverse_product : coefficientJacobian*inverseJacobian=1 := by decide
end CycleJacobianSeed
