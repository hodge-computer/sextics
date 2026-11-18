import Proposal.JacobianModel
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

/-! Partial seed data for cycle-three; not a certificate.
The full equation and coefficient derivatives were checked independently by
Python-FLINT and SymPy. The Lean incidence and inverse checks are now complete;
JacobianSeedBinding binds this matrix to the actual coefficient derivatives.
Prepared with OpenAI Codex assistance for hodgepodgeconjecture. -/

noncomputable section
namespace CycleJacobianSeed
open Polynomial
abbrev K := ZMod 5

def r : Polynomial K := 1 + 2*X + 4*X^2
def x : Polynomial K := 3 + X + 3*X^2 + 4*X^3 + 4*X^4
def y : Polynomial K := 2 + 3*X + 3*X^2 + 4*X^3 + 4*X^4 + X^5 + X^6

def reducedEquation {R : Type*} [CommRing R] (r t x y : R) : R :=
  y^2-x^3-2*t^2*r^2*x-
  (2*r^6+t*r^5+2*t^2*r^4+4*t^3*r^3+4*t^4*r^2+t^5*r+2*t^6)

theorem seed_incidence : reducedEquation r X x y = 0 := by
  have he : reducedEquation r X x y = 5*((-1651) * Polynomial.X^12 + (-5158) * Polynomial.X^11 + (-9307) * Polynomial.X^10 + (-11392) * Polynomial.X^9 + (-10486) * Polynomial.X^8 + (-7468) * Polynomial.X^7 + (-4245) * Polynomial.X^6 + (-1916) * Polynomial.X^5 + (-707) * Polynomial.X^4 + (-207) * Polynomial.X^3 + (-51) * Polynomial.X^2 + (-8) * Polynomial.X^1 + (-5) * Polynomial.X^0) := by
    dsimp [reducedEquation, r, x, y]
    ring
  have hz : (5 : Polynomial K) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (Polynomial.C : K →+* Polynomial K) (by decide : (5 : K) = 0)
  rw [he, hz, zero_mul]


theorem specialized_equation (r t x y : Polynomial K) :
    CycleJacobian.equation 2 3 1 r t x y = reducedEquation r t x y := by
  have he : CycleJacobian.equation 2 3 1 r t x y - reducedEquation r t x y =
      5*((346)*r^6 +
      (550765)*r^5*t^1 +
      (252060330)*r^4*t^2 +
      (26123999732)*r^3*t^3 +
      (-960)*r^3*t^1*x^1 +
      (805451142644)*r^2*t^4 +
      (-120038)*r^2*t^2*x^1 +
      (1530165112013)*r^1*t^5 +
      (752295975322)*t^6 +
      (-51)*x^3 +
      (51)*y^2) := by
    dsimp [CycleJacobian.equation, CycleJacobian.a8, CycleJacobian.b256, reducedEquation]
    ring
  have hz : (5 : Polynomial K) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (Polynomial.C : K →+* Polynomial K) (by decide : (5 : K) = 0)
  rw [hz, zero_mul] at he
  exact sub_eq_zero.mp he

theorem full_seed_incidence : CycleJacobian.equation 2 3 1 r X x y = 0 := by
  rw [specialized_equation]
  exact seed_incidence

/-- Coefficient rows 0..12; columns r1,r2,x1..x4,y0..y6.
JacobianSeedBinding proves that this is the actual incidence derivative matrix. -/
def coefficientJacobian : Matrix (Fin 13) (Fin 13) K := ![
![0,0,0,0,0,0,4,0,0,0,0,0,0],
![3,0,3,0,0,0,1,4,0,0,0,0,0],
![0,3,2,3,0,0,1,1,4,0,0,0,0],
![0,0,1,2,3,0,3,1,1,4,0,0,0],
![2,0,2,1,2,3,3,3,1,1,4,0,0],
![4,2,3,2,1,2,2,3,3,1,1,4,0],
![1,4,2,3,2,1,2,2,3,3,1,1,4],
![2,1,3,2,3,2,0,2,2,3,3,1,1],
![4,2,4,3,2,3,0,0,2,2,3,3,1],
![4,4,2,4,3,2,0,0,0,2,2,3,3],
![0,4,0,2,4,3,0,0,0,0,2,2,3],
![2,0,0,0,2,4,0,0,0,0,0,2,2],
![0,2,0,0,0,2,0,0,0,0,0,0,2]
]

def inverseJacobian : Matrix (Fin 13) (Fin 13) K := ![
![2,3,3,4,2,4,0,4,1,2,2,1,3],
![3,2,3,3,4,2,4,0,4,1,2,2,1],
![1,0,3,3,2,0,4,0,3,4,3,2,3],
![1,2,3,3,0,0,1,2,4,3,0,3,0],
![1,1,2,3,3,0,0,1,2,4,3,0,3],
![0,4,4,1,0,2,0,4,2,4,1,4,3],
![4,0,0,0,0,0,0,0,0,0,0,0,0],
![3,3,3,1,2,2,2,2,2,3,0,4,3],
![1,0,1,0,3,3,0,3,2,3,2,3,2],
![2,0,4,3,1,0,3,2,1,3,4,0,2],
![3,1,0,2,3,3,3,0,1,0,0,1,0],
![0,4,4,0,4,1,4,1,4,1,1,0,4],
![2,4,3,1,1,1,1,1,4,0,2,4,4]
]

theorem inverse_product : coefficientJacobian * inverseJacobian = 1 := by
  decide

end CycleJacobianSeed
