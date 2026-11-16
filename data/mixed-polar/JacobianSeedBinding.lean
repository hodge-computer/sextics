import Proposal.JacobianIncidence
import Proposal.JacobianSeed
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.NormNum

/-! Binding the explicit seed matrix to the actual incidence derivatives.
Adapted from the coefficient-Jacobian verification pattern of fqlx and
hodgepodgeconjecture. Prepared for benediamond with OpenAI Codex assistance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace MixedPolarJacobianSeedBinding
open Polynomial MixedPolarJacobianIncidence
abbrev K := ZMod 5
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
def seed : Fin 13 → K := ![4,4,3,2,2,4,1,0,1,0,1,0,1]
def endpoints : Fin 2 → K := ![1,4]
def seedCurve : Fin 3 → Polynomial K :=
  ![MixedPolarSeed.r,MixedPolarSeed.x,MixedPolarSeed.y]
lemma curveEval_seed : curveEval endpoints (RingHom.id K) seed=seedCurve := by
  rw [curveEval_eq_valueCurve]
  funext i
  fin_cases i <;> simp [valueCurve,endpoints,seed,seedCurve,
    MixedPolarSeed.r,MixedPolarSeed.x,MixedPolarSeed.y,map_ofNat] <;> ring
lemma seed_incidence : H (1 : Polynomial K) 3 X seedCurve=0 := by
  exact MixedPolarSeed.seed_incidence
lemma seed_gradient (i : Fin 3) :
    gradient (1 : Polynomial K) 3 X seedCurve i=MixedPolarSeed.gradient 1 3
      MixedPolarSeed.r X MixedPolarSeed.x MixedPolarSeed.y i := by
  fin_cases i <;> rfl

def gradientJacobian : Matrix (Fin 13) (Fin 13) K := fun i j =>
  (gradient (1 : Polynomial K) 3 X seedCurve (slotCoordinate j)*X^slotDegree j).coeff i.val
lemma gradientJacobian_eq : gradientJacobian=MixedPolarSeed.coefficientJacobian := by
  ext i j
  simp only [gradientJacobian,seed_gradient]
  rfl
lemma gradientJacobian_unit : IsUnit gradientJacobian.det := by
  rw [gradientJacobian_eq]
  have h : MixedPolarSeed.coefficientJacobian.det*MixedPolarSeed.inverseJacobian.det=1 := by
    rw [← Matrix.det_mul,MixedPolarSeed.inverse_product,Matrix.det_one]
  apply isUnit_iff_ne_zero.mpr
  intro hz
  rw [hz,zero_mul] at h
  exact zero_ne_one h

def integerEndpoints : Fin 2 → ℤ := ![1,4]
def integerEquations : Fin 13 → MvPolynomial (Fin 13) ℤ :=
  equations 1 3 integerEndpoints
lemma integer_curve_binding : curveEval integerEndpoints (Int.castRingHom K) seed=seedCurve := by
  rw [curveEval_eq_valueCurve]
  rw [← curveEval_seed,curveEval_eq_valueCurve]
  congr 1
  funext i
  fin_cases i <;> norm_num [integerEndpoints,endpoints]
lemma integer_seed_equations (i : Fin 13) :
    MvPolynomial.aeval seed (integerEquations i)=0 := by
  change MvPolynomial.eval₂Hom (Int.castRingHom K) seed
    (equations 1 3 integerEndpoints i)=0
  rw [equations_eval,integer_curve_binding]
  simpa only [map_one,map_ofNat,Polynomial.coeff_zero] using
    congrArg (fun p : Polynomial K => p.coeff i.val) seed_incidence
lemma integer_seed_jacobian : IsUnit (Matrix.det (fun i j : Fin 13 =>
    MvPolynomial.aeval seed (MvPolynomial.pderiv i (integerEquations j)))) := by
  have hm : (fun i j : Fin 13 => MvPolynomial.aeval seed
      (MvPolynomial.pderiv i (integerEquations j)))=gradientJacobian.transpose := by
    funext i j
    change MvPolynomial.eval₂Hom (Int.castRingHom K) seed
      (MvPolynomial.pderiv i (equations 1 3 integerEndpoints j))=_
    rw [equations_pderiv_eval,integer_curve_binding]
    simpa only [map_one,map_ofNat,seed_gradient,gradientJacobian,Matrix.transpose_apply]
  rw [hm,Matrix.det_transpose]
  exact gradientJacobian_unit

#print axioms integer_seed_equations
#print axioms integer_seed_jacobian
end MixedPolarJacobianSeedBinding
