import Proposal.JacobianIncidence
import Proposal.JacobianSeed
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.NormNum

/-! Binding the explicit seed matrix to the actual incidence derivatives.
Prepared with OpenAI Codex assistance for hodgepodgeconjecture, following the
coefficient-Jacobian verification pattern of the credited shared construction.
-/
noncomputable section
namespace CycleJacobianSeedBinding
open Polynomial CycleJacobianIncidence
abbrev K := ZMod 5
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
def seed : Fin 13 → K := ![2,4,1,3,4,4,2,3,3,4,4,1,1]
def endpoints : Fin 2 → K := ![1,3]
def seedCurve : Fin 3 → Polynomial K :=
  ![CycleJacobianSeed.r,CycleJacobianSeed.x,CycleJacobianSeed.y]
lemma curveEval_seed : curveEval endpoints (RingHom.id K) seed=seedCurve := by
  rw [curveEval_eq_valueCurve]
  funext i
  fin_cases i <;> simp [valueCurve,endpoints,seed,seedCurve,
    CycleJacobianSeed.r,CycleJacobianSeed.x,CycleJacobianSeed.y,map_ofNat] <;> ring
lemma seed_incidence : H (2 : Polynomial K) 3 X seedCurve=0 := by
  exact CycleJacobianSeed.full_seed_incidence
lemma five_zero : (5 : Polynomial K)=0 := by
  simpa only [map_ofNat,map_zero] using
    congrArg (Polynomial.C : K →+* Polynomial K) (by decide : (5 : K)=0)

def expandedGradient : Fin 3 → Polynomial K := ![
(3)*X^0 + (2)*X^3 + (4)*X^4 + (1)*X^5 + (2)*X^6 + (4)*X^7 + (4)*X^8 + (2)*X^10,
(3)*X^0 + (2)*X^1 + (1)*X^2 + (2)*X^3 + (3)*X^4 + (2)*X^5 + (3)*X^6 + (4)*X^7 + (2)*X^8,
(4)*X^0 + (1)*X^1 + (1)*X^2 + (3)*X^3 + (3)*X^4 + (2)*X^5 + (2)*X^6]
def gradientQuotient : Fin 3 → Polynomial K := ![
(2073)*X^0 + (2765920)*X^1 + (1029638656)*X^2 + (84530293350)*X^3 + (1948937755980)*X^4 + (5749732026675)*X^5 + (7795762094182)*X^6 + (1352507341004)*X^7 + (65941155020)*X^8 + (710103040)*X^9 + (2123366)*X^10,
(-1383)*X^0 + (-1882)*X^1 + (-128717)*X^2 + (-507802)*X^3 + (-1500519)*X^4 + (-2017690)*X^5 + (-2018919)*X^6 + (-66356)*X^7 + (-2458)*X^8,
(204)*X^0 + (307)*X^1 + (307)*X^2 + (409)*X^3 + (409)*X^4 + (102)*X^5 + (102)*X^6]
lemma seed_gradient (i : Fin 3) :
    gradient (2 : Polynomial K) 3 X seedCurve i=expandedGradient i := by
  have he : gradient (2 : Polynomial K) 3 X seedCurve i-expandedGradient i=
      5*gradientQuotient i := by
    fin_cases i <;> dsimp [gradient,a8r,b256r,CycleJacobian.a8,seedCurve,
      CycleJacobianSeed.r,CycleJacobianSeed.x,CycleJacobianSeed.y,
      expandedGradient,gradientQuotient] <;> ring
  rw [five_zero,zero_mul] at he
  exact sub_eq_zero.mp he

def gradientJacobian : Matrix (Fin 13) (Fin 13) K := fun i j =>
  (expandedGradient (slotCoordinate j)*X^slotDegree j).coeff i.val
lemma gradientJacobian_eq : gradientJacobian=CycleJacobianSeed.coefficientJacobian := by
  ext i j
  change (expandedGradient (slotCoordinate j)*X^slotDegree j).coeff i.val = _
  rw [Polynomial.coeff_mul_X_pow']
  fin_cases i <;> fin_cases j <;>
    norm_num [expandedGradient,slotCoordinate,slotDegree,CycleJacobianSeed.coefficientJacobian,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Matrix.cons_val_succ,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
      Polynomial.coeff_mul_X_pow',Polynomial.coeff_mul_X,Polynomial.coeff_add,
      Polynomial.coeff_X_pow,Polynomial.coeff_one,Polynomial.coeff_ofNat_zero,
      Polynomial.coeff_ofNat_succ,Polynomial.coeff_X] <;> decide
lemma gradientJacobian_unit : IsUnit gradientJacobian.det := by
  rw [gradientJacobian_eq]
  have h : CycleJacobianSeed.coefficientJacobian.det*CycleJacobianSeed.inverseJacobian.det=1 := by
    rw [← Matrix.det_mul,CycleJacobianSeed.inverse_product,Matrix.det_one]
  apply isUnit_iff_ne_zero.mpr
  intro hz
  rw [hz,zero_mul] at h
  exact zero_ne_one h

def integerEndpoints : Fin 2 → ℤ := ![1,3]
def integerEquations : Fin 13 → MvPolynomial (Fin 13) ℤ :=
  equations 2 3 integerEndpoints
lemma integer_curve_binding : curveEval integerEndpoints (Int.castRingHom K) seed=seedCurve := by
  rw [curveEval_eq_valueCurve]
  rw [← curveEval_seed,curveEval_eq_valueCurve]
  congr 1
  funext i
  fin_cases i <;> norm_num [integerEndpoints,endpoints]
lemma integer_seed_equations (i : Fin 13) :
    MvPolynomial.aeval seed (integerEquations i)=0 := by
  change MvPolynomial.eval₂Hom (Int.castRingHom K) seed
    (equations 2 3 integerEndpoints i)=0
  rw [equations_eval,integer_curve_binding]
  simpa only [map_ofNat,Polynomial.coeff_zero] using
    congrArg (fun p : Polynomial K => p.coeff i.val) seed_incidence
lemma integer_seed_jacobian : IsUnit (Matrix.det (fun i j : Fin 13 =>
    MvPolynomial.aeval seed (MvPolynomial.pderiv i (integerEquations j)))) := by
  have hm : (fun i j : Fin 13 => MvPolynomial.aeval seed
      (MvPolynomial.pderiv i (integerEquations j)))=gradientJacobian.transpose := by
    funext i j
    change MvPolynomial.eval₂Hom (Int.castRingHom K) seed
      (MvPolynomial.pderiv i (equations 2 3 integerEndpoints j))=_
    rw [equations_pderiv_eval,integer_curve_binding]
    simpa only [map_ofNat,seed_gradient,gradientJacobian,Matrix.transpose_apply]
  rw [hm,Matrix.det_transpose]
  exact gradientJacobian_unit

#print axioms integer_seed_equations
#print axioms integer_seed_jacobian
end CycleJacobianSeedBinding
