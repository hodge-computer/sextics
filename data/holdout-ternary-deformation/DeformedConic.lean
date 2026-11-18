import Proposal.ConicSeed

noncomputable section
set_option profiler true
set_option profiler.threshold 100
namespace DeformedConic
open Polynomial
local instance deformedConic_local_1 : Fact (Nat.Prime 5) := ⟨by decide⟩

def seedJacobian : Matrix (Fin 13) (Fin 13) K := fun i j =>
  MvPolynomial.eval₂Hom (RingHom.id K) seed
    (MvPolynomial.pderiv j (equations 1 0 parameters i))
def explicitJacobian : Matrix (Fin 13) (Fin 13) K := !![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
3, 3, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0;
2, 3, 3, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0;
0, 2, 3, 0, 0, 2, 0, 0, 0, 1, 2, 1, 0;
1, 0, 2, 0, 0, 2, 2, 0, 0, 2, 1, 2, 1;
2, 1, 0, 0, 0, 1, 2, 2, 0, 0, 2, 1, 2;
0, 2, 1, 0, 0, 3, 1, 2, 2, 0, 0, 2, 1;
1, 0, 2, 0, 0, 0, 3, 1, 2, 2, 0, 0, 2;
2, 1, 0, 0, 0, 3, 0, 3, 1, 3, 2, 0, 0;
4, 2, 1, 0, 0, 0, 3, 0, 3, 4, 3, 2, 0;
0, 4, 2, 0, 0, 0, 0, 3, 0, 0, 4, 3, 2;
0, 0, 4, 3, 0, 0, 0, 0, 3, 0, 0, 4, 3;
0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 4]
def inverseJacobian : Matrix (Fin 13) (Fin 13) K := !![2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
4, 3, 4, 2, 1, 1, 3, 4, 3, 2, 3, 4, 2;
4, 4, 2, 4, 2, 1, 2, 4, 2, 0, 3, 2, 1;
3, 0, 0, 2, 0, 4, 1, 2, 3, 0, 3, 2, 0;
0, 3, 1, 0, 2, 0, 3, 0, 4, 1, 4, 4, 0;
0, 3, 4, 1, 3, 3, 2, 0, 3, 2, 2, 4, 2;
1, 3, 1, 4, 4, 4, 3, 2, 2, 2, 1, 4, 3;
2, 3, 2, 4, 1, 4, 1, 4, 1, 4, 3, 4, 1;
1, 4, 2, 1, 1, 3, 4, 3, 2, 3, 4, 2, 1;
4, 2, 3, 2, 2, 3, 0, 1, 3, 4, 3, 1, 4;
4, 2, 1, 3, 0, 3, 2, 4, 0, 0, 2, 1, 3;
3, 0, 3, 0, 4, 0, 0, 1, 4, 3, 4, 0, 4;
0, 4, 3, 0, 1, 0, 4, 0, 2, 3, 2, 2, 4]
def gradientJacobian : Matrix (Fin 13) (Fin 13) K := fun i j =>
  (expandedGradient (slotCoordinate j)*X^slotDegree j).coeff i.val
lemma seedJacobian_gradient : seedJacobian=gradientJacobian := by
  unfold seedJacobian gradientJacobian
  funext i j
  rw [equations_pderiv_eval,curveEval_seed]
  simp only [RingHom.id_apply,map_one,map_zero,seed_gradient]
lemma gradientJacobian_eq : gradientJacobian=explicitJacobian := by
  ext i j
  change (expandedGradient (slotCoordinate j)*X^slotDegree j).coeff i.val = _
  rw [Polynomial.coeff_mul_X_pow']
  fin_cases i <;> fin_cases j <;>
    norm_num [expandedGradient,slotCoordinate,slotDegree,explicitJacobian,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Matrix.cons_val_succ,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
      Polynomial.coeff_mul_X_pow',Polynomial.coeff_mul_X,Polynomial.coeff_add,
      Polynomial.coeff_X_pow,Polynomial.coeff_one,Polynomial.coeff_ofNat_zero,Polynomial.coeff_ofNat_succ,Polynomial.coeff_X] <;> decide
lemma seedJacobian_eq : seedJacobian=explicitJacobian :=
  seedJacobian_gradient.trans gradientJacobian_eq
lemma seedJacobian_inverse : explicitJacobian*inverseJacobian=1 := by decide
lemma seed_jacobian_unit : IsUnit seedJacobian.det := by
  rw [seedJacobian_eq]
  have h : explicitJacobian.det*inverseJacobian.det=1 := by
    rw [← Matrix.det_mul,seedJacobian_inverse,Matrix.det_one]
  apply isUnit_iff_ne_zero.mpr
  intro hz
  rw [hz,zero_mul] at h
  exact zero_ne_one h

#print axioms seed_incidence
#print axioms seedJacobian_eq
#print axioms seed_jacobian_unit
end DeformedConic
