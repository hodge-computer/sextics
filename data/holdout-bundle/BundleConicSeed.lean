import Proposal.BundleConic

/-!
Exact F5 seed for the complementary diagonal quotient's moving conic.
The inverse matrix is checked by Lean's kernel-supported decision procedure;
no native decision procedure or external arithmetic assertion is used.
The incidence pattern builds on fqlx and hodgepodgeconjecture's accepted proofs.
Prepared with OpenAI ChatGPT assistance.
-/
noncomputable section
namespace HoldoutBundle
open Polynomial
abbrev SeedField := ZMod 5
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

def seed : Fin 12 → SeedField := ![1,0,4,1,4,2,2,4,4,1,1,2]
def seedEndpoint : Fin 4 → SeedField := ![1,1,4,1]
def seedCurve : Fin 5 → Polynomial SeedField := ![(1)+(1)*X^1,
(1)*X^1,
(1)+(4)*X^1+(1)*X^2,
(4)+(4)*X^1+(2)*X^2+(2)*X^3+(4)*X^4,
(1)+(4)*X^1+(1)*X^2+(1)*X^3+(2)*X^4]

lemma curveEval_seed : curveEval seedEndpoint (RingHom.id SeedField) seed = seedCurve := by
  funext i
  fin_cases i <;> simp [curveEval,curve,cv,cp,seed,seedEndpoint,seedCurve,map_ofNat]

lemma seed_incidence : K (0 : Polynomial SeedField) 3 seedCurve = 0 := by
  have he : K (0 : Polynomial SeedField) 3 seedCurve = 5*((1)+(14)*X^1+(86)*X^2+(344)*X^3+(1021)*X^4+(2122)*X^5+(2735)*X^6+(2094)*X^7+(1007)*X^8+(317)*X^9+(60)*X^10+(12)*X^11+(5)*X^12) := by
    dsimp [K,seedCurve]
    ring
  have h5 : (5 : Polynomial SeedField)=0 := CharP.cast_eq_zero _ 5
  rw [he,h5,zero_mul]

lemma seed_equations (i : Fin 12) :
    MvPolynomial.eval₂Hom (RingHom.id SeedField) seed
      (equations 0 3 seedEndpoint i)=0 := by
  rw [equations_eval,curveEval_seed]
  simpa only [RingHom.id_apply,map_zero,map_ofNat,Polynomial.coeff_zero] using
    congrArg (fun p : Polynomial SeedField => p.coeff (i.val+1)) seed_incidence

def seedGradient : Fin 5 → Polynomial SeedField := ![(1)+(2)*X^1+(1)*X^2+(2)*X^3+(1)*X^5+(2)*X^7,
(4)+(1)*X^1+(4)*X^2+(3)*X^3+(4)*X^4+(3)*X^5+(1)*X^7+(1)*X^8,
(1)+(1)*X^3+(4)*X^4+(1)*X^6+(2)*X^7+(1)*X^10,
(1)*X^1+(3)*X^2+(3)*X^3+(1)*X^4,
(4)+(2)*X^1+(2)*X^2+(1)*X^3+(1)*X^4+(3)*X^5+(1)*X^7+(1)*X^8]
private def gradientCorrection : Fin 5 → Polynomial SeedField := ![(1)+(8)*X^1+(19)*X^2+(20)*X^3+(12)*X^4+(7)*X^5+(6)*X^6+(2)*X^7,
(3)*X^1+(5)*X^2+(9)*X^3+(14)*X^4+(10)*X^5+(7)*X^6+(6)*X^7+(1)*X^8,
(1)+(24)*X^1+(198)*X^2+(864)*X^3+(2124)*X^4+(2909)*X^5+(2124)*X^6+(864)*X^7+(198)*X^8+(24)*X^9+(1)*X^10,
0,
(1)+(14)*X^1+(32)*X^2+(18)*X^3+(24)*X^4+(32)*X^5+(9)*X^6+(7)*X^7+(7)*X^8]

lemma seed_gradient : gradient (0 : Polynomial SeedField) 3 seedCurve = seedGradient := by
  have he : gradient (0 : Polynomial SeedField) 3 seedCurve =
      fun i => seedGradient i+5*gradientCorrection i := by
    funext i
    fin_cases i <;> dsimp [gradient,seedCurve,seedGradient,gradientCorrection] <;> ring
  have h5 : (5 : Polynomial SeedField)=0 := CharP.cast_eq_zero _ 5
  simpa only [h5,zero_mul,add_zero] using he

def seedJacobian : Matrix (Fin 12) (Fin 12) SeedField := fun i j =>
  MvPolynomial.eval₂Hom (RingHom.id SeedField) seed
    (MvPolynomial.pderiv j (equations 0 3 seedEndpoint i))
def explicitJacobian : Matrix (Fin 12) (Fin 12) SeedField := !![1, 0, 1, 0, 0, 0, 0, 0, 4, 0, 0, 0;
2, 1, 0, 1, 1, 0, 0, 0, 2, 4, 0, 0;
1, 2, 0, 0, 3, 1, 0, 0, 2, 2, 4, 0;
2, 1, 1, 0, 3, 3, 1, 0, 1, 2, 2, 4;
0, 2, 4, 1, 1, 3, 3, 1, 1, 1, 2, 2;
1, 0, 0, 4, 0, 1, 3, 3, 3, 1, 1, 2;
0, 1, 1, 0, 0, 0, 1, 3, 0, 3, 1, 1;
2, 0, 2, 1, 0, 0, 0, 1, 1, 0, 3, 1;
0, 2, 0, 2, 0, 0, 0, 0, 1, 1, 0, 3;
0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0;
0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1;
0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]
def inverseJacobian : Matrix (Fin 12) (Fin 12) SeedField := !![4, 0, 2, 1, 1, 2, 0, 3, 4, 2, 0, 0;
2, 3, 4, 0, 0, 1, 2, 1, 4, 4, 4, 4;
2, 1, 2, 3, 4, 2, 4, 3, 0, 3, 0, 4;
3, 4, 2, 1, 2, 4, 1, 3, 3, 1, 1, 0;
1, 4, 2, 1, 3, 1, 2, 3, 4, 4, 3, 3;
2, 4, 2, 2, 4, 1, 3, 4, 2, 0, 4, 0;
1, 2, 2, 2, 1, 4, 4, 0, 3, 4, 4, 0;
0, 3, 3, 4, 1, 2, 2, 3, 4, 1, 4, 2;
0, 1, 4, 4, 0, 4, 4, 1, 4, 0, 0, 4;
4, 2, 0, 2, 2, 3, 3, 0, 2, 3, 3, 0;
1, 3, 0, 3, 3, 2, 2, 0, 3, 3, 2, 0;
2, 1, 3, 4, 3, 1, 4, 2, 2, 4, 4, 1]

def gradientJacobian : Matrix (Fin 12) (Fin 12) SeedField := fun i j =>
  (seedGradient (slotCoordinate j)*X^slotDegree j).coeff (i.val+1)

lemma seedJacobian_gradient : seedJacobian=gradientJacobian := by
  unfold seedJacobian gradientJacobian
  funext i j
  rw [equations_pderiv_eval,curveEval_seed]
  simp only [RingHom.id_apply,map_zero,map_ofNat,seed_gradient]

lemma gradientJacobian_eq : gradientJacobian=explicitJacobian := by
  ext i j
  change (seedGradient (slotCoordinate j)*X^slotDegree j).coeff (i.val+1) = _
  rw [Polynomial.coeff_mul_X_pow']
  fin_cases i <;> fin_cases j <;>
    norm_num [seedGradient,slotCoordinate,slotDegree,explicitJacobian,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Matrix.cons_val_succ,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
      Polynomial.coeff_mul_X_pow',Polynomial.coeff_mul_X,Polynomial.coeff_add,
      Polynomial.coeff_X_pow,Polynomial.coeff_one,Polynomial.coeff_ofNat_zero,
      Polynomial.coeff_ofNat_succ,Polynomial.coeff_X] <;> decide

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
#print axioms seed_jacobian_unit
end HoldoutBundle
