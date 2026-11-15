import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! A direct determinant calculation for the mixed-polar quotient chart.
Adapted from the accepted physical Jacobian calculation of fqlx and
hodgepodgeconjecture, with OpenAI Codex assistance. The last row is arbitrary,
so derivatives of the algebraic shear in passive directions are retained. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace MixedPolarJacobianGeometry
open scoped BigOperators
section Determinant
variable {K : Type*} [Field K]
def rawMatrix (p f : Fin 6 → K) (z : Fin 5 → K) (u : K) : Matrix (Fin 5) (Fin 5) K :=
  !![6*p 2^2*p 3^6*f 1/(p 0^7*f 0),
     2*p 2*p 3^6/p 0^6+6*p 2^2*p 3^6*f 2/(p 0^7*f 0),
     6*p 2^2*p 3^5/p 0^6+6*p 2^2*p 3^6*f 3/(p 0^7*f 0),
     6*p 2^2*p 3^6*f 4/(p 0^7*f 0),6*p 2^2*p 3^6*f 5/(p 0^7*f 0);
     -p 0*p 4/(p 1^2*p 3)-f 1/f 0*p 4/(p 1*p 3),
     -f 2/f 0*p 4/(p 1*p 3),
     -p 0*p 4/(p 1*p 3^2)-f 3/f 0*p 4/(p 1*p 3),
     p 0/(p 1*p 3)-f 4/f 0*p 4/(p 1*p 3),-f 5/f 0*p 4/(p 1*p 3);
     -f 1/f 0*p 5/(p 2*p 3),
     -p 0*p 5/(p 2^2*p 3)-f 2/f 0*p 5/(p 2*p 3),
     -p 0*p 5/(p 2*p 3^2)-f 3/f 0*p 5/(p 2*p 3),
     -f 4/f 0*p 5/(p 2*p 3),p 0/(p 2*p 3)-f 5/f 0*p 5/(p 2*p 3);
     0,2*p 2,0,0,0;
     p 2^4*z 0,p 2^4*z 1+4*p 2^3*u,p 2^4*z 2,p 2^4*z 3,p 2^4*z 4]

theorem raw_determinant (p f : Fin 6 → K) (z : Fin 5 → K) (u : K)
    (h0 : p 0≠0) (h1 : p 1≠0) (h2 : p 2≠0) (h3 : p 3≠0) (hf : f 0≠0) :
    (rawMatrix p f z u).det=
      -12*p 2^6*p 3^3/(p 0^5*p 1^2*f 0)*
        ((p 0*f 0+p 3*f 3)*p 1*z 0-p 3*(p 1*f 1+p 4*f 4)*z 2+
          (p 0*f 0+p 3*f 3)*p 4*z 3) := by
  rw [Matrix.det_succ_row _ (3:Fin 5)]
  have hrow (j : Fin 5) : rawMatrix p f z u 3 j=if j=1 then 2*p 2 else 0 := by
    fin_cases j <;> norm_num [rawMatrix,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons]
  simp_rw [hrow]
  simp only [mul_ite,ite_mul,mul_zero,zero_mul,Finset.sum_ite_eq',
    Finset.mem_univ,if_true]
  have hminor (A : Matrix (Fin 4) (Fin 4) K) :
      A.det=A 0 0*(A 1 1*A 2 2*A 3 3-A 1 1*A 2 3*A 3 2-A 1 2*A 2 1*A 3 3+
        A 1 2*A 2 3*A 3 1+A 1 3*A 2 1*A 3 2-A 1 3*A 2 2*A 3 1)-
      A 0 1*(A 1 0*A 2 2*A 3 3-A 1 0*A 2 3*A 3 2-A 1 2*A 2 0*A 3 3+
        A 1 2*A 2 3*A 3 0+A 1 3*A 2 0*A 3 2-A 1 3*A 2 2*A 3 0)+
      A 0 2*(A 1 0*A 2 1*A 3 3-A 1 0*A 2 3*A 3 1-A 1 1*A 2 0*A 3 3+
        A 1 1*A 2 3*A 3 0+A 1 3*A 2 0*A 3 1-A 1 3*A 2 1*A 3 0)-
      A 0 3*(A 1 0*A 2 1*A 3 2-A 1 0*A 2 2*A 3 1-A 1 1*A 2 0*A 3 2+
        A 1 1*A 2 2*A 3 0+A 1 2*A 2 0*A 3 1-A 1 2*A 2 1*A 3 0) := by
    rw [Matrix.det_succ_row_zero]
    simp only [Fin.sum_univ_succ,Matrix.det_fin_three,Matrix.submatrix_apply,
      Finset.univ_eq_empty,Finset.sum_empty,add_zero]
    norm_num only [Fin.val_zero,Fin.val_succ,Fin.val_one]
    simp only [Fin.succ_zero_eq_one,Fin.succ_one_eq_two,
      show (Fin.succAbove (0:Fin 4) (0:Fin 3))=(1:Fin 4) by decide,
      show (Fin.succAbove (0:Fin 4) (1:Fin 3))=(2:Fin 4) by decide,
      show (Fin.succAbove (0:Fin 4) (2:Fin 3))=(3:Fin 4) by decide,
      show (Fin.succAbove (1:Fin 4) (0:Fin 3))=(0:Fin 4) by decide,
      show (Fin.succAbove (1:Fin 4) (1:Fin 3))=(2:Fin 4) by decide,
      show (Fin.succAbove (1:Fin 4) (2:Fin 3))=(3:Fin 4) by decide,
      show (Fin.succAbove (2:Fin 4) (0:Fin 3))=(0:Fin 4) by decide,
      show (Fin.succAbove (2:Fin 4) (1:Fin 3))=(1:Fin 4) by decide,
      show (Fin.succAbove (2:Fin 4) (2:Fin 3))=(3:Fin 4) by decide,
      show (Fin.succAbove (3:Fin 4) (0:Fin 3))=(0:Fin 4) by decide,
      show (Fin.succAbove (3:Fin 4) (1:Fin 3))=(1:Fin 4) by decide,
      show (Fin.succAbove (3:Fin 4) (2:Fin 3))=(2:Fin 4) by decide,
      show (Fin.succ (0:Fin 3))=(1:Fin 4) by decide,
      show (Fin.succ (1:Fin 3))=(2:Fin 4) by decide,
      show (Fin.succ (2:Fin 3))=(3:Fin 4) by decide]
    ring
  rw [hminor]
  have hc : (-1:K)^((3:Fin 5).val+(1:Fin 5).val)=1 := by norm_num
  rw [hc,one_mul]
  change (2*p 2)*((rawMatrix p f z u 0 0)*((rawMatrix p f z u 1 2)*(rawMatrix p f z u 2 3)*(rawMatrix p f z u 4 4)-(rawMatrix p f z u 1 2)*(rawMatrix p f z u 2 4)*(rawMatrix p f z u 4 3)-(rawMatrix p f z u 1 3)*(rawMatrix p f z u 2 2)*(rawMatrix p f z u 4 4)+(rawMatrix p f z u 1 3)*(rawMatrix p f z u 2 4)*(rawMatrix p f z u 4 2)+(rawMatrix p f z u 1 4)*(rawMatrix p f z u 2 2)*(rawMatrix p f z u 4 3)-(rawMatrix p f z u 1 4)*(rawMatrix p f z u 2 3)*(rawMatrix p f z u 4 2))-(rawMatrix p f z u 0 2)*((rawMatrix p f z u 1 0)*(rawMatrix p f z u 2 3)*(rawMatrix p f z u 4 4)-(rawMatrix p f z u 1 0)*(rawMatrix p f z u 2 4)*(rawMatrix p f z u 4 3)-(rawMatrix p f z u 1 3)*(rawMatrix p f z u 2 0)*(rawMatrix p f z u 4 4)+(rawMatrix p f z u 1 3)*(rawMatrix p f z u 2 4)*(rawMatrix p f z u 4 0)+(rawMatrix p f z u 1 4)*(rawMatrix p f z u 2 0)*(rawMatrix p f z u 4 3)-(rawMatrix p f z u 1 4)*(rawMatrix p f z u 2 3)*(rawMatrix p f z u 4 0))+(rawMatrix p f z u 0 3)*((rawMatrix p f z u 1 0)*(rawMatrix p f z u 2 2)*(rawMatrix p f z u 4 4)-(rawMatrix p f z u 1 0)*(rawMatrix p f z u 2 4)*(rawMatrix p f z u 4 2)-(rawMatrix p f z u 1 2)*(rawMatrix p f z u 2 0)*(rawMatrix p f z u 4 4)+(rawMatrix p f z u 1 2)*(rawMatrix p f z u 2 4)*(rawMatrix p f z u 4 0)+(rawMatrix p f z u 1 4)*(rawMatrix p f z u 2 0)*(rawMatrix p f z u 4 2)-(rawMatrix p f z u 1 4)*(rawMatrix p f z u 2 2)*(rawMatrix p f z u 4 0))-(rawMatrix p f z u 0 4)*((rawMatrix p f z u 1 0)*(rawMatrix p f z u 2 2)*(rawMatrix p f z u 4 3)-(rawMatrix p f z u 1 0)*(rawMatrix p f z u 2 3)*(rawMatrix p f z u 4 2)-(rawMatrix p f z u 1 2)*(rawMatrix p f z u 2 0)*(rawMatrix p f z u 4 3)+(rawMatrix p f z u 1 2)*(rawMatrix p f z u 2 3)*(rawMatrix p f z u 4 0)+(rawMatrix p f z u 1 3)*(rawMatrix p f z u 2 0)*(rawMatrix p f z u 4 2)-(rawMatrix p f z u 1 3)*(rawMatrix p f z u 2 2)*(rawMatrix p f z u 4 0)))=_
  norm_num only [rawMatrix,Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
    Matrix.head_cons,Matrix.tail_cons,Matrix.cons_val_succ',Matrix.cons_val_zero',Function.comp_apply]
  field_simp
  ring
end Determinant
end MixedPolarJacobianGeometry
#print axioms MixedPolarJacobianGeometry.raw_determinant
