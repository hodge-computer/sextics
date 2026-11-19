import Proposal.QuarticMatrix
import Proposal.QuarticGradientCoefficients
import Proposal.QuarticSeedIncidence

noncomputable section
namespace ReflectionCoupledFano
open Polynomial CoupledFanoQuarticSeed
variable {K : Type*} [Field K] [CharP K 5]

private lemma modGradient_matrix_column_0 (j : K) (i : Index) (s : Fin 4) :
    (if s.val+1 ≤ equationDegree i then
      seedCoeff j (equationDegree i-(s.val+1)) 0 else 0) =
      seedMatrix j (finProdFinEquiv i) (finProdFinEquiv ((0,s) : Index)) := by
  rcases i with ⟨i,r⟩
  fin_cases i <;> fin_cases r <;> fin_cases s <;>
    norm_num [seedCoeff, seedMatrix, equationDegree, finProdFinEquiv, Matrix.cons_val] <;> rfl

private lemma modGradient_matrix_column_1 (j : K) (i : Index) (s : Fin 4) :
    (if s.val+1 ≤ equationDegree i then
      seedCoeff j (equationDegree i-(s.val+1)) 1 else 0) =
      seedMatrix j (finProdFinEquiv i) (finProdFinEquiv ((1,s) : Index)) := by
  rcases i with ⟨i,r⟩
  fin_cases i <;> fin_cases r <;> fin_cases s <;>
    norm_num [seedCoeff, seedMatrix, equationDegree, finProdFinEquiv, Matrix.cons_val] <;> rfl

private lemma modGradient_matrix_column_2 (j : K) (i : Index) (s : Fin 4) :
    (if s.val+1 ≤ equationDegree i then
      seedCoeff j (equationDegree i-(s.val+1)) 2 else 0) =
      seedMatrix j (finProdFinEquiv i) (finProdFinEquiv ((2,s) : Index)) := by
  rcases i with ⟨i,r⟩
  fin_cases i <;> fin_cases r <;> fin_cases s <;>
    norm_num [seedCoeff, seedMatrix, equationDegree, finProdFinEquiv, Matrix.cons_val] <;> rfl

private lemma modGradient_matrix_column_3 (j : K) (i : Index) (s : Fin 4) :
    (if s.val+1 ≤ equationDegree i then
      seedCoeff j (equationDegree i-(s.val+1)) 3 else 0) =
      seedMatrix j (finProdFinEquiv i) (finProdFinEquiv ((3,s) : Index)) := by
  rcases i with ⟨i,r⟩
  fin_cases i <;> fin_cases r <;> fin_cases s <;>
    norm_num [seedCoeff, seedMatrix, equationDegree, finProdFinEquiv, Matrix.cons_val] <;> rfl

private lemma modGradient_matrix_column_4 (j : K) (i : Index) (s : Fin 4) :
    (if s.val+1 ≤ equationDegree i then
      seedCoeff j (equationDegree i-(s.val+1)) 4 else 0) =
      seedMatrix j (finProdFinEquiv i) (finProdFinEquiv ((4,s) : Index)) := by
  rcases i with ⟨i,r⟩
  fin_cases i <;> fin_cases r <;> fin_cases s <;>
    norm_num [seedCoeff, seedMatrix, equationDegree, finProdFinEquiv, Matrix.cons_val] <;> rfl

private lemma modGradient_matrix_column_5 (j : K) (i : Index) (s : Fin 4) :
    (if s.val+1 ≤ equationDegree i then
      seedCoeff j (equationDegree i-(s.val+1)) 5 else 0) =
      seedMatrix j (finProdFinEquiv i) (finProdFinEquiv ((5,s) : Index)) := by
  rcases i with ⟨i,r⟩
  fin_cases i <;> fin_cases r <;> fin_cases s <;>
    norm_num [seedCoeff, seedMatrix, equationDegree, finProdFinEquiv, Matrix.cons_val] <;> rfl

lemma modGradient_matrix (j : K) (i k : Index) :
    (seedGradient j k.1 * X^(k.2.val+1)).coeff (equationDegree i) =
      seedMatrix j (finProdFinEquiv i) (finProdFinEquiv k) := by
  rw [coeff_mul_X_pow', seedGradient_coeff]
  rcases k with ⟨k,s⟩
  fin_cases k
  · exact modGradient_matrix_column_0 j i s
  · exact modGradient_matrix_column_1 j i s
  · exact modGradient_matrix_column_2 j i s
  · exact modGradient_matrix_column_3 j i s
  · exact modGradient_matrix_column_4 j i s
  · exact modGradient_matrix_column_5 j i s

def modJacobian (j : K) : Matrix Index Index K := fun i k =>
  MvPolynomial.eval₂Hom (RingHom.id K) (modCoefficients j)
    (MvPolynomial.pderiv k (equations 0 (modEndpoint j) i))

lemma modJacobian_eq {j : K} (hj : j^2=2) :
    modJacobian j = Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
      (seedMatrix j) := by
  ext i k
  rw [modJacobian, equations_pderiv_eval₂]
  simp only [RingHom.id_apply, map_zero, modCurve_value, modCurve_gradient hj]
  exact modGradient_matrix j i k

lemma modJacobian_det_ne_zero {j : K} (hj : j^2=2) : (modJacobian j).det ≠ 0 := by
  rw [modJacobian_eq hj, Matrix.det_reindex_self]
  exact seedMatrix_det_ne_zero hj

lemma modJacobian_det_isUnit {j : K} (hj : j^2=2) : IsUnit (modJacobian j).det :=
  isUnit_iff_ne_zero.mpr (modJacobian_det_ne_zero hj)

lemma modJacobian_polynomial_det_isUnit {j : K} (hj : j^2=2) :
    IsUnit (MvPolynomial.eval₂Hom (RingHom.id K) (modCoefficients j)
      (Matrix.det (fun i k : Index => MvPolynomial.pderiv k
        (equations 0 (modEndpoint j) i)))) := by
  exact (congrArg IsUnit (RingHom.map_det _ _)).mpr (modJacobian_det_isUnit hj)

end ReflectionCoupledFano
