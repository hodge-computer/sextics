import Proposal.QuarticGradient
import Proposal.QuarticIncidence

noncomputable section
namespace ReflectionCoupledFano
open Polynomial CoupledFanoQuarticSeed
variable {K : Type*} [Field K] [CharP K 5]

def modEndpoint (j : K) : Fin 6 → K := ![j,0,0,0,1,1]

def modCoefficients (j : K) : Index → K := fun i =>
  ![![0,0,0,j], ![2+j,0,2+j,0], ![0,j,0,0],
    ![j,0,-j,0], ![0,0,0,-1], ![0,0,0,1]] i.1 i.2

def modCurve (j : K) : Fin 6 → K[X] :=
  ![seedX j 0, seedX j 1, seedX j 2, seedX j 3, seedX j 4, seedU]

lemma modCurve_value (j : K) : valueCurve (modEndpoint j) (modCoefficients j) = modCurve j := by
  funext i
  rw [valueCurve_explicit]
  fin_cases i <;>
    simp [modEndpoint, modCoefficients, modCurve, seedX, seedU, Fin.sum_univ_succ,
      Matrix.cons_val, map_ofNat] <;> ring

lemma modCurve_equation {j : K} (hj : j^2=2) : H 0 (modCurve j) = 0 := by
  have h := seed_equation hj
  simp only [H, zero_mul, add_zero]
  simpa [modCurve, seedX, Fin.sum_univ_succ, Matrix.cons_val, add_comm, add_left_comm,
    add_assoc] using h

lemma modEquations_zero {j : K} (hj : j^2=2) (i : Index) :
    MvPolynomial.eval₂Hom (RingHom.id K) (modCoefficients j)
      (equations 0 (modEndpoint j) i) = 0 := by
  rw [equations_eval₂]
  simp only [RingHom.id_apply, map_zero, modCurve_value, modCurve_equation hj, coeff_zero]

lemma modCurve_gradient {j : K} (hj : j^2=2) : gradient 0 (modCurve j) = seedGradient j := by
  funext i
  fin_cases i
  · simpa [gradient, modCurve, Matrix.cons_val] using (seedGradient_weight_one hj (0 : Fin 5)).symm
  · simpa [gradient, modCurve, Matrix.cons_val] using (seedGradient_weight_one hj (1 : Fin 5)).symm
  · simpa [gradient, modCurve, Matrix.cons_val] using (seedGradient_weight_one hj (2 : Fin 5)).symm
  · simpa [gradient, modCurve, Matrix.cons_val] using (seedGradient_weight_one hj (3 : Fin 5)).symm
  · simpa [gradient, modCurve, Matrix.cons_val] using (seedGradient_weight_one hj (4 : Fin 5)).symm
  · simpa [gradient, modCurve, Matrix.cons_val] using (seedGradient_weight_two (K:=K) j).symm

lemma modCoefficient_linear_ne_zero {j : K} (hj : j^2=2) : modCoefficients j (1,0) ≠ 0 := by
  simp only [modCoefficients, Matrix.cons_val]
  intro h
  have h2 : (2 : K) = 0 := by linear_combination (2-j)*h+hj
  exact two_ne_zero h2

end ReflectionCoupledFano
