import Proposal.LineIncidence
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
The free weighted line identified by rbajaj5 in discussion #112.
Its six positive-coefficient deformations have a nonsingular Jacobian.
The exact argument, including the inverse matrix, is kernel checked.
-/
noncomputable section
namespace CyclicTriple
open Polynomial

def coupling : ℂ := 5/7
def seedEndpoint : Fin 6 → ℂ := ![Complex.I,0,0,1,0,0]
def seedCoefficients : Index → ℂ := ![0,0,Complex.I,0,0,0]
def seedCurve : Fin 6 → ℂ[X] := ![C Complex.I,X,0,1,C Complex.I*X,0]

theorem seedCurve_value (i : Fin 6) :
    valueCurve seedEndpoint seedCoefficients i = seedCurve i := by
  fin_cases i <;> simp [valueCurve_explicit, seedEndpoint, seedCoefficients, seedCurve]

theorem seedCurve_equation : H (C coupling) seedCurve = 0 := by
  have hi6 : Complex.I^6 = -1 := by
    rw [show (6 : ℕ) = 2*3 by decide, pow_mul, Complex.I_sq]
    norm_num
  dsimp [H, seedCurve]
  simp [mul_pow, ← map_pow, hi6]

theorem seedEquations (i : Index) :
    MvPolynomial.eval₂Hom (RingHom.id ℂ) seedCoefficients
      (equations coupling seedEndpoint i) = 0 := by
  rw [equations_eval₂]
  change (H (C coupling) (valueCurve seedEndpoint seedCoefficients)).coeff _ = 0
  rw [funext seedCurve_value, seedCurve_equation, coeff_zero]

def seedGradient : Fin 6 → ℂ[X] :=
  ![C (6*Complex.I),6*X^5,C (coupling*Complex.I)*X^4,
    6,C (6*Complex.I)*X^5,C (coupling*Complex.I)*X]

theorem seedGradient_eq (i : Fin 6) :
    gradient (C coupling) seedCurve i = seedGradient i := by
  fin_cases i <;>
    dsimp [gradient, seedCurve, seedGradient] <;>
    norm_num [mul_pow, ← map_pow, Complex.I_pow_eq_pow_mod,
      Polynomial.C_mul, Polynomial.C_ofNat] <;> ring

def seedMatrix : Matrix Index Index ℂ := fun i j =>
  if i=0 ∧ j=0 then 6*Complex.I else
  if i=1 ∧ j=3 then coupling*Complex.I else
  if i=2 ∧ j=4 then coupling*Complex.I else
  if i=3 ∧ j=5 then coupling*Complex.I else
  if i=4 ∧ j=1 then coupling*Complex.I else
  if i=5 ∧ j=2 then 6*Complex.I else 0

theorem seedJacobian_eq :
    (fun i j : Index => MvPolynomial.eval₂Hom (RingHom.id ℂ) seedCoefficients
      (MvPolynomial.pderiv j (equations coupling seedEndpoint i))) = seedMatrix := by
  funext i j
  rw [equations_pderiv_eval₂]
  change (gradient (C coupling) (valueCurve seedEndpoint seedCoefficients) (variationCoordinate j) * X ^ variationDegree j).coeff _ = _
  rw [funext seedCurve_value, seedGradient_eq]
  fin_cases i <;> fin_cases j <;>
    dsimp [seedGradient, seedMatrix, variationCoordinate, variationDegree, equationDegree] <;>
    norm_num [seedGradient, seedMatrix, variationCoordinate, variationDegree,
      equationDegree, Matrix.cons_val, coeff_mul_X_pow, coeff_mul_X_pow', coeff_mul_C]

def seedInverse : Matrix Index Index ℂ := fun i j =>
  if i=0 ∧ j=0 then -Complex.I/6 else
  if i=1 ∧ j=4 then -7*Complex.I/5 else
  if i=2 ∧ j=5 then -Complex.I/6 else
  if i=3 ∧ j=1 then -7*Complex.I/5 else
  if i=4 ∧ j=2 then -7*Complex.I/5 else
  if i=5 ∧ j=3 then -7*Complex.I/5 else 0

theorem seedMatrix_inverse : (seedMatrix : Matrix Index Index ℂ) * seedInverse = 1 := by
  ext i j
  change (∑ k, seedMatrix i k * seedInverse k j) = (if i = j then 1 else 0)
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.sum_univ_succ] <;>
    norm_num [Fin.ext_iff, Matrix.mul_apply, Fin.sum_univ_succ, seedMatrix, seedInverse,
      coupling, Matrix.cons_val, Matrix.one_apply] <;> ring_nf <;> norm_num

theorem seedJacobian_unit :
    IsUnit (Matrix.det (fun i j : Index => MvPolynomial.eval₂Hom (RingHom.id ℂ)
      seedCoefficients (MvPolynomial.pderiv j (equations coupling seedEndpoint i)))) := by
  rw [seedJacobian_eq]
  exact Matrix.isUnit_det_of_right_inverse seedMatrix_inverse

end CyclicTriple
#print axioms CyclicTriple.seedEquations
#print axioms CyclicTriple.seedJacobian_unit
