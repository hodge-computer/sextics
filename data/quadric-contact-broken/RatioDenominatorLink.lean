import Proposal.RatioMatrixInverse
import Proposal.DenominatorAssembly
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Matrix.ToLin

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
noncomputable section
namespace QuadricContactRatioDenominator
open Polynomial QuadricContactRatioInverse
attribute [local irreducible] QuadricContactRatioInverse.linePolynomial

/-- The exact 27-line algebra at alpha=1,beta=2, with no assumed matrix data. -/
abbrev Auxiliary := AdjoinRoot linePolynomial

def root : Auxiliary := AdjoinRoot.root linePolynomial

theorem root_equation : Polynomial.aeval root linePolynomial = 0 := by
  rw [root, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

theorem polynomial_degree : linePolynomial.natDegree = 27 := by
  unfold linePolynomial
  compute_degree!

theorem polynomial_monic : linePolynomial.Monic := by
  unfold Polynomial.Monic
  rw [Polynomial.leadingCoeff, polynomial_degree]
  simp only [linePolynomial, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C, Polynomial.coeff_X_pow]
  norm_num

def basis : Module.Basis (Fin 27) ℂ Auxiliary :=
  (AdjoinRoot.powerBasisAux' polynomial_monic).reindex (finCongr polynomial_degree)

def sumElement : Auxiliary := Polynomial.aeval root lineSum
def inverseElement : Auxiliary := Polynomial.aeval root inversePolynomial

theorem element_inverse :
    (sumElement ^ 3 + 140 * sumElement + 536) * inverseElement = 1 :=
  evaluated_inverse root root_equation

/-- Multiplication by the actual line-coordinate sum in the exact quotient. -/
def sumMatrix : Matrix (Fin 27) (Fin 27) ℂ := Algebra.leftMulMatrix basis sumElement
def inverseMatrix : Matrix (Fin 27) (Fin 27) ℂ := Algebra.leftMulMatrix basis inverseElement

theorem actual_matrix_inverse :
    (sumMatrix ^ 3 + (140 : ℂ) • sumMatrix +
      (536 : ℂ) • (1 : Matrix (Fin 27) (Fin 27) ℂ)) * inverseMatrix = 1 := by
  have h := congrArg (Algebra.leftMulMatrix basis) element_inverse
  simp only [map_mul, map_add, map_pow, map_ofNat, map_one] at h
  simpa only [sumMatrix, inverseMatrix, Algebra.smul_def, map_ofNat, mul_one] using h

def sumPolynomialMatrix : Matrix (Fin 27) (Fin 27) (Polynomial ℂ) :=
  sumMatrix.map Polynomial.C

def inversePolynomialMatrix : Matrix (Fin 27) (Fin 27) (Polynomial ℂ) :=
  inverseMatrix.map Polynomial.C

theorem actual_polynomial_matrix_inverse :
    (sumPolynomialMatrix ^ 3 + (140 : Polynomial ℂ) • sumPolynomialMatrix +
      (536 : Polynomial ℂ) • (1 : Matrix (Fin 27) (Fin 27) (Polynomial ℂ))) *
      inversePolynomialMatrix = 1 := by
  have hn : (sumMatrix ^ 3 + 140 * sumMatrix + 536) * inverseMatrix = 1 := by
    simpa only [Algebra.smul_def, map_ofNat, mul_one] using actual_matrix_inverse
  have h := congrArg (Polynomial.C.mapMatrix (m := Fin 27)) hn
  simp only [map_mul, map_add, map_pow, map_ofNat, map_one] at h
  simpa only [sumPolynomialMatrix, inversePolynomialMatrix, Algebra.smul_def,
    map_ofNat, mul_one, RingHom.mapMatrix_apply] using h

/-- The actual auxiliary denominator is admissible for the original sextic,
provided the generic clearing construction specializes to this norm. All
matrix data and the inverse are defined and proved above, not hypotheses. -/
theorem denominator_legal (D : HodgeComputer.Poly) (κ : ℂ) (hκ : κ ≠ 0)
    (hD : (QuadricContactDenominator.toUni D).map QuadricContactDenominator.specialize =
      Polynomial.C κ *
      ((2 * Polynomial.X ^ 2 : Polynomial ℂ) •
        (1 : Matrix (Fin 27) (Fin 27) (Polynomial ℂ)) - sumPolynomialMatrix).det) :
    IsRelPrime QuadricContactDenominator.targetF D := by
  exact QuadricContactDenominator.denominator_legal_of_matrix_inverse
    D sumPolynomialMatrix inversePolynomialMatrix κ hκ actual_polynomial_matrix_inverse hD

end QuadricContactRatioDenominator

#print axioms QuadricContactRatioDenominator.actual_matrix_inverse
#print axioms QuadricContactRatioDenominator.denominator_legal
