import Proposal.ContactCubicExistence
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Derivation

/-!
# Rational polynomial interpretation of the certified contact equations

The sparse integer lists used by the contact certificate are genuine
multivariate polynomials over the rationals.  Their formal Jacobian is the
same derivative already proved bijective by the analytic certificate.
-/

noncomputable section

namespace ContactRationalPolynomial

open MvPolynomial ContactExactArithmetic ContactPolynomialBounds
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def monomialRat {n : ℕ} : List (Fin n) → MvPolynomial (Fin n) ℚ
  | [] => 1
  | i :: m => X i * monomialRat m

def polynomialRat {n : ℕ} : IntPolynomial n → MvPolynomial (Fin n) ℚ
  | [] => 0
  | (a, m) :: p => C (a : ℚ) * monomialRat m + polynomialRat p

theorem aeval_monomialRat {n : ℕ} (m : List (Fin n)) (x : Space n) :
    aeval x (monomialRat m) = ContactPolynomialBounds.monomial m x := by
  induction m with
  | nil => simp [monomialRat, ContactPolynomialBounds.monomial]
  | cons i m ih => simp [monomialRat, ContactPolynomialBounds.monomial, ih]

theorem aeval_polynomialRat {n : ℕ} (p : IntPolynomial n) (x : Space n) :
    aeval x (polynomialRat p) = poly (complexPoly p) x := by
  induction p with
  | nil => simp [polynomialRat, complexPoly, poly]
  | cons t p ih =>
      simp [polynomialRat, complexPoly, poly, aeval_monomialRat, ih]

theorem aeval_pderiv_monomialRat {n : ℕ} (m : List (Fin n))
    (x : Space n) (j : Fin n) :
    aeval x (pderiv j (monomialRat m)) =
      monomialDeriv m x (Pi.single j 1) := by
  induction m with
  | nil => simp [monomialRat, monomialDeriv]
  | cons i m ih =>
      simp only [monomialRat, pderiv_mul, map_add, map_mul,
        aeval_X, aeval_monomialRat, ih, monomialDeriv,
        add_apply, smul_apply,
        ContinuousLinearMap.proj_apply, smul_eq_mul]
      by_cases hij : i = j
      · subst i
        simp [pderiv_X, add_comm]
      · simp [pderiv_X, hij]

theorem aeval_pderiv_polynomialRat {n : ℕ} (p : IntPolynomial n)
    (x : Space n) (j : Fin n) :
    aeval x (pderiv j (polynomialRat p)) =
      polyDeriv (complexPoly p) x (Pi.single j 1) := by
  induction p with
  | nil => simp [polynomialRat, complexPoly, polyDeriv]
  | cons t p ih =>
      simp [polynomialRat, complexPoly, polyDeriv,
        aeval_pderiv_monomialRat, ih]

def rationalSystem : Fin 44 → MvPolynomial (Fin 44) ℚ :=
  fun i => polynomialRat (ContactCubicData.integerPolys i)

theorem rationalSystem_zero (x : Space 44)
    (hx : ∀ i, poly (ContactCubicData.polynomials i) x = 0) :
    ∀ i, aeval x (rationalSystem i) = 0 := by
  intro i
  simpa only [rationalSystem, aeval_polynomialRat,
    ContactCubicData.polynomials, complexPoly] using hx i

theorem rationalSystem_det_ne_zero (x : Space 44)
    (hx : Function.Bijective (systemDeriv ContactCubicData.polynomials x)) :
    (Matrix.det fun i j => aeval x (pderiv j (rationalSystem i))) ≠ 0 := by
  let J : Matrix (Fin 44) (Fin 44) ℂ :=
    fun i j => aeval x (pderiv j (rationalSystem i))
  have hJ : matrixCLM J = systemDeriv ContactCubicData.polynomials x := by
    apply matrixCLM_systemDeriv
    intro i j
    exact aeval_pderiv_polynomialRat (ContactCubicData.integerPolys i) x j
  have hmul : Function.Injective J.mulVec := by
    intro v w hvw
    apply hx.1
    simpa only [← hJ, matrixCLM_apply] using hvw
  exact ((Matrix.isUnit_iff_isUnit_det J).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hmul)).ne_zero

#print axioms rationalSystem_zero
#print axioms rationalSystem_det_ne_zero

end ContactRationalPolynomial
