import Proposal.SymmetricReflections
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Primality of the exact protected symmetric sextic

View the protected F as a monic polynomial in X0 over the polynomial ring in
the other five variables. Specializing X1=X2=Y2=0 and Y1=1 gives X0^6+Y0^6+1.
This polynomial is Eisenstein at Y0-I: Y0^6+1 vanishes simply at I. Monic
specialization lifts irreducibility to the actual F, and unique factorization
gives primality. No geometric theorem or certificate-existence assumption is
used in this proof.
-/

noncomputable section

namespace SymmetricPrime

open Polynomial

set_option maxHeartbeats 1000000

/-- The constant coefficient of the Eisenstein section. -/
def sectionConstant : Polynomial ℂ := X ^ 6 + 1

/-- X0^6 + Y0^6 + 1, with X0 the outer polynomial variable. -/
def planeSection : Polynomial (Polynomial ℂ) := X ^ 6 + C sectionConstant

def atI : Ideal (Polynomial ℂ) := Ideal.span {X - C Complex.I}

theorem sectionConstant_mem : sectionConstant ∈ atI := by
  have hi6 : Complex.I ^ 6 = -1 := by
    calc
      Complex.I ^ 6 = (Complex.I ^ 2) ^ 3 := by rw [← pow_mul]
      _ = -1 := by rw [Complex.I_sq]; norm_num
  rw [atI, Ideal.mem_span_singleton, Polynomial.dvd_iff_isRoot]
  simp [sectionConstant, Polynomial.IsRoot, hi6]

theorem sectionConstant_not_mem_square : sectionConstant ∉ atI ^ 2 := by
  intro h
  rw [atI, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  have hd : (X - C Complex.I : Polynomial ℂ) ∣ derivative sectionConstant := by
    simpa using Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd h
  have he := Polynomial.dvd_iff_isRoot.mp hd
  norm_num [sectionConstant, Polynomial.IsRoot, Polynomial.derivative_X_pow] at he

theorem atI_isPrime : atI.IsPrime := by
  exact (Ideal.span_singleton_prime (Polynomial.X_sub_C_ne_zero Complex.I)).mpr
    (Polynomial.prime_X_sub_C Complex.I)

theorem planeSection_monic : planeSection.Monic :=
  Polynomial.monic_X_pow_add_C sectionConstant (by decide)

theorem planeSection_natDegree : planeSection.natDegree = 6 :=
  Polynomial.natDegree_X_pow_add_C

theorem planeSection_eisenstein : planeSection.IsEisensteinAt atI := by
  constructor
  · rw [planeSection_monic.leadingCoeff, atI, Ideal.mem_span_singleton,
      Polynomial.dvd_iff_isRoot]
    simp [Polynomial.IsRoot]
  · intro n hn
    rw [planeSection_natDegree] at hn
    by_cases hn0 : n = 0
    · subst n
      simpa [planeSection] using sectionConstant_mem
    · have h6n : 6 ≠ n := by omega
      simp [planeSection, Polynomial.coeff_X_pow, Polynomial.coeff_C, hn0, Ne.symm h6n]
  · simpa [planeSection] using sectionConstant_not_mem_square

theorem planeSection_irreducible : Irreducible planeSection :=
  planeSection_eisenstein.irreducible atI_isPrime planeSection_monic.isPrimitive
    (by rw [planeSection_natDegree]; decide)

/-- Coefficients in the variables X1,X2,Y0,Y1,Y2, in this order. -/
abbrev CoeffRing := MvPolynomial (Fin 5) ℂ

def univariateF : Polynomial CoeffRing :=
  MvPolynomial.finSuccEquiv ℂ 5 HodgeSubmission.F

def restQY : CoeffRing :=
  MvPolynomial.X 2 * MvPolynomial.X 3 +
  MvPolynomial.X 2 * MvPolynomial.X 4 +
  MvPolynomial.X 3 * MvPolynomial.X 4

def coeffTwo : CoeffRing :=
  MvPolynomial.C (1 / 7 : ℂ) *
    (5 * (MvPolynomial.X 0 + MvPolynomial.X 1) ^ 2 * restQY)

def coeffOne : CoeffRing :=
  MvPolynomial.C (1 / 7 : ℂ) *
    (10 * (MvPolynomial.X 0 + MvPolynomial.X 1) *
      (MvPolynomial.X 0 * MvPolynomial.X 1) * restQY +
     10 * (MvPolynomial.X 0 + MvPolynomial.X 1) * restQY ^ 2)

def coeffZero : CoeffRing :=
  MvPolynomial.X 0 ^ 6 + MvPolynomial.X 1 ^ 6 +
  MvPolynomial.X 2 ^ 6 + MvPolynomial.X 3 ^ 6 + MvPolynomial.X 4 ^ 6 +
  MvPolynomial.C (1 / 7 : ℂ) *
    (5 * (MvPolynomial.X 0 * MvPolynomial.X 1) ^ 2 * restQY +
     10 * (MvPolynomial.X 0 * MvPolynomial.X 1) * restQY ^ 2)

theorem univariateF_formula :
    univariateF = X ^ 6 + (C coeffTwo * X ^ 2 + C coeffOne * X + C coeffZero) := by
  have hX : ∀ i : Fin 6, MvPolynomial.finSuccEquiv ℂ 5 (MvPolynomial.X i) =
      ![Polynomial.X, C (MvPolynomial.X 0), C (MvPolynomial.X 1),
        C (MvPolynomial.X 2), C (MvPolynomial.X 3), C (MvPolynomial.X 4)] i := by
    intro i
    fin_cases i <;> simp [MvPolynomial.finSuccEquiv_apply] <;> rfl
  have hC : ∀ c : ℂ, MvPolynomial.finSuccEquiv ℂ 5 (MvPolynomial.C c) =
      C (MvPolynomial.C c) := by
    intro c
    simp [MvPolynomial.finSuccEquiv_apply]
  rw [univariateF, SymmetricReflections.exactF_compact]
  simp [hX, hC, SymmetricReflections.compactF,
    SymmetricReflections.QX, SymmetricReflections.QY,
    coeffTwo, coeffOne, coeffZero, restQY, map_ofNat]
  ring

theorem univariateF_monic : univariateF.Monic := by
  rw [univariateF_formula]
  apply Polynomial.monic_X_pow_add
  exact lt_of_le_of_lt Polynomial.degree_quadratic_le (by norm_num)

/-- The coefficient specialization leaves Y0 as a polynomial variable. -/
def specializeRest : CoeffRing →+* Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C ![0, 0, Polynomial.X, 1, 0]

theorem specialization_is_planeSection : univariateF.map specializeRest = planeSection := by
  rw [univariateF_formula]
  simp [specializeRest, coeffTwo, coeffOne, coeffZero, restQY,
    planeSection, sectionConstant]

/-- Irreducibility of the actual protected six-variable polynomial. -/
theorem target_irreducible : Irreducible HodgeSubmission.F := by
  have hu : Irreducible univariateF :=
    Polynomial.Monic.irreducible_of_irreducible_map specializeRest univariateF
      univariateF_monic (by rw [specialization_is_planeSection]; exact planeSection_irreducible)
  exact (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv ℂ 5)).mp hu

/-- The prime-element hypothesis needed for automatic legal clearing. -/
theorem target_prime : Prime (HodgeSubmission.F : HodgeComputer.AmbientPoly 5) :=
  irreducible_iff_prime.mp target_irreducible

#print axioms sectionConstant_not_mem_square
#print axioms planeSection_irreducible
#print axioms univariateF_monic
#print axioms specialization_is_planeSection
#print axioms target_irreducible
#print axioms target_prime

end SymmetricPrime
