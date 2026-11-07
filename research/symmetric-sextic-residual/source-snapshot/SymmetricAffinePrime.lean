import WeightedPrimitiveTransportCore
import SymmetricPrime

/-!
# The actual reflection chart is integral

This proves irreducibility of the chart equation without assuming a function
field exists.  After exchanging the lambda and b coordinates, the equation is
monic of degree six in b.  A coefficient specialization gives
`b^6 + 2 + 30*T^2 + 30*T^4 + 2*T^6`, which is Eisenstein at `T-I`.

Only this elementary domain construction is proved here.  Existence of the
relative rational primitive remains a separate geometric problem.
-/

noncomputable section

namespace SymmetricAffinePrime

open Polynomial

set_option maxHeartbeats 2000000

def sectionConstant : Polynomial ℂ := 2 + 30*X^2 + 30*X^4 + 2*X^6
def planeSection : Polynomial (Polynomial ℂ) := X ^ 6 + C sectionConstant

theorem sectionConstant_mem : sectionConstant ∈ SymmetricPrime.atI := by
  have hi6 : Complex.I ^ 6 = -1 := by
    calc
      Complex.I ^ 6 = (Complex.I ^ 2)^3 := by rw [← pow_mul]
      _ = -1 := by rw [Complex.I_sq]; norm_num
  rw [SymmetricPrime.atI, Ideal.mem_span_singleton, Polynomial.dvd_iff_isRoot]
  norm_num [sectionConstant, Polynomial.IsRoot, hi6]

theorem sectionConstant_not_mem_square :
    sectionConstant ∉ SymmetricPrime.atI ^ 2 := by
  intro h
  rw [SymmetricPrime.atI, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  have hd : (X - C Complex.I : Polynomial ℂ) ∣ derivative sectionConstant := by
    simpa using Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd h
  have he := Polynomial.dvd_iff_isRoot.mp hd
  have hi5 : Complex.I ^ 5 = Complex.I := by
    calc
      Complex.I ^ 5 = Complex.I ^ 4 * Complex.I := pow_succ _ _
      _ = Complex.I := by rw [Complex.I_pow_four, one_mul]
  norm_num [sectionConstant, Polynomial.IsRoot, Polynomial.derivative_X_pow,
    hi5] at he
  have hz : Complex.I = 0 := by linear_combination (-1/48 : ℂ) * he
  exact Complex.I_ne_zero hz

theorem planeSection_monic : planeSection.Monic :=
  Polynomial.monic_X_pow_add_C sectionConstant (by decide)

theorem planeSection_natDegree : planeSection.natDegree = 6 :=
  Polynomial.natDegree_X_pow_add_C

theorem planeSection_eisenstein : planeSection.IsEisensteinAt SymmetricPrime.atI := by
  constructor
  · rw [planeSection_monic.leadingCoeff, SymmetricPrime.atI, Ideal.mem_span_singleton,
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
  planeSection_eisenstein.irreducible SymmetricPrime.atI_isPrime
    planeSection_monic.isPrimitive (by rw [planeSection_natDegree]; decide)

abbrev CoeffRing := MvPolynomial (Fin 4) ℂ

/-- Extract b as the polynomial variable, with coefficients in (lambda,c,d,v). -/
def bFirst : WeightedPrimitiveTransport.Poly ≃ₐ[ℂ] Polynomial CoeffRing :=
  (MvPolynomial.renameEquiv ℂ (Equiv.swap (0 : Fin 5) 1)).trans
    (MvPolynomial.finSuccEquiv ℂ 4)

def univariateH : Polynomial CoeffRing :=
  bFirst WeightedPrimitiveTransport.chartEquation

def t : CoeffRing := 1 - MvPolynomial.X 3 ^ 2
def q : CoeffRing := MvPolynomial.X 1 ^ 2 +
  2 * MvPolynomial.X 1 * MvPolynomial.X 2 -
  MvPolynomial.X 0 ^ 2 * MvPolynomial.X 3 ^ 2

def coeffTwo : CoeffRing := 4 * MvPolynomial.C (5/7 : ℂ) * q
def coeffOne : CoeffRing := 4 * MvPolynomial.C (5/7 : ℂ) * t*q +
  2 * MvPolynomial.C (10/7 : ℂ) * q^2
def coeffZero : CoeffRing :=
  2 + 2 * MvPolynomial.X 1 ^ 6 + MvPolynomial.X 2 ^ 6 +
    30 * MvPolynomial.X 3 ^ 2 + 30 * MvPolynomial.X 3 ^ 4 +
    2 * MvPolynomial.X 3 ^ 6 +
    30 * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 4 * MvPolynomial.X 3 ^ 2 +
    30 * MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 ^ 2 * MvPolynomial.X 3 ^ 4 +
    2 * MvPolynomial.X 0 ^ 6 * MvPolynomial.X 3 ^ 6 +
    MvPolynomial.C (5/7 : ℂ) * t^2*q +
    MvPolynomial.C (10/7 : ℂ) * t*q^2

theorem bFirst_X (i : Fin 5) :
    bFirst (MvPolynomial.X i) =
      ![C (MvPolynomial.X 0), Polynomial.X, C (MvPolynomial.X 1),
        C (MvPolynomial.X 2), C (MvPolynomial.X 3)] i := by
  fin_cases i <;>
    norm_num [bFirst, MvPolynomial.renameEquiv_apply, MvPolynomial.finSuccEquiv_apply,
      Equiv.swap_apply_def] <;> rfl

theorem bFirst_C (c : ℂ) : bFirst (MvPolynomial.C c) = C (MvPolynomial.C c) := by
  simp [bFirst, MvPolynomial.renameEquiv_apply, MvPolynomial.finSuccEquiv_apply]

theorem univariateH_formula :
    univariateH = X^6 + (C coeffTwo * X^2 + C coeffOne * X + C coeffZero) := by
  simp [univariateH, WeightedPrimitiveTransport.chartEquation,
    WeightedPrimitiveTransport.rawWeighted, WeightedPrimitiveTransport.leftQuadric,
    WeightedPrimitiveTransport.rightQuadric, bFirst_X, bFirst_C,
    coeffTwo, coeffOne, coeffZero, t, q, map_ofNat]
  ring

theorem univariateH_monic : univariateH.Monic := by
  rw [univariateH_formula]
  apply Polynomial.monic_X_pow_add
  exact lt_of_le_of_lt Polynomial.degree_quadratic_le (by norm_num)

/-- Set lambda=c=d=0 and retain v as the coefficient variable. -/
def specializeRest : CoeffRing →+* Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C ![0, 0, 0, Polynomial.X]

theorem specialization_is_planeSection :
    univariateH.map specializeRest = planeSection := by
  rw [univariateH_formula]
  simp [specializeRest, coeffTwo, coeffOne, coeffZero, t, q,
    planeSection, sectionConstant, map_ofNat]

/-- The actual chart polynomial is irreducible, with no geometric assumption. -/
theorem chart_irreducible : Irreducible WeightedPrimitiveTransport.chartEquation := by
  have hu : Irreducible univariateH :=
    Polynomial.Monic.irreducible_of_irreducible_map specializeRest univariateH
      univariateH_monic (by
        rw [specialization_is_planeSection]
        exact planeSection_irreducible)
  exact (MulEquiv.irreducible_iff bFirst).mp hu

theorem chart_prime : Prime WeightedPrimitiveTransport.chartEquation :=
  irreducible_iff_prime.mp chart_irreducible

#print axioms planeSection_irreducible
#print axioms univariateH_formula
#print axioms specialization_is_planeSection
#print axioms chart_irreducible
#print axioms chart_prime

end SymmetricAffinePrime
