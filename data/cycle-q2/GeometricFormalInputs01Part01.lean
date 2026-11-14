import Proposal.Workspace
import HodgeTarget
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.MvPolynomial.Equiv
import HodgeComputer.Constructions.HoldoutCover.HypersurfaceDomain
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import HodgeComputer.CertificateOperations
import HodgeComputer.Verify
import HodgeComputer.Constructions.RationalFields.Calculus
import HodgeComputer.Constructions.FiniteAlgebra.FractionDerivation
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Tactic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Topology.Irreducible
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.LinearAlgebra.Isomorphisms
import Proposal.GeometricSeed
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import HodgeComputer.Constructions.HigherResidues.HigherResidue
import HodgeComputer.Constructions.HoldoutCover.ResidueDerivatives
import HodgeComputer.Constructions.RationalFields.Homogenization
import HodgeComputer.Constructions.RationalFields.CommonDenominatorSubstitution
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Set.Countable
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.HahnSeries.PowerSeries
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.FreeModule.Basic
import HodgeComputer.Constructions.PolynomialCurves.ArithmeticLifting
import HodgeComputer.Constructions.HoldoutCover.GenericIncidence
import Mathlib.RingTheory.Smooth.AdicCompletion

/-! Source partition of GeometricFormalInputs.lean. See solution.md for verification status. -/

set_option Elab.async false

/- Component: geometry/ExactTargetNonsingular.lean -/
section
/-!
# The protected cycle-q2 equation has no nonzero affine critical point

This discharges a concrete premise of the geometric proof. It does not assert
divisor support or certificate existence. There are no admissions or new axioms.

The main theorem is `protected_F_gradient_nonzero`: for every nonzero affine
representative, at least one evaluated formal partial derivative of the actual
protected polynomial is nonzero. No equation-value hypothesis is needed.
-/

noncomputable section

namespace CycleQ2ExactNonsingular

open MvPolynomial

abbrev Poly := HodgeComputer.AmbientPoly 5
abbrev F : Poly := HodgeSubmission.F

/-- The six formal derivatives, in the protected coordinate order. -/
def gradientValue (z : Fin 6 → ℂ) : Fin 6 → ℂ := ![
  6 * z 0 ^ 5 + (3 * (z 0 ^ 2 * z 1 * z 3 * z 4) +
    z 2 ^ 3 * z 5 * z 3) / 2,
  6 * z 1 ^ 5 + (3 * (z 1 ^ 2 * z 2 * z 4 * z 5) +
    z 0 ^ 3 * z 3 * z 4) / 2,
  6 * z 2 ^ 5 + (3 * (z 2 ^ 2 * z 0 * z 5 * z 3) +
    z 1 ^ 3 * z 4 * z 5) / 2,
  6 * z 3 ^ 5 + (1 * (z 0 ^ 3 * z 1 * z 4) +
    z 2 ^ 3 * z 0 * z 5) / 2,
  6 * z 4 ^ 5 + (1 * (z 0 ^ 3 * z 1 * z 3) +
    z 1 ^ 3 * z 2 * z 5) / 2,
  6 * z 5 ^ 5 + (1 * (z 1 ^ 3 * z 2 * z 4) +
    z 2 ^ 3 * z 0 * z 3) / 2]

lemma quadratic_monomial_bound (z : Fin 6 → ℂ) (M : ℝ)
    (hM : 0 ≤ M) (h : ∀ j, ‖z j‖ ≤ M) (i j k l : Fin 6) :
    ‖z i ^ 2 * z j * z k * z l‖ ≤ M ^ 5 := by
  calc
    ‖z i ^ 2 * z j * z k * z l‖ =
        ‖z i‖ ^ 2 * ‖z j‖ * ‖z k‖ * ‖z l‖ := by
      simp only [norm_mul, norm_pow]
    _ ≤ M ^ 2 * M * M * M := by gcongr <;> apply h
    _ = M ^ 5 := by ring

lemma cubic_monomial_bound (z : Fin 6 → ℂ) (M : ℝ)
    (hM : 0 ≤ M) (h : ∀ j, ‖z j‖ ≤ M) (i j k : Fin 6) :
    ‖z i ^ 3 * z j * z k‖ ≤ M ^ 5 := by
  calc
    ‖z i ^ 3 * z j * z k‖ = ‖z i‖ ^ 3 * ‖z j‖ * ‖z k‖ := by
      simp only [norm_mul, norm_pow]
    _ ≤ M ^ 3 * M * M := by gcongr <;> apply h
    _ = M ^ 5 := by ring

/-- A pure sixth-power derivative dominates both mixed terms. -/
lemma dominant_derivative_ne_zero (a b c k : ℂ)
    (ha : 0 < ‖a‖) (hb : ‖b‖ ≤ ‖a‖ ^ 5) (hc : ‖c‖ ≤ ‖a‖ ^ 5)
    (hk : ‖k‖ ≤ 3) :
    6 * a ^ 5 + (k * b + c) / 2 ≠ 0 := by
  intro hz
  have hpert : ‖(k * b + c) / 2‖ ≤ 2 * ‖a‖ ^ 5 := by
    calc
      ‖(k * b + c) / 2‖ = ‖k * b + c‖ / 2 := by
        norm_num [norm_div]
      _ ≤ (‖k * b‖ + ‖c‖) / 2 := by
        gcongr
        exact norm_add_le _ _
      _ = (‖k‖ * ‖b‖ + ‖c‖) / 2 := by rw [norm_mul]
      _ ≤ (3 * ‖a‖ ^ 5 + ‖a‖ ^ 5) / 2 := by gcongr
      _ = 2 * ‖a‖ ^ 5 := by ring
  have heq : (6 : ℂ) * a ^ 5 = -((k * b + c) / 2) :=
    eq_neg_of_add_eq_zero_left hz
  have hn : 6 * ‖a‖ ^ 5 = ‖(k * b + c) / 2‖ := by
    have hn' := congrArg norm heq
    simpa only [norm_mul, norm_pow, norm_neg, Complex.norm_ofNat] using hn'
  have hp : 0 < ‖a‖ ^ 5 := pow_pos ha 5
  linarith

theorem gradientValue_nonzero (z : Fin 6 → ℂ) (hz : z ≠ 0) :
    ∃ i, gradientValue z i ≠ 0 := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun j : Fin 6 => ‖z j‖) (by simp)
  have hmax : ∀ j, ‖z j‖ ≤ ‖z i‖ := fun j => hi j (Finset.mem_univ j)
  have hpos : 0 < ‖z i‖ := by
    by_contra hnot
    have hi0 : ‖z i‖ ≤ 0 := le_of_not_gt hnot
    apply hz
    funext j
    apply norm_eq_zero.mp
    exact le_antisymm ((hmax j).trans hi0) (norm_nonneg _)
  have hnonneg : 0 ≤ ‖z i‖ := norm_nonneg _
  refine ⟨i, ?_⟩
  fin_cases i
  · exact dominant_derivative_ne_zero _ _ _ _ hpos
      (quadratic_monomial_bound z _ hnonneg hmax 0 1 3 4)
      (cubic_monomial_bound z _ hnonneg hmax 2 5 3) (by norm_num)
  · exact dominant_derivative_ne_zero _ _ _ _ hpos
      (quadratic_monomial_bound z _ hnonneg hmax 1 2 4 5)
      (cubic_monomial_bound z _ hnonneg hmax 0 3 4) (by norm_num)
  · exact dominant_derivative_ne_zero _ _ _ _ hpos
      (quadratic_monomial_bound z _ hnonneg hmax 2 0 5 3)
      (cubic_monomial_bound z _ hnonneg hmax 1 4 5) (by norm_num)
  · exact dominant_derivative_ne_zero _ _ _ _ hpos
      (cubic_monomial_bound z _ hnonneg hmax 0 1 4)
      (cubic_monomial_bound z _ hnonneg hmax 2 0 5) (by norm_num)
  · exact dominant_derivative_ne_zero _ _ _ _ hpos
      (cubic_monomial_bound z _ hnonneg hmax 0 1 3)
      (cubic_monomial_bound z _ hnonneg hmax 1 2 5) (by norm_num)
  · exact dominant_derivative_ne_zero _ _ _ _ hpos
      (cubic_monomial_bound z _ hnonneg hmax 1 2 4)
      (cubic_monomial_bound z _ hnonneg hmax 2 0 3) (by norm_num)

/-- Binding the elementary norm argument to the actual protected polynomial. -/
theorem eval_pderiv_F (z : Fin 6 → ℂ) (i : Fin 6) :
    eval z (pderiv i F) = gradientValue z i := by
  fin_cases i <;>
    norm_num [F, HodgeSubmission.F, gradientValue, map_add, pderiv_mul,
      pderiv_pow, pderiv_C, Pi.single_apply, Fin.ext_iff] <;> ring

/-- The needed nonsingularity condition, for the protected `HodgeSubmission.F`. -/
theorem protected_F_gradient_nonzero (z : Fin 6 → ℂ) (hz : z ≠ 0) :
    ∃ i, eval z (pderiv i HodgeSubmission.F) ≠ 0 := by
  obtain ⟨i, hi⟩ := gradientValue_nonzero z hz
  exact ⟨i, by simpa only [← eval_pderiv_F] using hi⟩

#print axioms protected_F_gradient_nonzero

end CycleQ2ExactNonsingular
end
end


/- Component: geometry/ExactTargetIrreducible.lean -/
section
/-!
# Absolute irreducibility of the protected cycle-q2 equation

The coefficient field is already `ℂ`. We view the exact protected polynomial as
monic in X0, then specialize the other variables by
`(X1,X2,Y0,Y1,Y2) = (0,0,t+1,0,I)`. The image is
`X0^6 + (t+1)^6 - 1`, Eisenstein at `t`. Monic specialization reflects
irreducibility. The Eisenstein helper is the existing proved project theorem
`HoldoutConstruction.irreducible_power_add_constant`.

This supplies a genuine premise for coprimality and polynomial divisibility in
the certificate bridge. It does not assert certificate existence.
-/

noncomputable section

namespace CycleQ2ExactIrreducible

open Polynomial

abbrev Coeff := MvPolynomial (Fin 5) ℂ

/-- Coefficients are ordered `(X1,X2,Y0,Y1,Y2)`. -/
def cubicCoeff : Coeff :=
  MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.X 0 *
    MvPolynomial.X 2 * MvPolynomial.X 3

def linearCoeff : Coeff :=
  MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.X 1 ^ 3 *
    MvPolynomial.X 4 * MvPolynomial.X 2

def constantCoeff : Coeff :=
  MvPolynomial.X 0 ^ 6 + MvPolynomial.X 1 ^ 6 + MvPolynomial.X 2 ^ 6 +
    MvPolynomial.X 3 ^ 6 + MvPolynomial.X 4 ^ 6 +
    MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.X 0 ^ 3 *
      MvPolynomial.X 1 * MvPolynomial.X 3 * MvPolynomial.X 4

def univariateF : Coeff[X] :=
  X ^ 6 + (C cubicCoeff * X ^ 3 + (C linearCoeff * X ^ 1 + C constantCoeff))

theorem univariateF_monic : univariateF.Monic := by
  unfold univariateF
  apply monic_X_pow_add
  apply lt_of_le_of_lt (degree_add_le _ _)
  apply max_lt
  · exact lt_of_le_of_lt (degree_C_mul_X_pow_le 3 _) (by decide)
  · apply lt_of_le_of_lt (degree_add_le _ _)
    apply max_lt
    · exact lt_of_le_of_lt (degree_C_mul_X_pow_le 1 _) (by decide)
    · exact lt_of_le_of_lt degree_C_le (by decide)

def coefficientSpecialization : Coeff →+* ℂ[X] :=
  MvPolynomial.eval₂Hom C ![0, 0, X + 1, 0, C Complex.I]

lemma I_pow_six : Complex.I ^ 6 = -1 := by
  calc
    Complex.I ^ 6 = (Complex.I ^ 2) ^ 3 := by ring
    _ = -1 := by rw [Complex.I_sq]; norm_num

theorem univariateF_specialization :
    univariateF.map coefficientSpecialization =
      (X : (ℂ[X])[X]) ^ 6 + C ((X + 1) ^ 6 - 1) := by
  simp [univariateF, cubicCoeff, linearCoeff, constantCoeff,
    coefficientSpecialization, ← map_pow, I_pow_six, sub_eq_add_neg]

theorem univariateF_irreducible : Irreducible univariateF := by
  apply univariateF_monic.irreducible_of_irreducible_map coefficientSpecialization
  rw [univariateF_specialization]
  exact HoldoutConstruction.irreducible_power_add_constant ((X + 1) ^ 6 - 1 : ℂ[X])
    (by simp [coeff_X_add_one_pow])
    (by norm_num [coeff_X_add_one_pow, coeff_one]) 6 (by decide)

/-- Exact binding to the protected polynomial, including all three half-weight
mixed terms. -/
theorem protected_F_univariate :
    MvPolynomial.finSuccEquiv ℂ 5 HodgeSubmission.F = univariateF := by
  have he : (Fin.cases (X : Coeff[X]) (fun j => C (MvPolynomial.X j))) =
      ![X, C (MvPolynomial.X 0), C (MvPolynomial.X 1),
        C (MvPolynomial.X 2), C (MvPolynomial.X 3), C (MvPolynomial.X 4)] := by
    funext i
    fin_cases i <;> rfl
  simp [HodgeSubmission.F, univariateF, cubicCoeff, linearCoeff, constantCoeff,
    MvPolynomial.finSuccEquiv_apply, he]
  ring

theorem protected_F_irreducible : Irreducible HodgeSubmission.F := by
  apply (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv ℂ 5)).mp
  rw [protected_F_univariate]
  exact univariateF_irreducible

theorem protected_F_prime : Prime HodgeSubmission.F :=
  protected_F_irreducible.prime

theorem protected_F_quotient_isDomain :
    IsDomain (HodgeComputer.AmbientPoly 5 ⧸ Ideal.span {HodgeSubmission.F}) :=
  (Ideal.Quotient.isDomain_iff_prime _).mpr
    ((Ideal.span_singleton_prime protected_F_irreducible.ne_zero).mpr protected_F_prime)

#print axioms protected_F_irreducible
#print axioms protected_F_prime
#print axioms protected_F_quotient_isDomain

end CycleQ2ExactIrreducible
end
end


/- Component: higgs/FermatHiggsData.lean -/
section
/-!
Exact monomial data for Chapter 3D's Fermat Higgs forms.
These declarations check finite algebra only, not Hodge-theoretic comparison.
Every finite check below is kernel-reduced `decide`, with no native evaluator.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CycleQ2FermatHiggs

def basisMonomial : Fin 33 → Fin 5 → ℕ := ![
  ![0, 0, 1, 3, 1],
  ![0, 0, 4, 0, 1],
  ![0, 0, 4, 2, 0],
  ![0, 1, 2, 1, 1],
  ![0, 1, 2, 3, 0],
  ![0, 2, 0, 2, 1],
  ![0, 2, 0, 4, 0],
  ![0, 2, 3, 1, 0],
  ![0, 3, 1, 0, 1],
  ![0, 3, 1, 2, 0],
  ![0, 4, 2, 0, 0],
  ![1, 0, 2, 1, 1],
  ![1, 0, 2, 3, 0],
  ![1, 1, 0, 2, 1],
  ![1, 1, 0, 4, 0],
  ![1, 1, 3, 1, 0],
  ![1, 2, 1, 0, 1],
  ![1, 2, 1, 2, 0],
  ![1, 3, 2, 0, 0],
  ![1, 4, 0, 1, 0],
  ![2, 0, 0, 2, 1],
  ![2, 0, 0, 4, 0],
  ![2, 0, 3, 1, 0],
  ![2, 1, 1, 0, 1],
  ![2, 1, 1, 2, 0],
  ![2, 2, 2, 0, 0],
  ![2, 3, 0, 1, 0],
  ![3, 0, 1, 0, 1],
  ![3, 0, 1, 2, 0],
  ![3, 1, 2, 0, 0],
  ![3, 2, 0, 1, 0],
  ![4, 0, 2, 0, 0],
  ![4, 1, 0, 1, 0]]

def tangentMonomial : Fin 35 → Fin 5 → ℕ := ![
  ![0, 0, 0, 4, 1],
  ![0, 0, 3, 1, 1],
  ![0, 0, 3, 3, 0],
  ![0, 1, 1, 2, 1],
  ![0, 1, 1, 4, 0],
  ![0, 1, 4, 1, 0],
  ![0, 2, 2, 0, 1],
  ![0, 2, 2, 2, 0],
  ![0, 3, 0, 1, 1],
  ![0, 3, 0, 3, 0],
  ![0, 3, 3, 0, 0],
  ![0, 4, 1, 1, 0],
  ![1, 0, 1, 2, 1],
  ![1, 0, 1, 4, 0],
  ![1, 0, 4, 1, 0],
  ![1, 1, 2, 0, 1],
  ![1, 1, 2, 2, 0],
  ![1, 2, 0, 1, 1],
  ![1, 2, 0, 3, 0],
  ![1, 2, 3, 0, 0],
  ![1, 3, 1, 1, 0],
  ![2, 0, 2, 0, 1],
  ![2, 0, 2, 2, 0],
  ![2, 1, 0, 1, 1],
  ![2, 1, 0, 3, 0],
  ![2, 1, 3, 0, 0],
  ![2, 2, 1, 1, 0],
  ![2, 4, 0, 0, 0],
  ![3, 0, 0, 1, 1],
  ![3, 0, 0, 3, 0],
  ![3, 0, 3, 0, 0],
  ![3, 1, 1, 1, 0],
  ![3, 3, 0, 0, 0],
  ![4, 0, 1, 1, 0],
  ![4, 2, 0, 0, 0]]

def socle : Fin 5 → ℕ := ![4, 4, 4, 4, 1]

def weightedDegree (a : Fin 5 → ℕ) : ℕ :=
  a 0 + a 1 + a 2 + a 3 + 2 * a 4

def character (a : Fin 5 → ℕ) : ℕ :=
  (2 * a 0 + 2 * a 1 + a 2) % 3

def complement : Fin 35 → Fin 33 → Option (Fin 33) := ![
  ![none, none, none, none, none, none, none, none, none, none, some 31, none, none, none, none, none, none, none, some 29, none, none, none, none, none, none, some 25, none, none, none, some 18, none, some 10, none],
  ![none, none, none, none, none, none, none, none, none, some 32, none, none, none, none, none, none, none, some 30, none, some 28, none, none, none, none, some 26, none, some 24, none, some 19, none, some 17, none, some 9],
  ![none, none, none, none, none, none, none, none, some 32, none, none, none, none, none, none, none, some 30, none, none, some 27, none, none, none, some 26, none, none, some 23, some 19, none, none, some 16, none, some 8],
  ![none, none, none, none, none, none, none, some 32, none, some 31, none, none, none, none, none, some 30, none, some 29, some 28, none, none, none, some 26, none, some 25, some 24, some 22, none, some 18, some 17, some 15, some 9, some 7],
  ![none, none, none, none, none, none, none, none, some 31, none, none, none, none, none, none, none, some 29, none, some 27, none, none, none, none, some 25, none, some 23, none, some 18, none, some 16, none, some 8, none],
  ![none, none, none, none, none, some 32, none, none, none, none, none, none, none, some 30, none, none, none, none, none, none, some 26, none, none, none, none, none, some 20, none, none, none, some 13, none, some 5],
  ![none, none, none, none, some 32, none, some 31, none, none, none, none, none, some 30, none, some 29, none, none, some 28, none, none, none, some 25, none, none, some 24, some 21, none, none, some 17, some 14, some 12, some 6, some 4],
  ![none, none, none, some 32, none, some 31, none, none, none, none, none, some 30, none, some 29, none, none, some 28, some 27, none, none, some 25, none, none, some 24, some 23, some 20, none, some 17, some 16, some 13, some 11, some 5, some 3],
  ![none, none, some 32, none, some 31, none, none, none, none, none, none, none, some 29, none, none, some 28, none, none, none, none, none, none, some 24, none, some 22, none, none, none, some 15, some 12, none, some 4, some 2],
  ![none, some 32, none, some 31, none, none, none, none, none, none, none, some 29, none, none, none, some 27, none, none, none, none, none, none, some 23, some 22, none, none, none, some 15, none, some 11, none, some 3, some 1],
  ![some 32, none, none, none, none, none, none, none, none, none, none, none, none, some 28, some 27, none, none, none, none, none, some 24, some 23, none, some 21, some 20, none, none, some 14, some 13, none, none, none, some 0],
  ![some 31, none, none, none, none, none, none, none, none, none, none, some 28, some 27, none, none, none, none, none, none, none, some 22, none, some 20, none, none, none, none, some 12, some 11, none, none, some 0, none],
  ![none, none, none, none, none, none, none, some 30, none, some 29, some 28, none, none, none, none, some 26, none, some 25, some 24, some 22, none, none, some 19, none, some 18, some 17, some 15, none, some 10, some 9, some 7, none, none],
  ![none, none, none, none, none, none, none, none, some 29, none, some 27, none, none, none, none, none, some 25, none, some 23, none, none, none, none, some 18, none, some 16, none, some 10, none, some 8, none, none, none],
  ![none, none, none, none, none, some 30, none, none, none, none, none, none, none, some 26, none, none, none, none, none, some 20, some 19, none, none, none, none, none, some 13, none, none, none, some 5, none, none],
  ![none, none, none, none, some 30, none, some 29, none, none, some 28, none, none, some 26, none, some 25, none, none, some 24, some 21, none, none, some 18, none, none, some 17, some 14, some 12, none, some 9, some 6, some 4, none, none],
  ![none, none, none, some 30, none, some 29, none, none, some 28, some 27, none, some 26, none, some 25, none, none, some 24, some 23, some 20, none, some 18, none, none, some 17, some 16, some 13, some 11, some 9, some 8, some 5, some 3, none, none],
  ![none, none, some 30, none, some 29, none, none, some 28, none, none, none, none, some 25, none, none, some 24, none, some 22, none, none, none, none, some 17, none, some 15, some 12, none, none, some 7, some 4, some 2, none, none],
  ![none, some 30, none, some 29, none, none, none, some 27, none, none, none, some 25, none, none, none, some 23, some 22, none, none, none, none, none, some 16, some 15, none, some 11, none, some 7, none, some 3, some 1, none, none],
  ![some 30, none, none, none, none, some 28, some 27, none, none, none, none, none, none, some 24, some 23, none, some 21, some 20, none, none, some 17, some 16, none, some 14, some 13, none, none, some 6, some 5, none, some 0, none, none],
  ![some 29, none, none, some 28, some 27, none, none, none, none, none, none, some 24, some 23, some 22, none, some 20, none, none, none, none, some 15, none, some 13, some 12, some 11, none, none, some 4, some 3, some 0, none, none, none],
  ![none, none, none, none, some 26, none, some 25, none, none, some 24, some 21, none, some 19, none, some 18, none, none, some 17, some 14, some 12, none, some 10, none, none, some 9, some 6, some 4, none, none, none, none, none, none],
  ![none, none, none, some 26, none, some 25, none, none, some 24, some 23, some 20, some 19, none, some 18, none, none, some 17, some 16, some 13, some 11, some 10, none, none, some 9, some 8, some 5, some 3, none, none, none, none, none, none],
  ![none, none, some 26, none, some 25, none, none, some 24, none, some 22, none, none, some 18, none, none, some 17, none, some 15, some 12, none, none, none, some 9, none, some 7, some 4, some 2, none, none, none, none, none, none],
  ![none, some 26, none, some 25, none, none, none, some 23, some 22, none, none, some 18, none, none, none, some 16, some 15, none, some 11, none, none, none, some 8, some 7, none, some 3, some 1, none, none, none, none, none, none],
  ![some 26, none, none, none, none, some 24, some 23, none, some 21, some 20, none, none, none, some 17, some 16, none, some 14, some 13, none, none, some 9, some 8, none, some 6, some 5, none, some 0, none, none, none, none, none, none],
  ![some 25, none, none, some 24, some 23, some 22, none, some 20, none, none, none, some 17, some 16, some 15, none, some 13, some 12, some 11, none, none, some 7, none, some 5, some 4, some 3, some 0, none, none, none, none, none, none, none],
  ![some 22, some 21, some 20, none, none, none, none, none, none, none, none, some 12, some 11, none, none, none, none, none, none, none, some 2, some 1, some 0, none, none, none, none, none, none, none, none, none, none],
  ![none, none, some 19, none, some 18, none, none, some 17, none, some 15, some 12, none, some 10, none, none, some 9, none, some 7, some 4, some 2, none, none, none, none, none, none, none, none, none, none, none, none, none],
  ![none, some 19, none, some 18, none, none, none, some 16, some 15, none, some 11, some 10, none, none, none, some 8, some 7, none, some 3, some 1, none, none, none, none, none, none, none, none, none, none, none, none, none],
  ![some 19, none, none, none, none, some 17, some 16, none, some 14, some 13, none, none, none, some 9, some 8, none, some 6, some 5, none, some 0, none, none, none, none, none, none, none, none, none, none, none, none, none],
  ![some 18, none, none, some 17, some 16, some 15, none, some 13, some 12, some 11, none, some 9, some 8, some 7, none, some 5, some 4, some 3, some 0, none, none, none, none, none, none, none, none, none, none, none, none, none, none],
  ![some 15, some 14, some 13, some 12, some 11, none, none, none, none, none, none, some 4, some 3, some 2, some 1, some 0, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none],
  ![some 10, none, none, some 9, some 8, some 7, none, some 5, some 4, some 3, some 0, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none],
  ![some 7, some 6, some 5, some 4, some 3, some 2, some 1, some 0, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]]

theorem basis_properties : ∀ i : Fin 33,
    weightedDegree (basisMonomial i) = 6 ∧ character (basisMonomial i) = 1 ∧
      ∀ k, basisMonomial i k ≤ socle k := by
  decide

theorem tangent_properties : ∀ m : Fin 35,
    weightedDegree (tangentMonomial m) = 6 ∧ character (tangentMonomial m) = 0 ∧
      ∀ k, tangentMonomial m k ≤ socle k := by
  decide

theorem basis_injective : Function.Injective basisMonomial := by
  decide

theorem tangent_injective : Function.Injective tangentMonomial := by
  decide

theorem basis_complete : ∀ a b c d : Fin 5, ∀ w : Fin 2,
    let v : Fin 5 → ℕ := ![a.val, b.val, c.val, d.val, w.val]
    weightedDegree v = 6 → character v = 1 → ∃ i, basisMonomial i = v := by
  intro a
  fin_cases a <;> decide +kernel

theorem tangent_complete : ∀ a b c d : Fin 5, ∀ w : Fin 2,
    let v : Fin 5 → ℕ := ![a.val, b.val, c.val, d.val, w.val]
    weightedDegree v = 6 → character v = 0 → ∃ m, tangentMonomial m = v := by
  intro a
  fin_cases a <;> decide +kernel

def ComplementRow (m : Fin 35) (i : Fin 33) : Prop :=
    match complement m i with
    | some j => ∀ k : Fin 5,
        basisMonomial i k + basisMonomial j k + tangentMonomial m k = socle k
    | none => ∃ k : Fin 5, socle k < basisMonomial i k + tangentMonomial m k

instance (m : Fin 35) (i : Fin 33) : Decidable (ComplementRow m i) := by
  unfold ComplementRow
  split <;> infer_instance

/-- Each nonempty complement is correct; an empty one exceeds the socle
in at least one coordinate. This checks 35 * 33 small cases. -/
theorem complement_row : ∀ m : Fin 35, ∀ i : Fin 33, ComplementRow m i := by
  intro m
  fin_cases m <;> decide +kernel

theorem complement_spec : ∀ m : Fin 35, ∀ i j : Fin 33,
    complement m i = some j ↔
      ∀ k : Fin 5, basisMonomial i k + basisMonomial j k + tangentMonomial m k =
        socle k := by
  intro m i j
  have hr := complement_row m i
  unfold ComplementRow at hr
  cases hc : complement m i with
  | none =>
      simp only [hc] at hr
      constructor
      · intro h
        cases h
      · intro hs
        obtain ⟨k, hk⟩ := hr
        have hh := hs k
        omega
  | some r =>
      simp only [hc] at hr
      constructor
      · intro h
        have he : r = j := Option.some.inj h
        subst r
        exact hr
      · intro hs
        have he : basisMonomial r = basisMonomial j := by
          funext k
          have h1 := hr k
          have h2 := hs k
          omega
        exact congrArg some (basis_injective he)

theorem complement_symm (m : Fin 35) (i j : Fin 33) :
    complement m i = some j ↔ complement m j = some i := by
  rw [complement_spec, complement_spec]
  simp only [Nat.add_comm (basisMonomial i _) (basisMonomial j _)]

def higgsMatrix (K : Type*) [Zero K] [One K] (m : Fin 35) :
    Matrix (Fin 33) (Fin 33) K :=
  fun i j => if complement m i = some j then 1 else 0

theorem higgsMatrix_socle (K : Type*) [Zero K] [One K]
    (m : Fin 35) (i j : Fin 33) :
    higgsMatrix K m i j =
      if (∀ k : Fin 5, basisMonomial i k + basisMonomial j k +
          tangentMonomial m k = socle k) then 1 else 0 := by
  simp only [higgsMatrix, complement_spec]

end CycleQ2FermatHiggs

#print axioms CycleQ2FermatHiggs.complement_spec
#print axioms CycleQ2FermatHiggs.basis_complete
end


