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

/-!
# Checked inputs for the nonconstructive cycle-q2 route

This module proves the complete algebraic implication from an actual affine
residue primitive to the unchanged protected certificate. The function field,
derivations, residue map, normal-source identity, lifts, homogeneous degrees,
and legal denominator clearing are all bound to the actual protected target.
The actual relative Kaehler module, exterior powers, and degree-three exterior
derivative are constructed. Exactness of the resulting source form is proved
equivalent to the residue PDE. A genuine formal normal chart sends f to T;
the Laurent residue of its pole-three density is proved to be that source.
The actual universal exterior pullback has the proved normal Jacobian factor;
the coefficient tangents obey the corresponding implicit chain rule.
It does not prove that the residue primitive or exterior-form primitive exists.

The finite Higgs matrices are bound to the actual Fermat Jacobian quotient,
graded bases, and socle trace. The sparse seed matrix is bound to an actual
quotient trace. Their identification with geometric Hodge/Abel--Jacobi maps
and the support theorem remain separate obligations. Gradient nonvanishing
is a proved polynomial statement, not a formal geometric Jacobian criterion.

The affine route uses elementary normal-pole reduction and unrestricted
legal denominators. It requires no mixed-Hodge-module strictness or Bott
vanishing. A proof of geometric support and its global algebraic de Rham
comparison with the actual residue primitive is still missing. Countable
algebraic avoidance is proved for actual complex coefficient spaces.
Formal lifting and coefficient extraction do not assert algebraization of
a formal primitive. The one-mixed-term certificate is proved for that distinct
family only; the protected target has all three mixed terms.
The actual Cartier-curve cubic matrix factorization and exactness of its
periodic quotient complex are proved. The actual Segre seed identities,
cofactor relations, local image line, transition cocycle, and universal
logarithmic differentials are proved. Square polynomial systems have genuine
formal lifts and finite separable generic solutions on prescribed opens.
An invertible complementary relation block forces all residual equations.
The actual large incidence system's quotient normal forms and seed minors
are not yet bound to these lifting theorems. These algebraic results do not
assert the geometric cylinder map or generation of invariant cohomology.
The paired-sign weighted equation and source are also bound to the actual
function field. Three concrete derivations preserve its pencil parameter;
their relative primitive equation implies the protected four-variable
residue equation by an explicit divergence identity. Existence of that
relative primitive remains a separate obligation.

All finite checks use ordinary kernel-checked proofs. The source generator
and its spanning-forest choices are outside the trust boundary.

This consolidation uses one proposal file so the preserved legacy route and
all new inputs remain within the protected 64-file submission limit.
-/

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
  intro a b c d w
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    fin_cases w <;> decide +kernel

theorem tangent_complete : ∀ a b c d : Fin 5, ∀ w : Fin 2,
    let v : Fin 5 → ℕ := ![a.val, b.val, c.val, d.val, w.val]
    weightedDegree v = 6 → character v = 0 → ∃ m, tangentMonomial m = v := by
  intro a b c d w
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    fin_cases w <;> decide +kernel

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


/- Component: higgs/FermatHiggs.lean -/
section
/-!
Exact scalar-commutant theorem for all 35 Fermat Higgs forms.
The proof uses a spanning forest of the entry-equality constraints. Every
edge below is checked as a literal instance of the supplied matrix equation.
The theorem applies over any semiring; no modular rank inference is used.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CycleQ2FermatHiggs
open scoped BigOperators

def entryConstraints {K : Type*} [Zero K] (P : Matrix (Fin 33) (Fin 33) K) : Prop :=
  ∀ m : Fin 35, ∀ i j : Fin 33,
    (match complement m j with | none => 0 | some k => P k i) =
    (match complement m i with | none => 0 | some k => P k j)

theorem scalar_of_entryConstraints {K : Type*} [Zero K]
    (P : Matrix (Fin 33) (Fin 33) K) (h : entryConstraints P) :
    ∃ c : K, ∀ i j, P i j = if i = j then c else 0 := by
  have h0 : P 0 0 = P 0 0 := rfl
  have h1023 : P 31 0 = 0 := (h 0 0 10)
  have h957 : P 29 0 = 0 := (h 0 0 18)
  have h825 : P 25 0 = 0 := (h 0 0 25)
  have h594 : P 18 0 = 0 := (h 0 0 29)
  have h330 : P 10 0 = 0 := (h 0 0 31)
  have h1024 : P 31 1 = 0 := (h 0 1 10)
  have h958 : P 29 1 = 0 := (h 0 1 18)
  have h826 : P 25 1 = 0 := (h 0 1 25)
  have h595 : P 18 1 = 0 := (h 0 1 29)
  have h331 : P 10 1 = 0 := (h 0 1 31)
  have h1025 : P 31 2 = 0 := (h 0 2 10)
  have h959 : P 29 2 = 0 := (h 0 2 18)
  have h827 : P 25 2 = 0 := (h 0 2 25)
  have h596 : P 18 2 = 0 := (h 0 2 29)
  have h332 : P 10 2 = 0 := (h 0 2 31)
  have h1026 : P 31 3 = 0 := (h 0 3 10)
  have h960 : P 29 3 = 0 := (h 0 3 18)
  have h828 : P 25 3 = 0 := (h 0 3 25)
  have h597 : P 18 3 = 0 := (h 0 3 29)
  have h333 : P 10 3 = 0 := (h 0 3 31)
  have h1027 : P 31 4 = 0 := (h 0 4 10)
  have h961 : P 29 4 = 0 := (h 0 4 18)
  have h829 : P 25 4 = 0 := (h 0 4 25)
  have h598 : P 18 4 = 0 := (h 0 4 29)
  have h334 : P 10 4 = 0 := (h 0 4 31)
  have h1028 : P 31 5 = 0 := (h 0 5 10)
  have h962 : P 29 5 = 0 := (h 0 5 18)
  have h830 : P 25 5 = 0 := (h 0 5 25)
  have h599 : P 18 5 = 0 := (h 0 5 29)
  have h335 : P 10 5 = 0 := (h 0 5 31)
  have h1029 : P 31 6 = 0 := (h 0 6 10)
  have h963 : P 29 6 = 0 := (h 0 6 18)
  have h831 : P 25 6 = 0 := (h 0 6 25)
  have h600 : P 18 6 = 0 := (h 0 6 29)
  have h336 : P 10 6 = 0 := (h 0 6 31)
  have h1030 : P 31 7 = 0 := (h 0 7 10)
  have h964 : P 29 7 = 0 := (h 0 7 18)
  have h832 : P 25 7 = 0 := (h 0 7 25)
  have h601 : P 18 7 = 0 := (h 0 7 29)
  have h337 : P 10 7 = 0 := (h 0 7 31)
  have h1031 : P 31 8 = 0 := (h 0 8 10)
  have h965 : P 29 8 = 0 := (h 0 8 18)
  have h833 : P 25 8 = 0 := (h 0 8 25)
  have h602 : P 18 8 = 0 := (h 0 8 29)
  have h338 : P 10 8 = 0 := (h 0 8 31)
  have h1032 : P 31 9 = 0 := (h 0 9 10)
  have h966 : P 29 9 = 0 := (h 0 9 18)
  have h834 : P 25 9 = 0 := (h 0 9 25)
  have h603 : P 18 9 = 0 := (h 0 9 29)
  have h339 : P 10 9 = 0 := (h 0 9 31)
  have h1034 : P 31 11 = 0 := (h 0 10 11).symm
  have h1035 : P 31 12 = 0 := (h 0 10 12).symm
  have h1036 : P 31 13 = 0 := (h 0 10 13).symm
  have h1037 : P 31 14 = 0 := (h 0 10 14).symm
  have h1038 : P 31 15 = 0 := (h 0 10 15).symm
  have h1039 : P 31 16 = 0 := (h 0 10 16).symm
  have h1040 : P 31 17 = 0 := (h 0 10 17).symm
  have h1042 : P 31 19 = 0 := (h 0 10 19).symm
  have h1043 : P 31 20 = 0 := (h 0 10 20).symm
  have h1044 : P 31 21 = 0 := (h 0 10 21).symm
  have h1045 : P 31 22 = 0 := (h 0 10 22).symm
  have h1046 : P 31 23 = 0 := (h 0 10 23).symm
  have h1047 : P 31 24 = 0 := (h 0 10 24).symm
  have h1049 : P 31 26 = 0 := (h 0 10 26).symm
  have h1050 : P 31 27 = 0 := (h 0 10 27).symm
  have h1051 : P 31 28 = 0 := (h 0 10 28).symm
  have h1053 : P 31 30 = 0 := (h 0 10 30).symm
  have h1055 : P 31 32 = 0 := (h 0 10 32).symm
  have h968 : P 29 11 = 0 := (h 0 11 18)
  have h836 : P 25 11 = 0 := (h 0 11 25)
  have h605 : P 18 11 = 0 := (h 0 11 29)
  have h341 : P 10 11 = 0 := (h 0 11 31)
  have h969 : P 29 12 = 0 := (h 0 12 18)
  have h837 : P 25 12 = 0 := (h 0 12 25)
  have h606 : P 18 12 = 0 := (h 0 12 29)
  have h342 : P 10 12 = 0 := (h 0 12 31)
  have h970 : P 29 13 = 0 := (h 0 13 18)
  have h838 : P 25 13 = 0 := (h 0 13 25)
  have h607 : P 18 13 = 0 := (h 0 13 29)
  have h343 : P 10 13 = 0 := (h 0 13 31)
  have h971 : P 29 14 = 0 := (h 0 14 18)
  have h839 : P 25 14 = 0 := (h 0 14 25)
  have h608 : P 18 14 = 0 := (h 0 14 29)
  have h344 : P 10 14 = 0 := (h 0 14 31)
  have h972 : P 29 15 = 0 := (h 0 15 18)
  have h840 : P 25 15 = 0 := (h 0 15 25)
  have h609 : P 18 15 = 0 := (h 0 15 29)
  have h345 : P 10 15 = 0 := (h 0 15 31)
  have h973 : P 29 16 = 0 := (h 0 16 18)
  have h841 : P 25 16 = 0 := (h 0 16 25)
  have h610 : P 18 16 = 0 := (h 0 16 29)
  have h346 : P 10 16 = 0 := (h 0 16 31)
  have h974 : P 29 17 = 0 := (h 0 17 18)
  have h842 : P 25 17 = 0 := (h 0 17 25)
  have h611 : P 18 17 = 0 := (h 0 17 29)
  have h347 : P 10 17 = 0 := (h 0 17 31)
  have h976 : P 29 19 = 0 := (h 0 18 19).symm
  have h977 : P 29 20 = 0 := (h 0 18 20).symm
  have h978 : P 29 21 = 0 := (h 0 18 21).symm
  have h979 : P 29 22 = 0 := (h 0 18 22).symm
  have h980 : P 29 23 = 0 := (h 0 18 23).symm
  have h981 : P 29 24 = 0 := (h 0 18 24).symm
  have h983 : P 29 26 = 0 := (h 0 18 26).symm
  have h984 : P 29 27 = 0 := (h 0 18 27).symm
  have h985 : P 29 28 = 0 := (h 0 18 28).symm
  have h987 : P 29 30 = 0 := (h 0 18 30).symm
  have h989 : P 29 32 = 0 := (h 0 18 32).symm
  have h844 : P 25 19 = 0 := (h 0 19 25)
  have h613 : P 18 19 = 0 := (h 0 19 29)
  have h349 : P 10 19 = 0 := (h 0 19 31)
  have h845 : P 25 20 = 0 := (h 0 20 25)
  have h614 : P 18 20 = 0 := (h 0 20 29)
  have h350 : P 10 20 = 0 := (h 0 20 31)
  have h846 : P 25 21 = 0 := (h 0 21 25)
  have h615 : P 18 21 = 0 := (h 0 21 29)
  have h351 : P 10 21 = 0 := (h 0 21 31)
  have h847 : P 25 22 = 0 := (h 0 22 25)
  have h616 : P 18 22 = 0 := (h 0 22 29)
  have h352 : P 10 22 = 0 := (h 0 22 31)
  have h848 : P 25 23 = 0 := (h 0 23 25)
  have h617 : P 18 23 = 0 := (h 0 23 29)
  have h353 : P 10 23 = 0 := (h 0 23 31)
  have h849 : P 25 24 = 0 := (h 0 24 25)
  have h618 : P 18 24 = 0 := (h 0 24 29)
  have h354 : P 10 24 = 0 := (h 0 24 31)
  have h851 : P 25 26 = 0 := (h 0 25 26).symm
  have h852 : P 25 27 = 0 := (h 0 25 27).symm
  have h853 : P 25 28 = 0 := (h 0 25 28).symm
  have h855 : P 25 30 = 0 := (h 0 25 30).symm
  have h857 : P 25 32 = 0 := (h 0 25 32).symm
  have h620 : P 18 26 = 0 := (h 0 26 29)
  have h356 : P 10 26 = 0 := (h 0 26 31)
  have h621 : P 18 27 = 0 := (h 0 27 29)
  have h357 : P 10 27 = 0 := (h 0 27 31)
  have h622 : P 18 28 = 0 := (h 0 28 29)
  have h358 : P 10 28 = 0 := (h 0 28 31)
  have h624 : P 18 30 = 0 := (h 0 29 30).symm
  have h626 : P 18 32 = 0 := (h 0 29 32).symm
  have h360 : P 10 30 = 0 := (h 0 30 31)
  have h362 : P 10 32 = 0 := (h 0 31 32).symm
  have h1056 : P 32 0 = 0 := (h 1 0 9)
  have h990 : P 30 0 = 0 := (h 1 0 17)
  have h924 : P 28 0 = 0 := (h 1 0 19)
  have h858 : P 26 0 = 0 := (h 1 0 24)
  have h792 : P 24 0 = 0 := (h 1 0 26)
  have h627 : P 19 0 = 0 := (h 1 0 28)
  have h561 : P 17 0 = 0 := (h 1 0 30)
  have h297 : P 9 0 = 0 := (h 1 0 32)
  have h1057 : P 32 1 = 0 := (h 1 1 9)
  have h991 : P 30 1 = 0 := (h 1 1 17)
  have h925 : P 28 1 = 0 := (h 1 1 19)
  have h859 : P 26 1 = 0 := (h 1 1 24)
  have h793 : P 24 1 = 0 := (h 1 1 26)
  have h628 : P 19 1 = 0 := (h 1 1 28)
  have h562 : P 17 1 = 0 := (h 1 1 30)
  have h298 : P 9 1 = 0 := (h 1 1 32)
  have h1058 : P 32 2 = 0 := (h 1 2 9)
  have h992 : P 30 2 = 0 := (h 1 2 17)
  have h926 : P 28 2 = 0 := (h 1 2 19)
  have h860 : P 26 2 = 0 := (h 1 2 24)
  have h794 : P 24 2 = 0 := (h 1 2 26)
  have h629 : P 19 2 = 0 := (h 1 2 28)
  have h563 : P 17 2 = 0 := (h 1 2 30)
  have h299 : P 9 2 = 0 := (h 1 2 32)
  have h1059 : P 32 3 = 0 := (h 1 3 9)
  have h993 : P 30 3 = 0 := (h 1 3 17)
  have h927 : P 28 3 = 0 := (h 1 3 19)
  have h861 : P 26 3 = 0 := (h 1 3 24)
  have h795 : P 24 3 = 0 := (h 1 3 26)
  have h630 : P 19 3 = 0 := (h 1 3 28)
  have h564 : P 17 3 = 0 := (h 1 3 30)
  have h300 : P 9 3 = 0 := (h 1 3 32)
  have h1060 : P 32 4 = 0 := (h 1 4 9)
  have h994 : P 30 4 = 0 := (h 1 4 17)
  have h928 : P 28 4 = 0 := (h 1 4 19)
  have h862 : P 26 4 = 0 := (h 1 4 24)
  have h796 : P 24 4 = 0 := (h 1 4 26)
  have h631 : P 19 4 = 0 := (h 1 4 28)
  have h565 : P 17 4 = 0 := (h 1 4 30)
  have h301 : P 9 4 = 0 := (h 1 4 32)
  have h1061 : P 32 5 = 0 := (h 1 5 9)
  have h995 : P 30 5 = 0 := (h 1 5 17)
  have h929 : P 28 5 = 0 := (h 1 5 19)
  have h863 : P 26 5 = 0 := (h 1 5 24)
  have h797 : P 24 5 = 0 := (h 1 5 26)
  have h632 : P 19 5 = 0 := (h 1 5 28)
  have h566 : P 17 5 = 0 := (h 1 5 30)
  have h302 : P 9 5 = 0 := (h 1 5 32)
  have h1062 : P 32 6 = 0 := (h 1 6 9)
  have h996 : P 30 6 = 0 := (h 1 6 17)
  have h930 : P 28 6 = 0 := (h 1 6 19)
  have h864 : P 26 6 = 0 := (h 1 6 24)
  have h798 : P 24 6 = 0 := (h 1 6 26)
  have h633 : P 19 6 = 0 := (h 1 6 28)
  have h567 : P 17 6 = 0 := (h 1 6 30)
  have h303 : P 9 6 = 0 := (h 1 6 32)
  have h1063 : P 32 7 = 0 := (h 1 7 9)
  have h997 : P 30 7 = 0 := (h 1 7 17)
  have h931 : P 28 7 = 0 := (h 1 7 19)
  have h865 : P 26 7 = 0 := (h 1 7 24)
  have h799 : P 24 7 = 0 := (h 1 7 26)
  have h634 : P 19 7 = 0 := (h 1 7 28)
  have h568 : P 17 7 = 0 := (h 1 7 30)
  have h304 : P 9 7 = 0 := (h 1 7 32)
  have h1064 : P 32 8 = 0 := (h 1 8 9)
  have h998 : P 30 8 = 0 := (h 1 8 17)
  have h932 : P 28 8 = 0 := (h 1 8 19)
  have h866 : P 26 8 = 0 := (h 1 8 24)
  have h800 : P 24 8 = 0 := (h 1 8 26)
  have h635 : P 19 8 = 0 := (h 1 8 28)
  have h569 : P 17 8 = 0 := (h 1 8 30)
  have h305 : P 9 8 = 0 := (h 1 8 32)
  have h1066 : P 32 10 = 0 := (h 1 9 10).symm
  have h1067 : P 32 11 = 0 := (h 1 9 11).symm
  have h1068 : P 32 12 = 0 := (h 1 9 12).symm
  have h1069 : P 32 13 = 0 := (h 1 9 13).symm
  have h1070 : P 32 14 = 0 := (h 1 9 14).symm
  have h1071 : P 32 15 = 0 := (h 1 9 15).symm
  have h1072 : P 32 16 = 0 := (h 1 9 16).symm
  have h1074 : P 32 18 = 0 := (h 1 9 18).symm
  have h1076 : P 32 20 = 0 := (h 1 9 20).symm
  have h1077 : P 32 21 = 0 := (h 1 9 21).symm
  have h1078 : P 32 22 = 0 := (h 1 9 22).symm
  have h1079 : P 32 23 = 0 := (h 1 9 23).symm
  have h1081 : P 32 25 = 0 := (h 1 9 25).symm
  have h1083 : P 32 27 = 0 := (h 1 9 27).symm
  have h1085 : P 32 29 = 0 := (h 1 9 29).symm
  have h1087 : P 32 31 = 0 := (h 1 9 31).symm
  have h1000 : P 30 10 = 0 := (h 1 10 17)
  have h934 : P 28 10 = 0 := (h 1 10 19)
  have h868 : P 26 10 = 0 := (h 1 10 24)
  have h802 : P 24 10 = 0 := (h 1 10 26)
  have h637 : P 19 10 = 0 := (h 1 10 28)
  have h571 : P 17 10 = 0 := (h 1 10 30)
  have h307 : P 9 10 = 0 := (h 1 10 32)
  have h1001 : P 30 11 = 0 := (h 1 11 17)
  have h935 : P 28 11 = 0 := (h 1 11 19)
  have h869 : P 26 11 = 0 := (h 1 11 24)
  have h803 : P 24 11 = 0 := (h 1 11 26)
  have h638 : P 19 11 = 0 := (h 1 11 28)
  have h572 : P 17 11 = 0 := (h 1 11 30)
  have h308 : P 9 11 = 0 := (h 1 11 32)
  have h1002 : P 30 12 = 0 := (h 1 12 17)
  have h936 : P 28 12 = 0 := (h 1 12 19)
  have h870 : P 26 12 = 0 := (h 1 12 24)
  have h804 : P 24 12 = 0 := (h 1 12 26)
  have h639 : P 19 12 = 0 := (h 1 12 28)
  have h573 : P 17 12 = 0 := (h 1 12 30)
  have h309 : P 9 12 = 0 := (h 1 12 32)
  have h1003 : P 30 13 = 0 := (h 1 13 17)
  have h937 : P 28 13 = 0 := (h 1 13 19)
  have h871 : P 26 13 = 0 := (h 1 13 24)
  have h805 : P 24 13 = 0 := (h 1 13 26)
  have h640 : P 19 13 = 0 := (h 1 13 28)
  have h574 : P 17 13 = 0 := (h 1 13 30)
  have h310 : P 9 13 = 0 := (h 1 13 32)
  have h1004 : P 30 14 = 0 := (h 1 14 17)
  have h938 : P 28 14 = 0 := (h 1 14 19)
  have h872 : P 26 14 = 0 := (h 1 14 24)
  have h806 : P 24 14 = 0 := (h 1 14 26)
  have h641 : P 19 14 = 0 := (h 1 14 28)
  have h575 : P 17 14 = 0 := (h 1 14 30)
  have h311 : P 9 14 = 0 := (h 1 14 32)
  have h1005 : P 30 15 = 0 := (h 1 15 17)
  have h939 : P 28 15 = 0 := (h 1 15 19)
  have h873 : P 26 15 = 0 := (h 1 15 24)
  have h807 : P 24 15 = 0 := (h 1 15 26)
  have h642 : P 19 15 = 0 := (h 1 15 28)
  have h576 : P 17 15 = 0 := (h 1 15 30)
  have h312 : P 9 15 = 0 := (h 1 15 32)
  have h1006 : P 30 16 = 0 := (h 1 16 17)
  have h940 : P 28 16 = 0 := (h 1 16 19)
  have h874 : P 26 16 = 0 := (h 1 16 24)
  have h808 : P 24 16 = 0 := (h 1 16 26)
  have h643 : P 19 16 = 0 := (h 1 16 28)
  have h577 : P 17 16 = 0 := (h 1 16 30)
  have h313 : P 9 16 = 0 := (h 1 16 32)
  have h1008 : P 30 18 = 0 := (h 1 17 18).symm
  have h1010 : P 30 20 = 0 := (h 1 17 20).symm
  have h1011 : P 30 21 = 0 := (h 1 17 21).symm
  have h1012 : P 30 22 = 0 := (h 1 17 22).symm
  have h1013 : P 30 23 = 0 := (h 1 17 23).symm
  have h1015 : P 30 25 = 0 := (h 1 17 25).symm
  have h1017 : P 30 27 = 0 := (h 1 17 27).symm
  have h1019 : P 30 29 = 0 := (h 1 17 29).symm
  have h1021 : P 30 31 = 0 := (h 1 17 31).symm
  have h942 : P 28 18 = 0 := (h 1 18 19)
  have h876 : P 26 18 = 0 := (h 1 18 24)
  have h810 : P 24 18 = 0 := (h 1 18 26)
  have h645 : P 19 18 = 0 := (h 1 18 28)
  have h579 : P 17 18 = 0 := (h 1 18 30)
  have h315 : P 9 18 = 0 := (h 1 18 32)
  have h944 : P 28 20 = 0 := (h 1 19 20).symm
  have h945 : P 28 21 = 0 := (h 1 19 21).symm
  have h946 : P 28 22 = 0 := (h 1 19 22).symm
  have h947 : P 28 23 = 0 := (h 1 19 23).symm
  have h949 : P 28 25 = 0 := (h 1 19 25).symm
  have h951 : P 28 27 = 0 := (h 1 19 27).symm
  have h953 : P 28 29 = 0 := (h 1 19 29).symm
  have h955 : P 28 31 = 0 := (h 1 19 31).symm
  have h878 : P 26 20 = 0 := (h 1 20 24)
  have h812 : P 24 20 = 0 := (h 1 20 26)
  have h647 : P 19 20 = 0 := (h 1 20 28)
  have h581 : P 17 20 = 0 := (h 1 20 30)
  have h317 : P 9 20 = 0 := (h 1 20 32)
  have h879 : P 26 21 = 0 := (h 1 21 24)
  have h813 : P 24 21 = 0 := (h 1 21 26)
  have h648 : P 19 21 = 0 := (h 1 21 28)
  have h582 : P 17 21 = 0 := (h 1 21 30)
  have h318 : P 9 21 = 0 := (h 1 21 32)
  have h880 : P 26 22 = 0 := (h 1 22 24)
  have h814 : P 24 22 = 0 := (h 1 22 26)
  have h649 : P 19 22 = 0 := (h 1 22 28)
  have h583 : P 17 22 = 0 := (h 1 22 30)
  have h319 : P 9 22 = 0 := (h 1 22 32)
  have h881 : P 26 23 = 0 := (h 1 23 24)
  have h815 : P 24 23 = 0 := (h 1 23 26)
  have h650 : P 19 23 = 0 := (h 1 23 28)
  have h584 : P 17 23 = 0 := (h 1 23 30)
  have h320 : P 9 23 = 0 := (h 1 23 32)
  have h883 : P 26 25 = 0 := (h 1 24 25).symm
  have h885 : P 26 27 = 0 := (h 1 24 27).symm
  have h887 : P 26 29 = 0 := (h 1 24 29).symm
  have h889 : P 26 31 = 0 := (h 1 24 31).symm
  have h817 : P 24 25 = 0 := (h 1 25 26)
  have h652 : P 19 25 = 0 := (h 1 25 28)
  have h586 : P 17 25 = 0 := (h 1 25 30)
  have h322 : P 9 25 = 0 := (h 1 25 32)
  have h819 : P 24 27 = 0 := (h 1 26 27).symm
  have h821 : P 24 29 = 0 := (h 1 26 29).symm
  have h823 : P 24 31 = 0 := (h 1 26 31).symm
  have h654 : P 19 27 = 0 := (h 1 27 28)
  have h588 : P 17 27 = 0 := (h 1 27 30)
  have h324 : P 9 27 = 0 := (h 1 27 32)
  have h656 : P 19 29 = 0 := (h 1 28 29).symm
  have h658 : P 19 31 = 0 := (h 1 28 31).symm
  have h590 : P 17 29 = 0 := (h 1 29 30)
  have h326 : P 9 29 = 0 := (h 1 29 32)
  have h592 : P 17 31 = 0 := (h 1 30 31).symm
  have h328 : P 9 31 = 0 := (h 1 31 32)
  have h891 : P 27 0 = 0 := (h 2 0 19)
  have h759 : P 23 0 = 0 := (h 2 0 26)
  have h528 : P 16 0 = 0 := (h 2 0 30)
  have h264 : P 8 0 = 0 := (h 2 0 32)
  have h892 : P 27 1 = 0 := (h 2 1 19)
  have h760 : P 23 1 = 0 := (h 2 1 26)
  have h529 : P 16 1 = 0 := (h 2 1 30)
  have h265 : P 8 1 = 0 := (h 2 1 32)
  have h893 : P 27 2 = 0 := (h 2 2 19)
  have h761 : P 23 2 = 0 := (h 2 2 26)
  have h530 : P 16 2 = 0 := (h 2 2 30)
  have h266 : P 8 2 = 0 := (h 2 2 32)
  have h894 : P 27 3 = 0 := (h 2 3 19)
  have h762 : P 23 3 = 0 := (h 2 3 26)
  have h531 : P 16 3 = 0 := (h 2 3 30)
  have h267 : P 8 3 = 0 := (h 2 3 32)
  have h895 : P 27 4 = 0 := (h 2 4 19)
  have h763 : P 23 4 = 0 := (h 2 4 26)
  have h532 : P 16 4 = 0 := (h 2 4 30)
  have h268 : P 8 4 = 0 := (h 2 4 32)
  have h896 : P 27 5 = 0 := (h 2 5 19)
  have h764 : P 23 5 = 0 := (h 2 5 26)
  have h533 : P 16 5 = 0 := (h 2 5 30)
  have h269 : P 8 5 = 0 := (h 2 5 32)
  have h897 : P 27 6 = 0 := (h 2 6 19)
  have h765 : P 23 6 = 0 := (h 2 6 26)
  have h534 : P 16 6 = 0 := (h 2 6 30)
  have h270 : P 8 6 = 0 := (h 2 6 32)
  have h898 : P 27 7 = 0 := (h 2 7 19)
  have h766 : P 23 7 = 0 := (h 2 7 26)
  have h535 : P 16 7 = 0 := (h 2 7 30)
  have h271 : P 8 7 = 0 := (h 2 7 32)
  have h1065 : P 32 9 = 0 := (h 2 8 9).symm
  have h1073 : P 32 17 = 0 := (h 2 8 17).symm
  have h1080 : P 32 24 = 0 := (h 2 8 24).symm
  have h1084 : P 32 28 = 0 := (h 2 8 28).symm
  have h999 : P 30 9 = 0 := (h 2 9 16)
  have h900 : P 27 9 = 0 := (h 2 9 19)
  have h867 : P 26 9 = 0 := (h 2 9 23)
  have h768 : P 23 9 = 0 := (h 2 9 26)
  have h636 : P 19 9 = 0 := (h 2 9 27)
  have h537 : P 16 9 = 0 := (h 2 9 30)
  have h273 : P 8 9 = 0 := (h 2 9 32)
  have h901 : P 27 10 = 0 := (h 2 10 19)
  have h769 : P 23 10 = 0 := (h 2 10 26)
  have h538 : P 16 10 = 0 := (h 2 10 30)
  have h274 : P 8 10 = 0 := (h 2 10 32)
  have h902 : P 27 11 = 0 := (h 2 11 19)
  have h770 : P 23 11 = 0 := (h 2 11 26)
  have h539 : P 16 11 = 0 := (h 2 11 30)
  have h275 : P 8 11 = 0 := (h 2 11 32)
  have h903 : P 27 12 = 0 := (h 2 12 19)
  have h771 : P 23 12 = 0 := (h 2 12 26)
  have h540 : P 16 12 = 0 := (h 2 12 30)
  have h276 : P 8 12 = 0 := (h 2 12 32)
  have h904 : P 27 13 = 0 := (h 2 13 19)
  have h772 : P 23 13 = 0 := (h 2 13 26)
  have h541 : P 16 13 = 0 := (h 2 13 30)
  have h277 : P 8 13 = 0 := (h 2 13 32)
  have h905 : P 27 14 = 0 := (h 2 14 19)
  have h773 : P 23 14 = 0 := (h 2 14 26)
  have h542 : P 16 14 = 0 := (h 2 14 30)
  have h278 : P 8 14 = 0 := (h 2 14 32)
  have h906 : P 27 15 = 0 := (h 2 15 19)
  have h774 : P 23 15 = 0 := (h 2 15 26)
  have h543 : P 16 15 = 0 := (h 2 15 30)
  have h279 : P 8 15 = 0 := (h 2 15 32)
  have h1007 : P 30 17 = 0 := (h 2 16 17).symm
  have h1014 : P 30 24 = 0 := (h 2 16 24).symm
  have h1018 : P 30 28 = 0 := (h 2 16 28).symm
  have h908 : P 27 17 = 0 := (h 2 17 19)
  have h875 : P 26 17 = 0 := (h 2 17 23)
  have h776 : P 23 17 = 0 := (h 2 17 26)
  have h644 : P 19 17 = 0 := (h 2 17 27)
  have h545 : P 16 17 = 0 := (h 2 17 30)
  have h281 : P 8 17 = 0 := (h 2 17 32)
  have h909 : P 27 18 = 0 := (h 2 18 19)
  have h777 : P 23 18 = 0 := (h 2 18 26)
  have h546 : P 16 18 = 0 := (h 2 18 30)
  have h282 : P 8 18 = 0 := (h 2 18 32)
  have h911 : P 27 20 = 0 := (h 2 19 20).symm
  have h912 : P 27 21 = 0 := (h 2 19 21).symm
  have h913 : P 27 22 = 0 := (h 2 19 22).symm
  have h915 : P 27 24 = 0 := (h 2 19 24).symm
  have h916 : P 27 25 = 0 := (h 2 19 25).symm
  have h919 : P 27 28 = 0 := (h 2 19 28).symm
  have h920 : P 27 29 = 0 := (h 2 19 29).symm
  have h922 : P 27 31 = 0 := (h 2 19 31).symm
  have h779 : P 23 20 = 0 := (h 2 20 26)
  have h548 : P 16 20 = 0 := (h 2 20 30)
  have h284 : P 8 20 = 0 := (h 2 20 32)
  have h780 : P 23 21 = 0 := (h 2 21 26)
  have h549 : P 16 21 = 0 := (h 2 21 30)
  have h285 : P 8 21 = 0 := (h 2 21 32)
  have h781 : P 23 22 = 0 := (h 2 22 26)
  have h550 : P 16 22 = 0 := (h 2 22 30)
  have h286 : P 8 22 = 0 := (h 2 22 32)
  have h882 : P 26 24 = 0 := (h 2 23 24).symm
  have h886 : P 26 28 = 0 := (h 2 23 28).symm
  have h783 : P 23 24 = 0 := (h 2 24 26)
  have h651 : P 19 24 = 0 := (h 2 24 27)
  have h552 : P 16 24 = 0 := (h 2 24 30)
  have h288 : P 8 24 = 0 := (h 2 24 32)
  have h784 : P 23 25 = 0 := (h 2 25 26)
  have h553 : P 16 25 = 0 := (h 2 25 30)
  have h289 : P 8 25 = 0 := (h 2 25 32)
  have h787 : P 23 28 = 0 := (h 2 26 28).symm
  have h788 : P 23 29 = 0 := (h 2 26 29).symm
  have h790 : P 23 31 = 0 := (h 2 26 31).symm
  have h655 : P 19 28 = 0 := (h 2 27 28).symm
  have h556 : P 16 28 = 0 := (h 2 28 30)
  have h292 : P 8 28 = 0 := (h 2 28 32)
  have h557 : P 16 29 = 0 := (h 2 29 30)
  have h293 : P 8 29 = 0 := (h 2 29 32)
  have h559 : P 16 31 = 0 := (h 2 30 31).symm
  have h295 : P 8 31 = 0 := (h 2 31 32)
  have h726 : P 22 0 = 0 := (h 3 0 26)
  have h495 : P 15 0 = 0 := (h 3 0 30)
  have h231 : P 7 0 = 0 := (h 3 0 32)
  have h727 : P 22 1 = 0 := (h 3 1 26)
  have h496 : P 15 1 = 0 := (h 3 1 30)
  have h232 : P 7 1 = 0 := (h 3 1 32)
  have h728 : P 22 2 = 0 := (h 3 2 26)
  have h497 : P 15 2 = 0 := (h 3 2 30)
  have h233 : P 7 2 = 0 := (h 3 2 32)
  have h729 : P 22 3 = 0 := (h 3 3 26)
  have h498 : P 15 3 = 0 := (h 3 3 30)
  have h234 : P 7 3 = 0 := (h 3 3 32)
  have h730 : P 22 4 = 0 := (h 3 4 26)
  have h499 : P 15 4 = 0 := (h 3 4 30)
  have h235 : P 7 4 = 0 := (h 3 4 32)
  have h731 : P 22 5 = 0 := (h 3 5 26)
  have h500 : P 15 5 = 0 := (h 3 5 30)
  have h236 : P 7 5 = 0 := (h 3 5 32)
  have h732 : P 22 6 = 0 := (h 3 6 26)
  have h501 : P 15 6 = 0 := (h 3 6 30)
  have h237 : P 7 6 = 0 := (h 3 6 32)
  have h1075 : P 32 19 = 0 := (h 3 7 19).symm
  have h734 : P 22 8 = 0 := (h 3 8 26)
  have h503 : P 15 8 = 0 := (h 3 8 30)
  have h239 : P 7 8 = 0 := (h 3 8 32)
  have h1033 : P 31 10 = 0 := (h 3 9 10).symm
  have h967 : P 29 10 = 0 := (h 3 10 17)
  have h835 : P 25 10 = 0 := (h 3 10 24)
  have h736 : P 22 10 = 0 := (h 3 10 26)
  have h604 : P 18 10 = 0 := (h 3 10 28)
  have h505 : P 15 10 = 0 := (h 3 10 30)
  have h241 : P 7 10 = 0 := (h 3 10 32)
  have h737 : P 22 11 = 0 := (h 3 11 26)
  have h506 : P 15 11 = 0 := (h 3 11 30)
  have h242 : P 7 11 = 0 := (h 3 11 32)
  have h738 : P 22 12 = 0 := (h 3 12 26)
  have h507 : P 15 12 = 0 := (h 3 12 30)
  have h243 : P 7 12 = 0 := (h 3 12 32)
  have h739 : P 22 13 = 0 := (h 3 13 26)
  have h508 : P 15 13 = 0 := (h 3 13 30)
  have h244 : P 7 13 = 0 := (h 3 13 32)
  have h740 : P 22 14 = 0 := (h 3 14 26)
  have h509 : P 15 14 = 0 := (h 3 14 30)
  have h245 : P 7 14 = 0 := (h 3 14 32)
  have h1009 : P 30 19 = 0 := (h 3 15 19).symm
  have h742 : P 22 16 = 0 := (h 3 16 26)
  have h511 : P 15 16 = 0 := (h 3 16 30)
  have h247 : P 7 16 = 0 := (h 3 16 32)
  have h943 : P 28 19 = 0 := (h 3 18 19).symm
  have h877 : P 26 19 = 0 := (h 3 19 22)
  have h811 : P 24 19 = 0 := (h 3 19 25)
  have h745 : P 22 19 = 0 := (h 3 19 26)
  have h580 : P 17 19 = 0 := (h 3 19 29)
  have h514 : P 15 19 = 0 := (h 3 19 30)
  have h316 : P 9 19 = 0 := (h 3 19 31)
  have h250 : P 7 19 = 0 := (h 3 19 32)
  have h746 : P 22 20 = 0 := (h 3 20 26)
  have h515 : P 15 20 = 0 := (h 3 20 30)
  have h251 : P 7 20 = 0 := (h 3 20 32)
  have h747 : P 22 21 = 0 := (h 3 21 26)
  have h516 : P 15 21 = 0 := (h 3 21 30)
  have h252 : P 7 21 = 0 := (h 3 21 32)
  have h749 : P 22 23 = 0 := (h 3 23 26)
  have h518 : P 15 23 = 0 := (h 3 23 30)
  have h254 : P 7 23 = 0 := (h 3 23 32)
  have h753 : P 22 27 = 0 := (h 3 26 27).symm
  have h522 : P 15 27 = 0 := (h 3 27 30)
  have h258 : P 7 27 = 0 := (h 3 27 32)
  have h910 : P 27 19 = 0 := (h 4 18 19).symm
  have h917 : P 27 26 = 0 := (h 4 18 26).symm
  have h921 : P 27 30 = 0 := (h 4 18 30).symm
  have h923 : P 27 32 = 0 := (h 4 18 32).symm
  have h778 : P 23 19 = 0 := (h 4 19 25)
  have h547 : P 16 19 = 0 := (h 4 19 29)
  have h283 : P 8 19 = 0 := (h 4 19 31)
  have h785 : P 23 26 = 0 := (h 4 25 26).symm
  have h789 : P 23 30 = 0 := (h 4 25 30).symm
  have h791 : P 23 32 = 0 := (h 4 25 32).symm
  have h554 : P 16 26 = 0 := (h 4 26 29)
  have h290 : P 8 26 = 0 := (h 4 26 31)
  have h558 : P 16 30 = 0 := (h 4 29 30).symm
  have h560 : P 16 32 = 0 := (h 4 29 32).symm
  have h294 : P 8 30 = 0 := (h 4 30 31)
  have h296 : P 8 32 = 0 := (h 4 31 32).symm
  have h660 : P 20 0 = 0 := (h 5 0 26)
  have h429 : P 13 0 = 0 := (h 5 0 30)
  have h165 : P 5 0 = 0 := (h 5 0 32)
  have h661 : P 20 1 = 0 := (h 5 1 26)
  have h430 : P 13 1 = 0 := (h 5 1 30)
  have h166 : P 5 1 = 0 := (h 5 1 32)
  have h662 : P 20 2 = 0 := (h 5 2 26)
  have h431 : P 13 2 = 0 := (h 5 2 30)
  have h167 : P 5 2 = 0 := (h 5 2 32)
  have h663 : P 20 3 = 0 := (h 5 3 26)
  have h432 : P 13 3 = 0 := (h 5 3 30)
  have h168 : P 5 3 = 0 := (h 5 3 32)
  have h664 : P 20 4 = 0 := (h 5 4 26)
  have h433 : P 13 4 = 0 := (h 5 4 30)
  have h169 : P 5 4 = 0 := (h 5 4 32)
  have h666 : P 20 6 = 0 := (h 5 6 26)
  have h435 : P 13 6 = 0 := (h 5 6 30)
  have h171 : P 5 6 = 0 := (h 5 6 32)
  have h667 : P 20 7 = 0 := (h 5 7 26)
  have h436 : P 13 7 = 0 := (h 5 7 30)
  have h172 : P 5 7 = 0 := (h 5 7 32)
  have h668 : P 20 8 = 0 := (h 5 8 26)
  have h437 : P 13 8 = 0 := (h 5 8 30)
  have h173 : P 5 8 = 0 := (h 5 8 32)
  have h669 : P 20 9 = 0 := (h 5 9 26)
  have h438 : P 13 9 = 0 := (h 5 9 30)
  have h174 : P 5 9 = 0 := (h 5 9 32)
  have h670 : P 20 10 = 0 := (h 5 10 26)
  have h439 : P 13 10 = 0 := (h 5 10 30)
  have h175 : P 5 10 = 0 := (h 5 10 32)
  have h671 : P 20 11 = 0 := (h 5 11 26)
  have h440 : P 13 11 = 0 := (h 5 11 30)
  have h176 : P 5 11 = 0 := (h 5 11 32)
  have h672 : P 20 12 = 0 := (h 5 12 26)
  have h441 : P 13 12 = 0 := (h 5 12 30)
  have h177 : P 5 12 = 0 := (h 5 12 32)
  have h674 : P 20 14 = 0 := (h 5 14 26)
  have h443 : P 13 14 = 0 := (h 5 14 30)
  have h179 : P 5 14 = 0 := (h 5 14 32)
  have h675 : P 20 15 = 0 := (h 5 15 26)
  have h444 : P 13 15 = 0 := (h 5 15 30)
  have h180 : P 5 15 = 0 := (h 5 15 32)
  have h676 : P 20 16 = 0 := (h 5 16 26)
  have h445 : P 13 16 = 0 := (h 5 16 30)
  have h181 : P 5 16 = 0 := (h 5 16 32)
  have h677 : P 20 17 = 0 := (h 5 17 26)
  have h446 : P 13 17 = 0 := (h 5 17 30)
  have h182 : P 5 17 = 0 := (h 5 17 32)
  have h678 : P 20 18 = 0 := (h 5 18 26)
  have h447 : P 13 18 = 0 := (h 5 18 30)
  have h183 : P 5 18 = 0 := (h 5 18 32)
  have h679 : P 20 19 = 0 := (h 5 19 26)
  have h448 : P 13 19 = 0 := (h 5 19 30)
  have h184 : P 5 19 = 0 := (h 5 19 32)
  have h681 : P 20 21 = 0 := (h 5 21 26)
  have h450 : P 13 21 = 0 := (h 5 21 30)
  have h186 : P 5 21 = 0 := (h 5 21 32)
  have h682 : P 20 22 = 0 := (h 5 22 26)
  have h451 : P 13 22 = 0 := (h 5 22 30)
  have h187 : P 5 22 = 0 := (h 5 22 32)
  have h683 : P 20 23 = 0 := (h 5 23 26)
  have h452 : P 13 23 = 0 := (h 5 23 30)
  have h188 : P 5 23 = 0 := (h 5 23 32)
  have h684 : P 20 24 = 0 := (h 5 24 26)
  have h453 : P 13 24 = 0 := (h 5 24 30)
  have h189 : P 5 24 = 0 := (h 5 24 32)
  have h685 : P 20 25 = 0 := (h 5 25 26)
  have h454 : P 13 25 = 0 := (h 5 25 30)
  have h190 : P 5 25 = 0 := (h 5 25 32)
  have h687 : P 20 27 = 0 := (h 5 26 27).symm
  have h688 : P 20 28 = 0 := (h 5 26 28).symm
  have h689 : P 20 29 = 0 := (h 5 26 29).symm
  have h691 : P 20 31 = 0 := (h 5 26 31).symm
  have h456 : P 13 27 = 0 := (h 5 27 30)
  have h192 : P 5 27 = 0 := (h 5 27 32)
  have h457 : P 13 28 = 0 := (h 5 28 30)
  have h193 : P 5 28 = 0 := (h 5 28 32)
  have h458 : P 13 29 = 0 := (h 5 29 30)
  have h194 : P 5 29 = 0 := (h 5 29 32)
  have h460 : P 13 31 = 0 := (h 5 30 31).symm
  have h196 : P 5 31 = 0 := (h 5 31 32)
  have h693 : P 21 0 = 0 := (h 6 0 25)
  have h462 : P 14 0 = 0 := (h 6 0 29)
  have h396 : P 12 0 = 0 := (h 6 0 30)
  have h198 : P 6 0 = 0 := (h 6 0 31)
  have h132 : P 4 0 = 0 := (h 6 0 32)
  have h694 : P 21 1 = 0 := (h 6 1 25)
  have h463 : P 14 1 = 0 := (h 6 1 29)
  have h397 : P 12 1 = 0 := (h 6 1 30)
  have h199 : P 6 1 = 0 := (h 6 1 31)
  have h133 : P 4 1 = 0 := (h 6 1 32)
  have h695 : P 21 2 = 0 := (h 6 2 25)
  have h464 : P 14 2 = 0 := (h 6 2 29)
  have h398 : P 12 2 = 0 := (h 6 2 30)
  have h200 : P 6 2 = 0 := (h 6 2 31)
  have h134 : P 4 2 = 0 := (h 6 2 32)
  have h696 : P 21 3 = 0 := (h 6 3 25)
  have h465 : P 14 3 = 0 := (h 6 3 29)
  have h399 : P 12 3 = 0 := (h 6 3 30)
  have h201 : P 6 3 = 0 := (h 6 3 31)
  have h135 : P 4 3 = 0 := (h 6 3 32)
  have h1082 : P 32 26 = 0 := (h 6 4 26).symm
  have h698 : P 21 5 = 0 := (h 6 5 25)
  have h467 : P 14 5 = 0 := (h 6 5 29)
  have h401 : P 12 5 = 0 := (h 6 5 30)
  have h203 : P 6 5 = 0 := (h 6 5 31)
  have h137 : P 4 5 = 0 := (h 6 5 32)
  have h1041 : P 31 18 = 0 := (h 6 6 18).symm
  have h700 : P 21 7 = 0 := (h 6 7 25)
  have h469 : P 14 7 = 0 := (h 6 7 29)
  have h403 : P 12 7 = 0 := (h 6 7 30)
  have h205 : P 6 7 = 0 := (h 6 7 31)
  have h139 : P 4 7 = 0 := (h 6 7 32)
  have h701 : P 21 8 = 0 := (h 6 8 25)
  have h470 : P 14 8 = 0 := (h 6 8 29)
  have h404 : P 12 8 = 0 := (h 6 8 30)
  have h206 : P 6 8 = 0 := (h 6 8 31)
  have h140 : P 4 8 = 0 := (h 6 8 32)
  have h933 : P 28 9 = 0 := (h 6 9 17)
  have h801 : P 24 9 = 0 := (h 6 9 24)
  have h702 : P 21 9 = 0 := (h 6 9 25)
  have h570 : P 17 9 = 0 := (h 6 9 28)
  have h471 : P 14 9 = 0 := (h 6 9 29)
  have h405 : P 12 9 = 0 := (h 6 9 30)
  have h207 : P 6 9 = 0 := (h 6 9 31)
  have h141 : P 4 9 = 0 := (h 6 9 32)
  have h703 : P 21 10 = 0 := (h 6 10 25)
  have h472 : P 14 10 = 0 := (h 6 10 29)
  have h406 : P 12 10 = 0 := (h 6 10 30)
  have h208 : P 6 10 = 0 := (h 6 10 31)
  have h142 : P 4 10 = 0 := (h 6 10 32)
  have h704 : P 21 11 = 0 := (h 6 11 25)
  have h473 : P 14 11 = 0 := (h 6 11 29)
  have h407 : P 12 11 = 0 := (h 6 11 30)
  have h209 : P 6 11 = 0 := (h 6 11 31)
  have h143 : P 4 11 = 0 := (h 6 11 32)
  have h1016 : P 30 26 = 0 := (h 6 12 26).symm
  have h706 : P 21 13 = 0 := (h 6 13 25)
  have h475 : P 14 13 = 0 := (h 6 13 29)
  have h409 : P 12 13 = 0 := (h 6 13 30)
  have h211 : P 6 13 = 0 := (h 6 13 31)
  have h145 : P 4 13 = 0 := (h 6 13 32)
  have h975 : P 29 18 = 0 := (h 6 14 18).symm
  have h708 : P 21 15 = 0 := (h 6 15 25)
  have h477 : P 14 15 = 0 := (h 6 15 29)
  have h411 : P 12 15 = 0 := (h 6 15 30)
  have h213 : P 6 15 = 0 := (h 6 15 31)
  have h147 : P 4 15 = 0 := (h 6 15 32)
  have h709 : P 21 16 = 0 := (h 6 16 25)
  have h478 : P 14 16 = 0 := (h 6 16 29)
  have h412 : P 12 16 = 0 := (h 6 16 30)
  have h214 : P 6 16 = 0 := (h 6 16 31)
  have h148 : P 4 16 = 0 := (h 6 16 32)
  have h950 : P 28 26 = 0 := (h 6 17 26).symm
  have h843 : P 25 18 = 0 := (h 6 18 21)
  have h711 : P 21 18 = 0 := (h 6 18 25)
  have h480 : P 14 18 = 0 := (h 6 18 29)
  have h414 : P 12 18 = 0 := (h 6 18 30)
  have h216 : P 6 18 = 0 := (h 6 18 31)
  have h150 : P 4 18 = 0 := (h 6 18 32)
  have h712 : P 21 19 = 0 := (h 6 19 25)
  have h481 : P 14 19 = 0 := (h 6 19 29)
  have h415 : P 12 19 = 0 := (h 6 19 30)
  have h217 : P 6 19 = 0 := (h 6 19 31)
  have h151 : P 4 19 = 0 := (h 6 19 32)
  have h713 : P 21 20 = 0 := (h 6 20 25)
  have h482 : P 14 20 = 0 := (h 6 20 29)
  have h416 : P 12 20 = 0 := (h 6 20 30)
  have h218 : P 6 20 = 0 := (h 6 20 31)
  have h152 : P 4 20 = 0 := (h 6 20 32)
  have h715 : P 21 22 = 0 := (h 6 22 25)
  have h484 : P 14 22 = 0 := (h 6 22 29)
  have h418 : P 12 22 = 0 := (h 6 22 30)
  have h220 : P 6 22 = 0 := (h 6 22 31)
  have h154 : P 4 22 = 0 := (h 6 22 32)
  have h716 : P 21 23 = 0 := (h 6 23 25)
  have h485 : P 14 23 = 0 := (h 6 23 29)
  have h419 : P 12 23 = 0 := (h 6 23 30)
  have h221 : P 6 23 = 0 := (h 6 23 31)
  have h155 : P 4 23 = 0 := (h 6 23 32)
  have h818 : P 24 26 = 0 := (h 6 24 26).symm
  have h719 : P 21 26 = 0 := (h 6 25 26).symm
  have h720 : P 21 27 = 0 := (h 6 25 27).symm
  have h587 : P 17 26 = 0 := (h 6 26 28)
  have h488 : P 14 26 = 0 := (h 6 26 29)
  have h422 : P 12 26 = 0 := (h 6 26 30)
  have h224 : P 6 26 = 0 := (h 6 26 31)
  have h158 : P 4 26 = 0 := (h 6 26 32)
  have h489 : P 14 27 = 0 := (h 6 27 29)
  have h423 : P 12 27 = 0 := (h 6 27 30)
  have h225 : P 6 27 = 0 := (h 6 27 31)
  have h159 : P 4 27 = 0 := (h 6 27 32)
  have h363 : P 11 0 = 0 := (h 7 0 30)
  have h99 : P 3 0 = 0 := (h 7 0 32)
  have h364 : P 11 1 = 0 := (h 7 1 30)
  have h100 : P 3 1 = 0 := (h 7 1 32)
  have h365 : P 11 2 = 0 := (h 7 2 30)
  have h101 : P 3 2 = 0 := (h 7 2 32)
  have h367 : P 11 4 = 0 := (h 7 4 30)
  have h103 : P 3 4 = 0 := (h 7 4 32)
  have h369 : P 11 6 = 0 := (h 7 6 30)
  have h105 : P 3 6 = 0 := (h 7 6 32)
  have h370 : P 11 7 = 0 := (h 7 7 30)
  have h106 : P 3 7 = 0 := (h 7 7 32)
  have h899 : P 27 8 = 0 := (h 7 8 17)
  have h767 : P 23 8 = 0 := (h 7 8 24)
  have h536 : P 16 8 = 0 := (h 7 8 28)
  have h371 : P 11 8 = 0 := (h 7 8 30)
  have h107 : P 3 8 = 0 := (h 7 8 32)
  have h372 : P 11 9 = 0 := (h 7 9 30)
  have h108 : P 3 9 = 0 := (h 7 9 32)
  have h373 : P 11 10 = 0 := (h 7 10 30)
  have h109 : P 3 10 = 0 := (h 7 10 32)
  have h375 : P 11 12 = 0 := (h 7 12 30)
  have h111 : P 3 12 = 0 := (h 7 12 32)
  have h377 : P 11 14 = 0 := (h 7 14 30)
  have h113 : P 3 14 = 0 := (h 7 14 32)
  have h378 : P 11 15 = 0 := (h 7 15 30)
  have h114 : P 3 15 = 0 := (h 7 15 32)
  have h381 : P 11 18 = 0 := (h 7 18 30)
  have h117 : P 3 18 = 0 := (h 7 18 32)
  have h382 : P 11 19 = 0 := (h 7 19 30)
  have h118 : P 3 19 = 0 := (h 7 19 32)
  have h384 : P 11 21 = 0 := (h 7 21 30)
  have h120 : P 3 21 = 0 := (h 7 21 32)
  have h385 : P 11 22 = 0 := (h 7 22 30)
  have h121 : P 3 22 = 0 := (h 7 22 32)
  have h686 : P 20 26 = 0 := (h 7 25 26).symm
  have h455 : P 13 26 = 0 := (h 7 26 29)
  have h389 : P 11 26 = 0 := (h 7 26 30)
  have h191 : P 5 26 = 0 := (h 7 26 31)
  have h125 : P 3 26 = 0 := (h 7 26 32)
  have h66 : P 2 0 = 0 := (h 8 0 32)
  have h67 : P 2 1 = 0 := (h 8 1 32)
  have h1086 : P 32 30 = 0 := (h 8 2 30).symm
  have h69 : P 2 3 = 0 := (h 8 3 32)
  have h1048 : P 31 25 = 0 := (h 8 4 25).symm
  have h71 : P 2 5 = 0 := (h 8 5 32)
  have h402 : P 12 6 = 0 := (h 8 6 29)
  have h138 : P 4 6 = 0 := (h 8 6 31)
  have h72 : P 2 6 = 0 := (h 8 6 32)
  have h733 : P 22 7 = 0 := (h 8 7 24)
  have h502 : P 15 7 = 0 := (h 8 7 28)
  have h73 : P 2 7 = 0 := (h 8 7 32)
  have h74 : P 2 8 = 0 := (h 8 8 32)
  have h735 : P 22 9 = 0 := (h 8 9 24)
  have h504 : P 15 9 = 0 := (h 8 9 28)
  have h75 : P 2 9 = 0 := (h 8 9 32)
  have h76 : P 2 10 = 0 := (h 8 10 32)
  have h77 : P 2 11 = 0 := (h 8 11 32)
  have h982 : P 29 25 = 0 := (h 8 12 25).symm
  have h79 : P 2 13 = 0 := (h 8 13 32)
  have h410 : P 12 14 = 0 := (h 8 14 29)
  have h146 : P 4 14 = 0 := (h 8 14 31)
  have h80 : P 2 14 = 0 := (h 8 14 32)
  have h941 : P 28 17 = 0 := (h 8 15 17).symm
  have h954 : P 28 30 = 0 := (h 8 15 30).symm
  have h82 : P 2 16 = 0 := (h 8 16 32)
  have h809 : P 24 17 = 0 := (h 8 17 22)
  have h743 : P 22 17 = 0 := (h 8 17 24)
  have h512 : P 15 17 = 0 := (h 8 17 28)
  have h413 : P 12 17 = 0 := (h 8 17 29)
  have h149 : P 4 17 = 0 := (h 8 17 31)
  have h83 : P 2 17 = 0 := (h 8 17 32)
  have h744 : P 22 18 = 0 := (h 8 18 24)
  have h513 : P 15 18 = 0 := (h 8 18 28)
  have h84 : P 2 18 = 0 := (h 8 18 32)
  have h85 : P 2 19 = 0 := (h 8 19 32)
  have h86 : P 2 20 = 0 := (h 8 20 32)
  have h417 : P 12 21 = 0 := (h 8 21 29)
  have h153 : P 4 21 = 0 := (h 8 21 31)
  have h87 : P 2 21 = 0 := (h 8 21 32)
  have h822 : P 24 30 = 0 := (h 8 22 30).symm
  have h89 : P 2 23 = 0 := (h 8 23 32)
  have h751 : P 22 25 = 0 := (h 8 24 25).symm
  have h752 : P 22 26 = 0 := (h 8 24 26).symm
  have h756 : P 22 30 = 0 := (h 8 24 30).symm
  have h520 : P 15 25 = 0 := (h 8 25 28)
  have h421 : P 12 25 = 0 := (h 8 25 29)
  have h157 : P 4 25 = 0 := (h 8 25 31)
  have h91 : P 2 25 = 0 := (h 8 25 32)
  have h521 : P 15 26 = 0 := (h 8 26 28)
  have h92 : P 2 26 = 0 := (h 8 26 32)
  have h93 : P 2 27 = 0 := (h 8 27 32)
  have h525 : P 15 30 = 0 := (h 8 28 30).symm
  have h426 : P 12 30 = 0 := (h 8 29 30).symm
  have h162 : P 4 30 = 0 := (h 8 30 31)
  have h96 : P 2 30 = 0 := (h 8 30 32)
  have h33 : P 1 0 = 0 := (h 9 0 32)
  have h35 : P 1 2 = 0 := (h 9 2 32)
  have h37 : P 1 4 = 0 := (h 9 4 32)
  have h368 : P 11 5 = 0 := (h 9 5 29)
  have h104 : P 3 5 = 0 := (h 9 5 31)
  have h38 : P 1 5 = 0 := (h 9 5 32)
  have h39 : P 1 6 = 0 := (h 9 6 32)
  have h40 : P 1 7 = 0 := (h 9 7 32)
  have h41 : P 1 8 = 0 := (h 9 8 32)
  have h42 : P 1 9 = 0 := (h 9 9 32)
  have h43 : P 1 10 = 0 := (h 9 10 32)
  have h45 : P 1 12 = 0 := (h 9 12 32)
  have h376 : P 11 13 = 0 := (h 9 13 29)
  have h112 : P 3 13 = 0 := (h 9 13 31)
  have h46 : P 1 13 = 0 := (h 9 13 32)
  have h47 : P 1 14 = 0 := (h 9 14 32)
  have h907 : P 27 16 = 0 := (h 9 15 16).symm
  have h775 : P 23 16 = 0 := (h 9 16 22)
  have h379 : P 11 16 = 0 := (h 9 16 29)
  have h115 : P 3 16 = 0 := (h 9 16 31)
  have h49 : P 1 16 = 0 := (h 9 16 32)
  have h380 : P 11 17 = 0 := (h 9 17 29)
  have h116 : P 3 17 = 0 := (h 9 17 31)
  have h50 : P 1 17 = 0 := (h 9 17 32)
  have h51 : P 1 18 = 0 := (h 9 18 32)
  have h52 : P 1 19 = 0 := (h 9 19 32)
  have h383 : P 11 20 = 0 := (h 9 20 29)
  have h119 : P 3 20 = 0 := (h 9 20 31)
  have h53 : P 1 20 = 0 := (h 9 20 32)
  have h54 : P 1 21 = 0 := (h 9 21 32)
  have h750 : P 22 24 = 0 := (h 9 23 24).symm
  have h754 : P 22 28 = 0 := (h 9 23 28).symm
  have h519 : P 15 24 = 0 := (h 9 24 27)
  have h387 : P 11 24 = 0 := (h 9 24 29)
  have h123 : P 3 24 = 0 := (h 9 24 31)
  have h57 : P 1 24 = 0 := (h 9 24 32)
  have h388 : P 11 25 = 0 := (h 9 25 29)
  have h124 : P 3 25 = 0 := (h 9 25 31)
  have h58 : P 1 25 = 0 := (h 9 25 32)
  have h59 : P 1 26 = 0 := (h 9 26 32)
  have h523 : P 15 28 = 0 := (h 9 27 28).symm
  have h391 : P 11 28 = 0 := (h 9 28 29)
  have h127 : P 3 28 = 0 := (h 9 28 31)
  have h61 : P 1 28 = 0 := (h 9 28 32)
  have h393 : P 11 30 = 0 := (h 9 29 30).symm
  have h129 : P 3 30 = 0 := (h 9 30 31)
  have h63 : P 1 30 = 0 := (h 9 30 32)
  have h1 : P 0 1 = 0 := (h 10 1 32)
  have h2 : P 0 2 = 0 := (h 10 2 32)
  have h3 : P 0 3 = 0 := (h 10 3 32)
  have h697 : P 21 4 = 0 := (h 10 4 23)
  have h466 : P 14 4 = 0 := (h 10 4 27)
  have h4 : P 0 4 = 0 := (h 10 4 32)
  have h665 : P 20 5 = 0 := (h 10 5 24)
  have h434 : P 13 5 = 0 := (h 10 5 28)
  have h5 : P 0 5 = 0 := (h 10 5 32)
  have h699 : P 21 6 = 0 := (h 10 6 23)
  have h468 : P 14 6 = 0 := (h 10 6 27)
  have h6 : P 0 6 = 0 := (h 10 6 32)
  have h7 : P 0 7 = 0 := (h 10 7 32)
  have h8 : P 0 8 = 0 := (h 10 8 32)
  have h9 : P 0 9 = 0 := (h 10 9 32)
  have h10 : P 0 10 = 0 := (h 10 10 32)
  have h11 : P 0 11 = 0 := (h 10 11 32)
  have h705 : P 21 12 = 0 := (h 10 12 23)
  have h474 : P 14 12 = 0 := (h 10 12 27)
  have h12 : P 0 12 = 0 := (h 10 12 32)
  have h15 : P 0 15 = 0 := (h 10 15 32)
  have h16 : P 0 16 = 0 := (h 10 16 32)
  have h710 : P 21 17 = 0 := (h 10 17 23)
  have h479 : P 14 17 = 0 := (h 10 17 27)
  have h17 : P 0 17 = 0 := (h 10 17 32)
  have h18 : P 0 18 = 0 := (h 10 18 32)
  have h19 : P 0 19 = 0 := (h 10 19 32)
  have h22 : P 0 22 = 0 := (h 10 22 32)
  have h718 : P 21 25 = 0 := (h 10 23 25).symm
  have h722 : P 21 29 = 0 := (h 10 23 29).symm
  have h723 : P 21 30 = 0 := (h 10 23 30).symm
  have h724 : P 21 31 = 0 := (h 10 23 31).symm
  have h690 : P 20 30 = 0 := (h 10 24 30).symm
  have h487 : P 14 25 = 0 := (h 10 25 27)
  have h25 : P 0 25 = 0 := (h 10 25 32)
  have h26 : P 0 26 = 0 := (h 10 26 32)
  have h491 : P 14 29 = 0 := (h 10 27 29).symm
  have h492 : P 14 30 = 0 := (h 10 27 30).symm
  have h493 : P 14 31 = 0 := (h 10 27 31).symm
  have h459 : P 13 30 = 0 := (h 10 28 30).symm
  have h29 : P 0 29 = 0 := (h 10 29 32)
  have h30 : P 0 30 = 0 := (h 10 30 32)
  have h31 : P 0 31 = 0 := (h 10 31 32)
  have h1052 : P 31 29 = 0 := (h 11 0 29).symm
  have h366 : P 11 3 = 0 := (h 11 3 28)
  have h400 : P 12 4 = 0 := (h 11 4 27)
  have h948 : P 28 24 = 0 := (h 11 11 24).symm
  have h956 : P 28 32 = 0 := (h 11 11 32).symm
  have h914 : P 27 23 = 0 := (h 11 12 23).symm
  have h673 : P 20 13 = 0 := (h 11 13 22)
  have h13 : P 0 13 = 0 := (h 11 13 31)
  have h14 : P 0 14 = 0 := (h 11 14 31)
  have h741 : P 22 15 = 0 := (h 11 15 20)
  have h755 : P 22 29 = 0 := (h 11 20 29).symm
  have h758 : P 22 32 = 0 := (h 11 20 32).symm
  have h21 : P 0 21 = 0 := (h 11 21 31)
  have h692 : P 20 32 = 0 := (h 11 22 32).symm
  have h386 : P 11 23 = 0 := (h 11 23 28)
  have h23 : P 0 23 = 0 := (h 11 23 31)
  have h420 : P 12 24 = 0 := (h 11 24 27)
  have h24 : P 0 24 = 0 := (h 11 24 31)
  have h425 : P 12 29 = 0 := (h 11 27 29).symm
  have h428 : P 12 32 = 0 := (h 11 27 32).symm
  have h392 : P 11 29 = 0 := (h 11 28 29).symm
  have h395 : P 11 32 = 0 := (h 11 28 32).symm
  have h32 : P 0 32 = 0 := (h 11 31 32).symm
  have h1022 : P 30 32 = 0 := (h 12 7 32).symm
  have h988 : P 29 31 = 0 := (h 12 9 31).symm
  have h890 : P 26 32 = 0 := (h 12 15 32).symm
  have h856 : P 25 31 = 0 := (h 12 17 31).symm
  have h824 : P 24 32 = 0 := (h 12 18 32).symm
  have h757 : P 22 31 = 0 := (h 12 19 31).symm
  have h659 : P 19 32 = 0 := (h 12 22 32).symm
  have h625 : P 18 31 = 0 := (h 12 24 31).symm
  have h593 : P 17 32 = 0 := (h 12 25 32).symm
  have h526 : P 15 31 = 0 := (h 12 26 31).symm
  have h527 : P 15 32 = 0 := (h 12 26 32).symm
  have h361 : P 10 31 = 0 := (h 12 28 31).symm
  have h329 : P 9 32 = 0 := (h 12 29 32).symm
  have h262 : P 7 31 = 0 := (h 12 30 31).symm
  have h263 : P 7 32 = 0 := (h 12 30 32).symm
  have h461 : P 13 32 = 0 := (h 14 26 32).symm
  have h197 : P 5 32 = 0 := (h 14 30 32).symm
  have h725 : P 21 32 = 0 := (h 15 18 32).symm
  have h494 : P 14 32 = 0 := (h 15 25 32).symm
  have h427 : P 12 31 = 0 := (h 15 26 31).symm
  have h229 : P 6 31 = 0 := (h 15 29 31).symm
  have h230 : P 6 32 = 0 := (h 15 29 32).symm
  have h163 : P 4 31 = 0 := (h 15 30 31).symm
  have h164 : P 4 32 = 0 := (h 15 30 32).symm
  have h394 : P 11 31 = 0 := (h 16 26 31).symm
  have h130 : P 3 31 = 0 := (h 16 30 31).symm
  have h131 : P 3 32 = 0 := (h 16 30 32).symm
  have h240 : P 7 9 = 0 := (h 17 9 28)
  have h249 : P 7 18 = 0 := (h 17 18 28)
  have h257 : P 7 26 = 0 := (h 17 26 28)
  have h97 : P 2 31 = 0 := (h 17 30 31).symm
  have h98 : P 2 32 = 0 := (h 17 30 32).symm
  have h248 : P 7 17 = 0 := (h 18 17 27)
  have h255 : P 7 24 = 0 := (h 18 24 27)
  have h259 : P 7 28 = 0 := (h 18 27 28).symm
  have h64 : P 1 31 = 0 := (h 18 30 31).symm
  have h65 : P 1 32 = 0 := (h 18 30 32).symm
  have h202 : P 6 4 = 0 := (h 19 4 27)
  have h210 : P 6 12 = 0 := (h 19 12 27)
  have h223 : P 6 25 = 0 := (h 19 25 27)
  have h227 : P 6 29 = 0 := (h 19 27 29).symm
  have h888 : P 26 30 = 0 := (h 21 4 30).symm
  have h854 : P 25 29 = 0 := (h 21 6 29).symm
  have h820 : P 24 28 = 0 := (h 21 9 28).symm
  have h721 : P 21 28 = 0 := (h 21 10 28).symm
  have h657 : P 19 30 = 0 := (h 21 12 30).symm
  have h623 : P 18 29 = 0 := (h 21 14 29).symm
  have h589 : P 17 28 = 0 := (h 21 17 28).symm
  have h591 : P 17 30 = 0 := (h 21 17 30).symm
  have h490 : P 14 28 = 0 := (h 21 18 28).symm
  have h424 : P 12 28 = 0 := (h 21 19 28).symm
  have h359 : P 10 29 = 0 := (h 21 21 29).symm
  have h325 : P 9 28 = 0 := (h 21 24 28).symm
  have h327 : P 9 30 = 0 := (h 21 24 30).symm
  have h226 : P 6 28 = 0 := (h 21 25 28).symm
  have h228 : P 6 30 = 0 := (h 21 25 30).symm
  have h160 : P 4 28 = 0 := (h 21 26 28).symm
  have h161 : P 4 29 = 0 := (h 21 26 29).symm
  have h786 : P 23 27 = 0 := (h 22 9 27).symm
  have h555 : P 16 27 = 0 := (h 22 17 27).symm
  have h390 : P 11 27 = 0 := (h 22 19 27).symm
  have h291 : P 8 27 = 0 := (h 22 24 27).symm
  have h195 : P 5 30 = 0 := (h 22 25 30).symm
  have h126 : P 3 27 = 0 := (h 22 26 27).symm
  have h128 : P 3 29 = 0 := (h 22 26 29).symm
  have h524 : P 15 29 = 0 := (h 23 17 29).symm
  have h260 : P 7 29 = 0 := (h 23 24 29).symm
  have h261 : P 7 30 = 0 := (h 23 24 30).symm
  have h94 : P 2 28 = 0 := (h 23 26 28).symm
  have h95 : P 2 29 = 0 := (h 23 26 29).symm
  have h60 : P 1 27 = 0 := (h 24 26 27).symm
  have h62 : P 1 29 = 0 := (h 24 26 29).symm
  have h27 : P 0 27 = 0 := (h 25 26 27).symm
  have h28 : P 0 28 = 0 := (h 25 26 28).symm
  have h707 : P 21 14 = 0 := (h 27 1 14).symm
  have h717 : P 21 24 = 0 := (h 27 1 24).symm
  have h36 : P 1 3 = 0 := (h 27 3 21)
  have h70 : P 2 4 = 0 := (h 27 4 20)
  have h81 : P 2 15 = 0 := (h 27 15 20)
  have h48 : P 1 15 = 0 := (h 27 15 21)
  have h90 : P 2 24 = 0 := (h 27 20 24).symm
  have h56 : P 1 23 = 0 := (h 27 21 23).symm
  have h653 : P 19 26 = 0 := (h 28 2 26).symm
  have h619 : P 18 25 = 0 := (h 28 4 25).symm
  have h585 : P 17 24 = 0 := (h 28 7 24).symm
  have h517 : P 15 22 = 0 := (h 28 9 22).symm
  have h355 : P 10 25 = 0 := (h 28 12 25).symm
  have h321 : P 9 24 = 0 := (h 28 15 24).symm
  have h323 : P 9 26 = 0 := (h 28 15 26).symm
  have h253 : P 7 22 = 0 := (h 28 17 22).symm
  have h256 : P 7 25 = 0 := (h 28 17 25).symm
  have h156 : P 4 24 = 0 := (h 28 18 24).symm
  have h88 : P 2 22 = 0 := (h 28 19 22).symm
  have h551 : P 16 23 = 0 := (h 29 7 23).symm
  have h287 : P 8 23 = 0 := (h 29 15 23).symm
  have h122 : P 3 23 = 0 := (h 29 18 23).symm
  have h55 : P 1 22 = 0 := (h 29 19 22).symm
  have h483 : P 14 21 = 0 := (h 30 8 21).symm
  have h486 : P 14 24 = 0 := (h 30 8 24).symm
  have h449 : P 13 20 = 0 := (h 30 9 20).symm
  have h219 : P 6 21 = 0 := (h 30 16 21).symm
  have h222 : P 6 24 = 0 := (h 30 16 24).symm
  have h185 : P 5 20 = 0 := (h 30 17 20).symm
  have h20 : P 0 20 = 0 := (h 30 19 20).symm
  have h348 : P 10 18 = 0 := (h 33 0 18).symm
  have h314 : P 9 17 = 0 := (h 33 3 17).symm
  have h280 : P 8 16 = 0 := (h 33 4 16).symm
  have h246 : P 7 15 = 0 := (h 33 5 15).symm
  have h178 : P 5 13 = 0 := (h 33 7 13).symm
  have h144 : P 4 12 = 0 := (h 33 8 12).symm
  have h110 : P 3 11 = 0 := (h 33 9 11).symm
  have h212 : P 6 14 = 0 := (h 34 1 14).symm
  have h215 : P 6 17 = 0 := (h 34 1 17).symm
  have h78 : P 2 12 = 0 := (h 34 5 12).symm
  have h44 : P 1 11 = 0 := (h 34 6 11).symm
  have h1088 : P 32 32 = P 0 0 := (h 10 0 32).symm.trans h0
  have h1054 : P 31 31 = P 0 0 := (h 11 0 31).symm.trans h0
  have h1020 : P 30 30 = P 0 0 := (h 19 0 30).symm.trans h0
  have h986 : P 29 29 = P 0 0 := (h 20 0 29).symm.trans h0
  have h884 : P 26 26 = P 0 0 := (h 25 0 26).symm.trans h0
  have h850 : P 25 25 = P 0 0 := (h 26 0 25).symm.trans h0
  have h748 : P 22 22 = P 0 0 := (h 27 0 22).symm.trans h0
  have h646 : P 19 19 = P 0 0 := (h 30 0 19).symm.trans h0
  have h612 : P 18 18 = P 0 0 := (h 31 0 18).symm.trans h0
  have h510 : P 15 15 = P 0 0 := (h 32 0 15).symm.trans h0
  have h340 : P 10 10 = P 0 0 := (h 33 0 10).symm.trans h0
  have h238 : P 7 7 = P 0 0 := (h 34 0 7).symm.trans h0
  have h306 : P 9 9 = P 0 0 := (h 1 9 32).trans h1088
  have h272 : P 8 8 = P 0 0 := (h 2 8 32).trans h1088
  have h170 : P 5 5 = P 0 0 := (h 5 5 32).trans h1088
  have h136 : P 4 4 = P 0 0 := (h 6 4 32).trans h1088
  have h102 : P 3 3 = P 0 0 := (h 7 3 32).trans h1088
  have h68 : P 2 2 = P 0 0 := (h 8 2 32).trans h1088
  have h34 : P 1 1 = P 0 0 := (h 9 1 32).trans h1088
  have h204 : P 6 6 = P 0 0 := (h 6 6 31).trans h1054
  have h578 : P 17 17 = P 0 0 := (h 1 17 30).trans h1020
  have h544 : P 16 16 = P 0 0 := (h 2 16 30).trans h1020
  have h442 : P 13 13 = P 0 0 := (h 5 13 30).trans h1020
  have h408 : P 12 12 = P 0 0 := (h 6 12 30).trans h1020
  have h374 : P 11 11 = P 0 0 := (h 7 11 30).trans h1020
  have h476 : P 14 14 = P 0 0 := (h 6 14 29).trans h986
  have h816 : P 24 24 = P 0 0 := (h 1 24 26).trans h884
  have h782 : P 23 23 = P 0 0 := (h 2 23 26).trans h884
  have h680 : P 20 20 = P 0 0 := (h 5 20 26).trans h884
  have h714 : P 21 21 = P 0 0 := (h 6 21 25).trans h850
  have h952 : P 28 28 = P 0 0 := (h 1 19 28).symm.trans h646
  have h918 : P 27 27 = P 0 0 := (h 2 19 27).symm.trans h646
  refine ⟨P 0 0, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h14
  · exact h15
  · exact h16
  · exact h17
  · exact h18
  · exact h19
  · exact h20
  · exact h21
  · exact h22
  · exact h23
  · exact h24
  · exact h25
  · exact h26
  · exact h27
  · exact h28
  · exact h29
  · exact h30
  · exact h31
  · exact h32
  · exact h33
  · exact h34
  · exact h35
  · exact h36
  · exact h37
  · exact h38
  · exact h39
  · exact h40
  · exact h41
  · exact h42
  · exact h43
  · exact h44
  · exact h45
  · exact h46
  · exact h47
  · exact h48
  · exact h49
  · exact h50
  · exact h51
  · exact h52
  · exact h53
  · exact h54
  · exact h55
  · exact h56
  · exact h57
  · exact h58
  · exact h59
  · exact h60
  · exact h61
  · exact h62
  · exact h63
  · exact h64
  · exact h65
  · exact h66
  · exact h67
  · exact h68
  · exact h69
  · exact h70
  · exact h71
  · exact h72
  · exact h73
  · exact h74
  · exact h75
  · exact h76
  · exact h77
  · exact h78
  · exact h79
  · exact h80
  · exact h81
  · exact h82
  · exact h83
  · exact h84
  · exact h85
  · exact h86
  · exact h87
  · exact h88
  · exact h89
  · exact h90
  · exact h91
  · exact h92
  · exact h93
  · exact h94
  · exact h95
  · exact h96
  · exact h97
  · exact h98
  · exact h99
  · exact h100
  · exact h101
  · exact h102
  · exact h103
  · exact h104
  · exact h105
  · exact h106
  · exact h107
  · exact h108
  · exact h109
  · exact h110
  · exact h111
  · exact h112
  · exact h113
  · exact h114
  · exact h115
  · exact h116
  · exact h117
  · exact h118
  · exact h119
  · exact h120
  · exact h121
  · exact h122
  · exact h123
  · exact h124
  · exact h125
  · exact h126
  · exact h127
  · exact h128
  · exact h129
  · exact h130
  · exact h131
  · exact h132
  · exact h133
  · exact h134
  · exact h135
  · exact h136
  · exact h137
  · exact h138
  · exact h139
  · exact h140
  · exact h141
  · exact h142
  · exact h143
  · exact h144
  · exact h145
  · exact h146
  · exact h147
  · exact h148
  · exact h149
  · exact h150
  · exact h151
  · exact h152
  · exact h153
  · exact h154
  · exact h155
  · exact h156
  · exact h157
  · exact h158
  · exact h159
  · exact h160
  · exact h161
  · exact h162
  · exact h163
  · exact h164
  · exact h165
  · exact h166
  · exact h167
  · exact h168
  · exact h169
  · exact h170
  · exact h171
  · exact h172
  · exact h173
  · exact h174
  · exact h175
  · exact h176
  · exact h177
  · exact h178
  · exact h179
  · exact h180
  · exact h181
  · exact h182
  · exact h183
  · exact h184
  · exact h185
  · exact h186
  · exact h187
  · exact h188
  · exact h189
  · exact h190
  · exact h191
  · exact h192
  · exact h193
  · exact h194
  · exact h195
  · exact h196
  · exact h197
  · exact h198
  · exact h199
  · exact h200
  · exact h201
  · exact h202
  · exact h203
  · exact h204
  · exact h205
  · exact h206
  · exact h207
  · exact h208
  · exact h209
  · exact h210
  · exact h211
  · exact h212
  · exact h213
  · exact h214
  · exact h215
  · exact h216
  · exact h217
  · exact h218
  · exact h219
  · exact h220
  · exact h221
  · exact h222
  · exact h223
  · exact h224
  · exact h225
  · exact h226
  · exact h227
  · exact h228
  · exact h229
  · exact h230
  · exact h231
  · exact h232
  · exact h233
  · exact h234
  · exact h235
  · exact h236
  · exact h237
  · exact h238
  · exact h239
  · exact h240
  · exact h241
  · exact h242
  · exact h243
  · exact h244
  · exact h245
  · exact h246
  · exact h247
  · exact h248
  · exact h249
  · exact h250
  · exact h251
  · exact h252
  · exact h253
  · exact h254
  · exact h255
  · exact h256
  · exact h257
  · exact h258
  · exact h259
  · exact h260
  · exact h261
  · exact h262
  · exact h263
  · exact h264
  · exact h265
  · exact h266
  · exact h267
  · exact h268
  · exact h269
  · exact h270
  · exact h271
  · exact h272
  · exact h273
  · exact h274
  · exact h275
  · exact h276
  · exact h277
  · exact h278
  · exact h279
  · exact h280
  · exact h281
  · exact h282
  · exact h283
  · exact h284
  · exact h285
  · exact h286
  · exact h287
  · exact h288
  · exact h289
  · exact h290
  · exact h291
  · exact h292
  · exact h293
  · exact h294
  · exact h295
  · exact h296
  · exact h297
  · exact h298
  · exact h299
  · exact h300
  · exact h301
  · exact h302
  · exact h303
  · exact h304
  · exact h305
  · exact h306
  · exact h307
  · exact h308
  · exact h309
  · exact h310
  · exact h311
  · exact h312
  · exact h313
  · exact h314
  · exact h315
  · exact h316
  · exact h317
  · exact h318
  · exact h319
  · exact h320
  · exact h321
  · exact h322
  · exact h323
  · exact h324
  · exact h325
  · exact h326
  · exact h327
  · exact h328
  · exact h329
  · exact h330
  · exact h331
  · exact h332
  · exact h333
  · exact h334
  · exact h335
  · exact h336
  · exact h337
  · exact h338
  · exact h339
  · exact h340
  · exact h341
  · exact h342
  · exact h343
  · exact h344
  · exact h345
  · exact h346
  · exact h347
  · exact h348
  · exact h349
  · exact h350
  · exact h351
  · exact h352
  · exact h353
  · exact h354
  · exact h355
  · exact h356
  · exact h357
  · exact h358
  · exact h359
  · exact h360
  · exact h361
  · exact h362
  · exact h363
  · exact h364
  · exact h365
  · exact h366
  · exact h367
  · exact h368
  · exact h369
  · exact h370
  · exact h371
  · exact h372
  · exact h373
  · exact h374
  · exact h375
  · exact h376
  · exact h377
  · exact h378
  · exact h379
  · exact h380
  · exact h381
  · exact h382
  · exact h383
  · exact h384
  · exact h385
  · exact h386
  · exact h387
  · exact h388
  · exact h389
  · exact h390
  · exact h391
  · exact h392
  · exact h393
  · exact h394
  · exact h395
  · exact h396
  · exact h397
  · exact h398
  · exact h399
  · exact h400
  · exact h401
  · exact h402
  · exact h403
  · exact h404
  · exact h405
  · exact h406
  · exact h407
  · exact h408
  · exact h409
  · exact h410
  · exact h411
  · exact h412
  · exact h413
  · exact h414
  · exact h415
  · exact h416
  · exact h417
  · exact h418
  · exact h419
  · exact h420
  · exact h421
  · exact h422
  · exact h423
  · exact h424
  · exact h425
  · exact h426
  · exact h427
  · exact h428
  · exact h429
  · exact h430
  · exact h431
  · exact h432
  · exact h433
  · exact h434
  · exact h435
  · exact h436
  · exact h437
  · exact h438
  · exact h439
  · exact h440
  · exact h441
  · exact h442
  · exact h443
  · exact h444
  · exact h445
  · exact h446
  · exact h447
  · exact h448
  · exact h449
  · exact h450
  · exact h451
  · exact h452
  · exact h453
  · exact h454
  · exact h455
  · exact h456
  · exact h457
  · exact h458
  · exact h459
  · exact h460
  · exact h461
  · exact h462
  · exact h463
  · exact h464
  · exact h465
  · exact h466
  · exact h467
  · exact h468
  · exact h469
  · exact h470
  · exact h471
  · exact h472
  · exact h473
  · exact h474
  · exact h475
  · exact h476
  · exact h477
  · exact h478
  · exact h479
  · exact h480
  · exact h481
  · exact h482
  · exact h483
  · exact h484
  · exact h485
  · exact h486
  · exact h487
  · exact h488
  · exact h489
  · exact h490
  · exact h491
  · exact h492
  · exact h493
  · exact h494
  · exact h495
  · exact h496
  · exact h497
  · exact h498
  · exact h499
  · exact h500
  · exact h501
  · exact h502
  · exact h503
  · exact h504
  · exact h505
  · exact h506
  · exact h507
  · exact h508
  · exact h509
  · exact h510
  · exact h511
  · exact h512
  · exact h513
  · exact h514
  · exact h515
  · exact h516
  · exact h517
  · exact h518
  · exact h519
  · exact h520
  · exact h521
  · exact h522
  · exact h523
  · exact h524
  · exact h525
  · exact h526
  · exact h527
  · exact h528
  · exact h529
  · exact h530
  · exact h531
  · exact h532
  · exact h533
  · exact h534
  · exact h535
  · exact h536
  · exact h537
  · exact h538
  · exact h539
  · exact h540
  · exact h541
  · exact h542
  · exact h543
  · exact h544
  · exact h545
  · exact h546
  · exact h547
  · exact h548
  · exact h549
  · exact h550
  · exact h551
  · exact h552
  · exact h553
  · exact h554
  · exact h555
  · exact h556
  · exact h557
  · exact h558
  · exact h559
  · exact h560
  · exact h561
  · exact h562
  · exact h563
  · exact h564
  · exact h565
  · exact h566
  · exact h567
  · exact h568
  · exact h569
  · exact h570
  · exact h571
  · exact h572
  · exact h573
  · exact h574
  · exact h575
  · exact h576
  · exact h577
  · exact h578
  · exact h579
  · exact h580
  · exact h581
  · exact h582
  · exact h583
  · exact h584
  · exact h585
  · exact h586
  · exact h587
  · exact h588
  · exact h589
  · exact h590
  · exact h591
  · exact h592
  · exact h593
  · exact h594
  · exact h595
  · exact h596
  · exact h597
  · exact h598
  · exact h599
  · exact h600
  · exact h601
  · exact h602
  · exact h603
  · exact h604
  · exact h605
  · exact h606
  · exact h607
  · exact h608
  · exact h609
  · exact h610
  · exact h611
  · exact h612
  · exact h613
  · exact h614
  · exact h615
  · exact h616
  · exact h617
  · exact h618
  · exact h619
  · exact h620
  · exact h621
  · exact h622
  · exact h623
  · exact h624
  · exact h625
  · exact h626
  · exact h627
  · exact h628
  · exact h629
  · exact h630
  · exact h631
  · exact h632
  · exact h633
  · exact h634
  · exact h635
  · exact h636
  · exact h637
  · exact h638
  · exact h639
  · exact h640
  · exact h641
  · exact h642
  · exact h643
  · exact h644
  · exact h645
  · exact h646
  · exact h647
  · exact h648
  · exact h649
  · exact h650
  · exact h651
  · exact h652
  · exact h653
  · exact h654
  · exact h655
  · exact h656
  · exact h657
  · exact h658
  · exact h659
  · exact h660
  · exact h661
  · exact h662
  · exact h663
  · exact h664
  · exact h665
  · exact h666
  · exact h667
  · exact h668
  · exact h669
  · exact h670
  · exact h671
  · exact h672
  · exact h673
  · exact h674
  · exact h675
  · exact h676
  · exact h677
  · exact h678
  · exact h679
  · exact h680
  · exact h681
  · exact h682
  · exact h683
  · exact h684
  · exact h685
  · exact h686
  · exact h687
  · exact h688
  · exact h689
  · exact h690
  · exact h691
  · exact h692
  · exact h693
  · exact h694
  · exact h695
  · exact h696
  · exact h697
  · exact h698
  · exact h699
  · exact h700
  · exact h701
  · exact h702
  · exact h703
  · exact h704
  · exact h705
  · exact h706
  · exact h707
  · exact h708
  · exact h709
  · exact h710
  · exact h711
  · exact h712
  · exact h713
  · exact h714
  · exact h715
  · exact h716
  · exact h717
  · exact h718
  · exact h719
  · exact h720
  · exact h721
  · exact h722
  · exact h723
  · exact h724
  · exact h725
  · exact h726
  · exact h727
  · exact h728
  · exact h729
  · exact h730
  · exact h731
  · exact h732
  · exact h733
  · exact h734
  · exact h735
  · exact h736
  · exact h737
  · exact h738
  · exact h739
  · exact h740
  · exact h741
  · exact h742
  · exact h743
  · exact h744
  · exact h745
  · exact h746
  · exact h747
  · exact h748
  · exact h749
  · exact h750
  · exact h751
  · exact h752
  · exact h753
  · exact h754
  · exact h755
  · exact h756
  · exact h757
  · exact h758
  · exact h759
  · exact h760
  · exact h761
  · exact h762
  · exact h763
  · exact h764
  · exact h765
  · exact h766
  · exact h767
  · exact h768
  · exact h769
  · exact h770
  · exact h771
  · exact h772
  · exact h773
  · exact h774
  · exact h775
  · exact h776
  · exact h777
  · exact h778
  · exact h779
  · exact h780
  · exact h781
  · exact h782
  · exact h783
  · exact h784
  · exact h785
  · exact h786
  · exact h787
  · exact h788
  · exact h789
  · exact h790
  · exact h791
  · exact h792
  · exact h793
  · exact h794
  · exact h795
  · exact h796
  · exact h797
  · exact h798
  · exact h799
  · exact h800
  · exact h801
  · exact h802
  · exact h803
  · exact h804
  · exact h805
  · exact h806
  · exact h807
  · exact h808
  · exact h809
  · exact h810
  · exact h811
  · exact h812
  · exact h813
  · exact h814
  · exact h815
  · exact h816
  · exact h817
  · exact h818
  · exact h819
  · exact h820
  · exact h821
  · exact h822
  · exact h823
  · exact h824
  · exact h825
  · exact h826
  · exact h827
  · exact h828
  · exact h829
  · exact h830
  · exact h831
  · exact h832
  · exact h833
  · exact h834
  · exact h835
  · exact h836
  · exact h837
  · exact h838
  · exact h839
  · exact h840
  · exact h841
  · exact h842
  · exact h843
  · exact h844
  · exact h845
  · exact h846
  · exact h847
  · exact h848
  · exact h849
  · exact h850
  · exact h851
  · exact h852
  · exact h853
  · exact h854
  · exact h855
  · exact h856
  · exact h857
  · exact h858
  · exact h859
  · exact h860
  · exact h861
  · exact h862
  · exact h863
  · exact h864
  · exact h865
  · exact h866
  · exact h867
  · exact h868
  · exact h869
  · exact h870
  · exact h871
  · exact h872
  · exact h873
  · exact h874
  · exact h875
  · exact h876
  · exact h877
  · exact h878
  · exact h879
  · exact h880
  · exact h881
  · exact h882
  · exact h883
  · exact h884
  · exact h885
  · exact h886
  · exact h887
  · exact h888
  · exact h889
  · exact h890
  · exact h891
  · exact h892
  · exact h893
  · exact h894
  · exact h895
  · exact h896
  · exact h897
  · exact h898
  · exact h899
  · exact h900
  · exact h901
  · exact h902
  · exact h903
  · exact h904
  · exact h905
  · exact h906
  · exact h907
  · exact h908
  · exact h909
  · exact h910
  · exact h911
  · exact h912
  · exact h913
  · exact h914
  · exact h915
  · exact h916
  · exact h917
  · exact h918
  · exact h919
  · exact h920
  · exact h921
  · exact h922
  · exact h923
  · exact h924
  · exact h925
  · exact h926
  · exact h927
  · exact h928
  · exact h929
  · exact h930
  · exact h931
  · exact h932
  · exact h933
  · exact h934
  · exact h935
  · exact h936
  · exact h937
  · exact h938
  · exact h939
  · exact h940
  · exact h941
  · exact h942
  · exact h943
  · exact h944
  · exact h945
  · exact h946
  · exact h947
  · exact h948
  · exact h949
  · exact h950
  · exact h951
  · exact h952
  · exact h953
  · exact h954
  · exact h955
  · exact h956
  · exact h957
  · exact h958
  · exact h959
  · exact h960
  · exact h961
  · exact h962
  · exact h963
  · exact h964
  · exact h965
  · exact h966
  · exact h967
  · exact h968
  · exact h969
  · exact h970
  · exact h971
  · exact h972
  · exact h973
  · exact h974
  · exact h975
  · exact h976
  · exact h977
  · exact h978
  · exact h979
  · exact h980
  · exact h981
  · exact h982
  · exact h983
  · exact h984
  · exact h985
  · exact h986
  · exact h987
  · exact h988
  · exact h989
  · exact h990
  · exact h991
  · exact h992
  · exact h993
  · exact h994
  · exact h995
  · exact h996
  · exact h997
  · exact h998
  · exact h999
  · exact h1000
  · exact h1001
  · exact h1002
  · exact h1003
  · exact h1004
  · exact h1005
  · exact h1006
  · exact h1007
  · exact h1008
  · exact h1009
  · exact h1010
  · exact h1011
  · exact h1012
  · exact h1013
  · exact h1014
  · exact h1015
  · exact h1016
  · exact h1017
  · exact h1018
  · exact h1019
  · exact h1020
  · exact h1021
  · exact h1022
  · exact h1023
  · exact h1024
  · exact h1025
  · exact h1026
  · exact h1027
  · exact h1028
  · exact h1029
  · exact h1030
  · exact h1031
  · exact h1032
  · exact h1033
  · exact h1034
  · exact h1035
  · exact h1036
  · exact h1037
  · exact h1038
  · exact h1039
  · exact h1040
  · exact h1041
  · exact h1042
  · exact h1043
  · exact h1044
  · exact h1045
  · exact h1046
  · exact h1047
  · exact h1048
  · exact h1049
  · exact h1050
  · exact h1051
  · exact h1052
  · exact h1053
  · exact h1054
  · exact h1055
  · exact h1056
  · exact h1057
  · exact h1058
  · exact h1059
  · exact h1060
  · exact h1061
  · exact h1062
  · exact h1063
  · exact h1064
  · exact h1065
  · exact h1066
  · exact h1067
  · exact h1068
  · exact h1069
  · exact h1070
  · exact h1071
  · exact h1072
  · exact h1073
  · exact h1074
  · exact h1075
  · exact h1076
  · exact h1077
  · exact h1078
  · exact h1079
  · exact h1080
  · exact h1081
  · exact h1082
  · exact h1083
  · exact h1084
  · exact h1085
  · exact h1086
  · exact h1087
  · exact h1088


theorem transpose_mul_higgs_apply {K : Type*} [Semiring K]
    (P : Matrix (Fin 33) (Fin 33) K) (m : Fin 35) (i j : Fin 33) :
    (P.transpose * higgsMatrix K m) i j =
      (match complement m j with | none => 0 | some k => P k i) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, higgsMatrix]
  simp_rw [complement_symm m _ j]
  cases hc : complement m j with
  | none => simp [hc]
  | some k => simp [hc, eq_comm]

theorem higgs_mul_apply {K : Type*} [Semiring K]
    (P : Matrix (Fin 33) (Fin 33) K) (m : Fin 35) (i j : Fin 33) :
    (higgsMatrix K m * P) i j =
      (match complement m i with | none => 0 | some k => P k j) := by
  simp only [Matrix.mul_apply, higgsMatrix]
  cases hc : complement m i with
  | none => simp [hc]
  | some k => simp [hc, eq_comm]

theorem scalar_of_higgs_equations {K : Type*} [Semiring K]
    (P : Matrix (Fin 33) (Fin 33) K)
    (h : ∀ m : Fin 35, P.transpose * higgsMatrix K m = higgsMatrix K m * P) :
    ∃ c : K, ∀ i j, P i j = if i = j then c else 0 := by
  apply scalar_of_entryConstraints P
  intro m i j
  have he := congrArg (fun M : Matrix (Fin 33) (Fin 33) K => M i j) (h m)
  simpa only [transpose_mul_higgs_apply, higgs_mul_apply] using he

/-- The compatible idempotents are exactly zero and the identity. Turning
a geometric subvariation into such a matrix remains a separate theorem. -/
theorem compatible_projector_trivial {K : Type*} [Field K]
    (P : Matrix (Fin 33) (Fin 33) K)
    (h : ∀ m : Fin 35, P.transpose * higgsMatrix K m = higgsMatrix K m * P)
    (hP : P * P = P) : P = 0 ∨ P = 1 := by
  obtain ⟨c, hc⟩ := scalar_of_higgs_equations P h
  have hm : (P * P) 0 0 = c * c := by
    simp [Matrix.mul_apply, hc, eq_comm]
  have he : c * c = c := by
    have ht := congrArg (fun M : Matrix (Fin 33) (Fin 33) K => M 0 0) hP
    simpa only [hm, hc 0 0, ite_true] using ht
  have hz : c * (c - 1) = 0 := by
    rw [mul_sub, mul_one, he, sub_self]
  rcases mul_eq_zero.mp hz with hzero | hone
  · left
    ext i j
    simpa only [hzero, ite_self, Matrix.zero_apply] using hc i j
  · right
    have hc1 : c = 1 := sub_eq_zero.mp hone
    ext i j
    simpa only [hc1, Matrix.one_apply] using hc i j

end CycleQ2FermatHiggs

#print axioms CycleQ2FermatHiggs.scalar_of_higgs_equations
#print axioms CycleQ2FermatHiggs.compatible_projector_trivial
end


/- Component: algebra/FiniteAveraging.lean -/
section
/-!+# Finite linear combinations with an explicit legal denominator

The denominator is the product of the supplied denominators. The numerator
and quotient are finite sums with the corresponding complementary products.
No denominator-degree bound, strictness condition, or coefficient search is
introduced. The final averaging theorem retains the original source whenever
the scalar weights sum to one.
-/

noncomputable section

namespace HodgeComputer

open HodgeTestbed MvPolynomial
open scoped BigOperators

theorem divergenceNumerator_C_mul {n : ℕ} (D : AmbientPoly n)
    (N : Fin (n + 1) → AmbientPoly n) (c : ℂ) :
    divergenceNumerator D (fun i => C c * N i) =
      C c * divergenceNumerator D N := by
  have hc : directional (C c : AmbientPoly n) N = 0 := by
    simp [directional]
  unfold divergenceNumerator
  rw [divergence_mul, hc, zero_add, directional_mul]
  ring

theorem defect_C_mul {n : ℕ} (F A D : AmbientPoly n) (q : ℕ)
    (N : Fin (n + 1) → AmbientPoly n) (c : ℂ) :
    defect F (C c * A) D q (fun i => C c * N i) =
      C c * defect F A D q N := by
  unfold defect
  rw [directional_mul, divergenceNumerator_C_mul]
  ring

theorem Verify.C_mul {n : ℕ} {F A D Q : AmbientPoly n} {d q : ℕ}
    {N : Fin (n + 1) → AmbientPoly n}
    (h : Verify F A d q D N Q) (c : ℂ) :
    Verify F (C c * A) d q D (fun i => C c * N i) (C c * Q) where
  hypersurface_ne_zero := h.hypersurface_ne_zero
  hypersurface_homogeneous := h.hypersurface_homogeneous
  source_homogeneous := h.source_homogeneous.C_mul c
  denominator_ne_zero := h.denominator_ne_zero
  denominator_homogeneous := h.denominator_homogeneous
  numerator_homogeneous := fun i => (h.numerator_homogeneous i).C_mul c
  denominator_legal := h.denominator_legal
  identity := by
    rw [defect_C_mul, h.identity]
    ring

/-- Adding a legal homogeneous factor to the denominator preserves the
certificate, with the same factor in every numerator and its square in Q. -/
theorem Verify.scale_denominator {n : ℕ} {F A D Q : AmbientPoly n} {d q : ℕ}
    {N : Fin (n + 1) → AmbientPoly n}
    (h : Verify F A d q D N Q) (H : AmbientPoly n)
    (hH : H ≠ 0) (hHhom : H.IsHomogeneous H.totalDegree)
    (hHlegal : IsRelPrime F H) :
    Verify F A d q (H * D) (fun i => H * N i) (H ^ 2 * Q) where
  hypersurface_ne_zero := h.hypersurface_ne_zero
  hypersurface_homogeneous := h.hypersurface_homogeneous
  source_homogeneous := h.source_homogeneous
  denominator_ne_zero := mul_ne_zero hH h.denominator_ne_zero
  denominator_homogeneous := by
    rw [MvPolynomial.totalDegree_mul_of_isDomain hH h.denominator_ne_zero]
    exact hHhom.mul h.denominator_homogeneous
  numerator_homogeneous := by
    intro i
    have hn := (Homogeneous.of_isHomogeneous hHhom).mul (h.numerator_homogeneous i)
    rw [MvPolynomial.totalDegree_mul_of_isDomain hH h.denominator_ne_zero,
      Nat.cast_add]
    convert hn using 1 <;> ring
  denominator_legal := hHlegal.mul_right h.denominator_legal
  identity := by
    rw [defect_scale_denominator, h.identity]
    ring

/-- Zero source with any already legal homogeneous denominator. -/
theorem Verify.zero_denominator {n : ℕ} (F D : AmbientPoly n) (d q : ℕ)
    (hF : F ≠ 0) (hFhom : F.IsHomogeneous d)
    (hD : D ≠ 0) (hDhom : D.IsHomogeneous D.totalDegree)
    (hDlegal : IsRelPrime F D) :
    Verify F 0 d q D (fun _ => 0) 0 where
  hypersurface_ne_zero := hF
  hypersurface_homogeneous := hFhom
  source_homogeneous := homogeneous_zero _
  denominator_ne_zero := hD
  denominator_homogeneous := hDhom
  numerator_homogeneous := fun _ => homogeneous_zero _
  denominator_legal := hDlegal
  identity := by simp [defect, directional, divergenceNumerator, divergence]

theorem Verify.add_same_denominator {n : ℕ}
    {F A B D Q R : AmbientPoly n} {d q : ℕ}
    {N M : Fin (n + 1) → AmbientPoly n}
    (h : Verify F A d q D N Q) (k : Verify F B d q D M R) :
    Verify F (A + B) d q D (fun i => N i + M i) (Q + R) where
  hypersurface_ne_zero := h.hypersurface_ne_zero
  hypersurface_homogeneous := h.hypersurface_homogeneous
  source_homogeneous := h.source_homogeneous.add k.source_homogeneous
  denominator_ne_zero := h.denominator_ne_zero
  denominator_homogeneous := h.denominator_homogeneous
  numerator_homogeneous := fun i =>
    (h.numerator_homogeneous i).add (k.numerator_homogeneous i)
  denominator_legal := h.denominator_legal
  identity := by
    rw [defect_add_same_denominator, h.identity, k.identity]
    ring

/-- Finite addition at one denominator does not raise its degree. -/
theorem Verify.sum_same_denominator {n : ℕ} {ι : Type*}
    (s : Finset ι) (F D : AmbientPoly n) (d q : ℕ)
    (A Q : ι → AmbientPoly n) (N : ι → Fin (n + 1) → AmbientPoly n)
    (hF : F ≠ 0) (hFhom : F.IsHomogeneous d)
    (hD : D ≠ 0) (hDhom : D.IsHomogeneous D.totalDegree)
    (hDlegal : IsRelPrime F D)
    (h : ∀ j ∈ s, Verify F (A j) d q D (N j) (Q j)) :
    Verify F (∑ j ∈ s, A j) d q D
      (fun i => ∑ j ∈ s, N j i) (∑ j ∈ s, Q j) := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simpa using Verify.zero_denominator F D d q hF hFhom hD hDhom hDlegal
  | @insert a s ha ih =>
      intro h
      have hs := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      have hsum := (h a (Finset.mem_insert_self a s)).add_same_denominator hs
      simpa only [Finset.sum_insert ha] using hsum

/-- Finite products retain all three denominator side conditions. -/
theorem homogeneous_legal_product {n : ℕ} {ι : Type*}
    (s : Finset ι) (F : AmbientPoly n) (D : ι → AmbientPoly n)
    (h : ∀ j ∈ s, D j ≠ 0 ∧ (D j).IsHomogeneous (D j).totalDegree ∧
      IsRelPrime F (D j)) :
    (∏ j ∈ s, D j) ≠ 0 ∧
      (∏ j ∈ s, D j).IsHomogeneous (∏ j ∈ s, D j).totalDegree ∧
      IsRelPrime F (∏ j ∈ s, D j) := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simp only [Finset.prod_empty]
      exact ⟨one_ne_zero, by simpa using isHomogeneous_one (Fin (n + 1)) ℂ,
        isRelPrime_one_right⟩
  | @insert a s ha ih =>
      intro h
      rcases ih (fun j hj => h j (Finset.mem_insert_of_mem hj)) with
        ⟨hs, hshom, hslegal⟩
      rcases h a (Finset.mem_insert_self a s) with ⟨ha0, hahom, halegal⟩
      rw [Finset.prod_insert ha]
      refine ⟨mul_ne_zero ha0 hs, ?_, halegal.mul_right hslegal⟩
      rw [MvPolynomial.totalDegree_mul_of_isDomain ha0 hs]
      exact hahom.mul hshom

/-- The product denominator has exactly the sum of the input degrees. -/
theorem totalDegree_product_of_nonzero {n : ℕ} {ι : Type*}
    (s : Finset ι) (D : ι → AmbientPoly n)
    (h : ∀ j ∈ s, D j ≠ 0) :
    (∏ j ∈ s, D j).totalDegree = ∑ j ∈ s, (D j).totalDegree := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      intro h
      have hs : (∏ j ∈ s, D j) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun j hj => h j (Finset.mem_insert_of_mem hj))
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        MvPolynomial.totalDegree_mul_of_isDomain (h a (Finset.mem_insert_self a s)) hs,
        ih (fun j hj => h j (Finset.mem_insert_of_mem hj))]

/-- Explicit finite linear combination. Each complementary product clears
one summand; the product of all denominators is homogeneous and relatively
prime to F. The quotient is retained even when it is nonzero. -/
theorem Verify.linearCombination {n : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (F : AmbientPoly n) (d q : ℕ)
    (A D Q : ι → AmbientPoly n) (N : ι → Fin (n + 1) → AmbientPoly n)
    (c : ι → ℂ) (hF : F ≠ 0) (hFhom : F.IsHomogeneous d)
    (h : ∀ j ∈ s, Verify F (A j) d q (D j) (N j) (Q j)) :
    Verify F (∑ j ∈ s, C (c j) * A j) d q (∏ j ∈ s, D j)
      (fun i => ∑ j ∈ s, (∏ k ∈ s.erase j, D k) * (C (c j) * N j i))
      (∑ j ∈ s, (∏ k ∈ s.erase j, D k) ^ 2 * (C (c j) * Q j)) := by
  have hden := homogeneous_legal_product s F D (fun j hj =>
    ⟨(h j hj).denominator_ne_zero, (h j hj).denominator_homogeneous,
      (h j hj).denominator_legal⟩)
  apply Verify.sum_same_denominator s F (∏ j ∈ s, D j) d q
    (fun j => C (c j) * A j)
    (fun j => (∏ k ∈ s.erase j, D k) ^ 2 * (C (c j) * Q j))
    (fun j i => (∏ k ∈ s.erase j, D k) * (C (c j) * N j i))
    hF hFhom hden.1 hden.2.1 hden.2.2
  intro j hj
  have hrest := homogeneous_legal_product (s.erase j) F D (fun k hk =>
    ⟨(h k (Finset.mem_of_mem_erase hk)).denominator_ne_zero,
      (h k (Finset.mem_of_mem_erase hk)).denominator_homogeneous,
      (h k (Finset.mem_of_mem_erase hk)).denominator_legal⟩)
  have hscaled := ((h j hj).C_mul (c j)).scale_denominator
    (∏ k ∈ s.erase j, D k) hrest.1 hrest.2.1 hrest.2.2
  have hprod : (∏ k ∈ s.erase j, D k) * D j = ∏ k ∈ s, D k := by
    calc
      (∏ k ∈ s.erase j, D k) * D j =
          D j * (∏ k ∈ s.erase j, D k) := mul_comm _ _
      _ = ∏ k ∈ insert j (s.erase j), D k :=
        (Finset.prod_insert (Finset.notMem_erase j s)).symm
      _ = ∏ k ∈ s, D k := by rw [Finset.insert_erase hj]
  simpa only [hprod] using hscaled

/-- Weighted averaging preserves a common source. This is the algebraic
certificate step needed after a finite family of conjugate witnesses has
been supplied; the resulting denominator is their product. -/
theorem Verify.average {n : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (F A : AmbientPoly n) (d q : ℕ)
    (D Q : ι → AmbientPoly n) (N : ι → Fin (n + 1) → AmbientPoly n)
    (c : ι → ℂ) (hc : ∑ j ∈ s, c j = 1)
    (hF : F ≠ 0) (hFhom : F.IsHomogeneous d)
    (h : ∀ j ∈ s, Verify F A d q (D j) (N j) (Q j)) :
    Verify F A d q (∏ j ∈ s, D j)
      (fun i => ∑ j ∈ s, (∏ k ∈ s.erase j, D k) * (C (c j) * N j i))
      (∑ j ∈ s, (∏ k ∈ s.erase j, D k) ^ 2 * (C (c j) * Q j)) := by
  have hsource : (∑ j ∈ s, C (c j) * A) = A := by
    calc
      (∑ j ∈ s, C (c j) * A) = (∑ j ∈ s, C (c j)) * A :=
        (Finset.sum_mul s (fun j => C (c j)) A).symm
      _ = C (∑ j ∈ s, c j) * A := by rw [map_sum]
      _ = A := by rw [hc]; simp
  simpa only [hsource] using
    Verify.linearCombination s F d q (fun _ => A) D Q N c hF hFhom h

/-- Equal-weight averaging over a nonempty finite family. -/
theorem Verify.uniformAverage {n : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) (F A : AmbientPoly n) (d q : ℕ)
    (D Q : ι → AmbientPoly n) (N : ι → Fin (n + 1) → AmbientPoly n)
    (hF : F ≠ 0) (hFhom : F.IsHomogeneous d)
    (h : ∀ j ∈ s, Verify F A d q (D j) (N j) (Q j)) :
    Verify F A d q (∏ j ∈ s, D j)
      (fun i => ∑ j ∈ s,
        (∏ k ∈ s.erase j, D k) * (C ((s.card : ℂ)⁻¹) * N j i))
      (∑ j ∈ s,
        (∏ k ∈ s.erase j, D k) ^ 2 * (C ((s.card : ℂ)⁻¹) * Q j)) := by
  have hcard : (s.card : ℂ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  have hc : (∑ _j ∈ s, (s.card : ℂ)⁻¹) = 1 := by
    simp [nsmul_eq_mul, hcard]
  exact Verify.average s F A d q D Q N (fun _ => (s.card : ℂ)⁻¹) hc hF hFhom h

end HodgeComputer

#print axioms HodgeComputer.Verify.scale_denominator
#print axioms HodgeComputer.Verify.linearCombination
#print axioms HodgeComputer.Verify.average
#print axioms HodgeComputer.Verify.uniformAverage
end
end


/- Component: bridge/LocalizedCertificate.lean -/
section
/-!
# Rational differential equations and the protected certificate

This module supplies the algebraic end of the nonconstructive support argument.
It uses actual derivations on the fraction field of the ambient polynomial ring.
The quotient rule is proved by the existing fraction-derivation construction;
the divergence and the cleared defect are then identified without additional
differential hypotheses.

The key equivalence allows the residual term to have an arbitrary denominator
coprime to the hypersurface. Euclid's lemma removes that residual denominator,
so geometry need only prove regularity along the hypersurface. It need not
predict the polynomial quotient accepted by `Verify`.

The prescribed-power constructor proves nonvanishing, homogeneity, the exact
numerator degree, and coprimality for D = S^q. For a sextic at q = 2, its
denominator is S^2 and numerator degree is 2 * degree(S) + 7.

No support theorem or geometric existence assertion is assumed as an axiom.
The geometric input remains an explicit hypothesis of the final constructor.
The fraction derivations and vector-field calculus are reused with their
original attribution from the repository's accepted constructions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace CycleQ2Bridge

open MvPolynomial HodgeComputer HodgeTestbed HodgeTestbed.Conic
open scoped BigOperators

variable {n : ℕ}

/-- The actual rational-function field in the homogeneous coordinates. -/
abbrev RationalFunction (n : ℕ) := FractionRing (AmbientPoly n)

-- Choose the algebra-induced rational scalar action consistently. The
-- concrete localization also carries a transported module instance.
local instance rationalFunctionRatAlgebra (n : ℕ) : Algebra ℚ (RationalFunction n) :=
  DivisionRing.toRatAlgebra

local instance rationalFunctionRatModule (n : ℕ) : Module ℚ (RationalFunction n) :=
  Algebra.toModule

/-- The injective polynomial-to-rational-function map. -/
abbrev polynomialMap (n : ℕ) : AmbientPoly n →+* RationalFunction n :=
  algebraMap (AmbientPoly n) (RationalFunction n)

theorem polynomialMap_injective : Function.Injective (polynomialMap n) :=
  IsFractionRing.injective (AmbientPoly n) (RationalFunction n)

theorem polynomialMap_ne_zero {P : AmbientPoly n} (hP : P ≠ 0) :
    polynomialMap n P ≠ 0 := by
  intro h
  apply hP
  apply polynomialMap_injective
  simpa only [map_zero] using h

/-- Coordinate partial derivatives extended by the proved quotient rule. -/
def rationalPartial (n : ℕ) (i : Fin (n + 1)) :
    Derivation ℚ (RationalFunction n) (RationalFunction n) :=
  QuadricContactFraction.extend (F := RationalFunction n)
    ((MvPolynomial.pderiv i : Derivation ℂ (AmbientPoly n) (AmbientPoly n)).restrictScalars ℚ)

@[simp] theorem rationalPartial_map (i : Fin (n + 1)) (P : AmbientPoly n) :
    rationalPartial n i (polynomialMap n P) = polynomialMap n (pderiv i P) := by
  unfold rationalPartial polynomialMap
  rw [QuadricContactFraction.extend_map]
  rfl

/-- The rational field represented by a common polynomial denominator. -/
def rationalField (D : AmbientPoly n) (N : Fin (n + 1) → AmbientPoly n) :
    Fin (n + 1) → RationalFunction n :=
  fun i => polynomialMap n (N i) / polynomialMap n D

/-- The actual first-order rational differential expression. -/
def rationalDefect (F A : AmbientPoly n) (q : ℕ)
    (v : Fin (n + 1) → RationalFunction n) : RationalFunction n :=
  polynomialMap n A - (q : RationalFunction n) *
      fieldAction (k := ℚ) (rationalPartial n) v (polynomialMap n F) +
    polynomialMap n F * fieldDivergence (k := ℚ) (rationalPartial n) v

theorem rationalField_action (F D : AmbientPoly n)
    (N : Fin (n + 1) → AmbientPoly n) :
    fieldAction (k := ℚ) (rationalPartial n) (rationalField D N) (polynomialMap n F) =
      polynomialMap n (directional F N) / polynomialMap n D := by
  simp only [fieldAction_apply, rationalField, rationalPartial_map,
    directional, map_sum, map_mul, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The quotient-rule numerator really is the divergence of N / D. -/
theorem rationalField_divergence (D : AmbientPoly n)
    (N : Fin (n + 1) → AmbientPoly n) :
    fieldDivergence (k := ℚ) (rationalPartial n) (rationalField D N) =
      polynomialMap n (divergenceNumerator D N) / (polynomialMap n D)^2 := by
  have hdirection :
      (∑ i, polynomialMap n (N i) * polynomialMap n (pderiv i D)) =
        polynomialMap n (directional D N) := by
    simp only [directional, map_sum, map_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [fieldDivergence, rationalField, Derivation.leibniz_div,
    smul_eq_mul, rationalPartial_map]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, hdirection]
  simp only [divergenceNumerator, divergence, map_sub, map_mul, map_sum,
    div_eq_mul_inv, inv_pow]
  ring

/-- Clearing the common denominator identifies the rational and polynomial defects. -/
theorem rationalDefect_eq (F A D : AmbientPoly n) (q : ℕ)
    (N : Fin (n + 1) → AmbientPoly n) (hD : D ≠ 0) :
    rationalDefect F A q (rationalField D N) =
      polynomialMap n (defect F A D q N) / (polynomialMap n D)^2 := by
  have hD' := polynomialMap_ne_zero hD
  unfold rationalDefect
  rw [rationalField_action, rationalField_divergence]
  simp only [defect, map_add, map_sub, map_mul, map_pow, map_natCast]
  field_simp

/-- Exact polynomial equality is equivalent to its actual rational differential equation. -/
theorem identity_iff_rationalDefect (F A D Q : AmbientPoly n) (q : ℕ)
    (N : Fin (n + 1) → AmbientPoly n) (hD : D ≠ 0) :
    defect F A D q N = F^(q+1) * Q ↔
      rationalDefect F A q (rationalField D N) =
        (polynomialMap n F)^(q+1) *
          (polynomialMap n Q / (polynomialMap n D)^2) := by
  rw [rationalDefect_eq F A D q N hD]
  constructor
  · intro h
    rw [h, map_mul, map_pow]
    ring
  · intro h
    apply polynomialMap_injective
    have hD' := polynomialMap_ne_zero hD
    have hh := congrArg (fun z : RationalFunction n => z * (polynomialMap n D)^2) h
    simpa only [map_mul, map_pow] using (by
      field_simp at hh
      linear_combination hh : polynomialMap n (defect F A D q N) =
        (polynomialMap n F)^(q+1) * polynomialMap n Q)

/-- Divisibility of the residual expression by F^(q+1) in the ring of
rational functions with denominators coprime to F.

This is the precise algebraic meaning needed from regularity of the rational
top form along the hypersurface. The residual denominator T is unrestricted.
-/
def LocalizedEquation (F A : AmbientPoly n) (q : ℕ) (D : AmbientPoly n)
    (N : Fin (n + 1) → AmbientPoly n) : Prop :=
  ∃ P T : AmbientPoly n, T ≠ 0 ∧ IsRelPrime F T ∧
    rationalDefect F A q (rationalField D N) =
      (polynomialMap n F)^(q+1) * (polynomialMap n P / polynomialMap n T)

/-- An auxiliary residual denominator cancels by coprimality, not by an
unjustified assertion that the residual function was a polynomial. -/
theorem quotient_exists_of_localizedEquation
    (F A D : AmbientPoly n) (q : ℕ) (N : Fin (n + 1) → AmbientPoly n)
    (hD : D ≠ 0) (h : LocalizedEquation F A q D N) :
    ∃ Q : AmbientPoly n, defect F A D q N = F^(q+1) * Q := by
  obtain ⟨P, T, hT, hlegal, heq⟩ := h
  have hD' := polynomialMap_ne_zero hD
  have hT' := polynomialMap_ne_zero hT
  rw [rationalDefect_eq F A D q N hD] at heq
  have hcleared : T * defect F A D q N = F^(q+1) * (P * D^2) := by
    apply polynomialMap_injective
    simp only [map_mul, map_pow]
    field_simp at heq
    linear_combination heq
  have hdiv : F^(q+1) ∣ T * defect F A D q N := ⟨P * D^2, hcleared⟩
  exact (hlegal.pow_left : IsRelPrime (F^(q+1)) T).dvd_of_dvd_mul_left hdiv

/-- The polynomial quotient gives a legal localized residual with
denominator D^2, yielding an equivalence for a legal field. -/
theorem localizedEquation_iff_quotient
    (F A D : AmbientPoly n) (q : ℕ) (N : Fin (n + 1) → AmbientPoly n)
    (hD : D ≠ 0) (hlegal : IsRelPrime F D) :
    LocalizedEquation F A q D N ↔
      ∃ Q : AmbientPoly n, defect F A D q N = F^(q+1) * Q := by
  constructor
  · exact quotient_exists_of_localizedEquation F A D q N hD
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, D^2, pow_ne_zero 2 hD, hlegal.pow_right, ?_⟩
    simpa only [map_pow] using
      (identity_iff_rationalDefect F A D Q q N hD).mp hQ

/-- The actual first-order equation supplies exactly the quotient required
by Verify, retaining the stated homogeneous and legal field. -/
theorem exists_verify_iff_localizedEquation
    (F A D : AmbientPoly n) (d q : ℕ) (N : Fin (n + 1) → AmbientPoly n)
    (hF : F ≠ 0) (hFhom : F.IsHomogeneous d)
    (hA : Homogeneous A ((d : ℤ) * (q + 1) - (n + 1)))
    (hD : D ≠ 0) (hDhom : D.IsHomogeneous D.totalDegree)
    (hN : ∀ i, Homogeneous (N i) ((D.totalDegree : ℤ) + d*q - n))
    (hlegal : IsRelPrime F D) :
    (∃ Q : AmbientPoly n, Verify F A d q D N Q) ↔
      LocalizedEquation F A q D N := by
  constructor
  · rintro ⟨Q, hQ⟩
    exact (localizedEquation_iff_quotient F A D q N hD hlegal).mpr ⟨Q, hQ.identity⟩
  · intro h
    obtain ⟨Q, hQ⟩ := quotient_exists_of_localizedEquation F A D q N hD h
    exact ⟨Q, {
      hypersurface_ne_zero := hF
      hypersurface_homogeneous := hFhom
      source_homogeneous := hA
      denominator_ne_zero := hD
      denominator_homogeneous := hDhom
      numerator_homogeneous := hN
      denominator_legal := hlegal
      identity := hQ }⟩

/-- A nonconstructively chosen support equation with a bounded primitive
finishes every algebraic clause of the protected certificate. -/
theorem hasCertificate_of_prescribed_power
    (F A S : AmbientPoly n) (d q e : ℕ)
    (N : Fin (n + 1) → AmbientPoly n)
    (hF : F ≠ 0) (hFhom : F.IsHomogeneous d)
    (hA : Homogeneous A ((d : ℤ) * (q + 1) - (n + 1)))
    (hS : S ≠ 0) (hShom : S.IsHomogeneous e)
    (hlegal : IsRelPrime F S)
    (hN : ∀ i, Homogeneous (N i) ((e : ℤ)*q + d*q - n))
    (hlocal : LocalizedEquation F A q (S^q) N) :
    HasCertificate F q A := by
  have hD : S^q ≠ 0 := pow_ne_zero q hS
  have hDhom : (S^q).IsHomogeneous (e*q) := hShom.pow q
  have hdegree : (S^q).totalDegree = e*q := hDhom.totalDegree hD
  obtain ⟨Q, hQ⟩ := (exists_verify_iff_localizedEquation F A (S^q) d q N
    hF hFhom hA hD (by simpa only [hdegree] using hDhom)
    (by
      intro i
      simpa only [hdegree, Nat.cast_mul] using hN i)
    hlegal.pow_right).mpr hlocal
  exact hQ.hasCertificate

/-- The degree bookkeeping from the filtered double-pole primitive for a
sextic fourfold, without an explicit support equation or degree bound. -/
theorem sextic_q2_hasCertificate_of_square_primitive
    (F A S : AmbientPoly 5) (e : ℕ) (N : Fin 6 → AmbientPoly 5)
    (hF : F ≠ 0) (hFhom : F.IsHomogeneous 6)
    (hA : Homogeneous A 12)
    (hS : S ≠ 0) (hShom : S.IsHomogeneous e)
    (hlegal : IsRelPrime F S)
    (hN : ∀ i, Homogeneous (N i) (2*(e : ℤ)+7))
    (hlocal : LocalizedEquation F A 2 (S^2) N) :
    HasCertificate F 2 A := by
  apply hasCertificate_of_prescribed_power F A S 6 2 e N hF hFhom
  · simpa using hA
  · exact hS
  · exact hShom
  · exact hlegal
  · intro i
    convert hN i using 1
    ring
  · exact hlocal

/-- For an irreducible hypersurface, the geometric choice S outside (F)
already proves both denominator nonvanishing and coprimality. -/
theorem sextic_q2_hasCertificate_of_irreducible_square_primitive
    (F A S : AmbientPoly 5) (e : ℕ) (N : Fin 6 → AmbientPoly 5)
    (hF : Irreducible F) (hFhom : F.IsHomogeneous 6)
    (hA : Homogeneous A 12) (hShom : S.IsHomogeneous e)
    (hS : ¬ F ∣ S)
    (hN : ∀ i, Homogeneous (N i) (2*(e : ℤ)+7))
    (hlocal : LocalizedEquation F A 2 (S^2) N) :
    HasCertificate F 2 A := by
  have hS0 : S ≠ 0 := by
    intro hs
    apply hS
    rw [hs]
    exact dvd_zero F
  exact sextic_q2_hasCertificate_of_square_primitive F A S e N
    hF.ne_zero hFhom hA hS0 hShom
    (hF.isRelPrime_iff_not_dvd.mpr hS) hN hlocal

/-- Any nonzero denominator can be squared without changing the actual field. -/
theorem rationalField_square (D : AmbientPoly n)
    (N : Fin (n + 1) → AmbientPoly n) (hD : D ≠ 0) :
    rationalField (D^2) (fun i => D * N i) = rationalField D N := by
  have hD' := polynomialMap_ne_zero hD
  funext i
  simp only [rationalField, map_mul, map_pow]
  field_simp

/-- The square-support formulation is exactly the original existential
problem. It is not an extra denominator ansatz, and this equivalence does
not assert that either side has been proved for a particular source. -/
theorem sextic_q2_hasCertificate_iff_square_primitive
    (F A : AmbientPoly 5)
    (hF : Irreducible F) (hFhom : F.IsHomogeneous 6)
    (hA : Homogeneous A 12) :
    HasCertificate F 2 A ↔
      ∃ (e : ℕ) (S : AmbientPoly 5) (N : Fin 6 → AmbientPoly 5),
        S.IsHomogeneous e ∧ ¬ F ∣ S ∧
        (∀ i, Homogeneous (N i) (2*(e : ℤ)+7)) ∧
        LocalizedEquation F A 2 (S^2) N := by
  constructor
  · rintro ⟨D, N, Q, h⟩
    have hdegree : F.totalDegree = 6 := hFhom.totalDegree hF.ne_zero
    rw [hdegree] at h
    refine ⟨D.totalDegree, D, (fun i => D * N i), h.denominator_homogeneous,
      hF.isRelPrime_iff_not_dvd.mp h.denominator_legal, ?_, ?_⟩
    · intro i
      have hn := (Homogeneous.of_isHomogeneous h.denominator_homogeneous).mul
        (h.numerator_homogeneous i)
      convert hn using 1
      ring
    · have hlocal := (localizedEquation_iff_quotient F A D 2 N
        h.denominator_ne_zero h.denominator_legal).mpr ⟨Q, h.identity⟩
      simpa only [LocalizedEquation, rationalField_square D N h.denominator_ne_zero]
        using hlocal
  · rintro ⟨e, S, N, hShom, hS, hN, hlocal⟩
    exact sextic_q2_hasCertificate_of_irreducible_square_primitive
      F A S e N hF hFhom hA hShom hS hN hlocal

end CycleQ2Bridge

#print axioms CycleQ2Bridge.rationalField_divergence
#print axioms CycleQ2Bridge.quotient_exists_of_localizedEquation
#print axioms CycleQ2Bridge.exists_verify_iff_localizedEquation
#print axioms CycleQ2Bridge.sextic_q2_hasCertificate_of_square_primitive
#print axioms CycleQ2Bridge.sextic_q2_hasCertificate_of_irreducible_square_primitive
#print axioms CycleQ2Bridge.sextic_q2_hasCertificate_iff_square_primitive
end
end


/- Component: support_choice/ProjectiveSupportEquation.lean -/
section
/-!
# Choosing an ambient equation for an actual proper projective support

This file proves the support-equation choice using mathlib's actual projective
spectrum, homogeneous vanishing ideals, and homogeneous components. No
cohomology or residue support is postulated or constructed here.

For every closed strict subset Z of the protected hypersurface, the theorem
chooses a positive-degree homogeneous S that vanishes on Z and is not divisible
by F. Its square is therefore a nonzero homogeneous legal denominator.

The remaining geometric assertion is that the specified residue vanishes off
some such Z. The theorem below does not assert that support exists.
-/

noncomputable section

namespace CycleQ2SupportEquation

open MvPolynomial HodgeComputer

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A homogeneous ideal not contained in another ideal has a homogeneous
element outside the latter ideal. The proof selects an actual homogeneous
component of an actual ideal-membership witness. -/
theorem exists_homogeneous_mem_not_mem
    {σ R : Type*} [CommRing R]
    (I J : Ideal (MvPolynomial σ R))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ R))
    (hIJ : ¬ I ≤ J) :
    ∃ (e : ℕ) (S : MvPolynomial σ R),
      S ∈ I ∧ S.IsHomogeneous e ∧ S ∉ J := by
  classical
  obtain ⟨P, hPI, hPJ⟩ := SetLike.not_le_iff_exists.mp hIJ
  have hex : ∃ e : ℕ, homogeneousComponent e P ∉ J := by
    by_contra! h
    apply hPJ
    rw [← sum_homogeneousComponent P]
    exact J.sum_mem fun e _ => h e
  obtain ⟨e, he⟩ := hex
  exact ⟨e, homogeneousComponent e P,
    homogeneousComponent_mem_of_mem hI hPI e,
    homogeneousComponent_isHomogeneous e P, he⟩

/-- The special case used when the hypersurface ideal is properly contained
in the ideal of a support. -/
theorem homogeneous_equation_of_strict_ideal_inclusion
    {σ R : Type*} [CommRing R]
    (F : MvPolynomial σ R) (I : Ideal (MvPolynomial σ R))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ R))
    (hFI : Ideal.span ({F} : Set (MvPolynomial σ R)) < I) :
    ∃ (e : ℕ) (S : MvPolynomial σ R),
      S ∈ I ∧ S.IsHomogeneous e ∧ ¬ F ∣ S := by
  obtain ⟨e, S, hSI, hShom, hSF⟩ :=
    exists_homogeneous_mem_not_mem I (Ideal.span {F}) hI (not_le_of_gt hFI)
  exact ⟨e, S, hSI, hShom, by simpa only [Ideal.mem_span_singleton] using hSF⟩

abbrev ambientGrading (n : ℕ) := homogeneousSubmodule (Fin (n + 1)) ℂ

/-- The actual topological projective spectrum of the ambient polynomial ring. -/
abbrev AmbientProjectiveSpace (n : ℕ) := ProjectiveSpectrum (ambientGrading n)

/-- A proper closed subset of an actual projective hypersurface has a
homogeneous ambient equation that is not divisible by its defining equation.
No projective Nullstellensatz or saturation hypothesis is needed: otherwise
zero-locus antitonicity would force the entire hypersurface into the support. -/
theorem homogeneous_equation_of_closed_proper_subset
    {n : ℕ} (F : AmbientPoly n) (Z : Set (AmbientProjectiveSpace n))
    (hZ : IsClosed Z)
    (hproper : Z ⊂ ProjectiveSpectrum.zeroLocus (ambientGrading n) {F}) :
    ∃ (e : ℕ) (S : AmbientPoly n),
      S.IsHomogeneous e ∧ ¬ F ∣ S ∧
      Z ⊆ ProjectiveSpectrum.zeroLocus (ambientGrading n) {S} := by
  classical
  let I := ProjectiveSpectrum.vanishingIdeal Z
  have hnot : ¬ I.toIdeal ≤ Ideal.span ({F} : Set (AmbientPoly n)) := by
    intro h
    have hreverse := ProjectiveSpectrum.zeroLocus_anti_mono_ideal
      (ambientGrading n) h
    change ProjectiveSpectrum.zeroLocus (ambientGrading n) (Ideal.span {F}) ⊆
      ProjectiveSpectrum.zeroLocus (ambientGrading n)
        (ProjectiveSpectrum.vanishingIdeal Z) at hreverse
    rw [ProjectiveSpectrum.zeroLocus_span,
      ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure, hZ.closure_eq] at hreverse
    exact hproper.2 hreverse
  obtain ⟨e, S, hSI, hShom, hSF⟩ :=
    exists_homogeneous_mem_not_mem I.toIdeal (Ideal.span {F}) I.isHomogeneous hnot
  refine ⟨e, S, hShom, ?_, ?_⟩
  · simpa only [Ideal.mem_span_singleton] using hSF
  · apply (ProjectiveSpectrum.subset_zeroLocus_iff_subset_vanishingIdeal
      (ambientGrading n) Z {S}).mpr
    exact Set.singleton_subset_iff.mpr hSI

theorem not_dvd_coordinate_of_degree_gt_one
    {n : ℕ} (F : AmbientPoly n) (hdegree : 1 < F.totalDegree)
    (i : Fin (n + 1)) : ¬ F ∣ X i := by
  intro h
  have hh := totalDegree_le_of_dvd_of_isDomain h (X_ne_zero i)
  rw [totalDegree_X] at hh
  exact (not_le_of_gt hdegree) hh

/-- A positive-degree support equation and its square denominator, with
legality derived from irreducibility. This is the exact equation-selection
step used before filtered de Rham theory is invoked. -/
theorem legal_square_of_closed_proper_subset
    {n : ℕ} (F : AmbientPoly n) (Z : Set (AmbientProjectiveSpace n))
    (hF : Irreducible F) (hdegree : 1 < F.totalDegree)
    (hZ : IsClosed Z)
    (hproper : Z ⊂ ProjectiveSpectrum.zeroLocus (ambientGrading n) {F}) :
    ∃ (e : ℕ) (S : AmbientPoly n),
      0 < e ∧ S.IsHomogeneous e ∧ S ≠ 0 ∧ ¬ F ∣ S ∧
      Z ⊆ ProjectiveSpectrum.zeroLocus (ambientGrading n) {S} ∧
      (S ^ 2).IsHomogeneous (2 * e) ∧ S ^ 2 ≠ 0 ∧ IsRelPrime F (S ^ 2) := by
  obtain ⟨e, S, hShom, hnot, hcover⟩ :=
    homogeneous_equation_of_closed_proper_subset F Z hZ hproper
  have hS : S ≠ 0 := by
    intro h
    apply hnot
    rw [h]
    exact dvd_zero F
  have hlegal : IsRelPrime F S := hF.isRelPrime_iff_not_dvd.mpr hnot
  have hXlegal : IsRelPrime F (X (0 : Fin (n + 1))) :=
    hF.isRelPrime_iff_not_dvd.mpr (not_dvd_coordinate_of_degree_gt_one F hdegree 0)
  have hprodlegal : IsRelPrime F (S * X (0 : Fin (n + 1))) :=
    hlegal.mul_right hXlegal
  have hprod : S * X (0 : Fin (n + 1)) ≠ 0 := mul_ne_zero hS (X_ne_zero 0)
  have hprodhom : (S * X (0 : Fin (n + 1))).IsHomogeneous (e + 1) :=
    hShom.mul (isHomogeneous_X ℂ 0)
  refine ⟨e + 1, S * X 0, Nat.succ_pos e, hprodhom, hprod,
    hF.isRelPrime_iff_not_dvd.mp hprodlegal, ?_, ?_, pow_ne_zero 2 hprod,
    hprodlegal.pow_right⟩
  · rw [ProjectiveSpectrum.zeroLocus_singleton_mul]
    exact hcover.trans Set.subset_union_left
  · simpa only [Nat.mul_comm] using hprodhom.pow 2

/-- Exact target specialization: every actual proper projective closed
support admits a legal homogeneous square denominator, existentially. -/
theorem protected_support_has_legal_square
    (Z : Set (AmbientProjectiveSpace 5))
    (hZ : IsClosed Z)
    (hproper : Z ⊂ ProjectiveSpectrum.zeroLocus (ambientGrading 5) {HodgeSubmission.F}) :
    ∃ (e : ℕ) (S : AmbientPoly 5),
      0 < e ∧ S.IsHomogeneous e ∧ S ≠ 0 ∧ ¬ HodgeSubmission.F ∣ S ∧
      Z ⊆ ProjectiveSpectrum.zeroLocus (ambientGrading 5) {S} ∧
      (S ^ 2).IsHomogeneous (2 * e) ∧ S ^ 2 ≠ 0 ∧
      IsRelPrime HodgeSubmission.F (S ^ 2) := by
  apply legal_square_of_closed_proper_subset HodgeSubmission.F Z
    CycleQ2ExactIrreducible.protected_F_irreducible
  · rw [CycleQ2Workspace.originalF_totalDegree]
    decide
  · exact hZ
  · exact hproper

/-- The actual protected hypersurface as a closed subspace of projective
spectrum, with its induced topology. -/
abbrev ProtectedHypersurface :=
  {x : AmbientProjectiveSpace 5 //
    x ∈ ProjectiveSpectrum.zeroLocus (ambientGrading 5) {HodgeSubmission.F}}

/-- The geometric support statement normally provides a proper closed subset
inside X. Closedness of the hypersurface promotes that relative support to an
ambient closed set, so the preceding theorem applies without an added
ambient-closedness assumption. -/
theorem protected_relative_support_has_legal_square
    (Z : Set ProtectedHypersurface) (hZ : IsClosed Z) (hproper : Z ≠ Set.univ) :
    ∃ (e : ℕ) (S : AmbientPoly 5),
      0 < e ∧ S.IsHomogeneous e ∧ S ≠ 0 ∧ ¬ HodgeSubmission.F ∣ S ∧
      (∀ x ∈ Z, x.val ∈ ProjectiveSpectrum.zeroLocus (ambientGrading 5) {S}) ∧
      (S ^ 2).IsHomogeneous (2 * e) ∧ S ^ 2 ≠ 0 ∧
      IsRelPrime HodgeSubmission.F (S ^ 2) := by
  let Y : Set (AmbientProjectiveSpace 5) := Subtype.val '' Z
  have hY : IsClosed Y :=
    (ProjectiveSpectrum.isClosed_zeroLocus (ambientGrading 5)
      {HodgeSubmission.F}).isClosedMap_subtype_val Z hZ
  have hYproper : Y ⊂ ProjectiveSpectrum.zeroLocus (ambientGrading 5)
      {HodgeSubmission.F} := by
    refine ⟨?_, ?_⟩
    · rintro x ⟨y, hy, rfl⟩
      exact y.property
    · intro h
      apply hproper
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨y, hy, hxy⟩ := h x.property
      have he : y = x := Subtype.ext hxy
      simpa only [he] using hy
  obtain ⟨e, S, he, hShom, hS, hnot, hcover, hDhom, hD, hlegal⟩ :=
    protected_support_has_legal_square Y hY hYproper
  refine ⟨e, S, he, hShom, hS, hnot, ?_, hDhom, hD, hlegal⟩
  intro x hx
  exact hcover ⟨x, hx, rfl⟩


/-- The homogeneous prime ideal `(F)` is an actual generic point of the
projective hypersurface. The degree assumption excludes the irrelevant ideal.
Its singleton closure gives irreducibility of the actual projective zero set. -/
theorem hypersurface_isIrreducible
    {n d : ℕ} (F : AmbientPoly n)
    (hF : Irreducible F) (hhom : F.IsHomogeneous d)
    (hdegree : 1 < F.totalDegree) :
    IsIrreducible (ProjectiveSpectrum.zeroLocus (ambientGrading n) {F}) := by
  let I : HomogeneousIdeal (ambientGrading n) :=
    ⟨Ideal.span {F}, Ideal.homogeneous_span (ambientGrading n) {F} (by
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact ⟨d, hhom⟩)⟩
  let η : AmbientProjectiveSpace n :=
    { asHomogeneousIdeal := I
      isPrime := (Ideal.span_singleton_prime hF.ne_zero).mpr hF.prime
      not_irrelevant_le := by
        intro h
        have hX : (X (0 : Fin (n + 1)) : AmbientPoly n) ∈
            HomogeneousIdeal.irrelevant (ambientGrading n) :=
          HomogeneousIdeal.mem_irrelevant_of_mem (ambientGrading n)
            (by decide : 0 < 1) (isHomogeneous_X ℂ 0)
        exact not_dvd_coordinate_of_degree_gt_one F hdegree 0
          (Ideal.mem_span_singleton.mp (h hX)) }
  have hclosure : closure ({η} : Set (AmbientProjectiveSpace n)) =
      ProjectiveSpectrum.zeroLocus (ambientGrading n) {F} := by
    rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      ProjectiveSpectrum.vanishingIdeal_singleton]
    change ProjectiveSpectrum.zeroLocus (ambientGrading n) (Ideal.span {F}) = _
    exact ProjectiveSpectrum.zeroLocus_span (ambientGrading n) {F}
  rw [← hclosure]
  exact isIrreducible_singleton.closure

/-- Irreducibility of the exact protected hypersurface as an actual space. -/
theorem protected_hypersurface_irreducible :
    IrreducibleSpace ProtectedHypersurface := by
  apply Subtype.irreducibleSpace
  apply hypersurface_isIrreducible HodgeSubmission.F
    CycleQ2ExactIrreducible.protected_F_irreducible
    CycleQ2Workspace.originalF_homogeneous
  rw [CycleQ2Workspace.originalF_totalDegree]
  decide

/-- A finite collection of genuine proper closed supports inside the
protected hypersurface still has proper union. -/
theorem protected_finite_union_proper
    (T : Finset (Set ProtectedHypersurface))
    (hclosed : ∀ Z ∈ T, IsClosed Z)
    (hproper : ∀ Z ∈ T, Z ≠ Set.univ) :
    ⋃₀ (T : Set (Set ProtectedHypersurface)) ≠ Set.univ := by
  letI := protected_hypersurface_irreducible
  intro h
  obtain ⟨Z, hZT, hcover⟩ := isIrreducible_iff_sUnion_isClosed.mp
    (IrreducibleSpace.isIrreducible_univ ProtectedHypersurface) T hclosed
    (by rw [h])
  exact hproper Z hZT (Set.eq_univ_of_univ_subset hcover)

/-- A finite family of proper closed supports has one positive-degree
homogeneous ambient equation whose square is a legal denominator. -/
theorem protected_finite_supports_have_legal_square
    (T : Finset (Set ProtectedHypersurface))
    (hclosed : ∀ Z ∈ T, IsClosed Z)
    (hproper : ∀ Z ∈ T, Z ≠ Set.univ) :
    ∃ (e : ℕ) (S : AmbientPoly 5),
      0 < e ∧ S.IsHomogeneous e ∧ S ≠ 0 ∧ ¬ HodgeSubmission.F ∣ S ∧
      (∀ Z ∈ T, ∀ x ∈ Z,
        x.val ∈ ProjectiveSpectrum.zeroLocus (ambientGrading 5) {S}) ∧
      (S ^ 2).IsHomogeneous (2 * e) ∧ S ^ 2 ≠ 0 ∧
      IsRelPrime HodgeSubmission.F (S ^ 2) := by
  have hc : IsClosed (⋃₀ (T : Set (Set ProtectedHypersurface))) := by
    rw [Set.sUnion_eq_biUnion]
    exact isClosed_biUnion_finset hclosed
  obtain ⟨e, S, he, hShom, hS, hnot, hcover, hDhom, hD, hlegal⟩ :=
    protected_relative_support_has_legal_square _ hc
      (protected_finite_union_proper T hclosed hproper)
  refine ⟨e, S, he, hShom, hS, hnot, ?_, hDhom, hD, hlegal⟩
  intro Z hZT x hx
  exact hcover x ⟨Z, hZT, hx⟩

end CycleQ2SupportEquation

#print axioms CycleQ2SupportEquation.homogeneous_equation_of_closed_proper_subset
#print axioms CycleQ2SupportEquation.protected_support_has_legal_square
#print axioms CycleQ2SupportEquation.protected_relative_support_has_legal_square

#print axioms CycleQ2SupportEquation.protected_hypersurface_irreducible
#print axioms CycleQ2SupportEquation.protected_finite_supports_have_legal_square
end
end


/- Component: jacobian/FermatJacobian.lean -/
section
/-!
# The actual weighted Fermat Jacobian algebra

The coefficient functionals and the socle pairing in this file descend from
the polynomial ring to its actual Jacobian quotient. They are not supplied
as abstract pairing hypotheses. The comparison with geometric Hodge theory
remains a different assertion.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace CycleQ2FermatJacobian

open MvPolynomial
open CycleQ2FermatHiggs

abbrev Poly := MvPolynomial (Fin 5) ℂ
abbrev Exp := Fin 5 →₀ ℕ

def exponent (a : Fin 5 → ℕ) : Exp := Finsupp.equivFunOnFinite.symm a

@[simp] theorem exponent_apply (a : Fin 5 → ℕ) (i : Fin 5) : exponent a i = a i := rfl

def cutoff (i : Fin 5) : ℕ := socle i + 1
def fermat : Poly := X 0 ^ 6 + X 1 ^ 6 + X 2 ^ 6 + X 3 ^ 6 + X 4 ^ 3
def generator (i : Fin 5) : Poly := X i ^ cutoff i
def derivativeScalar (i : Fin 5) : ℂ := if i = 4 then 3 else 6
def jacobianIdeal : Ideal Poly := Ideal.span (Set.range fun i => pderiv i fermat)
def powerIdeal : Ideal Poly := Ideal.span (Set.range generator)

theorem derivative_eq (i : Fin 5) :
    pderiv i fermat = C (derivativeScalar i) * generator i := by
  fin_cases i <;>
    norm_num [fermat, derivativeScalar, generator, cutoff, socle, Pi.single_apply,
      Fin.ext_iff, map_ofNat] <;> ring <;> rfl

theorem derivativeScalar_ne_zero (i : Fin 5) : derivativeScalar i ≠ 0 := by
  unfold derivativeScalar
  split <;> norm_num

theorem jacobianIdeal_eq_powerIdeal : jacobianIdeal = powerIdeal := by
  apply le_antisymm
  · rw [jacobianIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change pderiv i fermat ∈ powerIdeal
    rw [derivative_eq]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rw [powerIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have hi : pderiv i fermat ∈ jacobianIdeal := Ideal.subset_span ⟨i, rfl⟩
    have hs := Ideal.mul_mem_left jacobianIdeal (C ((derivativeScalar i)⁻¹)) hi
    rw [derivative_eq, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (derivativeScalar_ne_zero i),
      map_one, one_mul] at hs
    exact hs

theorem powerIdeal_eq_monomialIdeal : powerIdeal =
    Ideal.span ((fun d : Exp => monomial d (1 : ℂ)) ''
      Set.range (fun i : Fin 5 => Finsupp.single i (cutoff i))) := by
  unfold powerIdeal
  congr 1
  ext p
  simp only [Set.mem_range, Set.mem_image, generator, X_pow_eq_monomial]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩

/-- An exact membership criterion in the ideal generated by the five actual
partial derivatives. -/
theorem mem_jacobianIdeal_iff (p : Poly) : p ∈ jacobianIdeal ↔
    ∀ d ∈ p.support, ∃ i : Fin 5, socle i < d i := by
  rw [jacobianIdeal_eq_powerIdeal, powerIdeal_eq_monomialIdeal,
    mem_ideal_span_monomial_image]
  simp only [Set.mem_range, exists_exists_eq_and, Finsupp.single_le_iff, cutoff,
    Nat.succ_le_iff]

def bounded : Set Exp := {d | ∀ i, d i ≤ socle i}
abbrev BoundedExp := bounded

theorem bounded_coeff_zero_of_mem {p : Poly} (hp : p ∈ jacobianIdeal)
    {d : Exp} (hd : d ∈ bounded) : coeff d p = 0 := by
  by_contra hc
  obtain ⟨i, hi⟩ := (mem_jacobianIdeal_iff p).mp hp d (mem_support_iff.mpr hc)
  exact (not_lt_of_ge (hd i)) hi

theorem mem_jacobianIdeal_iff_bounded_coeff_zero (p : Poly) :
    p ∈ jacobianIdeal ↔ ∀ d ∈ bounded, coeff d p = 0 := by
  constructor
  · exact fun hp d hd => bounded_coeff_zero_of_mem hp hd
  · intro hp
    apply (mem_jacobianIdeal_iff p).mpr
    intro d hd
    by_contra h
    push Not at h
    have hz := hp d (by simpa only [bounded, Set.mem_ofPred_eq, not_lt] using h)
    exact (mem_support_iff.mp hd) hz

abbrev JacobianRing := Poly ⧸ jacobianIdeal

def quotientMap : Poly →ₐ[ℂ] JacobianRing := Ideal.Quotient.mkₐ ℂ jacobianIdeal

/-- Coefficients inside the exponent box descend to the true Jacobian ring. -/
def quotientCoeff (d : BoundedExp) : JacobianRing →ₗ[ℂ] ℂ :=
  (jacobianIdeal.restrictScalars ℂ).liftQ (lcoeff ℂ d.val) (by
    intro p hp
    exact bounded_coeff_zero_of_mem hp d.property)

@[simp] theorem quotientCoeff_mk (d : BoundedExp) (p : Poly) :
    quotientCoeff d (quotientMap p) = coeff d.val p := rfl

def socleTrace : JacobianRing →ₗ[ℂ] ℂ :=
  quotientCoeff ⟨exponent socle, fun _ => le_rfl⟩

@[simp] theorem socleTrace_mk (p : Poly) :
    socleTrace (quotientMap p) = coeff (exponent socle) p := rfl

def monomialClass (a : Fin 5 → ℕ) : JacobianRing :=
  quotientMap (monomial (exponent a) 1)

theorem exponent_add (a b : Fin 5 → ℕ) :
    exponent a + exponent b = exponent (fun i => a i + b i) := by
  ext i
  rfl

/-- The socle trace of a triple product in the actual quotient is precisely
the exponent-sum test used to construct the finite Higgs matrices. -/
theorem socleTrace_triple_monomial (a b c : Fin 5 → ℕ) :
    socleTrace (monomialClass a * monomialClass b * monomialClass c) =
      if (∀ i, a i + b i + c i = socle i) then 1 else 0 := by
  classical
  rw [monomialClass, monomialClass, monomialClass, ← map_mul, ← map_mul,
    socleTrace_mk, monomial_mul, monomial_mul, one_mul, one_mul, coeff_monomial]
  congr 1
  apply propext
  constructor
  · intro h i
    exact congrArg (fun d : Exp => d i) h
  · intro h
    ext i
    exact h i

/-- This is a literal equality with the already checked finite matrix, not
an assumption naming an unspecified residue pairing. -/
theorem socleTrace_triple_eq_higgsMatrix (m : Fin 35) (i j : Fin 33) :
    socleTrace (monomialClass (basisMonomial i) * monomialClass (basisMonomial j) *
      monomialClass (tangentMonomial m)) = higgsMatrix ℂ m i j := by
  rw [socleTrace_triple_monomial, higgsMatrix_socle]

end CycleQ2FermatJacobian

#print axioms CycleQ2FermatJacobian.jacobianIdeal_eq_powerIdeal
#print axioms CycleQ2FermatJacobian.mem_jacobianIdeal_iff
#print axioms CycleQ2FermatJacobian.socleTrace_triple_eq_higgsMatrix
end
end


/- Component: jacobian/FermatJacobianBasis.lean -/
section
/-!
# Monomial basis of the actual Fermat Jacobian quotient

The normal form is constructed by retaining bounded coefficients. Its kernel
is proved to be the derivative ideal, so the basis below is a basis of the
actual quotient rather than a separately introduced finite algebra.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace CycleQ2FermatJacobian
open MvPolynomial
open CycleQ2FermatHiggs

def normalForm : Poly →ₗ[ℂ] (BoundedExp →₀ ℂ) :=
  (Finsupp.lsubtypeDomain bounded).comp
    (MvPolynomial.basisMonomials (Fin 5) ℂ).repr.toLinearMap

@[simp] theorem normalForm_apply (p : Poly) (d : BoundedExp) :
    normalForm p d = coeff d.val p := rfl

theorem normalForm_surjective : Function.Surjective normalForm := by
  classical
  intro f
  refine ⟨(MvPolynomial.basisMonomials (Fin 5) ℂ).repr.symm f.extendDomain, ?_⟩
  change Finsupp.subtypeDomain (fun x => x ∈ bounded)
    ((MvPolynomial.basisMonomials (Fin 5) ℂ).repr
      ((MvPolynomial.basisMonomials (Fin 5) ℂ).repr.symm f.extendDomain)) = f
  rw [LinearEquiv.apply_symm_apply, Finsupp.subtypeDomain_extendDomain]

theorem normalForm_ker :
    LinearMap.ker normalForm = jacobianIdeal.restrictScalars ℂ := by
  ext p
  rw [LinearMap.mem_ker, Finsupp.ext_iff]
  change (∀ d : BoundedExp, coeff d.val p = 0) ↔ p ∈ jacobianIdeal
  rw [mem_jacobianIdeal_iff_bounded_coeff_zero]
  exact Subtype.forall

/-- Unique bounded monomial coordinates in the actual Jacobian quotient. -/
def normalCoordinates : JacobianRing ≃ₗ[ℂ] (BoundedExp →₀ ℂ) :=
  (Submodule.quotEquivOfEq (jacobianIdeal.restrictScalars ℂ)
    (LinearMap.ker normalForm) normalForm_ker.symm).trans
      (normalForm.quotKerEquivOfSurjective normalForm_surjective)

@[simp] theorem normalCoordinates_mk (p : Poly) :
    normalCoordinates (quotientMap p) = normalForm p := rfl

/-- The classes of every monomial within the derivative exponent bounds form
a basis of the quotient over the complex numbers. -/
def quotientBasis : Module.Basis BoundedExp ℂ JacobianRing :=
  (Finsupp.basisSingleOne : Module.Basis BoundedExp ℂ (BoundedExp →₀ ℂ)).map
    normalCoordinates.symm

@[simp] theorem normalForm_monomial (d : BoundedExp) :
    normalForm (monomial d.val 1) = Finsupp.single d 1 := by
  classical
  ext e
  simp only [normalForm_apply, coeff_monomial, Finsupp.single_apply]
  congr 1
  exact propext Subtype.ext_iff.symm

theorem quotientBasis_eq_monomialClass (d : BoundedExp) :
    quotientBasis d = quotientMap (monomial d.val 1) := by
  apply normalCoordinates.injective
  simp [quotientBasis]

theorem boundedMonomials_linearIndependent :
    LinearIndependent ℂ (fun d : BoundedExp => quotientMap (monomial d.val 1)) := by
  simpa only [← quotientBasis_eq_monomialClass] using quotientBasis.linearIndependent

theorem boundedMonomials_span :
    Submodule.span ℂ (Set.range fun d : BoundedExp =>
      quotientMap (monomial d.val 1)) = ⊤ := by
  simpa only [← quotientBasis_eq_monomialClass] using quotientBasis.span_eq

/-- The exponent box has four side lengths five and one side length two. -/
def boundedExponentEquiv : BoundedExp ≃ (∀ i : Fin 5, Fin (cutoff i)) where
  toFun d i := ⟨d.val i, Nat.lt_succ_of_le (d.property i)⟩
  invFun a := ⟨exponent (fun i => (a i).val), fun i => Nat.le_of_lt_succ (a i).isLt⟩
  left_inv d := by
    apply Subtype.ext
    ext i
    rfl
  right_inv a := by
    funext i
    apply Fin.ext
    rfl

theorem boundedExponent_card : Nat.card BoundedExp = 1250 := by
  rw [Nat.card_congr boundedExponentEquiv, Nat.card_eq_fintype_card, Fintype.card_pi]
  norm_num [cutoff, socle, Fin.prod_univ_succ]

theorem jacobian_finrank : Module.finrank ℂ JacobianRing = 1250 := by
  rw [Module.finrank_eq_nat_card_basis quotientBasis, boundedExponent_card]

def basisIndex (i : Fin 33) : BoundedExp :=
  ⟨exponent (basisMonomial i), (basis_properties i).2.2⟩

def tangentIndex (m : Fin 35) : BoundedExp :=
  ⟨exponent (tangentMonomial m), (tangent_properties m).2.2⟩

theorem basisIndex_injective : Function.Injective basisIndex := by
  intro i j h
  apply basis_injective
  funext k
  exact congrArg (fun d : BoundedExp => d.val k) h

theorem tangentIndex_injective : Function.Injective tangentIndex := by
  intro i j h
  apply tangent_injective
  funext k
  exact congrArg (fun d : BoundedExp => d.val k) h

theorem basisMonomialClass_linearIndependent :
    LinearIndependent ℂ (fun i : Fin 33 => monomialClass (basisMonomial i)) :=
  boundedMonomials_linearIndependent.comp basisIndex basisIndex_injective

theorem tangentMonomialClass_linearIndependent :
    LinearIndependent ℂ (fun m : Fin 35 => monomialClass (tangentMonomial m)) :=
  boundedMonomials_linearIndependent.comp tangentIndex tangentIndex_injective

end CycleQ2FermatJacobian

#print axioms CycleQ2FermatJacobian.normalCoordinates
#print axioms CycleQ2FermatJacobian.quotientBasis_eq_monomialClass
#print axioms CycleQ2FermatJacobian.boundedMonomials_linearIndependent
#print axioms CycleQ2FermatJacobian.boundedMonomials_span
#print axioms CycleQ2FermatJacobian.jacobian_finrank
#print axioms CycleQ2FermatJacobian.basisMonomialClass_linearIndependent
#print axioms CycleQ2FermatJacobian.tangentMonomialClass_linearIndependent
end
end


/- Component: jacobian/FermatJacobianGraded.lean -/
section
/-!
# The actual degree-six character components

These components are images of polynomial support subspaces under the actual
Jacobian quotient map. The finite lists are proved to span those components;
their independence comes from the normal-form theorem for the quotient.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace CycleQ2FermatJacobian
open MvPolynomial
open CycleQ2FermatHiggs

def pieceSupport (n χ : ℕ) : Set Exp :=
  {d | weightedDegree d = n ∧ character d = χ}

def gradedPiece (n χ : ℕ) : Submodule ℂ JacobianRing :=
  Submodule.map quotientMap.toLinearMap (restrictSupport ℂ (pieceSupport n χ))

theorem unbounded_monomial_eq_zero (d : Exp) (hd : d ∉ bounded) :
    quotientMap (monomial d 1) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply (mem_jacobianIdeal_iff_bounded_coeff_zero _).mpr
  intro e he
  have hde : d ≠ e := by
    intro h
    exact hd (h ▸ he)
  simp [coeff_monomial, hde]

theorem bounded_exponent_tuple (d : Exp) (hd : d ∈ bounded) :
    ∃ a b c e : Fin 5, ∃ w : Fin 2,
      (d : Fin 5 → ℕ) = ![a.val, b.val, c.val, e.val, w.val] := by
  have h0 : d 0 < 5 := by simpa [socle] using Nat.lt_succ_of_le (hd 0)
  have h1 : d 1 < 5 := by simpa [socle] using Nat.lt_succ_of_le (hd 1)
  have h2 : d 2 < 5 := by simpa [socle] using Nat.lt_succ_of_le (hd 2)
  have h3 : d 3 < 5 := by simpa [socle] using Nat.lt_succ_of_le (hd 3)
  have h4 : d 4 < 2 := by simpa [socle] using Nat.lt_succ_of_le (hd 4)
  refine ⟨⟨d 0, h0⟩, ⟨d 1, h1⟩, ⟨d 2, h2⟩, ⟨d 3, h3⟩, ⟨d 4, h4⟩, ?_⟩
  funext i
  fin_cases i <;> rfl

theorem basis_complete_bounded (d : Exp) (hb : d ∈ bounded)
    (hn : weightedDegree d = 6) (hc : character d = 1) :
    ∃ i : Fin 33, exponent (basisMonomial i) = d := by
  obtain ⟨a, b, c, e, w, h⟩ := bounded_exponent_tuple d hb
  obtain ⟨i, hi⟩ := basis_complete a b c e w (h ▸ hn) (h ▸ hc)
  refine ⟨i, ?_⟩
  ext k
  exact congrFun (hi.trans h.symm) k

theorem tangent_complete_bounded (d : Exp) (hb : d ∈ bounded)
    (hn : weightedDegree d = 6) (hc : character d = 0) :
    ∃ m : Fin 35, exponent (tangentMonomial m) = d := by
  obtain ⟨a, b, c, e, w, h⟩ := bounded_exponent_tuple d hb
  obtain ⟨m, hm⟩ := tangent_complete a b c e w (h ▸ hn) (h ▸ hc)
  refine ⟨m, ?_⟩
  ext k
  exact congrFun (hm.trans h.symm) k

theorem gradedPiece_eq_span_of_enumeration {ι : Type} (a : ι → Fin 5 → ℕ)
    (n χ : ℕ) (hprop : ∀ i, weightedDegree (a i) = n ∧ character (a i) = χ)
    (hcomplete : ∀ d ∈ bounded, weightedDegree d = n → character d = χ →
      ∃ i, exponent (a i) = d) :
    gradedPiece n χ = Submodule.span ℂ (Set.range fun i => monomialClass (a i)) := by
  classical
  rw [gradedPiece, restrictSupport_eq_span, Submodule.map_span, Set.image_image]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro q ⟨d, hd, rfl⟩
    change quotientMap (monomial d 1) ∈ _
    by_cases hb : d ∈ bounded
    · obtain ⟨i, hi⟩ := hcomplete d hb hd.1 hd.2
      apply Submodule.subset_span
      refine ⟨i, ?_⟩
      change quotientMap (monomial (exponent (a i)) 1) = quotientMap (monomial d 1)
      rw [hi]
    · rw [unbounded_monomial_eq_zero d hb]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro q ⟨i, rfl⟩
    apply Submodule.subset_span
    exact ⟨exponent (a i), hprop i, rfl⟩

theorem degreeSixCharacterOne_eq_span :
    gradedPiece 6 1 = Submodule.span ℂ
      (Set.range fun i : Fin 33 => monomialClass (basisMonomial i)) :=
  gradedPiece_eq_span_of_enumeration basisMonomial 6 1
    (fun i => ⟨(basis_properties i).1, (basis_properties i).2.1⟩)
    basis_complete_bounded

theorem degreeSixCharacterZero_eq_span :
    gradedPiece 6 0 = Submodule.span ℂ
      (Set.range fun m : Fin 35 => monomialClass (tangentMonomial m)) :=
  gradedPiece_eq_span_of_enumeration tangentMonomial 6 0
    (fun m => ⟨(tangent_properties m).1, (tangent_properties m).2.1⟩)
    tangent_complete_bounded

def degreeSixCharacterOneBasis : Module.Basis (Fin 33) ℂ (gradedPiece 6 1) :=
  (Module.Basis.span basisMonomialClass_linearIndependent).map
    (LinearEquiv.ofEq _ _ degreeSixCharacterOne_eq_span.symm)

def degreeSixCharacterZeroBasis : Module.Basis (Fin 35) ℂ (gradedPiece 6 0) :=
  (Module.Basis.span tangentMonomialClass_linearIndependent).map
    (LinearEquiv.ofEq _ _ degreeSixCharacterZero_eq_span.symm)

theorem degreeSixCharacterOne_finrank : Module.finrank ℂ (gradedPiece 6 1) = 33 := by
  rw [Module.finrank_eq_card_basis degreeSixCharacterOneBasis]
  rfl

theorem degreeSixCharacterZero_finrank : Module.finrank ℂ (gradedPiece 6 0) = 35 := by
  rw [Module.finrank_eq_card_basis degreeSixCharacterZeroBasis]
  rfl

theorem degreeSixCharacterOneBasis_coe (i : Fin 33) :
    (degreeSixCharacterOneBasis i : JacobianRing) = monomialClass (basisMonomial i) := by
  simp [degreeSixCharacterOneBasis]

theorem degreeSixCharacterZeroBasis_coe (m : Fin 35) :
    (degreeSixCharacterZeroBasis m : JacobianRing) = monomialClass (tangentMonomial m) := by
  simp [degreeSixCharacterZeroBasis]

/-- The checked finite matrices are the trace matrices on the actual
degree-six character components of the Fermat derivative quotient. -/
theorem actual_component_trace_matrix (m : Fin 35) (i j : Fin 33) :
    socleTrace ((degreeSixCharacterOneBasis i : JacobianRing) *
      (degreeSixCharacterOneBasis j : JacobianRing) *
      (degreeSixCharacterZeroBasis m : JacobianRing)) = higgsMatrix ℂ m i j := by
  rw [degreeSixCharacterOneBasis_coe, degreeSixCharacterOneBasis_coe,
    degreeSixCharacterZeroBasis_coe, socleTrace_triple_eq_higgsMatrix]

theorem socle_weightedDegree_character :
    weightedDegree socle = 18 ∧ character socle = 2 := by decide

theorem socleTrace_normalized : socleTrace (monomialClass socle) = 1 := by
  rw [monomialClass, socleTrace_mk, coeff_monomial]
  simp

/-- The distinguished degree-eighteen class is actually in the socle:
each variable class annihilates it in the derivative quotient. -/
theorem socle_annihilated_by_variables (i : Fin 5) :
    quotientMap (X i) * monomialClass socle = 0 := by
  change quotientMap (monomial (Finsupp.single i 1) 1) *
    quotientMap (monomial (exponent socle) 1) = 0
  rw [← map_mul, monomial_mul, one_mul]
  apply unbounded_monomial_eq_zero
  intro h
  have hi := h i
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, exponent_apply] at hi
  omega

end CycleQ2FermatJacobian

#print axioms CycleQ2FermatJacobian.degreeSixCharacterOne_finrank
#print axioms CycleQ2FermatJacobian.degreeSixCharacterZero_finrank
#print axioms CycleQ2FermatJacobian.actual_component_trace_matrix
#print axioms CycleQ2FermatJacobian.socle_annihilated_by_variables
end
end


/- Component: seed_trace/SparseSeedTraceData.lean -/
section
/-!
# An actual quotient trace for the sparse seed

The finite trace is constructed as a coefficient of multiplication by an
explicit polynomial. Four polynomial annihilator identities prove that it
vanishes on the defining ideal, so it descends to the actual quotient.

This file concerns the sparse seed algebra. Its associated geometric surface
is singular; no smoothness or geometric trace comparison is asserted here.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section
namespace CycleQ2SeedTrace
open MvPolynomial

abbrev Poly := MvPolynomial (Fin 4) ℂ
abbrev Exp := Fin 4 →₀ ℕ

def exponent (a : Fin 4 → ℕ) : Exp := Finsupp.equivFunOnFinite.symm a

@[simp] theorem exponent_apply (a : Fin 4 → ℕ) (i : Fin 4) : exponent a i = a i := rfl

def mon (a b c d : ℕ) : Poly := X 0 ^ a * X 1 ^ b * X 2 ^ c * X 3 ^ d

def topExponent : Exp := exponent ![3, 9, 3, 9]
def cutoff (i : Fin 4) : ℕ := topExponent i + 1
def truncationIdeal : Ideal Poly := Ideal.span (Set.range fun i : Fin 4 => X i ^ cutoff i)

def b : Poly := X 3 ^ 3 + X 2 ^ 3 + X 1 * X 2 * X 3 + X 0 * X 2 * X 3 + X 0 * X 1 ^ 2
def h : Poly := b - C Complex.I * (X 1 ^ 3 + X 3 ^ 3)
def k : Poly := b + C Complex.I * (X 1 ^ 3 + X 3 ^ 3)

def relation (r : ℂ) : Fin 4 → Poly := ![
  X 0 ^ 2 - C r * X 1 * X 3,
  X 1 ^ 2 * X 3 ^ 2,
  X 2 ^ 4,
  h]

def reducedIdeal (r : ℂ) : Ideal Poly := Ideal.span (Set.range (relation r))

def traceNumerator (r : ℂ) : Poly :=
    C ((1 : ℂ)) * mon 3 9 3 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 3 9 2 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 3 8 1 3 +
    C ((-2 : ℂ) * r ^ 2) * mon 3 4 0 8 +
    C ((4 : ℂ)) * mon 3 3 0 9 +
    C ((4 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * mon 3 2 1 9 +
    C ((4 : ℂ) * r ^ 2 * Complex.I) * mon 3 1 3 8 +
    C ((-16 : ℂ) * Complex.I) * mon 3 0 3 9 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 2 9 2 2 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 2 9 1 3 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 2 8 3 2 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 2 8 0 5 +
    C ((-2 : ℂ) * r ^ 2 * Complex.I) * mon 2 5 0 8 +
    C ((4 : ℂ) * Complex.I) * mon 2 4 0 9 +
    C ((-2 : ℂ) * r ^ 2) * mon 2 3 1 9 +
    C ((-2 : ℂ) * r ^ 2) * mon 2 2 3 8 +
    C ((12 : ℂ)) * mon 2 1 3 9 +
    C ((-2 : ℂ) * Complex.I) * mon 1 9 1 4 +
    C ((-4 : ℂ)) * mon 1 5 0 9 +
    C ((8 : ℂ) * Complex.I) * mon 1 2 3 9 +
    C ((-2 : ℂ) * Complex.I) * mon 0 9 3 3 +
    C ((2 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 9 0 6 +
    C ((-4 : ℂ) * Complex.I) * mon 0 6 0 9 +
    C ((-4 : ℂ)) * mon 0 3 3 9

def witness00 (r : ℂ) : Poly :=
    C ((1 : ℂ)) * mon 1 9 3 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 9 2 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 1 8 1 3 +
    C ((-2 : ℂ) * r ^ 2) * mon 1 4 0 8 +
    C ((4 : ℂ)) * mon 1 3 0 9 +
    C ((4 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * mon 1 2 1 9 +
    C ((4 : ℂ) * r ^ 2 * Complex.I) * mon 1 1 3 8 +
    C ((-16 : ℂ) * Complex.I) * mon 1 0 3 9 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 9 2 2 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 9 1 3 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 8 3 2 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 0 8 0 5 +
    C ((-2 : ℂ) * r ^ 2 * Complex.I) * mon 0 5 0 8 +
    C ((4 : ℂ) * Complex.I) * mon 0 4 0 9 +
    C ((-2 : ℂ) * r ^ 2) * mon 0 3 1 9 +
    C ((-2 : ℂ) * r ^ 2) * mon 0 2 3 8 +
    C ((12 : ℂ)) * mon 0 1 3 9

def witness01 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r) * mon 3 0 3 1 +
    C ((-2 : ℂ) * Complex.I + (2 : ℂ)) * mon 3 0 2 2 +
    C ((-1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 2 0 2 3 +
    C ((2 : ℂ) * Complex.I) * mon 2 0 1 4 +
    C ((2 : ℂ) * r * Complex.I) * mon 1 0 1 5 +
    C ((2 : ℂ) * r * Complex.I) * mon 0 0 3 4 +
    C ((-2 : ℂ) * r * Complex.I + (-2 : ℂ) * r) * mon 0 0 0 7

def witness02 (r : ℂ) : Poly :=
    0

def witness03 (r : ℂ) : Poly :=
    C ((-4 : ℂ) * r) * mon 3 4 0 0 +
    C ((-8 : ℂ) * Complex.I + (4 : ℂ)) * mon 3 3 1 0 +
    C ((16 : ℂ) * r * Complex.I) * mon 3 1 3 0 +
    C ((-4 : ℂ) * r * Complex.I) * mon 2 5 0 0 +
    C ((4 : ℂ)) * mon 2 4 1 0 +
    C ((-12 : ℂ) * r) * mon 2 2 3 0 +
    C ((4 : ℂ) * r) * mon 1 6 0 0 +
    C ((-8 : ℂ) * r * Complex.I) * mon 1 3 3 0 +
    C ((4 : ℂ) * r * Complex.I) * mon 0 7 0 0 +
    C ((4 : ℂ) * r) * mon 0 4 3 0

theorem annihilator0 (r : ℂ) (hr : r ^ 3 = 2) :
    traceNumerator r * relation r 0 =
      X 0 ^ 4 * witness00 r +
      X 1 ^ 10 * witness01 r +
      X 2 ^ 4 * witness02 r +
      X 3 ^ 10 * witness03 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [traceNumerator, relation, b, h, mon,
    witness00, witness01, witness02, witness03,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one]
  ring_nf <;> (try simp only [hr', hi']) <;> ring

def witness10 (r : ℂ) : Poly :=
    0

def witness11 (r : ℂ) : Poly :=
    C ((1 : ℂ)) * mon 3 1 3 2 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 3 1 2 3 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 3 0 1 5 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 2 1 2 4 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 2 1 1 5 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 2 0 3 4 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 2 0 0 7 +
    C ((-2 : ℂ) * Complex.I) * mon 1 1 1 6 +
    C ((-2 : ℂ) * Complex.I) * mon 0 1 3 5 +
    C ((2 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 1 0 8

def witness12 (r : ℂ) : Poly :=
    0

def witness13 (r : ℂ) : Poly :=
    C ((-2 : ℂ) * r ^ 2) * mon 3 6 0 0 +
    C ((4 : ℂ)) * mon 3 5 0 1 +
    C ((4 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * mon 3 4 1 1 +
    C ((4 : ℂ) * r ^ 2 * Complex.I) * mon 3 3 3 0 +
    C ((-16 : ℂ) * Complex.I) * mon 3 2 3 1 +
    C ((-2 : ℂ) * r ^ 2 * Complex.I) * mon 2 7 0 0 +
    C ((4 : ℂ) * Complex.I) * mon 2 6 0 1 +
    C ((-2 : ℂ) * r ^ 2) * mon 2 5 1 1 +
    C ((-2 : ℂ) * r ^ 2) * mon 2 4 3 0 +
    C ((12 : ℂ)) * mon 2 3 3 1 +
    C ((-4 : ℂ)) * mon 1 7 0 1 +
    C ((8 : ℂ) * Complex.I) * mon 1 4 3 1 +
    C ((-4 : ℂ) * Complex.I) * mon 0 8 0 1 +
    C ((-4 : ℂ)) * mon 0 5 3 1

theorem annihilator1 (r : ℂ) (hr : r ^ 3 = 2) :
    traceNumerator r * relation r 1 =
      X 0 ^ 4 * witness10 r +
      X 1 ^ 10 * witness11 r +
      X 2 ^ 4 * witness12 r +
      X 3 ^ 10 * witness13 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [traceNumerator, relation, b, h, mon,
    witness10, witness11, witness12, witness13,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one]
  ring_nf <;> (try simp only [hr', hi']) <;> ring

def witness20 (r : ℂ) : Poly :=
    0

def witness21 (r : ℂ) : Poly :=
    0

def witness22 (r : ℂ) : Poly :=
    C ((1 : ℂ)) * mon 3 9 3 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 3 9 2 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 3 8 1 3 +
    C ((-2 : ℂ) * r ^ 2) * mon 3 4 0 8 +
    C ((4 : ℂ)) * mon 3 3 0 9 +
    C ((4 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * mon 3 2 1 9 +
    C ((4 : ℂ) * r ^ 2 * Complex.I) * mon 3 1 3 8 +
    C ((-16 : ℂ) * Complex.I) * mon 3 0 3 9 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 2 9 2 2 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 2 9 1 3 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 2 8 3 2 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 2 8 0 5 +
    C ((-2 : ℂ) * r ^ 2 * Complex.I) * mon 2 5 0 8 +
    C ((4 : ℂ) * Complex.I) * mon 2 4 0 9 +
    C ((-2 : ℂ) * r ^ 2) * mon 2 3 1 9 +
    C ((-2 : ℂ) * r ^ 2) * mon 2 2 3 8 +
    C ((12 : ℂ)) * mon 2 1 3 9 +
    C ((-2 : ℂ) * Complex.I) * mon 1 9 1 4 +
    C ((-4 : ℂ)) * mon 1 5 0 9 +
    C ((8 : ℂ) * Complex.I) * mon 1 2 3 9 +
    C ((-2 : ℂ) * Complex.I) * mon 0 9 3 3 +
    C ((2 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 9 0 6 +
    C ((-4 : ℂ) * Complex.I) * mon 0 6 0 9 +
    C ((-4 : ℂ)) * mon 0 3 3 9

def witness23 (r : ℂ) : Poly :=
    0

theorem annihilator2 (r : ℂ) (hr : r ^ 3 = 2) :
    traceNumerator r * relation r 2 =
      X 0 ^ 4 * witness20 r +
      X 1 ^ 10 * witness21 r +
      X 2 ^ 4 * witness22 r +
      X 3 ^ 10 * witness23 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [traceNumerator, relation, b, h, mon,
    witness20, witness21, witness22, witness23,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one]
  ring_nf <;> (try simp only [hr', hi']) <;> ring

def witness30 (r : ℂ) : Poly :=
    C ((1 : ℂ)) * mon 0 11 3 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 0 11 2 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 10 1 3 +
    C ((1 : ℂ)) * mon 0 9 4 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 0 9 3 2 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 8 2 4 +
    C ((-2 : ℂ) * r ^ 2) * mon 0 6 0 8 +
    C ((4 : ℂ)) * mon 0 5 0 9 +
    C ((4 : ℂ) * r ^ 2 * Complex.I + (-4 : ℂ) * r ^ 2) * mon 0 4 1 9 +
    C ((4 : ℂ) * r ^ 2 * Complex.I) * mon 0 3 3 8 +
    C ((4 : ℂ)) * mon 0 3 1 10 +
    C ((-16 : ℂ) * Complex.I) * mon 0 2 3 9 +
    C ((4 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * mon 0 2 2 10 +
    C ((4 : ℂ) * r ^ 2 * Complex.I) * mon 0 1 4 9 +
    C ((-16 : ℂ) * Complex.I) * mon 0 0 4 10

def witness31 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I) * mon 3 2 3 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 3 2 2 1 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 3 1 2 2 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 3 1 1 3 +
    C ((1 : ℂ)) * mon 3 0 4 1 +
    C ((-1 : ℂ) * r ^ 2) * mon 3 0 3 2 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 3 0 0 5 +
    C ((1 : ℂ) * Complex.I + (1 : ℂ)) * mon 2 2 2 2 +
    C ((-1 : ℂ) * r ^ 2) * mon 2 2 1 3 +
    C ((-1 : ℂ) * r ^ 2) * mon 2 1 3 2 +
    C ((-2 : ℂ) * Complex.I) * mon 2 1 1 4 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 2 1 0 5 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 2 0 3 3 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 2 0 2 4 +
    C ((-2 : ℂ)) * mon 1 2 1 4 +
    C ((-2 : ℂ) * Complex.I) * mon 1 1 3 3 +
    C ((2 : ℂ) * Complex.I + (2 : ℂ)) * mon 1 1 0 6 +
    C ((-2 : ℂ) * Complex.I) * mon 1 0 2 5 +
    C ((-2 : ℂ)) * mon 0 2 3 3 +
    C ((-2 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 2 0 6 +
    C ((-2 : ℂ) * Complex.I) * mon 0 0 4 4 +
    C ((2 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 0 1 7

def witness32 (r : ℂ) : Poly :=
    C ((1 : ℂ)) * mon 3 9 2 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 3 9 1 1 +
    C ((-2 : ℂ) * r ^ 2 * Complex.I) * mon 3 8 0 3 +
    C ((8 : ℂ) * r ^ 2 * Complex.I + (-4 : ℂ) * r ^ 2) * mon 3 2 0 9 +
    C ((4 : ℂ) * r ^ 2 * Complex.I) * mon 3 1 2 8 +
    C ((-16 : ℂ) * Complex.I + (12 : ℂ)) * mon 3 1 0 10 +
    C ((-16 : ℂ) * Complex.I) * mon 3 0 2 9 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 2 9 1 2 +
    C ((-2 : ℂ) * r ^ 2 * Complex.I) * mon 2 9 0 3 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 2 8 2 2 +
    C ((-4 : ℂ) * r ^ 2) * mon 2 3 0 9 +
    C ((-2 : ℂ) * r ^ 2) * mon 2 2 2 8 +
    C ((8 : ℂ) * Complex.I + (12 : ℂ)) * mon 2 2 0 10 +
    C ((12 : ℂ)) * mon 2 1 2 9 +
    C ((-4 : ℂ) * Complex.I) * mon 1 9 0 4 +
    C ((8 : ℂ) * Complex.I + (-4 : ℂ)) * mon 1 3 0 10 +
    C ((8 : ℂ) * Complex.I) * mon 1 2 2 9 +
    C ((-2 : ℂ) * Complex.I) * mon 0 9 2 3 +
    C ((-4 : ℂ)) * mon 0 4 0 10 +
    C ((-4 : ℂ)) * mon 0 3 2 9

def witness33 (r : ℂ) : Poly :=
    C ((4 : ℂ) * Complex.I + (4 : ℂ)) * mon 3 4 1 0 +
    C ((2 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * mon 3 4 0 1 +
    C ((4 : ℂ) * r ^ 2 * Complex.I + (-4 : ℂ) * r ^ 2) * mon 3 3 2 0 +
    C ((-4 : ℂ) * Complex.I + (4 : ℂ)) * mon 3 3 0 2 +
    C ((6 : ℂ) * r ^ 2 * Complex.I + (2 : ℂ) * r ^ 2) * mon 3 2 1 2 +
    C ((4 : ℂ) * r ^ 2 * Complex.I + (4 : ℂ) * r ^ 2) * mon 3 1 3 1 +
    C ((-16 : ℂ) * Complex.I + (-16 : ℂ)) * mon 3 0 3 2 +
    C ((4 : ℂ) * Complex.I + (-4 : ℂ)) * mon 2 5 1 0 +
    C ((-2 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * mon 2 5 0 1 +
    C ((-2 : ℂ) * r ^ 2) * mon 2 4 2 0 +
    C ((4 : ℂ) * Complex.I + (4 : ℂ)) * mon 2 4 0 2 +
    C ((2 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * mon 2 3 1 2 +
    C ((2 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * mon 2 2 3 1 +
    C ((-12 : ℂ) * Complex.I + (12 : ℂ)) * mon 2 1 3 2 +
    C ((-4 : ℂ) * Complex.I + (-4 : ℂ)) * mon 1 6 1 0 +
    C ((4 : ℂ) * Complex.I + (-4 : ℂ)) * mon 1 5 0 2 +
    C ((8 : ℂ) * Complex.I + (8 : ℂ)) * mon 1 2 3 2 +
    C ((-4 : ℂ) * Complex.I) * mon 0 7 1 0 +
    C ((-4 : ℂ) * Complex.I + (-4 : ℂ)) * mon 0 6 0 2 +
    C ((4 : ℂ) * Complex.I + (-4 : ℂ)) * mon 0 3 3 2

theorem annihilator3 (r : ℂ) (hr : r ^ 3 = 2) :
    traceNumerator r * relation r 3 =
      X 0 ^ 4 * witness30 r +
      X 1 ^ 10 * witness31 r +
      X 2 ^ 4 * witness32 r +
      X 3 ^ 10 * witness33 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [traceNumerator, relation, b, h, mon,
    witness30, witness31, witness32, witness33,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one]
  ring_nf <;> (try simp only [hr', hi']) <;> ring

end CycleQ2SeedTrace

#print axioms CycleQ2SeedTrace.annihilator0
#print axioms CycleQ2SeedTrace.annihilator1
#print axioms CycleQ2SeedTrace.annihilator2
#print axioms CycleQ2SeedTrace.annihilator3
end
end


/- Component: seed_trace/SparseSeedTrace.lean -/
section
/-!
# Descent of the constructed sparse trace to the actual ideal quotient

The polynomial annihilator certificates prove the trace vanishes on every
multiple of every defining relation, not just on selected finite products.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

noncomputable section
namespace CycleQ2SeedTrace
open MvPolynomial

theorem truncationIdeal_eq_monomials : truncationIdeal =
    Ideal.span ((fun d : Exp => monomial d (1 : ℂ)) ''
      Set.range (fun i : Fin 4 => Finsupp.single i (cutoff i))) := by
  unfold truncationIdeal
  congr 1
  ext p
  simp only [Set.mem_range, Set.mem_image, X_pow_eq_monomial]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩

theorem top_coeff_zero_of_mem {p : Poly} (hp : p ∈ truncationIdeal) :
    coeff topExponent p = 0 := by
  rw [truncationIdeal_eq_monomials, mem_ideal_span_monomial_image] at hp
  by_contra hc
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hp topExponent (mem_support_iff.mpr hc)
  have h := Finsupp.single_le_iff.mp hi
  change topExponent i + 1 ≤ topExponent i at h
  omega

theorem fourTerm_mem_truncation (a b c d : Poly) :
    X 0 ^ 4 * a + X 1 ^ 10 * b + X 2 ^ 4 * c + X 3 ^ 10 * d ∈
      truncationIdeal := by
  have hg (i : Fin 4) : X i ^ cutoff i ∈ truncationIdeal :=
    Ideal.subset_span ⟨i, rfl⟩
  exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _
    (Ideal.mul_mem_right a _ (hg 0)) (Ideal.mul_mem_right b _ (hg 1)))
    (Ideal.mul_mem_right c _ (hg 2))) (Ideal.mul_mem_right d _ (hg 3))

theorem annihilator_generators_mem (r : ℂ) (hr : r ^ 3 = 2) (i : Fin 4) :
    traceNumerator r * relation r i ∈ truncationIdeal := by
  fin_cases i
  · change traceNumerator r * relation r 0 ∈ truncationIdeal
    rw [annihilator0 r hr]
    exact fourTerm_mem_truncation _ _ _ _
  · change traceNumerator r * relation r 1 ∈ truncationIdeal
    rw [annihilator1 r hr]
    exact fourTerm_mem_truncation _ _ _ _
  · change traceNumerator r * relation r 2 ∈ truncationIdeal
    rw [annihilator2 r hr]
    exact fourTerm_mem_truncation _ _ _ _
  · change traceNumerator r * relation r 3 ∈ truncationIdeal
    rw [annihilator3 r hr]
    exact fourTerm_mem_truncation _ _ _ _

theorem traceNumerator_mul_mem (r : ℂ) (hr : r ^ 3 = 2)
    {p : Poly} (hp : p ∈ reducedIdeal r) :
    traceNumerator r * p ∈ truncationIdeal := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨i, rfl⟩ := hp
      exact annihilator_generators_mem r hr i
  | zero => simp
  | add p q _ _ hp hq =>
      simpa only [mul_add] using Ideal.add_mem truncationIdeal hp hq
  | smul a p _ hp =>
      simpa only [smul_eq_mul, mul_left_comm] using
        Ideal.mul_mem_left truncationIdeal a hp

def traceLinear (r : ℂ) : Poly →ₗ[ℂ] ℂ :=
  ((1 / 12 : ℂ) • lcoeff ℂ topExponent).comp
    (LinearMap.mul ℂ Poly (traceNumerator r))

@[simp] theorem traceLinear_apply (r : ℂ) (p : Poly) :
    traceLinear r p = (1 / 12 : ℂ) * coeff topExponent (traceNumerator r * p) := rfl

theorem traceLinear_zero_of_mem (r : ℂ) (hr : r ^ 3 = 2)
    {p : Poly} (hp : p ∈ reducedIdeal r) : traceLinear r p = 0 := by
  rw [traceLinear_apply, top_coeff_zero_of_mem (traceNumerator_mul_mem r hr hp), mul_zero]

abbrev ReducedAlgebra (r : ℂ) := Poly ⧸ reducedIdeal r

def reducedQuotient (r : ℂ) : Poly →ₐ[ℂ] ReducedAlgebra r :=
  Ideal.Quotient.mkₐ ℂ (reducedIdeal r)

/-- The normalized coefficient functional genuinely descends to the quotient. -/
def reducedTrace (r : ℂ) (hr : r ^ 3 = 2) : ReducedAlgebra r →ₗ[ℂ] ℂ :=
  ((reducedIdeal r).restrictScalars ℂ).liftQ (traceLinear r) (by
    intro p hp
    exact traceLinear_zero_of_mem r hr hp)

@[simp] theorem reducedTrace_mk (r : ℂ) (hr : r ^ 3 = 2) (p : Poly) :
    reducedTrace r hr (reducedQuotient r p) = traceLinear r p := rfl

theorem mon_eq_monomial (a b c d : ℕ) :
    mon a b c d = monomial (exponent ![a, b, c, d]) 1 := by
  simp only [mon, X_pow_eq_monomial, monomial_mul, one_mul]
  apply congrArg (fun e : Exp => monomial e (1 : ℂ))
  ext i
  fin_cases i <;> simp [exponent, Finsupp.single_apply, Fin.ext_iff]

theorem mon_mul (a b c d e f g h : ℕ) :
    mon a b c d * mon e f g h = mon (a+e) (b+f) (c+g) (d+h) := by
  simp only [mon, pow_add]
  ring

theorem coeff_top_mon (a b c d : ℕ) :
    coeff topExponent (mon a b c d) =
      if a = 3 ∧ b = 9 ∧ c = 3 ∧ d = 9 then 1 else 0 := by
  rw [mon_eq_monomial, coeff_monomial]
  congr 1
  apply propext
  constructor
  · intro h
    exact ⟨congrArg (fun e : Exp => e 0) h, congrArg (fun e : Exp => e 1) h,
      congrArg (fun e : Exp => e 2) h, congrArg (fun e : Exp => e 3) h⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

theorem trace_normalized (r : ℂ) (hr : r ^ 3 = 2) :
    reducedTrace r hr (reducedQuotient r (mon 1 8 0 0)) = 1 := by
  rw [reducedTrace_mk, traceLinear_apply]
  simp only [traceNumerator, add_mul, mul_assoc, mon_mul, coeff_add, coeff_C_mul,
    coeff_top_mon]
  norm_num

end CycleQ2SeedTrace

#print axioms CycleQ2SeedTrace.traceLinear_zero_of_mem
#print axioms CycleQ2SeedTrace.reducedTrace
#print axioms CycleQ2SeedTrace.trace_normalized
end
end


/- Component: seed_trace/SparseSeedOriginal.lean -/
section
/-!
# The trace on the original five-variable seed algebra

This uses the actual five relations f1,g1,f2,g2,h from the sparse seed.
Substitution w=-x2^2 sends their ideal into the four-variable ideal on which
the coefficient functional has already been proved to vanish.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

noncomputable section
namespace CycleQ2SeedTrace
open MvPolynomial

abbrev WeightedPoly := MvPolynomial (Fin 5) ℂ

def originalB : WeightedPoly :=
  X 3 ^ 3 + X 2 ^ 3 + X 1 * X 2 * X 3 + X 0 * X 2 * X 3 + X 0 * X 1 ^ 2
def originalH : WeightedPoly := originalB - C Complex.I * (X 1 ^ 3 + X 3 ^ 3)
def originalK : WeightedPoly := originalB + C Complex.I * (X 1 ^ 3 + X 3 ^ 3)
def originalF1 (r : ℂ) : WeightedPoly := X 0 ^ 2 - C r * X 1 * X 3
def originalG1 (r : ℂ) : WeightedPoly :=
  X 0 ^ 4 + C r * X 0 ^ 2 * X 1 * X 3 + C (r ^ 2) * X 1 ^ 2 * X 3 ^ 2
def originalF2 : WeightedPoly := X 4 + X 2 ^ 2
def originalG2 : WeightedPoly := X 4 ^ 2 - X 4 * X 2 ^ 2 + X 2 ^ 4

def seedEquation : WeightedPoly :=
  X 0 ^ 6 + X 1 ^ 6 + X 2 ^ 6 + X 3 ^ 6 + X 4 ^ 3 + originalB ^ 2

theorem seedEquation_decomposition (r : ℂ) (hr : r ^ 3 = 2) :
    seedEquation = originalF1 r * originalG1 r + originalF2 * originalG2 +
      originalH * originalK := by
  have hr' : (C r : WeightedPoly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : WeightedPoly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  simp only [seedEquation, originalF1, originalG1, originalF2, originalG2,
    originalH, originalK, map_pow]
  ring_nf
  rw [hr', hi']
  ring

def originalRelations (r : ℂ) : Fin 5 → WeightedPoly :=
  ![originalF1 r, originalG1 r, originalF2, originalG2, originalH]

def originalIdeal (r : ℂ) : Ideal WeightedPoly := Ideal.span (Set.range (originalRelations r))

def substitute : WeightedPoly →ₐ[ℂ] Poly :=
  MvPolynomial.aeval ![X 0, X 1, X 2, X 3, -(X 2 ^ 2)]

theorem substitute_relations (r : ℂ) (i : Fin 5) :
    substitute (originalRelations r i) =
      ![relation r 0,
        relation r 0 * (X 0 ^ 2 + C (2 * r) * X 1 * X 3) +
          C (3 * r ^ 2) * relation r 1,
        0,
        3 * relation r 2,
        relation r 3] i := by
  fin_cases i <;>
    norm_num [substitute, originalRelations, originalF1, originalG1, originalF2,
      originalG2, originalH, originalB, relation, b, h, map_pow, map_mul, map_ofNat,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons] <;> ring

theorem substitute_relations_mem (r : ℂ) (i : Fin 5) :
    substitute (originalRelations r i) ∈ reducedIdeal r := by
  have hg (j : Fin 4) : relation r j ∈ reducedIdeal r := Ideal.subset_span ⟨j, rfl⟩
  rw [substitute_relations]
  fin_cases i
  · exact hg 0
  · exact Ideal.add_mem _
      (Ideal.mul_mem_right _ _ (hg 0)) (Ideal.mul_mem_left _ _ (hg 1))
  · exact Ideal.zero_mem _
  · exact Ideal.mul_mem_left _ _ (hg 2)
  · exact hg 3

theorem substitute_mem_reduced (r : ℂ) {p : WeightedPoly} (hp : p ∈ originalIdeal r) :
    substitute p ∈ reducedIdeal r := by
  have hle : originalIdeal r ≤ Ideal.comap substitute.toRingHom (reducedIdeal r) := by
    rw [originalIdeal, Ideal.span_le]
    rintro p ⟨i, rfl⟩
    exact substitute_relations_mem r i
  exact hle hp

def originalTraceLinear (r : ℂ) : WeightedPoly →ₗ[ℂ] ℂ :=
  (traceLinear r).comp substitute.toLinearMap

theorem originalTraceLinear_zero_of_mem (r : ℂ) (hr : r ^ 3 = 2)
    {p : WeightedPoly} (hp : p ∈ originalIdeal r) : originalTraceLinear r p = 0 :=
  traceLinear_zero_of_mem r hr (substitute_mem_reduced r hp)

abbrev SeedAlgebra (r : ℂ) := WeightedPoly ⧸ originalIdeal r

def seedQuotient (r : ℂ) : WeightedPoly →ₐ[ℂ] SeedAlgebra r :=
  Ideal.Quotient.mkₐ ℂ (originalIdeal r)

/-- The constructed functional on the actual original seed ideal quotient. -/
def seedTrace (r : ℂ) (hr : r ^ 3 = 2) : SeedAlgebra r →ₗ[ℂ] ℂ :=
  ((originalIdeal r).restrictScalars ℂ).liftQ (originalTraceLinear r) (by
    intro p hp
    exact originalTraceLinear_zero_of_mem r hr hp)

@[simp] theorem seedTrace_mk (r : ℂ) (hr : r ^ 3 = 2) (p : WeightedPoly) :
    seedTrace r hr (seedQuotient r p) = traceLinear r (substitute p) := rfl

theorem seedTrace_normalized (r : ℂ) (hr : r ^ 3 = 2) :
    seedTrace r hr (seedQuotient r (X 0 * X 1 ^ 8)) = 1 := by
  rw [seedTrace_mk]
  have heq : substitute (X 0 * X 1 ^ 8) = mon 1 8 0 0 := by
    simp [substitute, mon]
  rw [heq]
  exact trace_normalized r hr

end CycleQ2SeedTrace

#print axioms CycleQ2SeedTrace.seedEquation_decomposition
#print axioms CycleQ2SeedTrace.seedTrace
#print axioms CycleQ2SeedTrace.seedTrace_normalized
end
end


/- Component: seed_trace/SparseSeedEvaluation.lean -/
section
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace CycleQ2SeedTrace
open MvPolynomial

private theorem shiftTest0 (a b c d : ℕ) :
    (3 + a = 3 ∧ 9 + b = 9 ∧ 3 + c = 3 ∧ 0 + d = 9) ↔ (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 9) := by omega

private theorem shiftTest1 (a b c d : ℕ) :
    (3 + a = 3 ∧ 9 + b = 9 ∧ 2 + c = 3 ∧ 1 + d = 9) ↔ (a = 0 ∧ b = 0 ∧ c = 1 ∧ d = 8) := by omega

private theorem shiftTest2 (a b c d : ℕ) :
    (3 + a = 3 ∧ 8 + b = 9 ∧ 1 + c = 3 ∧ 3 + d = 9) ↔ (a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 6) := by omega

private theorem shiftTest3 (a b c d : ℕ) :
    (3 + a = 3 ∧ 4 + b = 9 ∧ 0 + c = 3 ∧ 8 + d = 9) ↔ (a = 0 ∧ b = 5 ∧ c = 3 ∧ d = 1) := by omega

private theorem shiftTest4 (a b c d : ℕ) :
    (3 + a = 3 ∧ 3 + b = 9 ∧ 0 + c = 3 ∧ 9 + d = 9) ↔ (a = 0 ∧ b = 6 ∧ c = 3 ∧ d = 0) := by omega

private theorem shiftTest5 (a b c d : ℕ) :
    (3 + a = 3 ∧ 2 + b = 9 ∧ 1 + c = 3 ∧ 9 + d = 9) ↔ (a = 0 ∧ b = 7 ∧ c = 2 ∧ d = 0) := by omega

private theorem shiftTest6 (a b c d : ℕ) :
    (3 + a = 3 ∧ 1 + b = 9 ∧ 3 + c = 3 ∧ 8 + d = 9) ↔ (a = 0 ∧ b = 8 ∧ c = 0 ∧ d = 1) := by omega

private theorem shiftTest7 (a b c d : ℕ) :
    (3 + a = 3 ∧ 0 + b = 9 ∧ 3 + c = 3 ∧ 9 + d = 9) ↔ (a = 0 ∧ b = 9 ∧ c = 0 ∧ d = 0) := by omega

private theorem shiftTest8 (a b c d : ℕ) :
    (2 + a = 3 ∧ 9 + b = 9 ∧ 2 + c = 3 ∧ 2 + d = 9) ↔ (a = 1 ∧ b = 0 ∧ c = 1 ∧ d = 7) := by omega

private theorem shiftTest9 (a b c d : ℕ) :
    (2 + a = 3 ∧ 9 + b = 9 ∧ 1 + c = 3 ∧ 3 + d = 9) ↔ (a = 1 ∧ b = 0 ∧ c = 2 ∧ d = 6) := by omega

private theorem shiftTest10 (a b c d : ℕ) :
    (2 + a = 3 ∧ 8 + b = 9 ∧ 3 + c = 3 ∧ 2 + d = 9) ↔ (a = 1 ∧ b = 1 ∧ c = 0 ∧ d = 7) := by omega

private theorem shiftTest11 (a b c d : ℕ) :
    (2 + a = 3 ∧ 8 + b = 9 ∧ 0 + c = 3 ∧ 5 + d = 9) ↔ (a = 1 ∧ b = 1 ∧ c = 3 ∧ d = 4) := by omega

private theorem shiftTest12 (a b c d : ℕ) :
    (2 + a = 3 ∧ 5 + b = 9 ∧ 0 + c = 3 ∧ 8 + d = 9) ↔ (a = 1 ∧ b = 4 ∧ c = 3 ∧ d = 1) := by omega

private theorem shiftTest13 (a b c d : ℕ) :
    (2 + a = 3 ∧ 4 + b = 9 ∧ 0 + c = 3 ∧ 9 + d = 9) ↔ (a = 1 ∧ b = 5 ∧ c = 3 ∧ d = 0) := by omega

private theorem shiftTest14 (a b c d : ℕ) :
    (2 + a = 3 ∧ 3 + b = 9 ∧ 1 + c = 3 ∧ 9 + d = 9) ↔ (a = 1 ∧ b = 6 ∧ c = 2 ∧ d = 0) := by omega

private theorem shiftTest15 (a b c d : ℕ) :
    (2 + a = 3 ∧ 2 + b = 9 ∧ 3 + c = 3 ∧ 8 + d = 9) ↔ (a = 1 ∧ b = 7 ∧ c = 0 ∧ d = 1) := by omega

private theorem shiftTest16 (a b c d : ℕ) :
    (2 + a = 3 ∧ 1 + b = 9 ∧ 3 + c = 3 ∧ 9 + d = 9) ↔ (a = 1 ∧ b = 8 ∧ c = 0 ∧ d = 0) := by omega

private theorem shiftTest17 (a b c d : ℕ) :
    (1 + a = 3 ∧ 9 + b = 9 ∧ 1 + c = 3 ∧ 4 + d = 9) ↔ (a = 2 ∧ b = 0 ∧ c = 2 ∧ d = 5) := by omega

private theorem shiftTest18 (a b c d : ℕ) :
    (1 + a = 3 ∧ 5 + b = 9 ∧ 0 + c = 3 ∧ 9 + d = 9) ↔ (a = 2 ∧ b = 4 ∧ c = 3 ∧ d = 0) := by omega

private theorem shiftTest19 (a b c d : ℕ) :
    (1 + a = 3 ∧ 2 + b = 9 ∧ 3 + c = 3 ∧ 9 + d = 9) ↔ (a = 2 ∧ b = 7 ∧ c = 0 ∧ d = 0) := by omega

private theorem shiftTest20 (a b c d : ℕ) :
    (0 + a = 3 ∧ 9 + b = 9 ∧ 3 + c = 3 ∧ 3 + d = 9) ↔ (a = 3 ∧ b = 0 ∧ c = 0 ∧ d = 6) := by omega

private theorem shiftTest21 (a b c d : ℕ) :
    (0 + a = 3 ∧ 9 + b = 9 ∧ 0 + c = 3 ∧ 6 + d = 9) ↔ (a = 3 ∧ b = 0 ∧ c = 3 ∧ d = 3) := by omega

private theorem shiftTest22 (a b c d : ℕ) :
    (0 + a = 3 ∧ 6 + b = 9 ∧ 0 + c = 3 ∧ 9 + d = 9) ↔ (a = 3 ∧ b = 3 ∧ c = 3 ∧ d = 0) := by omega

private theorem shiftTest23 (a b c d : ℕ) :
    (0 + a = 3 ∧ 3 + b = 9 ∧ 3 + c = 3 ∧ 9 + d = 9) ↔ (a = 3 ∧ b = 6 ∧ c = 0 ∧ d = 0) := by omega

def traceValue (r : ℂ) (a b c d : ℕ) : ℂ :=
  (1 / 12) * (((1 : ℂ)) * (if a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 9 then 1 else 0) +
    ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * (if a = 0 ∧ b = 0 ∧ c = 1 ∧ d = 8 then 1 else 0) +
    ((-1 : ℂ) * r ^ 2 * Complex.I) * (if a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 6 then 1 else 0) +
    ((-2 : ℂ) * r ^ 2) * (if a = 0 ∧ b = 5 ∧ c = 3 ∧ d = 1 then 1 else 0) +
    ((4 : ℂ)) * (if a = 0 ∧ b = 6 ∧ c = 3 ∧ d = 0 then 1 else 0) +
    ((4 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * (if a = 0 ∧ b = 7 ∧ c = 2 ∧ d = 0 then 1 else 0) +
    ((4 : ℂ) * r ^ 2 * Complex.I) * (if a = 0 ∧ b = 8 ∧ c = 0 ∧ d = 1 then 1 else 0) +
    ((-16 : ℂ) * Complex.I) * (if a = 0 ∧ b = 9 ∧ c = 0 ∧ d = 0 then 1 else 0) +
    ((1 : ℂ) * Complex.I + (-1 : ℂ)) * (if a = 1 ∧ b = 0 ∧ c = 1 ∧ d = 7 then 1 else 0) +
    ((-1 : ℂ) * r ^ 2 * Complex.I) * (if a = 1 ∧ b = 0 ∧ c = 2 ∧ d = 6 then 1 else 0) +
    ((-1 : ℂ) * r ^ 2 * Complex.I) * (if a = 1 ∧ b = 1 ∧ c = 0 ∧ d = 7 then 1 else 0) +
    ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * (if a = 1 ∧ b = 1 ∧ c = 3 ∧ d = 4 then 1 else 0) +
    ((-2 : ℂ) * r ^ 2 * Complex.I) * (if a = 1 ∧ b = 4 ∧ c = 3 ∧ d = 1 then 1 else 0) +
    ((4 : ℂ) * Complex.I) * (if a = 1 ∧ b = 5 ∧ c = 3 ∧ d = 0 then 1 else 0) +
    ((-2 : ℂ) * r ^ 2) * (if a = 1 ∧ b = 6 ∧ c = 2 ∧ d = 0 then 1 else 0) +
    ((-2 : ℂ) * r ^ 2) * (if a = 1 ∧ b = 7 ∧ c = 0 ∧ d = 1 then 1 else 0) +
    ((12 : ℂ)) * (if a = 1 ∧ b = 8 ∧ c = 0 ∧ d = 0 then 1 else 0) +
    ((-2 : ℂ) * Complex.I) * (if a = 2 ∧ b = 0 ∧ c = 2 ∧ d = 5 then 1 else 0) +
    ((-4 : ℂ)) * (if a = 2 ∧ b = 4 ∧ c = 3 ∧ d = 0 then 1 else 0) +
    ((8 : ℂ) * Complex.I) * (if a = 2 ∧ b = 7 ∧ c = 0 ∧ d = 0 then 1 else 0) +
    ((-2 : ℂ) * Complex.I) * (if a = 3 ∧ b = 0 ∧ c = 0 ∧ d = 6 then 1 else 0) +
    ((2 : ℂ) * Complex.I + (2 : ℂ)) * (if a = 3 ∧ b = 0 ∧ c = 3 ∧ d = 3 then 1 else 0) +
    ((-4 : ℂ) * Complex.I) * (if a = 3 ∧ b = 3 ∧ c = 3 ∧ d = 0 then 1 else 0) +
    ((-4 : ℂ)) * (if a = 3 ∧ b = 6 ∧ c = 0 ∧ d = 0 then 1 else 0))

theorem traceLinear_mon (r : ℂ) (a b c d : ℕ) :
    traceLinear r (mon a b c d) = traceValue r a b c d := by
  simp only [traceLinear_apply, traceNumerator, add_mul, mul_assoc, mon_mul,
    coeff_add, coeff_C_mul, coeff_top_mon, traceValue,
    shiftTest0, shiftTest1, shiftTest2, shiftTest3, shiftTest4, shiftTest5, shiftTest6, shiftTest7, shiftTest8, shiftTest9, shiftTest10, shiftTest11, shiftTest12, shiftTest13, shiftTest14, shiftTest15, shiftTest16, shiftTest17, shiftTest18, shiftTest19, shiftTest20, shiftTest21, shiftTest22, shiftTest23]

theorem traceLinear_C_mul (r z : ℂ) (p : Poly) :
    traceLinear r (C z * p) = z * traceLinear r p := by
  simpa only [smul_eq_C_mul, smul_eq_mul] using (traceLinear r).map_smul z p

end CycleQ2SeedTrace

#print axioms CycleQ2SeedTrace.traceLinear_mon
end
end


/- Component: seed_trace/SparseSeedMatrix.lean -/
section
/-!
# Binding the sparse seed matrix to the constructed quotient trace

All entries are evaluated from the coefficient functional whose descent to
the original quotient has been proved. The geometric interpretation of the
trace as a Noether--Lefschetz or Abel--Jacobi derivative remains separate.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

noncomputable section
namespace CycleQ2SeedTrace
open MvPolynomial

attribute [local irreducible] traceLinear

def columnPolynomial : Fin 9 → Poly := ![
  mon 0 0 0 3, mon 0 0 3 0, mon 0 1 1 1, mon 0 3 0 0,
  mon 1 0 1 1, mon 1 2 0 0, mon 2 1 0 0, mon 3 0 0 0, -mon 0 0 2 1]

def rowPolynomial : Fin 8 → Poly := ![
  k * mon 0 0 1 2, k * mon 0 1 2 0, k * mon 0 2 0 1,
  k * mon 1 0 2 0, k * mon 1 1 0 1, k * mon 2 0 0 1,
  -(k * mon 0 0 3 0), -mon 0 0 3 3]

def rowScale (r : ℂ) : Fin 8 → ℂ := ![3*r, 3*r, 3*r, 3*r, 3*r, 3, 3, 6]

def polynomialTraceMatrix (r : ℂ) : Matrix (Fin 8) (Fin 9) ℂ :=
  fun i j => rowScale r i * traceLinear r (rowPolynomial i * columnPolynomial j)

theorem k_eq_monomials : k = mon 0 0 0 3 + mon 0 0 3 0 + mon 0 1 1 1 +
    mon 1 0 1 1 + mon 1 2 0 0 + C Complex.I * (mon 0 3 0 0 + mon 0 0 0 3) := by
  simp [k, b, mon]

theorem mon_mul_C_assoc (a b c d : ℕ) (q : Poly) (z : ℂ) :
    mon a b c d * (C z * q) = C z * (mon a b c d * q) := by ring

theorem polynomialTraceMatrix_eq_seedMatrix (r : ℂ) (hr : r ^ 3 = 2) :
    polynomialTraceMatrix r = CycleQ2GeometricSeed.seedMatrix := by
  ext i j
  change rowScale r i * traceLinear r (rowPolynomial i * columnPolynomial j) =
    CycleQ2GeometricSeed.seedMatrix i j
  fin_cases i <;> fin_cases j
  all_goals
    simp only [rowScale, rowPolynomial, columnPolynomial, CycleQ2GeometricSeed.seedMatrix,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
    simp only [k_eq_monomials,
      add_mul, mul_add, neg_mul, mul_neg, mul_assoc, mon_mul_C_assoc, mon_mul,
      map_add, map_neg, traceLinear_C_mul, traceLinear_mon]
    norm_num [traceValue] <;> ring_nf <;> norm_num [hr, Complex.I_sq] <;> ring

end CycleQ2SeedTrace

#print axioms CycleQ2SeedTrace.polynomialTraceMatrix_eq_seedMatrix
end
end


/- Component: seed_trace/SparseSeedBinding.lean -/
section
/-!
# The checked matrix is an actual quotient-trace matrix

This final binding uses the original weighted coordinates, original cubic
columns, original seven cycle rows and original derivative row. No finite
trace value is supplied as an assumption.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

noncomputable section
namespace CycleQ2SeedTrace
open MvPolynomial

def originalColumn : Fin 9 → WeightedPoly := ![
  X 3 ^ 3, X 2 ^ 3, X 1 * X 2 * X 3, X 1 ^ 3,
  X 0 * X 2 * X 3, X 0 * X 1 ^ 2, X 0 ^ 2 * X 1, X 0 ^ 3, X 3 * X 4]

def originalRow : Fin 8 → WeightedPoly := ![
  originalK * (X 2 * X 3 ^ 2), originalK * (X 1 * X 2 ^ 2),
  originalK * (X 1 ^ 2 * X 3), originalK * (X 0 * X 2 ^ 2),
  originalK * (X 0 * X 1 * X 3), originalK * (X 0 ^ 2 * X 3),
  originalK * (X 2 * X 4), X 2 * X 3 ^ 3 * X 4]

theorem substitute_originalK : substitute originalK = k := by
  norm_num [substitute, originalK, originalB, k, b,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons]

theorem substitute_originalColumn (j : Fin 9) :
    substitute (originalColumn j) = columnPolynomial j := by
  fin_cases j <;>
    norm_num [substitute, originalColumn, columnPolynomial, mon,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons] <;> ring <;> simp

theorem substitute_originalRow (i : Fin 8) :
    substitute (originalRow i) = rowPolynomial i := by
  fin_cases i <;>
    norm_num [originalRow, rowPolynomial, map_mul, substitute, originalK, originalB, k, b,
      mon, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons] <;> ring <;> simp

/-- The exact displayed scaling, written without divisions for its computation. -/
theorem rowScale_eq_displayed (r : ℂ) (hr : r ^ 3 = 2) :
    rowScale r = ![6 / r ^ 2, 6 / r ^ 2, 6 / r ^ 2, 6 / r ^ 2,
      6 / r ^ 2, 3, 3, 6] := by
  have hr0 : r ≠ 0 := by
    intro h
    rw [h] at hr
    norm_num at hr
  have hs : 3 * r = 6 / r ^ 2 := by
    apply (eq_div_iff (pow_ne_zero 2 hr0)).mpr
    calc
      3 * r * r ^ 2 = 3 * r ^ 3 := by ring
      _ = 6 := by rw [hr]; norm_num
  funext i
  fin_cases i <;> simp [rowScale, hs]

def actualSeedTraceMatrix (r : ℂ) (hr : r ^ 3 = 2) : Matrix (Fin 8) (Fin 9) ℂ :=
  fun i j => rowScale r i * seedTrace r hr
    (seedQuotient r (originalRow i) * seedQuotient r (originalColumn j))

theorem actualSeedTraceMatrix_eq_polynomial (r : ℂ) (hr : r ^ 3 = 2) :
    actualSeedTraceMatrix r hr = polynomialTraceMatrix r := by
  ext i j
  change rowScale r i * seedTrace r hr
      (seedQuotient r (originalRow i) * seedQuotient r (originalColumn j)) = _
  rw [← map_mul, seedTrace_mk, map_mul, substitute_originalRow, substitute_originalColumn]
  rfl

/-- Every one of the 72 entries of the checked array is identified with its
trace product in the actual original seed algebra. -/
theorem actualSeedTraceMatrix_eq_seedMatrix (r : ℂ) (hr : r ^ 3 = 2) :
    actualSeedTraceMatrix r hr = CycleQ2GeometricSeed.seedMatrix := by
  rw [actualSeedTraceMatrix_eq_polynomial, polynomialTraceMatrix_eq_seedMatrix r hr]

theorem actualSeedTraceMatrix_right_inverse (r : ℂ) (hr : r ^ 3 = 2) :
    actualSeedTraceMatrix r hr * CycleQ2GeometricSeed.seedRightInverse = 1 := by
  rw [actualSeedTraceMatrix_eq_seedMatrix, CycleQ2GeometricSeed.seed_right_inverse]

theorem actualSeedTraceMatrix_tangent (r : ℂ) (hr : r ^ 3 = 2) :
    (actualSeedTraceMatrix r hr).mulVec CycleQ2GeometricSeed.seedTangent =
      CycleQ2GeometricSeed.tangentImage := by
  rw [actualSeedTraceMatrix_eq_seedMatrix, CycleQ2GeometricSeed.seed_tangent_image]

end CycleQ2SeedTrace

#print axioms CycleQ2SeedTrace.actualSeedTraceMatrix_eq_seedMatrix
#print axioms CycleQ2SeedTrace.actualSeedTraceMatrix_right_inverse
#print axioms CycleQ2SeedTrace.actualSeedTraceMatrix_tangent
end
end


/- Component: seed_trace/SparseSeedGrading.lean -/
section
set_option autoImplicit false
noncomputable section
namespace CycleQ2SeedTrace
open MvPolynomial

theorem mon_homogeneous (a b c d : ℕ) :
    (mon a b c d).IsHomogeneous (a + b + c + d) :=
  (((isHomogeneous_X_pow 0 a).mul (isHomogeneous_X_pow 1 b)).mul
    (isHomogeneous_X_pow 2 c)).mul (isHomogeneous_X_pow 3 d)

theorem traceNumerator_homogeneous (r : ℂ) :
    (traceNumerator r).IsHomogeneous 15 := by
  unfold traceNumerator
  repeat' apply IsHomogeneous.add
  all_goals exact (mon_homogeneous _ _ _ _).C_mul _

theorem topExponent_degree : topExponent.degree = 24 := by
  rw [Finsupp.degree_eq_sum]
  norm_num [topExponent, exponent_apply, Fin.sum_univ_succ]

/-- The constructed quotient functional is concentrated in degree nine. -/
theorem traceLinear_zero_other_degree (r : ℂ) {p : Poly} {d : ℕ}
    (hp : p.IsHomogeneous d) (hd : d ≠ 9) : traceLinear r p = 0 := by
  have hprod := (traceNumerator_homogeneous r).mul hp
  have hzero : coeff topExponent (traceNumerator r * p) = 0 :=
    hprod.coeff_eq_zero (by rw [topExponent_degree]; omega)
  rw [traceLinear_apply, hzero, mul_zero]

end CycleQ2SeedTrace

#print axioms CycleQ2SeedTrace.traceLinear_zero_other_degree
end
end


/- Component: seed_trace/SparseSeedDegreeNineReduction.lean -/
section
/-!
# Monomial reductions for the actual degree-nine seed component

These reductions use the concrete ideal relations. They will be combined
with finite polynomial certificates for the surviving normal monomials.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace CycleQ2SeedTrace
open MvPolynomial

def normalizationClass (r : ℂ) : ReducedAlgebra r := reducedQuotient r (mon 1 8 0 0)
def degreeNineLine (r : ℂ) : Submodule ℂ (ReducedAlgebra r) :=
  Submodule.span ℂ {normalizationClass r}
def degreeNinePiece (r : ℂ) : Submodule ℂ (ReducedAlgebra r) :=
  Submodule.map (reducedQuotient r).toLinearMap (homogeneousSubmodule (Fin 4) ℂ 9)

theorem normalizationClass_mem_line (r : ℂ) : normalizationClass r ∈ degreeNineLine r :=
  Submodule.subset_span (Set.mem_singleton _)

theorem normalizationClass_mem_piece (r : ℂ) : normalizationClass r ∈ degreeNinePiece r := by
  exact ⟨mon 1 8 0 0, mon_homogeneous 1 8 0 0, rfl⟩

theorem normalizationClass_ne_zero (r : ℂ) (hr : r ^ 3 = 2) :
    normalizationClass r ≠ 0 := by
  intro hz
  have h := trace_normalized r hr
  change reducedTrace r hr (normalizationClass r) = 1 at h
  rw [hz, map_zero] at h
  exact zero_ne_one h

theorem fourRelationSum_mem (r : ℂ) (a b c d : Poly) :
    relation r 0 * a + relation r 1 * b + relation r 2 * c + relation r 3 * d ∈
      reducedIdeal r := by
  have hg (i : Fin 4) : relation r i ∈ reducedIdeal r := Ideal.subset_span ⟨i, rfl⟩
  exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _
    (Ideal.mul_mem_right a _ (hg 0)) (Ideal.mul_mem_right b _ (hg 1)))
    (Ideal.mul_mem_right c _ (hg 2))) (Ideal.mul_mem_right d _ (hg 3))

theorem quotient_eq_smul_of_relation (r z : ℂ) (p q : Poly)
    (hp : p - C z * q ∈ reducedIdeal r) :
    reducedQuotient r p = z • reducedQuotient r q := by
  have hz : reducedQuotient r (p - C z * q) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp
  rw [map_sub, ← smul_eq_C_mul, map_smul, sub_eq_zero] at hz
  exact hz

theorem class_mem_line_of_scaled_relation (r scale z : ℂ) (p : Poly)
    (hscale : scale ≠ 0)
    (hp : C scale * p - C z * mon 1 8 0 0 ∈ reducedIdeal r) :
    reducedQuotient r p ∈ degreeNineLine r := by
  have heq := quotient_eq_smul_of_relation r z (C scale * p) (mon 1 8 0 0) hp
  have hsmul : scale • reducedQuotient r p = z • normalizationClass r := by
    simpa only [← smul_eq_C_mul, map_smul, normalizationClass] using heq
  apply ((degreeNineLine r).smul_mem_iff hscale).mp
  rw [hsmul]
  exact Submodule.smul_mem _ _ (normalizationClass_mem_line r)

theorem quotient_mon_add_two (r : ℂ) (a b c d : ℕ) :
    reducedQuotient r (mon (a + 2) b c d) =
      r • reducedQuotient r (mon a (b + 1) c (d + 1)) := by
  apply quotient_eq_smul_of_relation
  have hpoly : mon (a + 2) b c d - C r * mon a (b + 1) c (d + 1) =
      relation r 0 * mon a b c d := by
    simp only [mon, relation, Matrix.cons_val_zero, pow_add, pow_one]
    ring
  rw [hpoly]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨0, rfl⟩)

theorem quotient_mon_c_add_four_zero (r : ℂ) (a b c d : ℕ) :
    reducedQuotient r (mon a b (c + 4) d) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hpoly : mon a b (c + 4) d = relation r 2 * mon a b c d := by
    norm_num [mon, relation, pow_add, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  rw [hpoly]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨2, rfl⟩)

theorem quotient_mon_bd_add_two_zero (r : ℂ) (a b c d : ℕ) :
    reducedQuotient r (mon a (b + 2) c (d + 2)) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hpoly : mon a (b + 2) c (d + 2) = relation r 1 * mon a b c d := by
    norm_num [mon, relation, pow_add]
    ring
  rw [hpoly]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨1, rfl⟩)

end CycleQ2SeedTrace
end
end


/- Component: seed_trace/SparseSeedDegreeNineData.lean -/
section
/-!
# Concrete degree-nine relations in the actual sparse seed ideal

The31-by-32 homogeneous relation matrix is used only to discover polynomial
witnesses. The identities below are proved directly in the original reduced
polynomial ring, with no matrix rank or trace value assumed.

This still concerns the sparse seed; no smoothness conclusion is asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
namespace CycleQ2SeedTrace
open MvPolynomial

def degreeNineExponent : Fin 32 → Fin 4 → ℕ := ![
  ![0, 0, 0, 9],
  ![0, 0, 1, 8],
  ![0, 0, 2, 7],
  ![0, 0, 3, 6],
  ![0, 1, 0, 8],
  ![0, 1, 1, 7],
  ![0, 1, 2, 6],
  ![0, 1, 3, 5],
  ![0, 5, 3, 1],
  ![0, 6, 2, 1],
  ![0, 6, 3, 0],
  ![0, 7, 1, 1],
  ![0, 7, 2, 0],
  ![0, 8, 0, 1],
  ![0, 8, 1, 0],
  ![0, 9, 0, 0],
  ![1, 0, 0, 8],
  ![1, 0, 1, 7],
  ![1, 0, 2, 6],
  ![1, 0, 3, 5],
  ![1, 1, 0, 7],
  ![1, 1, 1, 6],
  ![1, 1, 2, 5],
  ![1, 1, 3, 4],
  ![1, 4, 3, 1],
  ![1, 5, 2, 1],
  ![1, 5, 3, 0],
  ![1, 6, 1, 1],
  ![1, 6, 2, 0],
  ![1, 7, 0, 1],
  ![1, 7, 1, 0],
  ![1, 8, 0, 0]]

def degreeNineMonomial (i : Fin 32) : Poly :=
  mon (degreeNineExponent i 0) (degreeNineExponent i 1)
    (degreeNineExponent i 2) (degreeNineExponent i 3)

def degreeNineWitness0_0 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I) * mon 0 7 0 0 +
    C ((-1 : ℂ) * r * Complex.I) * mon 0 6 0 1 +
    C ((1 : ℂ) * Complex.I + (1 : ℂ)) * mon 0 5 1 1 +
    C ((1 : ℂ)) * mon 0 4 3 0 +
    C ((-1 : ℂ) * r * Complex.I) * mon 0 4 1 2 +
    C ((-3 : ℂ) * r) * mon 0 3 3 1 +
    C ((-6 : ℂ) * Complex.I + (7 : ℂ)) * mon 0 3 2 2 +
    C ((1 : ℂ)) * mon 0 2 4 1 +
    C ((6 : ℂ) * Complex.I) * mon 0 2 1 4 +
    C ((-3 : ℂ) * r) * mon 0 1 4 2 +
    C ((-6 : ℂ) * Complex.I + (6 : ℂ)) * mon 0 1 3 3 +
    C ((6 : ℂ) * Complex.I) * mon 0 0 2 5

def degreeNineWitness0_1 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 1 3 1 0 +
    C ((1 : ℂ) * Complex.I + (1 : ℂ)) * mon 1 3 0 1 +
    C ((-6 : ℂ) * Complex.I + (-5 : ℂ)) * mon 1 2 2 0 +
    C ((-1 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 1 2 0 2 +
    C ((-3 : ℂ) * r * Complex.I + (3 : ℂ) * r) * mon 1 1 2 1 +
    C ((5 : ℂ) * Complex.I + (7 : ℂ)) * mon 1 1 1 2 +
    C ((-2 : ℂ) * r * Complex.I + (-3 : ℂ) * r) * mon 1 0 4 0 +
    C ((-1 : ℂ) * Complex.I + (7 : ℂ)) * mon 1 0 3 1 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 1 0 0 4 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 5 0 0 +
    C ((1 : ℂ) * r * Complex.I + (2 : ℂ) * r) * mon 0 4 1 0 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 3 1 1 +
    C ((-1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 0 3 0 2 +
    C ((-3 : ℂ) * r ^ 2) * mon 0 2 3 0 +
    C ((-9 : ℂ) * r * Complex.I + (4 : ℂ) * r) * mon 0 2 2 1 +
    C ((6 : ℂ)) * mon 0 2 1 2 +
    C ((-2 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 0 1 4 0 +
    C ((6 : ℂ)) * mon 0 1 3 1 +
    C ((6 : ℂ) * r * Complex.I) * mon 0 1 1 3 +
    C ((6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 0 1 0 4 +
    C ((-3 : ℂ) * r ^ 2) * mon 0 0 4 1 +
    C ((-11 : ℂ) * r * Complex.I + (7 : ℂ) * r) * mon 0 0 3 2 +
    C ((6 : ℂ) * Complex.I) * mon 0 0 2 3

def degreeNineWitness0_2 (r : ℂ) : Poly :=
    C ((2 : ℂ)) * mon 1 3 0 1 +
    C ((1 : ℂ)) * mon 1 2 2 0 +
    C ((-3 : ℂ) * r) * mon 1 1 2 1 +
    C ((-6 : ℂ) * Complex.I + (6 : ℂ)) * mon 1 1 1 2 +
    C ((12 : ℂ) * Complex.I) * mon 1 0 0 4 +
    C ((-2 : ℂ) * r * Complex.I) * mon 0 2 2 1 +
    C ((-3 : ℂ) * r * Complex.I + (3 : ℂ) * r) * mon 0 1 1 3 +
    C ((12 : ℂ) * Complex.I) * mon 0 1 0 4 +
    C ((6 : ℂ) * Complex.I) * mon 0 0 2 3

def degreeNineWitness0_3 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I) * mon 1 5 0 0 +
    C ((1 : ℂ) * r * Complex.I) * mon 1 4 0 1 +
    C ((-1 : ℂ)) * mon 1 3 1 1 +
    C ((-1 : ℂ)) * mon 1 2 3 0 +
    C ((3 : ℂ) * r) * mon 1 1 3 1 +
    C ((6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 1 1 2 2 +
    C ((-6 : ℂ) * Complex.I) * mon 1 0 1 4 +
    C ((-1 : ℂ) * r) * mon 0 5 0 1 +
    C ((2 : ℂ) * r * Complex.I) * mon 0 2 3 1 +
    C ((3 : ℂ) * r * Complex.I + (-3 : ℂ) * r) * mon 0 1 2 3 +
    C ((-6 : ℂ) * Complex.I) * mon 0 1 1 4 +
    C ((-6 : ℂ) * Complex.I) * mon 0 0 3 3 +
    C ((6 : ℂ) * Complex.I + (6 : ℂ)) * mon 0 0 0 6

theorem degreeNineCertificate0 (r : ℂ) (hr : r ^ 3 = 2) :
    (12 : Poly) * mon 0 0 0 9 - C ((1 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness0_0 r +
      relation r 1 * degreeNineWitness0_1 r +
      relation r 2 * degreeNineWitness0_2 r +
      relation r 3 * degreeNineWitness0_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness0_0, degreeNineWitness0_1,
    degreeNineWitness0_2, degreeNineWitness0_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness1_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 0 7 0 0 +
    C ((2 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 6 0 1 +
    C ((-2 : ℂ) * r ^ 2) * mon 0 5 1 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 0 4 3 0 +
    C ((2 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 4 1 2 +
    C ((-6 : ℂ) * Complex.I + (6 : ℂ)) * mon 0 3 3 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 0 3 2 2 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 0 2 4 1 +
    C ((6 : ℂ) * Complex.I) * mon 0 2 2 3 +
    C ((-6 : ℂ) * Complex.I + (6 : ℂ)) * mon 0 1 4 2 +
    C ((6 : ℂ) * Complex.I) * mon 0 0 3 4

def degreeNineWitness1_1 (r : ℂ) : Poly :=
    C ((4 : ℂ) * Complex.I) * mon 1 3 1 0 +
    C ((-2 : ℂ) * r ^ 2) * mon 1 3 0 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 2 2 0 +
    C ((4 : ℂ)) * mon 1 2 0 2 +
    C ((-3 : ℂ) * r * Complex.I + (3 : ℂ) * r) * mon 1 1 3 0 +
    C ((6 : ℂ) * Complex.I + (6 : ℂ)) * mon 1 1 2 1 +
    C ((2 : ℂ) * r ^ 2 * Complex.I) * mon 1 1 1 2 +
    C ((-2 : ℂ) * Complex.I + (10 : ℂ)) * mon 1 0 4 0 +
    C ((2 : ℂ) * r ^ 2 * Complex.I) * mon 1 0 3 1 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 1 0 1 3 +
    C ((2 : ℂ) * r * Complex.I + (2 : ℂ) * r) * mon 0 5 0 0 +
    C ((2 : ℂ) * Complex.I + (-6 : ℂ)) * mon 0 4 1 0 +
    C ((2 : ℂ) * r * Complex.I + (2 : ℂ) * r) * mon 0 3 1 1 +
    C ((4 : ℂ) * Complex.I) * mon 0 3 0 2 +
    C ((-9 : ℂ) * r * Complex.I + (3 : ℂ) * r) * mon 0 2 3 0 +
    C ((2 : ℂ) * Complex.I + (4 : ℂ)) * mon 0 2 2 1 +
    C ((6 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 1 4 0 +
    C ((6 : ℂ) * r * Complex.I) * mon 0 1 2 2 +
    C ((6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 0 1 1 3 +
    C ((-9 : ℂ) * r * Complex.I + (9 : ℂ) * r) * mon 0 0 4 1 +
    C ((6 : ℂ) * Complex.I + (8 : ℂ)) * mon 0 0 3 2

def degreeNineWitness1_2 (r : ℂ) : Poly :=
    C ((2 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * mon 1 3 0 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 2 2 0 +
    C ((-6 : ℂ) * Complex.I + (6 : ℂ)) * mon 1 1 2 1 +
    C ((-3 : ℂ) * r * Complex.I + (3 : ℂ) * r) * mon 1 1 0 3 +
    C ((6 : ℂ) * Complex.I) * mon 1 0 1 3 +
    C ((4 : ℂ) * Complex.I + (4 : ℂ)) * mon 0 2 2 1 +
    C ((-3 : ℂ) * r * Complex.I + (3 : ℂ) * r) * mon 0 1 2 2 +
    C ((6 : ℂ) * Complex.I) * mon 0 1 1 3 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 0 0 0 5

def degreeNineWitness1_3 (r : ℂ) : Poly :=
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 1 5 0 0 +
    C ((-2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 4 0 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 1 3 1 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 1 2 3 0 +
    C ((6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 1 1 3 1 +
    C ((-6 : ℂ) * Complex.I) * mon 1 0 2 3 +
    C ((-2 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 5 0 1 +
    C ((-4 : ℂ) * Complex.I + (-4 : ℂ)) * mon 0 2 3 1 +
    C ((3 : ℂ) * r * Complex.I + (-3 : ℂ) * r) * mon 0 1 3 2 +
    C ((-6 : ℂ) * Complex.I) * mon 0 1 2 3 +
    C ((6 : ℂ) * Complex.I + (6 : ℂ)) * mon 0 0 1 5

theorem degreeNineCertificate1 (r : ℂ) (hr : r ^ 3 = 2) :
    (12 : Poly) * mon 0 0 1 8 - C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness1_0 r +
      relation r 1 * degreeNineWitness1_1 r +
      relation r 2 * degreeNineWitness1_2 r +
      relation r 3 * degreeNineWitness1_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness1_0, degreeNineWitness1_1,
    degreeNineWitness1_2, degreeNineWitness1_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness2_0 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I) * mon 0 2 3 2 +
    C ((1 : ℂ) * Complex.I) * mon 0 0 4 3

def degreeNineWitness2_1 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I + (1 : ℂ)) * mon 1 1 3 0 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 0 2 2 +
    C ((1 : ℂ)) * mon 0 2 3 0 +
    C ((1 : ℂ) * r * Complex.I) * mon 0 1 3 1 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 1 2 2 +
    C ((1 : ℂ) * Complex.I) * mon 0 0 4 1

def degreeNineWitness2_2 (r : ℂ) : Poly :=
    C ((2 : ℂ) * Complex.I) * mon 1 1 0 3 +
    C ((1 : ℂ) * Complex.I) * mon 1 0 2 2 +
    C ((1 : ℂ) * Complex.I) * mon 0 1 2 2 +
    C ((1 : ℂ) * r * Complex.I) * mon 0 1 0 4 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 0 1 4

def degreeNineWitness2_3 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I) * mon 1 0 3 2 +
    C ((-1 : ℂ) * Complex.I) * mon 0 1 3 2 +
    C ((1 : ℂ) * Complex.I + (1 : ℂ)) * mon 0 0 2 4

theorem degreeNineCertificate2 (r : ℂ) (hr : r ^ 3 = 2) :
    (2 : Poly) * mon 0 0 2 7 - C ((0 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness2_0 r +
      relation r 1 * degreeNineWitness2_1 r +
      relation r 2 * degreeNineWitness2_2 r +
      relation r 3 * degreeNineWitness2_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness2_0, degreeNineWitness2_1,
    degreeNineWitness2_2, degreeNineWitness2_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness3_0 (r : ℂ) : Poly :=
    0

def degreeNineWitness3_1 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 0 3 1 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 1 3 1

def degreeNineWitness3_2 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 0 0 4 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 1 0 4 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 0 2 3

def degreeNineWitness3_3 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I + (1 : ℂ)) * mon 0 0 3 3

theorem degreeNineCertificate3 (r : ℂ) (hr : r ^ 3 = 2) :
    (2 : Poly) * mon 0 0 3 6 - C ((0 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness3_0 r +
      relation r 1 * degreeNineWitness3_1 r +
      relation r 2 * degreeNineWitness3_2 r +
      relation r 3 * degreeNineWitness3_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness3_0, degreeNineWitness3_1,
    degreeNineWitness3_2, degreeNineWitness3_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness4_0 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I) * mon 0 3 1 3 +
    C ((1 : ℂ) * Complex.I) * mon 0 1 2 4

def degreeNineWitness4_1 (r : ℂ) : Poly :=
    C ((1 : ℂ)) * mon 1 2 1 1 +
    C ((1 : ℂ) * Complex.I) * mon 1 1 3 0 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 1 0 3 +
    C ((1 : ℂ) * Complex.I) * mon 1 0 2 2 +
    C ((1 : ℂ)) * mon 0 2 3 0 +
    C ((1 : ℂ) * r * Complex.I) * mon 0 2 1 2 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 2 0 3 +
    C ((1 : ℂ) * Complex.I) * mon 0 0 4 1 +
    C ((1 : ℂ) * r * Complex.I) * mon 0 0 2 3 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 0 1 4

def degreeNineWitness4_2 (r : ℂ) : Poly :=
    C ((2 : ℂ) * Complex.I) * mon 1 1 0 3 +
    C ((1 : ℂ) * Complex.I) * mon 0 1 2 2

def degreeNineWitness4_3 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I) * mon 1 1 1 3 +
    C ((-1 : ℂ) * Complex.I) * mon 0 1 3 2 +
    C ((1 : ℂ) * Complex.I + (1 : ℂ)) * mon 0 1 0 5

theorem degreeNineCertificate4 (r : ℂ) (hr : r ^ 3 = 2) :
    (2 : Poly) * mon 0 1 0 8 - C ((0 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness4_0 r +
      relation r 1 * degreeNineWitness4_1 r +
      relation r 2 * degreeNineWitness4_2 r +
      relation r 3 * degreeNineWitness4_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness4_0, degreeNineWitness4_1,
    degreeNineWitness4_2, degreeNineWitness4_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness5_0 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I) * mon 0 3 2 2 +
    C ((1 : ℂ) * Complex.I) * mon 0 1 3 3

def degreeNineWitness5_1 (r : ℂ) : Poly :=
    C ((1 : ℂ)) * mon 1 2 2 0 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 1 1 2 +
    C ((1 : ℂ) * Complex.I) * mon 1 0 3 1 +
    C ((1 : ℂ) * r * Complex.I) * mon 0 2 2 1 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 2 1 2 +
    C ((1 : ℂ) * r * Complex.I) * mon 0 0 3 2 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 0 2 3

def degreeNineWitness5_2 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I) * mon 1 1 1 2 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 1 0 4

def degreeNineWitness5_3 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I) * mon 1 1 2 2 +
    C ((1 : ℂ) * Complex.I + (1 : ℂ)) * mon 0 1 1 4

theorem degreeNineCertificate5 (r : ℂ) (hr : r ^ 3 = 2) :
    (2 : Poly) * mon 0 1 1 7 - C ((0 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness5_0 r +
      relation r 1 * degreeNineWitness5_1 r +
      relation r 2 * degreeNineWitness5_2 r +
      relation r 3 * degreeNineWitness5_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness5_0, degreeNineWitness5_1,
    degreeNineWitness5_2, degreeNineWitness5_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness6_0 (r : ℂ) : Poly :=
    C ((1 : ℂ) * r ^ 2) * mon 0 7 0 0 +
    C ((-2 : ℂ)) * mon 0 6 0 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 0 5 1 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 4 3 0 +
    C ((-2 : ℂ)) * mon 0 4 1 2 +
    C ((6 : ℂ) * Complex.I) * mon 0 3 3 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 3 2 2 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 2 4 1 +
    C ((6 : ℂ) * Complex.I) * mon 0 1 4 2

def degreeNineWitness6_1 (r : ℂ) : Poly :=
    C ((-2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 3 1 0 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 1 3 0 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 1 2 2 0 +
    C ((2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 2 0 2 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 1 1 2 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 1 1 2 +
    C ((6 : ℂ) * Complex.I + (-4 : ℂ)) * mon 1 0 4 0 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 0 3 1 +
    C ((-2 : ℂ) * r) * mon 0 5 0 0 +
    C ((-4 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 4 1 0 +
    C ((-2 : ℂ) * r) * mon 0 3 1 1 +
    C ((-2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 3 0 2 +
    C ((6 : ℂ) * r * Complex.I) * mon 0 2 3 0 +
    C ((4 : ℂ) * Complex.I + (-6 : ℂ)) * mon 0 2 2 1 +
    C ((-2 : ℂ) * Complex.I + (-4 : ℂ)) * mon 0 1 4 0 +
    C ((6 : ℂ) * r * Complex.I) * mon 0 0 4 1 +
    C ((-2 : ℂ) * Complex.I + (-10 : ℂ)) * mon 0 0 3 2

def degreeNineWitness6_2 (r : ℂ) : Poly :=
    C ((-2 : ℂ) * r ^ 2 * Complex.I) * mon 1 3 0 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 1 2 2 0 +
    C ((6 : ℂ) * Complex.I) * mon 1 1 2 1 +
    C ((-4 : ℂ)) * mon 0 2 2 1 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 0 1 1 3

def degreeNineWitness6_3 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r ^ 2) * mon 1 5 0 0 +
    C ((2 : ℂ)) * mon 1 4 0 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 1 3 1 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 1 2 3 0 +
    C ((-6 : ℂ) * Complex.I) * mon 1 1 3 1 +
    C ((2 : ℂ) * Complex.I) * mon 0 5 0 1 +
    C ((4 : ℂ)) * mon 0 2 3 1 +
    C ((6 : ℂ) * Complex.I + (6 : ℂ)) * mon 0 1 2 3

theorem degreeNineCertificate6 (r : ℂ) (hr : r ^ 3 = 2) :
    (12 : Poly) * mon 0 1 2 6 - C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness6_0 r +
      relation r 1 * degreeNineWitness6_1 r +
      relation r 2 * degreeNineWitness6_2 r +
      relation r 3 * degreeNineWitness6_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness6_0, degreeNineWitness6_1,
    degreeNineWitness6_2, degreeNineWitness6_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness7_0 (r : ℂ) : Poly :=
    0

def degreeNineWitness7_1 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 1 3 0 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 2 3 0 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 0 4 1

def degreeNineWitness7_2 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 1 0 3 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 1 2 2

def degreeNineWitness7_3 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I + (1 : ℂ)) * mon 0 1 3 2

theorem degreeNineCertificate7 (r : ℂ) (hr : r ^ 3 = 2) :
    (2 : Poly) * mon 0 1 3 5 - C ((0 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness7_0 r +
      relation r 1 * degreeNineWitness7_1 r +
      relation r 2 * degreeNineWitness7_2 r +
      relation r 3 * degreeNineWitness7_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness7_0, degreeNineWitness7_1,
    degreeNineWitness7_2, degreeNineWitness7_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness8_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 7 0 0 +
    C ((2 : ℂ) * Complex.I) * mon 0 6 0 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 0 5 1 1 +
    C ((-1 : ℂ) * r ^ 2) * mon 0 4 3 0 +
    C ((2 : ℂ) * Complex.I) * mon 0 4 1 2 +
    C ((-1 : ℂ) * r ^ 2) * mon 0 3 2 2 +
    C ((-1 : ℂ) * r ^ 2) * mon 0 2 4 1

def degreeNineWitness8_1 (r : ℂ) : Poly :=
    C ((2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 3 1 0 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 3 0 1 +
    C ((-1 : ℂ) * r ^ 2) * mon 1 2 2 0 +
    C ((2 : ℂ) * Complex.I + (2 : ℂ)) * mon 1 2 0 2 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 1 1 2 +
    C ((-2 : ℂ) * Complex.I) * mon 1 0 4 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 0 3 1 +
    C ((2 : ℂ) * r * Complex.I) * mon 0 5 0 0 +
    C ((-2 : ℂ) * Complex.I + (-4 : ℂ)) * mon 0 4 1 0 +
    C ((2 : ℂ) * r * Complex.I) * mon 0 3 1 1 +
    C ((2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 3 0 2 +
    C ((-2 : ℂ)) * mon 0 2 2 1 +
    C ((-2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 1 4 0 +
    C ((-2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 0 3 2

def degreeNineWitness8_2 (r : ℂ) : Poly :=
    C ((-2 : ℂ) * r ^ 2) * mon 1 3 0 1 +
    C ((-1 : ℂ) * r ^ 2) * mon 1 2 2 0 +
    C ((-2 : ℂ) * Complex.I) * mon 0 2 2 1

def degreeNineWitness8_3 (r : ℂ) : Poly :=
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 1 5 0 0 +
    C ((-2 : ℂ) * Complex.I) * mon 1 4 0 1 +
    C ((1 : ℂ) * r ^ 2) * mon 1 3 1 1 +
    C ((1 : ℂ) * r ^ 2) * mon 1 2 3 0 +
    C ((2 : ℂ)) * mon 0 5 0 1 +
    C ((2 : ℂ) * Complex.I) * mon 0 2 3 1

theorem degreeNineCertificate8 (r : ℂ) (hr : r ^ 3 = 2) :
    (6 : Poly) * mon 0 5 3 1 - C ((-1 : ℂ) * r ^ 2) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness8_0 r +
      relation r 1 * degreeNineWitness8_1 r +
      relation r 2 * degreeNineWitness8_2 r +
      relation r 3 * degreeNineWitness8_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness8_0, degreeNineWitness8_1,
    degreeNineWitness8_2, degreeNineWitness8_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness9_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ)) * mon 0 4 2 1 +
    C ((-1 : ℂ)) * mon 0 2 3 2

def degreeNineWitness9_1 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 1 3 0 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 0 2 2 +
    C ((-1 : ℂ) * r) * mon 0 3 2 0 +
    C ((-1 : ℂ) * Complex.I) * mon 0 2 3 0 +
    C ((-1 : ℂ) * r) * mon 0 1 3 1 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 1 2 2

def degreeNineWitness9_2 (r : ℂ) : Poly :=
    C ((-1 : ℂ)) * mon 1 2 1 1 +
    C ((-1 : ℂ) * Complex.I) * mon 0 3 1 1

def degreeNineWitness9_3 (r : ℂ) : Poly :=
    C ((1 : ℂ)) * mon 1 2 2 1 +
    C ((1 : ℂ) * Complex.I) * mon 0 3 2 1

theorem degreeNineCertificate9 (r : ℂ) (hr : r ^ 3 = 2) :
    (1 : Poly) * mon 0 6 2 1 - C ((0 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness9_0 r +
      relation r 1 * degreeNineWitness9_1 r +
      relation r 2 * degreeNineWitness9_2 r +
      relation r 3 * degreeNineWitness9_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness9_0, degreeNineWitness9_1,
    degreeNineWitness9_2, degreeNineWitness9_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness10_0 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I) * mon 0 7 0 0 +
    C ((-1 : ℂ) * r * Complex.I) * mon 0 6 0 1 +
    C ((1 : ℂ) * Complex.I + (1 : ℂ)) * mon 0 5 1 1 +
    C ((-2 : ℂ)) * mon 0 4 3 0 +
    C ((-1 : ℂ) * r * Complex.I) * mon 0 4 1 2 +
    C ((1 : ℂ)) * mon 0 3 2 2 +
    C ((-2 : ℂ)) * mon 0 2 4 1

def degreeNineWitness10_1 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 1 3 1 0 +
    C ((1 : ℂ) * Complex.I + (1 : ℂ)) * mon 1 3 0 1 +
    C ((1 : ℂ)) * mon 1 2 2 0 +
    C ((-1 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 1 2 0 2 +
    C ((-1 : ℂ) * Complex.I + (1 : ℂ)) * mon 1 1 1 2 +
    C ((1 : ℂ) * r * Complex.I) * mon 1 0 4 0 +
    C ((2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 0 3 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 5 0 0 +
    C ((1 : ℂ) * r * Complex.I + (2 : ℂ) * r) * mon 0 4 1 0 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 3 1 1 +
    C ((-1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 0 3 0 2 +
    C ((1 : ℂ) * r) * mon 0 2 2 1 +
    C ((1 : ℂ) * r * Complex.I + (-2 : ℂ) * r) * mon 0 1 4 0 +
    C ((-3 : ℂ) * Complex.I + (-3 : ℂ)) * mon 0 1 3 1 +
    C ((1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 0 0 3 2

def degreeNineWitness10_2 (r : ℂ) : Poly :=
    C ((-3 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 3 0 1 +
    C ((-2 : ℂ)) * mon 1 2 2 0 +
    C ((-3 : ℂ) * Complex.I) * mon 0 4 0 1 +
    C ((-3 : ℂ) * Complex.I) * mon 0 3 2 0 +
    C ((1 : ℂ) * r * Complex.I) * mon 0 2 2 1

def degreeNineWitness10_3 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I) * mon 1 5 0 0 +
    C ((1 : ℂ) * r * Complex.I) * mon 1 4 0 1 +
    C ((-1 : ℂ)) * mon 1 3 1 1 +
    C ((2 : ℂ)) * mon 1 2 3 0 +
    C ((-1 : ℂ) * r) * mon 0 5 0 1 +
    C ((3 : ℂ) * Complex.I) * mon 0 3 3 0 +
    C ((-1 : ℂ) * r * Complex.I) * mon 0 2 3 1

theorem degreeNineCertificate10 (r : ℂ) (hr : r ^ 3 = 2) :
    (3 : Poly) * mon 0 6 3 0 - C ((1 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness10_0 r +
      relation r 1 * degreeNineWitness10_1 r +
      relation r 2 * degreeNineWitness10_2 r +
      relation r 3 * degreeNineWitness10_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness10_0, degreeNineWitness10_1,
    degreeNineWitness10_2, degreeNineWitness10_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness11_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ)) * mon 0 5 1 1 +
    C ((-1 : ℂ)) * mon 0 3 2 2

def degreeNineWitness11_1 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 2 2 0 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 1 1 2 +
    C ((-1 : ℂ) * r) * mon 0 4 1 0 +
    C ((-1 : ℂ) * Complex.I) * mon 0 3 2 0 +
    C ((-1 : ℂ) * r) * mon 0 2 2 1 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 2 1 2

def degreeNineWitness11_2 (r : ℂ) : Poly :=
    C ((-1 : ℂ)) * mon 1 3 0 1 +
    C ((-1 : ℂ) * Complex.I) * mon 0 4 0 1

def degreeNineWitness11_3 (r : ℂ) : Poly :=
    C ((1 : ℂ)) * mon 1 3 1 1 +
    C ((1 : ℂ) * Complex.I) * mon 0 4 1 1

theorem degreeNineCertificate11 (r : ℂ) (hr : r ^ 3 = 2) :
    (1 : Poly) * mon 0 7 1 1 - C ((0 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness11_0 r +
      relation r 1 * degreeNineWitness11_1 r +
      relation r 2 * degreeNineWitness11_2 r +
      relation r 3 * degreeNineWitness11_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness11_0, degreeNineWitness11_1,
    degreeNineWitness11_2, degreeNineWitness11_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness12_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * mon 0 7 0 0 +
    C ((2 : ℂ) * Complex.I + (4 : ℂ)) * mon 0 6 0 1 +
    C ((-6 : ℂ)) * mon 0 5 2 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-3 : ℂ) * r ^ 2) * mon 0 5 1 1 +
    C ((2 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 0 4 3 0 +
    C ((6 : ℂ) * r) * mon 0 4 2 1 +
    C ((2 : ℂ) * Complex.I + (4 : ℂ)) * mon 0 4 1 2 +
    C ((-6 : ℂ)) * mon 0 3 3 1 +
    C ((2 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 0 3 2 2 +
    C ((2 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 0 2 4 1 +
    C ((6 : ℂ) * r) * mon 0 2 3 2

def degreeNineWitness12_1 (r : ℂ) : Poly :=
    C ((6 : ℂ) * Complex.I + (2 : ℂ)) * mon 1 3 1 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-3 : ℂ) * r ^ 2) * mon 1 3 0 1 +
    C ((2 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 2 2 0 +
    C ((-2 : ℂ) * Complex.I + (6 : ℂ)) * mon 1 2 0 2 +
    C ((6 : ℂ) * r * Complex.I + (6 : ℂ) * r) * mon 1 1 3 0 +
    C ((6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 1 1 2 1 +
    C ((3 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 1 1 1 2 +
    C ((4 : ℂ) * Complex.I + (2 : ℂ)) * mon 1 0 4 0 +
    C ((3 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 1 0 3 1 +
    C ((-6 : ℂ) * r * Complex.I + (6 : ℂ) * r) * mon 1 0 2 2 +
    C ((2 : ℂ) * r * Complex.I + (4 : ℂ) * r) * mon 0 5 0 0 +
    C ((6 : ℂ) * Complex.I + (-8 : ℂ)) * mon 0 4 1 0 +
    C ((6 : ℂ) * r ^ 2) * mon 0 3 2 0 +
    C ((2 : ℂ) * r * Complex.I + (4 : ℂ) * r) * mon 0 3 1 1 +
    C ((6 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 3 0 2 +
    C ((6 : ℂ) * r * Complex.I + (-6 : ℂ) * r) * mon 0 2 3 0 +
    C ((-2 : ℂ) * Complex.I + (-8 : ℂ)) * mon 0 2 2 1 +
    C ((8 : ℂ) * Complex.I) * mon 0 1 4 0 +
    C ((6 : ℂ) * r ^ 2) * mon 0 1 3 1 +
    C ((6 : ℂ) * r * Complex.I + (6 : ℂ) * r) * mon 0 1 2 2 +
    C ((2 : ℂ) * Complex.I + (6 : ℂ)) * mon 0 0 3 2

def degreeNineWitness12_2 (r : ℂ) : Poly :=
    C ((-6 : ℂ)) * mon 1 3 1 0 +
    C ((4 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * mon 1 3 0 1 +
    C ((2 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 2 2 0 +
    C ((6 : ℂ) * r) * mon 1 2 1 1 +
    C ((-6 : ℂ) * Complex.I) * mon 0 4 1 0 +
    C ((6 : ℂ) * r * Complex.I) * mon 0 3 1 1 +
    C ((4 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 2 2 1

def degreeNineWitness12_3 (r : ℂ) : Poly :=
    C ((1 : ℂ) * r ^ 2 * Complex.I + (2 : ℂ) * r ^ 2) * mon 1 5 0 0 +
    C ((-2 : ℂ) * Complex.I + (-4 : ℂ)) * mon 1 4 0 1 +
    C ((6 : ℂ)) * mon 1 3 2 0 +
    C ((-2 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 1 3 1 1 +
    C ((-2 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 1 2 3 0 +
    C ((-6 : ℂ) * r) * mon 1 2 2 1 +
    C ((-4 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 5 0 1 +
    C ((6 : ℂ) * Complex.I) * mon 0 4 2 0 +
    C ((-6 : ℂ) * r * Complex.I) * mon 0 3 2 1 +
    C ((-4 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 2 3 1

theorem degreeNineCertificate12 (r : ℂ) (hr : r ^ 3 = 2) :
    (6 : Poly) * mon 0 7 2 0 - C ((2 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness12_0 r +
      relation r 1 * degreeNineWitness12_1 r +
      relation r 2 * degreeNineWitness12_2 r +
      relation r 3 * degreeNineWitness12_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness12_0, degreeNineWitness12_1,
    degreeNineWitness12_2, degreeNineWitness12_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness13_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r ^ 2) * mon 0 7 0 0 +
    C ((-1 : ℂ)) * mon 0 6 0 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 0 5 1 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 0 4 3 0 +
    C ((-1 : ℂ)) * mon 0 4 1 2 +
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 0 3 2 2 +
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 0 2 4 1

def degreeNineWitness13_1 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 3 1 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 3 0 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 1 2 2 0 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 2 0 2 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 1 1 1 2 +
    C ((1 : ℂ)) * mon 1 0 4 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 1 0 3 1 +
    C ((-1 : ℂ) * r) * mon 0 5 0 0 +
    C ((1 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 4 1 0 +
    C ((-1 : ℂ) * r) * mon 0 3 1 1 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 3 0 2 +
    C ((2 : ℂ) * Complex.I) * mon 0 2 2 1 +
    C ((2 : ℂ) * Complex.I + (1 : ℂ)) * mon 0 1 4 0 +
    C ((-1 : ℂ) * Complex.I + (1 : ℂ)) * mon 0 0 3 2

def degreeNineWitness13_2 (r : ℂ) : Poly :=
    C ((2 : ℂ) * r ^ 2 * Complex.I) * mon 1 3 0 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 1 2 2 0 +
    C ((1 : ℂ)) * mon 0 2 2 1

def degreeNineWitness13_3 (r : ℂ) : Poly :=
    C ((1 : ℂ) * r ^ 2) * mon 1 5 0 0 +
    C ((1 : ℂ)) * mon 1 4 0 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 1 3 1 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 1 2 3 0 +
    C ((1 : ℂ) * Complex.I) * mon 0 5 0 1 +
    C ((-1 : ℂ)) * mon 0 2 3 1

theorem degreeNineCertificate13 (r : ℂ) (hr : r ^ 3 = 2) :
    (3 : Poly) * mon 0 8 0 1 - C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness13_0 r +
      relation r 1 * degreeNineWitness13_1 r +
      relation r 2 * degreeNineWitness13_2 r +
      relation r 3 * degreeNineWitness13_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness13_0, degreeNineWitness13_1,
    degreeNineWitness13_2, degreeNineWitness13_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness14_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ)) * mon 0 6 1 0 +
    C ((1 : ℂ) * r) * mon 0 5 1 1 +
    C ((2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 4 2 1 +
    C ((1 : ℂ) * r) * mon 0 3 2 2 +
    C ((2 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 2 3 2

def degreeNineWitness14_1 (r : ℂ) : Poly :=
    C ((1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 1 2 2 0 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 2 1 1 +
    C ((2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 1 3 0 +
    C ((-1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 1 1 1 2 +
    C ((3 : ℂ) * Complex.I + (1 : ℂ)) * mon 1 0 2 2 +
    C ((1 : ℂ) * r ^ 2) * mon 0 4 1 0 +
    C ((3 : ℂ) * r * Complex.I + (-2 : ℂ) * r) * mon 0 3 2 0 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 3 1 1 +
    C ((-1 : ℂ)) * mon 0 2 3 0 +
    C ((1 : ℂ) * r ^ 2) * mon 0 2 2 1 +
    C ((1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 0 2 1 2 +
    C ((2 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 0 1 3 1 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 1 2 2

def degreeNineWitness14_2 (r : ℂ) : Poly :=
    C ((-1 : ℂ)) * mon 1 4 0 0 +
    C ((1 : ℂ) * r) * mon 1 3 0 1 +
    C ((2 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 2 1 1 +
    C ((-1 : ℂ) * Complex.I) * mon 0 5 0 0 +
    C ((1 : ℂ) * r * Complex.I) * mon 0 4 0 1 +
    C ((-1 : ℂ)) * mon 0 3 1 1

def degreeNineWitness14_3 (r : ℂ) : Poly :=
    C ((1 : ℂ)) * mon 1 4 1 0 +
    C ((-1 : ℂ) * r) * mon 1 3 1 1 +
    C ((-2 : ℂ) * Complex.I + (1 : ℂ)) * mon 1 2 2 1 +
    C ((1 : ℂ) * Complex.I) * mon 0 5 1 0 +
    C ((-1 : ℂ) * r * Complex.I) * mon 0 4 1 1 +
    C ((1 : ℂ)) * mon 0 3 2 1

theorem degreeNineCertificate14 (r : ℂ) (hr : r ^ 3 = 2) :
    (1 : Poly) * mon 0 8 1 0 - C ((0 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness14_0 r +
      relation r 1 * degreeNineWitness14_1 r +
      relation r 2 * degreeNineWitness14_2 r +
      relation r 3 * degreeNineWitness14_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness14_0, degreeNineWitness14_1,
    degreeNineWitness14_2, degreeNineWitness14_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness15_0 (r : ℂ) : Poly :=
    C ((1 : ℂ)) * mon 0 7 0 0 +
    C ((-1 : ℂ) * r) * mon 0 6 0 1 +
    C ((2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 5 1 1 +
    C ((2 : ℂ) * Complex.I) * mon 0 4 3 0 +
    C ((-1 : ℂ) * r) * mon 0 4 1 2 +
    C ((2 : ℂ) * Complex.I + (-3 : ℂ)) * mon 0 3 2 2 +
    C ((2 : ℂ) * Complex.I) * mon 0 2 4 1

def degreeNineWitness15_1 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 1 3 1 0 +
    C ((-1 : ℂ) * Complex.I + (1 : ℂ)) * mon 1 3 0 1 +
    C ((2 : ℂ) * Complex.I + (-6 : ℂ)) * mon 1 2 2 0 +
    C ((1 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 1 2 0 2 +
    C ((5 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 1 1 2 +
    C ((1 : ℂ) * r) * mon 1 0 4 0 +
    C ((2 : ℂ) * Complex.I + (2 : ℂ)) * mon 1 0 3 1 +
    C ((-1 : ℂ) * r ^ 2) * mon 0 5 0 0 +
    C ((1 : ℂ) * r * Complex.I + (-2 : ℂ) * r) * mon 0 4 1 0 +
    C ((-3 : ℂ) * Complex.I + (-3 : ℂ)) * mon 0 4 0 1 +
    C ((-3 : ℂ)) * mon 0 3 2 0 +
    C ((-1 : ℂ) * r ^ 2) * mon 0 3 1 1 +
    C ((-1 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 0 3 0 2 +
    C ((2 : ℂ) * r * Complex.I + (-3 : ℂ) * r) * mon 0 2 2 1 +
    C ((3 : ℂ) * Complex.I + (-3 : ℂ)) * mon 0 2 1 2 +
    C ((2 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 0 1 4 0 +
    C ((3 : ℂ) * Complex.I + (-3 : ℂ)) * mon 0 1 3 1 +
    C ((-1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 0 0 3 2

def degreeNineWitness15_2 (r : ℂ) : Poly :=
    C ((4 : ℂ) * Complex.I + (-6 : ℂ)) * mon 1 3 0 1 +
    C ((2 : ℂ) * Complex.I) * mon 1 2 2 0 +
    C ((-6 : ℂ)) * mon 0 4 0 1 +
    C ((-3 : ℂ)) * mon 0 3 2 0 +
    C ((1 : ℂ) * r) * mon 0 2 2 1

def degreeNineWitness15_3 (r : ℂ) : Poly :=
    C ((-1 : ℂ)) * mon 1 5 0 0 +
    C ((1 : ℂ) * r) * mon 1 4 0 1 +
    C ((-2 : ℂ) * Complex.I + (3 : ℂ)) * mon 1 3 1 1 +
    C ((-2 : ℂ) * Complex.I) * mon 1 2 3 0 +
    C ((3 : ℂ) * Complex.I) * mon 0 6 0 0 +
    C ((1 : ℂ) * r * Complex.I) * mon 0 5 0 1 +
    C ((3 : ℂ)) * mon 0 4 1 1 +
    C ((3 : ℂ)) * mon 0 3 3 0 +
    C ((-1 : ℂ) * r) * mon 0 2 3 1

theorem degreeNineCertificate15 (r : ℂ) (hr : r ^ 3 = 2) :
    (3 : Poly) * mon 0 9 0 0 - C ((-4 : ℂ) * Complex.I) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness15_0 r +
      relation r 1 * degreeNineWitness15_1 r +
      relation r 2 * degreeNineWitness15_2 r +
      relation r 3 * degreeNineWitness15_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness15_0, degreeNineWitness15_1,
    degreeNineWitness15_2, degreeNineWitness15_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness16_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 0 3 2 2 +
    C ((2 : ℂ) * Complex.I) * mon 0 3 1 3 +
    C ((2 : ℂ) * Complex.I) * mon 0 2 3 2 +
    C ((-2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 2 0 5 +
    C ((-1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 0 1 3 3 +
    C ((2 : ℂ) * Complex.I) * mon 0 1 2 4 +
    C ((2 : ℂ) * Complex.I) * mon 0 0 4 3 +
    C ((-2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 0 1 6

def degreeNineWitness16_1 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 1 2 2 0 +
    C ((2 : ℂ)) * mon 1 2 1 1 +
    C ((2 : ℂ)) * mon 1 1 3 0 +
    C ((2 : ℂ) * r * Complex.I) * mon 1 1 1 2 +
    C ((2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 1 0 3 +
    C ((-1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 1 0 3 1 +
    C ((2 : ℂ) * Complex.I) * mon 1 0 2 2 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 0 2 2 1 +
    C ((2 : ℂ) * r * Complex.I + (2 : ℂ) * r) * mon 0 2 1 2 +
    C ((2 : ℂ) * r * Complex.I) * mon 0 1 3 1 +
    C ((-2 : ℂ) * r * Complex.I + (-2 : ℂ) * r) * mon 0 1 0 4 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 0 0 3 2 +
    C ((4 : ℂ) * r * Complex.I) * mon 0 0 2 3

def degreeNineWitness16_2 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 1 1 1 2 +
    C ((4 : ℂ) * Complex.I) * mon 1 1 0 3 +
    C ((2 : ℂ) * Complex.I) * mon 1 0 2 2 +
    C ((4 : ℂ) * r * Complex.I) * mon 0 1 0 4

def degreeNineWitness16_3 (r : ℂ) : Poly :=
    C ((1 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 1 1 2 2 +
    C ((-2 : ℂ) * Complex.I) * mon 1 1 1 3 +
    C ((-2 : ℂ) * Complex.I) * mon 1 0 3 2 +
    C ((2 : ℂ) * Complex.I + (2 : ℂ)) * mon 1 0 0 5 +
    C ((-2 : ℂ) * r * Complex.I) * mon 0 1 1 4

theorem degreeNineCertificate16 (r : ℂ) (hr : r ^ 3 = 2) :
    (4 : Poly) * mon 1 0 0 8 - C ((0 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness16_0 r +
      relation r 1 * degreeNineWitness16_1 r +
      relation r 2 * degreeNineWitness16_2 r +
      relation r 3 * degreeNineWitness16_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness16_0, degreeNineWitness16_1,
    degreeNineWitness16_2, degreeNineWitness16_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness17_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 7 0 0 +
    C ((1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 0 6 0 1 +
    C ((-2 : ℂ)) * mon 0 5 1 1 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 4 3 0 +
    C ((1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 0 4 1 2 +
    C ((-3 : ℂ) * r * Complex.I + (3 : ℂ) * r) * mon 0 3 3 1 +
    C ((7 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 3 2 2 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 2 4 1 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 0 2 1 4 +
    C ((-3 : ℂ) * r * Complex.I + (3 : ℂ) * r) * mon 0 1 4 2 +
    C ((6 : ℂ) * Complex.I) * mon 0 1 3 3 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 0 0 2 5

def degreeNineWitness17_1 (r : ℂ) : Poly :=
    C ((2 : ℂ) * r * Complex.I) * mon 1 3 1 0 +
    C ((-2 : ℂ)) * mon 1 3 0 1 +
    C ((1 : ℂ) * Complex.I + (5 : ℂ)) * mon 1 2 2 0 +
    C ((2 : ℂ) * r) * mon 1 2 0 2 +
    C ((6 : ℂ) * r * Complex.I) * mon 1 1 2 1 +
    C ((8 : ℂ) * Complex.I + (-6 : ℂ)) * mon 1 1 1 2 +
    C ((-1 : ℂ) * r * Complex.I + (5 : ℂ) * r) * mon 1 0 4 0 +
    C ((8 : ℂ) * Complex.I) * mon 1 0 3 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 0 5 0 0 +
    C ((1 : ℂ) * r * Complex.I + (-3 : ℂ) * r) * mon 0 4 1 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 0 3 1 1 +
    C ((2 : ℂ) * r * Complex.I) * mon 0 3 0 2 +
    C ((-3 : ℂ) * r ^ 2 * Complex.I + (3 : ℂ) * r ^ 2) * mon 0 2 3 0 +
    C ((7 : ℂ) * r * Complex.I + (5 : ℂ) * r) * mon 0 2 2 1 +
    C ((3 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 0 1 4 0 +
    C ((-6 : ℂ) * r * Complex.I + (-6 : ℂ) * r) * mon 0 1 1 3 +
    C ((-3 : ℂ) * r ^ 2 * Complex.I + (3 : ℂ) * r ^ 2) * mon 0 0 4 1 +
    C ((12 : ℂ) * r * Complex.I + (4 : ℂ) * r) * mon 0 0 3 2

def degreeNineWitness17_2 (r : ℂ) : Poly :=
    C ((2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 3 0 1 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 2 2 0 +
    C ((-3 : ℂ) * r * Complex.I + (3 : ℂ) * r) * mon 1 1 2 1 +
    C ((6 : ℂ) * Complex.I) * mon 1 1 1 2 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 1 0 0 4 +
    C ((2 : ℂ) * r * Complex.I + (2 : ℂ) * r) * mon 0 2 2 1 +
    C ((6 : ℂ) * r * Complex.I) * mon 0 1 1 3

def degreeNineWitness17_3 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I + (1 : ℂ)) * mon 1 5 0 0 +
    C ((-1 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 1 4 0 1 +
    C ((-1 : ℂ) * Complex.I + (1 : ℂ)) * mon 1 3 1 1 +
    C ((-1 : ℂ) * Complex.I + (1 : ℂ)) * mon 1 2 3 0 +
    C ((3 : ℂ) * r * Complex.I + (-3 : ℂ) * r) * mon 1 1 3 1 +
    C ((-6 : ℂ) * Complex.I) * mon 1 1 2 2 +
    C ((6 : ℂ) * Complex.I + (6 : ℂ)) * mon 1 0 1 4 +
    C ((-1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 0 5 0 1 +
    C ((-2 : ℂ) * r * Complex.I + (-2 : ℂ) * r) * mon 0 2 3 1 +
    C ((-6 : ℂ) * r * Complex.I) * mon 0 1 2 3

theorem degreeNineCertificate17 (r : ℂ) (hr : r ^ 3 = 2) :
    (12 : Poly) * mon 1 0 1 7 - C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness17_0 r +
      relation r 1 * degreeNineWitness17_1 r +
      relation r 2 * degreeNineWitness17_2 r +
      relation r 3 * degreeNineWitness17_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness17_0, degreeNineWitness17_1,
    degreeNineWitness17_2, degreeNineWitness17_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness18_0 (r : ℂ) : Poly :=
    C ((1 : ℂ) * r ^ 2) * mon 0 7 0 0 +
    C ((-2 : ℂ)) * mon 0 6 0 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 0 5 1 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 4 3 0 +
    C ((-2 : ℂ)) * mon 0 4 1 2 +
    C ((6 : ℂ) * Complex.I) * mon 0 3 3 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 3 2 2 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 2 4 1 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 0 2 2 3 +
    C ((6 : ℂ) * Complex.I) * mon 0 1 4 2 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 0 0 3 4

def degreeNineWitness18_1 (r : ℂ) : Poly :=
    C ((-2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 3 1 0 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 1 3 0 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 1 2 2 0 +
    C ((2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 2 0 2 +
    C ((6 : ℂ) * r * Complex.I) * mon 1 1 3 0 +
    C ((6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 1 1 2 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 1 1 2 +
    C ((6 : ℂ) * Complex.I + (-4 : ℂ)) * mon 1 0 4 0 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 0 3 1 +
    C ((-2 : ℂ) * r) * mon 0 5 0 0 +
    C ((-4 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 4 1 0 +
    C ((-2 : ℂ) * r) * mon 0 3 1 1 +
    C ((-2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 3 0 2 +
    C ((6 : ℂ) * r * Complex.I + (6 : ℂ) * r) * mon 0 2 3 0 +
    C ((-2 : ℂ) * Complex.I) * mon 0 2 2 1 +
    C ((-2 : ℂ) * Complex.I + (-4 : ℂ)) * mon 0 1 4 0 +
    C ((-6 : ℂ) * r * Complex.I + (-6 : ℂ) * r) * mon 0 1 2 2 +
    C ((12 : ℂ) * r * Complex.I) * mon 0 0 4 1 +
    C ((4 : ℂ) * Complex.I + (-4 : ℂ)) * mon 0 0 3 2

def degreeNineWitness18_2 (r : ℂ) : Poly :=
    C ((-2 : ℂ) * r ^ 2 * Complex.I) * mon 1 3 0 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 1 2 2 0 +
    C ((6 : ℂ) * Complex.I) * mon 1 1 2 1 +
    C ((6 : ℂ) * r * Complex.I) * mon 1 1 0 3 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 1 0 1 3 +
    C ((-4 : ℂ)) * mon 0 2 2 1 +
    C ((6 : ℂ) * r * Complex.I) * mon 0 1 2 2

def degreeNineWitness18_3 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r ^ 2) * mon 1 5 0 0 +
    C ((2 : ℂ)) * mon 1 4 0 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 1 3 1 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 1 2 3 0 +
    C ((-6 : ℂ) * Complex.I) * mon 1 1 3 1 +
    C ((6 : ℂ) * Complex.I + (6 : ℂ)) * mon 1 0 2 3 +
    C ((2 : ℂ) * Complex.I) * mon 0 5 0 1 +
    C ((4 : ℂ)) * mon 0 2 3 1 +
    C ((-6 : ℂ) * r * Complex.I) * mon 0 1 3 2

theorem degreeNineCertificate18 (r : ℂ) (hr : r ^ 3 = 2) :
    (12 : Poly) * mon 1 0 2 6 - C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness18_0 r +
      relation r 1 * degreeNineWitness18_1 r +
      relation r 2 * degreeNineWitness18_2 r +
      relation r 3 * degreeNineWitness18_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness18_0, degreeNineWitness18_1,
    degreeNineWitness18_2, degreeNineWitness18_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness19_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 2 3 2 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 0 4 3

def degreeNineWitness19_1 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 1 3 0 +
    C ((-1 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 0 1 3 1

def degreeNineWitness19_2 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 1 0 3 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 0 2 2 +
    C ((-1 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 0 1 0 4

def degreeNineWitness19_3 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I + (1 : ℂ)) * mon 1 0 3 2

theorem degreeNineCertificate19 (r : ℂ) (hr : r ^ 3 = 2) :
    (2 : Poly) * mon 1 0 3 5 - C ((0 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness19_0 r +
      relation r 1 * degreeNineWitness19_1 r +
      relation r 2 * degreeNineWitness19_2 r +
      relation r 3 * degreeNineWitness19_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness19_0, degreeNineWitness19_1,
    degreeNineWitness19_2, degreeNineWitness19_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness20_0 (r : ℂ) : Poly :=
    C ((1 : ℂ) * r ^ 2) * mon 0 7 0 0 +
    C ((-2 : ℂ)) * mon 0 6 0 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 0 5 1 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 4 3 0 +
    C ((-2 : ℂ)) * mon 0 4 1 2 +
    C ((6 : ℂ) * Complex.I) * mon 0 3 3 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 3 2 2 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 0 3 0 4 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 2 4 1 +
    C ((6 : ℂ) * Complex.I) * mon 0 1 4 2 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 0 1 1 5

def degreeNineWitness20_1 (r : ℂ) : Poly :=
    C ((-2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 3 1 0 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 1 3 0 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 1 2 2 0 +
    C ((8 : ℂ) * Complex.I + (-8 : ℂ)) * mon 1 2 0 2 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 1 1 2 +
    C ((6 : ℂ) * Complex.I + (-4 : ℂ)) * mon 1 0 4 0 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 0 3 1 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 1 0 1 3 +
    C ((-2 : ℂ) * r) * mon 0 5 0 0 +
    C ((-4 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 4 1 0 +
    C ((-2 : ℂ) * r) * mon 0 3 1 1 +
    C ((-2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 3 0 2 +
    C ((6 : ℂ) * r * Complex.I) * mon 0 2 3 0 +
    C ((-2 : ℂ) * Complex.I) * mon 0 2 2 1 +
    C ((-6 : ℂ) * r * Complex.I + (-6 : ℂ) * r) * mon 0 2 0 3 +
    C ((-2 : ℂ) * Complex.I + (-4 : ℂ)) * mon 0 1 4 0 +
    C ((6 : ℂ) * r * Complex.I) * mon 0 0 4 1 +
    C ((4 : ℂ) * Complex.I + (-4 : ℂ)) * mon 0 0 3 2 +
    C ((-6 : ℂ) * r * Complex.I + (-6 : ℂ) * r) * mon 0 0 1 4

def degreeNineWitness20_2 (r : ℂ) : Poly :=
    C ((-2 : ℂ) * r ^ 2 * Complex.I) * mon 1 3 0 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 1 2 2 0 +
    C ((6 : ℂ) * Complex.I) * mon 1 1 2 1 +
    C ((-4 : ℂ)) * mon 0 2 2 1

def degreeNineWitness20_3 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r ^ 2) * mon 1 5 0 0 +
    C ((2 : ℂ)) * mon 1 4 0 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 1 3 1 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 1 2 3 0 +
    C ((-6 : ℂ) * Complex.I) * mon 1 1 3 1 +
    C ((6 : ℂ) * Complex.I + (6 : ℂ)) * mon 1 1 0 4 +
    C ((2 : ℂ) * Complex.I) * mon 0 5 0 1 +
    C ((4 : ℂ)) * mon 0 2 3 1

theorem degreeNineCertificate20 (r : ℂ) (hr : r ^ 3 = 2) :
    (12 : Poly) * mon 1 1 0 7 - C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness20_0 r +
      relation r 1 * degreeNineWitness20_1 r +
      relation r 2 * degreeNineWitness20_2 r +
      relation r 3 * degreeNineWitness20_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness20_0, degreeNineWitness20_1,
    degreeNineWitness20_2, degreeNineWitness20_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness21_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 3 1 3 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 1 2 4

def degreeNineWitness21_1 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 2 1 1 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 0 2 2 +
    C ((-1 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 0 2 1 2 +
    C ((-1 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 0 0 2 3

def degreeNineWitness21_2 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 1 0 3

def degreeNineWitness21_3 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I + (1 : ℂ)) * mon 1 1 1 3

theorem degreeNineCertificate21 (r : ℂ) (hr : r ^ 3 = 2) :
    (2 : Poly) * mon 1 1 1 6 - C ((0 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness21_0 r +
      relation r 1 * degreeNineWitness21_1 r +
      relation r 2 * degreeNineWitness21_2 r +
      relation r 3 * degreeNineWitness21_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness21_0, degreeNineWitness21_1,
    degreeNineWitness21_2, degreeNineWitness21_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness22_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 3 2 2 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 1 3 3

def degreeNineWitness22_1 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 2 2 0 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 0 3 1 +
    C ((-1 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 0 2 2 1 +
    C ((-1 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 0 0 3 2

def degreeNineWitness22_2 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 1 1 2

def degreeNineWitness22_3 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I + (1 : ℂ)) * mon 1 1 2 2

theorem degreeNineCertificate22 (r : ℂ) (hr : r ^ 3 = 2) :
    (2 : Poly) * mon 1 1 2 5 - C ((0 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness22_0 r +
      relation r 1 * degreeNineWitness22_1 r +
      relation r 2 * degreeNineWitness22_2 r +
      relation r 3 * degreeNineWitness22_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness22_0, degreeNineWitness22_1,
    degreeNineWitness22_2, degreeNineWitness22_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness23_0 (r : ℂ) : Poly :=
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 0 7 0 0 +
    C ((-2 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 6 0 1 +
    C ((2 : ℂ) * r ^ 2 * Complex.I) * mon 0 5 1 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 0 4 3 0 +
    C ((-2 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 4 1 2 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 0 3 3 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 0 3 2 2 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 0 2 4 1 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 0 1 4 2

def degreeNineWitness23_1 (r : ℂ) : Poly :=
    C ((4 : ℂ)) * mon 1 3 1 0 +
    C ((2 : ℂ) * r ^ 2 * Complex.I) * mon 1 3 0 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 1 2 2 0 +
    C ((-4 : ℂ) * Complex.I) * mon 1 2 0 2 +
    C ((2 : ℂ) * r ^ 2) * mon 1 1 1 2 +
    C ((-10 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 0 4 0 +
    C ((2 : ℂ) * r ^ 2) * mon 1 0 3 1 +
    C ((-2 : ℂ) * r * Complex.I + (2 : ℂ) * r) * mon 0 5 0 0 +
    C ((6 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 4 1 0 +
    C ((-2 : ℂ) * r * Complex.I + (2 : ℂ) * r) * mon 0 3 1 1 +
    C ((4 : ℂ)) * mon 0 3 0 2 +
    C ((-6 : ℂ) * r * Complex.I + (-6 : ℂ) * r) * mon 0 2 3 0 +
    C ((2 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 2 2 1 +
    C ((-2 : ℂ) * Complex.I + (6 : ℂ)) * mon 0 1 4 0 +
    C ((-6 : ℂ) * r * Complex.I + (-6 : ℂ) * r) * mon 0 0 4 1 +
    C ((-8 : ℂ) * Complex.I) * mon 0 0 3 2

def degreeNineWitness23_2 (r : ℂ) : Poly :=
    C ((2 : ℂ) * r ^ 2 * Complex.I + (2 : ℂ) * r ^ 2) * mon 1 3 0 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 1 2 2 0 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 1 1 2 1 +
    C ((-4 : ℂ) * Complex.I + (4 : ℂ)) * mon 0 2 2 1

def degreeNineWitness23_3 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 1 5 0 0 +
    C ((2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 4 0 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 3 1 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 2 3 0 +
    C ((6 : ℂ) * Complex.I + (6 : ℂ)) * mon 1 1 3 1 +
    C ((-2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 5 0 1 +
    C ((4 : ℂ) * Complex.I + (-4 : ℂ)) * mon 0 2 3 1

theorem degreeNineCertificate23 (r : ℂ) (hr : r ^ 3 = 2) :
    (12 : Poly) * mon 1 1 3 4 - C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness23_0 r +
      relation r 1 * degreeNineWitness23_1 r +
      relation r 2 * degreeNineWitness23_2 r +
      relation r 3 * degreeNineWitness23_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness23_0, degreeNineWitness23_1,
    degreeNineWitness23_2, degreeNineWitness23_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness24_0 (r : ℂ) : Poly :=
    C ((1 : ℂ) * r ^ 2) * mon 0 7 0 0 +
    C ((-2 : ℂ)) * mon 0 6 0 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 0 5 1 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 4 3 0 +
    C ((-2 : ℂ)) * mon 0 4 1 2 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 3 2 2 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 2 4 1

def degreeNineWitness24_1 (r : ℂ) : Poly :=
    C ((-2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 3 1 0 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 1 3 0 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 1 2 2 0 +
    C ((2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 2 0 2 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 1 1 2 +
    C ((-4 : ℂ)) * mon 1 0 4 0 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 0 3 1 +
    C ((-2 : ℂ) * r) * mon 0 5 0 0 +
    C ((-4 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 4 1 0 +
    C ((-2 : ℂ) * r) * mon 0 3 1 1 +
    C ((-2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 3 0 2 +
    C ((-2 : ℂ) * Complex.I) * mon 0 2 2 1 +
    C ((-2 : ℂ) * Complex.I + (-4 : ℂ)) * mon 0 1 4 0 +
    C ((4 : ℂ) * Complex.I + (-4 : ℂ)) * mon 0 0 3 2

def degreeNineWitness24_2 (r : ℂ) : Poly :=
    C ((-2 : ℂ) * r ^ 2 * Complex.I) * mon 1 3 0 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 1 2 2 0 +
    C ((-4 : ℂ)) * mon 0 2 2 1

def degreeNineWitness24_3 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r ^ 2) * mon 1 5 0 0 +
    C ((2 : ℂ)) * mon 1 4 0 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 1 3 1 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 1 2 3 0 +
    C ((2 : ℂ) * Complex.I) * mon 0 5 0 1 +
    C ((4 : ℂ)) * mon 0 2 3 1

theorem degreeNineCertificate24 (r : ℂ) (hr : r ^ 3 = 2) :
    (6 : Poly) * mon 1 4 3 1 - C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness24_0 r +
      relation r 1 * degreeNineWitness24_1 r +
      relation r 2 * degreeNineWitness24_2 r +
      relation r 3 * degreeNineWitness24_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness24_0, degreeNineWitness24_1,
    degreeNineWitness24_2, degreeNineWitness24_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness25_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I) * mon 0 4 2 1 +
    C ((-1 : ℂ) * Complex.I) * mon 0 2 3 2

def degreeNineWitness25_1 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I) * mon 1 1 3 0 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 0 2 2 +
    C ((-1 : ℂ) * r * Complex.I) * mon 0 3 2 0 +
    C ((-1 : ℂ) * r * Complex.I) * mon 0 1 3 1

def degreeNineWitness25_2 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I) * mon 1 2 1 1

def degreeNineWitness25_3 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I) * mon 1 2 2 1

theorem degreeNineCertificate25 (r : ℂ) (hr : r ^ 3 = 2) :
    (1 : Poly) * mon 1 5 2 1 - C ((0 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness25_0 r +
      relation r 1 * degreeNineWitness25_1 r +
      relation r 2 * degreeNineWitness25_2 r +
      relation r 3 * degreeNineWitness25_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness25_0, degreeNineWitness25_1,
    degreeNineWitness25_2, degreeNineWitness25_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness26_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ)) * mon 0 7 0 0 +
    C ((1 : ℂ) * r) * mon 0 6 0 1 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 5 1 1 +
    C ((-2 : ℂ) * Complex.I) * mon 0 4 3 0 +
    C ((1 : ℂ) * r) * mon 0 4 1 2 +
    C ((1 : ℂ) * Complex.I) * mon 0 3 2 2 +
    C ((-2 : ℂ) * Complex.I) * mon 0 2 4 1

def degreeNineWitness26_1 (r : ℂ) : Poly :=
    C ((1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 1 3 1 0 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 3 0 1 +
    C ((1 : ℂ) * Complex.I) * mon 1 2 2 0 +
    C ((-1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 1 2 0 2 +
    C ((1 : ℂ) * Complex.I + (1 : ℂ)) * mon 1 1 1 2 +
    C ((-1 : ℂ) * r) * mon 1 0 4 0 +
    C ((-2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 0 3 1 +
    C ((1 : ℂ) * r ^ 2) * mon 0 5 0 0 +
    C ((2 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 0 4 1 0 +
    C ((1 : ℂ) * r ^ 2) * mon 0 3 1 1 +
    C ((1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 0 3 0 2 +
    C ((1 : ℂ) * r * Complex.I) * mon 0 2 2 1 +
    C ((-2 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 0 1 4 0 +
    C ((1 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 0 0 3 2

def degreeNineWitness26_2 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I) * mon 1 3 0 1 +
    C ((-2 : ℂ) * Complex.I) * mon 1 2 2 0 +
    C ((-1 : ℂ) * r) * mon 0 2 2 1

def degreeNineWitness26_3 (r : ℂ) : Poly :=
    C ((1 : ℂ)) * mon 1 5 0 0 +
    C ((-1 : ℂ) * r) * mon 1 4 0 1 +
    C ((-1 : ℂ) * Complex.I) * mon 1 3 1 1 +
    C ((2 : ℂ) * Complex.I) * mon 1 2 3 0 +
    C ((-1 : ℂ) * r * Complex.I) * mon 0 5 0 1 +
    C ((1 : ℂ) * r) * mon 0 2 3 1

theorem degreeNineCertificate26 (r : ℂ) (hr : r ^ 3 = 2) :
    (3 : Poly) * mon 1 5 3 0 - C ((1 : ℂ) * Complex.I) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness26_0 r +
      relation r 1 * degreeNineWitness26_1 r +
      relation r 2 * degreeNineWitness26_2 r +
      relation r 3 * degreeNineWitness26_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness26_0, degreeNineWitness26_1,
    degreeNineWitness26_2, degreeNineWitness26_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness27_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I) * mon 0 5 1 1 +
    C ((-1 : ℂ) * Complex.I) * mon 0 3 2 2

def degreeNineWitness27_1 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I) * mon 1 2 2 0 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 1 1 2 +
    C ((-1 : ℂ) * r * Complex.I) * mon 0 4 1 0 +
    C ((-1 : ℂ) * r * Complex.I) * mon 0 2 2 1

def degreeNineWitness27_2 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I) * mon 1 3 0 1

def degreeNineWitness27_3 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I) * mon 1 3 1 1

theorem degreeNineCertificate27 (r : ℂ) (hr : r ^ 3 = 2) :
    (1 : Poly) * mon 1 6 1 1 - C ((0 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness27_0 r +
      relation r 1 * degreeNineWitness27_1 r +
      relation r 2 * degreeNineWitness27_2 r +
      relation r 3 * degreeNineWitness27_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness27_0, degreeNineWitness27_1,
    degreeNineWitness27_2, degreeNineWitness27_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness28_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 7 0 0 +
    C ((2 : ℂ) * Complex.I) * mon 0 6 0 1 +
    C ((-6 : ℂ) * Complex.I) * mon 0 5 2 0 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 0 5 1 1 +
    C ((-1 : ℂ) * r ^ 2) * mon 0 4 3 0 +
    C ((6 : ℂ) * r * Complex.I) * mon 0 4 2 1 +
    C ((2 : ℂ) * Complex.I) * mon 0 4 1 2 +
    C ((-6 : ℂ) * Complex.I) * mon 0 3 3 1 +
    C ((-1 : ℂ) * r ^ 2) * mon 0 3 2 2 +
    C ((-1 : ℂ) * r ^ 2) * mon 0 2 4 1 +
    C ((6 : ℂ) * r * Complex.I) * mon 0 2 3 2

def degreeNineWitness28_1 (r : ℂ) : Poly :=
    C ((2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 3 1 0 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 3 0 1 +
    C ((-1 : ℂ) * r ^ 2) * mon 1 2 2 0 +
    C ((2 : ℂ) * Complex.I + (2 : ℂ)) * mon 1 2 0 2 +
    C ((6 : ℂ) * r * Complex.I + (-6 : ℂ) * r) * mon 1 1 3 0 +
    C ((-6 : ℂ) * Complex.I + (-6 : ℂ)) * mon 1 1 2 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 1 1 2 +
    C ((4 : ℂ) * Complex.I) * mon 1 0 4 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 0 3 1 +
    C ((6 : ℂ) * r * Complex.I + (6 : ℂ) * r) * mon 1 0 2 2 +
    C ((2 : ℂ) * r * Complex.I) * mon 0 5 0 0 +
    C ((-2 : ℂ) * Complex.I + (-4 : ℂ)) * mon 0 4 1 0 +
    C ((6 : ℂ) * r ^ 2 * Complex.I) * mon 0 3 2 0 +
    C ((2 : ℂ) * r * Complex.I) * mon 0 3 1 1 +
    C ((2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 3 0 2 +
    C ((-6 : ℂ) * r * Complex.I + (-6 : ℂ) * r) * mon 0 2 3 0 +
    C ((-2 : ℂ)) * mon 0 2 2 1 +
    C ((4 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 1 4 0 +
    C ((6 : ℂ) * r ^ 2 * Complex.I) * mon 0 1 3 1 +
    C ((6 : ℂ) * r * Complex.I + (-6 : ℂ) * r) * mon 0 1 2 2 +
    C ((4 : ℂ) * Complex.I + (4 : ℂ)) * mon 0 0 3 2

def degreeNineWitness28_2 (r : ℂ) : Poly :=
    C ((-6 : ℂ) * Complex.I) * mon 1 3 1 0 +
    C ((-2 : ℂ) * r ^ 2) * mon 1 3 0 1 +
    C ((-1 : ℂ) * r ^ 2) * mon 1 2 2 0 +
    C ((6 : ℂ) * r * Complex.I) * mon 1 2 1 1 +
    C ((-6 : ℂ) * r) * mon 0 3 1 1 +
    C ((4 : ℂ) * Complex.I) * mon 0 2 2 1

def degreeNineWitness28_3 (r : ℂ) : Poly :=
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 1 5 0 0 +
    C ((-2 : ℂ) * Complex.I) * mon 1 4 0 1 +
    C ((6 : ℂ) * Complex.I) * mon 1 3 2 0 +
    C ((1 : ℂ) * r ^ 2) * mon 1 3 1 1 +
    C ((1 : ℂ) * r ^ 2) * mon 1 2 3 0 +
    C ((-6 : ℂ) * r * Complex.I) * mon 1 2 2 1 +
    C ((2 : ℂ)) * mon 0 5 0 1 +
    C ((6 : ℂ) * r) * mon 0 3 2 1 +
    C ((-4 : ℂ) * Complex.I) * mon 0 2 3 1

theorem degreeNineCertificate28 (r : ℂ) (hr : r ^ 3 = 2) :
    (6 : Poly) * mon 1 6 2 0 - C ((-1 : ℂ) * r ^ 2) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness28_0 r +
      relation r 1 * degreeNineWitness28_1 r +
      relation r 2 * degreeNineWitness28_2 r +
      relation r 3 * degreeNineWitness28_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness28_0, degreeNineWitness28_1,
    degreeNineWitness28_2, degreeNineWitness28_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness29_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 7 0 0 +
    C ((-4 : ℂ) * Complex.I) * mon 0 6 0 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 0 5 1 1 +
    C ((-1 : ℂ) * r ^ 2) * mon 0 4 3 0 +
    C ((-4 : ℂ) * Complex.I) * mon 0 4 1 2 +
    C ((-1 : ℂ) * r ^ 2) * mon 0 3 2 2 +
    C ((-1 : ℂ) * r ^ 2) * mon 0 2 4 1

def degreeNineWitness29_1 (r : ℂ) : Poly :=
    C ((-4 : ℂ) * Complex.I + (-2 : ℂ)) * mon 1 3 1 0 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 3 0 1 +
    C ((-1 : ℂ) * r ^ 2) * mon 1 2 2 0 +
    C ((-4 : ℂ) * Complex.I + (-4 : ℂ)) * mon 1 2 0 2 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 1 1 2 +
    C ((4 : ℂ) * Complex.I) * mon 1 0 4 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 0 3 1 +
    C ((-4 : ℂ) * r * Complex.I) * mon 0 5 0 0 +
    C ((-2 : ℂ) * Complex.I + (-4 : ℂ)) * mon 0 4 1 0 +
    C ((-4 : ℂ) * r * Complex.I) * mon 0 3 1 1 +
    C ((2 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 3 0 2 +
    C ((-2 : ℂ)) * mon 0 2 2 1 +
    C ((4 : ℂ) * Complex.I + (-2 : ℂ)) * mon 0 1 4 0 +
    C ((4 : ℂ) * Complex.I + (4 : ℂ)) * mon 0 0 3 2

def degreeNineWitness29_2 (r : ℂ) : Poly :=
    C ((-2 : ℂ) * r ^ 2) * mon 1 3 0 1 +
    C ((-1 : ℂ) * r ^ 2) * mon 1 2 2 0 +
    C ((4 : ℂ) * Complex.I) * mon 0 2 2 1

def degreeNineWitness29_3 (r : ℂ) : Poly :=
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 1 5 0 0 +
    C ((4 : ℂ) * Complex.I) * mon 1 4 0 1 +
    C ((1 : ℂ) * r ^ 2) * mon 1 3 1 1 +
    C ((1 : ℂ) * r ^ 2) * mon 1 2 3 0 +
    C ((2 : ℂ)) * mon 0 5 0 1 +
    C ((-4 : ℂ) * Complex.I) * mon 0 2 3 1

theorem degreeNineCertificate29 (r : ℂ) (hr : r ^ 3 = 2) :
    (6 : Poly) * mon 1 7 0 1 - C ((-1 : ℂ) * r ^ 2) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness29_0 r +
      relation r 1 * degreeNineWitness29_1 r +
      relation r 2 * degreeNineWitness29_2 r +
      relation r 3 * degreeNineWitness29_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness29_0, degreeNineWitness29_1,
    degreeNineWitness29_2, degreeNineWitness29_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness30_0 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I) * mon 0 6 1 0 +
    C ((1 : ℂ) * r * Complex.I) * mon 0 5 1 1 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 4 2 1 +
    C ((1 : ℂ) * r * Complex.I) * mon 0 3 2 2 +
    C ((-1 : ℂ)) * mon 0 2 3 2

def degreeNineWitness30_1 (r : ℂ) : Poly :=
    C ((1 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 1 2 2 0 +
    C ((-1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 2 1 1 +
    C ((-1 : ℂ)) * mon 1 1 3 0 +
    C ((1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 1 1 1 2 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 1 0 2 2 +
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 0 4 1 0 +
    C ((-1 : ℂ) * r * Complex.I + (-2 : ℂ) * r) * mon 0 3 2 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I) * mon 0 2 2 1 +
    C ((1 : ℂ) * r * Complex.I + (-1 : ℂ) * r) * mon 0 2 1 2 +
    C ((-1 : ℂ) * r) * mon 0 1 3 1

def degreeNineWitness30_2 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I) * mon 1 4 0 0 +
    C ((1 : ℂ) * r * Complex.I) * mon 1 3 0 1 +
    C ((-1 : ℂ)) * mon 1 2 1 1 +
    C ((-1 : ℂ) * r) * mon 0 4 0 1

def degreeNineWitness30_3 (r : ℂ) : Poly :=
    C ((1 : ℂ) * Complex.I) * mon 1 4 1 0 +
    C ((-1 : ℂ) * r * Complex.I) * mon 1 3 1 1 +
    C ((1 : ℂ)) * mon 1 2 2 1 +
    C ((1 : ℂ) * r) * mon 0 4 1 1

theorem degreeNineCertificate30 (r : ℂ) (hr : r ^ 3 = 2) :
    (1 : Poly) * mon 1 7 1 0 - C ((0 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness30_0 r +
      relation r 1 * degreeNineWitness30_1 r +
      relation r 2 * degreeNineWitness30_2 r +
      relation r 3 * degreeNineWitness30_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness30_0, degreeNineWitness30_1,
    degreeNineWitness30_2, degreeNineWitness30_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

def degreeNineWitness31_0 (r : ℂ) : Poly :=
    0

def degreeNineWitness31_1 (r : ℂ) : Poly :=
    0

def degreeNineWitness31_2 (r : ℂ) : Poly :=
    0

def degreeNineWitness31_3 (r : ℂ) : Poly :=
    0

theorem degreeNineCertificate31 (r : ℂ) (hr : r ^ 3 = 2) :
    (1 : Poly) * mon 1 8 0 0 - C ((1 : ℂ)) * mon 1 8 0 0 =
      relation r 0 * degreeNineWitness31_0 r +
      relation r 1 * degreeNineWitness31_1 r +
      relation r 2 * degreeNineWitness31_2 r +
      relation r 3 * degreeNineWitness31_3 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [degreeNineWitness31_0, degreeNineWitness31_1,
    degreeNineWitness31_2, degreeNineWitness31_3, relation, b, h, mon,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one] <;>
    ring_nf <;> (try simp only [hr', hi']) <;> ring

end CycleQ2SeedTrace

#print axioms CycleQ2SeedTrace.degreeNineCertificate0
#print axioms CycleQ2SeedTrace.degreeNineCertificate1
#print axioms CycleQ2SeedTrace.degreeNineCertificate2
#print axioms CycleQ2SeedTrace.degreeNineCertificate3
#print axioms CycleQ2SeedTrace.degreeNineCertificate4
#print axioms CycleQ2SeedTrace.degreeNineCertificate5
#print axioms CycleQ2SeedTrace.degreeNineCertificate6
#print axioms CycleQ2SeedTrace.degreeNineCertificate7
#print axioms CycleQ2SeedTrace.degreeNineCertificate8
#print axioms CycleQ2SeedTrace.degreeNineCertificate9
#print axioms CycleQ2SeedTrace.degreeNineCertificate10
#print axioms CycleQ2SeedTrace.degreeNineCertificate11
#print axioms CycleQ2SeedTrace.degreeNineCertificate12
#print axioms CycleQ2SeedTrace.degreeNineCertificate13
#print axioms CycleQ2SeedTrace.degreeNineCertificate14
#print axioms CycleQ2SeedTrace.degreeNineCertificate15
#print axioms CycleQ2SeedTrace.degreeNineCertificate16
#print axioms CycleQ2SeedTrace.degreeNineCertificate17
#print axioms CycleQ2SeedTrace.degreeNineCertificate18
#print axioms CycleQ2SeedTrace.degreeNineCertificate19
#print axioms CycleQ2SeedTrace.degreeNineCertificate20
#print axioms CycleQ2SeedTrace.degreeNineCertificate21
#print axioms CycleQ2SeedTrace.degreeNineCertificate22
#print axioms CycleQ2SeedTrace.degreeNineCertificate23
#print axioms CycleQ2SeedTrace.degreeNineCertificate24
#print axioms CycleQ2SeedTrace.degreeNineCertificate25
#print axioms CycleQ2SeedTrace.degreeNineCertificate26
#print axioms CycleQ2SeedTrace.degreeNineCertificate27
#print axioms CycleQ2SeedTrace.degreeNineCertificate28
#print axioms CycleQ2SeedTrace.degreeNineCertificate29
#print axioms CycleQ2SeedTrace.degreeNineCertificate30
#print axioms CycleQ2SeedTrace.degreeNineCertificate31
end
end


/- Component: seed_trace/SparseSeedDegreeNineCertificates.lean -/
section
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace CycleQ2SeedTrace
open MvPolynomial

/-- Every displayed normal monomial is proved to lie on the normalization line. -/
theorem degreeNineMonomial_mem_line (r : ℂ) (hr : r ^ 3 = 2) (i : Fin 32) :
    reducedQuotient r (degreeNineMonomial i) ∈ degreeNineLine r := by
  fin_cases i
  · change reducedQuotient r (mon 0 0 0 9) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness0_0 r) (degreeNineWitness0_1 r)
      (degreeNineWitness0_2 r) (degreeNineWitness0_3 r)
    rw [← degreeNineCertificate0 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (12 : ℂ) ((1 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 0 1 8) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness1_0 r) (degreeNineWitness1_1 r)
      (degreeNineWitness1_2 r) (degreeNineWitness1_3 r)
    rw [← degreeNineCertificate1 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (12 : ℂ) ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 0 2 7) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness2_0 r) (degreeNineWitness2_1 r)
      (degreeNineWitness2_2 r) (degreeNineWitness2_3 r)
    rw [← degreeNineCertificate2 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (2 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 0 3 6) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness3_0 r) (degreeNineWitness3_1 r)
      (degreeNineWitness3_2 r) (degreeNineWitness3_3 r)
    rw [← degreeNineCertificate3 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (2 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 1 0 8) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness4_0 r) (degreeNineWitness4_1 r)
      (degreeNineWitness4_2 r) (degreeNineWitness4_3 r)
    rw [← degreeNineCertificate4 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (2 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 1 1 7) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness5_0 r) (degreeNineWitness5_1 r)
      (degreeNineWitness5_2 r) (degreeNineWitness5_3 r)
    rw [← degreeNineCertificate5 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (2 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 1 2 6) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness6_0 r) (degreeNineWitness6_1 r)
      (degreeNineWitness6_2 r) (degreeNineWitness6_3 r)
    rw [← degreeNineCertificate6 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (12 : ℂ) ((-1 : ℂ) * r ^ 2 * Complex.I) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 1 3 5) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness7_0 r) (degreeNineWitness7_1 r)
      (degreeNineWitness7_2 r) (degreeNineWitness7_3 r)
    rw [← degreeNineCertificate7 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (2 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 5 3 1) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness8_0 r) (degreeNineWitness8_1 r)
      (degreeNineWitness8_2 r) (degreeNineWitness8_3 r)
    rw [← degreeNineCertificate8 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (6 : ℂ) ((-1 : ℂ) * r ^ 2) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 6 2 1) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness9_0 r) (degreeNineWitness9_1 r)
      (degreeNineWitness9_2 r) (degreeNineWitness9_3 r)
    rw [← degreeNineCertificate9 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (1 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 6 3 0) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness10_0 r) (degreeNineWitness10_1 r)
      (degreeNineWitness10_2 r) (degreeNineWitness10_3 r)
    rw [← degreeNineCertificate10 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (3 : ℂ) ((1 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 7 1 1) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness11_0 r) (degreeNineWitness11_1 r)
      (degreeNineWitness11_2 r) (degreeNineWitness11_3 r)
    rw [← degreeNineCertificate11 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (1 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 7 2 0) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness12_0 r) (degreeNineWitness12_1 r)
      (degreeNineWitness12_2 r) (degreeNineWitness12_3 r)
    rw [← degreeNineCertificate12 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (6 : ℂ) ((2 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 8 0 1) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness13_0 r) (degreeNineWitness13_1 r)
      (degreeNineWitness13_2 r) (degreeNineWitness13_3 r)
    rw [← degreeNineCertificate13 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (3 : ℂ) ((1 : ℂ) * r ^ 2 * Complex.I) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 8 1 0) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness14_0 r) (degreeNineWitness14_1 r)
      (degreeNineWitness14_2 r) (degreeNineWitness14_3 r)
    rw [← degreeNineCertificate14 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (1 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 9 0 0) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness15_0 r) (degreeNineWitness15_1 r)
      (degreeNineWitness15_2 r) (degreeNineWitness15_3 r)
    rw [← degreeNineCertificate15 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (3 : ℂ) ((-4 : ℂ) * Complex.I) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 0 0 8) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness16_0 r) (degreeNineWitness16_1 r)
      (degreeNineWitness16_2 r) (degreeNineWitness16_3 r)
    rw [← degreeNineCertificate16 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (4 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 0 1 7) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness17_0 r) (degreeNineWitness17_1 r)
      (degreeNineWitness17_2 r) (degreeNineWitness17_3 r)
    rw [← degreeNineCertificate17 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (12 : ℂ) ((1 : ℂ) * Complex.I + (-1 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 0 2 6) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness18_0 r) (degreeNineWitness18_1 r)
      (degreeNineWitness18_2 r) (degreeNineWitness18_3 r)
    rw [← degreeNineCertificate18 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (12 : ℂ) ((-1 : ℂ) * r ^ 2 * Complex.I) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 0 3 5) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness19_0 r) (degreeNineWitness19_1 r)
      (degreeNineWitness19_2 r) (degreeNineWitness19_3 r)
    rw [← degreeNineCertificate19 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (2 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 1 0 7) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness20_0 r) (degreeNineWitness20_1 r)
      (degreeNineWitness20_2 r) (degreeNineWitness20_3 r)
    rw [← degreeNineCertificate20 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (12 : ℂ) ((-1 : ℂ) * r ^ 2 * Complex.I) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 1 1 6) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness21_0 r) (degreeNineWitness21_1 r)
      (degreeNineWitness21_2 r) (degreeNineWitness21_3 r)
    rw [← degreeNineCertificate21 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (2 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 1 2 5) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness22_0 r) (degreeNineWitness22_1 r)
      (degreeNineWitness22_2 r) (degreeNineWitness22_3 r)
    rw [← degreeNineCertificate22 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (2 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 1 3 4) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness23_0 r) (degreeNineWitness23_1 r)
      (degreeNineWitness23_2 r) (degreeNineWitness23_3 r)
    rw [← degreeNineCertificate23 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (12 : ℂ) ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 4 3 1) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness24_0 r) (degreeNineWitness24_1 r)
      (degreeNineWitness24_2 r) (degreeNineWitness24_3 r)
    rw [← degreeNineCertificate24 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (6 : ℂ) ((-1 : ℂ) * r ^ 2 * Complex.I) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 5 2 1) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness25_0 r) (degreeNineWitness25_1 r)
      (degreeNineWitness25_2 r) (degreeNineWitness25_3 r)
    rw [← degreeNineCertificate25 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (1 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 5 3 0) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness26_0 r) (degreeNineWitness26_1 r)
      (degreeNineWitness26_2 r) (degreeNineWitness26_3 r)
    rw [← degreeNineCertificate26 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (3 : ℂ) ((1 : ℂ) * Complex.I) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 6 1 1) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness27_0 r) (degreeNineWitness27_1 r)
      (degreeNineWitness27_2 r) (degreeNineWitness27_3 r)
    rw [← degreeNineCertificate27 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (1 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 6 2 0) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness28_0 r) (degreeNineWitness28_1 r)
      (degreeNineWitness28_2 r) (degreeNineWitness28_3 r)
    rw [← degreeNineCertificate28 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (6 : ℂ) ((-1 : ℂ) * r ^ 2) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 7 0 1) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness29_0 r) (degreeNineWitness29_1 r)
      (degreeNineWitness29_2 r) (degreeNineWitness29_3 r)
    rw [← degreeNineCertificate29 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (6 : ℂ) ((-1 : ℂ) * r ^ 2) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 7 1 0) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness30_0 r) (degreeNineWitness30_1 r)
      (degreeNineWitness30_2 r) (degreeNineWitness30_3 r)
    rw [← degreeNineCertificate30 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (1 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 8 0 0) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness31_0 r) (degreeNineWitness31_1 r)
      (degreeNineWitness31_2 r) (degreeNineWitness31_3 r)
    rw [← degreeNineCertificate31 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (1 : ℂ) ((1 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)

end CycleQ2SeedTrace

#print axioms CycleQ2SeedTrace.degreeNineMonomial_mem_line
end
end


/- Component: seed_trace/SparseSeedDegreeNine.lean -/
section
/-!
# The actual degree-nine quotient component has a unique normalized trace

Every degree-nine polynomial class is reduced using the concrete ideal
relations and finite polynomial membership certificates. The component is
then proved to be a nonzero line, and the previously constructed normalized
trace is proved unique on it.

This is a finite algebra theorem for the sparse seed. No smoothness or
geometric residue comparison is asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
noncomputable section
namespace CycleQ2SeedTrace
open MvPolynomial

theorem degreeNine_normal_complete_fin :
    ∀ a : Fin 2, ∀ b : Fin 10, ∀ c : Fin 4, ∀ d : Fin 10,
      a.val + b.val + c.val + d.val = 9 → (b.val < 2 ∨ d.val < 2) →
      ∃ i : Fin 32, degreeNineExponent i = ![a.val, b.val, c.val, d.val] := by
  intro a b c d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide +kernel

theorem degreeNine_normal_complete (a b c d : ℕ)
    (ha : a < 2) (hc : c < 4) (hbd : b < 2 ∨ d < 2)
    (hdegree : a + b + c + d = 9) :
    ∃ i : Fin 32, degreeNineMonomial i = mon a b c d := by
  have hb : b < 10 := by omega
  have hd : d < 10 := by omega
  obtain ⟨i, hi⟩ := degreeNine_normal_complete_fin
    ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩ hdegree hbd
  exact ⟨i, by simp [degreeNineMonomial, hi]⟩

theorem degreeNine_mon_class_mem_line (r : ℂ) (hr : r ^ 3 = 2)
    (a b c d : ℕ) (hdegree : a + b + c + d = 9) :
    reducedQuotient r (mon a b c d) ∈ degreeNineLine r := by
  induction a using Nat.strong_induction_on generalizing b c d with
  | h a ih =>
      by_cases ha : a < 2
      · by_cases hc : c < 4
        · by_cases hbd : b < 2 ∨ d < 2
          · obtain ⟨i, hi⟩ := degreeNine_normal_complete a b c d ha hc hbd hdegree
            rw [← hi]
            exact degreeNineMonomial_mem_line r hr i
          · have hb : b = (b - 2) + 2 := by omega
            have hd : d = (d - 2) + 2 := by omega
            rw [hb, hd, quotient_mon_bd_add_two_zero]
            exact Submodule.zero_mem _
        · have hc' : c = (c - 4) + 4 := by omega
          rw [hc', quotient_mon_c_add_four_zero]
          exact Submodule.zero_mem _
      · have ha' : a = (a - 2) + 2 := by omega
        rw [ha', quotient_mon_add_two]
        apply Submodule.smul_mem
        exact ih (a - 2) (by omega) (b + 1) c (d + 1) (by omega)

theorem monomial_eq_C_mul_mon (d : Exp) (z : ℂ) :
    monomial d z = C z * mon (d 0) (d 1) (d 2) (d 3) := by
  rw [mon_eq_monomial, C_mul_monomial, mul_one]
  apply congrArg (fun e : Exp => monomial e z)
  ext i
  fin_cases i <;> rfl

theorem homogeneous_degreeNine_class_mem_line (r : ℂ) (hr : r ^ 3 = 2)
    {p : Poly} (hp : p.IsHomogeneous 9) :
    reducedQuotient r p ∈ degreeNineLine r := by
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simpa only [map_zero] using (degreeNineLine r).zero_mem
  | add p q _ _ hp hq =>
      simpa only [map_add] using (degreeNineLine r).add_mem hp hq
  | monomial d z hd =>
      rw [monomial_eq_C_mul_mon, ← smul_eq_C_mul, map_smul]
      apply Submodule.smul_mem
      apply degreeNine_mon_class_mem_line r hr
      have hdegree : d.degree = 9 := by
        simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hd
      rw [Finsupp.degree_eq_sum] at hdegree
      norm_num [Fin.sum_univ_succ] at hdegree
      rw [show (Fin.succ (2 : Fin 3) : Fin 4) = 3 from rfl] at hdegree
      omega

theorem degreeNinePiece_eq_line (r : ℂ) (hr : r ^ 3 = 2) :
    degreeNinePiece r = degreeNineLine r := by
  apply le_antisymm
  · rintro x ⟨p, hp, rfl⟩
    exact homogeneous_degreeNine_class_mem_line r hr hp
  · unfold degreeNineLine
    apply Submodule.span_le.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact normalizationClass_mem_piece r

/-- The actual homogeneous degree-nine component of the ideal quotient is
one-dimensional. -/
theorem degreeNinePiece_finrank (r : ℂ) (hr : r ^ 3 = 2) :
    Module.finrank ℂ (degreeNinePiece r) = 1 := by
  rw [degreeNinePiece_eq_line r hr]
  exact finrank_span_singleton (normalizationClass_ne_zero r hr)

@[simp] theorem reducedTrace_normalizationClass (r : ℂ) (hr : r ^ 3 = 2) :
    reducedTrace r hr (normalizationClass r) = 1 := trace_normalized r hr

theorem degreeNine_class_eq_trace_smul (r : ℂ) (hr : r ^ 3 = 2)
    {x : ReducedAlgebra r} (hx : x ∈ degreeNinePiece r) :
    x = reducedTrace r hr x • normalizationClass r := by
  rw [degreeNinePiece_eq_line r hr] at hx
  obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [map_smul, reducedTrace_normalizationClass, smul_eq_mul, mul_one]

/-- Uniform polynomial ideal-membership statement, beyond the finite list. -/
theorem homogeneous_degreeNine_mod_trace (r : ℂ) (hr : r ^ 3 = 2)
    {p : Poly} (hp : p.IsHomogeneous 9) :
    p - C (traceLinear r p) * mon 1 8 0 0 ∈ reducedIdeal r := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change reducedQuotient r (p - C (traceLinear r p) * mon 1 8 0 0) = 0
  rw [map_sub, ← smul_eq_C_mul, map_smul, sub_eq_zero]
  exact degreeNine_class_eq_trace_smul r hr ⟨p, hp, rfl⟩

def degreeNineTrace (r : ℂ) (hr : r ^ 3 = 2) : degreeNinePiece r →ₗ[ℂ] ℂ :=
  (reducedTrace r hr).comp (degreeNinePiece r).subtype

def degreeNineNormalization (r : ℂ) : degreeNinePiece r :=
  ⟨normalizationClass r, normalizationClass_mem_piece r⟩

@[simp] theorem degreeNineTrace_normalized (r : ℂ) (hr : r ^ 3 = 2) :
    degreeNineTrace r hr (degreeNineNormalization r) = 1 := trace_normalized r hr

/-- Any complex-linear trace on this component with the stated normalization
is the constructed trace. No trace values remain as free input data. -/
theorem degreeNineTrace_unique (r : ℂ) (hr : r ^ 3 = 2)
    (τ : degreeNinePiece r →ₗ[ℂ] ℂ)
    (hτ : τ (degreeNineNormalization r) = 1) : τ = degreeNineTrace r hr := by
  ext x
  let c : ℂ := reducedTrace r hr (x : ReducedAlgebra r)
  have hx : x = c • degreeNineNormalization r := by
    apply Subtype.ext
    exact degreeNine_class_eq_trace_smul r hr x.property
  calc
    τ x = τ (c • degreeNineNormalization r) := congrArg τ hx
    _ = c := by rw [map_smul, hτ, smul_eq_mul, mul_one]
    _ = degreeNineTrace r hr x := rfl

end CycleQ2SeedTrace

#print axioms CycleQ2SeedTrace.degreeNinePiece_finrank
#print axioms CycleQ2SeedTrace.homogeneous_degreeNine_mod_trace
#print axioms CycleQ2SeedTrace.degreeNineTrace_unique
end
end


/- Component: euler_lift/EulerKoszulLift.lean -/
section
/-!
# Polynomial Euler lift of a horizontal four-form

In six homogeneous coordinates, a horizontal four-form is described dually
by a skew array B satisfying X_l B_ij - X_i B_lj + X_j B_li = 0.
For homogeneous entries of degree k+1, differentiating that relation gives
an explicit polynomial lift N_j = (sum_l partial_l B_lj)/(k+5).

The theorem proves the lift and its exact grading. It does not assert the
existence of a primitive or the geometric support of the protected residue.
-/

set_option autoImplicit false
noncomputable section

namespace CycleQ2EulerLift

open MvPolynomial HodgeComputer
open scoped BigOperators

abbrev Poly := AmbientPoly 5
abbrev SkewCoefficients := Fin 6 → Fin 6 → Poly

def columnDivergence (B : SkewCoefficients) (j : Fin 6) : Poly :=
  ∑ i, pderiv i (B i j)

def numeratorLift (k : ℕ) (B : SkewCoefficients) (j : Fin 6) : Poly :=
  C (((k + 5 : ℕ) : ℂ)⁻¹) * columnDivergence B j

theorem sum_partial_coordinate_mul (v : Fin 6 → Poly) (i : Fin 6) :
    (∑ j, pderiv j (X i * v j)) = v i + X i * ∑ j, pderiv j (v j) := by
  classical
  simp [pderiv_X, Pi.single_apply, Finset.sum_add_distrib,
    Finset.mul_sum, add_comm]

theorem sum_radial_derivative {P : Poly} {d : ℕ} (hP : P.IsHomogeneous d) :
    (∑ j : Fin 6, pderiv j (X j * P)) = C ((d + 6 : ℕ) : ℂ) * P := by
  simp only [pderiv_mul, pderiv_X_self, one_mul, Finset.sum_add_distrib]
  rw [hP.sum_X_mul_pderiv]
  simp [nsmul_eq_mul, map_ofNat]
  ring

theorem columnDivergence_homogeneous {k : ℕ} {B : SkewCoefficients}
    (hB : ∀ i j, (B i j).IsHomogeneous (k + 1)) (j : Fin 6) :
    (columnDivergence B j).IsHomogeneous k := by
  unfold columnDivergence
  apply IsHomogeneous.sum Finset.univ
  intro i _
  simpa only [Nat.add_sub_cancel] using (hB i j).pderiv (i := i)

theorem numeratorLift_homogeneous {k : ℕ} {B : SkewCoefficients}
    (hB : ∀ i j, (B i j).IsHomogeneous (k + 1)) (j : Fin 6) :
    (numeratorLift k B j).IsHomogeneous k :=
  (columnDivergence_homogeneous hB j).C_mul _

/-- The differentiated Koszul relation, before division by its nonzero scalar. -/
theorem differentiated_horizontal {k : ℕ} {B : SkewCoefficients}
    (hB : ∀ i j, (B i j).IsHomogeneous (k + 1))
    (hskew : ∀ i j, B j i = -B i j)
    (hhor : ∀ l i j, X l * B i j - X i * B l j + X j * B l i = 0)
    (i j : Fin 6) :
    C ((k + 5 : ℕ) : ℂ) * B i j =
      X i * columnDivergence B j - X j * columnDivergence B i := by
  have hd : (∑ l : Fin 6,
      pderiv l (X l * B i j - X i * B l j + X j * B l i)) = 0 := by
    simp_rw [hhor]
    simp
  simp only [map_add, map_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib] at hd
  rw [sum_radial_derivative (hB i j), sum_partial_coordinate_mul,
    sum_partial_coordinate_mul, hskew i j] at hd
  change C (((k + 1) + 6 : ℕ) : ℂ) * B i j -
    (B i j + X i * columnDivergence B j) +
    (-B i j + X j * columnDivergence B i) = 0 at hd
  simp only [Nat.cast_add, Nat.cast_ofNat, map_add, map_natCast, map_ofNat] at hd ⊢
  linear_combination hd

/-- Explicit Koszul exactness with the numerator degree required by Verify. -/
theorem numeratorLift_wedge {k : ℕ} {B : SkewCoefficients}
    (hB : ∀ i j, (B i j).IsHomogeneous (k + 1))
    (hskew : ∀ i j, B j i = -B i j)
    (hhor : ∀ l i j, X l * B i j - X i * B l j + X j * B l i = 0)
    (i j : Fin 6) :
    B i j = X i * numeratorLift k B j - X j * numeratorLift k B i := by
  have hc : ((k + 5 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : k + 5 ≠ 0)
  have hinv : C (((k + 5 : ℕ) : ℂ)⁻¹) * C ((k + 5 : ℕ) : ℂ) = (1 : Poly) := by
    rw [← map_mul, inv_mul_cancel₀ hc, map_one]
  have hd := differentiated_horizontal hB hskew hhor i j
  have hh := congrArg (fun P : Poly => C (((k + 5 : ℕ) : ℂ)⁻¹) * P) hd
  rw [← mul_assoc, hinv, one_mul] at hh
  rw [hh]
  unfold numeratorLift
  ring

/-- Every homogeneous horizontal skew array has polynomial numerator data. -/
theorem exists_homogeneous_lift {k : ℕ} {B : SkewCoefficients}
    (hB : ∀ i j, (B i j).IsHomogeneous (k + 1))
    (hskew : ∀ i j, B j i = -B i j)
    (hhor : ∀ l i j, X l * B i j - X i * B l j + X j * B l i = 0) :
    ∃ N : Fin 6 → Poly, (∀ i, (N i).IsHomogeneous k) ∧
      (∀ i j, B i j = X i * N j - X j * N i) :=
  ⟨numeratorLift k B, numeratorLift_homogeneous hB,
    numeratorLift_wedge hB hskew hhor⟩

end CycleQ2EulerLift

#print axioms CycleQ2EulerLift.exists_homogeneous_lift
end
end


/- Component: euler_lift/RationalCartan.lean -/
section
/-!
# The coordinate Cartan identity for the bounded primitive

All derivatives here are the actual fraction-field extensions of polynomial
coordinate derivations. The skew coefficients of a rational four-form are
represented in complementary indices. Their exterior derivative in those
coordinates is the column divergence. This file proves the coordinate
identity and its grading; no geometric primitive is assumed to exist.
-/

set_option autoImplicit false
noncomputable section

namespace CycleQ2Cartan

open MvPolynomial HodgeComputer HodgeTestbed.Conic CycleQ2Bridge
open scoped BigOperators

abbrev Poly := AmbientPoly 5
abbrev RF := RationalFunction 5

local instance : Algebra ℚ RF := DivisionRing.toRatAlgebra
local instance : Module ℚ RF := Algebra.toModule

abbrev coordinate (i : Fin 6) : RF := polynomialMap 5 (X i)
abbrev coordinateDeriv (i : Fin 6) : Derivation ℚ RF RF := rationalPartial 5 i

def radial : Derivation ℚ RF RF := fieldAction coordinateDeriv coordinate

def div (v : Fin 6 → RF) : RF := fieldDivergence coordinateDeriv v

def skewCoefficient (v : Fin 6 → RF) (i j : Fin 6) : RF :=
  coordinate i * v j - coordinate j * v i

theorem radial_polynomial {P : Poly} {d : ℕ} (hP : P.IsHomogeneous d) :
    radial (polynomialMap 5 P) = (d : RF) * polynomialMap 5 P := by
  have h := congrArg (polynomialMap 5) hP.sum_X_mul_pderiv
  simpa only [radial, fieldAction_apply, rationalPartial_map,
    coordinate, coordinateDeriv, map_sum, map_mul, map_nsmul, nsmul_eq_mul,
    map_natCast] using h

theorem radial_quotient {P D : Poly} {p d : ℕ}
    (hP : P.IsHomogeneous p) (hD : D.IsHomogeneous d) (hD0 : D ≠ 0) :
    radial (polynomialMap 5 P / polynomialMap 5 D) =
      ((p : RF) - (d : RF)) * (polynomialMap 5 P / polynomialMap 5 D) := by
  rw [Derivation.leibniz_div, radial_polynomial hP, radial_polynomial hD]
  have hD' := polynomialMap_ne_zero hD0
  simp only [smul_eq_mul]
  field_simp

theorem sum_partial_radial_mul (a : RF) :
    (∑ i : Fin 6, coordinateDeriv i (coordinate i * a)) = 6 * a + radial a := by
  simp only [Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
  have hd : ∀ i : Fin 6, coordinateDeriv i (coordinate i) = 1 := by
    intro i
    simp only [coordinateDeriv, coordinate, rationalPartial_map, pderiv_X_self, map_one]
  simp only [hd, mul_one]
  simp [radial, fieldAction_apply, nsmul_eq_mul, add_comm]

theorem sum_partial_coordinate_mul (v : Fin 6 → RF) (j : Fin 6) :
    (∑ i : Fin 6, coordinateDeriv i (coordinate j * v i)) = v j + coordinate j * div v := by
  classical
  have hd : ∀ i : Fin 6, coordinateDeriv i (coordinate j) = if j = i then 1 else 0 := by
    intro i
    simp [coordinateDeriv, coordinate, rationalPartial_map, pderiv_X, Pi.single_apply]
  simp [Derivation.leibniz, smul_eq_mul, hd, div, fieldDivergence,
    Finset.sum_add_distrib, Finset.mul_sum, add_comm]

/-- The ungraded Cartan coefficient identity. -/
theorem skew_divergence (v : Fin 6 → RF) (j : Fin 6) :
    (∑ i : Fin 6, coordinateDeriv i (skewCoefficient v i j)) =
      5 * v j + radial (v j) - coordinate j * div v := by
  simp only [skewCoefficient, map_sub, Finset.sum_sub_distrib]
  rw [sum_partial_radial_mul, sum_partial_coordinate_mul]
  ring

theorem skew_divergence_of_weight (v : Fin 6 → RF)
    (hv : ∀ j, radial (v j) = -5 * v j) (j : Fin 6) :
    (∑ i : Fin 6, coordinateDeriv i (skewCoefficient v i j)) =
      -coordinate j * div v := by
  rw [skew_divergence, hv]
  ring

def primitiveVector (F D : Poly) (N : Fin 6 → Poly) : Fin 6 → RF :=
  rationalField (F ^ 2 * D) N

theorem primitiveVector_eq (F D : Poly) (N : Fin 6 → Poly) (j : Fin 6) :
    primitiveVector F D N j = rationalField D N j / (polynomialMap 5 F)^2 := by
  simp only [primitiveVector, rationalField, map_mul, map_pow, div_eq_mul_inv,
    mul_inv_rev]
  ring

theorem primitiveVector_weight {F D : Poly} {m : ℕ} {N : Fin 6 → Poly}
    (hF : F.IsHomogeneous 6) (hF0 : F ≠ 0)
    (hD : D.IsHomogeneous m) (hD0 : D ≠ 0)
    (hN : ∀ j, (N j).IsHomogeneous (m + 7)) (j : Fin 6) :
    radial (primitiveVector F D N j) = -5 * primitiveVector F D N j := by
  have hden : (F ^ 2 * D).IsHomogeneous (m + 12) := by
    simpa only [Nat.mul_one, Nat.reduceMul, Nat.add_comm] using (hF.pow 2).mul hD
  have heq := radial_quotient (hN j) hden (mul_ne_zero (pow_ne_zero 2 hF0) hD0)
  change radial (polynomialMap 5 (N j) / polynomialMap 5 (F ^ 2 * D)) =
    -5 * (polynomialMap 5 (N j) / polynomialMap 5 (F ^ 2 * D))
  rw [heq]
  push_cast
  ring

/-- Divergence of v/F^2 in the actual rational-function differential algebra. -/
theorem div_scaled_square (v : Fin 6 → RF) (f : RF) (hf : f ≠ 0) :
    div (fun j => v j / f ^ 2) =
      (f * div v - 2 * fieldAction coordinateDeriv v f) / f ^ 3 := by
  have hi : ∀ i : Fin 6,
      coordinateDeriv i (v i / f ^ 2) = coordinateDeriv i (v i) / f ^ 2 -
        2 * (v i * coordinateDeriv i f) / f ^ 3 := by
    intro i
    simp only [Derivation.leibniz_div, Derivation.leibniz_pow,
      smul_eq_mul, nsmul_eq_mul]
    norm_num
    field_simp
  simp only [div, fieldDivergence, hi, fieldAction_apply,
    Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum]
  field_simp

/-- The exact coordinate form of omega - d beta = (defect/F^3) Omega. -/
theorem primitive_defect_coefficient {F D : Poly} (A : Poly) {m : ℕ}
    {N : Fin 6 → Poly}
    (hF : F.IsHomogeneous 6) (hF0 : F ≠ 0)
    (hD : D.IsHomogeneous m) (hD0 : D ≠ 0)
    (hN : ∀ j, (N j).IsHomogeneous (m + 7)) (j : Fin 6) :
    coordinate j * polynomialMap 5 A / (polynomialMap 5 F)^3 -
        (∑ i : Fin 6, coordinateDeriv i (skewCoefficient (primitiveVector F D N) i j)) =
      coordinate j * rationalDefect F A 2 (rationalField D N) /
        (polynomialMap 5 F)^3 := by
  rw [skew_divergence_of_weight _ (primitiveVector_weight hF hF0 hD hD0 hN)]
  have hw : primitiveVector F D N = fun j => rationalField D N j / (polynomialMap 5 F)^2 := by
    funext j
    exact primitiveVector_eq F D N j
  rw [hw, div_scaled_square _ _ (polynomialMap_ne_zero hF0)]
  simp only [rationalDefect, div]
  ring

end CycleQ2Cartan

#print axioms CycleQ2Cartan.primitive_defect_coefficient
end
end


/- Component: euler_lift/ComplexCoordinateDerivations.lean -/
section
/-!
# The actual fraction-field coordinate derivations over the complex numbers

The reused fraction-derivation extension was packaged over the rationals.
It annihilates every mapped complex constant. The Leibniz rule therefore
proves complex linearity and gives an actual complex derivation with exactly
the same underlying function and rational scalar restriction.

This resolves the coefficient-field typing needed for a later comparison
with relative complex differentials. No exterior-form comparison or geometric
primitive is asserted here.
-/

set_option autoImplicit false
noncomputable section

namespace CycleQ2ComplexDerivations
open MvPolynomial HodgeComputer CycleQ2Bridge

local instance rationalFunctionRatAlgebra (n : ℕ) : Algebra ℚ (RationalFunction n) :=
  DivisionRing.toRatAlgebra

local instance rationalFunctionRatModule (n : ℕ) : Module ℚ (RationalFunction n) :=
  Algebra.toModule

theorem rationalPartial_complex_constant (n : ℕ) (i : Fin (n + 1)) (c : ℂ) :
    rationalPartial n i (algebraMap ℂ (RationalFunction n) c) = 0 := by
  rw [IsScalarTower.algebraMap_apply ℂ (AmbientPoly n) (RationalFunction n)]
  change rationalPartial n i (polynomialMap n (C c)) = 0
  rw [rationalPartial_map, pderiv_C, map_zero]

theorem rationalPartial_complex_smul (n : ℕ) (i : Fin (n + 1))
    (c : ℂ) (x : RationalFunction n) :
    rationalPartial n i (c • x) = c • rationalPartial n i x := by
  simp only [Algebra.smul_def, Derivation.leibniz, smul_eq_mul,
    rationalPartial_complex_constant, mul_zero, add_zero]
  simp

/-- The same coordinate differential operator, now with its true complex
scalar linearity included in the type. -/
def complexRationalPartial (n : ℕ) (i : Fin (n + 1)) :
    Derivation ℂ (RationalFunction n) (RationalFunction n) where
  toFun := rationalPartial n i
  map_add' := (rationalPartial n i).map_add
  map_smul' := rationalPartial_complex_smul n i
  map_one_eq_zero' := (rationalPartial n i).map_one_eq_zero
  leibniz' := (rationalPartial n i).leibniz

@[simp] theorem complexRationalPartial_apply (n : ℕ) (i : Fin (n + 1))
    (x : RationalFunction n) : complexRationalPartial n i x = rationalPartial n i x := rfl

/-- Restricting this complex derivation recovers the exact original operator. -/
theorem complexRationalPartial_restrictScalars (n : ℕ) (i : Fin (n + 1)) :
    (complexRationalPartial n i).restrictScalars ℚ = rationalPartial n i := by
  ext x
  rfl

@[simp] theorem complexRationalPartial_map (n : ℕ) (i : Fin (n + 1))
    (P : AmbientPoly n) :
    complexRationalPartial n i (polynomialMap n P) = polynomialMap n (pderiv i P) :=
  rationalPartial_map i P

@[simp] theorem complexRationalPartial_constant (n : ℕ) (i : Fin (n + 1)) (c : ℂ) :
    complexRationalPartial n i (algebraMap ℂ (RationalFunction n) c) = 0 :=
  rationalPartial_complex_constant n i c

end CycleQ2ComplexDerivations

#print axioms CycleQ2ComplexDerivations.rationalPartial_complex_smul
#print axioms CycleQ2ComplexDerivations.complexRationalPartial_restrictScalars
end
end


/- Component: pole_reduction/RationalDerivationRegularity.lean -/
section
/-!
# Actual fraction regularity and commuting coordinate derivations

Regularity is represented by a polynomial denominator relatively prime to F.
All closure statements use actual fraction-field arithmetic and the actual
extended coordinate derivations. No regularity or commutation axiom is used.
-/

set_option autoImplicit false
noncomputable section

namespace CycleQ2Regularity

open MvPolynomial HodgeComputer CycleQ2Bridge
open scoped BigOperators

variable {n : ℕ}

local instance rationalFunctionRatAlgebra (n : ℕ) : Algebra ℚ (RationalFunction n) :=
  DivisionRing.toRatAlgebra

local instance rationalFunctionRatModule (n : ℕ) : Module ℚ (RationalFunction n) :=
  Algebra.toModule

/-- An actual rational function represented with an F-coprime denominator. -/
def RegularAlong (F : AmbientPoly n) (z : RationalFunction n) : Prop :=
  ∃ (P T : AmbientPoly n), T ≠ 0 ∧ IsRelPrime F T ∧
    z = polynomialMap n P / polynomialMap n T

theorem regular_polynomial (F P : AmbientPoly n) :
    RegularAlong F (polynomialMap n P) := by
  exact ⟨P, 1, one_ne_zero, isRelPrime_one_right, by simp⟩

@[simp] theorem regular_zero (F : AmbientPoly n) : RegularAlong F 0 := by
  simpa only [map_zero] using regular_polynomial F 0

@[simp] theorem regular_one (F : AmbientPoly n) : RegularAlong F 1 := by
  simpa only [map_one] using regular_polynomial F 1

theorem RegularAlong.add {F : AmbientPoly n} {x y : RationalFunction n}
    (hx : RegularAlong F x) (hy : RegularAlong F y) : RegularAlong F (x + y) := by
  obtain ⟨P, T, hT, hFT, rfl⟩ := hx
  obtain ⟨Q, U, hU, hFU, rfl⟩ := hy
  refine ⟨P * U + Q * T, T * U, mul_ne_zero hT hU, hFT.mul_right hFU, ?_⟩
  have hT' := polynomialMap_ne_zero hT
  have hU' := polynomialMap_ne_zero hU
  simp only [map_add, map_mul]
  field_simp

theorem RegularAlong.neg {F : AmbientPoly n} {x : RationalFunction n}
    (hx : RegularAlong F x) : RegularAlong F (-x) := by
  obtain ⟨P, T, hT, hFT, rfl⟩ := hx
  exact ⟨-P, T, hT, hFT, by simp only [map_neg, div_eq_mul_inv]; ring⟩

theorem RegularAlong.sub {F : AmbientPoly n} {x y : RationalFunction n}
    (hx : RegularAlong F x) (hy : RegularAlong F y) : RegularAlong F (x - y) := by
  simpa only [sub_eq_add_neg] using hx.add hy.neg

theorem RegularAlong.mul {F : AmbientPoly n} {x y : RationalFunction n}
    (hx : RegularAlong F x) (hy : RegularAlong F y) : RegularAlong F (x * y) := by
  obtain ⟨P, T, hT, hFT, rfl⟩ := hx
  obtain ⟨Q, U, hU, hFU, rfl⟩ := hy
  exact ⟨P * Q, T * U, mul_ne_zero hT hU, hFT.mul_right hFU,
    by simp only [map_mul, mul_div_mul_comm]⟩

theorem RegularAlong.pow {F : AmbientPoly n} {x : RationalFunction n}
    (hx : RegularAlong F x) (k : ℕ) : RegularAlong F (x ^ k) := by
  induction k with
  | zero => simpa only [pow_zero] using regular_one F
  | succ k ih => simpa only [pow_succ] using ih.mul hx

theorem RegularAlong.sum {ι : Type*} {F : AmbientPoly n}
    (s : Finset ι) (z : ι → RationalFunction n)
    (hz : ∀ i ∈ s, RegularAlong F (z i)) : RegularAlong F (∑ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using regular_zero F
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hz i (Finset.mem_insert_self i s)).add
      (ih fun j hj => hz j (Finset.mem_insert_of_mem hj))

theorem regular_inv_polynomial (F T : AmbientPoly n)
    (hT : T ≠ 0) (hFT : IsRelPrime F T) :
    RegularAlong F (polynomialMap n T)⁻¹ := by
  exact ⟨1, T, hT, hFT, by simp⟩

/-- Coordinate differentiation preserves actual regularity along F;
the new legal denominator is exactly the square of the old denominator. -/
theorem RegularAlong.rationalPartial {F : AmbientPoly n} {x : RationalFunction n}
    (hx : RegularAlong F x) (i : Fin (n + 1)) :
    RegularAlong F (CycleQ2Bridge.rationalPartial n i x) := by
  obtain ⟨P, T, hT, hFT, rfl⟩ := hx
  refine ⟨pderiv i P * T - P * pderiv i T, T ^ 2,
    pow_ne_zero 2 hT, hFT.pow_right, ?_⟩
  rw [Derivation.leibniz_div]
  simp only [CycleQ2Bridge.rationalPartial_map,
    smul_eq_mul, map_sub, map_mul, map_pow, div_eq_mul_inv, inv_pow]
  ring

/-- Polynomial mixed partials commute, proved directly coefficientwise. -/
theorem polynomial_partials_commute (i j : Fin (n + 1)) (P : AmbientPoly n) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  classical
  by_cases hij : i = j
  · subst j
    rfl
  ext m
  simp only [coeff_pderiv, Finsupp.add_apply, Finsupp.single_apply,
    if_neg hij, if_neg (Ne.symm hij), add_zero]
  rw [show m + Finsupp.single i 1 + Finsupp.single j 1 =
    m + Finsupp.single j 1 + Finsupp.single i 1 by abel]
  ring

/-- The commutator is a derivation; this elementary construction avoids
requiring a Lie-algebra infrastructure import. -/
private def derivationCommutator
    (D E : Derivation ℚ (RationalFunction n) (RationalFunction n)) :
    Derivation ℚ (RationalFunction n) (RationalFunction n) :=
  Derivation.mk'
    (D.toLinearMap.comp E.toLinearMap - E.toLinearMap.comp D.toLinearMap)
    (by
      intro x y
      change D (E (x * y)) - E (D (x * y)) =
        x * (D (E y) - E (D y)) + y * (D (E x) - E (D x))
      simp only [Derivation.leibniz, smul_eq_mul, map_add]
      ring)

private theorem derivationCommutator_apply
    (D E : Derivation ℚ (RationalFunction n) (RationalFunction n))
    (z : RationalFunction n) :
    derivationCommutator D E z = D (E z) - E (D z) := rfl

/-- The actual extended coordinate derivations commute on every rational
function, with no commutation hypothesis. -/
theorem rationalPartials_commute (i j : Fin (n + 1)) :
    Function.Commute (CycleQ2Bridge.rationalPartial n i)
      (CycleQ2Bridge.rationalPartial n j) := by
  let D := derivationCommutator (CycleQ2Bridge.rationalPartial n i)
    (CycleQ2Bridge.rationalPartial n j)
  have hmap : ∀ P : AmbientPoly n, D (polynomialMap n P) = 0 := by
    intro P
    dsimp only [D]
    rw [derivationCommutator_apply]
    simp only [CycleQ2Bridge.rationalPartial_map]
    rw [polynomial_partials_commute i j P, sub_self]
  intro z
  have hz : D z = 0 := by
    obtain ⟨P, T, _hT, rfl⟩ := IsFractionRing.div_surjective (AmbientPoly n) z
    rw [Derivation.leibniz_div, hmap P, hmap T]
    simp
  exact sub_eq_zero.mp hz

end CycleQ2Regularity

#print axioms CycleQ2Regularity.RegularAlong.rationalPartial
#print axioms CycleQ2Regularity.rationalPartials_commute
end
end


/- Component: euler_lift/HorizontalPrimitiveCertificate.lean -/
section
/-!
# A homogeneous horizontal primitive gives the protected certificate

The inputs here are actual rational coefficient arrays and regular fractions.
Euler lifting supplies the polynomial numerators; the coordinate differential
identity supplies the defect; legality of one coordinate lets us remove its
factor at the generic point of F. This closes the algebraic implication from
a bounded homogeneous primitive, but does not prove that primitive exists.
-/

set_option autoImplicit false
noncomputable section

namespace CycleQ2HorizontalPrimitive

open MvPolynomial HodgeComputer CycleQ2Bridge CycleQ2Regularity
open CycleQ2EulerLift CycleQ2Cartan
open scoped BigOperators

local instance : Algebra ℚ (RationalFunction 5) := DivisionRing.toRatAlgebra
local instance : Module ℚ (RationalFunction 5) := Algebra.toModule

def boundedCoefficient (F S : AmbientPoly 5)
    (B : SkewCoefficients) (i j : Fin 6) : RationalFunction 5 :=
  polynomialMap 5 (B i j) / polynomialMap 5 (F ^ 2 * S ^ 2)

def residualCoefficient (F A S : AmbientPoly 5)
    (B : SkewCoefficients) (j : Fin 6) : RationalFunction 5 :=
  coordinate j * polynomialMap 5 A / (polynomialMap 5 F) ^ 3 -
    ∑ i, rationalPartial 5 i (boundedCoefficient F S B i j)

/-- One nonvanishing homogeneous coordinate is a unit at the generic
point of F, so regularity of its coefficient implies the localized equation. -/
theorem localizedEquation_of_regular_coefficient
    {F A D : AmbientPoly 5} {N : Fin 6 → AmbientPoly 5} (j : Fin 6)
    (hF0 : F ≠ 0) (hX : IsRelPrime F (X j))
    (hregular : RegularAlong F
      (coordinate j * rationalDefect F A 2 (rationalField D N) /
        (polynomialMap 5 F) ^ 3)) :
    LocalizedEquation F A 2 D N := by
  obtain ⟨P, T, hT, hFT, heq⟩ := hregular
  refine ⟨P, X j * T, mul_ne_zero (X_ne_zero j) hT, hX.mul_right hFT, ?_⟩
  have hF := polynomialMap_ne_zero hF0
  have hX0 := polynomialMap_ne_zero (X_ne_zero j : (X j : AmbientPoly 5) ≠ 0)
  have hT0 := polynomialMap_ne_zero hT
  simp only [coordinate] at heq
  simp only [map_mul]
  field_simp at heq ⊢
  linear_combination heq

theorem boundedCoefficient_eq_skew
    (F S : AmbientPoly 5) (B : SkewCoefficients) (N : Fin 6 → AmbientPoly 5)
    (hB : ∀ i j, B i j = X i * N j - X j * N i) (i j : Fin 6) :
    boundedCoefficient F S B i j = skewCoefficient (primitiveVector F (S ^ 2) N) i j := by
  rw [boundedCoefficient, hB]
  simp only [skewCoefficient, primitiveVector, rationalField, coordinate,
    map_sub, map_mul, div_eq_mul_inv]
  ring

/-- A concrete homogeneous horizontal coefficient array with a regular
residual gives the unchanged protected theorem, with no extra axioms. -/
theorem protected_certificate_of_horizontal_primitive
    (e : ℕ) (S : AmbientPoly 5) (B : SkewCoefficients)
    (hS : S.IsHomogeneous e) (hlegal : ¬ HodgeSubmission.F ∣ S)
    (hB : ∀ i j, (B i j).IsHomogeneous (2 * e + 8))
    (hskew : ∀ i j, B j i = -B i j)
    (hhor : ∀ l i j, X l * B i j - X i * B l j + X j * B l i = 0)
    (hregular : RegularAlong HodgeSubmission.F
      (residualCoefficient HodgeSubmission.F HodgeSubmission.A S B 0)) :
    HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A := by
  have hS0 : S ≠ 0 := by
    intro hz
    exact hlegal (hz ▸ dvd_zero _)
  have hB' : ∀ i j, (B i j).IsHomogeneous ((2 * e + 7) + 1) := by
    simpa only [Nat.add_assoc] using hB
  obtain ⟨N, hN, hwedge⟩ := exists_homogeneous_lift hB' hskew hhor
  have hDhom : (S ^ 2).IsHomogeneous (2 * e) := by
    simpa only [Nat.mul_comm] using hS.pow 2
  have hres : residualCoefficient HodgeSubmission.F HodgeSubmission.A S B 0 =
      coordinate 0 * rationalDefect HodgeSubmission.F HodgeSubmission.A 2
        (rationalField (S ^ 2) N) / (polynomialMap 5 HodgeSubmission.F)^3 := by
    unfold residualCoefficient
    simp_rw [boundedCoefficient_eq_skew HodgeSubmission.F S B N hwedge]
    exact primitive_defect_coefficient HodgeSubmission.A
      CycleQ2Workspace.originalF_homogeneous CycleQ2Workspace.originalF_ne_zero
      hDhom (pow_ne_zero 2 hS0) hN 0
  rw [hres] at hregular
  have hX : IsRelPrime HodgeSubmission.F (X (0 : Fin 6)) :=
    CycleQ2ExactIrreducible.protected_F_irreducible.isRelPrime_iff_not_dvd.mpr
      (CycleQ2SupportEquation.not_dvd_coordinate_of_degree_gt_one
        HodgeSubmission.F
        (by rw [CycleQ2Workspace.originalF_totalDegree]; norm_num) 0)
  have hlocal := localizedEquation_of_regular_coefficient 0
    CycleQ2Workspace.originalF_ne_zero hX hregular
  exact (CycleQ2Bridge.sextic_q2_hasCertificate_iff_square_primitive
    HodgeSubmission.F HodgeSubmission.A
    CycleQ2ExactIrreducible.protected_F_irreducible
    CycleQ2Workspace.originalF_homogeneous
    (Homogeneous.of_isHomogeneous CycleQ2Workspace.originalA_homogeneous)).mpr
    ⟨e, S, N, hS, hlegal, (fun i => by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
        Homogeneous.of_isHomogeneous (hN i)), hlocal⟩

end CycleQ2HorizontalPrimitive

#print axioms CycleQ2HorizontalPrimitive.protected_certificate_of_horizontal_primitive
end
end


/- Component: pole_reduction/VectorPoleReduction.lean -/
section
/-!
# Elementary pole reduction for rational primitives

This is a calculation in a genuine differential field. Subtracting an exact
lower-degree form is represented by adding the divergence of a skew array.
Commutation of the coordinate derivations proves that this changes no top
differential. When the normal contraction is divisible by f, the formula
lowers the primitive's f-pole by one. No Hodge filtration is used.
-/

set_option autoImplicit false
noncomputable section

namespace CycleQ2PoleReduction

open HodgeTestbed.Conic
open scoped BigOperators

variable {ι K : Type*} [Fintype ι] [DecidableEq ι]
variable [Field K] [CharZero K] [Algebra ℚ K]

def skewDiv (δ : ι → Derivation ℚ K K) (B : ι → ι → K) (i : ι) : K :=
  ∑ j, δ j (B i j)

/-- Commuting partial derivatives annihilate the divergence of a skew array. -/
theorem divergence_skewDiv (δ : ι → Derivation ℚ K K)
    (hcomm : ∀ i j, Function.Commute (δ i) (δ j))
    (B : ι → ι → K) (hskew : ∀ i j, B j i = -B i j) :
    fieldDivergence δ (skewDiv δ B) = 0 := by
  have hs : fieldDivergence δ (skewDiv δ B) =
      -fieldDivergence δ (skewDiv δ B) := by
    simp only [fieldDivergence, skewDiv, map_sum]
    calc
      (∑ i, ∑ j, δ i (δ j (B i j))) = ∑ i, ∑ j, δ j (δ i (B j i)) :=
        Finset.sum_comm
      _ = ∑ i, ∑ j, -δ i (δ j (B i j)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        calc
          δ j (δ i (B j i)) = δ j (δ i (-B i j)) :=
            congrArg (fun z => δ j (δ i z)) (hskew i j)
          _ = -δ i (δ j (B i j)) := by rw [map_neg, map_neg, hcomm j i]
      _ = _ := by simp only [Finset.sum_neg_distrib]
  have ht : (2 : K) * fieldDivergence δ (skewDiv δ B) = 0 := by
    linear_combination hs
  exact (mul_eq_zero.mp ht).resolve_left (by norm_num)

def coordinateSkew (r : ι) (a : ι → K) (i j : ι) : K :=
  (if j = r then a i else 0) - (if i = r then a j else 0)

theorem coordinateSkew_skew (r : ι) (a : ι → K) (i j : ι) :
    coordinateSkew r a j i = -coordinateSkew r a i j := by
  simp only [coordinateSkew]
  ring

theorem skewDiv_coordinateSkew (δ : ι → Derivation ℚ K K)
    (r : ι) (a : ι → K) (i : ι) :
    skewDiv δ (coordinateSkew r a) i =
      δ r (a i) - if i = r then fieldDivergence δ a else 0 := by
  by_cases hi : i = r
  · subst i
    simp [skewDiv, coordinateSkew, fieldDivergence,
      Finset.sum_sub_distrib, apply_ite]
  · simp [skewDiv, coordinateSkew, hi, fieldDivergence,
      Finset.sum_sub_distrib, apply_ite]

/-- Adding this correction preserves the actual top differential. -/
theorem coordinate_correction_preserves_divergence
    (δ : ι → Derivation ℚ K K)
    (hcomm : ∀ i j, Function.Commute (δ i) (δ j))
    (r : ι) (a v : ι → K) :
    fieldDivergence δ
      (fun i => v i + δ r (a i) - if i = r then fieldDivergence δ a else 0) =
      fieldDivergence δ v := by
  have hc : (fun i => v i + δ r (a i) -
      if i = r then fieldDivergence δ a else 0) =
      fun i => v i + skewDiv δ (coordinateSkew r a) i := by
    funext i
    rw [skewDiv_coordinateSkew]
    ring
  rw [hc, fieldDivergence_add, divergence_skewDiv δ hcomm _
    (coordinateSkew_skew r a), add_zero]

/-- The quotient rule in the form used by a pole-lowering correction. -/
theorem derivative_over_power (δ : Derivation ℚ K K)
    (a f : K) (p : ℕ) (hp : p ≠ 0) (hf : f ≠ 0) :
    δ (a / ((p : K) * f ^ p)) =
      δ a / ((p : K) * f ^ p) - a * δ f / f ^ (p + 1) := by
  have hp' : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have hpred : p - 1 + 1 = p := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hp)
  have hpow : f ^ (p - 1) * f = f ^ p := by rw [← pow_succ, hpred]
  simp only [Derivation.leibniz_div, Derivation.leibniz, Derivation.map_natCast,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, mul_zero, add_zero]
  simp only [pow_succ, ← hpow]
  field_simp

theorem derivative_div_power (δ : Derivation ℚ K K)
    (a f : K) (p : ℕ) (hf : f ≠ 0) :
    δ (a / f ^ p) = δ a / f ^ p - (p : K) * a * δ f / f ^ (p + 1) := by
  by_cases hp : p = 0
  · subst p
    simp
  have hp' : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have h := derivative_over_power δ ((p : K) * a) f p hp hf
  have harg : (p : K) * a / ((p : K) * f ^ p) = a / f ^ p := by field_simp
  rw [harg] at h
  simpa only [Derivation.leibniz, Derivation.map_natCast, smul_eq_mul,
    mul_zero, add_zero, mul_div_mul_left _ _ hp'] using h

theorem divergence_div_power (δ : ι → Derivation ℚ K K)
    (b : ι → K) (f : K) (p : ℕ) (hf : f ≠ 0) :
    fieldDivergence δ (fun i => b i / f ^ p) =
      fieldDivergence δ b / f ^ p -
        (p : K) * fieldAction δ b f / f ^ (p + 1) := by
  simp only [fieldDivergence, derivative_div_power _ _ _ _ hf,
    fieldAction_apply, Finset.sum_sub_distrib, ← Finset.sum_div, Finset.mul_sum]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A third-order pole in the top differential forces the normal
contraction to be divisible by f whenever the primitive has a higher pole. -/
theorem normal_divisibility_of_triple_pole
    (δ : ι → Derivation ℚ K K) (b : ι → K) (f a r : K) (p : ℕ)
    (hp : 2 ≤ p) (hf : f ≠ 0)
    (hdiv : fieldDivergence δ (fun i => b i / f ^ (p + 1)) = a / f ^ 3 + r) :
    fieldAction δ b f = f *
      ((fieldDivergence δ b - a * f ^ (p - 2) - r * f ^ (p + 1)) / (p + 1 : ℕ)) := by
  rw [divergence_div_power δ b f (p + 1) hf] at hdiv
  have hp' : ((p + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have he : p = p - 2 + 2 := by omega
  have hpow : f ^ (p + 1) = f ^ (p - 2) * f ^ 3 := by
    rw [← pow_add]
    congr 1
    omega
  have hpow2 : f ^ (p + 1 + 1) = f ^ (p - 2) * f ^ 4 := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow, hpow2] at hdiv
  rw [hpow]
  have hbase : f ^ (p - 2) ≠ 0 := pow_ne_zero _ hf
  field_simp at hdiv ⊢
  linear_combination -hdiv

def reducedNumerator (δ : ι → Derivation ℚ K K)
    (r : ι) (b : ι → K) (g c : K) (p : ℕ) (i : ι) : K :=
  if i = r then
    c / g - (∑ j ∈ Finset.univ.erase r, δ j (b j / g)) / (p : K)
  else δ r (b i / g) / (p : K)

/-- One exact pole reduction. The normal contraction hypothesis is the
leading-pole cancellation forced by a bounded top differential. -/
theorem pole_drop (δ : ι → Derivation ℚ K K)
    (hcomm : ∀ i j, Function.Commute (δ i) (δ j))
    (r : ι) (b : ι → K) (f c : K) (p : ℕ)
    (hp : p ≠ 0) (hf : f ≠ 0) (hg : δ r f ≠ 0)
    (hnormal : fieldAction δ b f = f * c) :
    fieldDivergence δ (fun i => b i / f ^ (p + 1)) =
      fieldDivergence δ
        (fun i => reducedNumerator δ r b (δ r f) c p i / f ^ p) := by
  let g := δ r f
  let a : ι → K := fun i => (b i / g) / ((p : K) * f ^ p)
  have hcor := coordinate_correction_preserves_divergence δ hcomm r a
    (fun i => b i / f ^ (p + 1))
  have heq : (fun i => b i / f ^ (p + 1) + δ r (a i) -
      if i = r then fieldDivergence δ a else 0) =
      (fun i => reducedNumerator δ r b g c p i / f ^ p) := by
    funext i
    by_cases hi : i = r
    · subst i
      have hsum : fieldDivergence δ a = δ r (a r) +
          ∑ j ∈ Finset.univ.erase r, δ j (a j) := by
        exact (Finset.add_sum_erase Finset.univ (fun j => δ j (a j))
          (Finset.mem_univ r)).symm
      rw [hsum]
      simp only [reducedNumerator, if_true]
      have hd : ∀ j, δ j (a j) = δ j (b j / g) / ((p : K) * f ^ p) -
          (b j / g) * δ j f / f ^ (p + 1) := by
        intro j
        exact derivative_over_power (δ j) (b j / g) f p hp hf
      simp only [hd, Finset.sum_sub_distrib, ← Finset.sum_div]
      have hn : b r * g + ∑ j ∈ Finset.univ.erase r, b j * δ j f = f * c := by
        rw [fieldAction_apply] at hnormal
        rw [← Finset.add_sum_erase Finset.univ (fun j => b j * δ j f)
          (Finset.mem_univ r)] at hnormal
        exact hnormal
      have hfactor : (∑ j ∈ Finset.univ.erase r, (b j / g) * δ j f) =
          (∑ j ∈ Finset.univ.erase r, b j * δ j f) / g := by
        simp only [div_eq_mul_inv, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [hfactor]
      have hp' : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp
      have hg' : g ≠ 0 := hg
      field_simp
      linear_combination (p : K) * f ^ p * hn
    · simp only [hi, if_false, sub_zero, reducedNumerator]
      change b i / f ^ (p + 1) +
        δ r ((b i / g) / ((p : K) * f ^ p)) = _
      rw [derivative_over_power (δ r) (b i / g) f p hp hf]
      have hg' : g ≠ 0 := hg
      dsimp [g]
      field_simp
      ring
  rw [heq] at hcor
  exact hcor.symm

end CycleQ2PoleReduction

#print axioms CycleQ2PoleReduction.pole_drop
end
end


/- Component: pole_reduction/PoleNormalization.lean -/
section
/-!
# Double-pole normalization over the actual fraction field

Every rational vector admits a common finite pole order along an irreducible
F. If its top differential is A/F^3 plus an F-regular remainder, repeated
elementary pole reduction gives a vector with pole order at most two.
The proof keeps the same differential and permits unrestricted additional
denominators coprime to F. It requires no Hodge-filtration strictness.
-/

set_option autoImplicit false
noncomputable section

namespace CycleQ2PoleNormalization

open MvPolynomial HodgeComputer CycleQ2Bridge CycleQ2Regularity
open HodgeTestbed.Conic CycleQ2PoleReduction
open scoped BigOperators

variable {n : ℕ}

local instance : Algebra ℚ (RationalFunction n) := DivisionRing.toRatAlgebra
local instance : Module ℚ (RationalFunction n) := Algebra.toModule

theorem regular_constant (F : AmbientPoly n) (c : ℂ) :
    RegularAlong F (polynomialMap n (C c)) := regular_polynomial F (C c)

theorem regular_nat_inverse (F : AmbientPoly n) (p : ℕ) :
    RegularAlong F ((p : RationalFunction n)⁻¹) := by
  have h := regular_constant F ((p : ℂ)⁻¹)
  have he : polynomialMap n (C ((p : ℂ)⁻¹)) = (p : RationalFunction n)⁻¹ := by
    change ((polynomialMap n).comp C) ((p : ℂ)⁻¹) = _
    rw [map_inv₀, map_natCast]
  simpa only [he] using h

/-- Extracting the maximal power of F from a denominator gives an actual
F-regular numerator and a finite pole order. -/
theorem exists_regular_pole_representation
    {F : AmbientPoly n} (hF : Irreducible F) (z : RationalFunction n) :
    ∃ (m : ℕ) (b : RationalFunction n), RegularAlong F b ∧
      z = b / (polynomialMap n F)^m := by
  obtain ⟨P, T, hT, rfl⟩ := IsFractionRing.div_surjective (AmbientPoly n) z
  have hT0 : T ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hT
  obtain ⟨m, U, hFU, hfactor⟩ := WfDvdMonoid.max_power_factor hT0 hF
  have hU : U ≠ 0 := by
    intro h
    apply hT0
    simp [hfactor, h]
  refine ⟨m, polynomialMap n P / polynomialMap n U,
    ⟨P, U, hU, hF.isRelPrime_iff_not_dvd.mpr hFU, rfl⟩, ?_⟩
  simp only [hfactor, map_mul, map_pow, div_eq_mul_inv, mul_inv_rev]
  ring

theorem exists_uniform_pole_representation
    {F : AmbientPoly n} (hF : Irreducible F)
    (v : Fin (n + 1) → RationalFunction n) :
    ∃ (m : ℕ) (b : Fin (n + 1) → RationalFunction n),
      (∀ i, RegularAlong F (b i)) ∧
      v = fun i => b i / (polynomialMap n F)^m := by
  classical
  choose m b hb heq using fun i => exists_regular_pole_representation hF (v i)
  let M := Finset.univ.sup m
  have hm : ∀ i, m i ≤ M := fun i => Finset.le_sup (Finset.mem_univ i)
  refine ⟨M, fun i => b i * (polynomialMap n F)^(M - m i),
    (fun i => (hb i).mul ((regular_polynomial F F).pow _)), ?_⟩
  funext i
  rw [heq i]
  have hF0 := polynomialMap_ne_zero hF.ne_zero
  have hpow : (polynomialMap n F)^M =
      (polynomialMap n F)^(M - m i) * (polynomialMap n F)^(m i) := by
    rw [← pow_add, Nat.sub_add_cancel (hm i)]
  rw [hpow]
  field_simp

theorem regular_divergence {F : AmbientPoly n}
    {b : Fin (n + 1) → RationalFunction n} (hb : ∀ i, RegularAlong F (b i)) :
    RegularAlong F (fieldDivergence (rationalPartial n) b) := by
  exact RegularAlong.sum Finset.univ _ (fun i _ => (hb i).rationalPartial i)

/-- The explicit new numerator remains regular along F. -/
theorem regular_reducedNumerator {F : AmbientPoly n}
    (r : Fin (n + 1)) {b : Fin (n + 1) → RationalFunction n}
    {c : RationalFunction n} (p : ℕ)
    (hb : ∀ i, RegularAlong F (b i)) (hc : RegularAlong F c)
    (hg0 : pderiv r F ≠ 0) (hg : IsRelPrime F (pderiv r F)) (i : Fin (n + 1)) :
    RegularAlong F (reducedNumerator (rationalPartial n) r b
      (rationalPartial n r (polynomialMap n F)) c p i) := by
  have hginv : RegularAlong F (rationalPartial n r (polynomialMap n F))⁻¹ := by
    rw [rationalPartial_map]
    exact regular_inv_polynomial F _ hg0 hg
  have hbdiv : ∀ j, RegularAlong F (b j /
      rationalPartial n r (polynomialMap n F)) := fun j => by
    simpa only [div_eq_mul_inv] using (hb j).mul hginv
  unfold reducedNumerator
  split
  · apply RegularAlong.sub
    · simpa only [div_eq_mul_inv] using hc.mul hginv
    · simpa only [div_eq_mul_inv] using
        (RegularAlong.sum (Finset.univ.erase r) _
          (fun j _ => (hbdiv j).rationalPartial j)).mul (regular_nat_inverse F p)
  · simpa only [div_eq_mul_inv] using
      ((hbdiv i).rationalPartial r).mul (regular_nat_inverse F p)

/-- Induction lowers an arbitrary finite pole order to two. The remainder
and the top differential are preserved exactly throughout the induction. -/
theorem normalize_pole_order
    {F : AmbientPoly n} (hF0 : F ≠ 0) (r : Fin (n + 1))
    (hg0 : pderiv r F ≠ 0) (hg : IsRelPrime F (pderiv r F))
    (a t : RationalFunction n) (ha : RegularAlong F a) (ht : RegularAlong F t)
    (m : ℕ) (b : Fin (n + 1) → RationalFunction n)
    (hb : ∀ i, RegularAlong F (b i))
    (hdiv : fieldDivergence (rationalPartial n)
      (fun i => b i / (polynomialMap n F)^m) = a / (polynomialMap n F)^3 + t) :
    ∃ c : Fin (n + 1) → RationalFunction n,
      (∀ i, RegularAlong F (c i)) ∧
      fieldDivergence (rationalPartial n)
        (fun i => c i / (polynomialMap n F)^2) = a / (polynomialMap n F)^3 + t := by
  have hf := polynomialMap_ne_zero hF0
  induction m using Nat.strong_induction_on generalizing b with
  | h m ih =>
    by_cases hm : m ≤ 2
    · refine ⟨fun i => b i * (polynomialMap n F)^(2 - m),
        (fun i => (hb i).mul ((regular_polynomial F F).pow _)), ?_⟩
      have hv : (fun i => b i * (polynomialMap n F)^(2 - m) /
          (polynomialMap n F)^2) = fun i => b i / (polynomialMap n F)^m := by
        funext i
        have hpow : (polynomialMap n F)^2 =
            (polynomialMap n F)^(2 - m) * (polynomialMap n F)^m := by
          rw [← pow_add, Nat.sub_add_cancel hm]
        rw [hpow]
        field_simp
      rw [hv]
      exact hdiv
    · obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      have hp : 2 ≤ p := by omega
      let c := (fieldDivergence (rationalPartial n) b -
        a * (polynomialMap n F)^(p - 2) - t * (polynomialMap n F)^(p + 1)) /
          ((p + 1 : ℕ) : RationalFunction n)
      have hc : RegularAlong F c := by
        exact ((regular_divergence hb).sub
          (ha.mul ((regular_polynomial F F).pow _)) |>.sub
          (ht.mul ((regular_polynomial F F).pow _))).mul (regular_nat_inverse F (p + 1))
      have hn := normal_divisibility_of_triple_pole (rationalPartial n)
        b (polynomialMap n F) a t p hp hf hdiv
      have hgnz : rationalPartial n r (polynomialMap n F) ≠ 0 := by
        rw [rationalPartial_map]
        exact polynomialMap_ne_zero hg0
      have hdrop := pole_drop (rationalPartial n) rationalPartials_commute
        r b (polynomialMap n F) c p (by omega) hf hgnz hn
      let b' := reducedNumerator (rationalPartial n) r b
        (rationalPartial n r (polynomialMap n F)) c p
      apply ih p (by omega) b'
      · exact regular_reducedNumerator r p hb hc hg0 hg
      · exact hdrop.symm.trans hdiv

/-- Unrestricted rational primitives can always be normalized to double
poles along F. This is an existence theorem about an actual differential,
and does not assert that the initial rational primitive exists. -/
theorem double_pole_primitive_of_rational_primitive
    {F : AmbientPoly n} (hF : Irreducible F) (r : Fin (n + 1))
    (hg0 : pderiv r F ≠ 0) (hg : IsRelPrime F (pderiv r F))
    (a t : RationalFunction n) (ha : RegularAlong F a) (ht : RegularAlong F t)
    (v : Fin (n + 1) → RationalFunction n)
    (hdiv : fieldDivergence (rationalPartial n) v =
      a / (polynomialMap n F)^3 + t) :
    ∃ c : Fin (n + 1) → RationalFunction n,
      (∀ i, RegularAlong F (c i)) ∧
      fieldDivergence (rationalPartial n)
        (fun i => c i / (polynomialMap n F)^2) = a / (polynomialMap n F)^3 + t := by
  obtain ⟨m, b, hb, hv⟩ := exists_uniform_pole_representation hF v
  rw [hv] at hdiv
  exact normalize_pole_order hF.ne_zero r hg0 hg a t ha ht m b hb hdiv

end CycleQ2PoleNormalization

#print axioms CycleQ2PoleNormalization.double_pole_primitive_of_rational_primitive
end
end


/- Component: pole_reduction/ResiduePrimitiveClosure.lean -/
section
/-!
An explicit algebraic closure of a second normal-residue primitive.

The source coefficient and weighted residue divergence are the actual
definitions from the protected HigherResidues and HoldoutCover libraries.
The construction below derives its complete pole-two defect; the defect
identity is not an input. An application still has to prove existence of
the residue primitive and regularity of its lifts along the hypersurface.
-/

noncomputable section
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

namespace CycleQ2ResidueClosure

open HoldoutConstruction SplitHigherResidue
open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]
variable {ι : Type*} [Fintype ι]

/-- Tangent derivations obtained from the actual ambient coordinate derivatives. -/
def ambientTangent (D₀ : Derivation ℤ K K) (D : ι → Derivation ℤ K K)
    (f : K) (i : ι) : Derivation ℤ K K :=
  D i - (D i f / D₀ f) • D₀

@[simp] theorem ambientTangent_apply (D₀ : Derivation ℤ K K)
    (D : ι → Derivation ℤ K K) (f x : K) (i : ι) :
    ambientTangent D₀ D f i x = D i x - D i f / D₀ f * D₀ x := rfl

theorem ambientTangent_f (D₀ : Derivation ℤ K K)
    (D : ι → Derivation ℤ K K) (f : K) (hg : D₀ f ≠ 0) (i : ι) :
    ambientTangent D₀ D f i f = 0 := by
  rw [ambientTangent_apply]
  field_simp
  ring

/-- The existing second normal source is the second differentiated density. -/
theorem normalSourceTwo_eq_derivative (D₀ : Derivation ℤ K K)
    (a g : K) (hg : g ≠ 0) :
    normalSourceTwo a (D₀ a) (D₀ (D₀ a)) g (D₀ g) (D₀ (D₀ g)) =
      D₀ (D₀ (a / g) / (2 * g)) := by
  have htwo : D₀ (2 : K) = 0 := D₀.map_natCast 2
  simp only [normalSourceTwo, Derivation.leibniz_div, Derivation.leibniz_inv,
    Derivation.leibniz, Derivation.leibniz_pow, map_sub, map_add,
    htwo, smul_eq_mul, nsmul_eq_mul]
  ring_nf
  field_simp [hg]
  ring

private theorem half_density_derivative (D₀ : Derivation ℤ K K)
    (a g : K) (hg : g ≠ 0) :
    D₀ (a / (2 * g)) = D₀ (a / g) / 2 := by
  have htwo : D₀ (2 : K) = 0 := D₀.map_natCast 2
  simp only [Derivation.leibniz_div, Derivation.leibniz,
    htwo, smul_eq_mul]
  field_simp [hg]
  ring

/-- The normal component of the rational vector field. -/
def closureNormal (D₀ : Derivation ℤ K K) (D : ι → Derivation ℤ K K)
    (f a : K) (w : ι → K) : K :=
  a / (2 * D₀ f) + f * (D₀ (a / D₀ f) / (2 * D₀ f) -
    ∑ i, D i f * w i / D₀ f)

/-- The tangent ambient components of the rational vector field. -/
def closureTangent (f : K) (w : ι → K) (i : ι) : K := f * w i

theorem closure_action (D₀ : Derivation ℤ K K)
    (D : ι → Derivation ℤ K K) (f a : K) (w : ι → K)
    (hg : D₀ f ≠ 0) :
    2 * (closureNormal D₀ D f a w * D₀ f +
      ∑ i, closureTangent f w i * D i f) = a + f * D₀ (a / D₀ f) := by
  unfold closureNormal closureTangent
  rw [← Finset.sum_div]
  have hs : (∑ i, f * w i * D i f) = f * ∑ i, D i f * w i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  field_simp
  ring

private theorem tangent_quotient_derivative (D₀ : Derivation ℤ K K)
    (D : ι → Derivation ℤ K K) (f : K) (w : ι → K)
    (hg : D₀ f ≠ 0) (mixed : ∀ i, D₀ (D i f) = D i (D₀ f)) (i : ι) :
    D i (w i) - D₀ (D i f * w i / D₀ f) =
      ambientTangent D₀ D f i (w i) -
        w i * ambientTangent D₀ D f i (D₀ f) / D₀ f := by
  simp only [ambientTangent_apply, Derivation.leibniz_div,
    Derivation.leibniz, smul_eq_mul, mixed]
  field_simp
  ring

theorem closure_divergence (D₀ : Derivation ℤ K K)
    (D : ι → Derivation ℤ K K) (f a : K) (w : ι → K)
    (hg : D₀ f ≠ 0) (mixed : ∀ i, D₀ (D i f) = D i (D₀ f)) :
    D₀ (closureNormal D₀ D f a w) + ∑ i, D i (closureTangent f w i) =
      D₀ (a / D₀ f) + f *
        (normalSourceTwo a (D₀ a) (D₀ (D₀ a))
          (D₀ f) (D₀ (D₀ f)) (D₀ (D₀ (D₀ f))) +
          residueDivergence (ambientTangent D₀ D f) (D₀ f) w) := by
  have hs : (∑ i, D i (w i)) - ∑ i, D₀ (D i f * w i / D₀ f) =
      residueDivergence (ambientTangent D₀ D f) (D₀ f) w := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [tangent_quotient_derivative D₀ D f w hg mixed]
    simp only [residueDivergence, fieldDivergence, Finset.sum_sub_distrib,
      Finset.sum_div]
  rw [normalSourceTwo_eq_derivative D₀ a (D₀ f) hg]
  unfold closureNormal closureTangent
  simp only [map_add, map_sub, map_sum, Derivation.leibniz, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [half_density_derivative D₀ a (D₀ f) hg]
  rw [← hs]
  rw [← Finset.sum_div]
  have hswap : (∑ i, w i * D i f) = ∑ i, D i f * w i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hswap]
  field_simp [hg]
  ring

/-- The complete pole-two defect of the explicitly constructed field. -/
theorem closure_defect (D₀ : Derivation ℤ K K)
    (D : ι → Derivation ℤ K K) (f a : K) (w : ι → K)
    (hg : D₀ f ≠ 0) (mixed : ∀ i, D₀ (D i f) = D i (D₀ f)) :
    a - 2 * (closureNormal D₀ D f a w * D₀ f +
      ∑ i, closureTangent f w i * D i f) +
      f * (D₀ (closureNormal D₀ D f a w) +
        ∑ i, D i (closureTangent f w i)) =
      f ^ 2 *
        (normalSourceTwo a (D₀ a) (D₀ (D₀ a))
          (D₀ f) (D₀ (D₀ f)) (D₀ (D₀ (D₀ f))) +
          residueDivergence (ambientTangent D₀ D f) (D₀ f) w) := by
  rw [closure_action D₀ D f a w hg, closure_divergence D₀ D f a w hg mixed]
  ring

/-- Vanishing of the residue equation modulo f gives third-order divisibility. -/
theorem closure_defect_of_residue (D₀ : Derivation ℤ K K)
    (D : ι → Derivation ℤ K K) (f a : K) (w : ι → K) (t : K)
    (hg : D₀ f ≠ 0) (mixed : ∀ i, D₀ (D i f) = D i (D₀ f))
    (residue : normalSourceTwo a (D₀ a) (D₀ (D₀ a))
        (D₀ f) (D₀ (D₀ f)) (D₀ (D₀ (D₀ f))) +
        residueDivergence (ambientTangent D₀ D f) (D₀ f) w = f * t) :
    a - 2 * (closureNormal D₀ D f a w * D₀ f +
      ∑ i, closureTangent f w i * D i f) +
      f * (D₀ (closureNormal D₀ D f a w) +
        ∑ i, D i (closureTangent f w i)) = f ^ 3 * t := by
  rw [closure_defect D₀ D f a w hg mixed, residue]
  ring

/-- Commuting actual coordinate derivations supply the required mixed identity. -/
theorem closure_defect_of_commute (D₀ : Derivation ℤ K K)
    (D : ι → Derivation ℤ K K) (f a : K) (w : ι → K)
    (hg : D₀ f ≠ 0) (commute : ∀ i, Function.Commute D₀ (D i)) :
    a - 2 * (closureNormal D₀ D f a w * D₀ f +
      ∑ i, closureTangent f w i * D i f) +
      f * (D₀ (closureNormal D₀ D f a w) +
        ∑ i, D i (closureTangent f w i)) =
      f ^ 2 *
        (normalSourceTwo a (D₀ a) (D₀ (D₀ a))
          (D₀ f) (D₀ (D₀ f)) (D₀ (D₀ (D₀ f))) +
          residueDivergence (ambientTangent D₀ D f) (D₀ f) w) :=
  closure_defect D₀ D f a w hg (fun i => commute i f)

#print axioms normalSourceTwo_eq_derivative
#print axioms closure_defect
#print axioms closure_defect_of_residue

end CycleQ2ResidueClosure
end
end


/- Component: pole_reduction/ActualResidueClosure.lean -/
section
/-!
The direct q2 residue-primitive closure bound to actual polynomial fraction
fields, actual coordinate partial derivatives, and actual legal-denominator
regularity. Existence of the residue primitive is deliberately not asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace CycleQ2ActualResidueClosure

open MvPolynomial HodgeComputer CycleQ2Bridge CycleQ2Regularity
open HoldoutConstruction SplitHigherResidue CycleQ2ResidueClosure
open scoped BigOperators

variable {n : ℕ}

local instance rationalFunctionRatAlgebra (n : ℕ) : Algebra ℚ (RationalFunction n) :=
  DivisionRing.toRatAlgebra

local instance rationalFunctionRatModule (n : ℕ) : Module ℚ (RationalFunction n) :=
  Algebra.toModule

local instance rationalFunctionIntAlgebra (n : ℕ) : Algebra ℤ (RationalFunction n) :=
  Ring.toIntAlgebra _

/-- The actual extended partial, in the integer-linear trusted residue API. -/
def partialZ (n : ℕ) (i : Fin (n + 1)) :
    Derivation ℤ (RationalFunction n) (RationalFunction n) :=
  Derivation.mk' (rationalPartial n i).toLinearMap.toAddMonoidHom.toIntLinearMap
    (by
      intro x y
      exact (rationalPartial n i).leibniz x y)

@[simp] theorem partialZ_apply (i : Fin (n + 1)) (z : RationalFunction n) :
    partialZ n i z = rationalPartial n i z := rfl

@[simp] theorem partialZ_map (i : Fin (n + 1)) (P : AmbientPoly n) :
    partialZ n i (polynomialMap n P) = polynomialMap n (pderiv i P) :=
  rationalPartial_map i P

theorem partialZ_commute (i j : Fin (n + 1)) :
    Function.Commute (partialZ n i) (partialZ n j) :=
  rationalPartials_commute i j

/-- The actual ambient tangent derivations, with coordinate zero eliminated. -/
def actualTangent (F : AmbientPoly n) (j : Fin n) :
    Derivation ℤ (RationalFunction n) (RationalFunction n) :=
  ambientTangent (partialZ n 0) (fun i : Fin n => partialZ n i.succ)
    (polynomialMap n F) j

@[simp] theorem actualTangent_apply (F : AmbientPoly n) (j : Fin n)
    (z : RationalFunction n) :
    actualTangent F j z = rationalPartial n j.succ z -
      polynomialMap n (pderiv j.succ F) / polynomialMap n (pderiv 0 F) *
        rationalPartial n 0 z := by
  simp only [actualTangent, ambientTangent_apply, partialZ_apply, rationalPartial_map]

/-- The actual second normal source for the polynomial numerator. -/
def actualNormalSource (F A : AmbientPoly n) : RationalFunction n :=
  normalSourceTwo (polynomialMap n A) (polynomialMap n (pderiv 0 A))
    (polynomialMap n (pderiv 0 (pderiv 0 A)))
    (polynomialMap n (pderiv 0 F))
    (polynomialMap n (pderiv 0 (pderiv 0 F)))
    (polynomialMap n (pderiv 0 (pderiv 0 (pderiv 0 F))))

def actualResidueExpression (F A : AmbientPoly n) (w : Fin n → RationalFunction n) :
    RationalFunction n :=
  actualNormalSource F A +
    residueDivergence (actualTangent F) (polynomialMap n (pderiv 0 F)) w

/-- The explicit ambient rational vector field supplied by a lifted residue primitive. -/
def actualClosureVector (F A : AmbientPoly n) (w : Fin n → RationalFunction n) :
    Fin (n + 1) → RationalFunction n :=
  Fin.cases
    (closureNormal (partialZ n 0) (fun i : Fin n => partialZ n i.succ)
      (polynomialMap n F) (polynomialMap n A) w)
    (closureTangent (polynomialMap n F) w)

theorem actualClosureVector_zero (F A : AmbientPoly n)
    (w : Fin n → RationalFunction n) :
    actualClosureVector F A w 0 =
      polynomialMap n A / (2 * polynomialMap n (pderiv 0 F)) +
      polynomialMap n F *
        (rationalPartial n 0 (polynomialMap n A / polynomialMap n (pderiv 0 F)) /
          (2 * polynomialMap n (pderiv 0 F)) -
          ∑ i, polynomialMap n (pderiv i.succ F) * w i /
            polynomialMap n (pderiv 0 F)) := by
  simp only [actualClosureVector, Fin.cases_zero, closureNormal,
    partialZ_apply, rationalPartial_map]

@[simp] theorem actualClosureVector_succ (F A : AmbientPoly n)
    (w : Fin n → RationalFunction n) (i : Fin n) :
    actualClosureVector F A w i.succ = polynomialMap n F * w i := rfl

/-- The actual protected rational defect equals f² times the actual residue expression. -/
theorem actualClosure_defect (F A : AmbientPoly n)
    (w : Fin n → RationalFunction n) (hg : pderiv 0 F ≠ 0) :
    rationalDefect F A 2 (actualClosureVector F A w) =
      polynomialMap n F ^ 2 * actualResidueExpression F A w := by
  have ht : actualTangent F = ambientTangent (partialZ n 0)
      (fun i : Fin n => partialZ n i.succ) (polynomialMap n F) := rfl
  unfold actualResidueExpression
  rw [ht]
  have h := closure_defect_of_commute (partialZ n 0)
    (fun i : Fin n => partialZ n i.succ) (polynomialMap n F) (polynomialMap n A) w
    (by simpa only [partialZ_map] using polynomialMap_ne_zero hg)
    (fun i => partialZ_commute 0 i.succ)
  simpa only [rationalDefect, HodgeTestbed.Conic.fieldAction_apply,
    HodgeTestbed.Conic.fieldDivergence, Fin.sum_univ_succ,
    actualClosureVector, Fin.cases_zero, Fin.cases_succ, partialZ_apply,
    rationalPartial_map, actualNormalSource,
    Nat.cast_ofNat] using h

theorem actualClosure_defect_of_residue (F A : AmbientPoly n)
    (w : Fin n → RationalFunction n) (t : RationalFunction n)
    (hg : pderiv 0 F ≠ 0)
    (hres : actualResidueExpression F A w = polynomialMap n F * t) :
    rationalDefect F A 2 (actualClosureVector F A w) = polynomialMap n F ^ 3 * t := by
  rw [actualClosure_defect F A w hg, hres]
  ring

private theorem regular_two_inv (F : AmbientPoly n) :
    RegularAlong F (2 : RationalFunction n)⁻¹ := by
  have hu : IsUnit (2 : AmbientPoly n) := by
    simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℂ) ≠ 0)).map
      (C : ℂ →+* AmbientPoly n)
  simpa only [map_ofNat] using
    regular_inv_polynomial F 2 (by norm_num) hu.isRelPrime_right

private theorem regular_div_normal {F : AmbientPoly n} {z : RationalFunction n}
    (hz : RegularAlong F z) (hg : pderiv 0 F ≠ 0)
    (hlegal : IsRelPrime F (pderiv 0 F)) :
    RegularAlong F (z / polynomialMap n (pderiv 0 F)) := by
  simpa only [div_eq_mul_inv] using
    hz.mul (regular_inv_polynomial F _ hg hlegal)

private theorem regular_div_two_normal {F : AmbientPoly n} {z : RationalFunction n}
    (hz : RegularAlong F z) (hg : pderiv 0 F ≠ 0)
    (hlegal : IsRelPrime F (pderiv 0 F)) :
    RegularAlong F (z / (2 * polynomialMap n (pderiv 0 F))) := by
  simpa only [div_eq_mul_inv, mul_inv, mul_assoc] using
    (hz.mul (regular_two_inv F)).mul (regular_inv_polynomial F _ hg hlegal)

theorem regular_actualTangent {F : AmbientPoly n} {z : RationalFunction n}
    (hz : RegularAlong F z) (hg : pderiv 0 F ≠ 0)
    (hlegal : IsRelPrime F (pderiv 0 F)) (j : Fin n) :
    RegularAlong F (actualTangent F j z) := by
  rw [actualTangent_apply]
  exact (hz.rationalPartial j.succ).sub
    ((regular_div_normal (regular_polynomial F _) hg hlegal).mul
      (hz.rationalPartial 0))

theorem regular_actualNormalSource (F A : AmbientPoly n)
    (hg : pderiv 0 F ≠ 0) (hlegal : IsRelPrime F (pderiv 0 F)) :
    RegularAlong F (actualNormalSource F A) := by
  have hh := normalSourceTwo_eq_derivative (partialZ n 0)
    (polynomialMap n A) (polynomialMap n (pderiv 0 F)) (polynomialMap_ne_zero hg)
  simp only [partialZ_apply, rationalPartial_map] at hh
  unfold actualNormalSource
  rw [hh]
  exact (regular_div_two_normal
    ((regular_div_normal (regular_polynomial F A) hg hlegal).rationalPartial 0)
    hg hlegal).rationalPartial 0

theorem regular_actualResidueExpression (F A : AmbientPoly n)
    (w : Fin n → RationalFunction n) (hg : pderiv 0 F ≠ 0)
    (hlegal : IsRelPrime F (pderiv 0 F))
    (hw : ∀ j, RegularAlong F (w j)) :
    RegularAlong F (actualResidueExpression F A w) := by
  unfold actualResidueExpression
  apply (regular_actualNormalSource F A hg hlegal).add
  unfold residueDivergence HoldoutConstruction.fieldDivergence
  exact (RegularAlong.sum Finset.univ _ (fun i _ =>
    regular_actualTangent (hw i) hg hlegal i)).sub
    (regular_div_normal (RegularAlong.sum Finset.univ _ (fun i _ =>
      (hw i).mul (regular_actualTangent (regular_polynomial F _) hg hlegal i)))
      hg hlegal)

/-- Every output component has a genuine denominator relatively prime to F. -/
theorem regular_actualClosureVector (F A : AmbientPoly n)
    (w : Fin n → RationalFunction n) (hg : pderiv 0 F ≠ 0)
    (hlegal : IsRelPrime F (pderiv 0 F))
    (hw : ∀ j, RegularAlong F (w j)) (i : Fin (n + 1)) :
    RegularAlong F (actualClosureVector F A w i) := by
  induction i using Fin.cases with
  | zero =>
    rw [actualClosureVector_zero]
    exact (regular_div_two_normal (regular_polynomial F A) hg hlegal).add
      ((regular_polynomial F F).mul
        ((regular_div_two_normal
          ((regular_div_normal (regular_polynomial F A) hg hlegal).rationalPartial 0)
          hg hlegal).sub
          (RegularAlong.sum Finset.univ _ (fun j _ =>
            regular_div_normal ((regular_polynomial F _).mul (hw j)) hg hlegal))))
  | succ j =>
    rw [actualClosureVector_succ]
    exact (regular_polynomial F F).mul (hw j)

end CycleQ2ActualResidueClosure

#print axioms CycleQ2ActualResidueClosure.actualClosure_defect
#print axioms CycleQ2ActualResidueClosure.regular_actualClosureVector
end
end


/- Component: pole_reduction/HypersurfaceDerivations.lean -/
section
/-!
# Actual tangent derivations of the protected affine cone

The coordinate ring is the actual quotient C[Z0,...,Z5]/(F), and its
function field is its actual fraction field. This is the dimension-five
affine cone function field, not the dimension-four projective function field.
The trusted generic quotient/fraction derivation construction is specialized
to these rings, with all its hypotheses proved for the exact protected F.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace CycleQ2Hypersurface

open MvPolynomial HodgeComputer

abbrev ConeCoordinateRing := AmbientPoly 5 ⧸ Ideal.span {HodgeSubmission.F}

instance coneCoordinateRing_isDomain : IsDomain ConeCoordinateRing :=
  CycleQ2ExactIrreducible.protected_F_quotient_isDomain

abbrev ConeFunctionField := FractionRing ConeCoordinateRing

local instance coneFunctionFieldIntAlgebra : Algebra ℤ ConeFunctionField :=
  Ring.toIntAlgebra _

/-- Actual projection to the protected cone's coordinate ring. -/
def coneProjection : AmbientPoly 5 →+* ConeCoordinateRing := Ideal.Quotient.mk _

theorem coneProjection_surjective : Function.Surjective coneProjection :=
  Ideal.Quotient.mk_surjective

theorem coneProjection_kernel (P : AmbientPoly 5) :
    coneProjection P = 0 ↔ HodgeSubmission.F ∣ P := by
  simp only [coneProjection, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

/-- Actual polynomial class in the protected cone's function field. -/
def coneMap : AmbientPoly 5 →+* ConeFunctionField :=
  (algebraMap ConeCoordinateRing ConeFunctionField).comp coneProjection

theorem coneMap_kernel (P : AmbientPoly 5) :
    coneMap P = 0 ↔ HodgeSubmission.F ∣ P := by
  constructor
  · intro h
    apply (coneProjection_kernel P).mp
    apply IsFractionRing.injective ConeCoordinateRing ConeFunctionField
    simpa only [coneMap, RingHom.comp_apply, map_zero] using h
  · intro h
    change algebraMap ConeCoordinateRing ConeFunctionField (coneProjection P) = 0
    rw [(coneProjection_kernel P).mpr h, map_zero]

@[simp] theorem coneMap_F : coneMap HodgeSubmission.F = 0 :=
  (coneMap_kernel _).mpr (dvd_refl _)

/-- A concrete smooth point on the protected affine cone. -/
def normalPoint : Fin 6 → ℂ := ![1, Complex.I, 0, 0, 0, 0]

@[simp] theorem normalPoint_zero : normalPoint 0 = 1 := rfl
@[simp] theorem normalPoint_one : normalPoint 1 = Complex.I := rfl
@[simp] theorem normalPoint_two : normalPoint 2 = 0 := rfl
@[simp] theorem normalPoint_three : normalPoint 3 = 0 := rfl
@[simp] theorem normalPoint_four : normalPoint 4 = 0 := rfl
@[simp] theorem normalPoint_five : normalPoint 5 = 0 := rfl

theorem eval_normalPoint_F : eval normalPoint HodgeSubmission.F = 0 := by
  have hI : Complex.I ^ 6 = (-1 : ℂ) := by
    calc
      _ = (Complex.I ^ 2) ^ 3 := by ring
      _ = -1 := by rw [Complex.I_sq]; norm_num
  norm_num [HodgeSubmission.F, hI]

theorem eval_normalPoint_partial :
    eval normalPoint (pderiv 0 HodgeSubmission.F) = 6 := by
  rw [CycleQ2ExactNonsingular.eval_pderiv_F]
  norm_num [CycleQ2ExactNonsingular.gradientValue]

theorem protected_F_not_dvd_normal :
    ¬ HodgeSubmission.F ∣ pderiv 0 HodgeSubmission.F := by
  intro h
  have hh := map_dvd (eval normalPoint) h
  rw [eval_normalPoint_F, eval_normalPoint_partial] at hh
  norm_num at hh

/-- The normal derivative is nonzero in the actual cone function field. -/
theorem normal_ne_zero : coneMap (pderiv 0 HodgeSubmission.F) ≠ 0 := by
  intro h
  exact protected_F_not_dvd_normal ((coneMap_kernel _).mp h)

/-- Polynomial coordinate partials in the integer-linear interface used by
the trusted residue derivation construction. -/
def polynomialPartial (i : Fin 6) : Derivation ℤ (AmbientPoly 5) (AmbientPoly 5) :=
  (MvPolynomial.pderiv i).restrictScalars ℤ

@[simp] theorem polynomialPartial_apply (i : Fin 6) (P : AmbientPoly 5) :
    polynomialPartial i P = pderiv i P := rfl

theorem polynomialPartials_commute (i j : Fin 6) (P : AmbientPoly 5) :
    polynomialPartial i (polynomialPartial j P) =
      polynomialPartial j (polynomialPartial i P) :=
  CycleQ2Regularity.polynomial_partials_commute i j P

/-- The five actual tangent derivations, obtained by descent through (F)
followed by fraction-field extension. Coordinate zero is the eliminated normal. -/
def coneTangent (j : Fin 5) : Derivation ℤ ConeFunctionField ConeFunctionField :=
  HoldoutConstruction.residueTangent (K := ConeFunctionField)
    coneProjection coneProjection_surjective (polynomialPartial 0)
    (polynomialPartial j.succ) HodgeSubmission.F coneProjection_kernel normal_ne_zero

/-- The actual tangent derivative has the implicit-coordinate formula on
every polynomial class. -/
theorem coneTangent_apply (j : Fin 5) (P : AmbientPoly 5) :
    coneTangent j (coneMap P) = coneMap (pderiv j.succ P) -
      coneMap (pderiv j.succ HodgeSubmission.F) /
        coneMap (pderiv 0 HodgeSubmission.F) * coneMap (pderiv 0 P) :=
  HoldoutConstruction.residueTangent_apply (K := ConeFunctionField)
    coneProjection coneProjection_surjective (polynomialPartial 0)
    (polynomialPartial j.succ) HodgeSubmission.F coneProjection_kernel normal_ne_zero P

@[simp] theorem coneTangent_F (j : Fin 5) :
    coneTangent j (coneMap HodgeSubmission.F) = 0 := by
  rw [coneMap_F, map_zero]

/-- All five constructed tangent derivations commute on the entire actual
cone function field; no derivative-compatibility assumption remains. -/
theorem coneTangents_commute (i j : Fin 5) :
    Function.Commute (coneTangent i) (coneTangent j) :=
  HoldoutConstruction.residueTangent_commute (K := ConeFunctionField)
    coneProjection coneProjection_surjective (polynomialPartial 0)
    (polynomialPartial i.succ) (polynomialPartial j.succ) HodgeSubmission.F
    coneProjection_kernel normal_ne_zero (polynomialPartials_commute i.succ 0)
    (polynomialPartials_commute j.succ 0) (polynomialPartials_commute i.succ j.succ)

@[simp] theorem coneTangent_constant (j : Fin 5) (c : ℂ) :
    coneTangent j (coneMap (C c)) = 0 := by
  rw [coneTangent_apply]
  simp

/-- The independent coordinate classes have the expected Kronecker derivatives. -/
theorem coneTangent_coordinate (i j : Fin 5) :
    coneTangent i (coneMap (X j.succ)) = if j = i then 1 else 0 := by
  rw [coneTangent_apply]
  simp [pderiv_X, Pi.single_apply, Fin.succ_ne_zero]

/-- The eliminated coordinate differentiates by the implicit equation. -/
theorem coneTangent_normalCoordinate (i : Fin 5) :
    coneTangent i (coneMap (X 0)) =
      -coneMap (pderiv i.succ HodgeSubmission.F) /
        coneMap (pderiv 0 HodgeSubmission.F) := by
  rw [coneTangent_apply]
  simp [pderiv_X, Pi.single_apply, Fin.succ_ne_zero, div_eq_mul_inv]

end CycleQ2Hypersurface

#print axioms CycleQ2Hypersurface.normal_ne_zero
#print axioms CycleQ2Hypersurface.coneTangent_apply
#print axioms CycleQ2Hypersurface.coneTangents_commute
end
end


/- Component: pole_reduction/RegularResidue.lean -/
section
/-!
# Actual residue homomorphism along the protected hypersurface

The domain is the actual subring of ambient fractions admitting a denominator
relatively prime to F. The target is the actual fraction field of C[Z]/(F).
The representative-choice map is proved independent by cross multiplication.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace CycleQ2Residue

open MvPolynomial HodgeComputer CycleQ2Bridge CycleQ2Regularity CycleQ2Hypersurface

abbrev Poly := AmbientPoly 5
abbrev RatFun := RationalFunction 5

/-- The actual ring of ambient rational functions regular along F. -/
def RegularAtF : Subring RatFun where
  carrier := {z | RegularAlong HodgeSubmission.F z}
  zero_mem' := regular_zero _
  one_mem' := regular_one _
  add_mem' := fun hx hy => hx.add hy
  mul_mem' := fun hx hy => hx.mul hy
  neg_mem' := fun hx => hx.neg

private def presentationNumerator (z : RegularAtF) : Poly :=
  Classical.choose z.property

private def presentationDenominator (z : RegularAtF) : Poly :=
  Classical.choose (Classical.choose_spec z.property)

private theorem presentation_spec (z : RegularAtF) :
    presentationDenominator z ≠ 0 ∧
    IsRelPrime HodgeSubmission.F (presentationDenominator z) ∧
    (z : RatFun) = polynomialMap 5 (presentationNumerator z) /
      polynomialMap 5 (presentationDenominator z) :=
  Classical.choose_spec (Classical.choose_spec z.property)

/-- Every legal ambient denominator maps to a nonzero cone-function-field element. -/
theorem legal_coneMap_ne_zero (T : Poly) (hT : IsRelPrime HodgeSubmission.F T) :
    coneMap T ≠ 0 := by
  intro h
  exact (CycleQ2ExactIrreducible.protected_F_irreducible.isRelPrime_iff_not_dvd.mp hT)
    ((coneMap_kernel T).mp h)

private def residueValue (z : RegularAtF) : ConeFunctionField :=
  coneMap (presentationNumerator z) / coneMap (presentationDenominator z)

/-- Representative independence uses the injective ambient fraction map and
polynomial cross multiplication, not a chosen representative axiom. -/
private theorem residueValue_eq (z : RegularAtF) (P T : Poly)
    (hT : T ≠ 0) (hFT : IsRelPrime HodgeSubmission.F T)
    (hz : (z : RatFun) = polynomialMap 5 P / polynomialMap 5 T) :
    residueValue z = coneMap P / coneMap T := by
  have hs := presentation_spec z
  have hcross : presentationNumerator z * T = P * presentationDenominator z := by
    apply polynomialMap_injective
    simpa only [map_mul] using
      (div_eq_div_iff (polynomialMap_ne_zero hs.1) (polynomialMap_ne_zero hT)).mp
        (hs.2.2.symm.trans hz)
  apply (div_eq_div_iff
    (legal_coneMap_ne_zero _ hs.2.1) (legal_coneMap_ne_zero T hFT)).mpr
  simpa only [map_mul] using congrArg coneMap hcross

private theorem residueValue_zero : residueValue 0 = 0 := by
  simpa using residueValue_eq 0 0 1 one_ne_zero isRelPrime_one_right (by simp)

private theorem residueValue_one : residueValue 1 = 1 := by
  simpa using residueValue_eq 1 1 1 one_ne_zero isRelPrime_one_right (by simp)

private theorem residueValue_add (x y : RegularAtF) :
    residueValue (x + y) = residueValue x + residueValue y := by
  obtain ⟨P, T, hT, hFT, hx⟩ := x.property
  obtain ⟨Q, U, hU, hFU, hy⟩ := y.property
  have hxy : ((x + y : RegularAtF) : RatFun) =
      polynomialMap 5 (P * U + Q * T) / polynomialMap 5 (T * U) := by
    change (x : RatFun) + (y : RatFun) = _
    rw [hx, hy]
    have hT' := polynomialMap_ne_zero hT
    have hU' := polynomialMap_ne_zero hU
    simp only [map_add, map_mul]
    field_simp
  rw [residueValue_eq _ _ _ (mul_ne_zero hT hU) (hFT.mul_right hFU) hxy,
    residueValue_eq x P T hT hFT hx, residueValue_eq y Q U hU hFU hy]
  have hT' := legal_coneMap_ne_zero T hFT
  have hU' := legal_coneMap_ne_zero U hFU
  simp only [map_add, map_mul]
  field_simp

private theorem residueValue_mul (x y : RegularAtF) :
    residueValue (x * y) = residueValue x * residueValue y := by
  obtain ⟨P, T, hT, hFT, hx⟩ := x.property
  obtain ⟨Q, U, hU, hFU, hy⟩ := y.property
  have hxy : ((x * y : RegularAtF) : RatFun) =
      polynomialMap 5 (P * Q) / polynomialMap 5 (T * U) := by
    change (x : RatFun) * (y : RatFun) = _
    rw [hx, hy]
    simp only [map_mul, mul_div_mul_comm]
  rw [residueValue_eq _ _ _ (mul_ne_zero hT hU) (hFT.mul_right hFU) hxy,
    residueValue_eq x P T hT hFT hx, residueValue_eq y Q U hU hFU hy]
  simp only [map_mul, mul_div_mul_comm]

/-- The actual residue homomorphism from the regular subring to the protected
cone function field. All ring-homomorphism laws are proved above. -/
def residue : RegularAtF →+* ConeFunctionField where
  toFun := residueValue
  map_zero' := residueValue_zero
  map_one' := residueValue_one
  map_add' := residueValue_add
  map_mul' := residueValue_mul

theorem residue_fraction (z : RegularAtF) (P T : Poly)
    (hT : T ≠ 0) (hFT : IsRelPrime HodgeSubmission.F T)
    (hz : (z : RatFun) = polynomialMap 5 P / polynomialMap 5 T) :
    residue z = coneMap P / coneMap T :=
  residueValue_eq z P T hT hFT hz

/-- A polynomial viewed in the regular ambient subring. -/
def polynomialRegular (P : Poly) : RegularAtF :=
  ⟨polynomialMap 5 P, regular_polynomial HodgeSubmission.F P⟩

@[simp] theorem residue_polynomial (P : Poly) :
    residue (polynomialRegular P) = coneMap P := by
  simpa using residue_fraction (polynomialRegular P) P 1
    one_ne_zero isRelPrime_one_right (by simp [polynomialRegular])

theorem residue_fraction_eq_zero_iff (z : RegularAtF) (P T : Poly)
    (hT : T ≠ 0) (hFT : IsRelPrime HodgeSubmission.F T)
    (hz : (z : RatFun) = polynomialMap 5 P / polynomialMap 5 T) :
    residue z = 0 ↔ HodgeSubmission.F ∣ P := by
  rw [residue_fraction z P T hT hFT hz]
  have hT' := legal_coneMap_ne_zero T hFT
  rw [div_eq_zero_iff]
  simp only [hT', or_false]
  exact coneMap_kernel P

/-- The actual residue kernel is exactly multiplication by F inside the
regular subring. The quotient coefficient is still regular along F. -/
theorem residue_eq_zero_iff_exists_F_mul (z : RegularAtF) :
    residue z = 0 ↔ ∃ t : RegularAtF,
      (z : RatFun) = polynomialMap 5 HodgeSubmission.F * (t : RatFun) := by
  constructor
  · intro hz
    obtain ⟨P, T, hT, hFT, hrepr⟩ := z.property
    obtain ⟨Q, hQ⟩ := (residue_fraction_eq_zero_iff z P T hT hFT hrepr).mp hz
    let t : RegularAtF := ⟨polynomialMap 5 Q / polynomialMap 5 T,
      ⟨Q, T, hT, hFT, rfl⟩⟩
    refine ⟨t, ?_⟩
    change (z : RatFun) = polynomialMap 5 HodgeSubmission.F *
      (polynomialMap 5 Q / polynomialMap 5 T)
    rw [hrepr, hQ, map_mul]
    ring
  · rintro ⟨t, ht⟩
    have he : z = polynomialRegular HodgeSubmission.F * t := Subtype.ext ht
    rw [he, map_mul, residue_polynomial, coneMap_F, zero_mul]

/-- Equivalent form convenient for pole reduction: vanishing residue means
one can divide by F while remaining in the actual regular subring. -/
theorem residue_eq_zero_iff_regular_div_F (z : RegularAtF) :
    residue z = 0 ↔ RegularAlong HodgeSubmission.F
      ((z : RatFun) / polynomialMap 5 HodgeSubmission.F) := by
  have hF := polynomialMap_ne_zero CycleQ2ExactIrreducible.protected_F_irreducible.ne_zero
  constructor
  · intro hz
    obtain ⟨t, ht⟩ := (residue_eq_zero_iff_exists_F_mul z).mp hz
    have he : (z : RatFun) / polynomialMap 5 HodgeSubmission.F = (t : RatFun) := by
      rw [ht]
      field_simp
    rw [he]
    exact t.property
  · intro hz
    apply (residue_eq_zero_iff_exists_F_mul z).mpr
    refine ⟨⟨(z : RatFun) / polynomialMap 5 HodgeSubmission.F, hz⟩, ?_⟩
    change (z : RatFun) = polynomialMap 5 HodgeSubmission.F *
      ((z : RatFun) / polynomialMap 5 HodgeSubmission.F)
    field_simp


open CycleQ2ActualResidueClosure

local instance rationalFunctionIntAlgebra : Algebra ℤ RatFun := Ring.toIntAlgebra _
local instance coneFunctionFieldIntAlgebra : Algebra ℤ ConeFunctionField := Ring.toIntAlgebra _
local instance regularAtFIntAlgebra : Algebra ℤ RegularAtF := Ring.toIntAlgebra _

/-- The exact normal polynomial is nonzero before quotienting as well. -/
theorem normal_polynomial_ne_zero : pderiv 0 HodgeSubmission.F ≠ 0 := by
  intro h
  apply normal_ne_zero
  rw [h, map_zero]

theorem normal_polynomial_relPrime :
    IsRelPrime HodgeSubmission.F (pderiv 0 HodgeSubmission.F) :=
  CycleQ2ExactIrreducible.protected_F_irreducible.isRelPrime_iff_not_dvd.mpr
    protected_F_not_dvd_normal

/-- Restriction of the actual ambient tangent derivation to the actual regular
subring. Closure is proved from the quotient rule and normal-denominator legality. -/
def regularTangent (j : Fin 5) : Derivation ℤ RegularAtF RegularAtF :=
  Derivation.mk'
    ({ toFun := fun z => ⟨actualTangent HodgeSubmission.F j (z : RatFun),
         regular_actualTangent z.property normal_polynomial_ne_zero
           normal_polynomial_relPrime j⟩
       map_zero' := Subtype.ext (map_zero _)
       map_add' := fun x y => Subtype.ext (map_add _ _ _)
     } : RegularAtF →+ RegularAtF).toIntLinearMap
    (by
      intro x y
      apply Subtype.ext
      change actualTangent HodgeSubmission.F j ((x : RatFun) * (y : RatFun)) =
        (x : RatFun) * actualTangent HodgeSubmission.F j (y : RatFun) +
          (y : RatFun) * actualTangent HodgeSubmission.F j (x : RatFun)
      simpa only [smul_eq_mul] using
        (actualTangent HodgeSubmission.F j).leibniz (x : RatFun) (y : RatFun))

@[simp] theorem regularTangent_apply (j : Fin 5) (z : RegularAtF) :
    ((regularTangent j z : RegularAtF) : RatFun) =
      actualTangent HodgeSubmission.F j (z : RatFun) := rfl

@[simp] theorem residue_regularTangent_polynomial (j : Fin 5) (P : Poly) :
    residue (regularTangent j (polynomialRegular P)) =
      coneTangent j (coneMap P) := by
  let Q : Poly := pderiv 0 HodgeSubmission.F * pderiv j.succ P -
    pderiv j.succ HodgeSubmission.F * pderiv 0 P
  have hrepr : ((regularTangent j (polynomialRegular P) : RegularAtF) : RatFun) =
      polynomialMap 5 Q / polynomialMap 5 (pderiv 0 HodgeSubmission.F) := by
    change actualTangent HodgeSubmission.F j (polynomialMap 5 P) = _
    rw [actualTangent_apply]
    simp only [Q, rationalPartial_map, map_sub, map_mul]
    have hg := polynomialMap_ne_zero normal_polynomial_ne_zero
    field_simp <;> ring
  rw [residue_fraction _ Q _ normal_polynomial_ne_zero normal_polynomial_relPrime hrepr,
    coneTangent_apply]
  simp only [Q, map_sub, map_mul]
  have hg := normal_ne_zero
  field_simp <;> ring

/-- Exact compatibility of the actual regular-subring residue homomorphism
with the actual constructed tangent derivations on the cone function field. -/
theorem residue_regularTangent (j : Fin 5) (z : RegularAtF) :
    residue (regularTangent j z) = coneTangent j (residue z) := by
  obtain ⟨P, T, hT, hFT, hz⟩ := z.property
  have hprod : z * polynomialRegular T = polynomialRegular P := by
    apply Subtype.ext
    change (z : RatFun) * polynomialMap 5 T = polynomialMap 5 P
    rw [hz, div_mul_cancel₀ _ (polynomialMap_ne_zero hT)]
  have h₁ := congrArg (fun u : RegularAtF => residue (regularTangent j u)) hprod
  rw [Derivation.leibniz] at h₁
  simp only [smul_eq_mul, map_add, map_mul, residue_polynomial,
    residue_regularTangent_polynomial] at h₁
  have h₂ := congrArg (fun u : RegularAtF => coneTangent j (residue u)) hprod
  simp only [map_mul, residue_polynomial, Derivation.leibniz, smul_eq_mul] at h₂
  apply mul_left_cancel₀ (legal_coneMap_ne_zero T hFT)
  linear_combination h₁ - h₂


/-- Every element of the actual cone function field lifts to an actual
ambient fraction regular along F. This does not assert any homogeneity of
that lift. -/
theorem residue_surjective : Function.Surjective residue := by
  intro w
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective ConeCoordinateRing w
  obtain ⟨P, rfl⟩ := coneProjection_surjective a
  obtain ⟨T, rfl⟩ := coneProjection_surjective b
  have hden : coneMap T ≠ 0 := by
    change algebraMap ConeCoordinateRing ConeFunctionField (coneProjection T) ≠ 0
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hT : T ≠ 0 := by
    intro h
    apply hden
    rw [h, map_zero]
  have hFT : IsRelPrime HodgeSubmission.F T :=
    CycleQ2ExactIrreducible.protected_F_irreducible.isRelPrime_iff_not_dvd.mpr
      (fun h => hden ((coneMap_kernel T).mpr h))
  let z : RegularAtF := ⟨polynomialMap 5 P / polynomialMap 5 T,
    ⟨P, T, hT, hFT, rfl⟩⟩
  refine ⟨z, ?_⟩
  exact residue_fraction z P T hT hFT rfl

/-- A nonconstructive lift, justified by the proved residue surjectivity. -/
def liftResidue (w : ConeFunctionField) : RegularAtF :=
  Function.surjInv residue_surjective w

@[simp] theorem residue_liftResidue (w : ConeFunctionField) :
    residue (liftResidue w) = w := Function.surjInv_eq residue_surjective w

end CycleQ2Residue

#print axioms CycleQ2Residue.residue_fraction
#print axioms CycleQ2Residue.residue_eq_zero_iff_exists_F_mul
#print axioms CycleQ2Residue.residue_eq_zero_iff_regular_div_F

#print axioms CycleQ2Residue.residue_regularTangent

#print axioms CycleQ2Residue.residue_surjective
#print axioms CycleQ2Residue.residue_liftResidue
end
end


/- Component: pole_reduction/ProtectedResidueClosure.lean -/
section
/-!
Concrete closure of an actual residue primitive on the protected affine cone.

This proves regular ambient lifts and the third-order defect identity. It does
not assert existence of the residue primitive, and it does not assert the
homogeneous degree-seven condition on the resulting ambient vector field.
Projective homogenization or a graded primitive is a further step before
the protected HasCertificate theorem follows.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace CycleQ2ProtectedResidueClosure

open MvPolynomial HodgeComputer CycleQ2Bridge CycleQ2Regularity
open CycleQ2Hypersurface CycleQ2Residue CycleQ2ActualResidueClosure
open HoldoutConstruction SplitHigherResidue
open scoped BigOperators

local instance rationalFunctionIntAlgebra : Algebra ℤ RatFun := Ring.toIntAlgebra _
local instance coneFunctionFieldIntAlgebra : Algebra ℤ ConeFunctionField := Ring.toIntAlgebra _
local instance regularAtFIntAlgebra : Algebra ℤ RegularAtF := Ring.toIntAlgebra _

private theorem two_polynomial_relPrime : IsRelPrime HodgeSubmission.F (2 : Poly) := by
  have hu : IsUnit (2 : Poly) := by
    simpa only [map_ofNat] using
      (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℂ) ≠ 0)).map (C : ℂ →+* Poly)
  exact hu.isRelPrime_right

/-- The genuine inverse of the normal polynomial in the regular subring. -/
def normalInverse : RegularAtF :=
  ⟨(polynomialMap 5 (pderiv 0 HodgeSubmission.F))⁻¹,
    regular_inv_polynomial _ _ normal_polynomial_ne_zero normal_polynomial_relPrime⟩

@[simp] theorem normalInverse_val :
    (normalInverse : RatFun) = (polynomialMap 5 (pderiv 0 HodgeSubmission.F))⁻¹ := rfl

@[simp] theorem residue_normalInverse :
    residue normalInverse = (coneMap (pderiv 0 HodgeSubmission.F))⁻¹ := by
  simpa using residue_fraction normalInverse 1 (pderiv 0 HodgeSubmission.F)
    normal_polynomial_ne_zero normal_polynomial_relPrime (by simp [normalInverse])

private def halfRegular : RegularAtF :=
  ⟨(1 / 2 : RatFun), by
    change RegularAlong HodgeSubmission.F (1 / 2 : RatFun)
    simpa only [map_ofNat, one_div] using regular_inv_polynomial HodgeSubmission.F (2 : Poly)
      (by norm_num) two_polynomial_relPrime⟩

private theorem halfRegular_val : (halfRegular : RatFun) = (1 / 2 : RatFun) := rfl

private theorem residue_halfRegular : residue halfRegular = (1 / 2 : ConeFunctionField) := by
  simpa only [map_one, map_ofNat] using residue_fraction halfRegular 1 (2 : Poly)
    (by norm_num) two_polynomial_relPrime (by
      change (1 / 2 : RatFun) = polynomialMap 5 1 / polynomialMap 5 2
      simp only [map_one, map_ofNat])

/-- The exact normal source, now evaluated in the actual cone function field. -/
def coneNormalSource (A : Poly) : ConeFunctionField :=
  normalSourceTwo (coneMap A) (coneMap (pderiv 0 A))
    (coneMap (pderiv 0 (pderiv 0 A)))
    (coneMap (pderiv 0 HodgeSubmission.F))
    (coneMap (pderiv 0 (pderiv 0 HodgeSubmission.F)))
    (coneMap (pderiv 0 (pderiv 0 (pderiv 0 HodgeSubmission.F))))

/-- The concrete function-field residue equation whose solution is required. -/
def coneResidueExpression (A : Poly) (w : Fin 5 → ConeFunctionField) : ConeFunctionField :=
  coneNormalSource A +
    residueDivergence coneTangent (coneMap (pderiv 0 HodgeSubmission.F)) w

private def normalSourceRegular (A : Poly) : RegularAtF :=
  halfRegular *
    (polynomialRegular (pderiv 0 (pderiv 0 A)) * normalInverse ^ 2 -
      (3 * polynomialRegular (pderiv 0 A) *
          polynomialRegular (pderiv 0 (pderiv 0 HodgeSubmission.F)) +
        polynomialRegular A * polynomialRegular (pderiv 0 (pderiv 0 (pderiv 0 HodgeSubmission.F)))) *
        normalInverse ^ 3 +
      3 * polynomialRegular A * polynomialRegular (pderiv 0 (pderiv 0 HodgeSubmission.F)) ^ 2 *
        normalInverse ^ 4)

private theorem normalSourceRegular_val (A : Poly) :
    ((normalSourceRegular A : RegularAtF) : RatFun) =
      actualNormalSource HodgeSubmission.F A := by
  change RegularAtF.subtype (normalSourceRegular A) = _
  simp only [normalSourceRegular, actualNormalSource, normalSourceTwo,
    map_mul, map_add, map_sub, map_pow, map_ofNat, Subring.subtype_apply,
    halfRegular_val, normalInverse_val, polynomialRegular,
    div_eq_mul_inv, inv_pow]

private theorem residue_normalSourceRegular (A : Poly) :
    residue (normalSourceRegular A) = coneNormalSource A := by
  simp only [normalSourceRegular, map_mul, map_add, map_sub, map_pow, map_ofNat,
    residue_halfRegular, residue_normalInverse, residue_polynomial,
    coneNormalSource, normalSourceTwo, div_eq_mul_inv, inv_pow]

/-- The actual regular-subring lift of the entire residue equation. -/
def residueExpressionRegular (A : Poly) (w : Fin 5 → RegularAtF) : RegularAtF :=
  normalSourceRegular A +
    (∑ j, regularTangent j (w j)) -
    (∑ j, w j * regularTangent j (polynomialRegular (pderiv 0 HodgeSubmission.F))) *
      normalInverse

theorem residueExpressionRegular_val (A : Poly) (w : Fin 5 → RegularAtF) :
    ((residueExpressionRegular A w : RegularAtF) : RatFun) =
      actualResidueExpression HodgeSubmission.F A (fun j => (w j : RatFun)) := by
  change RegularAtF.subtype (residueExpressionRegular A w) = _
  simp only [residueExpressionRegular, map_add, map_sub, map_mul,
    map_sum, Subring.subtype_apply, regularTangent_apply, normalSourceRegular_val, normalInverse_val,
    polynomialRegular, actualResidueExpression, residueDivergence,
    HoldoutConstruction.fieldDivergence, div_eq_mul_inv]
  ring

/-- The ambient source and tangent divergence transport to the actual quotient
equation through the proved residue homomorphism. -/
theorem residue_residueExpressionRegular (A : Poly) (w : Fin 5 → RegularAtF) :
    residue (residueExpressionRegular A w) =
      coneResidueExpression A (fun j => residue (w j)) := by
  simp only [residueExpressionRegular, map_add, map_sub, map_mul, map_sum,
    residue_normalSourceRegular, residue_regularTangent, residue_polynomial,
    residue_normalInverse, coneResidueExpression, residueDivergence,
    HoldoutConstruction.fieldDivergence, div_eq_mul_inv]
  ring

/-- A solved cone residue equation for actual regular lifts gives an actual
regular ambient vector with third-order defect. Homogeneity is not asserted. -/
theorem regular_cone_primitive_closure (A : Poly) (w : Fin 5 → RegularAtF)
    (hres : coneResidueExpression A (fun j => residue (w j)) = 0) :
    ∃ (v : Fin 6 → RatFun) (t : RatFun),
      (∀ i, RegularAlong HodgeSubmission.F (v i)) ∧
      RegularAlong HodgeSubmission.F t ∧
      rationalDefect HodgeSubmission.F A 2 v =
        polynomialMap 5 HodgeSubmission.F ^ 3 * t := by
  have hz : residue (residueExpressionRegular A w) = 0 := by
    rw [residue_residueExpressionRegular]
    exact hres
  obtain ⟨t, ht⟩ := (residue_eq_zero_iff_exists_F_mul (residueExpressionRegular A w)).mp hz
  refine ⟨actualClosureVector HodgeSubmission.F A (fun j => (w j : RatFun)), t,
    ?_, t.property, ?_⟩
  · exact regular_actualClosureVector HodgeSubmission.F A _ normal_polynomial_ne_zero
      normal_polynomial_relPrime (fun j => (w j).property)
  · apply actualClosure_defect_of_residue HodgeSubmission.F A _ _ normal_polynomial_ne_zero
    rw [← residueExpressionRegular_val]
    exact ht

/-- Every actual cone primitive has regular ambient lifts. This conclusion
is the rational defect equation; no homogeneous-degree conclusion is hidden. -/
theorem cone_primitive_closure (A : Poly) (w : Fin 5 → ConeFunctionField)
    (hres : coneResidueExpression A w = 0) :
    ∃ (v : Fin 6 → RatFun) (t : RatFun),
      (∀ i, RegularAlong HodgeSubmission.F (v i)) ∧
      RegularAlong HodgeSubmission.F t ∧
      rationalDefect HodgeSubmission.F A 2 v =
        polynomialMap 5 HodgeSubmission.F ^ 3 * t := by
  apply regular_cone_primitive_closure A (fun j => liftResidue (w j))
  simpa only [residue_liftResidue] using hres

/-- The exact protected numerator is bound here to the concrete cone equation.
Its remaining primitive-existence hypothesis is stated explicitly. -/
theorem protected_regular_ambient_of_cone_primitive
    (h : ∃ w : Fin 5 → ConeFunctionField,
      coneResidueExpression HodgeSubmission.A w = 0) :
    ∃ (v : Fin 6 → RatFun) (t : RatFun),
      (∀ i, RegularAlong HodgeSubmission.F (v i)) ∧
      RegularAlong HodgeSubmission.F t ∧
      rationalDefect HodgeSubmission.F HodgeSubmission.A 2 v =
        polynomialMap 5 HodgeSubmission.F ^ 3 * t := by
  obtain ⟨w, hw⟩ := h
  exact cone_primitive_closure HodgeSubmission.A w hw

end CycleQ2ProtectedResidueClosure

#print axioms CycleQ2ProtectedResidueClosure.residue_residueExpressionRegular
#print axioms CycleQ2ProtectedResidueClosure.regular_cone_primitive_closure
#print axioms CycleQ2ProtectedResidueClosure.protected_regular_ambient_of_cone_primitive
end
end


/- Component: euler_lift/AffineChart.lean -/
section
/-!
# The actual projective chart over the complex rational-function fields

This adapts the injective chart and chain-rule proofs in benediamond's
accepted two-ternary dense Hessian construction, retaining their mathematical
credit. The protected coordinates are unchanged; the chart sets X0=1.
Its fraction-field map is constructed and proved injective, not assumed.
-/

set_option autoImplicit false
noncomputable section

namespace CycleQ2AffineChart

open MvPolynomial HodgeComputer CycleQ2Bridge HodgeTestbed.Conic
open scoped BigOperators

local instance (n : ℕ) : Algebra ℚ (RationalFunction n) := DivisionRing.toRatAlgebra
local instance (n : ℕ) : Module ℚ (RationalFunction n) := Algebra.toModule

def embed {n : ℕ} : AmbientPoly n →ₐ[ℂ] RationalFunction n :=
  IsScalarTower.toAlgHom ℂ (AmbientPoly n) (RationalFunction n)

abbrev coord {n : ℕ} (i : Fin (n + 1)) : RationalFunction n := polynomialMap n (X i)

theorem coord_ne_zero {n : ℕ} (i : Fin (n + 1)) : coord i ≠ 0 :=
  polynomialMap_ne_zero (X_ne_zero i)

@[simp] theorem partial_coord {n : ℕ} (i j : Fin (n + 1)) :
    rationalPartial n i (coord j) = if i = j then 1 else 0 := by
  simp [coord, rationalPartial_map, pderiv_X, Pi.single_apply, eq_comm]

def dehomogenize : AmbientPoly 5 →ₐ[ℂ] AmbientPoly 4 := aeval (Fin.cases 1 X)

abbrev ChartRing := Localization.Away (X (0 : Fin 6) : AmbientPoly 5)

def awayEmbed : AmbientPoly 5 →ₐ[ℂ] ChartRing :=
  IsScalarTower.toAlgHom ℂ (AmbientPoly 5) ChartRing

def awayEval : ChartRing →ₐ[ℂ] AmbientPoly 4 :=
  IsLocalization.Away.liftAlgHom (X (0 : Fin 6)) (f := dehomogenize) (by
    have hx : dehomogenize (X (0 : Fin 6)) = 1 := aeval_X _ _
    rw [hx]
    exact isUnit_one)

def awayFrac : ChartRing →ₐ[ℂ] RationalFunction 5 :=
  IsLocalization.Away.liftAlgHom (X (0 : Fin 6)) (f := embed)
    (isUnit_iff_ne_zero.mpr (coord_ne_zero 0))

@[simp] theorem awayEval_embed (P : AmbientPoly 5) :
    awayEval (awayEmbed P) = dehomogenize P := IsLocalization.lift_eq _ P

@[simp] theorem awayFrac_embed (P : AmbientPoly 5) :
    awayFrac (awayEmbed P) = polynomialMap 5 P := IsLocalization.lift_eq _ P

def inverseScale : ChartRing :=
  IsLocalization.Away.invSelf (S := ChartRing) (X (0 : Fin 6) : AmbientPoly 5)

theorem scale_mul_inverseScale : awayEmbed (X (0 : Fin 6)) * inverseScale = 1 :=
  IsLocalization.Away.mul_invSelf (S := ChartRing) (X (0 : Fin 6) : AmbientPoly 5)

@[simp] theorem awayEval_inverseScale : awayEval inverseScale = 1 := by
  have h := congrArg awayEval scale_mul_inverseScale
  have hx : dehomogenize (X (0 : Fin 6)) = 1 := aeval_X _ _
  simpa only [map_mul, awayEval_embed, hx, one_mul, map_one] using h

@[simp] theorem awayFrac_inverseScale : awayFrac inverseScale = (coord (0 : Fin 6))⁻¹ := by
  have h := congrArg awayFrac scale_mul_inverseScale
  apply mul_left_cancel₀ (coord_ne_zero (0 : Fin 6))
  rw [mul_inv_cancel₀ (coord_ne_zero (0 : Fin 6))]
  simpa only [coord, map_mul, awayFrac_embed, map_one] using h

theorem awayFrac_injective : Function.Injective awayFrac := by
  apply IsLocalization.injective_of_map_algebraMap_zero
    (M := Submonoid.powers (X (0 : Fin 6) : AmbientPoly 5)) ChartRing awayFrac.toRingHom
  intro P hP
  change awayFrac (awayEmbed P) = 0 at hP
  rw [awayFrac_embed] at hP
  have hz : P = 0 := polynomialMap_injective (by simpa only [map_zero] using hP)
  simp [hz]

def awayChart : AmbientPoly 4 →ₐ[ℂ] ChartRing :=
  aeval (fun i : Fin 5 => awayEmbed (X i.succ) * inverseScale)

theorem awayChart_leftInverse : awayEval.comp awayChart = AlgHom.id ℂ (AmbientPoly 4) := by
  ext1 i
  change awayEval (awayChart (X i)) = X i
  have hc : awayChart (X i) = awayEmbed (X i.succ) * inverseScale := aeval_X _ _
  have hd : dehomogenize (X i.succ) = X i := aeval_X _ _
  rw [hc, map_mul, awayEval_embed, hd, awayEval_inverseScale, mul_one]

def chartPoly : AmbientPoly 4 →ₐ[ℂ] RationalFunction 5 := awayFrac.comp awayChart

theorem chartPoly_injective : Function.Injective chartPoly := by
  apply awayFrac_injective.comp
  intro P Q h
  have hh := congrArg awayEval h
  have hp := AlgHom.congr_fun awayChart_leftInverse P
  have hq := AlgHom.congr_fun awayChart_leftInverse Q
  exact hp.symm.trans (hh.trans hq)

def chart : RationalFunction 4 →ₐ[ℂ] RationalFunction 5 :=
  IsFractionRing.liftAlgHom (g := chartPoly) chartPoly_injective

@[simp] theorem chart_embed (P : AmbientPoly 4) :
    chart (polynomialMap 4 P) = chartPoly P := IsLocalization.lift_eq _ P

@[simp] theorem chart_coord (i : Fin 5) :
    chart (coord i) = coord i.succ / coord (0 : Fin 6) := by
  rw [coord, chart_embed]
  change awayFrac (awayChart (X i)) = _
  have hc : awayChart (X i) = awayEmbed (X i.succ) * inverseScale := aeval_X _ _
  rw [hc, map_mul, awayFrac_embed, awayFrac_inverseScale]
  rfl

@[simp] theorem chart_constant (c : ℂ) :
    chart (polynomialMap 4 (C c)) = polynomialMap 5 (C c) := by
  exact chart.commutes c

theorem compatibility_of_coordinates
    (D : Derivation ℚ (RationalFunction 5) (RationalFunction 5))
    (E : Derivation ℚ (RationalFunction 4) (RationalFunction 4))
    (c : RationalFunction 5)
    (hD : ∀ a : ℂ, D (polynomialMap 5 (C a)) = 0)
    (hE : ∀ a : ℂ, E (polynomialMap 4 (C a)) = 0)
    (hcoord : ∀ j : Fin 5, D (chart (coord j)) = c * chart (E (coord j)))
    (z : RationalFunction 4) : D (chart z) = c * chart (E z) := by
  have hp (P : AmbientPoly 4) :
      D (chart (polynomialMap 4 P)) = c * chart (E (polynomialMap 4 P)) := by
    induction P using MvPolynomial.induction_on with
    | C a => simp only [chart_constant, hD, hE, map_zero, mul_zero]
    | add P Q hP hQ => simp only [map_add, hP, hQ]; ring
    | mul_X P j hP =>
      simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add]
      rw [hP, show D (chart (polynomialMap 4 (X j))) =
        c * chart (E (polynomialMap 4 (X j))) from hcoord j]
      ring
  obtain ⟨P, Q, _, rfl⟩ := IsFractionRing.div_surjective (AmbientPoly 4) z
  change D (chart (polynomialMap 4 P / polynomialMap 4 Q)) =
    c * chart (E (polynomialMap 4 P / polynomialMap 4 Q))
  simp only [div_eq_mul_inv, map_mul, map_inv₀, Derivation.leibniz,
    Derivation.leibniz_inv, smul_eq_mul, hp, map_neg, map_add, map_pow]
  ring

theorem affineEuler_coord (j : Fin 5) :
    fieldAction (rationalPartial 4) coord (coord j) = coord j := by
  simp [fieldAction_apply, Pi.single_apply]

theorem chart_zero (z : RationalFunction 4) :
    rationalPartial 5 0 (chart z) = -(coord (0 : Fin 6))⁻¹ *
      chart (fieldAction (rationalPartial 4) coord z) := by
  apply compatibility_of_coordinates (rationalPartial 5 0)
    (fieldAction (rationalPartial 4) coord) (-(coord (0 : Fin 6))⁻¹)
  · intro a
    simp only [rationalPartial_map, pderiv_C, map_zero]
  · intro a
    simp only [fieldAction_apply, rationalPartial_map, pderiv_C, map_zero,
      mul_zero, Finset.sum_const_zero]
  · intro j
    rw [affineEuler_coord, chart_coord]
    have hj0 : (0 : Fin 6) ≠ j.succ := Ne.symm (Fin.succ_ne_zero j)
    simp [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv,
      partial_coord, smul_eq_mul, hj0]
    ring

theorem chart_succ (i : Fin 5) (z : RationalFunction 4) :
    rationalPartial 5 i.succ (chart z) =
      (coord (0 : Fin 6))⁻¹ * chart (rationalPartial 4 i z) := by
  apply compatibility_of_coordinates (rationalPartial 5 i.succ)
    (rationalPartial 4 i) ((coord (0 : Fin 6))⁻¹)
  · intro a
    simp only [rationalPartial_map, pderiv_C, map_zero]
  · intro a
    simp only [rationalPartial_map, pderiv_C, map_zero]
  · intro j
    rw [chart_coord, partial_coord]
    simp only [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv,
      partial_coord, smul_eq_mul]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij, Fin.succ_inj]

theorem actual_homogeneousChart :
    HomogeneousChart (rationalPartial 4) (rationalPartial 5)
      chart.toRingHom (coord 0) coord where
  a_ne_zero := coord_ne_zero 0
  a_zero := by simp
  a_succ := by intro i; simp
  map_zero := chart_zero
  map_succ := chart_succ
  coordinate_diagonal := by intro i; simp

end CycleQ2AffineChart

#print axioms CycleQ2AffineChart.actual_homogeneousChart
end
end


/- Component: euler_lift/AffineHomogeneousClearing.lean -/
section
/-!
# Homogeneous clearing on the actual X0 affine chart

The clearing polynomial is the repository's proved bounded substitution.
Applying dehomogenization proves legality before taking fractions. Every
finite family of F-regular affine coefficients has a legal homogeneous
common denominator, with the exact numerator degree obtained by X0^7.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace CycleQ2AffineClearing

open MvPolynomial HodgeComputer CycleQ2Bridge CycleQ2Regularity CycleQ2AffineChart
open scoped BigOperators

local instance (n : ℕ) : Algebra ℚ (RationalFunction n) := DivisionRing.toRatAlgebra
local instance (n : ℕ) : Module ℚ (RationalFunction n) := Algebra.toModule

def homogenize (P : AmbientPoly 4) (d : ℕ) : AmbientPoly 5 :=
  CommonDenominatorSubstitution.cleared P (X 0) (fun i : Fin 5 => X i.succ) d

theorem homogenize_homogeneous (P : AmbientPoly 4) (d : ℕ) (hP : P.totalDegree ≤ d) :
    (homogenize P d).IsHomogeneous d := by
  simpa only [homogenize, one_mul] using CommonDenominatorSubstitution.cleared_homogeneous
    P (X 0) (fun i : Fin 5 => X i.succ) d 1 hP
    (isHomogeneous_X ℂ 0) (fun i => isHomogeneous_X ℂ i.succ)

theorem dehomogenize_homogenize (P : AmbientPoly 4) (d : ℕ) (hP : P.totalDegree ≤ d) :
    dehomogenize (homogenize P d) = P := by
  have h := CommonDenominatorSubstitution.map_cleared P (X 0)
    (fun i : Fin 5 => X i.succ) d hP dehomogenize.toRingHom 1 X
    (aeval_X _ _) (fun i => by simp [dehomogenize])
  have hc : dehomogenize.toRingHom.comp C = C := by ext c; simp [dehomogenize]
  simp only [AlgHom.toRingHom_eq_coe] at hc
  simpa only [homogenize, hc, one_pow, one_mul, eval₂_eta,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using h

theorem homogenize_ne_zero {P : AmbientPoly 4} {d : ℕ}
    (hP : P.totalDegree ≤ d) (hP0 : P ≠ 0) : homogenize P d ≠ 0 := by
  intro h
  have hh := congrArg dehomogenize h
  rw [dehomogenize_homogenize P d hP, map_zero] at hh
  exact hP0 hh

theorem homogenize_chart (P : AmbientPoly 4) (d : ℕ) (hP : P.totalDegree ≤ d) :
    polynomialMap 5 (homogenize P d) =
      (coord (0 : Fin 6))^d * chart (polynomialMap 4 P) := by
  have h := CommonDenominatorSubstitution.map_cleared_fraction P (X 0)
    (fun i : Fin 5 => X i.succ) d hP (polynomialMap 5) (coord_ne_zero 0)
  have hm : eval₂Hom ((polynomialMap 5).comp C)
      (fun i : Fin 5 => coord i.succ / coord (0 : Fin 6)) =
      chart.toRingHom.comp (polynomialMap 4) := by
    ext c
    · simpa only [eval₂Hom_C, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom] using (chart_constant c).symm
    · simpa only [eval₂Hom_X', RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom] using (chart_coord c).symm
  simpa only [homogenize, coord, ← coe_eval₂Hom, hm, RingHom.comp_apply,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using h

theorem cleared_self_of_homogeneous {P : AmbientPoly 5} {d : ℕ}
    (hP : P.IsHomogeneous d) (B : AmbientPoly 5) :
    CommonDenominatorSubstitution.cleared P B X d = P := by
  classical
  conv_rhs => rw [P.as_sum]
  rw [CommonDenominatorSubstitution.cleared]
  apply Finset.sum_congr rfl
  intro a ha
  have hdegree : a.sum (fun _ e => e) = d := by
    change a.degree = d
    exact_mod_cast Homogeneous.of_isHomogeneous hP (mem_support_iff.mp ha)
  rw [hdegree, Nat.sub_self, pow_zero, mul_one, monomial_eq]
  rfl

/-- A homogeneous polynomial is recovered from its chart with its exact
degree; the proof uses actual bounded polynomial substitution. -/
theorem homogeneous_chart {P : AmbientPoly 5} {d : ℕ} (hP : P.IsHomogeneous d) :
    polynomialMap 5 P = (coord (0 : Fin 6))^d * chart
      (polynomialMap 4 (dehomogenize P)) := by
  have h := CommonDenominatorSubstitution.map_cleared_fraction P (X 0) X
    d hP.totalDegree_le (polynomialMap 5) (coord_ne_zero 0)
  rw [cleared_self_of_homogeneous hP (X 0)] at h
  have hm : eval₂Hom ((polynomialMap 5).comp C)
      (fun i : Fin 6 => coord i / coord (0 : Fin 6)) =
      (chart.toRingHom.comp (polynomialMap 4)).comp dehomogenize.toRingHom := by
    ext c
    · simpa [dehomogenize] using (chart_constant c).symm
    · refine Fin.cases ?_ (fun j => ?_) c
      · simp [dehomogenize, coord_ne_zero 0]
      · simp only [eval₂Hom_X', RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
          AlgHom.coe_toRingHom]
        have hj : dehomogenize (X j.succ) = X j := aeval_X _ _
        rw [hj]
        exact (chart_coord j).symm
  simpa only [coord, ← coe_eval₂Hom, hm, RingHom.comp_apply,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using h

def affineF : AmbientPoly 4 := dehomogenize HodgeSubmission.F
def affineA : AmbientPoly 4 := dehomogenize HodgeSubmission.A

theorem protected_F_chart : polynomialMap 5 HodgeSubmission.F =
    (coord (0 : Fin 6))^6 * chart (polynomialMap 4 affineF) :=
  homogeneous_chart CycleQ2Workspace.originalF_homogeneous

theorem protected_A_chart : polynomialMap 5 HodgeSubmission.A =
    (coord (0 : Fin 6))^12 * chart (polynomialMap 4 affineA) :=
  homogeneous_chart CycleQ2Workspace.originalA_homogeneous

theorem affineF_ne_zero : affineF ≠ 0 := by
  intro h
  have hf := protected_F_chart
  rw [h, map_zero, map_zero, mul_zero] at hf
  exact polynomialMap_ne_zero CycleQ2Workspace.originalF_ne_zero hf

theorem affineF_not_isUnit : ¬ IsUnit affineF := by
  intro h
  let ev : AmbientPoly 4 →+* ℂ := eval₂Hom (RingHom.id ℂ)
    ![0, 0, Complex.I, 0, 0]
  have he : ev affineF = 0 := by
    have h1 : Fin.cases (1 : AmbientPoly 4) X (1 : Fin 6) = X (0 : Fin 5) := rfl
    have h2 : Fin.cases (1 : AmbientPoly 4) X (2 : Fin 6) = X (1 : Fin 5) := rfl
    have h3 : Fin.cases (1 : AmbientPoly 4) X (3 : Fin 6) = X (2 : Fin 5) := rfl
    have h4 : Fin.cases (1 : AmbientPoly 4) X (4 : Fin 6) = X (3 : Fin 5) := rfl
    have h5 : Fin.cases (1 : AmbientPoly 4) X (5 : Fin 6) = X (4 : Fin 5) := rfl
    norm_num [ev, affineF, dehomogenize, HodgeSubmission.F,
      Complex.I_sq, h1, h2, h3, h4, h5]
    dsimp
    norm_num [pow_succ, Complex.I_sq]
  have hu := h.map ev
  rw [he] at hu
  exact not_isUnit_zero hu

theorem homogenize_legal {P : AmbientPoly 4} {d : ℕ}
    (hP : P.totalDegree ≤ d) (hlegal : IsRelPrime affineF P) :
    IsRelPrime HodgeSubmission.F (homogenize P d) := by
  apply CycleQ2ExactIrreducible.protected_F_irreducible.isRelPrime_iff_not_dvd.mpr
  intro h
  have hd := map_dvd dehomogenize.toRingHom h
  change affineF ∣ dehomogenize (homogenize P d) at hd
  rw [dehomogenize_homogenize P d hP] at hd
  exact affineF_not_isUnit (hlegal.isUnit_of_dvd hd)

theorem regular_chart {z : RationalFunction 4} (hz : RegularAlong affineF z) :
    RegularAlong HodgeSubmission.F (chart z) := by
  obtain ⟨P, T, hT, hFT, rfl⟩ := hz
  let d := max P.totalDegree T.totalDegree
  have hp : P.totalDegree ≤ d := le_max_left _ _
  have ht : T.totalDegree ≤ d := le_max_right _ _
  refine ⟨homogenize P d, homogenize T d, homogenize_ne_zero ht hT,
    homogenize_legal ht hFT, ?_⟩
  rw [map_div₀, homogenize_chart P d hp, homogenize_chart T d ht]
  have hscale : coord (0 : Fin 6) ≠ 0 := coord_ne_zero 0
  field_simp

end CycleQ2AffineClearing

#print axioms CycleQ2AffineClearing.regular_chart
end
end


/- Component: euler_lift/AffineHypersurfaceGeometry.lean -/
section
/-! Exact algebraic geometry of the protected X0=1 chart. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace CycleQ2AffineGeometry

open MvPolynomial HodgeComputer CycleQ2Bridge CycleQ2AffineChart CycleQ2AffineClearing
open scoped BigOperators

theorem protected_coordinate_legal : IsRelPrime HodgeSubmission.F (X (0 : Fin 6)) :=
  CycleQ2ExactIrreducible.protected_F_irreducible.isRelPrime_iff_not_dvd.mpr
    (CycleQ2SupportEquation.not_dvd_coordinate_of_degree_gt_one HodgeSubmission.F
      (by rw [CycleQ2Workspace.originalF_totalDegree]; norm_num) 0)

theorem homogenize_dvd_iff (P : AmbientPoly 4) (d : ℕ) (hP : P.totalDegree ≤ d) :
    HodgeSubmission.F ∣ homogenize P d ↔ affineF ∣ P := by
  constructor
  · intro h
    have hd := map_dvd dehomogenize.toRingHom h
    change affineF ∣ dehomogenize (homogenize P d) at hd
    simpa only [dehomogenize_homogenize P d hP] using hd
  · rintro ⟨R, hR⟩
    have heq : X (0 : Fin 6)^(6 + R.totalDegree) * homogenize P d =
        HodgeSubmission.F * (X (0 : Fin 6)^d * homogenize R R.totalDegree) := by
      apply polynomialMap_injective (n := 5)
      simp only [map_mul, map_pow]
      rw [homogenize_chart P d hP, homogenize_chart R R.totalDegree le_rfl,
        protected_F_chart, hR, map_mul, map_mul, pow_add]
      ring
    have hd : HodgeSubmission.F ∣ X (0 : Fin 6)^(6 + R.totalDegree) * homogenize P d :=
      ⟨X (0 : Fin 6)^d * homogenize R R.totalDegree, heq⟩
    exact protected_coordinate_legal.pow_right.dvd_of_dvd_mul_left hd

theorem homogenize_mul (P Q : AmbientPoly 4) (d e : ℕ)
    (hP : P.totalDegree ≤ d) (hQ : Q.totalDegree ≤ e) :
    homogenize (P * Q) (d + e) = homogenize P d * homogenize Q e := by
  have hpq : (P * Q).totalDegree ≤ d + e :=
    (totalDegree_mul P Q).trans (Nat.add_le_add hP hQ)
  apply polynomialMap_injective (n := 5)
  rw [map_mul, homogenize_chart (P * Q) (d + e) hpq,
    homogenize_chart P d hP, homogenize_chart Q e hQ, map_mul, map_mul, pow_add]
  ring

theorem affineF_prime : Prime affineF := by
  refine ⟨affineF_ne_zero, affineF_not_isUnit, ?_⟩
  intro P Q h
  have hdegree : (P * Q).totalDegree ≤ P.totalDegree + Q.totalDegree := totalDegree_mul P Q
  have hh := (homogenize_dvd_iff (P * Q) (P.totalDegree + Q.totalDegree) hdegree).mpr h
  rw [homogenize_mul P Q P.totalDegree Q.totalDegree le_rfl le_rfl] at hh
  rcases CycleQ2ExactIrreducible.protected_F_irreducible.prime.dvd_or_dvd hh with hp | hq
  · exact Or.inl ((homogenize_dvd_iff P P.totalDegree le_rfl).mp hp)
  · exact Or.inr ((homogenize_dvd_iff Q Q.totalDegree le_rfl).mp hq)

theorem affineF_irreducible : Irreducible affineF := affineF_prime.irreducible

theorem affineF_formula : affineF =
    1 + X 0^6 + X 1^6 + X 2^6 + X 3^6 + X 4^6 +
      C (1 / 2 : ℂ) * (X 0 * X 2 * X 3 + X 0^3 * X 1 * X 3 * X 4 +
        X 1^3 * X 4 * X 2) := by
  have h1 : Fin.cases (1 : AmbientPoly 4) X (1 : Fin 6) = X (0 : Fin 5) := rfl
  have h2 : Fin.cases (1 : AmbientPoly 4) X (2 : Fin 6) = X (1 : Fin 5) := rfl
  have h3 : Fin.cases (1 : AmbientPoly 4) X (3 : Fin 6) = X (2 : Fin 5) := rfl
  have h4 : Fin.cases (1 : AmbientPoly 4) X (4 : Fin 6) = X (3 : Fin 5) := rfl
  have h5 : Fin.cases (1 : AmbientPoly 4) X (5 : Fin 6) = X (4 : Fin 5) := rfl
  norm_num [affineF, dehomogenize, HodgeSubmission.F, h1, h2, h3, h4, h5]
  ring

def testPoint : AmbientPoly 4 →+* ℂ :=
  eval₂Hom (RingHom.id ℂ) ![Complex.I, 0, 0, 0, 0]

theorem testPoint_F : testPoint affineF = 0 := by
  rw [affineF_formula]
  norm_num [testPoint, pow_succ, Complex.I_sq]
  dsimp
  ring

theorem testPoint_normal : testPoint (pderiv (0 : Fin 5) affineF) = 6 * Complex.I := by
  rw [affineF_formula]
  norm_num [testPoint, Pi.single_apply, Fin.ext_iff, pow_succ, Complex.I_sq]
  dsimp
  ring_nf
  norm_num [Complex.I_sq]
  have hI5 : Complex.I^5 = Complex.I := by
    calc
      Complex.I^5 = (Complex.I^2)^2 * Complex.I := by ring
      _ = Complex.I := by norm_num [Complex.I_sq]
  rw [hI5]
  ring

theorem affineF_not_dvd_normal : ¬ affineF ∣ pderiv (0 : Fin 5) affineF := by
  intro h
  have hh := map_dvd testPoint h
  rw [testPoint_F, testPoint_normal] at hh
  exact (mul_ne_zero (by norm_num : (6 : ℂ) ≠ 0) Complex.I_ne_zero)
    (zero_dvd_iff.mp hh)

theorem affine_normal_ne_zero : pderiv (0 : Fin 5) affineF ≠ 0 := by
  intro h
  apply affineF_not_dvd_normal
  rw [h]
  exact dvd_zero _

theorem affine_normal_legal : IsRelPrime affineF (pderiv (0 : Fin 5) affineF) :=
  affineF_irreducible.isRelPrime_iff_not_dvd.mpr affineF_not_dvd_normal

end CycleQ2AffineGeometry

#print axioms CycleQ2AffineGeometry.affineF_irreducible
#print axioms CycleQ2AffineGeometry.affine_normal_legal
end
end


/- Component: euler_lift/AffineCertificate.lean -/
section
/-!
# A regular affine primitive gives the exact protected certificate

This completes homogeneous clearing and the projective chart transfer with
actual fraction-field maps and proved chain rules. Numerators have degree
degree(D)+7, and the complete quotient is retained. The input is an actual
affine rational vector satisfying the residue equation; its existence is
not postulated or inferred merely from homogeneity or Hodge type.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace CycleQ2AffineCertificate

open MvPolynomial HodgeComputer CycleQ2Bridge CycleQ2Regularity
open CycleQ2AffineChart CycleQ2AffineClearing HodgeTestbed.Conic
open scoped BigOperators

local instance (n : ℕ) : Algebra ℚ (RationalFunction n) := DivisionRing.toRatAlgebra
local instance (n : ℕ) : Module ℚ (RationalFunction n) := Algebra.toModule

theorem regular_common_denominator {n : ℕ} {ι : Type*} [Fintype ι]
    (F : AmbientPoly n) (v : ι → RationalFunction n)
    (hv : ∀ i, RegularAlong F (v i)) :
    ∃ (T : AmbientPoly n) (P : ι → AmbientPoly n),
      T ≠ 0 ∧ IsRelPrime F T ∧ ∀ i,
        v i = polynomialMap n (P i) / polynomialMap n T := by
  classical
  choose P T hT hFT heq using hv
  let D := ∏ i, T i
  refine ⟨D, fun i => P i * ∏ j ∈ Finset.univ.erase i, T j,
    Finset.prod_ne_zero_iff.mpr (fun i _ => hT i),
    IsRelPrime.prod_right (fun i _ => hFT i), ?_⟩
  intro i
  have hp : D = T i * ∏ j ∈ Finset.univ.erase i, T j :=
    (Finset.mul_prod_erase Finset.univ T (Finset.mem_univ i)).symm
  have ht := polynomialMap_ne_zero (hT i)
  have hr := polynomialMap_ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun j _ => hT j) :
      (∏ j ∈ Finset.univ.erase i, T j) ≠ 0)
  rw [heq i, hp]
  simp only [map_mul]
  field_simp

def liftedField (v : Fin 5 → RationalFunction 4) : Fin 6 → RationalFunction 5 :=
  Fin.cases 0 (fun i => (coord (0 : Fin 6))^7 * chart (v i))

theorem liftedField_eq_scale (v : Fin 5 → RationalFunction 4) :
    liftedField v = fun i => (coord (0 : Fin 6))^6 *
      homogenizedField chart.toRingHom (coord 0) v i := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [liftedField, homogenizedField]
  · simp only [liftedField, homogenizedField, Fin.cases_succ,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    ring

theorem liftedField_action (v : Fin 5 → RationalFunction 4) (P : RationalFunction 4) :
    fieldAction (rationalPartial 5) (liftedField v)
        ((coord (0 : Fin 6))^6 * chart P) =
      (coord (0 : Fin 6))^12 * chart (fieldAction (rationalPartial 4) v P) := by
  rw [liftedField_eq_scale, fieldAction_scale]
  have he := homogenizedField_contraction (rationalPartial 4) (rationalPartial 5)
      chart.toRingHom (coord 0) coord v actual_homogeneousChart P
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at he ⊢
  rw [he]
  ring

theorem liftedField_divergence (v : Fin 5 → RationalFunction 4) :
    fieldDivergence (rationalPartial 5) (liftedField v) =
      (coord (0 : Fin 6))^6 * chart (fieldDivergence (rationalPartial 4) v) := by
  have hs : fieldAction (rationalPartial 5)
      (homogenizedField chart.toRingHom (coord 0) v) ((coord (0 : Fin 6))^6) = 0 := by
    rw [fieldAction_apply, Fin.sum_univ_succ]
    simp only [homogenizedField, Fin.cases_zero, zero_mul, Fin.cases_succ,
      Derivation.leibniz_pow, partial_coord, Fin.succ_ne_zero, if_false,
      smul_zero, mul_zero, Finset.sum_const_zero, add_zero]
  rw [liftedField_eq_scale, fieldDivergence_scale, hs, zero_add,
    homogenizedField_divergence (rationalPartial 4) (rationalPartial 5)
      chart.toRingHom (coord 0) coord v actual_homogeneousChart]
  rfl

def affineDefect (v : Fin 5 → RationalFunction 4) : RationalFunction 4 :=
  rationalDefect affineF affineA 2 v

theorem liftedField_defect (v : Fin 5 → RationalFunction 4) :
    rationalDefect HodgeSubmission.F HodgeSubmission.A 2 (liftedField v) =
      (coord (0 : Fin 6))^12 * chart (affineDefect v) := by
  unfold rationalDefect affineDefect
  rw [protected_F_chart, protected_A_chart, liftedField_action, liftedField_divergence]
  simp only [rationalDefect, map_add, map_sub, map_mul, map_natCast]
  ring

theorem exists_homogeneous_liftedField
    (v : Fin 5 → RationalFunction 4) (hv : ∀ i, RegularAlong affineF (v i)) :
    ∃ (d : ℕ) (D : AmbientPoly 5) (N : Fin 6 → AmbientPoly 5),
      D ≠ 0 ∧ D.IsHomogeneous d ∧ IsRelPrime HodgeSubmission.F D ∧
      (∀ i, (N i).IsHomogeneous (d + 7)) ∧
      rationalField D N = liftedField v := by
  classical
  obtain ⟨T, P, hT0, hFT, hv⟩ := regular_common_denominator affineF v hv
  let polys : Option (Fin 5) → AmbientPoly 4 := fun i => i.elim T P
  let d := ∑ i, (polys i).totalDegree
  have hb : ∀ i, (polys i).totalDegree ≤ d := fun i =>
    Finset.single_le_sum (fun j _ => Nat.zero_le (polys j).totalDegree) (Finset.mem_univ i)
  have ht : T.totalDegree ≤ d := hb none
  have hp : ∀ i, (P i).totalDegree ≤ d := fun i => hb (some i)
  let D := homogenize T d
  let N : Fin 6 → AmbientPoly 5 := Fin.cases 0
    (fun i => X (0 : Fin 6)^7 * homogenize (P i) d)
  refine ⟨d, D, N, homogenize_ne_zero ht hT0, homogenize_homogeneous T d ht,
    homogenize_legal ht hFT, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact isHomogeneous_zero _ _ _
    · simpa only [N, Fin.cases_succ, Nat.one_mul, Nat.add_comm] using
        ((isHomogeneous_X ℂ (0 : Fin 6)).pow 7).mul
          (homogenize_homogeneous (P j) d (hp j))
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [rationalField, N, liftedField]
    · change polynomialMap 5 (X (0 : Fin 6)^7 * homogenize (P j) d) /
        polynomialMap 5 (homogenize T d) =
        (coord (0 : Fin 6))^7 * chart (v j)
      rw [map_mul, map_pow, homogenize_chart (P j) d (hp j),
        homogenize_chart T d ht, hv j, map_div₀]
      have hscale := coord_ne_zero (0 : Fin 6)
      have hden : chart (polynomialMap 4 T) ≠ 0 :=
        (map_ne_zero chart).mpr (polynomialMap_ne_zero hT0)
      field_simp

theorem lifted_regular_residual
    (v : Fin 5 → RationalFunction 4)
    (h : RegularAlong affineF (affineDefect v / (polynomialMap 4 affineF)^3)) :
    RegularAlong HodgeSubmission.F
      (rationalDefect HodgeSubmission.F HodgeSubmission.A 2 (liftedField v) /
        (polynomialMap 5 HodgeSubmission.F)^3) := by
  have hX : IsRelPrime HodgeSubmission.F (X (0 : Fin 6)) :=
    CycleQ2ExactIrreducible.protected_F_irreducible.isRelPrime_iff_not_dvd.mpr
      (CycleQ2SupportEquation.not_dvd_coordinate_of_degree_gt_one HodgeSubmission.F
        (by rw [CycleQ2Workspace.originalF_totalDegree]; norm_num) 0)
  have hr := (regular_inv_polynomial HodgeSubmission.F (X (0 : Fin 6))
    (X_ne_zero 0) hX).pow 6
  have hc := hr.mul (regular_chart h)
  convert hc using 1
  rw [liftedField_defect, protected_F_chart, map_div₀, map_pow]
  have hs := coord_ne_zero (0 : Fin 6)
  have hf : chart (polynomialMap 4 affineF) ≠ 0 :=
    (map_ne_zero chart).mpr (polynomialMap_ne_zero affineF_ne_zero)
  simp only [coord]
  field_simp

/-- The complete algebraic implication from a genuine regular affine
primitive to the unchanged protected certificate. -/
theorem protected_certificate_of_affine_primitive
    (v : Fin 5 → RationalFunction 4)
    (hv : ∀ i, RegularAlong affineF (v i))
    (hres : RegularAlong affineF (affineDefect v / (polynomialMap 4 affineF)^3)) :
    HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A := by
  obtain ⟨d, D, N, hD0, hDhom, hFD, hN, hfield⟩ :=
    exists_homogeneous_liftedField v hv
  have hr := lifted_regular_residual v hres
  rw [← hfield] at hr
  obtain ⟨P, T, hT0, hFT, hr⟩ := hr
  have hlocal : LocalizedEquation HodgeSubmission.F HodgeSubmission.A 2 D N := by
    refine ⟨P, T, hT0, hFT, ?_⟩
    have hf := polynomialMap_ne_zero CycleQ2Workspace.originalF_ne_zero
    have ht := polynomialMap_ne_zero hT0
    field_simp at hr ⊢
    linear_combination hr
  have hdegree : D.totalDegree = d := hDhom.totalDegree hD0
  obtain ⟨Q, hQ⟩ := (exists_verify_iff_localizedEquation
    HodgeSubmission.F HodgeSubmission.A D 6 2 N
    CycleQ2Workspace.originalF_ne_zero CycleQ2Workspace.originalF_homogeneous
    (by simpa using Homogeneous.of_isHomogeneous CycleQ2Workspace.originalA_homogeneous)
    hD0 (by simpa only [hdegree] using hDhom)
    (fun i => by
      convert Homogeneous.of_isHomogeneous (hN i) using 1
      simp only [hdegree, Nat.cast_add, Nat.cast_ofNat]
      ring)
    hFD).mpr hlocal
  unfold HasCertificate
  rw [CycleQ2Workspace.originalF_totalDegree]
  exact ⟨D, N, Q, hQ⟩

end CycleQ2AffineCertificate

#print axioms CycleQ2AffineCertificate.protected_certificate_of_affine_primitive
end
end


/- Component: pole_reduction/AffineHypersurfaceDerivations.lean -/
section
/-!
# Actual tangent derivations on the protected projective affine chart

The coordinate ring is the actual quotient C[x0,...,x4]/(affineF), where
`affineF` is obtained from the protected sextic by setting homogeneous Z0=1.
Its fraction field is the function field of this affine hypersurface chart.
The four tangent derivations are constructed by quotient descent and
fraction-field extension, with all hypotheses proved for this exact equation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace CycleQ2AffineHypersurface

open MvPolynomial HodgeComputer CycleQ2AffineClearing CycleQ2AffineGeometry

abbrev AffineCoordinateRing := AmbientPoly 4 ⧸ Ideal.span {affineF}

instance affineCoordinateRing_isDomain : IsDomain AffineCoordinateRing :=
  (Ideal.Quotient.isDomain_iff_prime _).mpr
    ((Ideal.span_singleton_prime affineF_irreducible.ne_zero).mpr affineF_prime)

abbrev AffineFunctionField := FractionRing AffineCoordinateRing

local instance affineFunctionFieldIntAlgebra : Algebra ℤ AffineFunctionField :=
  Ring.toIntAlgebra _

/-- Actual projection to the protected affine chart's coordinate ring. -/
def affineProjection : AmbientPoly 4 →+* AffineCoordinateRing := Ideal.Quotient.mk _

theorem affineProjection_surjective : Function.Surjective affineProjection :=
  Ideal.Quotient.mk_surjective

theorem affineProjection_kernel (P : AmbientPoly 4) :
    affineProjection P = 0 ↔ affineF ∣ P := by
  simp only [affineProjection, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

/-- Actual polynomial class in the protected affine chart's function field. -/
def affineMap : AmbientPoly 4 →+* AffineFunctionField :=
  (algebraMap AffineCoordinateRing AffineFunctionField).comp affineProjection

theorem affineMap_kernel (P : AmbientPoly 4) :
    affineMap P = 0 ↔ affineF ∣ P := by
  constructor
  · intro h
    apply (affineProjection_kernel P).mp
    apply IsFractionRing.injective AffineCoordinateRing AffineFunctionField
    simpa only [affineMap, RingHom.comp_apply, map_zero] using h
  · intro h
    change algebraMap AffineCoordinateRing AffineFunctionField (affineProjection P) = 0
    rw [(affineProjection_kernel P).mpr h, map_zero]

@[simp] theorem affineMap_F : affineMap affineF = 0 :=
  (affineMap_kernel _).mpr (dvd_refl _)

/-- The normal derivative is nonzero in the actual affine function field. -/
theorem normal_ne_zero : affineMap (pderiv 0 affineF) ≠ 0 := by
  intro h
  exact affineF_not_dvd_normal ((affineMap_kernel _).mp h)

/-- Polynomial coordinate partials in the integer-linear interface used by
the trusted residue derivation construction. -/
def polynomialPartial (i : Fin 5) : Derivation ℤ (AmbientPoly 4) (AmbientPoly 4) :=
  (MvPolynomial.pderiv i).restrictScalars ℤ

@[simp] theorem polynomialPartial_apply (i : Fin 5) (P : AmbientPoly 4) :
    polynomialPartial i P = pderiv i P := rfl

theorem polynomialPartials_commute (i j : Fin 5) (P : AmbientPoly 4) :
    polynomialPartial i (polynomialPartial j P) =
      polynomialPartial j (polynomialPartial i P) :=
  CycleQ2Regularity.polynomial_partials_commute i j P

/-- The four actual tangent derivations, obtained by descent through (F)
followed by fraction-field extension. Coordinate zero is the eliminated normal. -/
def affineTangent (j : Fin 4) : Derivation ℤ AffineFunctionField AffineFunctionField :=
  HoldoutConstruction.residueTangent (K := AffineFunctionField)
    affineProjection affineProjection_surjective (polynomialPartial 0)
    (polynomialPartial j.succ) affineF affineProjection_kernel normal_ne_zero

/-- The actual tangent derivative has the implicit-coordinate formula on
every polynomial class. -/
theorem affineTangent_apply (j : Fin 4) (P : AmbientPoly 4) :
    affineTangent j (affineMap P) = affineMap (pderiv j.succ P) -
      affineMap (pderiv j.succ affineF) /
        affineMap (pderiv 0 affineF) * affineMap (pderiv 0 P) :=
  HoldoutConstruction.residueTangent_apply (K := AffineFunctionField)
    affineProjection affineProjection_surjective (polynomialPartial 0)
    (polynomialPartial j.succ) affineF affineProjection_kernel normal_ne_zero P

@[simp] theorem affineTangent_F (j : Fin 4) :
    affineTangent j (affineMap affineF) = 0 := by
  rw [affineMap_F, map_zero]

/-- All four constructed tangent derivations commute on the entire actual
affine chart function field; no derivative-compatibility assumption remains. -/
theorem affineTangents_commute (i j : Fin 4) :
    Function.Commute (affineTangent i) (affineTangent j) :=
  HoldoutConstruction.residueTangent_commute (K := AffineFunctionField)
    affineProjection affineProjection_surjective (polynomialPartial 0)
    (polynomialPartial i.succ) (polynomialPartial j.succ) affineF
    affineProjection_kernel normal_ne_zero (polynomialPartials_commute i.succ 0)
    (polynomialPartials_commute j.succ 0) (polynomialPartials_commute i.succ j.succ)

@[simp] theorem affineTangent_constant (j : Fin 4) (c : ℂ) :
    affineTangent j (affineMap (C c)) = 0 := by
  rw [affineTangent_apply]
  simp

/-- The independent coordinate classes have the expected Kronecker derivatives. -/
theorem affineTangent_coordinate (i j : Fin 4) :
    affineTangent i (affineMap (X j.succ)) = if j = i then 1 else 0 := by
  rw [affineTangent_apply]
  simp [pderiv_X, Pi.single_apply, Fin.succ_ne_zero]

/-- The eliminated coordinate differentiates by the implicit equation. -/
theorem affineTangent_normalCoordinate (i : Fin 4) :
    affineTangent i (affineMap (X 0)) =
      -affineMap (pderiv i.succ affineF) /
        affineMap (pderiv 0 affineF) := by
  rw [affineTangent_apply]
  simp [pderiv_X, Pi.single_apply, Fin.succ_ne_zero, div_eq_mul_inv]

end CycleQ2AffineHypersurface

#print axioms CycleQ2AffineHypersurface.normal_ne_zero
#print axioms CycleQ2AffineHypersurface.affineTangent_apply
#print axioms CycleQ2AffineHypersurface.affineTangents_commute
end
end


/- Component: pole_reduction/AffineRegularResidue.lean -/
section
/-!
# Actual residue homomorphism on the protected projective affine chart

The domain is the actual subring of five-variable ambient fractions admitting
a denominator relatively prime to affineF. The target is the actual fraction
field of the protected hypersurface chart Z0=1.
The representative-choice map is proved independent by cross multiplication.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace CycleQ2AffineResidue

open MvPolynomial HodgeComputer CycleQ2Bridge CycleQ2Regularity CycleQ2AffineHypersurface
  CycleQ2AffineClearing CycleQ2AffineGeometry

abbrev Poly := AmbientPoly 4
abbrev RatFun := RationalFunction 4

/-- The actual ring of ambient rational functions regular along F. -/
def RegularAtF : Subring RatFun where
  carrier := {z | RegularAlong affineF z}
  zero_mem' := regular_zero _
  one_mem' := regular_one _
  add_mem' := fun hx hy => hx.add hy
  mul_mem' := fun hx hy => hx.mul hy
  neg_mem' := fun hx => hx.neg

private def presentationNumerator (z : RegularAtF) : Poly :=
  Classical.choose z.property

private def presentationDenominator (z : RegularAtF) : Poly :=
  Classical.choose (Classical.choose_spec z.property)

private theorem presentation_spec (z : RegularAtF) :
    presentationDenominator z ≠ 0 ∧
    IsRelPrime affineF (presentationDenominator z) ∧
    (z : RatFun) = polynomialMap 4 (presentationNumerator z) /
      polynomialMap 4 (presentationDenominator z) :=
  Classical.choose_spec (Classical.choose_spec z.property)

/-- Every legal ambient denominator maps to a nonzero affine-chart-function-field element. -/
theorem legal_affineMap_ne_zero (T : Poly) (hT : IsRelPrime affineF T) :
    affineMap T ≠ 0 := by
  intro h
  exact (affineF_irreducible.isRelPrime_iff_not_dvd.mp hT)
    ((affineMap_kernel T).mp h)

private def residueValue (z : RegularAtF) : AffineFunctionField :=
  affineMap (presentationNumerator z) / affineMap (presentationDenominator z)

/-- Representative independence uses the injective ambient fraction map and
polynomial cross multiplication, not a chosen representative axiom. -/
private theorem residueValue_eq (z : RegularAtF) (P T : Poly)
    (hT : T ≠ 0) (hFT : IsRelPrime affineF T)
    (hz : (z : RatFun) = polynomialMap 4 P / polynomialMap 4 T) :
    residueValue z = affineMap P / affineMap T := by
  have hs := presentation_spec z
  have hcross : presentationNumerator z * T = P * presentationDenominator z := by
    apply polynomialMap_injective
    simpa only [map_mul] using
      (div_eq_div_iff (polynomialMap_ne_zero hs.1) (polynomialMap_ne_zero hT)).mp
        (hs.2.2.symm.trans hz)
  apply (div_eq_div_iff
    (legal_affineMap_ne_zero _ hs.2.1) (legal_affineMap_ne_zero T hFT)).mpr
  simpa only [map_mul] using congrArg affineMap hcross

private theorem residueValue_zero : residueValue 0 = 0 := by
  simpa using residueValue_eq 0 0 1 one_ne_zero isRelPrime_one_right (by simp)

private theorem residueValue_one : residueValue 1 = 1 := by
  simpa using residueValue_eq 1 1 1 one_ne_zero isRelPrime_one_right (by simp)

private theorem residueValue_add (x y : RegularAtF) :
    residueValue (x + y) = residueValue x + residueValue y := by
  obtain ⟨P, T, hT, hFT, hx⟩ := x.property
  obtain ⟨Q, U, hU, hFU, hy⟩ := y.property
  have hxy : ((x + y : RegularAtF) : RatFun) =
      polynomialMap 4 (P * U + Q * T) / polynomialMap 4 (T * U) := by
    change (x : RatFun) + (y : RatFun) = _
    rw [hx, hy]
    have hT' := polynomialMap_ne_zero hT
    have hU' := polynomialMap_ne_zero hU
    simp only [map_add, map_mul]
    field_simp
  rw [residueValue_eq _ _ _ (mul_ne_zero hT hU) (hFT.mul_right hFU) hxy,
    residueValue_eq x P T hT hFT hx, residueValue_eq y Q U hU hFU hy]
  have hT' := legal_affineMap_ne_zero T hFT
  have hU' := legal_affineMap_ne_zero U hFU
  simp only [map_add, map_mul]
  field_simp

private theorem residueValue_mul (x y : RegularAtF) :
    residueValue (x * y) = residueValue x * residueValue y := by
  obtain ⟨P, T, hT, hFT, hx⟩ := x.property
  obtain ⟨Q, U, hU, hFU, hy⟩ := y.property
  have hxy : ((x * y : RegularAtF) : RatFun) =
      polynomialMap 4 (P * Q) / polynomialMap 4 (T * U) := by
    change (x : RatFun) * (y : RatFun) = _
    rw [hx, hy]
    simp only [map_mul, mul_div_mul_comm]
  rw [residueValue_eq _ _ _ (mul_ne_zero hT hU) (hFT.mul_right hFU) hxy,
    residueValue_eq x P T hT hFT hx, residueValue_eq y Q U hU hFU hy]
  simp only [map_mul, mul_div_mul_comm]

/-- The actual residue homomorphism from the regular subring to the protected
affine chart function field. All ring-homomorphism laws are proved above. -/
def residue : RegularAtF →+* AffineFunctionField where
  toFun := residueValue
  map_zero' := residueValue_zero
  map_one' := residueValue_one
  map_add' := residueValue_add
  map_mul' := residueValue_mul

theorem residue_fraction (z : RegularAtF) (P T : Poly)
    (hT : T ≠ 0) (hFT : IsRelPrime affineF T)
    (hz : (z : RatFun) = polynomialMap 4 P / polynomialMap 4 T) :
    residue z = affineMap P / affineMap T :=
  residueValue_eq z P T hT hFT hz

/-- A polynomial viewed in the regular ambient subring. -/
def polynomialRegular (P : Poly) : RegularAtF :=
  ⟨polynomialMap 4 P, regular_polynomial affineF P⟩

@[simp] theorem residue_polynomial (P : Poly) :
    residue (polynomialRegular P) = affineMap P := by
  simpa using residue_fraction (polynomialRegular P) P 1
    one_ne_zero isRelPrime_one_right (by simp [polynomialRegular])

theorem residue_fraction_eq_zero_iff (z : RegularAtF) (P T : Poly)
    (hT : T ≠ 0) (hFT : IsRelPrime affineF T)
    (hz : (z : RatFun) = polynomialMap 4 P / polynomialMap 4 T) :
    residue z = 0 ↔ affineF ∣ P := by
  rw [residue_fraction z P T hT hFT hz]
  have hT' := legal_affineMap_ne_zero T hFT
  rw [div_eq_zero_iff]
  simp only [hT', or_false]
  exact affineMap_kernel P

/-- The actual residue kernel is exactly multiplication by F inside the
regular subring. The quotient coefficient is still regular along F. -/
theorem residue_eq_zero_iff_exists_F_mul (z : RegularAtF) :
    residue z = 0 ↔ ∃ t : RegularAtF,
      (z : RatFun) = polynomialMap 4 affineF * (t : RatFun) := by
  constructor
  · intro hz
    obtain ⟨P, T, hT, hFT, hrepr⟩ := z.property
    obtain ⟨Q, hQ⟩ := (residue_fraction_eq_zero_iff z P T hT hFT hrepr).mp hz
    let t : RegularAtF := ⟨polynomialMap 4 Q / polynomialMap 4 T,
      ⟨Q, T, hT, hFT, rfl⟩⟩
    refine ⟨t, ?_⟩
    change (z : RatFun) = polynomialMap 4 affineF *
      (polynomialMap 4 Q / polynomialMap 4 T)
    rw [hrepr, hQ, map_mul]
    ring
  · rintro ⟨t, ht⟩
    have he : z = polynomialRegular affineF * t := Subtype.ext ht
    rw [he, map_mul, residue_polynomial, affineMap_F, zero_mul]

/-- Equivalent form convenient for pole reduction: vanishing residue means
one can divide by F while remaining in the actual regular subring. -/
theorem residue_eq_zero_iff_regular_div_F (z : RegularAtF) :
    residue z = 0 ↔ RegularAlong affineF
      ((z : RatFun) / polynomialMap 4 affineF) := by
  have hF := polynomialMap_ne_zero affineF_irreducible.ne_zero
  constructor
  · intro hz
    obtain ⟨t, ht⟩ := (residue_eq_zero_iff_exists_F_mul z).mp hz
    have he : (z : RatFun) / polynomialMap 4 affineF = (t : RatFun) := by
      rw [ht]
      field_simp
    rw [he]
    exact t.property
  · intro hz
    apply (residue_eq_zero_iff_exists_F_mul z).mpr
    refine ⟨⟨(z : RatFun) / polynomialMap 4 affineF, hz⟩, ?_⟩
    change (z : RatFun) = polynomialMap 4 affineF *
      ((z : RatFun) / polynomialMap 4 affineF)
    field_simp


open CycleQ2ActualResidueClosure

local instance rationalFunctionIntAlgebra : Algebra ℤ RatFun := Ring.toIntAlgebra _
local instance affineFunctionFieldIntAlgebra : Algebra ℤ AffineFunctionField := Ring.toIntAlgebra _
local instance regularAtFIntAlgebra : Algebra ℤ RegularAtF := Ring.toIntAlgebra _

/-- The exact normal polynomial is nonzero before quotienting as well. -/
theorem normal_polynomial_ne_zero : pderiv 0 affineF ≠ 0 := by
  intro h
  apply normal_ne_zero
  rw [h, map_zero]

theorem normal_polynomial_relPrime :
    IsRelPrime affineF (pderiv 0 affineF) :=
  affineF_irreducible.isRelPrime_iff_not_dvd.mpr
    affineF_not_dvd_normal

/-- Restriction of the actual ambient tangent derivation to the actual regular
subring. Closure is proved from the quotient rule and normal-denominator legality. -/
def regularTangent (j : Fin 4) : Derivation ℤ RegularAtF RegularAtF :=
  Derivation.mk'
    ({ toFun := fun z => ⟨actualTangent affineF j (z : RatFun),
         regular_actualTangent z.property normal_polynomial_ne_zero
           normal_polynomial_relPrime j⟩
       map_zero' := Subtype.ext (map_zero _)
       map_add' := fun x y => Subtype.ext (map_add _ _ _)
     } : RegularAtF →+ RegularAtF).toIntLinearMap
    (by
      intro x y
      apply Subtype.ext
      change actualTangent affineF j ((x : RatFun) * (y : RatFun)) =
        (x : RatFun) * actualTangent affineF j (y : RatFun) +
          (y : RatFun) * actualTangent affineF j (x : RatFun)
      simpa only [smul_eq_mul] using
        (actualTangent affineF j).leibniz (x : RatFun) (y : RatFun))

@[simp] theorem regularTangent_apply (j : Fin 4) (z : RegularAtF) :
    ((regularTangent j z : RegularAtF) : RatFun) =
      actualTangent affineF j (z : RatFun) := rfl

@[simp] theorem residue_regularTangent_polynomial (j : Fin 4) (P : Poly) :
    residue (regularTangent j (polynomialRegular P)) =
      affineTangent j (affineMap P) := by
  let Q : Poly := pderiv 0 affineF * pderiv j.succ P -
    pderiv j.succ affineF * pderiv 0 P
  have hrepr : ((regularTangent j (polynomialRegular P) : RegularAtF) : RatFun) =
      polynomialMap 4 Q / polynomialMap 4 (pderiv 0 affineF) := by
    change actualTangent affineF j (polynomialMap 4 P) = _
    rw [actualTangent_apply]
    simp only [Q, rationalPartial_map, map_sub, map_mul]
    have hg := polynomialMap_ne_zero normal_polynomial_ne_zero
    field_simp <;> ring
  rw [residue_fraction _ Q _ normal_polynomial_ne_zero normal_polynomial_relPrime hrepr,
    affineTangent_apply]
  simp only [Q, map_sub, map_mul]
  have hg := normal_ne_zero
  field_simp <;> ring

/-- Exact compatibility of the actual regular-subring residue homomorphism
with the actual constructed tangent derivations on the affine chart function field. -/
theorem residue_regularTangent (j : Fin 4) (z : RegularAtF) :
    residue (regularTangent j z) = affineTangent j (residue z) := by
  obtain ⟨P, T, hT, hFT, hz⟩ := z.property
  have hprod : z * polynomialRegular T = polynomialRegular P := by
    apply Subtype.ext
    change (z : RatFun) * polynomialMap 4 T = polynomialMap 4 P
    rw [hz, div_mul_cancel₀ _ (polynomialMap_ne_zero hT)]
  have h₁ := congrArg (fun u : RegularAtF => residue (regularTangent j u)) hprod
  rw [Derivation.leibniz] at h₁
  simp only [smul_eq_mul, map_add, map_mul, residue_polynomial,
    residue_regularTangent_polynomial] at h₁
  have h₂ := congrArg (fun u : RegularAtF => affineTangent j (residue u)) hprod
  simp only [map_mul, residue_polynomial, Derivation.leibniz, smul_eq_mul] at h₂
  apply mul_left_cancel₀ (legal_affineMap_ne_zero T hFT)
  linear_combination h₁ - h₂


/-- Every element of the actual affine chart function field lifts to an actual
ambient fraction regular along affineF. The chart construction supplies
the projective interpretation independently of any grading of this lift. -/
theorem residue_surjective : Function.Surjective residue := by
  intro w
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective AffineCoordinateRing w
  obtain ⟨P, rfl⟩ := affineProjection_surjective a
  obtain ⟨T, rfl⟩ := affineProjection_surjective b
  have hden : affineMap T ≠ 0 := by
    change algebraMap AffineCoordinateRing AffineFunctionField (affineProjection T) ≠ 0
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hT : T ≠ 0 := by
    intro h
    apply hden
    rw [h, map_zero]
  have hFT : IsRelPrime affineF T :=
    affineF_irreducible.isRelPrime_iff_not_dvd.mpr
      (fun h => hden ((affineMap_kernel T).mpr h))
  let z : RegularAtF := ⟨polynomialMap 4 P / polynomialMap 4 T,
    ⟨P, T, hT, hFT, rfl⟩⟩
  refine ⟨z, ?_⟩
  exact residue_fraction z P T hT hFT rfl

/-- A nonconstructive lift, justified by the proved residue surjectivity. -/
def liftResidue (w : AffineFunctionField) : RegularAtF :=
  Function.surjInv residue_surjective w

@[simp] theorem residue_liftResidue (w : AffineFunctionField) :
    residue (liftResidue w) = w := Function.surjInv_eq residue_surjective w

end CycleQ2AffineResidue

#print axioms CycleQ2AffineResidue.residue_fraction
#print axioms CycleQ2AffineResidue.residue_eq_zero_iff_exists_F_mul
#print axioms CycleQ2AffineResidue.residue_eq_zero_iff_regular_div_F

#print axioms CycleQ2AffineResidue.residue_regularTangent

#print axioms CycleQ2AffineResidue.residue_surjective
#print axioms CycleQ2AffineResidue.residue_liftResidue
end
end


/- Component: pole_reduction/AffineResidueClosure.lean -/
section
/-!
Concrete closure of an actual residue primitive on the protected X0=1 chart.

The source, quotient function field, derivations, regular lifts, homogeneous
clearing, and final certificate are all bound to the actual protected instance.
The final theorem still explicitly requires existence of the affine residue
primitive; that geometric existence statement is not asserted here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace CycleQ2AffineResidueClosure

open MvPolynomial HodgeComputer CycleQ2Bridge CycleQ2Regularity
open CycleQ2AffineHypersurface CycleQ2AffineResidue CycleQ2ActualResidueClosure
open CycleQ2AffineClearing CycleQ2AffineCertificate
open HoldoutConstruction SplitHigherResidue
open scoped BigOperators

local instance rationalFunctionIntAlgebra : Algebra ℤ RatFun := Ring.toIntAlgebra _
local instance affineFunctionFieldIntAlgebra : Algebra ℤ AffineFunctionField := Ring.toIntAlgebra _
local instance regularAtFIntAlgebra : Algebra ℤ RegularAtF := Ring.toIntAlgebra _

private theorem two_polynomial_relPrime : IsRelPrime affineF (2 : Poly) := by
  have hu : IsUnit (2 : Poly) := by
    simpa only [map_ofNat] using
      (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℂ) ≠ 0)).map (C : ℂ →+* Poly)
  exact hu.isRelPrime_right

/-- The genuine inverse of the normal polynomial in the regular subring. -/
def normalInverse : RegularAtF :=
  ⟨(polynomialMap 4 (pderiv 0 affineF))⁻¹,
    regular_inv_polynomial _ _ normal_polynomial_ne_zero normal_polynomial_relPrime⟩

@[simp] theorem normalInverse_val :
    (normalInverse : RatFun) = (polynomialMap 4 (pderiv 0 affineF))⁻¹ := rfl

@[simp] theorem residue_normalInverse :
    residue normalInverse = (affineMap (pderiv 0 affineF))⁻¹ := by
  simpa using residue_fraction normalInverse 1 (pderiv 0 affineF)
    normal_polynomial_ne_zero normal_polynomial_relPrime (by simp [normalInverse])

private def halfRegular : RegularAtF :=
  ⟨(1 / 2 : RatFun), by
    change RegularAlong affineF (1 / 2 : RatFun)
    simpa only [map_ofNat, one_div] using regular_inv_polynomial affineF (2 : Poly)
      (by norm_num) two_polynomial_relPrime⟩

private theorem halfRegular_val : (halfRegular : RatFun) = (1 / 2 : RatFun) := rfl

private theorem residue_halfRegular : residue halfRegular = (1 / 2 : AffineFunctionField) := by
  simpa only [map_one, map_ofNat] using residue_fraction halfRegular 1 (2 : Poly)
    (by norm_num) two_polynomial_relPrime (by
      change (1 / 2 : RatFun) = polynomialMap 4 1 / polynomialMap 4 2
      simp only [map_one, map_ofNat])

/-- The exact normal source, now evaluated in the actual affine function field. -/
def affineNormalSource (A : Poly) : AffineFunctionField :=
  normalSourceTwo (affineMap A) (affineMap (pderiv 0 A))
    (affineMap (pderiv 0 (pderiv 0 A)))
    (affineMap (pderiv 0 affineF))
    (affineMap (pderiv 0 (pderiv 0 affineF)))
    (affineMap (pderiv 0 (pderiv 0 (pderiv 0 affineF))))

/-- The concrete function-field residue equation whose solution is required. -/
def affineResidueExpression (A : Poly) (w : Fin 4 → AffineFunctionField) : AffineFunctionField :=
  affineNormalSource A +
    residueDivergence affineTangent (affineMap (pderiv 0 affineF)) w

private def normalSourceRegular (A : Poly) : RegularAtF :=
  halfRegular *
    (polynomialRegular (pderiv 0 (pderiv 0 A)) * normalInverse ^ 2 -
      (3 * polynomialRegular (pderiv 0 A) *
          polynomialRegular (pderiv 0 (pderiv 0 affineF)) +
        polynomialRegular A * polynomialRegular (pderiv 0 (pderiv 0 (pderiv 0 affineF)))) *
        normalInverse ^ 3 +
      3 * polynomialRegular A * polynomialRegular (pderiv 0 (pderiv 0 affineF)) ^ 2 *
        normalInverse ^ 4)

private theorem normalSourceRegular_val (A : Poly) :
    ((normalSourceRegular A : RegularAtF) : RatFun) =
      actualNormalSource affineF A := by
  change RegularAtF.subtype (normalSourceRegular A) = _
  simp only [normalSourceRegular, actualNormalSource, normalSourceTwo,
    map_mul, map_add, map_sub, map_pow, map_ofNat, Subring.subtype_apply,
    halfRegular_val, normalInverse_val, polynomialRegular,
    div_eq_mul_inv, inv_pow]

private theorem residue_normalSourceRegular (A : Poly) :
    residue (normalSourceRegular A) = affineNormalSource A := by
  simp only [normalSourceRegular, map_mul, map_add, map_sub, map_pow, map_ofNat,
    residue_halfRegular, residue_normalInverse, residue_polynomial,
    affineNormalSource, normalSourceTwo, div_eq_mul_inv, inv_pow]

/-- The actual regular-subring lift of the entire residue equation. -/
def residueExpressionRegular (A : Poly) (w : Fin 4 → RegularAtF) : RegularAtF :=
  normalSourceRegular A +
    (∑ j, regularTangent j (w j)) -
    (∑ j, w j * regularTangent j (polynomialRegular (pderiv 0 affineF))) *
      normalInverse

theorem residueExpressionRegular_val (A : Poly) (w : Fin 4 → RegularAtF) :
    ((residueExpressionRegular A w : RegularAtF) : RatFun) =
      actualResidueExpression affineF A (fun j => (w j : RatFun)) := by
  change RegularAtF.subtype (residueExpressionRegular A w) = _
  simp only [residueExpressionRegular, map_add, map_sub, map_mul,
    map_sum, Subring.subtype_apply, regularTangent_apply, normalSourceRegular_val, normalInverse_val,
    polynomialRegular, actualResidueExpression, residueDivergence,
    HoldoutConstruction.fieldDivergence, div_eq_mul_inv]
  ring

/-- The ambient source and tangent divergence transport to the actual quotient
equation through the proved residue homomorphism. -/
theorem residue_residueExpressionRegular (A : Poly) (w : Fin 4 → RegularAtF) :
    residue (residueExpressionRegular A w) =
      affineResidueExpression A (fun j => residue (w j)) := by
  simp only [residueExpressionRegular, map_add, map_sub, map_mul, map_sum,
    residue_normalSourceRegular, residue_regularTangent, residue_polynomial,
    residue_normalInverse, affineResidueExpression, residueDivergence,
    HoldoutConstruction.fieldDivergence, div_eq_mul_inv]
  ring

/-- A solved affine residue equation for actual regular lifts gives an actual
regular ambient vector with third-order defect. Homogeneity is not asserted. -/
theorem regular_affine_primitive_closure (A : Poly) (w : Fin 4 → RegularAtF)
    (hres : affineResidueExpression A (fun j => residue (w j)) = 0) :
    ∃ (v : Fin 5 → RatFun) (t : RatFun),
      (∀ i, RegularAlong affineF (v i)) ∧
      RegularAlong affineF t ∧
      rationalDefect affineF A 2 v =
        polynomialMap 4 affineF ^ 3 * t := by
  have hz : residue (residueExpressionRegular A w) = 0 := by
    rw [residue_residueExpressionRegular]
    exact hres
  obtain ⟨t, ht⟩ := (residue_eq_zero_iff_exists_F_mul (residueExpressionRegular A w)).mp hz
  refine ⟨actualClosureVector affineF A (fun j => (w j : RatFun)), t,
    ?_, t.property, ?_⟩
  · exact regular_actualClosureVector affineF A _ normal_polynomial_ne_zero
      normal_polynomial_relPrime (fun j => (w j).property)
  · apply actualClosure_defect_of_residue affineF A _ _ normal_polynomial_ne_zero
    rw [← residueExpressionRegular_val]
    exact ht

/-- Every actual affine primitive has regular ambient lifts. This conclusion
is the rational defect equation; no homogeneous-degree conclusion is hidden. -/
theorem affine_primitive_closure (A : Poly) (w : Fin 4 → AffineFunctionField)
    (hres : affineResidueExpression A w = 0) :
    ∃ (v : Fin 5 → RatFun) (t : RatFun),
      (∀ i, RegularAlong affineF (v i)) ∧
      RegularAlong affineF t ∧
      rationalDefect affineF A 2 v =
        polynomialMap 4 affineF ^ 3 * t := by
  apply regular_affine_primitive_closure A (fun j => liftResidue (w j))
  simpa only [residue_liftResidue] using hres

/-- The exact chart numerator is bound here to the concrete affine equation.
Its remaining primitive-existence hypothesis is stated explicitly. -/
theorem protected_regular_ambient_of_affine_primitive
    (h : ∃ w : Fin 4 → AffineFunctionField,
      affineResidueExpression affineA w = 0) :
    ∃ (v : Fin 5 → RatFun) (t : RatFun),
      (∀ i, RegularAlong affineF (v i)) ∧
      RegularAlong affineF t ∧
      rationalDefect affineF affineA 2 v =
        polynomialMap 4 affineF ^ 3 * t := by
  obtain ⟨w, hw⟩ := h
  exact affine_primitive_closure affineA w hw

/-- A primitive for the exact affine function-field residue implies the
unchanged protected certificate. All field, derivative, regularity,
homogeneity, and denominator-legality steps are proved by this point. -/
theorem protected_certificate_of_affine_residue_primitive
    (h : ∃ w : Fin 4 → AffineFunctionField,
      affineResidueExpression affineA w = 0) :
    HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A := by
  obtain ⟨v, t, hv, ht, heq⟩ := protected_regular_ambient_of_affine_primitive h
  apply CycleQ2AffineCertificate.protected_certificate_of_affine_primitive v hv
  change RegularAlong affineF
    (rationalDefect affineF affineA 2 v / (polynomialMap 4 affineF) ^ 3)
  rw [heq]
  have hf := polynomialMap_ne_zero affineF_ne_zero
  have hquotient : polynomialMap 4 affineF ^ 3 * t / polynomialMap 4 affineF ^ 3 = t := by
    field_simp
  rw [hquotient]
  exact ht

end CycleQ2AffineResidueClosure

#print axioms CycleQ2AffineResidueClosure.residue_residueExpressionRegular
#print axioms CycleQ2AffineResidueClosure.regular_affine_primitive_closure
#print axioms CycleQ2AffineResidueClosure.protected_regular_ambient_of_affine_primitive
#print axioms CycleQ2AffineResidueClosure.protected_certificate_of_affine_residue_primitive
end
end


/- Component: continuation_2/AffineKaehler.lean -/
section
/-!
# Actual relative Kähler differentials of the protected affine chart

The four independent coordinate differentials form a basis of the genuine
mathlib module Ω[K⁄ℂ], where K is the already constructed function field of
the exact chart F(1,x)=0. The universal differential is computed by the
already constructed tangent derivations. No cohomological vanishing or
primitive-existence hypothesis is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace CycleQ2AffineDifferentials

open MvPolynomial HodgeComputer CycleQ2AffineHypersurface CycleQ2AffineClearing
open scoped BigOperators

abbrev K := AffineFunctionField
abbrev Omega := Ω[K⁄ℂ]

local instance intAlgebra : Algebra ℤ K := Ring.toIntAlgebra _

theorem affineMap_eq_algebraMap (P : AmbientPoly 4) :
    affineMap P = algebraMap (AmbientPoly 4) K P := rfl

theorem affineMap_constant (c : ℂ) :
    affineMap (C c) = algebraMap ℂ K c := rfl

theorem tangent_complex_constant (j : Fin 4) (c : ℂ) :
    affineTangent j (algebraMap ℂ K c) = 0 := by
  rw [← affineMap_constant]
  exact affineTangent_constant j c

theorem tangent_complex_smul (j : Fin 4) (c : ℂ) (z : K) :
    affineTangent j (c • z) = c • affineTangent j z := by
  simp only [Algebra.smul_def, Derivation.leibniz, smul_eq_mul,
    tangent_complex_constant, mul_zero, add_zero]
  simp

/-- The actual tangent operator, with its complex scalar linearity included
in the type. Its underlying function is unchanged. -/
def complexTangent (j : Fin 4) : Derivation ℂ K K where
  toFun := affineTangent j
  map_add' := (affineTangent j).map_add
  map_smul' := tangent_complex_smul j
  map_one_eq_zero' := (affineTangent j).map_one_eq_zero
  leibniz' := (affineTangent j).leibniz

@[simp] theorem complexTangent_apply (j : Fin 4) (z : K) :
    complexTangent j z = affineTangent j z := rfl

abbrev d : Derivation ℂ K Omega := KaehlerDifferential.D ℂ K

/-- The four independent coordinate differentials in the actual universal
module of relative differentials. -/
def coordinateDifferential (j : Fin 4) : Omega := d (affineMap (X j.succ))

private theorem sum_derivations_apply
    (q : Fin 5 → Derivation ℂ (AmbientPoly 4) Omega) (P : AmbientPoly 4) :
    (∑ i, q i) P = ∑ i, q i P := by
  simpa only [Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply] using
    congrFun (map_sum Derivation.coeFnAddMonoidHom q Finset.univ) P

theorem differential_polynomial (P : AmbientPoly 4) :
    d (affineMap P) = ∑ i : Fin 5, affineMap (pderiv i P) • d (affineMap (X i)) := by
  let dp : Derivation ℂ (AmbientPoly 4) Omega := d.compAlgebraMap (AmbientPoly 4)
  have he : dp = ∑ i : Fin 5,
      (LinearMap.toSpanSingleton (AmbientPoly 4) Omega (dp (X i))).compDer (pderiv i) := by
    apply MvPolynomial.derivation_ext
    intro i
    rw [sum_derivations_apply]
    simp [Derivation.coe_comp, pderiv_X, Pi.single_apply]
  have hh := Derivation.congr_fun he P
  rw [sum_derivations_apply] at hh
  simpa only [dp, Derivation.compAlgebraMap_apply,
    Derivation.coe_comp, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
    Derivation.coeFn_coe, LinearMap.toSpanSingleton_apply,
    affineMap_eq_algebraMap, IsScalarTower.algebraMap_smul] using hh

theorem differential_normal :
    d (affineMap (X (0 : Fin 5))) =
      ∑ j : Fin 4, (-affineMap (pderiv j.succ affineF) /
        affineMap (pderiv 0 affineF)) • coordinateDifferential j := by
  have hf := differential_polynomial affineF
  rw [affineMap_F, map_zero, Fin.sum_univ_succ] at hf
  have he : affineMap (pderiv 0 affineF) • d (affineMap (X (0 : Fin 5))) =
      -(∑ j : Fin 4, affineMap (pderiv j.succ affineF) • coordinateDifferential j) :=
    eq_neg_of_add_eq_zero_left hf.symm
  calc
    _ = (affineMap (pderiv 0 affineF))⁻¹ •
        (affineMap (pderiv 0 affineF) • d (affineMap (X (0 : Fin 5)))) := by
      rw [smul_smul, inv_mul_cancel₀ normal_ne_zero, one_smul]
    _ = _ := by
      rw [he]
      simp only [smul_neg, Finset.smul_sum, smul_smul]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← neg_smul]
      congr 1
      simp [div_eq_mul_inv, mul_comm]

theorem differential_polynomial_coordinates (P : AmbientPoly 4) :
    d (affineMap P) =
      ∑ j : Fin 4, affineTangent j (affineMap P) • coordinateDifferential j := by
  rw [differential_polynomial, Fin.sum_univ_succ, differential_normal, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [affineTangent_apply, smul_smul]
  simp only [coordinateDifferential]
  rw [← add_smul]
  congr 1
  ring

/-- The universal differential on every element of the actual chart field
is exactly its four actual implicit-coordinate partial derivatives. -/
theorem differential_coordinates (z : K) :
    d z = ∑ j : Fin 4, affineTangent j z • coordinateDifferential j := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective AffineCoordinateRing z
  obtain ⟨P, rfl⟩ := affineProjection_surjective a
  obtain ⟨T, rfl⟩ := affineProjection_surjective b
  change d (affineMap P / affineMap T) =
    ∑ j : Fin 4, affineTangent j (affineMap P / affineMap T) • coordinateDifferential j
  rw [Derivation.leibniz_div, differential_polynomial_coordinates,
    differential_polynomial_coordinates]
  simp only [Derivation.leibniz_div, Finset.smul_sum, smul_sub,
    ← Finset.sum_sub_distrib, smul_smul, smul_eq_mul, sub_smul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_sub, sub_smul]

/-- Evaluation of a universal differential against the four actual
complex tangent derivations. -/
def coordinateMap : Omega →ₗ[K] (Fin 4 → K) :=
  LinearMap.pi fun j => (complexTangent j).liftKaehlerDifferential

@[simp] theorem coordinateMap_d (z : K) (j : Fin 4) :
    coordinateMap (d z) j = affineTangent j z :=
  Derivation.liftKaehlerDifferential_comp_D (complexTangent j) z

@[simp] theorem coordinateMap_coordinateDifferential (i j : Fin 4) :
    coordinateMap (coordinateDifferential i) j = if i = j then 1 else 0 := by
  change coordinateMap (d (affineMap (X i.succ))) j = _
  rw [coordinateMap_d]
  exact affineTangent_coordinate j i

def coordinateExpansion : (Fin 4 → K) →ₗ[K] Omega :=
  Fintype.linearCombination K coordinateDifferential

@[simp] theorem coordinateExpansion_apply (v : Fin 4 → K) :
    coordinateExpansion v = ∑ j, v j • coordinateDifferential j := rfl

theorem coordinateExpansion_coordinateMap :
    coordinateExpansion.comp coordinateMap = LinearMap.id := by
  apply Derivation.liftKaehlerDifferential_unique
  ext z
  change coordinateExpansion (coordinateMap (d z)) = d z
  rw [coordinateExpansion_apply]
  simp only [coordinateMap_d]
  exact (differential_coordinates z).symm

theorem coordinateMap_coordinateExpansion :
    coordinateMap.comp coordinateExpansion = LinearMap.id := by
  ext v j
  simp [coordinateExpansion_apply, coordinateMap_coordinateDifferential,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, eq_comm]

/-- Concrete coordinates on the actual relative Kähler module. -/
def differentialCoordinates : Omega ≃ₗ[K] (Fin 4 → K) where
  toLinearMap := coordinateMap
  invFun := coordinateExpansion
  left_inv z := LinearMap.congr_fun coordinateExpansion_coordinateMap z
  right_inv v := LinearMap.congr_fun coordinateMap_coordinateExpansion v

/-- The four independent coordinate differentials are a basis. -/
def coordinateBasis : Module.Basis (Fin 4) K Omega :=
  Module.Basis.ofEquivFun differentialCoordinates

@[simp] theorem coordinateBasis_apply (j : Fin 4) :
    coordinateBasis j = coordinateDifferential j := by
  rw [coordinateBasis, Module.Basis.coe_ofEquivFun]
  change coordinateExpansion (Pi.single j 1) = coordinateDifferential j
  simp [coordinateExpansion]

@[simp] theorem coordinateBasis_repr_d (z : K) (j : Fin 4) :
    coordinateBasis.repr (d z) j = affineTangent j z := by
  rw [coordinateBasis, Module.Basis.ofEquivFun_repr_apply]
  exact coordinateMap_d z j

end CycleQ2AffineDifferentials

#print axioms CycleQ2AffineDifferentials.differential_coordinates
#print axioms CycleQ2AffineDifferentials.coordinateBasis_apply
#print axioms CycleQ2AffineDifferentials.coordinateBasis_repr_d
end
end


/- Component: continuation_2/AffineExterior.lean -/
section
/-!
# Genuine exterior forms on the protected hypersurface function field

This file works with exterior powers of the actual relative Kähler module.
The coordinate exterior derivative is characterized on the exact coordinate
generators, and its top-degree exactness criterion is compared with the
already defined residue equation. It asserts no geometric vanishing.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace CycleQ2AffineExterior

open CycleQ2AffineDifferentials CycleQ2AffineHypersurface
open scoped BigOperators

abbrev Form (p : ℕ) := ⋀[K]^p Omega

def omitIndex (i : Fin 4) : Set.powersetCard (Fin 4) 3 :=
  ⟨{i}ᶜ, by simp [Finset.card_compl]⟩

theorem omitIndex_bijective : Function.Bijective omitIndex := by
  constructor
  · intro i j hij
    have he := congrArg (fun s : Set.powersetCard (Fin 4) 3 => (s : Finset (Fin 4))ᶜ) hij
    simpa only [omitIndex, compl_compl, Finset.singleton_inj] using he
  · intro s
    have hc : ((s : Finset (Fin 4))ᶜ).card = 1 := by
      simp [Finset.card_compl, s.property]
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
    refine ⟨i, Subtype.ext ?_⟩
    change {i}ᶜ = (s : Finset (Fin 4))
    rw [← hi, compl_compl]

def omitEquiv : Fin 4 ≃ Set.powersetCard (Fin 4) 3 :=
  Equiv.ofBijective omitIndex omitIndex_bijective

/-- The increasing three-fold coordinate wedges, indexed by the omitted
coordinate. This is a basis of the genuine third exterior power. -/
def thirdBasis : Module.Basis (Fin 4) K (Form 3) :=
  (coordinateBasis.exteriorPower 3).reindex omitEquiv.symm

theorem thirdBasis_apply (i : Fin 4) :
    thirdBasis i = exteriorPower.ιMulti K 3 (i.removeNth coordinateDifferential) := by
  rw [thirdBasis, Module.Basis.reindex_apply, Equiv.symm_symm]
  change coordinateBasis.exteriorPower 3 (omitIndex i) = _
  rw [exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family
  congr 1
  funext j
  simp only [Function.comp_apply, coordinateBasis_apply,
    Set.powersetCard.ofFinEmbEquiv_symm_apply, omitIndex,
    Finset.orderEmbOfFin_compl_singleton_eq_succAboveOrderEmb, Fin.removeNth]
  rfl

/-- Canonical exterior multiplication of a one-form and a three-form. -/
def wedgeOneThree : Omega →ₗ[K] (Form 3 →ₗ[K] Form 4) :=
  exteriorPower.alternatingMapLinearEquiv.toLinearMap.comp
    (exteriorPower.ιMulti K 4).curryLeft

@[simp] theorem wedgeOneThree_wedge (a : Omega) (v : Fin 3 → Omega) :
    wedgeOneThree a (exteriorPower.ιMulti K 3 v) =
      exteriorPower.ιMulti K 4 (Matrix.vecCons a v) := by
  simp [wedgeOneThree]

@[simp] theorem wedgeOneThree_basis (a : Omega) (i : Fin 4) :
    wedgeOneThree a (thirdBasis i) =
      exteriorPower.ιMulti K 4 (Matrix.vecCons a (i.removeNth coordinateDifferential)) := by
  rw [thirdBasis_apply, wedgeOneThree_wedge]

def volume : Form 4 := exteriorPower.ιMulti K 4 coordinateDifferential

def topIndex : Set.powersetCard (Fin 4) 4 := ⟨Finset.univ, by simp⟩

theorem topIndex_unique (s : Set.powersetCard (Fin 4) 4) : s = topIndex := by
  apply Subtype.ext
  exact Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp [s.property])

theorem topBasis_apply : coordinateBasis.exteriorPower 4 topIndex = volume := by
  rw [exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family volume
  congr 1
  funext j
  rw [Function.comp_apply, coordinateBasis_apply]
  have ho : (fun i : Fin 4 => i) =
      (Finset.univ : Finset (Fin 4)).orderEmbOfFin (by simp) :=
    Finset.orderEmbOfFin_unique _ (fun _ => Finset.mem_univ _) strictMono_id
  exact congrArg coordinateDifferential (congrFun ho j).symm

def volumeCoefficient : Form 4 →ₗ[K] K :=
  (coordinateBasis.exteriorPower 4).coord topIndex

@[simp] theorem volumeCoefficient_volume : volumeCoefficient volume = 1 := by
  rw [← topBasis_apply]
  simp [volumeCoefficient]

theorem topForm_eq_coefficient (η : Form 4) :
    η = volumeCoefficient η • volume := by
  calc
    η = ∑ s, (coordinateBasis.exteriorPower 4).repr η s •
        coordinateBasis.exteriorPower 4 s :=
      ((coordinateBasis.exteriorPower 4).sum_repr η).symm
    _ = _ := by
      rw [Finset.sum_eq_single topIndex]
      · rw [topBasis_apply]
        rfl
      · intro i hi hne
        exact (hne (topIndex_unique i)).elim
      · simp

theorem volume_ne_zero : volume ≠ 0 := by
  intro h
  have hh := volumeCoefficient_volume
  rw [h, map_zero] at hh
  exact zero_ne_one hh

/-- The exact Koszul sign of a coordinate wedge. -/
theorem wedge_coordinate_basis (j i : Fin 4) :
    wedgeOneThree (coordinateDifferential j) (thirdBasis i) =
      (if j = i then (-1 : K) ^ i.val else 0) • volume := by
  rw [wedgeOneThree_basis]
  by_cases h : j = i
  · subst j
    rw [if_pos rfl]
    have hh := (exteriorPower.ιMulti K 4).neg_one_pow_smul_map_insertNth i
      (coordinateDifferential i) (i.removeNth coordinateDifferential)
    rw [Fin.insertNth_self_removeNth] at hh
    simpa only [volume, ← Int.cast_smul_eq_zsmul K, Int.cast_pow,
      Int.cast_neg, Int.cast_one] using hh.symm
  · rw [if_neg h, zero_smul]
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq h
    apply (exteriorPower.ιMulti K 4).map_eq_zero_of_eq (i := 0) (j := k.succ)
    · simp [Fin.removeNth, hk]
    · exact (Fin.succ_ne_zero k).symm

/-- The universal-property wedge agrees with multiplication in the actual
exterior algebra. -/
theorem wedgeOneThree_coe (a : Omega) (η : Form 3) :
    (wedgeOneThree a η : ExteriorAlgebra K Omega) =
      ExteriorAlgebra.ι K a * (η : ExteriorAlgebra K Omega) := by
  have he : (Form 4).subtype.comp (wedgeOneThree a) =
      (LinearMap.mulLeft K (ExteriorAlgebra.ι K a)).comp (Form 3).subtype := by
    apply thirdBasis.ext
    intro i
    change (wedgeOneThree a (thirdBasis i) : ExteriorAlgebra K Omega) =
      ExteriorAlgebra.ι K a * (thirdBasis i : ExteriorAlgebra K Omega)
    rw [wedgeOneThree_basis, thirdBasis_apply]
    change ExteriorAlgebra.ιMulti K 4
        (Matrix.vecCons a (i.removeNth coordinateDifferential)) =
      ExteriorAlgebra.ι K a * ExteriorAlgebra.ιMulti K 3 (i.removeNth coordinateDifferential)
    rw [ExteriorAlgebra.ιMulti_succ_apply]
    rfl
  exact LinearMap.congr_fun he η

theorem wedge_d_basis (a : K) (i : Fin 4) :
    wedgeOneThree (d a) (thirdBasis i) =
      ((-1 : K) ^ i.val * affineTangent i a) • volume := by
  rw [differential_coordinates, map_sum]
  simp only [map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    wedge_coordinate_basis, smul_smul]
  simp [mul_comm]

/-- The algebraic exterior differential in degree three, written in the
basis of exact coordinate wedges. It is complex-linear, not K-linear. -/
def exteriorD3 : Form 3 →ₗ[ℂ] Form 4 :=
  ∑ i : Fin 4,
    ((LinearMap.toSpanSingleton K (Form 4) ((-1 : K) ^ i.val • volume)).restrictScalars ℂ).comp
      ((complexTangent i).toLinearMap.comp ((thirdBasis.coord i).restrictScalars ℂ))

theorem exteriorD3_apply (η : Form 3) :
    exteriorD3 η =
      (∑ i : Fin 4, (-1 : K) ^ i.val * affineTangent i (thirdBasis.repr η i)) • volume := by
  simp only [exteriorD3, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.coe_restrictScalars, LinearMap.toSpanSingleton_apply,
    Module.Basis.coord_apply, Derivation.coeFn_coe, complexTangent_apply,
    smul_smul, ← Finset.sum_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The coordinate definition is the usual differential of a scalar times
a wedge of exact coordinate differentials. -/
theorem exteriorD3_smul_basis (a : K) (i : Fin 4) :
    exteriorD3 (a • thirdBasis i) = wedgeOneThree (d a) (thirdBasis i) := by
  rw [exteriorD3_apply, wedge_d_basis]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, hji, Ne.symm hji]
  · simp

@[simp] theorem exteriorD3_basis (i : Fin 4) : exteriorD3 (thirdBasis i) = 0 := by
  simpa only [one_smul, Derivation.map_one_eq_zero, map_zero, LinearMap.zero_apply] using
    exteriorD3_smul_basis 1 i

theorem exteriorD3_eq_sum_wedge (η : Form 3) :
    exteriorD3 η =
      ∑ i : Fin 4, wedgeOneThree (d (thirdBasis.repr η i)) (thirdBasis i) := by
  rw [exteriorD3_apply]
  simp only [wedge_d_basis, Finset.sum_smul]

/-- The actual scalar Leibniz rule for this exterior differential. -/
theorem exteriorD3_leibniz (a : K) (η : Form 3) :
    exteriorD3 (a • η) = wedgeOneThree (d a) η + a • exteriorD3 η := by
  have hh := congrArg (wedgeOneThree (d a)) (thirdBasis.sum_repr η)
  simp only [map_sum, map_smul] at hh
  rw [exteriorD3_eq_sum_wedge]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, Derivation.leibniz,
    map_add, LinearMap.add_apply, LinearMap.smul_apply, Finset.sum_add_distrib]
  rw [← Finset.smul_sum, ← exteriorD3_eq_sum_wedge, hh]
  exact add_comm _ _

/-- The scalar-times-generator formula uniquely determines the exterior
differential on the genuine third exterior power. -/
theorem exteriorD3_unique (δ : Form 3 →ₗ[ℂ] Form 4)
    (hδ : ∀ (a : K) (i : Fin 4),
      δ (a • thirdBasis i) = wedgeOneThree (d a) (thirdBasis i)) :
    δ = exteriorD3 := by
  apply LinearMap.ext
  intro η
  calc
    δ η = δ (∑ i, thirdBasis.repr η i • thirdBasis i) :=
      congrArg δ (thirdBasis.sum_repr η).symm
    _ = ∑ i, wedgeOneThree (d (thirdBasis.repr η i)) (thirdBasis i) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact hδ _ i
    _ = exteriorD3 η := (exteriorD3_eq_sum_wedge η).symm

end CycleQ2AffineExterior

#print axioms CycleQ2AffineExterior.thirdBasis_apply
#print axioms CycleQ2AffineExterior.topForm_eq_coefficient
#print axioms CycleQ2AffineExterior.wedge_coordinate_basis
#print axioms CycleQ2AffineExterior.exteriorD3_smul_basis
#print axioms CycleQ2AffineExterior.exteriorD3_leibniz
#print axioms CycleQ2AffineExterior.exteriorD3_unique
end
end


/- Component: continuation_2/AffineExactnessCriterion.lean -/
section
/-!
# Actual top-form exactness is equivalent to the protected residue PDE

Write g for the nonzero normal derivative and c for the actual second normal
source. The residue source is the genuine top exterior form (c/g) dx1∧⋯∧dx4.
The three-form with coefficients (-1)^i w_i/g has derivative
(residueDivergence w/g) dx1∧⋯∧dx4. Thus a solved PDE c+div_g(w)=0 makes its
negative a primitive of the positive source form. No exactness is assumed
without appearing explicitly as a hypothesis in the final implication.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace CycleQ2AffineExactness

open MvPolynomial HodgeComputer CycleQ2AffineDifferentials CycleQ2AffineExterior
open CycleQ2AffineHypersurface CycleQ2AffineClearing CycleQ2AffineResidueClosure
open HoldoutConstruction
open scoped BigOperators

local instance intAlgebra : Algebra ℤ K := Ring.toIntAlgebra _

def normalDensity : K := affineMap (pderiv 0 affineF)

theorem normalDensity_ne_zero : normalDensity ≠ 0 := normal_ne_zero

def coordinateSign (i : Fin 4) : K := (-1 : K) ^ i.val

theorem coordinateSign_mul_self (i : Fin 4) :
    coordinateSign i * coordinateSign i = 1 := by
  unfold coordinateSign
  rw [← pow_add, show i.val + i.val = 2 * i.val by omega, pow_mul]
  simp

@[simp] theorem tangent_coordinateSign (j i : Fin 4) :
    affineTangent j (coordinateSign i) = 0 := by
  simp only [coordinateSign, Derivation.leibniz_pow, map_neg,
    Derivation.map_one_eq_zero, neg_zero, smul_zero]

def signedCoefficients (η : Form 3) (i : Fin 4) : K :=
  coordinateSign i * thirdBasis.repr η i

def densityVector (η : Form 3) (i : Fin 4) : K :=
  normalDensity * signedCoefficients η i

theorem exteriorD3_as_divergence (η : Form 3) :
    exteriorD3 η = fieldDivergence affineTangent (signedCoefficients η) • volume := by
  rw [exteriorD3_apply]
  congr 1
  unfold fieldDivergence signedCoefficients
  apply Finset.sum_congr rfl
  intro i hi
  rw [Derivation.leibniz, tangent_coordinateSign]
  simp only [smul_eq_mul, mul_zero, add_zero, coordinateSign]

theorem densityVector_residueDivergence (η : Form 3) :
    residueDivergence affineTangent normalDensity (densityVector η) =
      normalDensity * fieldDivergence affineTangent (signedCoefficients η) :=
  residueDivergence_cancel_density affineTangent normalDensity normalDensity_ne_zero _

theorem volumeCoefficient_exteriorD3 (η : Form 3) :
    volumeCoefficient (exteriorD3 η) = fieldDivergence affineTangent (signedCoefficients η) := by
  rw [exteriorD3_as_divergence, map_smul, volumeCoefficient_volume, smul_eq_mul, mul_one]

/-- The actual source top-form, with the positive residue sign. -/
def residueSourceForm (A : AmbientPoly 4) : Form 4 :=
  (affineNormalSource A / normalDensity) • volume

@[simp] theorem volumeCoefficient_residueSourceForm (A : AmbientPoly 4) :
    volumeCoefficient (residueSourceForm A) = affineNormalSource A / normalDensity := by
  simp [residueSourceForm]

/-- The explicit three-form whose coordinate coefficients are (-1)^i w_i/g. -/
def residuePrimitiveForm (w : Fin 4 → K) : Form 3 :=
  thirdBasis.equivFun.symm (fun i => coordinateSign i * (w i / normalDensity))

@[simp] theorem residuePrimitiveForm_repr (w : Fin 4 → K) (i : Fin 4) :
    thirdBasis.repr (residuePrimitiveForm w) i =
      coordinateSign i * (w i / normalDensity) := by
  change thirdBasis.coord i (thirdBasis.equivFun.symm _) = _
  exact Module.Basis.coord_equivFun_symm thirdBasis i _

theorem densityVector_residuePrimitiveForm (w : Fin 4 → K) :
    densityVector (residuePrimitiveForm w) = w := by
  funext i
  simp only [densityVector, signedCoefficients, residuePrimitiveForm_repr]
  rw [← mul_assoc (coordinateSign i), coordinateSign_mul_self, one_mul]
  field_simp [normalDensity_ne_zero]

theorem residuePrimitiveForm_densityVector (η : Form 3) :
    residuePrimitiveForm (densityVector η) = η := by
  apply thirdBasis.repr.injective
  ext i
  rw [residuePrimitiveForm_repr]
  simp only [densityVector, signedCoefficients]
  rw [mul_div_cancel_left₀ _ normalDensity_ne_zero,
    ← mul_assoc, coordinateSign_mul_self, one_mul]

/-- Exact identity between the genuine exterior derivative and the existing
weighted residue divergence. -/
theorem exteriorD3_residuePrimitiveForm (w : Fin 4 → K) :
    exteriorD3 (residuePrimitiveForm w) =
      (residueDivergence affineTangent normalDensity w / normalDensity) • volume := by
  have hd := densityVector_residueDivergence (residuePrimitiveForm w)
  rw [densityVector_residuePrimitiveForm] at hd
  rw [exteriorD3_as_divergence]
  congr 1
  apply (eq_div_iff normalDensity_ne_zero).mpr
  simpa only [mul_comm] using hd.symm

theorem affineResidueExpression_densityVector (A : AmbientPoly 4) (η : Form 3) :
    affineResidueExpression A (densityVector η) =
      affineNormalSource A + normalDensity * volumeCoefficient (exteriorD3 η) := by
  change affineNormalSource A +
    residueDivergence affineTangent normalDensity (densityVector η) = _
  rw [densityVector_residueDivergence, volumeCoefficient_exteriorD3]

/-- The sign convention is explicit: a zero residue PDE gives the negative
of the positive source form as the derivative of `residuePrimitiveForm w`. -/
theorem exteriorD3_residuePrimitiveForm_add_source (A : AmbientPoly 4) (w : Fin 4 → K) :
    exteriorD3 (residuePrimitiveForm w) + residueSourceForm A =
      (affineResidueExpression A w / normalDensity) • volume := by
  rw [exteriorD3_residuePrimitiveForm, residueSourceForm, ← add_smul]
  change (residueDivergence affineTangent normalDensity w / normalDensity +
    affineNormalSource A / normalDensity) • volume =
      ((affineNormalSource A + residueDivergence affineTangent normalDensity w) /
        normalDensity) • volume
  congr 1
  ring

/-- Genuine exactness of the actual top exterior source is equivalent to
the already defined concrete residue PDE. Neither side is asserted here. -/
theorem exact_residueSourceForm_iff (A : AmbientPoly 4) :
    (∃ η : Form 3, exteriorD3 η = residueSourceForm A) ↔
      ∃ w : Fin 4 → K, affineResidueExpression A w = 0 := by
  constructor
  · rintro ⟨η, hη⟩
    refine ⟨densityVector (-η), ?_⟩
    rw [affineResidueExpression_densityVector, map_neg, hη, map_neg,
      volumeCoefficient_residueSourceForm]
    field_simp [normalDensity_ne_zero]
    ring
  · rintro ⟨w, hw⟩
    have hh := exteriorD3_residuePrimitiveForm_add_source A w
    rw [hw, zero_div, zero_smul] at hh
    refine ⟨-residuePrimitiveForm w, ?_⟩
    rw [map_neg, eq_neg_of_add_eq_zero_left hh, neg_neg]

/-- Actual exterior-form exactness now implies the unchanged protected
certificate through the proved residue, chart, and denominator constructions. -/
theorem protected_certificate_of_exact_residueSourceForm
    (h : ∃ η : Form 3, exteriorD3 η = residueSourceForm affineA) :
    HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A :=
  protected_certificate_of_affine_residue_primitive ((exact_residueSourceForm_iff affineA).mp h)

end CycleQ2AffineExactness

#print axioms CycleQ2AffineExactness.exteriorD3_residuePrimitiveForm_add_source
#print axioms CycleQ2AffineExactness.exact_residueSourceForm_iff
#print axioms CycleQ2AffineExactness.protected_certificate_of_exact_residueSourceForm
end
end


/- Component: continuation_2/VeryGeneralPoint.lean -/
section
/-!
Actual very-general-point selection in affine coefficient spaces.

The countable-proper-image specialization argument requires a complex point
outside countably many proper algebraic conditions. This module proves that
selection statement for genuine polynomial equations. It does not assert
that any moving cycle, supported projector, or primitive exists.
-/

set_option autoImplicit false
noncomputable section

namespace CycleQ2VeryGeneral

open MvPolynomial

variable {K : Type*} [Field K] [Uncountable K]

theorem exists_avoiding_univariate {ι : Type*} [Countable ι]
    (p : ι → Polynomial K) (hp : ∀ i, p i ≠ 0) :
    ∃ x : K, ∀ i, (p i).eval x ≠ 0 := by
  classical
  let roots : ι → Set K := fun i => {x | (p i).eval x = 0}
  have hroots (i : ι) : (roots i).Finite := by
    simpa only [roots, Polynomial.IsRoot] using
      (Polynomial.finite_setOfPred_isRoot (hp i))
  have hcount : (⋃ i, roots i).Countable :=
    Set.countable_iUnion (fun i => (hroots i).countable)
  have hout : ∃ x : K, x ∉ ⋃ i, roots i := by
    by_contra h
    push Not at h
    have heq : (⋃ i, roots i) = Set.univ := Set.eq_univ_of_forall h
    exact Set.not_countable_univ (heq ▸ hcount)
  obtain ⟨x, hx⟩ := hout
  refine ⟨x, fun i hi => hx ?_⟩
  exact Set.mem_iUnion.mpr ⟨i, hi⟩

/-- Countably many genuine nonzero multivariate polynomials have a common
nonvanishing point over an uncountable field. -/
theorem exists_avoiding_polynomials (n : ℕ) {ι : Type*} [Countable ι]
    (p : ι → MvPolynomial (Fin n) K) (hp : ∀ i, p i ≠ 0) :
    ∃ x : Fin n → K, ∀ i, eval x (p i) ≠ 0 := by
  classical
  induction n with
  | zero =>
      refine ⟨Fin.elim0, ?_⟩
      intro i hi
      obtain ⟨c, hc⟩ := (isEmptyAlgEquiv K (Fin 0)).symm.surjective (p i)
      have hpi : p i = C c := by simpa using hc.symm
      rw [hpi, eval_C] at hi
      exact hp i (by simp [hpi, hi])
  | succ n ih =>
      let q : ι → Polynomial (MvPolynomial (Fin n) K) :=
        fun i => finSuccEquiv K n (p i)
      have hq (i : ι) : q i ≠ 0 := by
        intro hz
        apply hp i
        apply (finSuccEquiv K n).injective
        simpa only [q, map_zero] using hz
      have hlc (i : ι) : (q i).leadingCoeff ≠ 0 := by
        simpa only [ne_eq, Polynomial.leadingCoeff_eq_zero] using hq i
      obtain ⟨y, hy⟩ := ih (fun i => (q i).leadingCoeff) hlc
      let s : ι → Polynomial K := fun i => (q i).map (eval y)
      have hs (i : ι) : s i ≠ 0 := by
        intro hz
        have hc := congrArg (fun z : Polynomial K => z.coeff (q i).natDegree) hz
        simp only [s, Polynomial.coeff_map, Polynomial.coeff_zero] at hc
        exact hy i hc
      obtain ⟨x, hx⟩ := exists_avoiding_univariate s hs
      refine ⟨Fin.cons x y, ?_⟩
      intro i
      simpa only [eval_eq_eval_mv_eval', q, s] using hx i

/-- A very general complex coefficient point can also be required to lie in
any prescribed nonempty principal open, without a coefficient bound. -/
theorem complex_point_in_principal_open_avoiding (n : ℕ)
    {ι : Type*} [Countable ι] (g : MvPolynomial (Fin n) ℂ) (hg : g ≠ 0)
    (p : ι → MvPolynomial (Fin n) ℂ) (hp : ∀ i, p i ≠ 0) :
    ∃ x : Fin n → ℂ, eval x g ≠ 0 ∧ ∀ i, eval x (p i) ≠ 0 := by
  letI : Uncountable ℂ := Set.not_countable_univ_iff.mp not_countable_complex
  let family : Option ι → MvPolynomial (Fin n) ℂ := fun i => Option.elim i g p
  have hn (i : Option ι) : family i ≠ 0 := by
    cases i with
    | none => exact hg
    | some i => exact hp i
  obtain ⟨x, hx⟩ := exists_avoiding_polynomials n family hn
  exact ⟨x, hx none, fun i => hx (some i)⟩

/-- A countable family of genuine affine algebraic zero loci covering a
nonempty principal open has a member equal to the whole affine space.
This is the countability step in proper-image specialization, without any
assumed existence of projectors or cycle families. -/
theorem complex_countable_algebraic_cover (n : ℕ)
    {ι : Type*} [Countable ι]
    (I : ι → Ideal (MvPolynomial (Fin n) ℂ))
    (g : MvPolynomial (Fin n) ℂ) (hg : g ≠ 0)
    (hcover : ∀ x : Fin n → ℂ, eval x g ≠ 0 →
      ∃ i, x ∈ zeroLocus ℂ (I i)) :
    ∃ i, zeroLocus ℂ (I i) = Set.univ := by
  classical
  by_contra h
  push Not at h
  have hn (i : ι) : I i ≠ ⊥ := by
    intro hi
    apply h i
    simp only [hi, zeroLocus_bot, Set.top_eq_univ]
  have hp (i : ι) : ∃ p : MvPolynomial (Fin n) ℂ, p ∈ I i ∧ p ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hn i
    apply le_antisymm
    · intro p hp
      exact (Ideal.mem_bot).mpr (hh p hp)
    · exact bot_le
  choose p hpI hpne using hp
  obtain ⟨x, hxg, hxp⟩ := complex_point_in_principal_open_avoiding n g hg p hpne
  obtain ⟨i, hxi⟩ := hcover x hxg
  apply hxp i
  exact hxi (p i) (hpI i)

end CycleQ2VeryGeneral

#print axioms CycleQ2VeryGeneral.exists_avoiding_polynomials
#print axioms CycleQ2VeryGeneral.complex_point_in_principal_open_avoiding
#print axioms CycleQ2VeryGeneral.complex_countable_algebraic_cover
end
end


/- Component: continuation_2/AffineFormalSpecialization.lean -/
section
/-!
An actual formal neighborhood of the protected affine hypersurface.

The normal derivative is already proved nonzero in its function field. Hensel's
lemma therefore solves the exact one-parameter deformation in that function
field's power series ring. This is a specialization tool: it does not turn a
formal primitive at the Fermat member into a rational primitive of the family.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace CycleQ2FormalSpecialization

open scoped PowerSeries

/-- Hensel lifting written with the actual constant-coefficient specialization.
No algebraicity or rationality of the resulting power series is inferred. -/
theorem simple_root_lifts {k : Type*} [Field k]
    (p : Polynomial (PowerSeries k)) (hp : p.Monic) (a : k)
    (ha : p.eval₂ (PowerSeries.constantCoeff (R := k)) a = 0)
    (hderiv : p.derivative.eval₂ (PowerSeries.constantCoeff (R := k)) a ≠ 0) :
    ∃ z : PowerSeries k, p.eval z = 0 ∧ z.constantCoeff = a := by
  let I : Ideal (PowerSeries k) := Ideal.span {PowerSeries.X}
  have hmem : p.eval (PowerSeries.C a) ∈ I := by
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    simpa only [← Polynomial.eval₂_at_apply, PowerSeries.constantCoeff_C] using ha
  have hu : IsUnit (p.derivative.eval (PowerSeries.C a)) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    apply isUnit_iff_ne_zero.mpr
    simpa only [← Polynomial.eval₂_at_apply, PowerSeries.constantCoeff_C] using hderiv
  obtain ⟨z, hz, hza⟩ := HenselianRing.is_henselian p hp (PowerSeries.C a)
    hmem (hu.map (Ideal.Quotient.mk I))
  refine ⟨z, hz, ?_⟩
  rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff] at hza
  simpa only [map_sub, PowerSeries.constantCoeff_C, sub_eq_zero] using hza

open MvPolynomial CycleQ2AffineClearing CycleQ2AffineGeometry
  CycleQ2AffineHypersurface

abbrev K := AffineFunctionField

def fieldCoordinate (i : Fin 5) : K := affineMap (MvPolynomial.X i)

/-- The family parameter is zero at the protected target and minus one at
the Fermat polynomial. The eliminated coordinate is the polynomial variable;
the other four coordinates are constants in the actual function field. -/
def targetFamily : Polynomial (PowerSeries K) :=
  Polynomial.X ^ 6 +
    Polynomial.C (PowerSeries.C (1 + fieldCoordinate 1 ^ 6 +
      fieldCoordinate 2 ^ 6 + fieldCoordinate 3 ^ 6 + fieldCoordinate 4 ^ 6)) +
    Polynomial.C (PowerSeries.C (1 / 2 : K) * (1 + PowerSeries.X)) *
      (Polynomial.X * Polynomial.C (PowerSeries.C (fieldCoordinate 2 * fieldCoordinate 3)) +
        Polynomial.X ^ 3 * Polynomial.C (PowerSeries.C
          (fieldCoordinate 1 * fieldCoordinate 3 * fieldCoordinate 4)) +
        Polynomial.C (PowerSeries.C
          (fieldCoordinate 1 ^ 3 * fieldCoordinate 4 * fieldCoordinate 2)))

theorem targetFamily_monic : targetFamily.Monic := by
  unfold targetFamily
  rw [add_assoc]
  apply Polynomial.monic_X_pow_add
  compute_degree!

theorem targetFamily_specializes :
    targetFamily.eval₂ (PowerSeries.constantCoeff (R := K)) (fieldCoordinate 0) = 0 := by
  have hc (c : ℂ) : affineMap (MvPolynomial.C c) = algebraMap ℂ K c := rfl
  have h := congrArg affineMap affineF_formula
  simp only [affineMap_F, map_add, map_mul, map_pow, map_one, hc] at h
  norm_num only [map_div₀, map_one, map_ofNat] at h
  convert h.symm using 1 <;> norm_num only [targetFamily, fieldCoordinate,
    Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_one, map_add, map_mul,
    map_one, map_zero, map_pow, map_ofNat, PowerSeries.constantCoeff_C,
    PowerSeries.constantCoeff_X] <;> ring

theorem targetFamily_simple :
    targetFamily.derivative.eval₂ (PowerSeries.constantCoeff (R := K))
      (fieldCoordinate 0) ≠ 0 := by
  have hc (c : ℂ) : affineMap (MvPolynomial.C c) = algebraMap ℂ K c := rfl
  have h := congrArg (fun P => affineMap (MvPolynomial.pderiv 0 P)) affineF_formula
  norm_num [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_X, Pi.single_apply, Fin.ext_iff, hc] at h
  have hn := normal_ne_zero
  rw [h] at hn
  convert hn using 1 <;>
    norm_num [targetFamily, fieldCoordinate, Polynomial.derivative_add,
      Polynomial.derivative_mul, Polynomial.derivative_pow,
      Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C] <;> simp only [map_ofNat] <;> ring

/-- The protected hypersurface has a genuine formal solution along the
specified deformation, with its original coordinate as constant coefficient. -/
theorem exists_target_formal_coordinate :
    ∃ z : PowerSeries K, targetFamily.eval z = 0 ∧
      z.constantCoeff = fieldCoordinate 0 :=
  simple_root_lifts targetFamily targetFamily_monic (fieldCoordinate 0)
    targetFamily_specializes targetFamily_simple

end CycleQ2FormalSpecialization

#print axioms CycleQ2FormalSpecialization.simple_root_lifts
#print axioms CycleQ2FormalSpecialization.exists_target_formal_coordinate
end
end


/- Component: continuation_2/LaurentCoefficientDerivations.lean -/
section
/-!
Coefficientwise derivations and exactness under formal Laurent extension.

The exponent is a deformation parameter, not a coordinate to differentiate.
The actual Hahn-series multiplication is used in the Leibniz proof. Taking
any Laurent coefficient commutes with these derivations, including for
series with negative powers. Consequently a Laurent primitive specializes
coefficientwise; no converse from formal deformation to a rational primitive
of a generic algebraic family is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace CycleQ2LaurentDerivation

open scoped BigOperators

variable {C K : Type*} [CommRing C] [CommRing K] [Algebra C K]

abbrev Series := HahnSeries ℤ K

/-- Use the coefficient algebra explicitly. The power-series imports also
provide a compatible algebra through the power-series embedding; fixing
this instance keeps the scalar action definitionally coefficientwise. -/
local instance coefficientAlgebra : Algebra C (Series (K := K)) :=
  HahnSeries.instAlgebra

def coefficientwise (D : Derivation C K K) (s : Series (K := K)) : Series (K := K) where
  coeff n := D (s.coeff n)
  isPWO_support' := s.isPWO_support.mono (by
    intro n hn hzero
    exact hn (by simp only [hzero, map_zero]))

@[simp] theorem coefficientwise_coeff (D : Derivation C K K) (s : Series (K := K)) (n : ℤ) :
    (coefficientwise D s).coeff n = D (s.coeff n) := rfl

theorem support_coefficientwise_subset (D : Derivation C K K) (s : Series (K := K)) :
    (coefficientwise D s).support ⊆ s.support := by
  intro n hn hzero
  exact hn (by simp only [coefficientwise_coeff, hzero, map_zero])

theorem coefficientwise_mul (D : Derivation C K K) (s t : Series (K := K)) :
    coefficientwise D (s * t) = s * coefficientwise D t + t * coefficientwise D s := by
  ext n
  rw [coefficientwise_coeff, HahnSeries.coeff_mul, map_sum, HahnSeries.coeff_add,
    HahnSeries.coeff_mul_right' t.isPWO_support (support_coefficientwise_subset D t),
    mul_comm t (coefficientwise D s),
    HahnSeries.coeff_mul_left' s.isPWO_support (support_coefficientwise_subset D s)]
  simp only [Derivation.leibniz, smul_eq_mul, coefficientwise_coeff, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro ij hij
  exact mul_comm _ _

/-- An actual derivation of the Laurent-series ring, obtained by applying the
coefficient derivation while keeping the formal parameter constant. -/
def extend (D : Derivation C K K) : Derivation C (Series (K := K)) (Series (K := K)) where
  toFun := coefficientwise D
  map_add' s t := by
    ext n
    simp
  map_smul' c s := by
    ext n
    simp only [coefficientwise_coeff, HahnSeries.coeff_smul,
      RingHom.id_apply, Derivation.map_smul]
  map_one_eq_zero' := by
    ext n
    by_cases hn : n = 0 <;> simp [HahnSeries.coeff_one, hn]
  leibniz' s t := by
    change coefficientwise D (s * t) = s * coefficientwise D t + t * coefficientwise D s
    exact coefficientwise_mul D s t

@[simp] theorem extend_coeff (D : Derivation C K K) (s : Series (K := K)) (n : ℤ) :
    (extend D s).coeff n = D (s.coeff n) := rfl

theorem extend_commute (D E : Derivation C K K) (h : Function.Commute D E) :
    Function.Commute (extend D) (extend E) := by
  intro s
  ext n
  exact h (s.coeff n)

@[simp] theorem extend_single (D : Derivation C K K) (n : ℤ) (a : K) :
    extend D (HahnSeries.single n a) = HahnSeries.single n (D a) := by
  ext j
  by_cases hj : j = n <;> simp [hj]

/-- Coefficient extraction is a left inverse on exactness, even when a
primitive has a pole in the deformation parameter. -/
theorem divergence_coefficient {ι : Type*} [Fintype ι]
    (D : ι → Derivation C K K) (v : ι → Series (K := K)) (b : Series (K := K))
    (h : (∑ i, extend (D i) (v i)) = b) (n : ℤ) :
    (∑ i, D i ((v i).coeff n)) = b.coeff n := by
  have hc := congrArg (fun s : Series (K := K) => s.coeff n) h
  simpa only [HahnSeries.coeff_sum, extend_coeff] using hc

/-- Extending the coefficient field to formal Laurent series cannot make a
constant source exact unless it was already exact over the original ring. -/
theorem exists_divergence_constant_iff {ι : Type*} [Fintype ι]
    (D : ι → Derivation C K K) (b : K) :
    (∃ v : ι → Series (K := K), ∑ i, extend (D i) (v i) = HahnSeries.single 0 b) ↔
      ∃ v : ι → K, ∑ i, D i (v i) = b := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨fun i => (v i).coeff 0, ?_⟩
    simpa using divergence_coefficient D v _ hv 0
  · rintro ⟨v, hv⟩
    refine ⟨fun i => HahnSeries.single 0 (v i), ?_⟩
    simp_rw [extend_single]
    change (∑ i, HahnSeries.single.addMonoidHom 0 (D i (v i))) =
      HahnSeries.single.addMonoidHom 0 b
    rw [← map_sum (HahnSeries.single.addMonoidHom 0), hv]

end CycleQ2LaurentDerivation

#print axioms CycleQ2LaurentDerivation.extend
#print axioms CycleQ2LaurentDerivation.divergence_coefficient
#print axioms CycleQ2LaurentDerivation.exists_divergence_constant_iff
end
end


/- Component: continuation_2/AffineNormalExpansion.lean -/
section
/-!
The actual normal formal coordinate at the generic point of f=0.

We solve f(x0(T),x1,...,x4)=T in K[[T]], prove that its constant-coefficient
map is the actual residue map on polynomials, and prove injectivity of the
resulting polynomial substitution. The formal derivative satisfies the
actual normal chain rule. These are local algebraic facts, independent of
any assertion that the target residue is exact.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace CycleQ2NormalExpansion

open MvPolynomial HodgeComputer CycleQ2AffineClearing CycleQ2AffineGeometry
  CycleQ2AffineHypersurface CycleQ2FormalSpecialization

abbrev K := AffineFunctionField
abbrev S := PowerSeries K

def normalEquation : Polynomial S :=
  Polynomial.X ^ 6 +
    (Polynomial.C (PowerSeries.C (1 + fieldCoordinate 1 ^ 6 +
      fieldCoordinate 2 ^ 6 + fieldCoordinate 3 ^ 6 + fieldCoordinate 4 ^ 6)) +
      Polynomial.C (PowerSeries.C (1 / 2 : K)) *
        (Polynomial.X * Polynomial.C (PowerSeries.C (fieldCoordinate 2 * fieldCoordinate 3)) +
          Polynomial.X ^ 3 * Polynomial.C (PowerSeries.C
            (fieldCoordinate 1 * fieldCoordinate 3 * fieldCoordinate 4)) +
          Polynomial.C (PowerSeries.C
            (fieldCoordinate 1 ^ 3 * fieldCoordinate 4 * fieldCoordinate 2))) -
      Polynomial.C PowerSeries.X)

theorem normalEquation_monic : normalEquation.Monic := by
  unfold normalEquation
  apply Polynomial.monic_X_pow_add
  compute_degree!

theorem normalEquation_specializes :
    normalEquation.eval₂ (PowerSeries.constantCoeff (R := K)) (fieldCoordinate 0) = 0 := by
  convert targetFamily_specializes using 1 <;>
    simp [normalEquation, targetFamily] <;> ring

theorem normalEquation_simple :
    normalEquation.derivative.eval₂ (PowerSeries.constantCoeff (R := K))
      (fieldCoordinate 0) ≠ 0 := by
  convert targetFamily_simple using 1 <;>
    simp [normalEquation, targetFamily, Polynomial.derivative_pow]

theorem normal_root_exists :
    ∃ z : S, normalEquation.eval z = 0 ∧ z.constantCoeff = fieldCoordinate 0 :=
  simple_root_lifts normalEquation normalEquation_monic (fieldCoordinate 0)
    normalEquation_specializes normalEquation_simple

def normalRoot : S := Classical.choose normal_root_exists

theorem normalRoot_equation : normalEquation.eval normalRoot = 0 :=
  (Classical.choose_spec normal_root_exists).1

@[simp] theorem normalRoot_constantCoeff :
    normalRoot.constantCoeff = fieldCoordinate 0 :=
  (Classical.choose_spec normal_root_exists).2

def normalCoordinates : Fin 5 → S :=
  Fin.cases normalRoot (fun j => PowerSeries.C (fieldCoordinate j.succ))

def normalExpansion : AmbientPoly 4 →+* S :=
  MvPolynomial.eval₂Hom (PowerSeries.C.comp (affineMap.comp MvPolynomial.C)) normalCoordinates

@[simp] theorem normalExpansion_C (c : ℂ) :
    normalExpansion (MvPolynomial.C c) = PowerSeries.C (affineMap (MvPolynomial.C c)) := by
  simp [normalExpansion]

@[simp] theorem normalExpansion_X_zero :
    normalExpansion (MvPolynomial.X (0 : Fin 5)) = normalRoot := by
  simp [normalExpansion, normalCoordinates]

@[simp] theorem normalExpansion_X_succ (j : Fin 4) :
    normalExpansion (MvPolynomial.X j.succ) = PowerSeries.C (fieldCoordinate j.succ) := by
  simp [normalExpansion, normalCoordinates]

/-- The constant coefficient is exactly the previously constructed quotient
map into the protected hypersurface function field, on every polynomial. -/
theorem constantCoeff_normalExpansion (P : AmbientPoly 4) :
    (normalExpansion P).constantCoeff = affineMap P := by
  have h : (PowerSeries.constantCoeff (R := K)).comp normalExpansion = affineMap := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [fieldCoordinate]
      · simp [fieldCoordinate]
  exact RingHom.congr_fun h P

/-- The normal parameter is the actual protected equation f. -/
theorem normalExpansion_F : normalExpansion affineF = PowerSeries.X := by
  have hf := congrArg normalExpansion affineF_formula
  have hr := normalRoot_equation
  have hc : normalExpansion (MvPolynomial.C (1 / 2 : ℂ)) =
      PowerSeries.C (1 / 2 : K) := by
    rw [normalExpansion_C]
    congr 1
    change (affineMap.comp MvPolynomial.C) (1 / 2 : ℂ) = _
    rw [map_div₀, map_one, map_ofNat]
  norm_num [normalEquation, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hr
  simp only [map_add, map_mul, map_pow, map_one, hc] at hf
  have h1 : normalExpansion (MvPolynomial.X (1 : Fin 5)) =
      PowerSeries.C (fieldCoordinate 1) := normalExpansion_X_succ 0
  have h2 : normalExpansion (MvPolynomial.X (2 : Fin 5)) =
      PowerSeries.C (fieldCoordinate 2) := normalExpansion_X_succ 1
  have h3 : normalExpansion (MvPolynomial.X (3 : Fin 5)) =
      PowerSeries.C (fieldCoordinate 3) := normalExpansion_X_succ 2
  have h4 : normalExpansion (MvPolynomial.X (4 : Fin 5)) =
      PowerSeries.C (fieldCoordinate 4) := normalExpansion_X_succ 3
  rw [hf]
  simp only [normalExpansion_X_zero, h1, h2, h3, h4]
  change 1 + normalRoot ^ 6 + PowerSeries.C (fieldCoordinate 1) ^ 6 +
    PowerSeries.C (fieldCoordinate 2) ^ 6 + PowerSeries.C (fieldCoordinate 3) ^ 6 +
    PowerSeries.C (fieldCoordinate 4) ^ 6 +
      PowerSeries.C (1 / 2 : K) *
        (normalRoot * PowerSeries.C (fieldCoordinate 2) * PowerSeries.C (fieldCoordinate 3) +
          normalRoot ^ 3 * PowerSeries.C (fieldCoordinate 1) *
            PowerSeries.C (fieldCoordinate 3) * PowerSeries.C (fieldCoordinate 4) +
          PowerSeries.C (fieldCoordinate 1) ^ 3 * PowerSeries.C (fieldCoordinate 4) *
            PowerSeries.C (fieldCoordinate 2)) = _
  simp only [one_div]
  linear_combination hr

theorem normalExpansion_injective : Function.Injective normalExpansion := by
  have hnonzero (P : AmbientPoly 4) (hP : P ≠ 0) : normalExpansion P ≠ 0 := by
    obtain ⟨m, U, hFU, hfactor⟩ := WfDvdMonoid.max_power_factor hP affineF_irreducible
    have hU : normalExpansion U ≠ 0 := by
      intro h
      have hc := congrArg (PowerSeries.constantCoeff (R := K)) h
      rw [constantCoeff_normalExpansion, map_zero] at hc
      exact hFU ((affineMap_kernel U).mp hc)
    rw [hfactor, map_mul, map_pow, normalExpansion_F]
    exact mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) hU
  intro P Q h
  by_contra hn
  exact hnonzero (P - Q) (sub_ne_zero.mpr hn) (by rw [map_sub, h, sub_self])

abbrev Dt : Derivation K S S := PowerSeries.derivative K

def normalVelocity : S := Dt normalRoot

/-- Chain rule for every polynomial under the actual formal normal chart. -/
theorem normalExpansion_chain_rule (P : AmbientPoly 4) :
    Dt (normalExpansion P) = normalExpansion (pderiv 0 P) * normalVelocity := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [Dt]
  | add P Q ihP ihQ =>
      simp only [map_add, ihP, ihQ, add_mul]
  | mul_X P i ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [map_mul, Derivation.leibniz, normalExpansion_X_zero, ih,
          normalVelocity, pderiv_mul, pderiv_X_self, mul_one, map_add,
          smul_eq_mul]
        ring
      · simp only [map_mul, Derivation.leibniz, normalExpansion_X_succ, ih,
          pderiv_mul, pderiv_X, Pi.single_apply, Fin.succ_ne_zero,
          if_false, mul_zero, add_zero, map_add, map_zero, smul_eq_mul,
          PowerSeries.derivative_C, mul_zero, zero_add]
        ring

theorem normal_velocity_identity :
    normalExpansion (pderiv 0 affineF) * normalVelocity = 1 := by
  have h := normalExpansion_chain_rule affineF
  rw [normalExpansion_F, PowerSeries.derivative_X] at h
  exact h.symm

end CycleQ2NormalExpansion

#print axioms CycleQ2NormalExpansion.normalExpansion_F
#print axioms CycleQ2NormalExpansion.normalExpansion_injective
#print axioms CycleQ2NormalExpansion.normalExpansion_chain_rule
#print axioms CycleQ2NormalExpansion.normal_velocity_identity
end
end


/- Component: continuation_2/AffineFormalResidue.lean -/
section
/-!
The actual pole-three residue coefficient in a genuine formal normal chart.

The normal chart sends f to T and holds the four other coordinates fixed.
Its Jacobian in the normal direction is dx0/dT. We prove that the T^(-1)
coefficient of A(x(T)) (dx0/dT) / T^3 is precisely the previously defined
normal source divided by g. This supplies the local residue calculation;
it does not assert geometric support or global de Rham vanishing.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section

namespace CycleQ2FormalResidue

open MvPolynomial HodgeComputer CycleQ2AffineClearing CycleQ2AffineHypersurface
  CycleQ2AffineResidueClosure CycleQ2NormalExpansion HoldoutConstruction
open SplitHigherResidue

abbrev K := AffineFunctionField
abbrev S := PowerSeries K

local instance coefficientCharZero : CharZero K :=
  charZero_of_injective_algebraMap (algebraMap ℂ K).injective

def normalG : K := affineMap (pderiv 0 affineF)
def normalG1 : K := affineMap (pderiv 0 (pderiv 0 affineF))
def normalG2 : K := affineMap (pderiv 0 (pderiv 0 (pderiv 0 affineF)))

theorem normalG_ne_zero : normalG ≠ 0 := normal_ne_zero

theorem velocity_first_identity :
    normalExpansion (pderiv 0 (pderiv 0 affineF)) * normalVelocity ^ 2 +
      normalExpansion (pderiv 0 affineF) * Dt normalVelocity = 0 := by
  have h := congrArg Dt normal_velocity_identity
  simp only [Derivation.leibniz, normalExpansion_chain_rule,
    smul_eq_mul, Derivation.map_one_eq_zero] at h
  linear_combination h

theorem velocity_second_identity :
    normalExpansion (pderiv 0 (pderiv 0 (pderiv 0 affineF))) * normalVelocity ^ 3 +
      3 * normalExpansion (pderiv 0 (pderiv 0 affineF)) * normalVelocity * Dt normalVelocity +
      normalExpansion (pderiv 0 affineF) * Dt (Dt normalVelocity) = 0 := by
  have h := congrArg Dt velocity_first_identity
  simp only [map_add, Derivation.leibniz, normalExpansion_chain_rule,
    Derivation.leibniz_pow, smul_eq_mul, map_zero] at h
  norm_num only [Nat.cast_ofNat, pow_one, Nat.reduceSub] at h
  linear_combination h

theorem velocity_constant : normalVelocity.constantCoeff = 1 / normalG := by
  have h := congrArg (PowerSeries.constantCoeff (R := K)) normal_velocity_identity
  simp only [map_mul, constantCoeff_normalExpansion, map_one] at h
  apply (eq_div_iff normalG_ne_zero).mpr
  simpa only [normalG, mul_comm] using h

theorem velocity_first_constant :
    (Dt normalVelocity).constantCoeff = -normalG1 / normalG ^ 3 := by
  have h := congrArg (PowerSeries.constantCoeff (R := K)) velocity_first_identity
  simp only [map_add, map_mul, map_pow, constantCoeff_normalExpansion, map_zero,
    velocity_constant] at h
  change normalG1 * (1 / normalG) ^ 2 +
    normalG * (Dt normalVelocity).constantCoeff = 0 at h
  apply (eq_div_iff (pow_ne_zero _ normalG_ne_zero)).mpr
  field_simp [normalG_ne_zero] at h
  linear_combination h

theorem velocity_second_constant :
    (Dt (Dt normalVelocity)).constantCoeff =
      (3 * normalG1 ^ 2 - normalG * normalG2) / normalG ^ 5 := by
  have h := congrArg (PowerSeries.constantCoeff (R := K)) velocity_second_identity
  simp only [map_add, map_mul, map_pow, map_ofNat, constantCoeff_normalExpansion,
    map_zero, velocity_constant, velocity_first_constant] at h
  change normalG2 * (1 / normalG) ^ 3 +
    3 * normalG1 * (1 / normalG) * (-normalG1 / normalG ^ 3) +
    normalG * (Dt (Dt normalVelocity)).constantCoeff = 0 at h
  apply (eq_div_iff (pow_ne_zero _ normalG_ne_zero)).mpr
  field_simp [normalG_ne_zero] at h
  linear_combination h

def densityStream (A : AmbientPoly 4) : S := normalExpansion A * normalVelocity

theorem densityStream_second_derivative (A : AmbientPoly 4) :
    Dt (Dt (densityStream A)) =
      normalExpansion (pderiv 0 (pderiv 0 A)) * normalVelocity ^ 3 +
        3 * normalExpansion (pderiv 0 A) * normalVelocity * Dt normalVelocity +
        normalExpansion A * Dt (Dt normalVelocity) := by
  simp only [densityStream, Derivation.leibniz, map_add, normalExpansion_chain_rule,
    smul_eq_mul]
  ring

/-- The normal Taylor coefficient is the actual residue density used in
the protected affine exactness criterion. -/
theorem densityStream_coefficient_two (A : AmbientPoly 4) :
    PowerSeries.coeff 2 (densityStream A) = affineNormalSource A / normalG := by
  have hcoef := PowerSeries.constantCoeff_iterate_derivative (densityStream A) 2
  norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one, mul_one] at hcoef
  have hderiv := congrArg (PowerSeries.constantCoeff (R := K))
    (densityStream_second_derivative A)
  simp only [map_add, map_mul, map_pow, map_ofNat, constantCoeff_normalExpansion,
    velocity_constant, velocity_first_constant, velocity_second_constant] at hderiv
  have he : PowerSeries.coeff 2 (densityStream A) =
      (affineMap (pderiv 0 (pderiv 0 A)) * (1 / normalG) ^ 3 +
        3 * affineMap (pderiv 0 A) * (1 / normalG) * (-normalG1 / normalG ^ 3) +
        affineMap A * ((3 * normalG1 ^ 2 - normalG * normalG2) / normalG ^ 5)) / 2 := by
    rw [hcoef] at hderiv
    apply (eq_div_iff (by norm_num : (2 : K) ≠ 0)).mpr
    simpa only [mul_comm] using hderiv
  rw [he]
  unfold affineNormalSource normalSourceTwo normalG normalG1 normalG2
  field_simp [normal_ne_zero]
  ring

/-- The density of the actual pulled-back pole-three form in the genuine
normal chart. Its denominator is the image of f, not a formal replacement. -/
def poleThreeDensity (A : AmbientPoly 4) : HahnSeries ℤ K :=
  HahnSeries.ofPowerSeries ℤ K (normalExpansion A) /
      (HahnSeries.ofPowerSeries ℤ K (normalExpansion affineF)) ^ 3 *
    HahnSeries.ofPowerSeries ℤ K normalVelocity

theorem poleThreeDensity_expansion (A : AmbientPoly 4) :
    poleThreeDensity A = HahnSeries.ofPowerSeries ℤ K (densityStream A) *
      HahnSeries.single (-3) 1 := by
  simp only [poleThreeDensity, normalExpansion_F, HahnSeries.ofPowerSeries_X,
    div_eq_mul_inv, HahnSeries.single_pow, nsmul_eq_mul, one_pow,
    HahnSeries.inv_single, inv_one, densityStream, map_mul]
  norm_num
  ring

/-- The Laurent residue of the actual pole-three normal pullback is c/g. -/
theorem poleThreeDensity_residue (A : AmbientPoly 4) :
    (poleThreeDensity A).coeff (-1) = affineNormalSource A / normalG := by
  rw [poleThreeDensity_expansion, HahnSeries.coeff_mul_single]
  norm_num only [Int.reduceSub, mul_one]
  change (HahnSeries.ofPowerSeries ℤ K (densityStream A)).coeff ((2 : ℕ) : ℤ) = _
  rw [HahnSeries.ofPowerSeries_apply_coeff, densityStream_coefficient_two]

/-- Binding to the genuine exterior form used by the certificate theorem.
The coefficient is computed from the actual normal pullback, not postulated. -/
theorem residueSourceForm_eq_formalResidue (A : AmbientPoly 4) :
    CycleQ2AffineExactness.residueSourceForm A =
      (poleThreeDensity A).coeff (-1) • CycleQ2AffineExterior.volume := by
  rw [poleThreeDensity_residue]
  rfl

end CycleQ2FormalResidue

#print axioms CycleQ2FormalResidue.densityStream_coefficient_two
#print axioms CycleQ2FormalResidue.poleThreeDensity_residue
#print axioms CycleQ2FormalResidue.residueSourceForm_eq_formalResidue
end
end


/- Component: continuation_2/NormalChartDerivations.lean -/
section
/-!+# Actual coordinate derivations and Jacobian of the formal normal chart

The coefficient derivations are the actual complex tangent derivations of
the protected affine function field, extended coefficient by coefficient.
The formal parameter is held constant.  The normal derivative and the four
tangent derivations therefore give the implicit-coordinate Jacobian of the
faithful chart already constructed from `f ↦ T`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace CycleQ2PowerSeriesTangents

variable {C K : Type*} [CommRing C] [CommRing K] [Algebra C K]

def coefficientwise (D : Derivation C K K) (f : PowerSeries K) : PowerSeries K :=
  PowerSeries.mk fun n => D (PowerSeries.coeff n f)

@[simp] theorem coefficientwise_coeff (D : Derivation C K K) (f : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff n (coefficientwise D f) = D (PowerSeries.coeff n f) := by
  simp [coefficientwise]

theorem coefficientwise_mul (D : Derivation C K K) (f g : PowerSeries K) :
    coefficientwise D (f * g) = f * coefficientwise D g + g * coefficientwise D f := by
  rw [mul_comm g (coefficientwise D f)]
  ext n
  simp only [coefficientwise_coeff, PowerSeries.coeff_mul, map_sum, map_add,
    Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro ij hij
  ring

/-- Coefficientwise extension as an actual complex-linear derivation. -/
def extend (D : Derivation C K K) : Derivation C (PowerSeries K) (PowerSeries K) where
  toFun := coefficientwise D
  map_add' f g := by
    ext n
    simp
  map_smul' c f := by
    ext n
    simp only [coefficientwise_coeff, PowerSeries.coeff_smul, Derivation.map_smul,
      RingHom.id_apply]
  map_one_eq_zero' := by
    ext n
    by_cases hn : n = 0 <;> simp [PowerSeries.coeff_one, hn]
  leibniz' f g := by
    change coefficientwise D (f * g) = f * coefficientwise D g + g * coefficientwise D f
    exact coefficientwise_mul D f g

@[simp] theorem extend_coeff (D : Derivation C K K) (f : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff n (extend D f) = D (PowerSeries.coeff n f) :=
  coefficientwise_coeff D f n

@[simp] theorem extend_C (D : Derivation C K K) (a : K) :
    extend D (PowerSeries.C a) = PowerSeries.C (D a) := by
  ext n
  by_cases hn : n = 0 <;> simp [PowerSeries.coeff_C, hn]

@[simp] theorem extend_X (D : Derivation C K K) : extend D PowerSeries.X = 0 := by
  ext n
  by_cases hn : n = 1 <;> simp [PowerSeries.coeff_X, hn]

theorem extend_commute (D E : Derivation C K K) (h : Function.Commute D E) :
    Function.Commute (extend D) (extend E) := by
  intro f
  ext n
  simpa only [extend_coeff] using h (PowerSeries.coeff n f)

theorem derivative_extend_commute (D : Derivation C K K) :
    Function.Commute (PowerSeries.derivative K) (extend D) := by
  intro f
  ext n
  simp [PowerSeries.coeff_derivative, Derivation.leibniz, smul_eq_mul, mul_comm]

end CycleQ2PowerSeriesTangents

namespace CycleQ2PolynomialChainRule

open MvPolynomial

variable {R B M σ : Type*} [CommRing R] [CommRing B] [Algebra R B]
  [Fintype σ] [DecidableEq σ] [AddCommGroup M] [Module B M] [Module R M]

/-- The genuine derivation chain rule for any polynomial algebra map. -/
theorem apply (φ : MvPolynomial σ R →ₐ[R] B) (δ : Derivation R B M)
    (P : MvPolynomial σ R) :
    δ (φ P) = ∑ i : σ, φ (pderiv i P) • δ (φ (X i)) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      have hc : φ (MvPolynomial.C c) = algebraMap R B c := φ.commutes c
      rw [hc, Derivation.map_algebraMap]
      simp
  | add P Q ihP ihQ =>
      simp only [map_add, ihP, ihQ, add_smul, Finset.sum_add_distrib]
  | mul_X P i ih =>
      have hs :
          (∑ j : σ, (φ (pderiv j P) * φ (X i)) • δ (φ (X j))) =
          φ (X i) • ∑ j : σ, φ (pderiv j P) • δ (φ (X j)) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [smul_smul]
        congr 1
        ring
      have hd :
          (∑ j : σ, (φ P * φ (pderiv j (X i))) • δ (φ (X j))) =
          φ P • δ (φ (X i)) := by
        simp [pderiv_X, Pi.single_apply, apply_ite]
      rw [map_mul, Derivation.leibniz, ih]
      simp only [pderiv_mul, map_add, map_mul, add_smul, Finset.sum_add_distrib]
      rw [hs, hd]
      exact add_comm _ _

end CycleQ2PolynomialChainRule

namespace CycleQ2NormalChart

open MvPolynomial HodgeComputer CycleQ2AffineClearing CycleQ2AffineHypersurface
  CycleQ2AffineDifferentials CycleQ2FormalSpecialization CycleQ2NormalExpansion

abbrev K := AffineFunctionField
abbrev S := PowerSeries K

def normalAlgHom : AmbientPoly 4 →ₐ[ℂ] S where
  toRingHom := normalExpansion
  commutes' c := by
    change normalExpansion (MvPolynomial.C c) = algebraMap ℂ S c
    rw [normalExpansion_C, PowerSeries.algebraMap_apply]
    rfl

def tangent (j : Fin 4) : Derivation ℂ S S :=
  CycleQ2PowerSeriesTangents.extend (complexTangent j)

def parameterDerivative : Derivation ℂ S S :=
  (PowerSeries.derivative K).restrictScalars ℂ

@[simp] theorem parameterDerivative_apply (f : S) : parameterDerivative f = Dt f := rfl

@[simp] theorem tangent_C (j : Fin 4) (a : K) :
    tangent j (PowerSeries.C a) = PowerSeries.C (affineTangent j a) := by
  exact CycleQ2PowerSeriesTangents.extend_C (complexTangent j) a

@[simp] theorem tangent_X (j : Fin 4) : tangent j PowerSeries.X = 0 :=
  CycleQ2PowerSeriesTangents.extend_X (complexTangent j)

@[simp] theorem tangent_coordinate (j i : Fin 4) :
    tangent j (PowerSeries.C (fieldCoordinate i.succ)) = if i = j then 1 else 0 := by
  rw [tangent_C]
  simp only [fieldCoordinate, affineTangent_coordinate]
  split_ifs <;> simp

theorem tangent_normalExpansion_chain (j : Fin 4) (P : AmbientPoly 4) :
    tangent j (normalExpansion P) =
      normalExpansion (pderiv 0 P) * tangent j normalRoot +
        normalExpansion (pderiv j.succ P) := by
  have h := CycleQ2PolynomialChainRule.apply normalAlgHom (tangent j) P
  change tangent j (normalExpansion P) =
    ∑ i : Fin 5, normalExpansion (pderiv i P) * tangent j (normalExpansion (X i)) at h
  rw [Fin.sum_univ_succ] at h
  simpa only [normalExpansion_X_zero, normalExpansion_X_succ, tangent_coordinate,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] using h

theorem tangent_normalRoot (j : Fin 4) :
    tangent j normalRoot = -normalVelocity * normalExpansion (pderiv j.succ affineF) := by
  have h := tangent_normalExpansion_chain j affineF
  rw [normalExpansion_F, tangent_X] at h
  calc
    tangent j normalRoot =
        (normalExpansion (pderiv 0 affineF) * normalVelocity) * tangent j normalRoot := by
      rw [normal_velocity_identity, one_mul]
    _ = -normalVelocity * normalExpansion (pderiv j.succ affineF) := by
      linear_combination -normalVelocity * h

/-- The actual implicit-coordinate derivative with `f` held equal to the
formal parameter.  Its reciprocal normal derivative is the proved velocity. -/
theorem tangent_normalExpansion (j : Fin 4) (P : AmbientPoly 4) :
    tangent j (normalExpansion P) = normalExpansion (pderiv j.succ P) -
      normalVelocity * normalExpansion (pderiv j.succ affineF) *
        normalExpansion (pderiv 0 P) := by
  rw [tangent_normalExpansion_chain, tangent_normalRoot]
  ring

theorem tangents_commute (i j : Fin 4) : Function.Commute (tangent i) (tangent j) := by
  apply CycleQ2PowerSeriesTangents.extend_commute
  exact affineTangents_commute i j

theorem parameter_tangent_commute (j : Fin 4) :
    Function.Commute parameterDerivative (tangent j) :=
  CycleQ2PowerSeriesTangents.derivative_extend_commute (complexTangent j)

/-- The coordinate derivations are ordered `(∂T,E₁,E₂,E₃,E₄)`. -/
def coordinateDerivative : Fin 5 → Derivation ℂ S S :=
  Fin.cases parameterDerivative tangent

/-- Rows are coordinate derivations; columns are the five original affine
coordinate functions after the actual normal substitution. -/
def jacobian : Matrix (Fin 5) (Fin 5) S :=
  fun i j => coordinateDerivative i (normalExpansion (X j))

theorem jacobian_zero_row (i : Fin 5) :
    jacobian 0 i = if i = 0 then normalVelocity else 0 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [jacobian, coordinateDerivative, normalVelocity]
  · simp [jacobian, coordinateDerivative, Dt]

theorem jacobian_succ_zero (j : Fin 4) :
    jacobian j.succ 0 = -normalVelocity * normalExpansion (pderiv j.succ affineF) := by
  simpa [jacobian, coordinateDerivative] using tangent_normalRoot j

theorem jacobian_succ_succ (i j : Fin 4) :
    jacobian i.succ j.succ = if j = i then 1 else 0 := by
  change tangent i (normalExpansion (X j.succ)) = _
  rw [normalExpansion_X_succ, tangent_coordinate]

/-- The determinant is the actual normal velocity, with positive sign in
the stipulated parameter-first coordinate order. -/
theorem jacobian_det : Matrix.det jacobian = normalVelocity := by
  have hminor : jacobian.submatrix Fin.succ Fin.succ =
      (1 : Matrix (Fin 4) (Fin 4) S) := by
    ext i j
    simp [Matrix.submatrix, jacobian_succ_succ, Matrix.one_apply, eq_comm]
  rw [Matrix.det_succ_row_zero]
  simp [jacobian_zero_row, hminor]

/-! The algebraic Kähler module of a power-series ring need not be generated
by these five coordinate differentials.  The following argument instead
differentiates the actual polynomial relation inside that entire module. -/

abbrev Omega := Ω[S⁄ℂ]
abbrev universalD : Derivation ℂ S Omega := KaehlerDifferential.D ℂ S
abbrev TopForm := ⋀[S]^5 Omega

theorem normalExpansion_complex_constant (c : ℂ) :
    normalExpansion (MvPolynomial.C c) = algebraMap ℂ S c := by
  rw [normalExpansion_C, PowerSeries.algebraMap_apply]
  rfl

/-- The universal polynomial chain rule in the full algebraic Kähler module
of the power-series ring; no finite-rank or continuity assertion is used. -/
theorem universal_polynomial_differential (P : AmbientPoly 4) :
    universalD (normalExpansion P) =
      ∑ i : Fin 5, normalExpansion (pderiv i P) • universalD (normalExpansion (X i)) := by
  exact CycleQ2PolynomialChainRule.apply normalAlgHom universalD P

def tangentDifferential (j : Fin 4) : Omega :=
  universalD (PowerSeries.C (fieldCoordinate j.succ))

theorem universal_normal_differential :
    universalD normalRoot = normalVelocity • universalD PowerSeries.X -
      ∑ j : Fin 4, (normalVelocity * normalExpansion (pderiv j.succ affineF)) •
        tangentDifferential j := by
  have h := universal_polynomial_differential affineF
  rw [normalExpansion_F, Fin.sum_univ_succ] at h
  simp only [normalExpansion_X_zero, normalExpansion_X_succ] at h
  have hm := congrArg (fun η : Omega => normalVelocity • η) h
  have hv : normalVelocity * normalExpansion (pderiv 0 affineF) = 1 := by
    rw [mul_comm, normal_velocity_identity]
  simp only [smul_add, Finset.smul_sum, smul_smul, hv, one_smul] at hm
  exact (eq_sub_iff_add_eq).mpr hm.symm

private def wedgeWithTangents : Omega →ₗ[S] TopForm where
  toFun a := exteriorPower.ιMulti S 5 (Matrix.vecCons a tangentDifferential)
  map_add' a b := (exteriorPower.ιMulti S 5).map_vecCons_add tangentDifferential a b
  map_smul' c a := (exteriorPower.ιMulti S 5).map_vecCons_smul tangentDifferential c a

private theorem wedgeWithTangents_tangent (j : Fin 4) :
    wedgeWithTangents (tangentDifferential j) = 0 := by
  apply (exteriorPower.ιMulti S 5).map_eq_zero_of_eq
    (Matrix.vecCons (tangentDifferential j) tangentDifferential)
    (i := 0) (j := j.succ)
  · simp
  · exact (Fin.succ_ne_zero j).symm

/-- The ordered coordinate volume `dT ∧ dx₁ ∧ ... ∧ dx₄` in the actual
universal exterior power of the formal chart ring. -/
def normalVolume : TopForm :=
  exteriorPower.ιMulti S 5 (Matrix.vecCons (universalD PowerSeries.X) tangentDifferential)

/-- The wedge of the actual universal differentials of the substituted
five affine coordinates: the coordinate-generator exterior pullback. -/
def pulledBackCoordinateVolume : TopForm :=
  exteriorPower.ιMulti S 5 (fun i : Fin 5 => universalD (normalExpansion (X i)))

/-- The Jacobian factor also holds in genuine universal exterior forms,
not merely after evaluating against the five coordinate derivations. -/
theorem pulledBackCoordinateVolume_eq :
    pulledBackCoordinateVolume = normalVelocity • normalVolume := by
  have ht : (fun i : Fin 5 => universalD (normalExpansion (X i))) =
      Matrix.vecCons (universalD normalRoot) tangentDifferential := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [tangentDifferential]
  unfold pulledBackCoordinateVolume
  rw [ht]
  change wedgeWithTangents (universalD normalRoot) = _
  rw [universal_normal_differential, map_sub, map_smul, map_sum]
  simp only [map_smul, wedgeWithTangents_tangent, smul_zero,
    Finset.sum_const_zero, sub_zero]
  rfl

section UniversalExteriorPullback

abbrev AmbientOmega := Ω[(AmbientPoly 4)⁄ℂ]

local instance normalAlgebra : Algebra (AmbientPoly 4) S :=
  normalAlgHom.toRingHom.toAlgebra

local instance normalOmegaModule : Module (AmbientPoly 4) Omega :=
  Module.compHom Omega normalAlgHom.toRingHom

local instance normalTopModule : Module (AmbientPoly 4) TopForm :=
  Module.compHom TopForm normalAlgHom.toRingHom

local instance normalOmegaTower : IsScalarTower (AmbientPoly 4) S Omega where
  smul_assoc a b η := by
    change (normalAlgHom a * b) • η = normalAlgHom a • (b • η)
    exact mul_smul _ _ _

local instance normalTopTower : IsScalarTower (AmbientPoly 4) S TopForm where
  smul_assoc a b η := by
    change (normalAlgHom a * b) • η = normalAlgHom a • (b • η)
    exact mul_smul _ _ _

local instance normalComplexOmegaTower : IsScalarTower ℂ (AmbientPoly 4) Omega where
  smul_assoc c a η := by
    change normalAlgHom (c • a) • η = c • (normalAlgHom a • η)
    rw [map_smul]
    exact smul_assoc _ _ _

/-- The actual map of universal one-forms induced by the normal chart. -/
def oneFormPullback : AmbientOmega →ₗ[AmbientPoly 4] Omega :=
  (universalD.compAlgebraMap (AmbientPoly 4)).liftKaehlerDifferential

@[simp] theorem oneFormPullback_D (P : AmbientPoly 4) :
    oneFormPullback (KaehlerDifferential.D ℂ (AmbientPoly 4) P) =
      universalD (normalExpansion P) := by
  rw [oneFormPullback, Derivation.liftKaehlerDifferential_comp_D]
  rfl

private def targetWedgeOverAmbient :
    Omega [⋀^Fin 5]→ₗ[AmbientPoly 4] TopForm where
  toMultilinearMap := (exteriorPower.ιMulti S 5).toMultilinearMap.restrictScalars (AmbientPoly 4)
  map_eq_zero_of_eq' := (exteriorPower.ιMulti S 5).map_eq_zero_of_eq

/-- The induced exterior pullback, defined by the universal alternating
property and the genuine one-form pullback. -/
def exteriorPullback : (⋀[AmbientPoly 4]^5 AmbientOmega) →ₗ[AmbientPoly 4] TopForm :=
  exteriorPower.alternatingMapLinearEquiv
    (targetWedgeOverAmbient.compLinearMap oneFormPullback)

def ambientCoordinateVolume : ⋀[AmbientPoly 4]^5 AmbientOmega :=
  exteriorPower.ιMulti (AmbientPoly 4) 5
    (fun i : Fin 5 => KaehlerDifferential.D ℂ (AmbientPoly 4) (X i))

theorem exteriorPullback_ambientCoordinateVolume :
    exteriorPullback ambientCoordinateVolume = normalVelocity • normalVolume := by
  rw [exteriorPullback, ambientCoordinateVolume,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.compLinearMap_apply]
  simp only [oneFormPullback_D]
  exact pulledBackCoordinateVolume_eq

end UniversalExteriorPullback

end CycleQ2NormalChart

#print axioms CycleQ2PowerSeriesTangents.extend
#print axioms CycleQ2NormalChart.tangent_normalExpansion
#print axioms CycleQ2NormalChart.jacobian_det
#print axioms CycleQ2NormalChart.universal_normal_differential
#print axioms CycleQ2NormalChart.pulledBackCoordinateVolume_eq
#print axioms CycleQ2NormalChart.exteriorPullback_ambientCoordinateVolume
end
end


/- Component: continuation_2/PureM2Certificate.lean -/
section
/-!+# An exact certificate along the genuine one-term Fermat deformation

For every complex parameter `s`, this module gives a complete certificate for
`sum X_i^6 + s * X₂^3 X₀ X₅ X₃`, with the original protected source monomial.
The denominator is `36 * (X₂^6+X₅^6) * (X₁^6+X₄^6)`.  The factor 36 clears
the rational scalar coefficients of the vector field.  This is a distinct
one-term family, not an assertion about the protected three-term sextic.
-/

noncomputable section
namespace CycleQ2PureM2

set_option maxRecDepth 10000

open MvPolynomial HodgeComputer

abbrev Poly := AmbientPoly 5
abbrev A : Poly := HodgeSubmission.A

def U : Poly := X 2 ^ 6 + X 5 ^ 6
def V : Poly := X 1 ^ 6 + X 4 ^ 6
def M : Poly := X 2 ^ 3 * X 0 * X 5 * X 3
def F (s : ℂ) : Poly :=
  X 0 ^ 6 + X 1 ^ 6 + X 2 ^ 6 + X 3 ^ 6 + X 4 ^ 6 + X 5 ^ 6 + C s * M

def D : Poly := C 36 * (U * V)

def N (s : ℂ) : Fin 6 → Poly :=
  ![0, C (-2 * s) * (A * M * X 1), C 3 * (A * V * X 2),
    0, C (-2 * s) * (A * M * X 4), C 3 * (A * V * X 5)]

theorem U_homogeneous : U.IsHomogeneous 6 := by
  exact (isHomogeneous_X_pow (2 : Fin 6) 6).add (isHomogeneous_X_pow 5 6)

theorem V_homogeneous : V.IsHomogeneous 6 := by
  exact (isHomogeneous_X_pow (1 : Fin 6) 6).add (isHomogeneous_X_pow 4 6)

theorem M_homogeneous : M.IsHomogeneous 6 := by
  have hx (i : Fin 6) : (X i : Poly).IsHomogeneous 1 := isHomogeneous_X ℂ i
  simpa [M] using ((((hx 2).pow 3).mul (hx 0)).mul (hx 5)).mul (hx 3)

theorem F_homogeneous (s : ℂ) : (F s).IsHomogeneous 6 := by
  exact ((((((isHomogeneous_X_pow (0 : Fin 6) 6).add
    (isHomogeneous_X_pow 1 6)).add (isHomogeneous_X_pow 2 6)).add
    (isHomogeneous_X_pow 3 6)).add (isHomogeneous_X_pow 4 6)).add
    (isHomogeneous_X_pow 5 6)).add (M_homogeneous.C_mul s)

theorem D_homogeneous : D.IsHomogeneous 12 := by
  simpa [D] using (U_homogeneous.mul V_homogeneous).C_mul (36 : ℂ)

theorem D_ne_zero : D ≠ 0 := by
  intro h
  have hh := congrArg (MvPolynomial.eval (fun _ : Fin 6 => (1 : ℂ))) h
  norm_num [D, U, V] at hh

theorem D_totalDegree : D.totalDegree = 12 := D_homogeneous.totalDegree D_ne_zero

theorem N_homogeneous (s : ℂ) (i : Fin 6) : (N s i).IsHomogeneous 19 := by
  have hA : A.IsHomogeneous 12 := CycleQ2Workspace.originalA_homogeneous
  have hx (j : Fin 6) : (X j : Poly).IsHomogeneous 1 := isHomogeneous_X ℂ j
  have hU (j : Fin 6) : (C (3 : ℂ) * (A * V * X j)).IsHomogeneous 19 := by
    simpa using ((hA.mul V_homogeneous).mul (hx j)).C_mul (3 : ℂ)
  have hM (j : Fin 6) : (C (-2 * s) * (A * M * X j)).IsHomogeneous 19 := by
    simpa using ((hA.mul M_homogeneous).mul (hx j)).C_mul (-2 * s)
  fin_cases i
  · exact isHomogeneous_zero (Fin 6) ℂ 19
  · exact hM 1
  · exact hU 2
  · exact isHomogeneous_zero (Fin 6) ℂ 19
  · exact hM 4
  · exact hU 5

/- The elementary univariate retraction and monic argument also used for the
Fermat subset denominators.  Here the perturbation is linear in `X 0`, so it
preserves monicity and both denominator factors are constant in this variable. -/
private def toUni : Poly →+* Polynomial Poly :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun i => if i = 0 then Polynomial.X else Polynomial.C (X i))

private def fromUni : Polynomial Poly →+* Poly :=
  Polynomial.eval₂RingHom (RingHom.id Poly) (X 0)

private theorem retract : fromUni.comp toUni = RingHom.id Poly := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [toUni, fromUni]
  · intro i
    by_cases hi : i = 0 <;> simp [toUni, fromUni, hi]

private theorem monic_relPrime_constant {R : Type*} [CommRing R] [IsDomain R]
    {f : Polynomial R} (hf : f.Monic) {c : R} (hc : c ≠ 0) :
    IsRelPrime f (Polynomial.C c) := by
  intro p hpf hpc
  by_contra hunit
  have hpos := Polynomial.natDegree_pos_of_not_isUnit_of_dvd_monic hf hunit hpf
  have hle := Polynomial.natDegree_le_of_dvd hpc (Polynomial.C_ne_zero.mpr hc)
  simp only [Polynomial.natDegree_C] at hle
  omega

private theorem toUni_F_monic (s : ℂ) : (toUni (F s)).Monic := by
  have hrepr : toUni (F s) = (Polynomial.X : Polynomial Poly) ^ 6 +
      (Polynomial.C (C s * X 2 ^ 3 * X 5 * X 3) * Polynomial.X +
       Polynomial.C (X 1 ^ 6 + X 2 ^ 6 + X 3 ^ 6 + X 4 ^ 6 + X 5 ^ 6)) := by
    simp [toUni, F, M]
    ring
  rw [hrepr]
  apply Polynomial.monic_X_pow_add
  exact (Polynomial.degree_add_le_of_le (Polynomial.degree_C_mul_X_le _)
    Polynomial.degree_C_le).trans_lt (by norm_num)

private theorem toUni_D : toUni D = Polynomial.C D := by
  simp [toUni, D, U, V]

theorem F_ne_zero (s : ℂ) : F s ≠ 0 := by
  intro h
  exact (toUni_F_monic s).ne_zero (by rw [h, map_zero])

theorem denominator_legal (s : ℂ) : IsRelPrime (F s) D := by
  apply HodgeComputer.relPrime_of_retract toUni fromUni retract
  rw [toUni_D]
  exact monic_relPrime_constant (toUni_F_monic s) D_ne_zero

private theorem sum_six (f : Fin 6 → Poly) :
    ∑ i, f i = f 0 + (f 1 + (f 2 + (f 3 + (f 4 + f 5)))) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  rfl

set_option maxHeartbeats 2000000 in
theorem normalized_directional (s : ℂ) :
    (2 : Poly) * HodgeTestbed.directional (F s) (N s) = A * D := by
  unfold HodgeTestbed.directional
  rw [sum_six]
  simp [F, N, A,
    HodgeSubmission.A, D, U, V, M, map_add, pderiv_X, map_mul, map_neg, map_ofNat]
  ring

set_option maxHeartbeats 2000000 in
theorem divergence_zero (s : ℂ) : HodgeTestbed.divergenceNumerator D (N s) = 0 := by
  have h2 (i : Fin 6) : pderiv i (2 : Poly) = 0 := (pderiv i).map_natCast 2
  have h3 (i : Fin 6) : pderiv i (3 : Poly) = 0 := (pderiv i).map_natCast 3
  have h36 (i : Fin 6) : pderiv i (36 : Poly) = 0 := (pderiv i).map_natCast 36
  unfold HodgeTestbed.divergenceNumerator HodgeTestbed.divergence HodgeTestbed.directional
  rw [sum_six, sum_six]
  simp [N, A, HodgeSubmission.A,
    D, U, V, M, map_add, pderiv_mul, pderiv_X,
    h2, h3, h36, map_mul, map_neg, map_ofNat]
  ring

theorem verified (s : ℂ) : Verify (F s) A 6 2 D (N s) 0 where
  hypersurface_ne_zero := F_ne_zero s
  hypersurface_homogeneous := F_homogeneous s
  source_homogeneous := by
    simpa using Homogeneous.of_isHomogeneous CycleQ2Workspace.originalA_homogeneous
  denominator_ne_zero := D_ne_zero
  denominator_homogeneous := by simpa only [D_totalDegree] using D_homogeneous
  numerator_homogeneous := by
    intro i
    simpa [D_totalDegree] using Homogeneous.of_isHomogeneous (N_homogeneous s i)
  denominator_legal := denominator_legal s
  identity := normalized_identity (normalized_directional s) (by
    simpa only [mul_zero] using divergence_zero s)

/-- A complete, unconditional certificate along this one-term family. -/
theorem hasCertificate (s : ℂ) : HasCertificate (F s) 2 HodgeSubmission.A :=
  (verified s).hasCertificate

end CycleQ2PureM2

#print axioms CycleQ2PureM2.denominator_legal
#print axioms CycleQ2PureM2.normalized_directional
#print axioms CycleQ2PureM2.divergence_zero
#print axioms CycleQ2PureM2.hasCertificate
end
end


/- Component: continuation_2/CartierMatrixFactorization.lean -/
section
/-!
# Actual polynomial resolution data for the invariant Cartier curve

All entries below are literal polynomials over an arbitrary commutative ring.
The six by six matrices factor the actual cubic a^3-b^3+c^3+d^3.
The augmentation is the previously constructed elliptic-sextic residual ideal.
The two original second syzygies alone do not give the full hypersurface
resolution: the four columns of H0 are necessary.

No geometric deformation theorem or characteristic-zero rank lifting is
asserted in this file.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CycleQ2CartierResolution

variable {R : Type*} [CommRing R] (a b c d : R)

def cubic : R := a ^ 3 - b ^ 3 + c ^ 3 + d ^ 3

def first : Matrix (Fin 4) (Fin 6) R :=
  !![a^2, b^2, -c^2, d^2, a*d, -b*c;
     c, -d, a, -b, 0, 0;
     b, a, 0, 0, c, -d;
     0, 0, d, c, b, a]

def second : Matrix (Fin 6) (Fin 2) R :=
  !![d, 0; c, 0; 0, b; 0, a; -a, -d; b, -c]

def homotopy0 : Matrix (Fin 6) (Fin 4) R :=
  !![a, c^2, -b^2, b*c;
     -b, -d^2, a^2, a*d;
     -c, a^2, a*d, d^2;
     d, b^2, -b*c, c^2;
     0, -b*c, c^2, -b^2;
     0, -a*d, -d^2, a^2]

def homotopy1 : Matrix (Fin 2) (Fin 6) R :=
  !![d^2, c^2, -b*c, -a*d, -a^2, -b^2;
     -a*d, b*c, -b^2, a^2, -d^2, -c^2]

def even : Matrix (Fin 6) (Fin 6) R :=
  !![d, 0, a, c^2, -b^2, b*c;
     c, 0, -b, -d^2, a^2, a*d;
     0, b, -c, a^2, a*d, d^2;
     0, a, d, b^2, -b*c, c^2;
     -a, -d, 0, -b*c, c^2, -b^2;
     b, -c, 0, -a*d, -d^2, a^2]

def odd : Matrix (Fin 6) (Fin 6) R :=
  !![d^2, c^2, -b*c, -a*d, -a^2, -b^2;
     -a*d, b*c, -b^2, a^2, -d^2, -c^2;
     a^2, b^2, -c^2, d^2, a*d, -b*c;
     c, -d, a, -b, 0, 0;
     b, a, 0, 0, c, -d;
     0, 0, d, c, b, a]

def generators : Matrix (Fin 1) (Fin 4) R :=
  !![a^2*b - c*d^2 + 2*c*(a*c+b*d),
     -2*a^3*c+a^2*d^2+a*b*c^2+2*b^3*c-b^2*c*d,
     -2*a^2*c*d-a*b^3+a*d^3-2*b^2*c^2+b*c^2*d,
     a*b^2*c-2*a*c*d^2-b^3*d+2*b*c^3+d^4]

def cubicColumn : Matrix (Fin 1) (Fin 6) R :=
  !![-a*b, 0, 2*a*c-d^2, -2*b*c, -b*d, 0]

theorem first_second : first a b c d * second a b c d = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [first, second, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem first_homotopy0 : first a b c d * homotopy0 a b c d =
    cubic a b c d • (1 : Matrix (Fin 4) (Fin 4) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [first, homotopy0, cubic, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem homotopy_identity :
    second a b c d * homotopy1 a b c d + homotopy0 a b c d * first a b c d =
      cubic a b c d • (1 : Matrix (Fin 6) (Fin 6) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [first, second, homotopy0, homotopy1, cubic,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem homotopy1_second : homotopy1 a b c d * second a b c d =
    cubic a b c d • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [homotopy1, second, cubic, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem homotopy1_homotopy0 : homotopy1 a b c d * homotopy0 a b c d = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [homotopy1, homotopy0, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem even_odd : even a b c d * odd a b c d =
    cubic a b c d • (1 : Matrix (Fin 6) (Fin 6) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [even, odd, cubic, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem odd_even : odd a b c d * even a b c d =
    cubic a b c d • (1 : Matrix (Fin 6) (Fin 6) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [even, odd, cubic, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem augmentation_first :
    generators a b c d * first a b c d + cubic a b c d • cubicColumn a b c d = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [generators, first, cubicColumn, cubic,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem cubicColumn_second : cubicColumn a b c d * second a b c d = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cubicColumn, second, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem cubicColumn_homotopy0 :
    cubicColumn a b c d * homotopy0 a b c d + generators a b c d = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cubicColumn, homotopy0, generators,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

end CycleQ2CartierResolution

#print axioms CycleQ2CartierResolution.even_odd
#print axioms CycleQ2CartierResolution.odd_even
#print axioms CycleQ2CartierResolution.homotopy_identity
#print axioms CycleQ2CartierResolution.augmentation_first
#print axioms CycleQ2CartierResolution.cubicColumn_homotopy0
end


/- Component: continuation_2/CartierMatrixFactorizationExactness.lean -/
section
/-!
# Genuine exactness of the actual periodic complex modulo the cubic

A matrix factorization over a domain gives an exact two-periodic complex
after quotienting by its nonzero scalar. The proof lifts a kernel vector,
uses divisibility by the scalar, and cancels that scalar in the domain.
The resulting theorem is applied to the actual six by six cubic matrices.

This proves quotient-module exactness. It does not assert saturation,
base change through the cubic section, or nonlinear geometric lifting.
-/

set_option autoImplicit false

noncomputable section
namespace CycleQ2CartierResolution

open Matrix

variable {R : Type*} [CommRing R] [IsDomain R]

theorem matrixFactorization_exact_mod
    {n : Type*} [Fintype n] [DecidableEq n]
    (g : R) (hg : g ≠ 0) (A B : Matrix n n R)
    (hAB : A * B = g • (1 : Matrix n n R))
    (hBA : B * A = g • (1 : Matrix n n R))
    (x : n → R ⧸ Ideal.span ({g} : Set R)) :
    A.map (Ideal.Quotient.mk (Ideal.span ({g} : Set R))) *ᵥ x = 0 ↔
      ∃ y, B.map (Ideal.Quotient.mk (Ideal.span ({g} : Set R))) *ᵥ y = x := by
  let I : Ideal R := Ideal.span ({g} : Set R)
  let q : R →+* R ⧸ I := Ideal.Quotient.mk I
  change A.map q *ᵥ x = 0 ↔ ∃ y, B.map q *ᵥ y = x
  have hqg : q g = 0 := by
    apply (Ideal.Quotient.eq_zero_iff_mem).mpr
    exact Ideal.subset_span (Set.mem_singleton g)
  have hqAB : A.map q * B.map q = 0 := by
    rw [← Matrix.map_mul, hAB]
    ext i j
    simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, hqg]
  constructor
  · intro hx
    choose z hz using fun i => Ideal.Quotient.mk_surjective (x i)
    have hqz : q ∘ z = x := funext hz
    have hdiv : ∀ i, g ∣ (A *ᵥ z) i := by
      intro i
      apply Ideal.mem_span_singleton.mp
      apply (Ideal.Quotient.eq_zero_iff_mem).mp
      change q ((A *ᵥ z) i) = 0
      rw [RingHom.map_mulVec, hqz, hx]
      rfl
    choose y hy using hdiv
    have hAz : A *ᵥ z = g • y := by
      funext i
      exact hy i
    have hcancel : g • z = g • (B *ᵥ y) := by
      calc
        g • z = (B * A) *ᵥ z := by
          rw [hBA, smul_mulVec, one_mulVec]
        _ = B *ᵥ (A *ᵥ z) := (mulVec_mulVec z B A).symm
        _ = B *ᵥ (g • y) := by rw [hAz]
        _ = g • (B *ᵥ y) := mulVec_smul B g y
    have hzy : z = B *ᵥ y := by
      funext i
      apply mul_left_cancel₀ hg
      exact congrArg (fun v : n → R => v i) hcancel
    refine ⟨q ∘ y, ?_⟩
    funext i
    rw [← RingHom.map_mulVec, ← hzy]
    exact hz i
  · rintro ⟨y, rfl⟩
    rw [mulVec_mulVec, hqAB, zero_mulVec]

abbrev cubicQuotient (a b c d : R) := R ⧸ Ideal.span ({cubic a b c d} : Set R)

def cubicQuotientMap (a b c d : R) : R →+* cubicQuotient a b c d :=
  Ideal.Quotient.mk (Ideal.span ({cubic a b c d} : Set R))

theorem even_exact_mod_cubic (a b c d : R) (hg : cubic a b c d ≠ 0)
    (x : Fin 6 → cubicQuotient a b c d) :
    (even a b c d).map (cubicQuotientMap a b c d) *ᵥ x = 0 ↔
      ∃ y, (odd a b c d).map (cubicQuotientMap a b c d) *ᵥ y = x :=
  matrixFactorization_exact_mod (cubic a b c d) hg (even a b c d) (odd a b c d)
    (even_odd a b c d) (odd_even a b c d) x

theorem odd_exact_mod_cubic (a b c d : R) (hg : cubic a b c d ≠ 0)
    (x : Fin 6 → cubicQuotient a b c d) :
    (odd a b c d).map (cubicQuotientMap a b c d) *ᵥ x = 0 ↔
      ∃ y, (even a b c d).map (cubicQuotientMap a b c d) *ᵥ y = x :=
  matrixFactorization_exact_mod (cubic a b c d) hg (odd a b c d) (even a b c d)
    (odd_even a b c d) (even_odd a b c d) x

end CycleQ2CartierResolution

#print axioms CycleQ2CartierResolution.matrixFactorization_exact_mod
#print axioms CycleQ2CartierResolution.even_exact_mod_cubic
#print axioms CycleQ2CartierResolution.odd_exact_mod_cubic
end
end


/- Component: continuation_2/SegreSyzygyElimination.lean -/
section
/-!
# The actual nonlinear Segre relations and complementary-equation elimination

The sixteen rows are the twelve off-diagonal adjugate relations and four
diagonal differences. They are polynomial identities for every three by
three matrix, not identities only at the geometric seed.

The last two theorems justify dropping redundant equations after adjoining
an inverse of the complementary relation minor. They do not assume that a
selected square system has a solution; that input is supplied separately by
the trusted generic lifting theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CycleQ2SegreRelations
open Matrix

variable {R : Type*} [CommRing R]

def cofactors (M : Matrix (Fin 3) (Fin 3) R) : Fin 9 → R :=
  ![M 1 1*M 2 2-M 1 2*M 2 1,
    M 1 2*M 2 0-M 1 0*M 2 2,
    M 1 0*M 2 1-M 1 1*M 2 0,
    M 0 2*M 2 1-M 0 1*M 2 2,
    M 0 0*M 2 2-M 0 2*M 2 0,
    M 0 1*M 2 0-M 0 0*M 2 1,
    M 0 1*M 1 2-M 0 2*M 1 1,
    M 0 2*M 1 0-M 0 0*M 1 2,
    M 0 0*M 1 1-M 0 1*M 1 0]

def cofactorMatrix (M : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  !![cofactors M 0, cofactors M 1, cofactors M 2;
     cofactors M 3, cofactors M 4, cofactors M 5;
     cofactors M 6, cofactors M 7, cofactors M 8]

theorem cofactorMatrix_eq_transpose_adjugate (M : Matrix (Fin 3) (Fin 3) R) :
    cofactorMatrix M = M.adjugate.transpose := by
  rw [adjugate_fin_three]
  ext i j
  fin_cases i <;> fin_cases j
  · change M 1 1*M 2 2-M 1 2*M 2 1 = M 1 1*M 2 2-M 1 2*M 2 1
    ring
  · change M 1 2*M 2 0-M 1 0*M 2 2 = -(M 1 0*M 2 2)+M 1 2*M 2 0
    ring
  · change M 1 0*M 2 1-M 1 1*M 2 0 = M 1 0*M 2 1-M 1 1*M 2 0
    ring
  · change M 0 2*M 2 1-M 0 1*M 2 2 = -(M 0 1*M 2 2)+M 0 2*M 2 1
    ring
  · change M 0 0*M 2 2-M 0 2*M 2 0 = M 0 0*M 2 2-M 0 2*M 2 0
    ring
  · change M 0 1*M 2 0-M 0 0*M 2 1 = -(M 0 0*M 2 1)+M 0 1*M 2 0
    ring
  · change M 0 1*M 1 2-M 0 2*M 1 1 = M 0 1*M 1 2-M 0 2*M 1 1
    ring
  · change M 0 2*M 1 0-M 0 0*M 1 2 = -(M 0 0*M 1 2)+M 0 2*M 1 0
    ring
  · change M 0 0*M 1 1-M 0 1*M 1 0 = M 0 0*M 1 1-M 0 1*M 1 0
    ring

def relations (M : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 16) (Fin 9) R :=
  !![0,0,0, M 0 0,M 0 1,M 0 2, 0,0,0;
     0,0,0, 0,0,0, M 0 0,M 0 1,M 0 2;
     M 1 0,M 1 1,M 1 2, 0,0,0, 0,0,0;
     0,0,0, 0,0,0, M 1 0,M 1 1,M 1 2;
     M 2 0,M 2 1,M 2 2, 0,0,0, 0,0,0;
     0,0,0, M 2 0,M 2 1,M 2 2, 0,0,0;
     M 0 1,0,0, M 1 1,0,0, M 2 1,0,0;
     M 0 2,0,0, M 1 2,0,0, M 2 2,0,0;
     0,M 0 0,0, 0,M 1 0,0, 0,M 2 0,0;
     0,M 0 2,0, 0,M 1 2,0, 0,M 2 2,0;
     0,0,M 0 0, 0,0,M 1 0, 0,0,M 2 0;
     0,0,M 0 1, 0,0,M 1 1, 0,0,M 2 1;
     -M 0 0,-M 0 1,-M 0 2, M 1 0,M 1 1,M 1 2, 0,0,0;
     -M 0 0,-M 0 1,-M 0 2, 0,0,0, M 2 0,M 2 1,M 2 2;
     -M 0 0,M 0 1,0, -M 1 0,M 1 1,0, -M 2 0,M 2 1,0;
     -M 0 0,0,M 0 2, -M 1 0,0,M 1 2, -M 2 0,0,M 2 2]

/-- The sixteen genuine nonlinear polynomial relations on the nine cofactors. -/
theorem relations_cofactors (M : Matrix (Fin 3) (Fin 3) R) :
    relations M *ᵥ cofactors M = 0 := by
  funext i
  fin_cases i <;>
    norm_num [relations, cofactors, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]

/-- At any point where the chosen complementary relation block is a unit,
vanishing of the selected equations forces all residual equations to vanish. -/
theorem residual_eq_zero_of_relation_block
    (A : Matrix n n R) (B : Matrix n m R) (v : n → R) (e : m → R)
    (hrel : A *ᵥ v + B *ᵥ e = 0) (he : e = 0) (hdet : IsUnit A.det) : v = 0 := by
  have hv : A *ᵥ v = 0 := by simpa [he] using hrel
  calc
    v = (A⁻¹ * A) *ᵥ v := by rw [nonsing_inv_mul A hdet, one_mulVec]
    _ = A⁻¹ *ᵥ (A *ᵥ v) := (mulVec_mulVec v A⁻¹ A).symm
    _ = 0 := by rw [hv, mulVec_zero]

/-- The elimination lemma after arbitrary coefficient evaluation, as needed
at the generic algebraic point produced by square-system lifting. -/
theorem evaluated_residual_eq_zero
    {S : Type*} [CommRing S] (f : R →+* S)
    (A : Matrix n n R) (B : Matrix n m R) (v : n → R) (e : m → R)
    (hrel : A *ᵥ v + B *ᵥ e = 0)
    (he : f ∘ e = 0) (hdet : IsUnit (f A.det)) : f ∘ v = 0 := by
  apply residual_eq_zero_of_relation_block (A.map f) (B.map f) (f ∘ v) (f ∘ e)
  · funext i
    change (A.map f *ᵥ (f ∘ v)) i + (B.map f *ᵥ (f ∘ e)) i = 0
    rw [← RingHom.map_mulVec, ← RingHom.map_mulVec, ← map_add]
    have hz := congrArg (fun z : n → R => z i) hrel
    change (A *ᵥ v) i + (B *ᵥ e) i = 0 at hz
    rw [hz, map_zero]
  · exact he
  · change IsUnit (f.mapMatrix A).det
    rw [← f.map_det]
    exact hdet

end CycleQ2SegreRelations

#print axioms CycleQ2SegreRelations.relations_cofactors
#print axioms CycleQ2SegreRelations.residual_eq_zero_of_relation_block
#print axioms CycleQ2SegreRelations.evaluated_residual_eq_zero
end


/- Component: continuation_2/SegreLocalFactorization.lean -/
section
/-!
# Local factorization of the actual three-by-three Segre equations

The nine equations are the row-major cofactors, i.e. the transpose of
mathlib's actual adjugate. Their vanishing is equivalent to all two-by-two
minors vanishing. On every chart where one entry is a unit, the matrix has
an explicit outer-product factorization. Its image has a generator whose
pivot coordinate is one, with the coordinate projection as a left inverse.
No global line-bundle, deformation, or geometric existence claim is made.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

noncomputable section
namespace CycleQ2SegreLocal

open Matrix
open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- Row-major signed cofactors; the equation index is `(row,column)`. -/
def cofactors (M : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  M.adjugate.transpose

/-- The actual nine cofactor equations imply every two-by-two minor. -/
theorem minors_of_cofactors_zero (M : Matrix (Fin 3) (Fin 3) R)
    (h : cofactors M = 0) (i j k l : Fin 3) :
    M i j * M k l = M i l * M k j := by
  have ha : M.adjugate = 0 := by
    simpa [cofactors] using congrArg Matrix.transpose h
  rw [Matrix.adjugate_fin_three] at ha
  have h00 : M 1 1 * M 2 2 - M 1 2 * M 2 1 = 0 :=
    congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A 0 0) ha
  have h01 : -(M 0 1 * M 2 2) + M 0 2 * M 2 1 = 0 :=
    congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A 0 1) ha
  have h02 : M 0 1 * M 1 2 - M 0 2 * M 1 1 = 0 :=
    congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A 0 2) ha
  have h10 : -(M 1 0 * M 2 2) + M 1 2 * M 2 0 = 0 :=
    congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A 1 0) ha
  have h11 : M 0 0 * M 2 2 - M 0 2 * M 2 0 = 0 :=
    congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A 1 1) ha
  have h12 : -(M 0 0 * M 1 2) + M 0 2 * M 1 0 = 0 :=
    congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A 1 2) ha
  have h20 : M 1 0 * M 2 1 - M 1 1 * M 2 0 = 0 :=
    congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A 2 0) ha
  have h21 : -(M 0 0 * M 2 1) + M 0 1 * M 2 0 = 0 :=
    congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A 2 1) ha
  have h22 : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 0 :=
    congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A 2 2) ha
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> dsimp at * <;>
    solve
    | ring1
    | linear_combination h00
    | linear_combination -h00
    | linear_combination h01
    | linear_combination -h01
    | linear_combination h02
    | linear_combination -h02
    | linear_combination h10
    | linear_combination -h10
    | linear_combination h11
    | linear_combination -h11
    | linear_combination h12
    | linear_combination -h12
    | linear_combination h20
    | linear_combination -h20
    | linear_combination h21
    | linear_combination -h21
    | linear_combination h22
    | linear_combination -h22

/-- A unit entry gives a normalized column and the actual pivot row. -/
theorem unit_pivot_factorization (M : Matrix (Fin 3) (Fin 3) R)
    (h : cofactors M = 0) (i0 j0 : Fin 3) (u : Rˣ)
    (hu : (u : R) = M i0 j0) (i j : Fin 3) :
    M i j = (M i j0 * (↑(u⁻¹) : R)) * M i0 j := by
  have hm := minors_of_cofactors_zero M h i j i0 j0
  calc
    M i j = (M i j * M i0 j0) * (↑(u⁻¹) : R) := by
      rw [← hu, mul_assoc, Units.mul_inv, mul_one]
    _ = (M i j0 * M i0 j) * (↑(u⁻¹) : R) := by rw [hm]
    _ = (M i j0 * (↑(u⁻¹) : R)) * M i0 j := by ring

/-- Conversely, every literal outer product satisfies all nine equations. -/
theorem cofactors_outerProduct (a b : Fin 3 → R) :
    cofactors (fun i j => a i * b j) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cofactors, Matrix.adjugate_fin_three, Matrix.transpose_apply] <;> ring

/-- No field hypothesis is needed for the pivot chart. -/
theorem normalized_factorization (M : Matrix (Fin 3) (Fin 3) R)
    (h : cofactors M = 0) (i0 j0 : Fin 3) (hu : IsUnit (M i0 j0)) :
    ∃ a b : Fin 3 → R, a i0 = 1 ∧ b = M i0 ∧
      (∀ i j, M i j = a i * b j) := by
  obtain ⟨u, hu⟩ := hu
  refine ⟨fun i => M i j0 * (↑(u⁻¹) : R), M i0, ?_, rfl, ?_⟩
  · change M i0 j0 * (↑(u⁻¹) : R) = 1
    rw [← hu, Units.mul_inv]
  · exact unit_pivot_factorization M h i0 j0 u hu

/-- The normalized column generates the image. Its pivot coordinate gives
an explicit left inverse, so this local image is a free rank-one summand. -/
theorem image_generator_with_retraction (M : Matrix (Fin 3) (Fin 3) R)
    (h : cofactors M = 0) (i0 j0 : Fin 3) (hu : IsUnit (M i0 j0)) :
    ∃ a : Fin 3 → R,
      a i0 = 1 ∧
      (∀ x : Fin 3 → R, M *ᵥ x = (∑ j, M i0 j * x j) • a) ∧
      (∀ r : R, (r • a) i0 = r) ∧
      (∀ r : R, ∃ x : Fin 3 → R, M *ᵥ x = r • a) := by
  obtain ⟨u, hunit⟩ := hu
  let a : Fin 3 → R := fun i => M i j0 * (↑(u⁻¹) : R)
  have ha : a i0 = 1 := by
    dsimp [a]
    rw [← hunit, Units.mul_inv]
  have hf (i j : Fin 3) : M i j = a i * M i0 j :=
    unit_pivot_factorization M h i0 j0 u hunit i j
  have hmul (x : Fin 3 → R) : M *ᵥ x = (∑ j, M i0 j * x j) • a := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hf]
    ring
  refine ⟨a, ha, hmul, ?_, ?_⟩
  · intro r
    simp [ha]
  · intro r
    refine ⟨Pi.single j0 ((↑(u⁻¹) : R) * r), ?_⟩
    rw [hmul]
    simp [Pi.single_apply, ← hunit]

end CycleQ2SegreLocal

#print axioms CycleQ2SegreLocal.minors_of_cofactors_zero
#print axioms CycleQ2SegreLocal.normalized_factorization
#print axioms CycleQ2SegreLocal.image_generator_with_retraction
end
end


/- Component: continuation_2/SegreImageLine.lean -/
section
/-!
# The actual image module on a Segre pivot chart

A vanishing cofactor matrix and a unit entry give an explicit linear
isomorphism from the coefficient ring to the matrix image. The separate
basepoint lemma shows how actual ideal-membership witnesses provide a
pivot after evaluation in a field. Neither theorem assumes a line bundle.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace CycleQ2SegreImage

open Matrix
open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- The image submodule of the actual matrix map is a free line on any
unit-entry chart. The isomorphism is proved directly from the equations. -/
theorem image_linearEquiv (M : Matrix (Fin 3) (Fin 3) R)
    (h : CycleQ2SegreLocal.cofactors M = 0)
    (i0 j0 : Fin 3) (hu : IsUnit (M i0 j0)) :
    Nonempty (R ≃ₗ[R] LinearMap.range M.mulVecLin) := by
  obtain ⟨a, ha, hmul, hret, hsurj⟩ :=
    CycleQ2SegreLocal.image_generator_with_retraction M h i0 j0 hu
  let f : R →ₗ[R] LinearMap.range M.mulVecLin :=
    { toFun := fun r => ⟨r • a, hsurj r⟩
      map_add' := by
        intro r s
        apply Subtype.ext
        exact add_smul r s a
      map_smul' := by
        intro r s
        apply Subtype.ext
        exact mul_smul r s a }
  have hinj : Function.Injective f := by
    intro r s hrs
    have hval := congrArg (fun v : LinearMap.range M.mulVecLin => v.val i0) hrs
    change (r • a) i0 = (s • a) i0 at hval
    simpa only [hret] using hval
  have honto : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := y.property
    refine ⟨∑ j, M i0 j * x j, ?_⟩
    apply Subtype.ext
    change (∑ j, M i0 j * x j) • a = y.val
    rw [← hmul]
    exact hx
  exact ⟨LinearEquiv.ofBijective f ⟨hinj, honto⟩⟩

/-- Ideal membership is enough to exclude a common zero of the matrix
entries wherever one of the tested coordinates is nonzero. -/
theorem exists_nonzero_entry_of_coordinate_powers
    {ι K : Type*} [Field K] (M : Matrix (Fin 3) (Fin 3) R)
    (coordinates : ι → R) (degrees : ι → ℕ)
    (hmem : ∀ i, coordinates i ^ degrees i ∈
      Ideal.span (Set.range (fun p : Fin 3 × Fin 3 => M p.1 p.2)))
    (φ : R →+* K) (hpoint : ∃ i, φ (coordinates i) ≠ 0) :
    ∃ i j, φ (M i j) ≠ 0 := by
  by_contra! hzero
  have hker : Ideal.span (Set.range (fun p : Fin 3 × Fin 3 => M p.1 p.2)) ≤
      RingHom.ker φ := by
    apply Ideal.span_le.mpr
    rintro z ⟨p, rfl⟩
    exact hzero p.1 p.2
  obtain ⟨i, hi⟩ := hpoint
  have hz : φ (coordinates i ^ degrees i) = 0 := hker (hmem i)
  rw [map_pow] at hz
  exact pow_ne_zero _ hi hz

/-- The same basepoint witnesses yield an actual unit-entry chart in any
field-valued point satisfying the nonzero-coordinate condition. -/
theorem exists_unit_entry_of_coordinate_powers
    {ι K : Type*} [Field K] (M : Matrix (Fin 3) (Fin 3) R)
    (coordinates : ι → R) (degrees : ι → ℕ)
    (hmem : ∀ i, coordinates i ^ degrees i ∈
      Ideal.span (Set.range (fun p : Fin 3 × Fin 3 => M p.1 p.2)))
    (φ : R →+* K) (hpoint : ∃ i, φ (coordinates i) ≠ 0) :
    ∃ i j, IsUnit (φ (M i j)) := by
  obtain ⟨i, j, hij⟩ := exists_nonzero_entry_of_coordinate_powers
    M coordinates degrees hmem φ hpoint
  exact ⟨i, j, isUnit_iff_ne_zero.mpr hij⟩

end CycleQ2SegreImage

#print axioms CycleQ2SegreImage.image_linearEquiv
#print axioms CycleQ2SegreImage.exists_nonzero_entry_of_coordinate_powers
#print axioms CycleQ2SegreImage.exists_unit_entry_of_coordinate_powers
end
end


/- Component: continuation_2/SegreCechDlog.lean -/
section
/-!
# Explicit overlap units and the Kähler Čech cocycle of a rank-one matrix

The common coefficient ring in these theorems may be the coordinate ring of
any overlap of unit-entry charts. No field hypothesis is used. The transition
units are calculated from the actual matrix entries and chosen pivot units.
The additive cocycle takes values in mathlib's universal Kähler module.

The first-column equations generate the same ideal on overlaps. A separate
nonzerodivisor hypothesis is needed to call their zero scheme an effective
Cartier divisor. This file does not construct a cycle class, a Gysin map, an
Abel--Jacobi map, or a rational primitive.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section
namespace CycleQ2SegreCech

open Matrix

variable {R : Type*} [CommRing R]

abbrev Chart := Fin 3 × Fin 3

/-- The image generator normalized to one at the pivot row. -/
def column (M : Matrix (Fin 3) (Fin 3) R) (p : Chart) (up : Rˣ) : Fin 3 → R :=
  fun i => M i p.2 * (↑(up⁻¹) : R)

private theorem transition_mul_reverse
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2) :
    (M q.1 p.2 * (↑(up⁻¹) : R)) * (M p.1 q.2 * (↑(uq⁻¹) : R)) = 1 := by
  have hm := CycleQ2SegreLocal.minors_of_cofactors_zero M hM q.1 p.2 p.1 q.2
  calc
    _ = (M q.1 p.2 * M p.1 q.2) * ((↑(up⁻¹) : R) * (↑(uq⁻¹) : R)) := by ring
    _ = (M q.1 q.2 * M p.1 p.2) * ((↑(up⁻¹) : R) * (↑(uq⁻¹) : R)) := by rw [hm]
    _ = ((up : R) * ↑(up⁻¹)) * ((uq : R) * ↑(uq⁻¹)) := by rw [← hp, ← hq]; ring
    _ = 1 := by rw [Units.mul_inv, Units.mul_inv, mul_one]

/-- The unit carrying the normalized image generator on chart `q` to the
one on chart `p`. Its inverse is another explicit matrix-entry ratio. -/
def transition
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2) : Rˣ where
  val := M q.1 p.2 * (↑(up⁻¹) : R)
  inv := M p.1 q.2 * (↑(uq⁻¹) : R)
  val_inv := transition_mul_reverse M hM p q up uq hp hq
  inv_val := transition_mul_reverse M hM q p uq up hq hp

@[simp] theorem transition_val
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2) :
    (transition M hM p q up uq hp hq : R) = column M p up q.1 := rfl

theorem column_pivot
    (M : Matrix (Fin 3) (Fin 3) R) (p : Chart) (up : Rˣ)
    (hp : (up : R) = M p.1 p.2) : column M p up p.1 = 1 := by
  simp [column, ← hp]

/-- The explicit normalized columns glue by the displayed transition unit. -/
theorem column_overlap
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2)
    (i : Fin 3) :
    column M p up i = (transition M hM p q up uq hp hq : R) * column M q uq i := by
  change M i p.2 * (↑(up⁻¹) : R) =
    (M q.1 p.2 * (↑(up⁻¹) : R)) * (M i q.2 * (↑(uq⁻¹) : R))
  rw [CycleQ2SegreLocal.unit_pivot_factorization M hM q.1 q.2 uq hq i p.2]
  ring

@[simp] theorem transition_self
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p : Chart) (up : Rˣ) (hp : (up : R) = M p.1 p.2) :
    transition M hM p p up up hp hp = 1 := by
  apply Units.ext
  exact column_pivot M p up hp

theorem transition_reverse
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2) :
    transition M hM q p uq up hq hp = (transition M hM p q up uq hp hq)⁻¹ := by
  apply Units.ext
  rfl

/-- The multiplicative Čech cocycle on every triple overlap. -/
theorem transition_cocycle
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q r : Chart) (up uq ur : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2)
    (hr : (ur : R) = M r.1 r.2) :
    transition M hM p q up uq hp hq * transition M hM q r uq ur hq hr =
      transition M hM p r up ur hp hr := by
  apply Units.ext
  exact (column_overlap M hM p q up uq hp hq r.1).symm

/-- The pivot row gives the local first-column equation. The same transition
unit relates its equations on different charts. -/
theorem row_overlap
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2)
    (j : Fin 3) :
    M q.1 j = (transition M hM p q up uq hp hq : R) * M p.1 j :=
  CycleQ2SegreLocal.unit_pivot_factorization M hM p.1 p.2 up hp q.1 j

theorem first_column_ideal_overlap
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2) :
    Ideal.span ({M q.1 0} : Set R) = Ideal.span ({M p.1 0} : Set R) := by
  rw [row_overlap M hM p q up uq hp hq 0]
  exact Ideal.span_singleton_mul_left_unit (transition M hM p q up uq hp hq).isUnit _

/-- Passing to an overlap ring preserves the actual cofactor equations. -/
theorem cofactors_map_zero
    {S : Type*} [CommRing S] (f : R →+* S)
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0) :
    CycleQ2SegreLocal.cofactors (f.mapMatrix M) = 0 := by
  unfold CycleQ2SegreLocal.cofactors
  rw [← f.map_adjugate]
  change f.mapMatrix (CycleQ2SegreLocal.cofactors M) = 0
  rw [hM]
  ext i j
  exact f.map_zero

/-- Restriction of an overlap unit is the unit computed from the restricted
matrix. In particular the displayed cocycle is compatible with localization. -/
theorem transition_map
    {S : Type*} [CommRing S] (f : R →+* S)
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2) :
    Units.map f.toMonoidHom (transition M hM p q up uq hp hq) =
      transition (f.mapMatrix M) (cofactors_map_zero f M hM) p q
        (Units.map f.toMonoidHom up) (Units.map f.toMonoidHom uq)
        (congrArg f hp) (congrArg f hq) := by
  apply Units.ext
  exact f.map_mul _ _

/-- A homogeneous matrix of degree `d` needs the ambient `O(d)` transition
as well as the normalized-image transition. Here `xp,xq` trivialize `O(1)`
on the chosen projective coordinate charts. -/
def twistedTransition
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2)
    (xp xq : Rˣ) (d : ℕ) : Rˣ :=
  (xp * xq⁻¹)^d * transition M hM p q up uq hp hq

theorem twistedTransition_cocycle
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q r : Chart) (up uq ur : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2)
    (hr : (ur : R) = M r.1 r.2) (xp xq xr : Rˣ) (d : ℕ) :
    twistedTransition M hM p q up uq hp hq xp xq d *
      twistedTransition M hM q r uq ur hq hr xq xr d =
        twistedTransition M hM p r up ur hp hr xp xr d := by
  have ha : (xp * xq⁻¹)^d * (xq * xr⁻¹)^d = (xp * xr⁻¹)^d := by
    rw [← mul_pow]
    congr 1
    group
  dsimp [twistedTransition]
  calc
    _ = ((xp * xq⁻¹)^d * (xq * xr⁻¹)^d) *
        (transition M hM p q up uq hp hq * transition M hM q r uq ur hq hr) := by
      ac_rfl
    _ = _ := by rw [ha, transition_cocycle]

/-- The degree-`d` local first-column equations transform by the twisted
unit, so their local principal ideals agree. -/
theorem homogeneous_first_column_overlap
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2)
    (xp xq : Rˣ) (d : ℕ) :
    M q.1 0 * (↑(xq⁻¹) : R)^d =
      (twistedTransition M hM p q up uq hp hq xp xq d : R) *
        (M p.1 0 * (↑(xp⁻¹) : R)^d) := by
  have ha : ((xp * xq⁻¹)^d : Rˣ) * (xp⁻¹)^d = (xq⁻¹)^d := by
    rw [← mul_pow]
    congr 1
    calc
      _ = (xp * xp⁻¹) * xq⁻¹ := by ac_rfl
      _ = xq⁻¹ := by rw [mul_inv_cancel, one_mul]
  have hb : (↑(xp * xq⁻¹) : R)^d * (↑(xp⁻¹) : R)^d = (↑(xq⁻¹) : R)^d :=
    congrArg (fun u : Rˣ => (u : R)) ha
  rw [row_overlap M hM p q up uq hp hq 0]
  change ((transition M hM p q up uq hp hq : R) * M p.1 0) * (↑(xq⁻¹) : R)^d =
    ((↑(xp * xq⁻¹) : R)^d * (transition M hM p q up uq hp hq : R)) *
      (M p.1 0 * (↑(xp⁻¹) : R)^d)
  rw [← hb]
  ring

section Differential

variable (K : Type*) [CommRing K] [Algebra K R]

/-- Logarithmic differential in the actual universal Kähler module. -/
def unitDlog (u : Rˣ) : Ω[R⁄K] :=
  (↑(u⁻¹) : R) • KaehlerDifferential.D K R (u : R)

@[simp] theorem unitDlog_one : unitDlog K (1 : Rˣ) = 0 := by
  simp [unitDlog]

theorem unitDlog_mul (u v : Rˣ) :
    unitDlog K (u * v) = unitDlog K u + unitDlog K v := by
  simp only [unitDlog, _root_.mul_inv_rev, Units.val_mul, Derivation.leibniz,
    smul_add, smul_smul]
  have hu : ((↑(v⁻¹) : R) * ↑(u⁻¹)) * ↑u = ↑(v⁻¹) := by simp [mul_assoc]
  have hv : ((↑(v⁻¹) : R) * ↑(u⁻¹)) * ↑v = ↑(u⁻¹) := by
    calc
      _ = (↑(u⁻¹) : R) * (↑(v⁻¹) * ↑v) := by ring
      _ = ↑(u⁻¹) := by rw [Units.inv_mul, mul_one]
  rw [hu, hv, add_comm]

theorem unitDlog_inv (u : Rˣ) : unitDlog K u⁻¹ = -unitDlog K u := by
  have h := unitDlog_mul K u u⁻¹
  simp only [mul_inv_cancel, unitDlog_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem unitDlog_pow (u : Rˣ) (n : ℕ) : unitDlog K (u^n) = n • unitDlog K u := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, unitDlog_mul, ih, succ_nsmul]

/-- Evaluation by any derivation gives the ordinary logarithmic derivative;
the construction is genuinely universal, rather than an assumed trace. -/
theorem unitDlog_apply
    {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower K R V]
    (d : Derivation K R V) (u : Rˣ) :
    d.liftKaehlerDifferential (unitDlog K u) = (↑(u⁻¹) : R) • d (u : R) := by
  simp [unitDlog]

/-- The universal logarithmic differential commutes with restriction to an
algebra, including every further localization of a chart overlap. -/
theorem unitDlog_map
    {S : Type*} [CommRing S] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
    (u : Rˣ) :
    KaehlerDifferential.map K K R S (unitDlog K u) =
      unitDlog K (Units.map (algebraMap R S).toMonoidHom u) := by
  simp only [unitDlog, map_smul, KaehlerDifferential.map_D,
    Units.coe_map_inv, Units.coe_map]
  exact (algebraMap_smul S (↑(u⁻¹) : R) _).symm

/-- The ambient twist is retained in the Kähler cocycle. The actual Segre
entries have `d=14`; identifying the seed divisor class is a separate binding. -/
theorem twistedTransition_dlog
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2)
    (xp xq : Rˣ) (d : ℕ) :
    unitDlog K (twistedTransition M hM p q up uq hp hq xp xq d) =
      d • (unitDlog K xp - unitDlog K xq) +
        unitDlog K (transition M hM p q up uq hp hq) := by
  rw [twistedTransition, unitDlog_mul, unitDlog_pow, unitDlog_mul, unitDlog_inv,
    sub_eq_add_neg]

/-- The actual Kähler Čech one-cocycle of the normalized image generators. -/
theorem transition_dlog_cocycle
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q r : Chart) (up uq ur : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2)
    (hr : (ur : R) = M r.1 r.2) :
    unitDlog K (transition M hM p q up uq hp hq) +
      unitDlog K (transition M hM q r uq ur hq hr) =
        unitDlog K (transition M hM p r up ur hp hr) := by
  rw [← unitDlog_mul, transition_cocycle]

theorem transition_dlog_reverse
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2) :
    unitDlog K (transition M hM q p uq up hq hp) =
      -unitDlog K (transition M hM p q up uq hp hq) := by
  rw [transition_reverse, unitDlog_inv]

end Differential
end CycleQ2SegreCech

#print axioms CycleQ2SegreCech.transition_cocycle
#print axioms CycleQ2SegreCech.first_column_ideal_overlap
#print axioms CycleQ2SegreCech.transition_dlog_cocycle
#print axioms CycleQ2SegreCech.unitDlog_apply
end
end


/- Component: continuation_2/OpenSquareLifting.lean -/
section
/-!
A nonsingular square polynomial system has a finite separable generic point
inside any principal open containing the seed.  The open condition is imposed
by an actual additional equation u * c(x) - 1, whose Jacobian is block triangular.
This is an algebraic existence statement, not a formal-series lifting premise.
It creates no particular incidence seed or rank certificate.
-/

noncomputable section

set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2OpenSquareLifting

open MvPolynomial HoldoutConstruction

variable {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The inverse coordinate is the left summand; the original coordinates are
in the right summand. -/
def extendedPoint (x : ι → T) (u : T) : Unit ⊕ ι → T :=
  Sum.elim (fun _ => u) x

/-- Actual polynomial equations for the chosen square system on the principal
open defined by c. -/
def openSystem (equations : ι → MvPolynomial ι R) (c : MvPolynomial ι R) :
    Unit ⊕ ι → MvPolynomial (Unit ⊕ ι) R :=
  Sum.elim (fun _ => X (Sum.inl ()) * rename Sum.inr c - 1)
    (fun i => rename Sum.inr (equations i))

@[simp] theorem aeval_extended_rename (x : ι → T) (u : T)
    (p : MvPolynomial ι R) :
    aeval (extendedPoint x u) (rename (Sum.inr : ι → Unit ⊕ ι) p) = aeval x p := by
  rw [aeval_rename]
  rfl

@[simp] theorem pderiv_inverse_rename (p : MvPolynomial ι R) :
    pderiv (Sum.inl ()) (rename (Sum.inr : ι → Unit ⊕ ι) p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [pderiv_mul, hp, pderiv_X, Pi.single_apply]

@[simp] theorem pderiv_original_rename (i : ι) (p : MvPolynomial ι R) :
    pderiv (Sum.inr i) (rename (Sum.inr : ι → Unit ⊕ ι) p) =
      rename Sum.inr (pderiv i p) :=
  pderiv_rename Sum.inr_injective i p

/-- An actual solution with an inverse for c evaluates every augmented
polynomial equation to zero. -/
theorem openSystem_seed (equations : ι → MvPolynomial ι R)
    (c : MvPolynomial ι R) (x : ι → T) (u : T)
    (hx : ∀ i, aeval x (equations i) = 0) (hu : u * aeval x c = 1) :
    ∀ i, aeval (extendedPoint x u) (openSystem equations c i) = 0 := by
  intro i
  cases i with
  | inl z => cases z; simpa [openSystem, aeval_rename, extendedPoint, Function.comp_def] using sub_eq_zero.mpr hu
  | inr i => simpa [openSystem] using hx i

/-- The full augmented Jacobian is a triangular block matrix.  This equality
holds at every point, independently of the polynomial equations. -/
theorem openSystem_jacobian_det (equations : ι → MvPolynomial ι R)
    (c : MvPolynomial ι R) (x : ι → T) (u : T) :
    Matrix.det (fun i j => aeval (extendedPoint x u)
      (pderiv i (openSystem equations c j))) =
    aeval x c * Matrix.det (fun i j => aeval x (pderiv i (equations j))) := by
  have hmatrix :
      (fun i j => aeval (extendedPoint x u) (pderiv i (openSystem equations c j))) =
      Matrix.fromBlocks (fun (_ _ : Unit) => aeval x c)
        (0 : Matrix Unit ι T)
        (fun i (_ : Unit) => u * aeval x (pderiv i c))
        (fun i j => aeval x (pderiv i (equations j))) := by
    ext i j
    cases i with
    | inl z =>
      cases z
      cases j with
      | inl w => cases w; simp [openSystem, aeval_rename, extendedPoint, Function.comp_def, Matrix.fromBlocks]
      | inr j => simp [openSystem, Matrix.fromBlocks]
    | inr i =>
      cases j with
      | inl w =>
        cases w
        simp [openSystem, aeval_rename, extendedPoint, Function.comp_def, Matrix.fromBlocks, pderiv_X]
      | inr j => simp [openSystem, Matrix.fromBlocks]
  rw [hmatrix, Matrix.det_fromBlocks_zero₁₂, Matrix.det_unique]

/-- Every solution of the augmented system solves the original system, and
its value of c is a unit. -/
theorem solution_on_open (equations : ι → MvPolynomial ι R)
    (c : MvPolynomial ι R) (z : Unit ⊕ ι → T)
    (hz : ∀ i, aeval z (openSystem equations c i) = 0) :
    (∀ i, aeval (fun i => z (Sum.inr i)) (equations i) = 0) ∧
      IsUnit (aeval (fun i => z (Sum.inr i)) c) := by
  have hrename (p : MvPolynomial ι R) :
      aeval z (rename (Sum.inr : ι → Unit ⊕ ι) p) =
        aeval (fun i => z (Sum.inr i)) p := by rw [aeval_rename]; rfl
  constructor
  · intro i
    simpa only [openSystem, Sum.elim_inr, hrename] using hz (Sum.inr i)
  · have hi := hz (Sum.inl ())
    simp only [openSystem, Sum.elim_inl, map_sub, map_mul, aeval_X, map_one,
      hrename, sub_eq_zero] at hi
    refine ⟨⟨aeval (fun i => z (Sum.inr i)) c, z (Sum.inl ()), ?_, hi⟩, rfl⟩
    exact (mul_comm (aeval (fun i => z (Sum.inr i)) c) (z (Sum.inl ()))).trans hi

section GenericPoint

set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] [Algebra R K] [Nontrivial T]

/-- A genuine finite separable generic solution inside the specified open
locus, obtained from a nonsingular special-fiber seed.  Coefficients must
embed in K; the special-fiber coefficient map need not be injective. -/
theorem square_system_generic_lift_on_open
    (equations : ι → MvPolynomial ι R) (c : MvPolynomial ι R)
    (seed : ι → T)
    (hseed : ∀ i, aeval seed (equations i) = 0)
    (hjac : IsUnit (Matrix.det
      (fun i j => aeval seed (pderiv i (equations j)))))
    (hc : IsUnit (aeval seed c))
    (hinj : Function.Injective (algebraMap R K)) :
    ∃ I : Ideal (SquareGenericAlgebra K (openSystem equations c)), I.IsMaximal ∧
      Module.Finite K ((SquareGenericAlgebra K (openSystem equations c)) ⧸ I) ∧
      Algebra.IsSeparable K ((SquareGenericAlgebra K (openSystem equations c)) ⧸ I) ∧
      ∃ x : ι → ((SquareGenericAlgebra K (openSystem equations c)) ⧸ I),
        (∀ i, aeval x (equations i) = 0) ∧ IsUnit (aeval x c) := by
  obtain ⟨u, hu⟩ := hc.exists_left_inv
  have haug := openSystem_seed equations c seed u hseed hu
  have hjaug : IsUnit (Matrix.det (fun i j => aeval (extendedPoint seed u)
      (pderiv i (openSystem equations c j)))) := by
    rw [openSystem_jacobian_det]
    exact hc.mul hjac
  obtain ⟨I, hI, hfinite, hsep, hsol, hj⟩ :=
    ReflectionCoupledFano.square_system_generic_lift (K := K)
      (openSystem equations c) (extendedPoint seed u) haug hjaug hinj
  clear hj
  generalize hcoords : squareGenericCoordinates (K := K) (openSystem equations c) I = z at hsol
  refine ⟨I, hI, hfinite, hsep, (fun i => z (Sum.inr i)), ?_, ?_⟩
  · intro i
    have hi := hsol (Sum.inr i)
    change aeval z (rename (Sum.inr : ι → Unit ⊕ ι) (equations i)) = 0 at hi
    rw [aeval_rename] at hi
    exact hi
  · have hi := hsol (Sum.inl ())
    change aeval z (X (Sum.inl ()) * rename (Sum.inr : ι → Unit ⊕ ι) c - 1) = 0 at hi
    simp only [map_sub, map_mul, aeval_X, map_one, aeval_rename, sub_eq_zero] at hi
    refine ⟨⟨aeval (fun i => z (Sum.inr i)) c, z (Sum.inl ()), ?_, hi⟩, rfl⟩
    exact (mul_comm (aeval (fun i => z (Sum.inr i)) c) (z (Sum.inl ()))).trans hi

end GenericPoint

end CycleQ2OpenSquareLifting

#print axioms CycleQ2OpenSquareLifting.openSystem_jacobian_det
#print axioms CycleQ2OpenSquareLifting.square_system_generic_lift_on_open
end
end


/- Component: continuation_2/SquareAdicLifting.lean -/
section
/-!
Actual adic lifting of square polynomial systems with invertible seed Jacobian.
The proof uses the established étale Jacobian localization and mathlib's
compatible infinitesimal lifts into an adically complete ring.  The seed is
preserved.  No existence of a formal solution is assumed.
-/

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SquareAdicLifting

open MvPolynomial HoldoutConstruction

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual polynomial presentation map into its Jacobian localization. -/
def polynomialToEtale (equations : ι → MvPolynomial ι R) :
    MvPolynomial ι R →ₐ[R] SquareEtaleRing equations :=
  (IsScalarTower.toAlgHom R (SquareSystemRing equations) (SquareEtaleRing equations)).comp
    (Ideal.Quotient.mkₐ R (Ideal.span (Set.range equations)))

@[simp] theorem polynomialToEtale_equation (equations : ι → MvPolynomial ι R) (i : ι) :
    polynomialToEtale equations (equations i) = 0 := by
  have hz : Ideal.Quotient.mk (Ideal.span (Set.range equations)) (equations i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
  change algebraMap (SquareSystemRing equations) (SquareEtaleRing equations)
    (Ideal.Quotient.mk _ (equations i)) = 0
  rw [hz, map_zero]

/-- The square system lifts from the residue ring into any complete adic
algebra, while retaining its specified residue coordinates. -/
theorem square_system_adic_lift (equations : ι → MvPolynomial ι R)
    (I : Ideal S) [IsAdicComplete I S] (seed : ι → S ⧸ I)
    (hseed : ∀ i, aeval seed (equations i) = 0)
    (hjac : IsUnit (Matrix.det
      (fun i j => aeval seed (pderiv i (equations j))))) :
    ∃ x : ι → S,
      (∀ i, Ideal.Quotient.mk I (x i) = seed i) ∧
      (∀ i, aeval x (equations i) = 0) := by
  letI : Algebra.Etale R (SquareEtaleRing equations) :=
    square_system_jacobian_etale equations
  let f : SquareEtaleRing equations →ₐ[R] S ⧸ I :=
    squareSystemEtaleEval equations seed hseed hjac
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete f
  let x : ι → S := fun i => g (polynomialToEtale equations (X i))
  have heval : aeval x = g.comp (polynomialToEtale equations) := by
    ext i
    simp [x]
  have hres : f.comp (polynomialToEtale equations) = aeval seed := by
    ext i
    simp [f, polynomialToEtale, squareSystemEtaleEval, squareSystemEval,
      IsLocalization.Away.liftAlgHom, Ideal.Quotient.lift_mk]
  refine ⟨x, ?_, ?_⟩
  · intro i
    have h := AlgHom.congr_fun hg (polynomialToEtale equations (X i))
    change Ideal.Quotient.mk I (x i) = f (polynomialToEtale equations (X i)) at h
    rw [h]
    have hs := AlgHom.congr_fun hres (X i)
    simpa only [AlgHom.comp_apply, aeval_X] using hs
  · intro i
    rw [heval, AlgHom.comp_apply, polynomialToEtale_equation, map_zero]

section PowerSeries

variable {K : Type*} [CommRing K]

/-- Square equations with arbitrary formal coefficients have an actual
formal solution through each nonsingular constant seed.  The hypotheses
are polynomial evaluation and the actual partial-derivative Jacobian. -/
theorem square_system_powerSeries_lift
    (equations : ι → MvPolynomial ι (PowerSeries K)) (seed : ι → K)
    (hseed : ∀ i, eval₂ PowerSeries.constantCoeff seed (equations i) = 0)
    (hjac : IsUnit (Matrix.det (fun i j =>
      eval₂ PowerSeries.constantCoeff seed (pderiv i (equations j))))) :
    ∃ x : ι → PowerSeries K,
      (∀ i, PowerSeries.constantCoeff (x i) = seed i) ∧
      (∀ i, aeval x (equations i) = 0) := by
  letI : Algebra (PowerSeries K) K := PowerSeries.constantCoeff.toAlgebra
  let cc : PowerSeries K →ₐ[PowerSeries K] K :=
    { PowerSeries.constantCoeff with commutes' := by intro r; rfl }
  let I : Ideal (PowerSeries K) := RingHom.ker cc
  have hI : I = Ideal.span {PowerSeries.X} := by
    ext z
    simp only [I, RingHom.mem_ker, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    rfl
  letI : IsAdicComplete I (PowerSeries K) := by
    rw [hI]
    infer_instance
  let e : ((PowerSeries K) ⧸ I) ≃ₐ[PowerSeries K] K :=
    Ideal.quotientKerAlgEquivOfSurjective (f := cc) PowerSeries.constantCoeff_surj
  let seed' : ι → (PowerSeries K) ⧸ I := fun i => e.symm (seed i)
  have heval (p : MvPolynomial ι (PowerSeries K)) :
      aeval seed' p = e.symm (eval₂ PowerSeries.constantCoeff seed p) := by
    exact (MvPolynomial.comp_aeval_apply seed e.symm.toAlgHom p).symm
  have hs : ∀ i, aeval seed' (equations i) = 0 := by
    intro i
    rw [heval, hseed i, map_zero]
  have hj : IsUnit (Matrix.det (fun i j => aeval seed' (pderiv i (equations j)))) := by
    simp only [heval]
    have hd :
        Matrix.det (fun i j => e.symm
          (eval₂ PowerSeries.constantCoeff seed (pderiv i (equations j)))) =
        e.symm (Matrix.det (fun i j =>
          eval₂ PowerSeries.constantCoeff seed (pderiv i (equations j)))) :=
      (e.symm.toAlgHom.map_det (fun i j =>
        eval₂ PowerSeries.constantCoeff seed (pderiv i (equations j)))).symm
    rw [hd]
    exact hjac.map e.symm.toRingEquiv.toRingHom
  obtain ⟨x, hx, heq⟩ := square_system_adic_lift equations I seed' hs hj
  refine ⟨x, ?_, heq⟩
  intro i
  have hi := congrArg e (hx i)
  change cc (x i) = e (e.symm (seed i)) at hi
  have hcc (z : PowerSeries K) : cc z = PowerSeries.constantCoeff z := rfl
  simpa only [AlgEquiv.apply_symm_apply, hcc] using hi

end PowerSeries

end CycleQ2SquareAdicLifting

#print axioms CycleQ2SquareAdicLifting.square_system_adic_lift
#print axioms CycleQ2SquareAdicLifting.square_system_powerSeries_lift
end
end


/- Component: continuation_2/SegreFormalLifting.lean -/
section
/-!
# Formal lifting with genuine redundant polynomial equations

A nonsingular square subsystem lifts through its seed. If the residual
polynomials satisfy actual polynomial relations whose complementary block
is invertible at the seed, every omitted equation vanishes along that lift.
All coefficient series may vary: the theorem is not a tangent-only statement.
No seed or minor of the particular large incidence system is assumed proved.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace CycleQ2SegreFormalLifting

open MvPolynomial Matrix

variable {K ι κ : Type*} [CommRing K]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The complete nonlinear system has a seed-preserving formal solution.
The premises concern polynomial identities and the two actual seed minors;
none assumes a formal solution of either the full or square system. -/
theorem lift_all_equations
    (equations : ι → MvPolynomial ι (PowerSeries K))
    (residual : κ → MvPolynomial ι (PowerSeries K))
    (A : Matrix κ κ (MvPolynomial ι (PowerSeries K)))
    (B : Matrix κ ι (MvPolynomial ι (PowerSeries K)))
    (hrelations : A *ᵥ residual + B *ᵥ equations = 0)
    (seed : ι → K)
    (hseed : ∀ i, eval₂ PowerSeries.constantCoeff seed (equations i) = 0)
    (hjac : IsUnit (Matrix.det (fun i j =>
      eval₂ PowerSeries.constantCoeff seed (pderiv i (equations j)))))
    (hcomplement : IsUnit (eval₂ PowerSeries.constantCoeff seed A.det)) :
    ∃ x : ι → PowerSeries K,
      (∀ i, PowerSeries.constantCoeff (x i) = seed i) ∧
      (∀ i, aeval x (equations i) = 0) ∧
      (∀ j, aeval x (residual j) = 0) := by
  obtain ⟨x, hx, heq⟩ :=
    CycleQ2SquareAdicLifting.square_system_powerSeries_lift equations seed hseed hjac
  have hcc (p : MvPolynomial ι (PowerSeries K)) :
      PowerSeries.constantCoeff (aeval x p) = eval₂ PowerSeries.constantCoeff seed p := by
    induction p using MvPolynomial.induction_on with
    | C c => simp
    | add p q hp hq => simp only [map_add, eval₂_add, hp, hq]
    | mul_X p i hp => simp only [map_mul, aeval_X, eval₂_mul, eval₂_X, hp, hx]
  have hunit : IsUnit (aeval x A.det) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    rw [hcc]
    exact hcomplement
  let φ : MvPolynomial ι (PowerSeries K) →+* PowerSeries K :=
    (aeval x).toRingHom
  have heq' : φ ∘ equations = 0 := by
    funext i
    exact heq i
  have hr : φ ∘ residual = 0 :=
    CycleQ2SegreRelations.evaluated_residual_eq_zero
      φ A B residual equations hrelations heq' hunit
  refine ⟨x, hx, heq, ?_⟩
  intro j
  exact congrFun hr j

end CycleQ2SegreFormalLifting

#print axioms CycleQ2SegreFormalLifting.lift_all_equations
end
end


/- Component: continuation_2/SegreSeedPolynomials.lean -/
section
/-!
# Literal polynomial identities for the chosen Segre seed

All coefficients and sections come from the explicit seed and its 25 linkage
pairings.  Every theorem is a universal identity over a commutative ring,
proved by ordinary ring normalization or by smaller proved identities.
In particular, no relation r^3=2 is needed here: r is an arbitrary coefficient.
The nine cofactors are divisible by the actual G before imposing h.
This module asserts no rank bound, projective basepoint freeness, deformation
existence, residue primitive, or protected certificate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

noncomputable section
namespace CycleQ2SegreSeed

open Matrix

variable {R : Type*} [CommRing R]

def linkageP (a b c d : R) : R := a * c + b * d
def linkageG (a b c d : R) : R := a ^ 3 - b ^ 3 + c ^ 3 + d ^ 3

def linkageE (a b c d : R) : Fin 5 → R :=
  ![a * c + b * d,
  a ^ 3 - b ^ 3,
  a ^ 2 * d + b ^ 2 * c,
  a * d ^ 2 - b * c ^ 2,
  c ^ 3 + d ^ 3]

def linkageEprime (a b c d : R) : Fin 5 → R :=
  ![a * c + b * d,
  a ^ 3 + d ^ 3,
  a ^ 2 * b - c * d ^ 2,
  a * b ^ 2 + c ^ 2 * d,
  -b ^ 3 + c ^ 3]

def linkageQ (a b c d : R) : Matrix (Fin 5) (Fin 5) R :=
  ![![a * c + b * d,
  a ^ 3 + d ^ 3,
  a ^ 2 * b - c * d ^ 2,
  a * b ^ 2 + c ^ 2 * d,
  -b ^ 3 + c ^ 3],
  ![a ^ 3 - b ^ 3,
  -a ^ 2 * c ^ 2 + a * b * c * d - b ^ 2 * d ^ 2,
  -a ^ 2 * d ^ 2 - a * b * c ^ 2 + b ^ 2 * c * d,
  a ^ 2 * c * d - a * b * d ^ 2 - b ^ 2 * c ^ 2,
  a ^ 2 * c ^ 2 - a * b * c * d + b ^ 2 * d ^ 2],
  ![a ^ 2 * d + b ^ 2 * c,
  a ^ 2 * b ^ 2 - a * c ^ 2 * d + b * c * d ^ 2,
  a * b ^ 3 - a * d ^ 3 - b * c ^ 2 * d,
  a * c * d ^ 2 + b ^ 4 - b * d ^ 3,
  -a ^ 2 * b ^ 2 + a * c ^ 2 * d - b * c * d ^ 2],
  ![a * d ^ 2 - b * c ^ 2,
  -a ^ 2 * b * c + a * b ^ 2 * d - c ^ 2 * d ^ 2,
  -a * b ^ 2 * c + b ^ 3 * d - d ^ 4,
  a ^ 2 * b * d - b ^ 3 * c + c * d ^ 3,
  a ^ 2 * b * c - a * b ^ 2 * d + c ^ 2 * d ^ 2],
  ![c ^ 3 + d ^ 3,
  a ^ 2 * c ^ 2 - a * b * c * d + b ^ 2 * d ^ 2,
  a ^ 2 * d ^ 2 + a * b * c ^ 2 - b ^ 2 * c * d,
  -a ^ 2 * c * d + a * b * d ^ 2 + b ^ 2 * c ^ 2,
  -a ^ 2 * c ^ 2 + a * b * c * d - b ^ 2 * d ^ 2]]

def linkageT (a b c d : R) : Matrix (Fin 5) (Fin 5) R :=
  ![![0,
  0,
  0,
  0,
  0],
  ![0,
  a ^ 3,
  a ^ 2 * b,
  a * b ^ 2,
  -b ^ 3],
  ![0,
  a ^ 2 * d,
  a * b * d,
  b ^ 2 * d,
  b ^ 2 * c],
  ![0,
  a * d ^ 2,
  b * d ^ 2,
  -b * c * d,
  -b * c ^ 2],
  ![0,
  d ^ 3,
  -c * d ^ 2,
  c ^ 2 * d,
  c ^ 3]]

/-- All 25 exact linkage pairings, with their literal polynomial quotients. -/
theorem linkage_pairing (a b c d : R) (i j : Fin 5) :
    linkageE a b c d i * linkageEprime a b c d j =
      linkageP a b c d * linkageQ a b c d i j +
      linkageG a b c d * linkageT a b c d i j := by
  fin_cases i <;> fin_cases j <;>
    simp only [linkageE, linkageEprime, linkageP, linkageG, linkageQ, linkageT,
      Matrix.of_apply, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] <;> ring

/-- The ordinary signed cross product, used only as a polynomial expression. -/
def cross (u v : Fin 3 → R) : Fin 3 → R :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

/-- A small Cauchy--Binet identity, proved directly over a commutative ring. -/
theorem cofactors_rank_two (u v s t : Fin 3 → R) :
    (Matrix.adjugate (fun i j => u i * s j + v i * t j)).transpose =
      fun i j => cross u v i * cross s t j := by
  rw [Matrix.adjugate_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.transpose_apply, cross, Matrix.of_apply,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring

def coreRight0 (a b c d u0 u1 u2 : R) : R :=
  (a*c+b*d)*u0 + (a^2*b-c*d^2)*u1 + (a*b^2+c^2*d)*u2

def coreRight1 (a b c d u0 u1 u2 : R) : R :=
  (a^3-b^3)*u0 + (-a^2*d^2-a*b*c^2+b^2*c*d)*u1 +
    (a^2*c*d-a*b*d^2-b^2*c^2)*u2

def coreMinorQuotient (a b c d u0 u1 u2 v0 v1 v2 : R) : R :=
  -(a^2*b)*(u0*v1-v0*u1) - (a*b^2)*(u0*v2-v0*u2) +
    (a*b*c*d)*(u1*v2-v1*u2)

/-- The three central two-by-two minors have their actual common factor G. -/
theorem coreRight_minor (a b c d u0 u1 u2 v0 v1 v2 : R) :
    coreRight0 a b c d u0 u1 u2 * coreRight1 a b c d v0 v1 v2 -
      coreRight0 a b c d v0 v1 v2 * coreRight1 a b c d u0 u1 u2 =
      linkageG a b c d * coreMinorQuotient a b c d u0 u1 u2 v0 v1 v2 := by
  unfold coreRight0 coreRight1 linkageG coreMinorQuotient
  ring

def coreProductCorrection (a b u1 v1 v2 : R) : R :=
  u1 * (v1 * (a^2*b) + v2 * (a*b^2))

theorem core_product (a b c d u0 u1 v0 v1 v2 : R) :
    (u0*linkageP a b c d + u1*(a^3-b^3)) * coreRight0 a b c d v0 v1 v2 =
      linkageP a b c d * (u0*coreRight0 a b c d v0 v1 v2 +
        u1*coreRight1 a b c d v0 v1 v2) +
      linkageG a b c d * coreProductCorrection a b u1 v1 v2 := by
  unfold coreRight0 coreRight1 linkageG linkageP coreProductCorrection
  ring

def seedP (r x0 x1 x2 x3 w : R) : R := linkageP (x0^2) (r*x1*x3) w (x2^2)
def seedG (r x0 x1 x2 x3 w : R) : R := linkageG (x0^2) (r*x1*x3) w (x2^2)

theorem seedG_expanded (r x0 x1 x2 x3 w : R) :
    seedG r x0 x1 x2 x3 w = x0^6-r^3*x1^3*x3^3+x2^6+w^3 := by
  unfold seedG linkageG
  ring

def leftCoeff0 (x0 x1 x2 x3 w : R) : Fin 3 → R :=
  ![-w ^ 2 * x1 * x3 + x1 ^ 2 * x2 ^ 4,
  -w * x1 ^ 4 + x0 ^ 2 * x2 ^ 4 + x1 * x2 ^ 3 * x3 ^ 2,
  -w ^ 2 * x0 * x3 + x1 ^ 4 * x3 ^ 2 + x2 ^ 2 * x3 ^ 4]

def leftCoeff1 (x0 x1 x2 x3 w : R) : Fin 3 → R :=
  ![x0 * x1 * x2 ^ 2 - x0 * x2 * x3 ^ 2,
  x3 ^ 4,
  x3 ^ 4]

def rightCoeff0 (x0 x1 x2 x3 w : R) : Fin 3 → R :=
  ![2 * w ^ 2 + 2 * w * x3 ^ 2,
  w * x0 * x2 + x0 ^ 2 * x2 ^ 2,
  x0 * x1 ^ 2 * x3 + x1 * x2 * x3 ^ 2 - x2 ^ 3 * x3 + x3 ^ 4]

def rightCoeff2 (x0 x1 x2 x3 w : R) : Fin 3 → R :=
  ![w + x3 ^ 2,
  w,
  0]

def rightCoeff3 (x0 x1 x2 x3 w : R) : Fin 3 → R :=
  ![0,
  x0 * x3,
  0]

def baseRow0 (r x0 x1 x2 x3 w : R) (j : Fin 3) : R :=
  coreRight0 (x0^2) (r*x1*x3) w (x2^2)
    (rightCoeff0 x0 x1 x2 x3 w j) (rightCoeff2 x0 x1 x2 x3 w j)
    (rightCoeff3 x0 x1 x2 x3 w j)

def baseRow1 (r x0 x1 x2 x3 w : R) (j : Fin 3) : R :=
  coreRight1 (x0^2) (r*x1*x3) w (x2^2)
    (rightCoeff0 x0 x1 x2 x3 w j) (rightCoeff2 x0 x1 x2 x3 w j)
    (rightCoeff3 x0 x1 x2 x3 w j)

def rightMinorQuotient (r x0 x1 x2 x3 w : R) (j k : Fin 3) : R :=
  coreMinorQuotient (x0^2) (r*x1*x3) w (x2^2)
    (rightCoeff0 x0 x1 x2 x3 w j) (rightCoeff2 x0 x1 x2 x3 w j)
    (rightCoeff3 x0 x1 x2 x3 w j)
    (rightCoeff0 x0 x1 x2 x3 w k) (rightCoeff2 x0 x1 x2 x3 w k)
    (rightCoeff3 x0 x1 x2 x3 w k)

def rightCrossQuotient (r x0 x1 x2 x3 w : R) : Fin 3 → R :=
  ![rightMinorQuotient r x0 x1 x2 x3 w 1 2,
    rightMinorQuotient r x0 x1 x2 x3 w 2 0,
    rightMinorQuotient r x0 x1 x2 x3 w 0 1]

theorem baseRow_minor (r x0 x1 x2 x3 w : R) (j k : Fin 3) :
    baseRow0 r x0 x1 x2 x3 w j * baseRow1 r x0 x1 x2 x3 w k -
      baseRow0 r x0 x1 x2 x3 w k * baseRow1 r x0 x1 x2 x3 w j =
      seedG r x0 x1 x2 x3 w * rightMinorQuotient r x0 x1 x2 x3 w j k := by
  exact coreRight_minor _ _ _ _ _ _ _ _ _ _

theorem baseRow_cross (r x0 x1 x2 x3 w : R) :
    cross (baseRow0 r x0 x1 x2 x3 w) (baseRow1 r x0 x1 x2 x3 w) =
      fun j => seedG r x0 x1 x2 x3 w * rightCrossQuotient r x0 x1 x2 x3 w j := by
  ext j
  fin_cases j
  · exact baseRow_minor r x0 x1 x2 x3 w 1 2
  · exact baseRow_minor r x0 x1 x2 x3 w 2 0
  · exact baseRow_minor r x0 x1 x2 x3 w 0 1

/-- The actual raw matrix, written without expanding its chosen section coefficients. -/
def rawMatrix (r x0 x1 x2 x3 w : R) : Matrix (Fin 3) (Fin 3) R :=
  fun i j => leftCoeff0 x0 x1 x2 x3 w i * baseRow0 r x0 x1 x2 x3 w j +
    leftCoeff1 x0 x1 x2 x3 w i * baseRow1 r x0 x1 x2 x3 w j

def rawCofactorQuotient (r x0 x1 x2 x3 w : R) : Matrix (Fin 3) (Fin 3) R :=
  fun i j => cross (leftCoeff0 x0 x1 x2 x3 w) (leftCoeff1 x0 x1 x2 x3 w) i *
    rightCrossQuotient r x0 x1 x2 x3 w j

def productCorrection (r x0 x1 x2 x3 w : R) (i j : Fin 3) : R :=
  coreProductCorrection (x0^2) (r*x1*x3) (leftCoeff1 x0 x1 x2 x3 w i)
    (rightCoeff2 x0 x1 x2 x3 w j) (rightCoeff3 x0 x1 x2 x3 w j)

def leftSection (r x0 x1 x2 x3 w : R) (i : Fin 3) : R :=
  leftCoeff0 x0 x1 x2 x3 w i * seedP r x0 x1 x2 x3 w +
    leftCoeff1 x0 x1 x2 x3 w i * ((x0^2)^3-(r*x1*x3)^3)

def rightSectionNumerator (r x0 x1 x2 x3 w : R) : Fin 3 → R :=
  baseRow0 r x0 x1 x2 x3 w

/-- Each raw entry is exactly the product built from the chosen linkage sections. -/
theorem rawMatrix_factorization (r x0 x1 x2 x3 w : R) :
    rawMatrix r x0 x1 x2 x3 w =
      fun i j => leftCoeff0 x0 x1 x2 x3 w i * baseRow0 r x0 x1 x2 x3 w j +
        leftCoeff1 x0 x1 x2 x3 w i * baseRow1 r x0 x1 x2 x3 w j := rfl

/-- The literal quotient polynomials agree with the smaller factored expressions. -/
theorem rawCofactorQuotient_factorization (r x0 x1 x2 x3 w : R) :
    rawCofactorQuotient r x0 x1 x2 x3 w =
      fun i j => cross (leftCoeff0 x0 x1 x2 x3 w) (leftCoeff1 x0 x1 x2 x3 w) i *
        rightCrossQuotient r x0 x1 x2 x3 w j := rfl

/-- All nine cofactors of the actual raw seed matrix are divisible by G, before h. -/
theorem rawMatrix_cofactor_identity (r x0 x1 x2 x3 w : R) :
    (rawMatrix r x0 x1 x2 x3 w).adjugate.transpose =
      fun i j => seedG r x0 x1 x2 x3 w * rawCofactorQuotient r x0 x1 x2 x3 w i j := by
  rw [rawMatrix_factorization, cofactors_rank_two, rawCofactorQuotient_factorization]
  ext i j
  rw [baseRow_cross]
  ring

/-- The actual selected L and M sections multiply to p times the raw entry modulo G. -/
theorem selected_product_identity (r x0 x1 x2 x3 w : R) (i j : Fin 3) :
    leftSection r x0 x1 x2 x3 w i * rightSectionNumerator r x0 x1 x2 x3 w j =
      seedP r x0 x1 x2 x3 w * rawMatrix r x0 x1 x2 x3 w i j +
      seedG r x0 x1 x2 x3 w * productCorrection r x0 x1 x2 x3 w i j := by
  exact core_product _ _ _ _ _ _ _ _ _

/-- The chosen first M section is the original Gamma4 numerator. -/
theorem first_rightSection (r x0 x1 x2 x3 w : R) :
    rightSectionNumerator r x0 x1 x2 x3 w 0 =
      (w+x3^2) * (2*w*seedP r x0 x1 x2 x3 w +
        (x0^2)^2*(r*x1*x3)-w*(x2^2)^2) := by
  simp only [rightSectionNumerator, baseRow0, coreRight0, rightCoeff0, rightCoeff2,
    rightCoeff3, seedP, linkageP, Matrix.cons_val_zero]
  ring

end CycleQ2SegreSeed

#print axioms CycleQ2SegreSeed.linkage_pairing
#print axioms CycleQ2SegreSeed.rawMatrix_cofactor_identity
#print axioms CycleQ2SegreSeed.selected_product_identity
#print axioms CycleQ2SegreSeed.first_rightSection

set_option linter.unusedSimpArgs true
end
end


/- Component: continuation_2/AffineWeightedTransfer.lean -/
section
/-!
# Actual paired-sign relative residue transfer

All coordinates and derivations below belong to the already constructed
function field of the protected chart X0=1.  The parameter is lambda=Y2/X2
and the weighted coordinate is X2^2.  An explicit change of divergence
coefficients transfers a three-direction relative primitive to the actual
four-direction affine residue equation.  No relative primitive, geometric
family, Leray statement, or cohomological vanishing is assumed to exist.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace CycleQ2AffineWeightedTransfer

open MvPolynomial HodgeComputer CycleQ2AffineClearing CycleQ2AffineHypersurface
  CycleQ2AffineResidueClosure CycleQ2AffineDifferentials HoldoutConstruction
open scoped BigOperators

abbrev K := AffineFunctionField
abbrev Poly := AmbientPoly 4

local instance coefficientCharZero : CharZero K :=
  charZero_of_injective_algebraMap (algebraMap ℂ K).injective
local instance coefficientIntAlgebra : Algebra ℤ K := Ring.toIntAlgebra _

/-- Coordinates are (X1,X2,Y0,Y1,Y2) in the protected X0=1 chart. -/
def z (i : Fin 5) : K := affineMap (X i)
def u : K := z 1
def v : K := z 4
def parameter : K := v / u

def E (i : Fin 4) : Derivation ℂ K K := complexTangent i

@[simp] theorem E_apply (i : Fin 4) (x : K) : E i x = affineTangent i x := rfl

@[simp] theorem E_u (i : Fin 4) : E i u = if i = 0 then 1 else 0 := by
  simpa [E, u, z, eq_comm] using affineTangent_coordinate i 0

@[simp] theorem E_v (i : Fin 4) : E i v = if i = 3 then 1 else 0 := by
  simpa [E, v, z, eq_comm] using affineTangent_coordinate i 3

/-- Nonvanishing is proved in the actual quotient field by differentiating
an alleged zero coordinate; no additional divisibility premise is used. -/
theorem u_ne_zero : u ≠ 0 := by
  intro hu
  have h : E 0 u = 1 := by simp only [E_u, if_true]
  rw [hu, map_zero] at h
  exact zero_ne_one h

@[simp] theorem E_two (i : Fin 4) : E i (2 : K) = 0 := (E i).map_natCast 2

@[simp] theorem E_parameter_zero : E 0 parameter = -parameter / u := by
  rw [parameter, Derivation.leibniz_div]
  simp only [E_u, E_v, Fin.reduceEq, if_false, if_true, smul_eq_mul, mul_zero,
    zero_sub, mul_one]
  ring

@[simp] theorem E_parameter_one : E 1 parameter = 0 := by
  rw [parameter, Derivation.leibniz_div]
  simp only [E_u, E_v, Fin.reduceEq, if_false, smul_eq_mul, mul_zero, sub_self]

@[simp] theorem E_parameter_two : E 2 parameter = 0 := by
  rw [parameter, Derivation.leibniz_div]
  simp only [E_u, E_v, Fin.reduceEq, if_false, smul_eq_mul, mul_zero, sub_self]

@[simp] theorem E_parameter_three : E 3 parameter = 1 / u := by
  rw [parameter, Derivation.leibniz_div]
  simp only [E_u, E_v, Fin.reduceEq, if_false, if_true, smul_eq_mul, mul_zero,
    sub_zero, mul_one]
  field_simp [u_ne_zero]

/-- Actual relative derivations in the Y0, Y1, X2^2 directions. -/
def relativeDerivation : Fin 3 → Derivation ℂ K K :=
  ![E 1, E 2, (2 * u)⁻¹ • (E 0 + parameter • E 3)]

@[simp] theorem relativeDerivation_zero (x : K) : relativeDerivation 0 x = E 1 x := rfl
@[simp] theorem relativeDerivation_one (x : K) : relativeDerivation 1 x = E 2 x := rfl
@[simp] theorem relativeDerivation_two (x : K) :
    relativeDerivation 2 x = (E 0 x + parameter * E 3 x) / (2 * u) := by
  change ((2 * u)⁻¹ • (E 0 + parameter • E 3)) x = _
  simp only [Derivation.smul_apply, Derivation.add_apply, smul_eq_mul]
  ring

/-- Every relative direction fixes the actual quotient parameter. -/
theorem relative_parameter (j : Fin 3) : relativeDerivation j parameter = 0 := by
  fin_cases j
  · exact E_parameter_one
  · exact E_parameter_two
  · change relativeDerivation 2 parameter = 0
    rw [relativeDerivation_two, E_parameter_zero, E_parameter_three]
    ring

/-- The radial relative direction has zero ordinary coordinate divergence. -/
theorem radial_divergence : E 0 (1 / (2 * u)) + E 3 (parameter / (2 * u)) = 0 := by
  simp only [Derivation.leibniz_div, Derivation.leibniz, Derivation.map_one_eq_zero,
    E_two, E_u, E_parameter_three, smul_eq_mul, Fin.reduceEq, if_false,
    if_true, mul_zero, add_zero, mul_one]
  field_simp [u_ne_zero]
  ring

/-- The actual weighted numerator before multiplying by lambda. -/
def weightedSource : Poly := X 0 ^ 2 * X 1 ^ 4 * X 2 ^ 2 * X 3 ^ 2

theorem parameter_mul_u : parameter * u = v := by
  unfold parameter
  exact div_mul_cancel₀ v u_ne_zero

/-- The actual polynomial equation in the weighted coordinate X2^2 and
the quotient parameter Y2/X2. -/
def weightedEquation (a c d w l : K) : K :=
  1 + a ^ 6 + c ^ 6 + d ^ 6 + (1 + l ^ 6) * w ^ 3 +
    (a * c * d) / 2 + (l * a ^ 3 * d * w) / 2 + (l * c * w ^ 2) / 2

theorem weighted_equation : weightedEquation (z 0) (z 2) (z 3) (u ^ 2) parameter = 0 := by
  have hhalf : affineMap (C (1 / 2 : ℂ)) = (1 / 2 : K) := by
    change (algebraMap ℂ K) (1 / 2 : ℂ) = (1 / 2 : K)
    simp only [map_div₀, map_one, map_ofNat]
  have hf := (congrArg affineMap CycleQ2AffineGeometry.affineF_formula).symm.trans
    affineMap_F
  simp only [map_add, map_mul, map_pow, map_one, hhalf] at hf
  change 1 + z 0 ^ 6 + u ^ 6 + z 2 ^ 6 + z 3 ^ 6 + v ^ 6 +
    (1 / 2 : K) * (z 0 * z 2 * z 3 + z 0 ^ 3 * u * z 3 * v +
      u ^ 3 * v * z 2) = 0 at hf
  rw [← parameter_mul_u] at hf
  calc
    weightedEquation (z 0) (z 2) (z 3) (u ^ 2) parameter =
      1 + z 0 ^ 6 + u ^ 6 + z 2 ^ 6 + z 3 ^ 6 + (parameter * u) ^ 6 +
        (1 / 2 : K) * (z 0 * z 2 * z 3 + z 0 ^ 3 * u * z 3 * (parameter * u) +
          u ^ 3 * (parameter * u) * z 2) := by
            unfold weightedEquation
            ring
    _ = 0 := hf

/-- The actual weighted numerator is a²c²d²w². -/
theorem weighted_source_value :
    affineMap weightedSource = z 0 ^ 2 * z 2 ^ 2 * z 3 ^ 2 * (u ^ 2) ^ 2 := by
  simp only [weightedSource, map_mul, map_pow]
  change z 0 ^ 2 * u ^ 4 * z 2 ^ 2 * z 3 ^ 2 = _
  ring

theorem affineA_formula : affineA =
    X 0 ^ 2 * X 1 ^ 3 * X 2 ^ 2 * X 3 ^ 2 * X 4 := by
  have h1 : Fin.cases (1 : Poly) X (1 : Fin 6) = X (0 : Fin 5) := rfl
  have h2 : Fin.cases (1 : Poly) X (2 : Fin 6) = X (1 : Fin 5) := rfl
  have h3 : Fin.cases (1 : Poly) X (3 : Fin 6) = X (2 : Fin 5) := rfl
  have h4 : Fin.cases (1 : Poly) X (4 : Fin 6) = X (3 : Fin 5) := rfl
  have h5 : Fin.cases (1 : Poly) X (5 : Fin 6) = X (4 : Fin 5) := rfl
  simp [affineA, CycleQ2AffineChart.dehomogenize, HodgeSubmission.A, h1, h2, h3, h4, h5]

theorem source_product : affineA * X 1 = weightedSource * X 4 := by
  rw [affineA_formula]
  unfold weightedSource
  ring

private theorem normal_partial_product_coordinate (P : Poly) (j : Fin 5) (hj : j ≠ 0) :
    pderiv 0 (P * X j) = pderiv 0 P * X j := by
  simp [pderiv_X, hj, mul_comm]

theorem source_first_jet_product : pderiv 0 affineA * X 1 = pderiv 0 weightedSource * X 4 := by
  have h := congrArg (pderiv (0 : Fin 5)) source_product
  simpa only [normal_partial_product_coordinate _ _ (by decide : (1 : Fin 5) ≠ 0),
    normal_partial_product_coordinate _ _ (by decide : (4 : Fin 5) ≠ 0)] using h

theorem source_second_jet_product :
    pderiv 0 (pderiv 0 affineA) * X 1 = pderiv 0 (pderiv 0 weightedSource) * X 4 := by
  have h := congrArg (pderiv (0 : Fin 5)) source_first_jet_product
  simpa only [normal_partial_product_coordinate _ _ (by decide : (1 : Fin 5) ≠ 0),
    normal_partial_product_coordinate _ _ (by decide : (4 : Fin 5) ≠ 0)] using h

private theorem mapped_source_ratio (P Q : Poly) (h : P * X 1 = Q * X 4) :
    affineMap P = parameter * affineMap Q := by
  have hm := congrArg affineMap h
  simp only [map_mul] at hm
  change affineMap P * u = affineMap Q * v at hm
  rw [(eq_div_iff u_ne_zero).mpr hm]
  unfold parameter
  ring

theorem affine_source_ratio : affineMap affineA = parameter * affineMap weightedSource :=
  mapped_source_ratio _ _ source_product

/-- The literal normal jets prove the normal-source scaling for the exact
protected numerator; the normal variable is not changed. -/
theorem normal_source_ratio :
    affineNormalSource affineA = parameter * affineNormalSource weightedSource := by
  have h0 := mapped_source_ratio _ _ source_product
  have h1 := mapped_source_ratio _ _ source_first_jet_product
  have h2 := mapped_source_ratio _ _ source_second_jet_product
  simp only [affineNormalSource, SplitHigherResidue.normalSourceTwo, h0, h1, h2]
  ring

/-- The actual coefficient transfer in the (X2,Y0,Y1,Y2) directions. -/
def transferVector (w : Fin 3 → K) : Fin 4 → K :=
  ![parameter * w 2 / (2 * u), parameter * w 0, parameter * w 1,
    parameter ^ 2 * w 2 / (2 * u)]

def normalDensity : K := affineMap (pderiv 0 affineF)

def relativeResidueExpression (w : Fin 3 → K) : K :=
  affineNormalSource weightedSource +
    (∑ j, relativeDerivation j (w j)) -
    (∑ j, w j * relativeDerivation j normalDensity) / normalDensity

private theorem sum_three (f : Fin 3 → K) : (∑ i, f i) = f 0 + f 1 + f 2 := by
  have h : (∑ i, f i) = f 0 + (f 1 + f 2) := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    rfl
  rw [h]
  ring

private theorem sum_four (f : Fin 4 → K) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 := by
  have h : (∑ i, f i) = f 0 + (f 1 + (f 2 + f 3)) := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    rfl
  rw [h]
  ring

@[simp] theorem transferVector_zero (w : Fin 3 → K) :
    transferVector w 0 = parameter * w 2 / (2 * u) := rfl
@[simp] theorem transferVector_one (w : Fin 3 → K) :
    transferVector w 1 = parameter * w 0 := rfl
@[simp] theorem transferVector_two (w : Fin 3 → K) :
    transferVector w 2 = parameter * w 1 := rfl
@[simp] theorem transferVector_three (w : Fin 3 → K) :
    transferVector w 3 = parameter ^ 2 * w 2 / (2 * u) := rfl

/-- The product-rule terms cancel because the radial direction has zero
divergence and fixes lambda. All derivatives are the actual field operators. -/
theorem transferred_divergence (w : Fin 3 → K) :
    (∑ i, E i (transferVector w i)) =
      parameter * ∑ j, relativeDerivation j (w j) := by
  rw [sum_four, sum_three]
  simp only [transferVector_zero, transferVector_one, transferVector_two,
    transferVector_three, relativeDerivation_zero,
    relativeDerivation_one, relativeDerivation_two, Derivation.leibniz_div,
    Derivation.leibniz, Derivation.leibniz_pow, E_parameter_zero, E_parameter_one,
    E_parameter_two, E_parameter_three, E_two, E_u, smul_eq_mul, nsmul_eq_mul,
    Fin.reduceEq, if_true, if_false, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp [u_ne_zero]
  ring

/-- The logarithmic normal-density term undergoes the same transfer. -/
theorem transferred_density_term (w : Fin 3 → K) :
    (∑ i, transferVector w i * E i normalDensity) =
      parameter * ∑ j, w j * relativeDerivation j normalDensity := by
  rw [sum_four, sum_three]
  simp only [transferVector_zero, transferVector_one, transferVector_two,
    transferVector_three, relativeDerivation_zero,
    relativeDerivation_one, relativeDerivation_two]
  ring

/-- Exact actual-field relative-PDE transfer for the protected source. -/
theorem affine_residue_transfer (w : Fin 3 → K) :
    affineResidueExpression affineA (transferVector w) =
      parameter * relativeResidueExpression w := by
  unfold affineResidueExpression residueDivergence fieldDivergence
  rw [normal_source_ratio]
  change parameter * affineNormalSource weightedSource +
    ((∑ i, E i (transferVector w i)) -
      (∑ i, transferVector w i * E i normalDensity) / normalDensity) = _
  rw [transferred_divergence, transferred_density_term]
  unfold relativeResidueExpression
  ring

/-- An actual relative three-direction primitive suffices for the original
protected certificate. Its existence is not asserted in this module. -/
theorem protected_certificate_of_relative_primitive
    (h : ∃ w : Fin 3 → K, relativeResidueExpression w = 0) :
    HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A := by
  obtain ⟨w, hw⟩ := h
  apply protected_certificate_of_affine_residue_primitive
  refine ⟨transferVector w, ?_⟩
  rw [affine_residue_transfer, hw, mul_zero]

end CycleQ2AffineWeightedTransfer

#print axioms CycleQ2AffineWeightedTransfer.u_ne_zero
#print axioms CycleQ2AffineWeightedTransfer.normal_source_ratio
#print axioms CycleQ2AffineWeightedTransfer.weighted_equation
#print axioms CycleQ2AffineWeightedTransfer.affine_residue_transfer
#print axioms CycleQ2AffineWeightedTransfer.protected_certificate_of_relative_primitive
end
end


namespace CycleQ2FormalInputs

/-- A precise equivalent form of the unchanged protected goal. This theorem
does not prove the existential on either side. In particular, it makes no
assumption that a supporting equation or primitive has already been found. -/
theorem protected_certificate_iff_square_primitive :
    HodgeComputer.HasCertificate
        HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A ↔
      ∃ (e : ℕ) (S : HodgeComputer.AmbientPoly 5)
          (N : Fin 6 → HodgeComputer.AmbientPoly 5),
        S.IsHomogeneous e ∧ ¬ HodgeSubmission.F ∣ S ∧
        (∀ i, HodgeComputer.Homogeneous (N i) (2 * (e : ℤ) + 7)) ∧
        CycleQ2Bridge.LocalizedEquation
          HodgeSubmission.F HodgeSubmission.A 2 (S ^ 2) N := by
  exact CycleQ2Bridge.sextic_q2_hasCertificate_iff_square_primitive
    HodgeSubmission.F HodgeSubmission.A
    CycleQ2ExactIrreducible.protected_F_irreducible
    CycleQ2Workspace.originalF_homogeneous
    (HodgeComputer.Homogeneous.of_isHomogeneous
      CycleQ2Workspace.originalA_homogeneous)

end CycleQ2FormalInputs

#print axioms CycleQ2FormalInputs.protected_certificate_iff_square_primitive
