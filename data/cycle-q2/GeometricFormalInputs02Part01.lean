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
import Proposal.GeometricFormalInputs01Part04

/-! Source partition of GeometricFormalInputs.lean. See solution.md for verification status. -/

set_option Elab.async false

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


