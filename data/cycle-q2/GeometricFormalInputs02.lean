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
import Proposal.GeometricFormalInputs01

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


