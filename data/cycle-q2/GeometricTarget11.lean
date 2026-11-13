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
import HodgeComputer.Constructions.HoldoutCover.FiniteTrace
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.Fintype.Card
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.Data.Finsupp.MonomialOrder.DegLex
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.FunProp
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.CharP.Basic
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Data.Finsupp.Encodable
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Tactic.Abel
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Data.List.OfFn
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Data.Fintype.Fin
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.Module
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.Localization.AtPrime.Basic
import HodgeComputer.Constructions.HoldoutCover.FiniteDifferentials
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Proposal.GeometricFormalInputs
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Proposal.GeometricTarget10

/-! Source partition of GeometricTarget.lean. See solution.md for verification status. -/

set_option Elab.async false

/- Component: continuation_3/CurveRestrictionModularLeft.lean -/
section
set_option maxRecDepth 100000

set_option maxHeartbeats 0

set_option Elab.async false

set_option backward.isDefEq.respectTransparency false

set_option linter.unusedSimpArgs false

namespace CycleQ2CurveRestrictionModularChecks

open MvPolynomial CycleQ2CurveRestriction CycleQ2SparseModularPolynomial

open CycleQ2CurveRestrictionReflection CycleQ2CurveRestrictionMatrixCheck

open CycleQ2CurveRestrictionModularData

noncomputable section

variable {R : Type*} [CommRing R] [CharP R 109]

theorem left_quadric_value : value (R:=R) leftQuadric = quadric .left (57 : R) := by

  have hc : CharP (CurvePoly R) 109 := inferInstance

  simp only [leftQuadric, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg, quadric, cubic]

  apply sub_eq_zero.mp

  ring_nf <;> reduce_mod_char!

theorem left_cubic_value : value (R:=R) leftCubic = cubic .left (57 : R) 33 := by

  have hc : CharP (CurvePoly R) 109 := inferInstance

  simp only [leftCubic, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg, quadric, cubic]

  apply sub_eq_zero.mp

  ring_nf <;> reduce_mod_char!

private theorem left_normal_good_0 : goodPolynomial .left 10 leftNormal0=true := by decide +kernel

private theorem left_normal_check_0 :

    checkZero (residual leftInput0 leftNormal0 leftQ0 leftH0 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_0 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,0,0,10,0)) = value leftNormal0 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,0,0,10,0)) = value leftInput0 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput0, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput0 leftNormal0 leftQ0 leftH0

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_0 left_normal_check_0

private theorem left_normal_good_1 : goodPolynomial .left 10 leftNormal1=true := by decide +kernel

private theorem left_normal_check_1 :

    checkZero (residual leftInput1 leftNormal1 leftQ1 leftH1 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_1 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,0,3,7,0)) = value leftNormal1 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,0,3,7,0)) = value leftInput1 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput1, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput1 leftNormal1 leftQ1 leftH1

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_1 left_normal_check_1

private theorem left_normal_good_2 : goodPolynomial .left 10 leftNormal2=true := by decide +kernel

private theorem left_normal_check_2 :

    checkZero (residual leftInput2 leftNormal2 leftQ2 leftH2 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_2 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,0,6,4,0)) = value leftNormal2 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,0,6,4,0)) = value leftInput2 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput2, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput2 leftNormal2 leftQ2 leftH2

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_2 left_normal_check_2

private theorem left_normal_good_3 : goodPolynomial .left 10 leftNormal3=true := by decide +kernel

private theorem left_normal_check_3 :

    checkZero (residual leftInput3 leftNormal3 leftQ3 leftH3 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_3 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,0,9,1,0)) = value leftNormal3 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,0,9,1,0)) = value leftInput3 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput3, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput3 leftNormal3 leftQ3 leftH3

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_3 left_normal_check_3

private theorem left_normal_good_4 : goodPolynomial .left 10 leftNormal4=true := by decide +kernel

private theorem left_normal_check_4 :

    checkZero (residual leftInput4 leftNormal4 leftQ4 leftH4 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_4 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,1,1,8,0)) = value leftNormal4 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,1,1,8,0)) = value leftInput4 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput4, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput4 leftNormal4 leftQ4 leftH4

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_4 left_normal_check_4

private theorem left_normal_good_5 : goodPolynomial .left 10 leftNormal5=true := by decide +kernel

private theorem left_normal_check_5 :

    checkZero (residual leftInput5 leftNormal5 leftQ5 leftH5 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_5 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,1,4,5,0)) = value leftNormal5 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,1,4,5,0)) = value leftInput5 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput5, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput5 leftNormal5 leftQ5 leftH5

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_5 left_normal_check_5

private theorem left_normal_good_6 : goodPolynomial .left 10 leftNormal6=true := by decide +kernel

private theorem left_normal_check_6 :

    checkZero (residual leftInput6 leftNormal6 leftQ6 leftH6 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_6 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,1,7,2,0)) = value leftNormal6 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,1,7,2,0)) = value leftInput6 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput6, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput6 leftNormal6 leftQ6 leftH6

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_6 left_normal_check_6

private theorem left_normal_good_7 : goodPolynomial .left 10 leftNormal7=true := by decide +kernel

private theorem left_normal_check_7 :

    checkZero (residual leftInput7 leftNormal7 leftQ7 leftH7 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_7 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,2,2,6,0)) = value leftNormal7 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,2,2,6,0)) = value leftInput7 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput7, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput7 leftNormal7 leftQ7 leftH7

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_7 left_normal_check_7

private theorem left_normal_good_8 : goodPolynomial .left 10 leftNormal8=true := by decide +kernel

private theorem left_normal_check_8 :

    checkZero (residual leftInput8 leftNormal8 leftQ8 leftH8 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_8 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,2,5,3,0)) = value leftNormal8 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,2,5,3,0)) = value leftInput8 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput8, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput8 leftNormal8 leftQ8 leftH8

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_8 left_normal_check_8

private theorem left_normal_good_9 : goodPolynomial .left 10 leftNormal9=true := by decide +kernel

private theorem left_normal_check_9 :

    checkZero (residual leftInput9 leftNormal9 leftQ9 leftH9 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_9 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,2,8,0,0)) = value leftNormal9 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,2,8,0,0)) = value leftInput9 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput9, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput9 leftNormal9 leftQ9 leftH9

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_9 left_normal_check_9

private theorem left_normal_good_10 : goodPolynomial .left 10 leftNormal10=true := by decide +kernel

private theorem left_normal_check_10 :

    checkZero (residual leftInput10 leftNormal10 leftQ10 leftH10 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_10 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,3,0,7,0)) = value leftNormal10 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,3,0,7,0)) = value leftInput10 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput10, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput10 leftNormal10 leftQ10 leftH10

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_10 left_normal_check_10

private theorem left_normal_good_11 : goodPolynomial .left 10 leftNormal11=true := by decide +kernel

private theorem left_normal_check_11 :

    checkZero (residual leftInput11 leftNormal11 leftQ11 leftH11 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_11 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,3,3,4,0)) = value leftNormal11 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,3,3,4,0)) = value leftInput11 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput11, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput11 leftNormal11 leftQ11 leftH11

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_11 left_normal_check_11

private theorem left_normal_good_12 : goodPolynomial .left 10 leftNormal12=true := by decide +kernel

private theorem left_normal_check_12 :

    checkZero (residual leftInput12 leftNormal12 leftQ12 leftH12 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_12 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,3,6,1,0)) = value leftNormal12 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,3,6,1,0)) = value leftInput12 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput12, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput12 leftNormal12 leftQ12 leftH12

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_12 left_normal_check_12

private theorem left_normal_good_13 : goodPolynomial .left 10 leftNormal13=true := by decide +kernel

private theorem left_normal_check_13 :

    checkZero (residual leftInput13 leftNormal13 leftQ13 leftH13 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_13 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,4,1,5,0)) = value leftNormal13 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,4,1,5,0)) = value leftInput13 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput13, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput13 leftNormal13 leftQ13 leftH13

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_13 left_normal_check_13

private theorem left_normal_good_14 : goodPolynomial .left 10 leftNormal14=true := by decide +kernel

private theorem left_normal_check_14 :

    checkZero (residual leftInput14 leftNormal14 leftQ14 leftH14 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_14 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,4,4,2,0)) = value leftNormal14 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,4,4,2,0)) = value leftInput14 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput14, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput14 leftNormal14 leftQ14 leftH14

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_14 left_normal_check_14

private theorem left_normal_good_15 : goodPolynomial .left 10 leftNormal15=true := by decide +kernel

private theorem left_normal_check_15 :

    checkZero (residual leftInput15 leftNormal15 leftQ15 leftH15 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_15 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,5,2,3,0)) = value leftNormal15 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,5,2,3,0)) = value leftInput15 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput15, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput15 leftNormal15 leftQ15 leftH15

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_15 left_normal_check_15

private theorem left_normal_good_16 : goodPolynomial .left 10 leftNormal16=true := by decide +kernel

private theorem left_normal_check_16 :

    checkZero (residual leftInput16 leftNormal16 leftQ16 leftH16 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_16 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,5,5,0,0)) = value leftNormal16 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,5,5,0,0)) = value leftInput16 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput16, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput16 leftNormal16 leftQ16 leftH16

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_16 left_normal_check_16

private theorem left_normal_good_17 : goodPolynomial .left 10 leftNormal17=true := by decide +kernel

private theorem left_normal_check_17 :

    checkZero (residual leftInput17 leftNormal17 leftQ17 leftH17 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_17 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,6,0,4,0)) = value leftNormal17 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,6,0,4,0)) = value leftInput17 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput17, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput17 leftNormal17 leftQ17 leftH17

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_17 left_normal_check_17

private theorem left_normal_good_18 : goodPolynomial .left 10 leftNormal18=true := by decide +kernel

private theorem left_normal_check_18 :

    checkZero (residual leftInput18 leftNormal18 leftQ18 leftH18 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_18 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,6,3,1,0)) = value leftNormal18 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,6,3,1,0)) = value leftInput18 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput18, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput18 leftNormal18 leftQ18 leftH18

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_18 left_normal_check_18

private theorem left_normal_good_19 : goodPolynomial .left 10 leftNormal19=true := by decide +kernel

private theorem left_normal_check_19 :

    checkZero (residual leftInput19 leftNormal19 leftQ19 leftH19 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_19 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,7,1,2,0)) = value leftNormal19 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,7,1,2,0)) = value leftInput19 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput19, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput19 leftNormal19 leftQ19 leftH19

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_19 left_normal_check_19

private theorem left_normal_good_20 : goodPolynomial .left 10 leftNormal20=true := by decide +kernel

private theorem left_normal_check_20 :

    checkZero (residual leftInput20 leftNormal20 leftQ20 leftH20 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_20 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,8,2,0,0)) = value leftNormal20 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,8,2,0,0)) = value leftInput20 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput20, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput20 leftNormal20 leftQ20 leftH20

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_20 left_normal_check_20

private theorem left_normal_good_21 : goodPolynomial .left 10 leftNormal21=true := by decide +kernel

private theorem left_normal_check_21 :

    checkZero (residual leftInput21 leftNormal21 leftQ21 leftH21 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_21 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,9,0,1,0)) = value leftNormal21 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,9,0,1,0)) = value leftInput21 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput21, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput21 leftNormal21 leftQ21 leftH21

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_21 left_normal_check_21

private theorem left_normal_good_22 : goodPolynomial .left 10 leftNormal22=true := by decide +kernel

private theorem left_normal_check_22 :

    checkZero (residual leftInput22 leftNormal22 leftQ22 leftH22 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_22 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,0,0,8,1)) = value leftNormal22 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,0,0,8,1)) = value leftInput22 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput22, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput22 leftNormal22 leftQ22 leftH22

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_22 left_normal_check_22

private theorem left_normal_good_23 : goodPolynomial .left 10 leftNormal23=true := by decide +kernel

private theorem left_normal_check_23 :

    checkZero (residual leftInput23 leftNormal23 leftQ23 leftH23 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_23 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,0,3,5,1)) = value leftNormal23 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,0,3,5,1)) = value leftInput23 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput23, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput23 leftNormal23 leftQ23 leftH23

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_23 left_normal_check_23

private theorem left_normal_good_24 : goodPolynomial .left 10 leftNormal24=true := by decide +kernel

private theorem left_normal_check_24 :

    checkZero (residual leftInput24 leftNormal24 leftQ24 leftH24 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_24 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,0,6,2,1)) = value leftNormal24 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,0,6,2,1)) = value leftInput24 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput24, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput24 leftNormal24 leftQ24 leftH24

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_24 left_normal_check_24

private theorem left_normal_good_25 : goodPolynomial .left 10 leftNormal25=true := by decide +kernel

private theorem left_normal_check_25 :

    checkZero (residual leftInput25 leftNormal25 leftQ25 leftH25 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_25 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,1,1,6,1)) = value leftNormal25 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,1,1,6,1)) = value leftInput25 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput25, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput25 leftNormal25 leftQ25 leftH25

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_25 left_normal_check_25

private theorem left_normal_good_26 : goodPolynomial .left 10 leftNormal26=true := by decide +kernel

private theorem left_normal_check_26 :

    checkZero (residual leftInput26 leftNormal26 leftQ26 leftH26 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_26 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,1,4,3,1)) = value leftNormal26 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,1,4,3,1)) = value leftInput26 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput26, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput26 leftNormal26 leftQ26 leftH26

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_26 left_normal_check_26

private theorem left_normal_good_27 : goodPolynomial .left 10 leftNormal27=true := by decide +kernel

private theorem left_normal_check_27 :

    checkZero (residual leftInput27 leftNormal27 leftQ27 leftH27 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_27 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,1,7,0,1)) = value leftNormal27 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,1,7,0,1)) = value leftInput27 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput27, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput27 leftNormal27 leftQ27 leftH27

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_27 left_normal_check_27

private theorem left_normal_good_28 : goodPolynomial .left 10 leftNormal28=true := by decide +kernel

private theorem left_normal_check_28 :

    checkZero (residual leftInput28 leftNormal28 leftQ28 leftH28 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_28 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,2,2,4,1)) = value leftNormal28 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,2,2,4,1)) = value leftInput28 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput28, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput28 leftNormal28 leftQ28 leftH28

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_28 left_normal_check_28

private theorem left_normal_good_29 : goodPolynomial .left 10 leftNormal29=true := by decide +kernel

private theorem left_normal_check_29 :

    checkZero (residual leftInput29 leftNormal29 leftQ29 leftH29 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_29 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,2,5,1,1)) = value leftNormal29 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,2,5,1,1)) = value leftInput29 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput29, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput29 leftNormal29 leftQ29 leftH29

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_29 left_normal_check_29

private theorem left_normal_good_30 : goodPolynomial .left 10 leftNormal30=true := by decide +kernel

private theorem left_normal_check_30 :

    checkZero (residual leftInput30 leftNormal30 leftQ30 leftH30 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_30 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,3,0,5,1)) = value leftNormal30 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,3,0,5,1)) = value leftInput30 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput30, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput30 leftNormal30 leftQ30 leftH30

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_30 left_normal_check_30

private theorem left_normal_good_31 : goodPolynomial .left 10 leftNormal31=true := by decide +kernel

private theorem left_normal_check_31 :

    checkZero (residual leftInput31 leftNormal31 leftQ31 leftH31 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_31 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,3,3,2,1)) = value leftNormal31 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,3,3,2,1)) = value leftInput31 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput31, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput31 leftNormal31 leftQ31 leftH31

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_31 left_normal_check_31

private theorem left_normal_good_32 : goodPolynomial .left 10 leftNormal32=true := by decide +kernel

private theorem left_normal_check_32 :

    checkZero (residual leftInput32 leftNormal32 leftQ32 leftH32 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_32 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,4,1,3,1)) = value leftNormal32 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,4,1,3,1)) = value leftInput32 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput32, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput32 leftNormal32 leftQ32 leftH32

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_32 left_normal_check_32

private theorem left_normal_good_33 : goodPolynomial .left 10 leftNormal33=true := by decide +kernel

private theorem left_normal_check_33 :

    checkZero (residual leftInput33 leftNormal33 leftQ33 leftH33 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_33 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,4,4,0,1)) = value leftNormal33 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,4,4,0,1)) = value leftInput33 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput33, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput33 leftNormal33 leftQ33 leftH33

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_33 left_normal_check_33

private theorem left_normal_good_34 : goodPolynomial .left 10 leftNormal34=true := by decide +kernel

private theorem left_normal_check_34 :

    checkZero (residual leftInput34 leftNormal34 leftQ34 leftH34 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_34 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,5,2,1,1)) = value leftNormal34 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,5,2,1,1)) = value leftInput34 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput34, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput34 leftNormal34 leftQ34 leftH34

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_34 left_normal_check_34

private theorem left_normal_good_35 : goodPolynomial .left 10 leftNormal35=true := by decide +kernel

private theorem left_normal_check_35 :

    checkZero (residual leftInput35 leftNormal35 leftQ35 leftH35 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_35 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,6,0,2,1)) = value leftNormal35 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,6,0,2,1)) = value leftInput35 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput35, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput35 leftNormal35 leftQ35 leftH35

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_35 left_normal_check_35

private theorem left_normal_good_36 : goodPolynomial .left 10 leftNormal36=true := by decide +kernel

private theorem left_normal_check_36 :

    checkZero (residual leftInput36 leftNormal36 leftQ36 leftH36 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_36 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,7,1,0,1)) = value leftNormal36 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,7,1,0,1)) = value leftInput36 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput36, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput36 leftNormal36 leftQ36 leftH36

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_36 left_normal_check_36

private theorem left_normal_good_37 : goodPolynomial .left 10 leftNormal37=true := by decide +kernel

private theorem left_normal_check_37 :

    checkZero (residual leftInput37 leftNormal37 leftQ37 leftH37 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_37 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,0,0,6,2)) = value leftNormal37 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,0,0,6,2)) = value leftInput37 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput37, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput37 leftNormal37 leftQ37 leftH37

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_37 left_normal_check_37

private theorem left_normal_good_38 : goodPolynomial .left 10 leftNormal38=true := by decide +kernel

private theorem left_normal_check_38 :

    checkZero (residual leftInput38 leftNormal38 leftQ38 leftH38 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_38 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,0,3,3,2)) = value leftNormal38 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,0,3,3,2)) = value leftInput38 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput38, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput38 leftNormal38 leftQ38 leftH38

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_38 left_normal_check_38

private theorem left_normal_good_39 : goodPolynomial .left 10 leftNormal39=true := by decide +kernel

private theorem left_normal_check_39 :

    checkZero (residual leftInput39 leftNormal39 leftQ39 leftH39 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_39 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,0,6,0,2)) = value leftNormal39 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,0,6,0,2)) = value leftInput39 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput39, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput39 leftNormal39 leftQ39 leftH39

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_39 left_normal_check_39

private theorem left_normal_good_40 : goodPolynomial .left 10 leftNormal40=true := by decide +kernel

private theorem left_normal_check_40 :

    checkZero (residual leftInput40 leftNormal40 leftQ40 leftH40 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_40 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,1,1,4,2)) = value leftNormal40 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,1,1,4,2)) = value leftInput40 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput40, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput40 leftNormal40 leftQ40 leftH40

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_40 left_normal_check_40

private theorem left_normal_good_41 : goodPolynomial .left 10 leftNormal41=true := by decide +kernel

private theorem left_normal_check_41 :

    checkZero (residual leftInput41 leftNormal41 leftQ41 leftH41 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_41 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,1,4,1,2)) = value leftNormal41 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,1,4,1,2)) = value leftInput41 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput41, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput41 leftNormal41 leftQ41 leftH41

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_41 left_normal_check_41

private theorem left_normal_good_42 : goodPolynomial .left 10 leftNormal42=true := by decide +kernel

private theorem left_normal_check_42 :

    checkZero (residual leftInput42 leftNormal42 leftQ42 leftH42 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_42 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,2,2,2,2)) = value leftNormal42 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,2,2,2,2)) = value leftInput42 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput42, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput42 leftNormal42 leftQ42 leftH42

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_42 left_normal_check_42

private theorem left_normal_good_43 : goodPolynomial .left 10 leftNormal43=true := by decide +kernel

private theorem left_normal_check_43 :

    checkZero (residual leftInput43 leftNormal43 leftQ43 leftH43 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_43 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,3,3,0,2)) = value leftNormal43 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,3,3,0,2)) = value leftInput43 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput43, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput43 leftNormal43 leftQ43 leftH43

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_43 left_normal_check_43

private theorem left_normal_good_44 : goodPolynomial .left 10 leftNormal44=true := by decide +kernel

private theorem left_normal_check_44 :

    checkZero (residual leftInput44 leftNormal44 leftQ44 leftH44 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_44 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (0,4,1,1,2)) = value leftNormal44 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (0,4,1,1,2)) = value leftInput44 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput44, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput44 leftNormal44 leftQ44 leftH44

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_44 left_normal_check_44

private theorem left_normal_good_45 : goodPolynomial .left 10 leftNormal45=true := by decide +kernel

private theorem left_normal_check_45 :

    checkZero (residual leftInput45 leftNormal45 leftQ45 leftH45 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_45 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (1,0,1,8,0)) = value leftNormal45 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (1,0,1,8,0)) = value leftInput45 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput45, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput45 leftNormal45 leftQ45 leftH45

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_45 left_normal_check_45

private theorem left_normal_good_46 : goodPolynomial .left 10 leftNormal46=true := by decide +kernel

private theorem left_normal_check_46 :

    checkZero (residual leftInput46 leftNormal46 leftQ46 leftH46 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_46 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (1,0,4,5,0)) = value leftNormal46 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (1,0,4,5,0)) = value leftInput46 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput46, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput46 leftNormal46 leftQ46 leftH46

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_46 left_normal_check_46

private theorem left_normal_good_47 : goodPolynomial .left 10 leftNormal47=true := by decide +kernel

private theorem left_normal_check_47 :

    checkZero (residual leftInput47 leftNormal47 leftQ47 leftH47 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_47 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (1,0,7,2,0)) = value leftNormal47 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (1,0,7,2,0)) = value leftInput47 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput47, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput47 leftNormal47 leftQ47 leftH47

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_47 left_normal_check_47

private theorem left_normal_good_48 : goodPolynomial .left 10 leftNormal48=true := by decide +kernel

private theorem left_normal_check_48 :

    checkZero (residual leftInput48 leftNormal48 leftQ48 leftH48 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_48 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (1,1,2,6,0)) = value leftNormal48 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (1,1,2,6,0)) = value leftInput48 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput48, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput48 leftNormal48 leftQ48 leftH48

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_48 left_normal_check_48

private theorem left_normal_good_49 : goodPolynomial .left 10 leftNormal49=true := by decide +kernel

private theorem left_normal_check_49 :

    checkZero (residual leftInput49 leftNormal49 leftQ49 leftH49 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_49 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (1,1,5,3,0)) = value leftNormal49 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (1,1,5,3,0)) = value leftInput49 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput49, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput49 leftNormal49 leftQ49 leftH49

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_49 left_normal_check_49

private theorem left_normal_good_50 : goodPolynomial .left 10 leftNormal50=true := by decide +kernel

private theorem left_normal_check_50 :

    checkZero (residual leftInput50 leftNormal50 leftQ50 leftH50 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_50 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (1,1,8,0,0)) = value leftNormal50 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (1,1,8,0,0)) = value leftInput50 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput50, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput50 leftNormal50 leftQ50 leftH50

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_50 left_normal_check_50

private theorem left_normal_good_51 : goodPolynomial .left 10 leftNormal51=true := by decide +kernel

private theorem left_normal_check_51 :

    checkZero (residual leftInput51 leftNormal51 leftQ51 leftH51 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_51 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (1,2,0,7,0)) = value leftNormal51 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (1,2,0,7,0)) = value leftInput51 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput51, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput51 leftNormal51 leftQ51 leftH51

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_51 left_normal_check_51

private theorem left_normal_good_52 : goodPolynomial .left 10 leftNormal52=true := by decide +kernel

private theorem left_normal_check_52 :

    checkZero (residual leftInput52 leftNormal52 leftQ52 leftH52 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_52 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (1,2,3,4,0)) = value leftNormal52 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (1,2,3,4,0)) = value leftInput52 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput52, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput52 leftNormal52 leftQ52 leftH52

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_52 left_normal_check_52

private theorem left_normal_good_53 : goodPolynomial .left 10 leftNormal53=true := by decide +kernel

private theorem left_normal_check_53 :

    checkZero (residual leftInput53 leftNormal53 leftQ53 leftH53 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_53 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (1,3,1,5,0)) = value leftNormal53 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (1,3,1,5,0)) = value leftInput53 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput53, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput53 leftNormal53 leftQ53 leftH53

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_53 left_normal_check_53

private theorem left_normal_good_54 : goodPolynomial .left 10 leftNormal54=true := by decide +kernel

private theorem left_normal_check_54 :

    checkZero (residual leftInput54 leftNormal54 leftQ54 leftH54 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_54 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (1,5,0,4,0)) = value leftNormal54 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (1,5,0,4,0)) = value leftInput54 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput54, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput54 leftNormal54 leftQ54 leftH54

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_54 left_normal_check_54

private theorem left_normal_good_55 : goodPolynomial .left 10 leftNormal55=true := by decide +kernel

private theorem left_normal_check_55 :

    checkZero (residual leftInput55 leftNormal55 leftQ55 leftH55 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_55 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (1,6,1,2,0)) = value leftNormal55 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (1,6,1,2,0)) = value leftInput55 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput55, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput55 leftNormal55 leftQ55 leftH55

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_55 left_normal_check_55

private theorem left_normal_good_56 : goodPolynomial .left 10 leftNormal56=true := by decide +kernel

private theorem left_normal_check_56 :

    checkZero (residual leftInput56 leftNormal56 leftQ56 leftH56 leftQuadric leftCubic)=true := by

  decide +kernel

theorem left_column_56 [Nontrivial R] :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (1,0,1,6,1)) = value leftNormal56 := by

  have hinput : substitution .left (57 : R) (sourceMonomial (1,0,1,6,1)) = value leftInput56 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, leftInput56, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .left 57 33 10 leftInput56 leftNormal56 leftQ56 leftH56

    leftQuadric leftCubic left_quadric_value left_cubic_value

    left_normal_good_56 left_normal_check_56

theorem left_columns [Nontrivial R] (j : Fin 57) :

    restrictionNormal .left (57 : R) 33 (sourceMonomial (leftSources j)) = value (leftNormals j) := by

  fin_cases j

  · exact left_column_0

  · exact left_column_1

  · exact left_column_2

  · exact left_column_3

  · exact left_column_4

  · exact left_column_5

  · exact left_column_6

  · exact left_column_7

  · exact left_column_8

  · exact left_column_9

  · exact left_column_10

  · exact left_column_11

  · exact left_column_12

  · exact left_column_13

  · exact left_column_14

  · exact left_column_15

  · exact left_column_16

  · exact left_column_17

  · exact left_column_18

  · exact left_column_19

  · exact left_column_20

  · exact left_column_21

  · exact left_column_22

  · exact left_column_23

  · exact left_column_24

  · exact left_column_25

  · exact left_column_26

  · exact left_column_27

  · exact left_column_28

  · exact left_column_29

  · exact left_column_30

  · exact left_column_31

  · exact left_column_32

  · exact left_column_33

  · exact left_column_34

  · exact left_column_35

  · exact left_column_36

  · exact left_column_37

  · exact left_column_38

  · exact left_column_39

  · exact left_column_40

  · exact left_column_41

  · exact left_column_42

  · exact left_column_43

  · exact left_column_44

  · exact left_column_45

  · exact left_column_46

  · exact left_column_47

  · exact left_column_48

  · exact left_column_49

  · exact left_column_50

  · exact left_column_51

  · exact left_column_52

  · exact left_column_53

  · exact left_column_54

  · exact left_column_55

  · exact left_column_56

private theorem left_coefficient_row_0 : ∀ j : Fin 57,

    coefficient (leftRows 0) (leftNormals j) = (leftMinorRows 0).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_1 : ∀ j : Fin 57,

    coefficient (leftRows 1) (leftNormals j) = (leftMinorRows 1).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_2 : ∀ j : Fin 57,

    coefficient (leftRows 2) (leftNormals j) = (leftMinorRows 2).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_3 : ∀ j : Fin 57,

    coefficient (leftRows 3) (leftNormals j) = (leftMinorRows 3).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_4 : ∀ j : Fin 57,

    coefficient (leftRows 4) (leftNormals j) = (leftMinorRows 4).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_5 : ∀ j : Fin 57,

    coefficient (leftRows 5) (leftNormals j) = (leftMinorRows 5).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_6 : ∀ j : Fin 57,

    coefficient (leftRows 6) (leftNormals j) = (leftMinorRows 6).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_7 : ∀ j : Fin 57,

    coefficient (leftRows 7) (leftNormals j) = (leftMinorRows 7).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_8 : ∀ j : Fin 57,

    coefficient (leftRows 8) (leftNormals j) = (leftMinorRows 8).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_9 : ∀ j : Fin 57,

    coefficient (leftRows 9) (leftNormals j) = (leftMinorRows 9).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_10 : ∀ j : Fin 57,

    coefficient (leftRows 10) (leftNormals j) = (leftMinorRows 10).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_11 : ∀ j : Fin 57,

    coefficient (leftRows 11) (leftNormals j) = (leftMinorRows 11).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_12 : ∀ j : Fin 57,

    coefficient (leftRows 12) (leftNormals j) = (leftMinorRows 12).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_13 : ∀ j : Fin 57,

    coefficient (leftRows 13) (leftNormals j) = (leftMinorRows 13).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_14 : ∀ j : Fin 57,

    coefficient (leftRows 14) (leftNormals j) = (leftMinorRows 14).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_15 : ∀ j : Fin 57,

    coefficient (leftRows 15) (leftNormals j) = (leftMinorRows 15).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_16 : ∀ j : Fin 57,

    coefficient (leftRows 16) (leftNormals j) = (leftMinorRows 16).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_17 : ∀ j : Fin 57,

    coefficient (leftRows 17) (leftNormals j) = (leftMinorRows 17).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_18 : ∀ j : Fin 57,

    coefficient (leftRows 18) (leftNormals j) = (leftMinorRows 18).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_19 : ∀ j : Fin 57,

    coefficient (leftRows 19) (leftNormals j) = (leftMinorRows 19).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_20 : ∀ j : Fin 57,

    coefficient (leftRows 20) (leftNormals j) = (leftMinorRows 20).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_21 : ∀ j : Fin 57,

    coefficient (leftRows 21) (leftNormals j) = (leftMinorRows 21).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_22 : ∀ j : Fin 57,

    coefficient (leftRows 22) (leftNormals j) = (leftMinorRows 22).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_23 : ∀ j : Fin 57,

    coefficient (leftRows 23) (leftNormals j) = (leftMinorRows 23).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_24 : ∀ j : Fin 57,

    coefficient (leftRows 24) (leftNormals j) = (leftMinorRows 24).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_25 : ∀ j : Fin 57,

    coefficient (leftRows 25) (leftNormals j) = (leftMinorRows 25).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_26 : ∀ j : Fin 57,

    coefficient (leftRows 26) (leftNormals j) = (leftMinorRows 26).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_27 : ∀ j : Fin 57,

    coefficient (leftRows 27) (leftNormals j) = (leftMinorRows 27).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_28 : ∀ j : Fin 57,

    coefficient (leftRows 28) (leftNormals j) = (leftMinorRows 28).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_29 : ∀ j : Fin 57,

    coefficient (leftRows 29) (leftNormals j) = (leftMinorRows 29).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_30 : ∀ j : Fin 57,

    coefficient (leftRows 30) (leftNormals j) = (leftMinorRows 30).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_31 : ∀ j : Fin 57,

    coefficient (leftRows 31) (leftNormals j) = (leftMinorRows 31).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_32 : ∀ j : Fin 57,

    coefficient (leftRows 32) (leftNormals j) = (leftMinorRows 32).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_33 : ∀ j : Fin 57,

    coefficient (leftRows 33) (leftNormals j) = (leftMinorRows 33).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_34 : ∀ j : Fin 57,

    coefficient (leftRows 34) (leftNormals j) = (leftMinorRows 34).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_35 : ∀ j : Fin 57,

    coefficient (leftRows 35) (leftNormals j) = (leftMinorRows 35).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_36 : ∀ j : Fin 57,

    coefficient (leftRows 36) (leftNormals j) = (leftMinorRows 36).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_37 : ∀ j : Fin 57,

    coefficient (leftRows 37) (leftNormals j) = (leftMinorRows 37).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_38 : ∀ j : Fin 57,

    coefficient (leftRows 38) (leftNormals j) = (leftMinorRows 38).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_39 : ∀ j : Fin 57,

    coefficient (leftRows 39) (leftNormals j) = (leftMinorRows 39).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_40 : ∀ j : Fin 57,

    coefficient (leftRows 40) (leftNormals j) = (leftMinorRows 40).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_41 : ∀ j : Fin 57,

    coefficient (leftRows 41) (leftNormals j) = (leftMinorRows 41).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_42 : ∀ j : Fin 57,

    coefficient (leftRows 42) (leftNormals j) = (leftMinorRows 42).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_43 : ∀ j : Fin 57,

    coefficient (leftRows 43) (leftNormals j) = (leftMinorRows 43).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_44 : ∀ j : Fin 57,

    coefficient (leftRows 44) (leftNormals j) = (leftMinorRows 44).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_45 : ∀ j : Fin 57,

    coefficient (leftRows 45) (leftNormals j) = (leftMinorRows 45).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_46 : ∀ j : Fin 57,

    coefficient (leftRows 46) (leftNormals j) = (leftMinorRows 46).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_47 : ∀ j : Fin 57,

    coefficient (leftRows 47) (leftNormals j) = (leftMinorRows 47).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_48 : ∀ j : Fin 57,

    coefficient (leftRows 48) (leftNormals j) = (leftMinorRows 48).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_49 : ∀ j : Fin 57,

    coefficient (leftRows 49) (leftNormals j) = (leftMinorRows 49).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_50 : ∀ j : Fin 57,

    coefficient (leftRows 50) (leftNormals j) = (leftMinorRows 50).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_51 : ∀ j : Fin 57,

    coefficient (leftRows 51) (leftNormals j) = (leftMinorRows 51).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_52 : ∀ j : Fin 57,

    coefficient (leftRows 52) (leftNormals j) = (leftMinorRows 52).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_53 : ∀ j : Fin 57,

    coefficient (leftRows 53) (leftNormals j) = (leftMinorRows 53).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_54 : ∀ j : Fin 57,

    coefficient (leftRows 54) (leftNormals j) = (leftMinorRows 54).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_55 : ∀ j : Fin 57,

    coefficient (leftRows 55) (leftNormals j) = (leftMinorRows 55).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_56 : ∀ j : Fin 57,

    coefficient (leftRows 56) (leftNormals j) = (leftMinorRows 56).getD j.val 0 := by

  decide +kernel

theorem left_coefficient_table (i j : Fin 57) :

    coefficient (leftRows i) (leftNormals j) = (leftMinorRows i).getD j.val 0 := by

  fin_cases i

  · exact left_coefficient_row_0 j

  · exact left_coefficient_row_1 j

  · exact left_coefficient_row_2 j

  · exact left_coefficient_row_3 j

  · exact left_coefficient_row_4 j

  · exact left_coefficient_row_5 j

  · exact left_coefficient_row_6 j

  · exact left_coefficient_row_7 j

  · exact left_coefficient_row_8 j

  · exact left_coefficient_row_9 j

  · exact left_coefficient_row_10 j

  · exact left_coefficient_row_11 j

  · exact left_coefficient_row_12 j

  · exact left_coefficient_row_13 j

  · exact left_coefficient_row_14 j

  · exact left_coefficient_row_15 j

  · exact left_coefficient_row_16 j

  · exact left_coefficient_row_17 j

  · exact left_coefficient_row_18 j

  · exact left_coefficient_row_19 j

  · exact left_coefficient_row_20 j

  · exact left_coefficient_row_21 j

  · exact left_coefficient_row_22 j

  · exact left_coefficient_row_23 j

  · exact left_coefficient_row_24 j

  · exact left_coefficient_row_25 j

  · exact left_coefficient_row_26 j

  · exact left_coefficient_row_27 j

  · exact left_coefficient_row_28 j

  · exact left_coefficient_row_29 j

  · exact left_coefficient_row_30 j

  · exact left_coefficient_row_31 j

  · exact left_coefficient_row_32 j

  · exact left_coefficient_row_33 j

  · exact left_coefficient_row_34 j

  · exact left_coefficient_row_35 j

  · exact left_coefficient_row_36 j

  · exact left_coefficient_row_37 j

  · exact left_coefficient_row_38 j

  · exact left_coefficient_row_39 j

  · exact left_coefficient_row_40 j

  · exact left_coefficient_row_41 j

  · exact left_coefficient_row_42 j

  · exact left_coefficient_row_43 j

  · exact left_coefficient_row_44 j

  · exact left_coefficient_row_45 j

  · exact left_coefficient_row_46 j

  · exact left_coefficient_row_47 j

  · exact left_coefficient_row_48 j

  · exact left_coefficient_row_49 j

  · exact left_coefficient_row_50 j

  · exact left_coefficient_row_51 j

  · exact left_coefficient_row_52 j

  · exact left_coefficient_row_53 j

  · exact left_coefficient_row_54 j

  · exact left_coefficient_row_55 j

  · exact left_coefficient_row_56 j

theorem left_matrix_coefficients [Nontrivial R] (i j : Fin 57) :

    matrixCoefficient .left (57 : R) 33 (leftRows i) (leftSources j) =

      ((leftMinorRows i).getD j.val 0 : R) := by

  rw [matrixCoefficient,left_columns,value_coefficient,left_coefficient_table]

private theorem left_inverse_row_0 : ∀ j : Fin 57,

    dotMod (leftMinorRows 0) (leftInverseColumns j) = if (0 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_1 : ∀ j : Fin 57,

    dotMod (leftMinorRows 1) (leftInverseColumns j) = if (1 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_2 : ∀ j : Fin 57,

    dotMod (leftMinorRows 2) (leftInverseColumns j) = if (2 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_3 : ∀ j : Fin 57,

    dotMod (leftMinorRows 3) (leftInverseColumns j) = if (3 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_4 : ∀ j : Fin 57,

    dotMod (leftMinorRows 4) (leftInverseColumns j) = if (4 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_5 : ∀ j : Fin 57,

    dotMod (leftMinorRows 5) (leftInverseColumns j) = if (5 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_6 : ∀ j : Fin 57,

    dotMod (leftMinorRows 6) (leftInverseColumns j) = if (6 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_7 : ∀ j : Fin 57,

    dotMod (leftMinorRows 7) (leftInverseColumns j) = if (7 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_8 : ∀ j : Fin 57,

    dotMod (leftMinorRows 8) (leftInverseColumns j) = if (8 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_9 : ∀ j : Fin 57,

    dotMod (leftMinorRows 9) (leftInverseColumns j) = if (9 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_10 : ∀ j : Fin 57,

    dotMod (leftMinorRows 10) (leftInverseColumns j) = if (10 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_11 : ∀ j : Fin 57,

    dotMod (leftMinorRows 11) (leftInverseColumns j) = if (11 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_12 : ∀ j : Fin 57,

    dotMod (leftMinorRows 12) (leftInverseColumns j) = if (12 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_13 : ∀ j : Fin 57,

    dotMod (leftMinorRows 13) (leftInverseColumns j) = if (13 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_14 : ∀ j : Fin 57,

    dotMod (leftMinorRows 14) (leftInverseColumns j) = if (14 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_15 : ∀ j : Fin 57,

    dotMod (leftMinorRows 15) (leftInverseColumns j) = if (15 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_16 : ∀ j : Fin 57,

    dotMod (leftMinorRows 16) (leftInverseColumns j) = if (16 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_17 : ∀ j : Fin 57,

    dotMod (leftMinorRows 17) (leftInverseColumns j) = if (17 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_18 : ∀ j : Fin 57,

    dotMod (leftMinorRows 18) (leftInverseColumns j) = if (18 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_19 : ∀ j : Fin 57,

    dotMod (leftMinorRows 19) (leftInverseColumns j) = if (19 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_20 : ∀ j : Fin 57,

    dotMod (leftMinorRows 20) (leftInverseColumns j) = if (20 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_21 : ∀ j : Fin 57,

    dotMod (leftMinorRows 21) (leftInverseColumns j) = if (21 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_22 : ∀ j : Fin 57,

    dotMod (leftMinorRows 22) (leftInverseColumns j) = if (22 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_23 : ∀ j : Fin 57,

    dotMod (leftMinorRows 23) (leftInverseColumns j) = if (23 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_24 : ∀ j : Fin 57,

    dotMod (leftMinorRows 24) (leftInverseColumns j) = if (24 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_25 : ∀ j : Fin 57,

    dotMod (leftMinorRows 25) (leftInverseColumns j) = if (25 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_26 : ∀ j : Fin 57,

    dotMod (leftMinorRows 26) (leftInverseColumns j) = if (26 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_27 : ∀ j : Fin 57,

    dotMod (leftMinorRows 27) (leftInverseColumns j) = if (27 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_28 : ∀ j : Fin 57,

    dotMod (leftMinorRows 28) (leftInverseColumns j) = if (28 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_29 : ∀ j : Fin 57,

    dotMod (leftMinorRows 29) (leftInverseColumns j) = if (29 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_30 : ∀ j : Fin 57,

    dotMod (leftMinorRows 30) (leftInverseColumns j) = if (30 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_31 : ∀ j : Fin 57,

    dotMod (leftMinorRows 31) (leftInverseColumns j) = if (31 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_32 : ∀ j : Fin 57,

    dotMod (leftMinorRows 32) (leftInverseColumns j) = if (32 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_33 : ∀ j : Fin 57,

    dotMod (leftMinorRows 33) (leftInverseColumns j) = if (33 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_34 : ∀ j : Fin 57,

    dotMod (leftMinorRows 34) (leftInverseColumns j) = if (34 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_35 : ∀ j : Fin 57,

    dotMod (leftMinorRows 35) (leftInverseColumns j) = if (35 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_36 : ∀ j : Fin 57,

    dotMod (leftMinorRows 36) (leftInverseColumns j) = if (36 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_37 : ∀ j : Fin 57,

    dotMod (leftMinorRows 37) (leftInverseColumns j) = if (37 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_38 : ∀ j : Fin 57,

    dotMod (leftMinorRows 38) (leftInverseColumns j) = if (38 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_39 : ∀ j : Fin 57,

    dotMod (leftMinorRows 39) (leftInverseColumns j) = if (39 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_40 : ∀ j : Fin 57,

    dotMod (leftMinorRows 40) (leftInverseColumns j) = if (40 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_41 : ∀ j : Fin 57,

    dotMod (leftMinorRows 41) (leftInverseColumns j) = if (41 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_42 : ∀ j : Fin 57,

    dotMod (leftMinorRows 42) (leftInverseColumns j) = if (42 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_43 : ∀ j : Fin 57,

    dotMod (leftMinorRows 43) (leftInverseColumns j) = if (43 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_44 : ∀ j : Fin 57,

    dotMod (leftMinorRows 44) (leftInverseColumns j) = if (44 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_45 : ∀ j : Fin 57,

    dotMod (leftMinorRows 45) (leftInverseColumns j) = if (45 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_46 : ∀ j : Fin 57,

    dotMod (leftMinorRows 46) (leftInverseColumns j) = if (46 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_47 : ∀ j : Fin 57,

    dotMod (leftMinorRows 47) (leftInverseColumns j) = if (47 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_48 : ∀ j : Fin 57,

    dotMod (leftMinorRows 48) (leftInverseColumns j) = if (48 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_49 : ∀ j : Fin 57,

    dotMod (leftMinorRows 49) (leftInverseColumns j) = if (49 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_50 : ∀ j : Fin 57,

    dotMod (leftMinorRows 50) (leftInverseColumns j) = if (50 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_51 : ∀ j : Fin 57,

    dotMod (leftMinorRows 51) (leftInverseColumns j) = if (51 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_52 : ∀ j : Fin 57,

    dotMod (leftMinorRows 52) (leftInverseColumns j) = if (52 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_53 : ∀ j : Fin 57,

    dotMod (leftMinorRows 53) (leftInverseColumns j) = if (53 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_54 : ∀ j : Fin 57,

    dotMod (leftMinorRows 54) (leftInverseColumns j) = if (54 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_55 : ∀ j : Fin 57,

    dotMod (leftMinorRows 55) (leftInverseColumns j) = if (55 : Fin 57)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_56 : ∀ j : Fin 57,

    dotMod (leftMinorRows 56) (leftInverseColumns j) = if (56 : Fin 57)=j then 1 else 0 := by

  decide +kernel

theorem left_inverse_checks (i j : Fin 57) :

    dotMod (leftMinorRows i) (leftInverseColumns j) = if i=j then 1 else 0 := by

  fin_cases i

  · exact left_inverse_row_0 j

  · exact left_inverse_row_1 j

  · exact left_inverse_row_2 j

  · exact left_inverse_row_3 j

  · exact left_inverse_row_4 j

  · exact left_inverse_row_5 j

  · exact left_inverse_row_6 j

  · exact left_inverse_row_7 j

  · exact left_inverse_row_8 j

  · exact left_inverse_row_9 j

  · exact left_inverse_row_10 j

  · exact left_inverse_row_11 j

  · exact left_inverse_row_12 j

  · exact left_inverse_row_13 j

  · exact left_inverse_row_14 j

  · exact left_inverse_row_15 j

  · exact left_inverse_row_16 j

  · exact left_inverse_row_17 j

  · exact left_inverse_row_18 j

  · exact left_inverse_row_19 j

  · exact left_inverse_row_20 j

  · exact left_inverse_row_21 j

  · exact left_inverse_row_22 j

  · exact left_inverse_row_23 j

  · exact left_inverse_row_24 j

  · exact left_inverse_row_25 j

  · exact left_inverse_row_26 j

  · exact left_inverse_row_27 j

  · exact left_inverse_row_28 j

  · exact left_inverse_row_29 j

  · exact left_inverse_row_30 j

  · exact left_inverse_row_31 j

  · exact left_inverse_row_32 j

  · exact left_inverse_row_33 j

  · exact left_inverse_row_34 j

  · exact left_inverse_row_35 j

  · exact left_inverse_row_36 j

  · exact left_inverse_row_37 j

  · exact left_inverse_row_38 j

  · exact left_inverse_row_39 j

  · exact left_inverse_row_40 j

  · exact left_inverse_row_41 j

  · exact left_inverse_row_42 j

  · exact left_inverse_row_43 j

  · exact left_inverse_row_44 j

  · exact left_inverse_row_45 j

  · exact left_inverse_row_46 j

  · exact left_inverse_row_47 j

  · exact left_inverse_row_48 j

  · exact left_inverse_row_49 j

  · exact left_inverse_row_50 j

  · exact left_inverse_row_51 j

  · exact left_inverse_row_52 j

  · exact left_inverse_row_53 j

  · exact left_inverse_row_54 j

  · exact left_inverse_row_55 j

  · exact left_inverse_row_56 j

theorem left_minor_det_ne_zero [Nontrivial R] :

    Matrix.det (fun i j : Fin 57 => matrixCoefficient .left (57 : R) 33 (leftRows i) (leftSources j)) ≠ 0 := by

  have hm : (fun i j : Fin 57 => matrixCoefficient .left (57 : R) 33 (leftRows i) (leftSources j)) =

      matrixOfRows leftMinorRows := by ext i j; exact left_matrix_coefficients i j

  rw [hm]

  apply determinant_ne_zero_of_dot_checks leftMinorRows leftInverseColumns

  · decide +kernel

  · decide +kernel

  · exact left_inverse_checks

end

end CycleQ2CurveRestrictionModularChecks

#print axioms CycleQ2CurveRestrictionModularChecks.left_minor_det_ne_zero
end


/- End of continuation partition. -/


/- Uncompiled continuation: GeometricBridgeAlgebra.lean (2026-11-12). -/
section Q2UncompiledHiggsBridge

/-!
# Self-adjoint projectors on the actual Fermat Jacobian component

This file supplies an algebraic step in the reconstructed geometric argument.
The existing finite theorem `CycleQ2FermatHiggs.compatible_projector_trivial`
concerns matrices. Here it is applied to endomorphisms of the actual
`CycleQ2FermatJacobian.gradedPiece 6 1`, using the actual socle triple-product
pairings and the already constructed monomial basis.

In particular, the compatibility premise below is an equality in the actual
Fermat derivative quotient, not a premise asserting geometric support or
existence of a residue primitive. Interpreting a geometric polarized sub-VHS
projector as one of these endomorphisms remains a separate geometric theorem.

Written against the recorded project sources and the pinned mathlib source
at 0df444a360eaa60ab8c11dca51a86af692955474. Development compilation status
is recorded in solution.md.
-/

set_option autoImplicit false

noncomputable section

namespace CycleQ2GeometricBridgeAlgebra

open CycleQ2FermatJacobian

open scoped BigOperators

/-- The actual degree-six character-one component of the Fermat quotient. -/
abbrev InvariantHodgeModel := gradedPiece 6 1

/-- The actual degree-six character-zero deformation component. -/
abbrev InvariantTangentModel := gradedPiece 6 0

/-- The triple-product form on the actual quotient, linear in both inputs.
The names of the models indicate their intended geometric interpretation;
no Hodge-theoretic comparison is assumed or asserted in this definition. -/
def actualTracePairing (t : InvariantTangentModel) :
    InvariantHodgeModel →ₗ[ℂ] InvariantHodgeModel →ₗ[ℂ] ℂ where
  toFun u :=
    { toFun := fun v =>
        socleTrace ((u : JacobianRing) * (v : JacobianRing) * (t : JacobianRing))
      map_add' := by
        intro v w
        simp [mul_add, add_mul]
      map_smul' := by
        intro c v
        simp [mul_smul_comm, smul_mul_assoc] }
  map_add' := by
    intro u v
    ext w
    simp [add_mul]
  map_smul' := by
    intro c u
    ext v
    simp [smul_mul_assoc]

@[simp] theorem actualTracePairing_apply (t : InvariantTangentModel)
    (u v : InvariantHodgeModel) :
    actualTracePairing t u v =
      socleTrace ((u : JacobianRing) * (v : JacobianRing) * (t : JacobianRing)) :=
  rfl

theorem actualTracePairing_symmetric (t : InvariantTangentModel)
    (u v : InvariantHodgeModel) :
    actualTracePairing t u v = actualTracePairing t v u := by
  change socleTrace ((u : JacobianRing) * (v : JacobianRing) * (t : JacobianRing)) =
    socleTrace ((v : JacobianRing) * (u : JacobianRing) * (t : JacobianRing))
  rw [mul_comm (u : JacobianRing) (v : JacobianRing)]

@[simp] theorem actualTracePairing_flip_apply (t : InvariantTangentModel)
    (u v : InvariantHodgeModel) :
    (actualTracePairing t).flip v u = actualTracePairing t u v :=
  rfl

/-- Its matrices are the already proved finite Fermat Higgs matrices. -/
theorem actualTracePairing_basis (m : Fin 35) (i j : Fin 33) :
    actualTracePairing (degreeSixCharacterZeroBasis m)
      (degreeSixCharacterOneBasis i) (degreeSixCharacterOneBasis j) =
        CycleQ2FermatHiggs.higgsMatrix ℂ m i j :=
  actual_component_trace_matrix m i j

/-- The matrix of an actual endomorphism, with the established quotient basis. -/
def actualEndomorphismMatrix
    (P : Module.End ℂ InvariantHodgeModel) : Matrix (Fin 33) (Fin 33) ℂ :=
  LinearMap.toMatrixAlgEquiv degreeSixCharacterOneBasis P

theorem actualEndomorphismMatrix_apply
    (P : Module.End ℂ InvariantHodgeModel) (i j : Fin 33) :
    actualEndomorphismMatrix P i j =
      degreeSixCharacterOneBasis.repr (P (degreeSixCharacterOneBasis j)) i :=
  LinearMap.toMatrixAlgEquiv_apply degreeSixCharacterOneBasis P i j

theorem actualTracePairing_expand_left (t : InvariantTangentModel)
    (u v : InvariantHodgeModel) :
    actualTracePairing t u v =
      ∑ i : Fin 33, degreeSixCharacterOneBasis.repr u i *
        actualTracePairing t (degreeSixCharacterOneBasis i) v := by
  have h := congrArg ((actualTracePairing t).flip v)
    (degreeSixCharacterOneBasis.sum_repr u)
  simpa only [map_sum, map_smul, actualTracePairing_flip_apply, smul_eq_mul]
    using h.symm

theorem actualTracePairing_expand_right (t : InvariantTangentModel)
    (u v : InvariantHodgeModel) :
    actualTracePairing t u v =
      ∑ i : Fin 33, degreeSixCharacterOneBasis.repr v i *
        actualTracePairing t u (degreeSixCharacterOneBasis i) := by
  have h := congrArg (actualTracePairing t u)
    (degreeSixCharacterOneBasis.sum_repr v)
  simpa only [map_sum, map_smul, smul_eq_mul] using h.symm

/-- The left side of the finite commutant equation is evaluation of the
actual trace pairing after applying the endomorphism to its first input. -/
theorem transpose_mul_higgs_eq_actualTracePairing
    (P : Module.End ℂ InvariantHodgeModel) (m : Fin 35) (i j : Fin 33) :
    ((actualEndomorphismMatrix P).transpose *
        CycleQ2FermatHiggs.higgsMatrix ℂ m) i j =
      actualTracePairing (degreeSixCharacterZeroBasis m)
        (P (degreeSixCharacterOneBasis i)) (degreeSixCharacterOneBasis j) := by
  rw [actualTracePairing_expand_left]
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    actualEndomorphismMatrix_apply, actualTracePairing_basis]

/-- The right side of the finite commutant equation is evaluation after
applying the actual endomorphism to the second input. -/
theorem higgs_mul_eq_actualTracePairing
    (P : Module.End ℂ InvariantHodgeModel) (m : Fin 35) (i j : Fin 33) :
    (CycleQ2FermatHiggs.higgsMatrix ℂ m * actualEndomorphismMatrix P) i j =
      actualTracePairing (degreeSixCharacterZeroBasis m)
        (degreeSixCharacterOneBasis i) (P (degreeSixCharacterOneBasis j)) := by
  rw [actualTracePairing_expand_right]
  simp only [Matrix.mul_apply, actualEndomorphismMatrix_apply,
    actualTracePairing_basis]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

/-- Self-adjointness for the genuine triple-product pairings implies the
finite matrix compatibility equations, with no geometric comparison premise. -/
theorem higgs_equations_of_actual_trace_selfAdjoint
    (P : Module.End ℂ InvariantHodgeModel)
    (hP : ∀ (t : InvariantTangentModel) (u v : InvariantHodgeModel),
      actualTracePairing t (P u) v = actualTracePairing t u (P v)) :
    ∀ m : Fin 35,
      (actualEndomorphismMatrix P).transpose *
          CycleQ2FermatHiggs.higgsMatrix ℂ m =
        CycleQ2FermatHiggs.higgsMatrix ℂ m * actualEndomorphismMatrix P := by
  intro m
  ext i j
  rw [transpose_mul_higgs_eq_actualTracePairing,
    higgs_mul_eq_actualTracePairing]
  exact hP (degreeSixCharacterZeroBasis m)
    (degreeSixCharacterOneBasis i) (degreeSixCharacterOneBasis j)

/-- An idempotent on the actual Fermat component that is self-adjoint for
every actual trace pairing is zero or the identity. This is the algebraic
projector conclusion needed at the Fermat point in the geometric Higgs
argument. It does not assert existence of a geometric subvariation projector. -/
theorem actual_trace_selfAdjoint_projector_trivial
    (P : Module.End ℂ InvariantHodgeModel)
    (hP : ∀ (t : InvariantTangentModel) (u v : InvariantHodgeModel),
      actualTracePairing t (P u) v = actualTracePairing t u (P v))
    (hIdempotent : P * P = P) : P = 0 ∨ P = 1 := by
  let e := LinearMap.toMatrixAlgEquiv degreeSixCharacterOneBasis
  have hMatrix : actualEndomorphismMatrix P * actualEndomorphismMatrix P =
      actualEndomorphismMatrix P := by
    change e P * e P = e P
    rw [← map_mul, hIdempotent]
  rcases CycleQ2FermatHiggs.compatible_projector_trivial
      (actualEndomorphismMatrix P)
      (higgs_equations_of_actual_trace_selfAdjoint P hP) hMatrix with hZero | hOne
  · left
    apply e.injective
    simpa only [actualEndomorphismMatrix, e, map_zero] using hZero
  · right
    apply e.injective
    simpa only [actualEndomorphismMatrix, e, map_one] using hOne

/-- Consequently no proper nonzero image can occur for such a projector. -/
theorem actual_trace_selfAdjoint_projector_range
    (P : Module.End ℂ InvariantHodgeModel)
    (hP : ∀ (t : InvariantTangentModel) (u v : InvariantHodgeModel),
      actualTracePairing t (P u) v = actualTracePairing t u (P v))
    (hIdempotent : P * P = P) :
    LinearMap.range P = ⊥ ∨ LinearMap.range P = ⊤ := by
  rcases actual_trace_selfAdjoint_projector_trivial P hP hIdempotent with hZero | hOne
  · left
    rw [hZero]
    simp
  · right
    rw [hOne]
    simp [Module.End.one_eq_id]

end CycleQ2GeometricBridgeAlgebra

end

end Q2UncompiledHiggsBridge


/- Component: continuation_20261112/SupportedProjectorAlgebra.lean -/
section Q2UncompiledProjectorConstruction

/-!
# Orthogonal generation and polynomial projectors for cycle-q2

DEVELOPMENT CONTINUATION, 12 November 2026. Compilation status is recorded
in solution.md. These lemmas extend the existing actual Fermat trace-pairing
bridge. They do not define a geometric variation of Hodge structure or an
algebraic cycle class map, and they do not prove residue exactness.

This component continues the actual Fermat trace-pairing bridge above.
-/

set_option autoImplicit false

noncomputable section

namespace CycleQ2GeometricBridgeAlgebra

/-- A common orthogonal direct sum for the actual socle pairings gives an
actual self-adjoint projection. The projection is constructed from the two
submodules; it is not supplied as an additional hypothesis. -/
theorem actual_trace_projection_selfAdjoint
    (U W : Submodule ℂ InvariantHodgeModel) (hUW : IsCompl U W)
    (horth : ∀ (t : InvariantTangentModel) (u : U) (w : W),
      actualTracePairing t (u : InvariantHodgeModel)
        (w : InvariantHodgeModel) = 0) :
    ∀ (t : InvariantTangentModel) (u v : InvariantHodgeModel),
      actualTracePairing t (U.projection W hUW u) v =
        actualTracePairing t u (U.projection W hUW v) := by
  intro t u v
  obtain ⟨u₁, u₂, hu, _⟩ := Submodule.existsUnique_add_of_isCompl hUW u
  obtain ⟨v₁, v₂, hv, _⟩ := Submodule.existsUnique_add_of_isCompl hUW v
  have hcross : actualTracePairing t (u₂ : InvariantHodgeModel)
      (v₁ : InvariantHodgeModel) = 0 := by
    rw [actualTracePairing_symmetric]
    exact horth t v₁ u₂
  rw [← hu, ← hv]
  simp only [map_add, LinearMap.add_apply,
    Submodule.projection_apply_left, Submodule.projection_apply_right,
    add_zero, horth t u₁ v₂, hcross]

/-- The finite Higgs result rules out a proper nonzero submodule having a
complement orthogonal for every actual socle pairing. -/
theorem actual_trace_orthogonal_direct_sum_trivial
    (U W : Submodule ℂ InvariantHodgeModel) (hUW : IsCompl U W)
    (horth : ∀ (t : InvariantTangentModel) (u : U) (w : W),
      actualTracePairing t (u : InvariantHodgeModel)
        (w : InvariantHodgeModel) = 0) :
    U = ⊥ ∨ U = ⊤ := by
  have hIdempotent : U.projection W hUW * U.projection W hUW =
      U.projection W hUW :=
    Submodule.isIdempotentElem_projection hUW
  have h := actual_trace_selfAdjoint_projector_range
    (U.projection W hUW)
    (actual_trace_projection_selfAdjoint U W hUW horth) hIdempotent
  simpa only [Submodule.range_projection] using h

/-- Once a geometric construction supplies the common orthogonal complement
of its image in the actual Fermat component, one nonzero image suffices for
surjectivity. The needed orthogonality remains an explicit algebraic premise. -/
theorem actual_trace_orthogonal_range_surjective
    {A : Type*} [AddCommGroup A] [Module ℂ A]
    (f : A →ₗ[ℂ] InvariantHodgeModel)
    (W : Submodule ℂ InvariantHodgeModel)
    (hW : IsCompl (LinearMap.range f) W)
    (horth : ∀ (t : InvariantTangentModel)
      (u : LinearMap.range f) (w : W),
      actualTracePairing t (u : InvariantHodgeModel)
        (w : InvariantHodgeModel) = 0)
    (hf : f ≠ 0) : Function.Surjective f := by
  rcases actual_trace_orthogonal_direct_sum_trivial
      (LinearMap.range f) W hW horth with hZero | hTop
  · exfalso
    apply hf
    apply LinearMap.ext
    intro x
    have hx : f x ∈ LinearMap.range f := ⟨x, rfl⟩
    rw [hZero] at hx
    simpa only [Submodule.mem_bot, LinearMap.zero_apply] using hx
  · exact LinearMap.range_eq_top.mp hTop

end CycleQ2GeometricBridgeAlgebra

namespace CycleQ2SupportedProjectorAlgebra

variable {K : Type*} [Field K]

/-- Normalization of an annihilating polynomial. Its constant coefficient
vanishes if the original constant coefficient is nonzero. -/
def projectorPolynomial (q : Polynomial K) : Polynomial K :=
  1 - Polynomial.C ((q.coeff 0)⁻¹) * q

theorem projectorPolynomial_coeff_zero (q : Polynomial K)
    (hq : q.coeff 0 ≠ 0) : (projectorPolynomial q).coeff 0 = 0 := by
  simp [projectorPolynomial, hq]

/-- Evaluation of the normalized annihilator is the identity. This is valid
in a possibly noncommutative algebra, including an endomorphism algebra. -/
theorem projectorPolynomial_aeval
    {A : Type*} [Ring A] [Algebra K A]
    (M : A) (q : Polynomial K) (hq : Polynomial.aeval M q = 0) :
    Polynomial.aeval M (projectorPolynomial q) = 1 := by
  simp [projectorPolynomial, hq]

section Endomorphisms

variable {V : Type*} [AddCommGroup V] [Module K V]

/-- A polynomial with zero constant coefficient kills every vector killed
by the endomorphism. Factoring by X makes the composition order explicit. -/
theorem aeval_apply_zero_of_coeff_zero
    (M : Module.End K V) (p : Polynomial K) (hp : p.coeff 0 = 0)
    (v : V) (hv : M v = 0) : Polynomial.aeval M p v = 0 := by
  obtain ⟨r, hr⟩ := Polynomial.X_dvd_iff.mpr hp
  rw [hr, mul_comm (Polynomial.X : Polynomial K) r, map_mul,
    Polynomial.aeval_X]
  change Polynomial.aeval M r (M v) = 0
  rw [hv, map_zero]

/-- On the kernel of the chosen annihilator, the normalized polynomial acts
as the identity even if that annihilator does not vanish on the whole space. -/
theorem projectorPolynomial_apply_of_annihilator
    (M : Module.End K V) (q : Polynomial K) (v : V)
    (hv : Polynomial.aeval M q v = 0) :
    Polynomial.aeval M (projectorPolynomial q) v = v := by
  simp only [projectorPolynomial, map_sub, map_one, map_mul,
    Polynomial.aeval_C]
  change v - (algebraMap K (Module.End K V) ((q.coeff 0)⁻¹))
    (Polynomial.aeval M q v) = v
  rw [hv, map_zero, sub_zero]

/-- The normalized polynomial selects one direct summand: its restriction
there is the identity and its restriction to the other summand is zero. -/
theorem projectorPolynomial_aeval_eq_projection
    (M : Module.End K V)
    (U W : Submodule K V) (hUW : IsCompl U W)
    (q : Polynomial K) (hq : q.coeff 0 ≠ 0)
    (hU : ∀ u : U, Polynomial.aeval M q (u : V) = 0)
    (hW : ∀ w : W, M (w : V) = 0) :
    Polynomial.aeval M (projectorPolynomial q) = U.projection W hUW := by
  ext v
  obtain ⟨u, w, hv, _⟩ := Submodule.existsUnique_add_of_isCompl hUW v
  rw [← hv, map_add, map_add, Submodule.projection_apply_left,
    Submodule.projection_apply_right]
  rw [projectorPolynomial_apply_of_annihilator M q (u : V) (hU u),
    aeval_apply_zero_of_coeff_zero M (projectorPolynomial q)
      (projectorPolynomial_coeff_zero q hq) (w : V) (hW w)]

end Endomorphisms

/-- The algebraic support argument needs only closure under sums, scalars,
and composition on the right by M. A zero-constant polynomial in M then
belongs to the same submodule. No algebraic cycle support is defined here. -/
theorem aeval_mem_of_coeff_zero
    {A : Type*} [Ring A] [Algebra K A]
    (S : Submodule K A) (M : A) (hM : M ∈ S)
    (hmul : ∀ N ∈ S, N * M ∈ S)
    (p : Polynomial K) (hp : p.coeff 0 = 0) :
    Polynomial.aeval M p ∈ S := by
  have hpowers (n : ℕ) : M ^ (n + 1) ∈ S := by
    induction n with
    | zero => simpa only [Nat.zero_add, pow_one] using hM
    | succ n ih =>
      simpa only [Nat.succ_eq_add_one, pow_succ] using hmul (M ^ (n + 1)) ih
  rw [Polynomial.aeval_eq_sum_range]
  apply S.sum_mem
  intro n hn
  cases n with
  | zero => simpa only [hp, zero_smul] using S.zero_mem
  | succ n => exact S.smul_mem (p.coeff (n + 1)) (hpowers n)

/-- A supplied algebraic correspondence operator, with its two summands and
annihilator, yields an actual idempotent in any composition-stable submodule
containing that operator. In a geometric application the submodule must be
proved to consist of classes represented on the required divisor square. -/
theorem projection_mem_of_annihilator
    {V : Type*} [AddCommGroup V] [Module K V]
    (S : Submodule K (Module.End K V))
    (M : Module.End K V) (hM : M ∈ S)
    (hmul : ∀ N ∈ S, N * M ∈ S)
    (U W : Submodule K V) (hUW : IsCompl U W)
    (q : Polynomial K) (hq : q.coeff 0 ≠ 0)
    (hU : ∀ u : U, Polynomial.aeval M q (u : V) = 0)
    (hW : ∀ w : W, M (w : V) = 0) :
    U.projection W hUW ∈ S := by
  rw [← projectorPolynomial_aeval_eq_projection M U W hUW q hq hU hW]
  exact aeval_mem_of_coeff_zero S M hM hmul
    (projectorPolynomial q) (projectorPolynomial_coeff_zero q hq)

end CycleQ2SupportedProjectorAlgebra

namespace CycleQ2GeometricBridgeAlgebra

open CycleQ2FermatJacobian
open CycleQ2SupportedProjectorAlgebra

/-- An explicit polynomial in an actual Fermat-component endomorphism.
The minimal polynomial is supplied by Mathlib's algebraic definition; its
annihilation and the nonzero constant term are established below. -/
def actualProjectorPolynomial (M : Module.End ℂ InvariantHodgeModel) :
    Polynomial ℂ :=
  projectorPolynomial (minpoly ℂ M)

theorem actualProjectorPolynomial_coeff_zero
    (M : Module.End ℂ InvariantHodgeModel) (hM : Function.Injective M) :
    (actualProjectorPolynomial M).coeff 0 = 0 := by
  letI : Module.Free ℂ InvariantHodgeModel :=
    Module.Free.of_basis degreeSixCharacterOneBasis
  letI : Module.Finite ℂ InvariantHodgeModel :=
    Module.Finite.of_basis degreeSixCharacterOneBasis
  apply projectorPolynomial_coeff_zero
  exact LinearMap.minpoly_coeff_zero_of_injective hM

theorem actualProjectorPolynomial_aeval
    (M : Module.End ℂ InvariantHodgeModel) :
    Polynomial.aeval M (actualProjectorPolynomial M) = 1 := by
  exact projectorPolynomial_aeval M (minpoly ℂ M) (minpoly.aeval ℂ M)

/-- Injectivity on the actual 33-dimensional quotient component supplies an
identity polynomial with no constant term. This is the finite-dimensional
algebra needed to keep the projector inside a divisor-supported span. -/
theorem actual_zero_constant_polynomial_identity
    (M : Module.End ℂ InvariantHodgeModel) (hM : Function.Injective M) :
    ∃ p : Polynomial ℂ, p.coeff 0 = 0 ∧ Polynomial.aeval M p = 1 :=
  ⟨actualProjectorPolynomial M, actualProjectorPolynomial_coeff_zero M hM,
    actualProjectorPolynomial_aeval M⟩

/-- The actual identity is in every composition-stable submodule of
endomorphisms containing an injective operator. Establishing the geometric
support interpretation of such a submodule remains a separate theorem. -/
theorem actual_identity_mem_of_composition_stable
    (S : Submodule ℂ (Module.End ℂ InvariantHodgeModel))
    (M : Module.End ℂ InvariantHodgeModel) (hM : M ∈ S)
    (hmul : ∀ N ∈ S, N * M ∈ S)
    (hInjective : Function.Injective M) :
    (1 : Module.End ℂ InvariantHodgeModel) ∈ S := by
  obtain ⟨p, hp, hEval⟩ := actual_zero_constant_polynomial_identity M hInjective
  rw [← hEval]
  exact aeval_mem_of_coeff_zero S M hM hmul p hp

end CycleQ2GeometricBridgeAlgebra

end

end Q2UncompiledProjectorConstruction


/- Component: continuation_20261112/AffineFiniteTopCohomology.lean -/
section Q2UncompiledFiniteTopDeRham

/-!
# Finite field trace on the actual generic-point top de Rham quotient

DEVELOPMENT CONTINUATION. Compilation status is recorded in solution.md.

For a finite extension of the protected affine function field, this file
constructs its actual relative Kähler module, the pulled-back coordinate
basis, genuine exterior forms, the degree-three exterior differential, and
normalized trace on three-forms and four-forms. Trace commutes with that
differential and is a left inverse to exterior pullback. Consequently the
pullback on the existing `CycleQ2AffineTopCohomology.TopDeRham` is injective.

The complex algebra structure on the extension is required to be the one
compatible with the given tower. Finite separability follows from the base
field's characteristic zero; no geometric existence hypothesis is added.

This constructs finite-cover descent. It does not prove that the protected
residue class vanishes, and does not replace `missing_geometric_existence`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable section

namespace CycleQ2AffineFiniteTopCohomology

open scoped BigOperators TensorProduct

abbrev K := CycleQ2AffineHypersurface.AffineFunctionField

local instance coefficientCharZero : CharZero K :=
  charZero_of_injective_algebraMap (algebraMap ℂ K).injective

local instance coefficientIntAlgebra : Algebra ℤ K := Ring.toIntAlgebra _

variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra ℂ L] [IsScalarTower ℂ K L]

abbrev Omega := Ω[L⁄ℂ]
abbrev d : Derivation ℂ L (Omega L) := KaehlerDifferential.D ℂ L

theorem tangent_complex_constant (j : Fin 4) (c : ℂ) :
    CycleQ2AffineFiniteDescent.tangent L j (algebraMap ℂ L c) = 0 := by
  rw [IsScalarTower.algebraMap_apply ℂ K L]
  exact CycleQ2AffineFiniteDescent.tangent_complex_constant L j c

theorem tangent_complex_smul (j : Fin 4) (c : ℂ) (z : L) :
    CycleQ2AffineFiniteDescent.tangent L j (c • z) =
      c • CycleQ2AffineFiniteDescent.tangent L j z := by
  simp only [Algebra.smul_def, Derivation.leibniz, smul_eq_mul,
    tangent_complex_constant, mul_zero, add_zero]
  simp

/-- The already constructed finite-extension tangent, with its actual
complex linearity included in the type. -/
def complexTangent (j : Fin 4) : Derivation ℂ L L where
  toFun := CycleQ2AffineFiniteDescent.tangent L j
  map_add' := (CycleQ2AffineFiniteDescent.tangent L j).map_add
  map_smul' := tangent_complex_smul L j
  map_one_eq_zero' := (CycleQ2AffineFiniteDescent.tangent L j).map_one_eq_zero
  leibniz' := (CycleQ2AffineFiniteDescent.tangent L j).leibniz

@[simp] theorem complexTangent_apply (j : Fin 4) (z : L) :
    complexTangent L j z = CycleQ2AffineFiniteDescent.tangent L j z := rfl

/-- The canonical pullback of universal one-forms, rather than an abstract
vector space supplied with a coordinate label. -/
def oneFormPullback : CycleQ2AffineDifferentials.Omega →ₗ[K] Omega L :=
  KaehlerDifferential.map ℂ ℂ K L

def coordinateDifferential (j : Fin 4) : Omega L :=
  d L (algebraMap K L
    (CycleQ2AffineHypersurface.affineMap (MvPolynomial.X j.succ)))

@[simp] theorem oneFormPullback_coordinateBasis (j : Fin 4) :
    oneFormPullback L (CycleQ2AffineDifferentials.coordinateBasis j) =
      coordinateDifferential L j := by
  rw [CycleQ2AffineDifferentials.coordinateBasis_apply]
  exact KaehlerDifferential.map_D ℂ ℂ K L _

def coordinateMap : Omega L →ₗ[L] (Fin 4 → L) :=
  LinearMap.pi fun j => (complexTangent L j).liftKaehlerDifferential

@[simp] theorem coordinateMap_d (z : L) (j : Fin 4) :
    coordinateMap L (d L z) j = CycleQ2AffineFiniteDescent.tangent L j z :=
  Derivation.liftKaehlerDifferential_comp_D (complexTangent L j) z

@[simp] theorem coordinateMap_coordinateDifferential (i j : Fin 4) :
    coordinateMap L (coordinateDifferential L i) j =
      if i = j then 1 else 0 := by
  rw [coordinateDifferential, coordinateMap_d,
    CycleQ2AffineFiniteDescent.tangent_algebraMap,
    CycleQ2AffineHypersurface.affineTangent_coordinate]
  split_ifs <;> simp

def coordinateExpansion : (Fin 4 → L) →ₗ[L] Omega L :=
  Fintype.linearCombination L (coordinateDifferential L)

@[simp] theorem coordinateExpansion_apply (v : Fin 4 → L) :
    coordinateExpansion L v = ∑ j, v j • coordinateDifferential L j := rfl

/-- Finite separability makes the relative module Ω[L/K] zero. The
transitivity sequence therefore says that actual base one-forms span Ω[L/ℂ]. -/
theorem oneFormBaseChange_surjective :
    Function.Surjective (KaehlerDifferential.mapBaseChange ℂ K L) := by
  letI : Algebra.FormallyUnramified K L :=
    Algebra.FormallyUnramified.of_isSeparable K L
  rw [← LinearMap.range_eq_top, KaehlerDifferential.range_mapBaseChange]
  apply top_unique
  intro ω _
  change KaehlerDifferential.map ℂ K L L ω = 0
  exact Subsingleton.elim _ _

private theorem coordinateExpansion_coordinateMap_pullback
    (ω : CycleQ2AffineDifferentials.Omega) :
    coordinateExpansion L (coordinateMap L (oneFormPullback L ω)) =
      oneFormPullback L ω := by
  have h : (((coordinateExpansion L).comp (coordinateMap L)).restrictScalars K).comp
      (oneFormPullback L) = oneFormPullback L := by
    apply CycleQ2AffineDifferentials.coordinateBasis.ext
    intro i
    change coordinateExpansion L
        (coordinateMap L
          (oneFormPullback L (CycleQ2AffineDifferentials.coordinateBasis i))) =
      oneFormPullback L (CycleQ2AffineDifferentials.coordinateBasis i)
    rw [oneFormPullback_coordinateBasis]
    simp [coordinateExpansion_apply, eq_comm]
  exact LinearMap.congr_fun h ω

theorem coordinateExpansion_coordinateMap :
    (coordinateExpansion L).comp (coordinateMap L) = LinearMap.id := by
  apply LinearMap.ext
  intro ω
  obtain ⟨u, rfl⟩ := oneFormBaseChange_surjective L ω
  change coordinateExpansion L
      (coordinateMap L (KaehlerDifferential.mapBaseChange ℂ K L u)) =
    KaehlerDifferential.mapBaseChange ℂ K L u
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a η =>
      simp only [KaehlerDifferential.mapBaseChange_tmul]
      change coordinateExpansion L (coordinateMap L (a • oneFormPullback L η)) =
        a • oneFormPullback L η
      rw [map_smul, map_smul, coordinateExpansion_coordinateMap_pullback]
  | add u v hu hv => simp only [map_add, hu, hv]

theorem coordinateMap_coordinateExpansion :
    (coordinateMap L).comp (coordinateExpansion L) = LinearMap.id := by
  ext v j
  simp [coordinateExpansion_apply, coordinateMap_coordinateDifferential,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, eq_comm]

def differentialCoordinates : Omega L ≃ₗ[L] (Fin 4 → L) where
  toLinearMap := coordinateMap L
  invFun := coordinateExpansion L
  left_inv z := LinearMap.congr_fun (coordinateExpansion_coordinateMap L) z
  right_inv v := LinearMap.congr_fun (coordinateMap_coordinateExpansion L) v

/-- This basis is derived from universal differentials and separability.
It is not a chosen basis of an unrelated four-dimensional space. -/
def coordinateBasis : Module.Basis (Fin 4) L (Omega L) :=
  Module.Basis.ofEquivFun (differentialCoordinates L)

@[simp] theorem coordinateBasis_apply (j : Fin 4) :
    coordinateBasis L j = coordinateDifferential L j := by
  rw [coordinateBasis, Module.Basis.coe_ofEquivFun]
  change coordinateExpansion L (Pi.single j 1) = coordinateDifferential L j
  simp [coordinateExpansion]

@[simp] theorem coordinateBasis_repr_d (z : L) (j : Fin 4) :
    (coordinateBasis L).repr (d L z) j =
      CycleQ2AffineFiniteDescent.tangent L j z := by
  rw [coordinateBasis, Module.Basis.ofEquivFun_repr_apply]
  exact coordinateMap_d L z j

theorem differential_coordinates (z : L) :
    d L z = ∑ j, CycleQ2AffineFiniteDescent.tangent L j z •
      coordinateDifferential L j := by
  have h := LinearMap.congr_fun (coordinateExpansion_coordinateMap L) (d L z)
  simpa only [LinearMap.comp_apply, LinearMap.id_apply,
    coordinateExpansion_apply, coordinateMap_d] using h.symm

abbrev Form (p : ℕ) := ⋀[L]^p (Omega L)

def thirdBasis : Module.Basis (Fin 4) L (Form L 3) :=
  ((coordinateBasis L).exteriorPower 3).reindex CycleQ2AffineExterior.omitEquiv.symm

theorem thirdBasis_apply (i : Fin 4) :
    thirdBasis L i = exteriorPower.ιMulti L 3
      (i.removeNth (coordinateDifferential L)) := by
  rw [thirdBasis, Module.Basis.reindex_apply, Equiv.symm_symm]
  change (coordinateBasis L).exteriorPower 3 (CycleQ2AffineExterior.omitIndex i) = _
  rw [exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family
  congr 1
  funext j
  simp only [Function.comp_apply, coordinateBasis_apply,
    Set.powersetCard.ofFinEmbEquiv_symm_apply, CycleQ2AffineExterior.omitIndex,
    Finset.orderEmbOfFin_compl_singleton_eq_succAboveOrderEmb, Fin.removeNth]
  rfl

def volume : Form L 4 := exteriorPower.ιMulti L 4 (coordinateDifferential L)

theorem topBasis_apply :
    (coordinateBasis L).exteriorPower 4 CycleQ2AffineExterior.topIndex = volume L := by
  rw [exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family volume
  congr 1
  funext j
  rw [Function.comp_apply, coordinateBasis_apply]
  have ho : (fun i : Fin 4 => i) =
      (Finset.univ : Finset (Fin 4)).orderEmbOfFin (by simp) :=
    Finset.orderEmbOfFin_unique _ (fun _ => Finset.mem_univ _) strictMono_id
  exact congrArg (coordinateDifferential L) (congrFun ho j).symm

def volumeCoefficient : Form L 4 →ₗ[L] L :=
  ((coordinateBasis L).exteriorPower 4).coord CycleQ2AffineExterior.topIndex

@[simp] theorem volumeCoefficient_volume : volumeCoefficient L (volume L) = 1 := by
  rw [← topBasis_apply]
  simp [volumeCoefficient]

theorem topForm_eq_coefficient (ω : Form L 4) :
    ω = volumeCoefficient L ω • volume L := by
  calc
    ω = ∑ s, ((coordinateBasis L).exteriorPower 4).repr ω s •
        (coordinateBasis L).exteriorPower 4 s :=
      (((coordinateBasis L).exteriorPower 4).sum_repr ω).symm
    _ = _ := by
      rw [Finset.sum_eq_single CycleQ2AffineExterior.topIndex]
      · rw [topBasis_apply]
        rfl
      · intro i hi hne
        exact (hne (CycleQ2AffineExterior.topIndex_unique i)).elim
      · simp

def wedgeOneThree : Omega L →ₗ[L] (Form L 3 →ₗ[L] Form L 4) :=
  exteriorPower.alternatingMapLinearEquiv.toLinearMap.comp
    (exteriorPower.ιMulti L 4).curryLeft

@[simp] theorem wedgeOneThree_wedge (a : Omega L) (v : Fin 3 → Omega L) :
    wedgeOneThree L a (exteriorPower.ιMulti L 3 v) =
      exteriorPower.ιMulti L 4 (Matrix.vecCons a v) := by
  simp [wedgeOneThree]

@[simp] theorem wedgeOneThree_basis (a : Omega L) (i : Fin 4) :
    wedgeOneThree L a (thirdBasis L i) =
      exteriorPower.ιMulti L 4
        (Matrix.vecCons a (i.removeNth (coordinateDifferential L))) := by
  rw [thirdBasis_apply, wedgeOneThree_wedge]

theorem wedge_coordinate_basis (j i : Fin 4) :
    wedgeOneThree L (coordinateDifferential L j) (thirdBasis L i) =
      (if j = i then (-1 : L) ^ i.val else 0) • volume L := by
  rw [wedgeOneThree_basis]
  by_cases h : j = i
  · subst j
    rw [if_pos rfl]
    have hh := (exteriorPower.ιMulti L 4).neg_one_pow_smul_map_insertNth i
      (coordinateDifferential L i) (i.removeNth (coordinateDifferential L))
    rw [Fin.insertNth_self_removeNth] at hh
    simpa only [volume, ← Int.cast_smul_eq_zsmul L, Int.cast_pow,
      Int.cast_neg, Int.cast_one] using hh.symm
  · rw [if_neg h, zero_smul]
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq h
    apply (exteriorPower.ιMulti L 4).map_eq_zero_of_eq (i := 0) (j := k.succ)
    · simp [Fin.removeNth, hk]
    · exact (Fin.succ_ne_zero k).symm

theorem wedge_d_basis (a : L) (i : Fin 4) :
    wedgeOneThree L (d L a) (thirdBasis L i) =
      ((-1 : L) ^ i.val * CycleQ2AffineFiniteDescent.tangent L i a) • volume L := by
  rw [differential_coordinates, map_sum]
  simp only [map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    wedge_coordinate_basis, smul_smul]
  simp [mul_comm]

/-- The usual differential in the pulled-back basis of exact coordinate
wedges. Its equality to `da ∧ basis` is proved below. -/
def exteriorD3 : Form L 3 →ₗ[ℂ] Form L 4 :=
  ∑ i : Fin 4,
    ((LinearMap.toSpanSingleton L (Form L 4)
      ((-1 : L) ^ i.val • volume L)).restrictScalars ℂ).comp
      ((complexTangent L i).toLinearMap.comp
        (((thirdBasis L).coord i).restrictScalars ℂ))

theorem exteriorD3_apply (η : Form L 3) :
    exteriorD3 L η =
      (∑ i : Fin 4, (-1 : L) ^ i.val *
        CycleQ2AffineFiniteDescent.tangent L i ((thirdBasis L).repr η i)) • volume L := by
  simp only [exteriorD3, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.coe_restrictScalars, LinearMap.toSpanSingleton_apply,
    Module.Basis.coord_apply, Derivation.coeFn_coe, complexTangent_apply,
    smul_smul, ← Finset.sum_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem exteriorD3_smul_basis (a : L) (i : Fin 4) :
    exteriorD3 L (a • thirdBasis L i) =
      wedgeOneThree L (d L a) (thirdBasis L i) := by
  rw [exteriorD3_apply, wedge_d_basis]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, hji, Ne.symm hji]
  · simp

theorem exteriorD3_eq_sum_wedge (η : Form L 3) :
    exteriorD3 L η = ∑ i : Fin 4,
      wedgeOneThree L (d L ((thirdBasis L).repr η i)) (thirdBasis L i) := by
  rw [exteriorD3_apply]
  simp only [wedge_d_basis, Finset.sum_smul]

theorem exteriorD3_leibniz (a : L) (η : Form L 3) :
    exteriorD3 L (a • η) =
      wedgeOneThree L (d L a) η + a • exteriorD3 L η := by
  have hh := congrArg (wedgeOneThree L (d L a)) ((thirdBasis L).sum_repr η)
  simp only [map_sum, map_smul] at hh
  rw [exteriorD3_eq_sum_wedge]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, Derivation.leibniz,
    map_add, LinearMap.add_apply, LinearMap.smul_apply, Finset.sum_add_distrib]
  rw [← Finset.smul_sum, ← exteriorD3_eq_sum_wedge, hh]
  exact add_comm _ _

private def targetWedgeOverBase (p : ℕ) :
    (Omega L) [⋀^Fin p]→ₗ[K] (Form L p) where
  toMultilinearMap := (exteriorPower.ιMulti L p).toMultilinearMap.restrictScalars K
  map_eq_zero_of_eq' := (exteriorPower.ιMulti L p).map_eq_zero_of_eq

/-- Pullback on genuine exterior powers, induced by the canonical map on
universal one-forms and the universal alternating property. -/
def exteriorPullback (p : ℕ) :
    CycleQ2AffineExterior.Form p →ₗ[K] Form L p :=
  exteriorPower.alternatingMapLinearEquiv
    ((targetWedgeOverBase L p).compLinearMap (oneFormPullback L))

@[simp] theorem exteriorPullback_ιMulti (p : ℕ)
    (v : Fin p → CycleQ2AffineDifferentials.Omega) :
    exteriorPullback L p (exteriorPower.ιMulti K p v) =
      exteriorPower.ιMulti L p (fun i => oneFormPullback L (v i)) := by
  rw [exteriorPullback, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.compLinearMap_apply]
  rfl

theorem exteriorPullback_basis (p : ℕ) (s : Set.powersetCard (Fin 4) p) :
    exteriorPullback L p (CycleQ2AffineDifferentials.coordinateBasis.exteriorPower p s) =
      (coordinateBasis L).exteriorPower p s := by
  simp only [exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorPullback_ιMulti]
  congr 1
  funext j
  exact (oneFormPullback_coordinateBasis L _).trans (coordinateBasis_apply L _).symm

@[simp] theorem exteriorPullback_thirdBasis (i : Fin 4) :
    exteriorPullback L 3 (CycleQ2AffineExterior.thirdBasis i) = thirdBasis L i := by
  simpa only [CycleQ2AffineExterior.thirdBasis, thirdBasis,
    Module.Basis.reindex_apply, Equiv.symm_symm] using
    exteriorPullback_basis L 3 (CycleQ2AffineExterior.omitEquiv i)

@[simp] theorem exteriorPullback_volume :
    exteriorPullback L 4 CycleQ2AffineExterior.volume = volume L := by
  rw [← CycleQ2AffineExterior.topBasis_apply, ← topBasis_apply]
  exact exteriorPullback_basis L 4 CycleQ2AffineExterior.topIndex

theorem exteriorPullback_three_repr (η : CycleQ2AffineExterior.Form 3) (i : Fin 4) :
    (thirdBasis L).repr (exteriorPullback L 3 η) i =
      algebraMap K L (CycleQ2AffineExterior.thirdBasis.repr η i) := by
  have h : (((thirdBasis L).coord i).restrictScalars K).comp (exteriorPullback L 3) =
      (Algebra.linearMap K L).comp (CycleQ2AffineExterior.thirdBasis.coord i) := by
    apply CycleQ2AffineExterior.thirdBasis.ext
    intro j
    simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars,
      exteriorPullback_thirdBasis, Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_apply, Algebra.linearMap_apply]
    split_ifs <;> simp
  exact LinearMap.congr_fun h η

theorem exteriorPullback_top (ω : CycleQ2AffineExterior.Form 4) :
    exteriorPullback L 4 ω =
      algebraMap K L (CycleQ2AffineExterior.volumeCoefficient ω) • volume L := by
  calc
    exteriorPullback L 4 ω = exteriorPullback L 4
        (CycleQ2AffineExterior.volumeCoefficient ω • CycleQ2AffineExterior.volume) :=
      congrArg (exteriorPullback L 4) (CycleQ2AffineExterior.topForm_eq_coefficient ω)
    _ = CycleQ2AffineExterior.volumeCoefficient ω • volume L := by
      rw [map_smul, exteriorPullback_volume]
    _ = _ := by simp only [IsScalarTower.algebraMap_smul]

/-- Pullback commutes with the actual degree-three exterior differential. -/
theorem exteriorD3_pullback (η : CycleQ2AffineExterior.Form 3) :
    exteriorD3 L (exteriorPullback L 3 η) =
      exteriorPullback L 4 (CycleQ2AffineExterior.exteriorD3 η) := by
  calc
    exteriorD3 L (exteriorPullback L 3 η) =
        (∑ i : Fin 4, (-1 : L) ^ i.val * algebraMap K L
          (CycleQ2AffineHypersurface.affineTangent i
            (CycleQ2AffineExterior.thirdBasis.repr η i))) • volume L := by
      rw [exteriorD3_apply]
      simp only [exteriorPullback_three_repr, CycleQ2AffineFiniteDescent.tangent_algebraMap]
    _ = algebraMap K L (∑ i : Fin 4, (-1 : K) ^ i.val *
        CycleQ2AffineHypersurface.affineTangent i
          (CycleQ2AffineExterior.thirdBasis.repr η i)) • volume L := by
      simp only [map_sum, map_mul, map_pow, map_neg, map_one]
    _ = (∑ i : Fin 4, (-1 : K) ^ i.val *
        CycleQ2AffineHypersurface.affineTangent i
          (CycleQ2AffineExterior.thirdBasis.repr η i)) • volume L := by
      simp only [IsScalarTower.algebraMap_smul]
    _ = exteriorPullback L 4 (CycleQ2AffineExterior.exteriorD3 η) := by
      rw [CycleQ2AffineExterior.exteriorD3_apply, map_smul, exteriorPullback_volume]

private def traceCoefficients : (Fin 4 → L) →ₗ[K] (Fin 4 → K) :=
  LinearMap.pi fun i => (Algebra.normalizedTrace K L).comp (LinearMap.proj i)

/-- Normalized trace of the actual three-form coefficients, in the
pulled-back exact-coordinate wedge basis. -/
def traceThree : Form L 3 →ₗ[K] CycleQ2AffineExterior.Form 3 :=
  CycleQ2AffineExterior.thirdBasis.equivFun.symm.toLinearMap.comp
    ((traceCoefficients L).comp
      ((thirdBasis L).equivFun.toLinearMap.restrictScalars K))

@[simp] theorem traceThree_repr (η : Form L 3) (i : Fin 4) :
    CycleQ2AffineExterior.thirdBasis.repr (traceThree L η) i =
      Algebra.normalizedTrace K L ((thirdBasis L).repr η i) := by
  change CycleQ2AffineExterior.thirdBasis.coord i
      (CycleQ2AffineExterior.thirdBasis.equivFun.symm
        (fun j => Algebra.normalizedTrace K L ((thirdBasis L).repr η j))) = _
  exact Module.Basis.coord_equivFun_symm CycleQ2AffineExterior.thirdBasis i _

/-- Normalized trace of the coefficient of the actual pulled-back top
volume. This is K-linear on forms; its induced cohomology map is C-linear. -/
def traceFour : Form L 4 →ₗ[K] CycleQ2AffineExterior.Form 4 :=
  (LinearMap.toSpanSingleton K (CycleQ2AffineExterior.Form 4)
    CycleQ2AffineExterior.volume).comp
      ((Algebra.normalizedTrace K L).comp ((volumeCoefficient L).restrictScalars K))

@[simp] theorem traceFour_apply (ω : Form L 4) :
    traceFour L ω =
      Algebra.normalizedTrace K L (volumeCoefficient L ω) • CycleQ2AffineExterior.volume :=
  rfl

private theorem trace_signed_tangent (i : Fin 4) (x : L) :
    Algebra.normalizedTrace K L
        ((-1 : L) ^ i.val * CycleQ2AffineFiniteDescent.tangent L i x) =
      (-1 : K) ^ i.val * CycleQ2AffineHypersurface.affineTangent i
        (Algebra.normalizedTrace K L x) := by
  calc
    Algebra.normalizedTrace K L
        ((-1 : L) ^ i.val * CycleQ2AffineFiniteDescent.tangent L i x) =
        Algebra.normalizedTrace K L
          (((-1 : K) ^ i.val) • CycleQ2AffineFiniteDescent.tangent L i x) := by
      simp only [Algebra.smul_def, map_pow, map_neg, map_one]
    _ = (-1 : K) ^ i.val *
        Algebra.normalizedTrace K L (CycleQ2AffineFiniteDescent.tangent L i x) := by
      rw [map_smul, smul_eq_mul]
    _ = _ := by
      rw [HoldoutConstruction.finiteNormalizedTrace_derivation
        (CycleQ2AffineHypersurface.affineTangent i)
        (CycleQ2AffineFiniteDescent.tangent L i)
        (CycleQ2AffineFiniteDescent.tangent_algebraMap L i)]

/-- The chain identity follows from the actual finite-field trace theorem,
with the exterior signs retained. No commutation assumption is supplied. -/
theorem traceFour_exteriorD3 (η : Form L 3) :
    traceFour L (exteriorD3 L η) =
      CycleQ2AffineExterior.exteriorD3 (traceThree L η) := by
  rw [traceFour_apply, exteriorD3_apply, map_smul, volumeCoefficient_volume,
    smul_eq_mul, mul_one, map_sum, CycleQ2AffineExterior.exteriorD3_apply]
  simp only [traceThree_repr]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => trace_signed_tangent L i _)

@[simp] theorem traceThree_pullback (η : CycleQ2AffineExterior.Form 3) :
    traceThree L (exteriorPullback L 3 η) = η := by
  apply CycleQ2AffineExterior.thirdBasis.repr.injective
  ext i
  rw [traceThree_repr, exteriorPullback_three_repr,
    Algebra.normalizedTrace_algebraMap_apply_eq_self]

@[simp] theorem traceFour_pullback (ω : CycleQ2AffineExterior.Form 4) :
    traceFour L (exteriorPullback L 4 ω) = ω := by
  rw [traceFour_apply, exteriorPullback_top, map_smul,
    volumeCoefficient_volume, smul_eq_mul, mul_one,
    Algebra.normalizedTrace_algebraMap_apply_eq_self]
  exact (CycleQ2AffineExterior.topForm_eq_coefficient ω).symm

instance formFiveSubsingleton : Subsingleton (Form L 5) := by
  refine ⟨?_⟩
  intro η ξ
  apply ((coordinateBasis L).exteriorPower 5).repr.injective
  apply Finsupp.ext
  intro s
  have hcard : (s : Finset (Fin 4)).card ≤ 4 := by
    simpa using Finset.card_le_univ (s : Finset (Fin 4))
  have hs : (s : Finset (Fin 4)).card = 5 := s.property
  exact False.elim (by omega)

def exactTopForms : Submodule ℂ (Form L 4) := LinearMap.range (exteriorD3 L)
abbrev TopDeRham := (Form L 4) ⧸ exactTopForms L
def classOf : Form L 4 →ₗ[ℂ] TopDeRham L := (exactTopForms L).mkQ

theorem classOf_eq_zero_iff (ω : Form L 4) :
    classOf L ω = 0 ↔ ∃ η : Form L 3, exteriorD3 L η = ω := by
  change (Submodule.Quotient.mk ω : TopDeRham L) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  change ω ∈ LinearMap.range (exteriorD3 L) ↔ _
  exact LinearMap.mem_range

@[simp] theorem classOf_exteriorD3 (η : Form L 3) :
    classOf L (exteriorD3 L η) = 0 :=
  (classOf_eq_zero_iff L _).mpr ⟨η, rfl⟩

/-- Canonical pullback from the existing, unchanged protected TopDeRham. -/
def pullbackClass : CycleQ2AffineTopCohomology.TopDeRham →ₗ[ℂ] TopDeRham L :=
  CycleQ2AffineTopCohomology.descend
    ((classOf L).comp ((exteriorPullback L 4).restrictScalars ℂ)) (by
      intro η
      change classOf L (exteriorPullback L 4 (CycleQ2AffineExterior.exteriorD3 η)) = 0
      rw [← exteriorD3_pullback, classOf_exteriorD3])

/-- Constructed normalized trace on the actual quotient by exact forms. -/
def traceClass : TopDeRham L →ₗ[ℂ] CycleQ2AffineTopCohomology.TopDeRham :=
  (exactTopForms L).liftQ
    (CycleQ2AffineTopCohomology.classOf.comp ((traceFour L).restrictScalars ℂ)) (by
      rintro ω ⟨η, rfl⟩
      change CycleQ2AffineTopCohomology.classOf (traceFour L (exteriorD3 L η)) = 0
      rw [traceFour_exteriorD3, CycleQ2AffineTopCohomology.classOf_exteriorD3])

@[simp] theorem pullbackClass_classOf (ω : CycleQ2AffineExterior.Form 4) :
    pullbackClass L (CycleQ2AffineTopCohomology.classOf ω) =
      classOf L (exteriorPullback L 4 ω) := rfl

@[simp] theorem traceClass_classOf (ω : Form L 4) :
    traceClass L (classOf L ω) =
      CycleQ2AffineTopCohomology.classOf (traceFour L ω) := rfl

/-- Trace is a left inverse on actual top de Rham classes. -/
@[simp] theorem traceClass_pullbackClass (c : CycleQ2AffineTopCohomology.TopDeRham) :
    traceClass L (pullbackClass L c) = c := by
  obtain ⟨ω, rfl⟩ := CycleQ2AffineTopCohomology.exactTopForms.mkQ_surjective c
  change CycleQ2AffineTopCohomology.classOf
      (traceFour L (exteriorPullback L 4 ω)) = CycleQ2AffineTopCohomology.classOf ω
  rw [traceFour_pullback]

theorem pullbackClass_injective : Function.Injective (pullbackClass L) := by
  have h : Function.LeftInverse (traceClass L) (pullbackClass L) :=
    traceClass_pullbackClass L
  exact h.injective

theorem pullbackClass_eq_zero_iff (c : CycleQ2AffineTopCohomology.TopDeRham) :
    pullbackClass L c = 0 ↔ c = 0 := by
  constructor
  · intro h
    apply pullbackClass_injective L
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

/-- A primitive on the finite field descends to an actual rational
three-form on the protected field by the explicitly constructed trace. -/
theorem exact_pullback_iff (ω : CycleQ2AffineExterior.Form 4) :
    (∃ η : Form L 3, exteriorD3 L η = exteriorPullback L 4 ω) ↔
      ∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η = ω := by
  constructor
  · rintro ⟨η, hη⟩
    refine ⟨traceThree L η, ?_⟩
    rw [← traceFour_exteriorD3, hη, traceFour_pullback]
  · rintro ⟨η, hη⟩
    exact ⟨exteriorPullback L 3 η, by rw [exteriorD3_pullback, hη]⟩

/-- Binding of the constructed finite-cover pullback to the original
positive residue source class. It proves preservation and reflection of
vanishing, without asserting that the protected class vanishes. -/
theorem residueClass_pullback_eq_zero_iff (A : HodgeComputer.AmbientPoly 4) :
    classOf L (exteriorPullback L 4 (CycleQ2AffineExactness.residueSourceForm A)) = 0 ↔
      CycleQ2AffineTopCohomology.residueClass A = 0 :=
  pullbackClass_eq_zero_iff L (CycleQ2AffineTopCohomology.residueClass A)

end CycleQ2AffineFiniteTopCohomology

end

end Q2UncompiledFiniteTopDeRham
