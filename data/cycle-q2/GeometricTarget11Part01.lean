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

end
end CycleQ2CurveRestrictionModularChecks
end

