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
import Proposal.GeometricTarget09

/-! Source partition of GeometricTarget.lean. See solution.md for verification status. -/

set_option Elab.async false

/- Component: continuation_3/SegreModularBasepointChecks4.lean -/
section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularBasepointData
open CycleQ2SparseModularPolynomial CycleQ2SegreModularTangentData
def residualExpression4 : Blocks :=
  addBlocks target4 (negBlocks (addBlocks (mulBlocks m00 witness4_00) (addBlocks (mulBlocks m01 witness4_01) (addBlocks (mulBlocks m02 witness4_02) (addBlocks (mulBlocks m10 witness4_10) (addBlocks (mulBlocks m11 witness4_11) (addBlocks (mulBlocks m12 witness4_12) (addBlocks (mulBlocks m20 witness4_20) (addBlocks (mulBlocks m21 witness4_21) (addBlocks (mulBlocks m22 witness4_22) (addBlocks (mulBlocks h hWitness4) (addBlocks (mulBlocks g gWitness4) []))))))))))))

private theorem block_4_0_0 : checkBlock residualExpression4 0 0 = true := by
  decide +kernel

private theorem block_4_0_1 : checkBlock residualExpression4 0 1 = true := by
  decide +kernel

private theorem block_4_0_2 : checkBlock residualExpression4 0 2 = true := by
  decide +kernel

private theorem block_4_0_3 : checkBlock residualExpression4 0 3 = true := by
  decide +kernel

private theorem block_4_0_4 : checkBlock residualExpression4 0 4 = true := by
  decide +kernel

private theorem block_4_0_5 : checkBlock residualExpression4 0 5 = true := by
  decide +kernel

private theorem block_4_0_6 : checkBlock residualExpression4 0 6 = true := by
  decide +kernel

private theorem block_4_0_7 : checkBlock residualExpression4 0 7 = true := by
  decide +kernel

private theorem block_4_0_8 : checkBlock residualExpression4 0 8 = true := by
  decide +kernel

private theorem block_4_0_9 : checkBlock residualExpression4 0 9 = true := by
  decide +kernel

private theorem block_4_0_10 : checkBlock residualExpression4 0 10 = true := by
  decide +kernel

private theorem block_4_0_11 : checkBlock residualExpression4 0 11 = true := by
  decide +kernel

private theorem block_4_0_12 : checkBlock residualExpression4 0 12 = true := by
  decide +kernel

private theorem block_4_1_0 : checkBlock residualExpression4 1 0 = true := by
  decide +kernel

private theorem block_4_1_1 : checkBlock residualExpression4 1 1 = true := by
  decide +kernel

private theorem block_4_1_2 : checkBlock residualExpression4 1 2 = true := by
  decide +kernel

private theorem block_4_1_3 : checkBlock residualExpression4 1 3 = true := by
  decide +kernel

private theorem block_4_1_4 : checkBlock residualExpression4 1 4 = true := by
  decide +kernel

private theorem block_4_1_5 : checkBlock residualExpression4 1 5 = true := by
  decide +kernel

private theorem block_4_1_6 : checkBlock residualExpression4 1 6 = true := by
  decide +kernel

private theorem block_4_2_0 : checkBlock residualExpression4 2 0 = true := by
  decide +kernel

private theorem block_4_2_1 : checkBlock residualExpression4 2 1 = true := by
  decide +kernel

private theorem block_4_2_2 : checkBlock residualExpression4 2 2 = true := by
  decide +kernel

private theorem block_4_2_3 : checkBlock residualExpression4 2 3 = true := by
  decide +kernel

private theorem block_4_2_4 : checkBlock residualExpression4 2 4 = true := by
  decide +kernel

private theorem block_4_2_5 : checkBlock residualExpression4 2 5 = true := by
  decide +kernel

private theorem block_4_2_6 : checkBlock residualExpression4 2 6 = true := by
  decide +kernel

private theorem block_4_2_7 : checkBlock residualExpression4 2 7 = true := by
  decide +kernel

private theorem block_4_3_0 : checkBlock residualExpression4 3 0 = true := by
  decide +kernel

private theorem block_4_3_1 : checkBlock residualExpression4 3 1 = true := by
  decide +kernel

private theorem block_4_3_2 : checkBlock residualExpression4 3 2 = true := by
  decide +kernel

private theorem block_4_3_3 : checkBlock residualExpression4 3 3 = true := by
  decide +kernel

private theorem block_4_3_4 : checkBlock residualExpression4 3 4 = true := by
  decide +kernel

private theorem block_4_3_5 : checkBlock residualExpression4 3 5 = true := by
  decide +kernel

private theorem block_4_3_6 : checkBlock residualExpression4 3 6 = true := by
  decide +kernel

private theorem block_4_3_7 : checkBlock residualExpression4 3 7 = true := by
  decide +kernel

private theorem block_4_4_0 : checkBlock residualExpression4 4 0 = true := by
  decide +kernel

private theorem block_4_4_1 : checkBlock residualExpression4 4 1 = true := by
  decide +kernel

private theorem block_4_4_2 : checkBlock residualExpression4 4 2 = true := by
  decide +kernel

private theorem block_4_4_3 : checkBlock residualExpression4 4 3 = true := by
  decide +kernel

private theorem block_4_4_4 : checkBlock residualExpression4 4 4 = true := by
  decide +kernel

private theorem block_4_4_5 : checkBlock residualExpression4 4 5 = true := by
  decide +kernel

private theorem block_4_4_6 : checkBlock residualExpression4 4 6 = true := by
  decide +kernel

private theorem block_4_4_7 : checkBlock residualExpression4 4 7 = true := by
  decide +kernel

private theorem block_4_5_0 : checkBlock residualExpression4 5 0 = true := by
  decide +kernel

private theorem block_4_5_1 : checkBlock residualExpression4 5 1 = true := by
  decide +kernel

private theorem block_4_5_2 : checkBlock residualExpression4 5 2 = true := by
  decide +kernel

private theorem block_4_5_3 : checkBlock residualExpression4 5 3 = true := by
  decide +kernel

private theorem block_4_5_4 : checkBlock residualExpression4 5 4 = true := by
  decide +kernel

private theorem block_4_5_5 : checkBlock residualExpression4 5 5 = true := by
  decide +kernel

private theorem block_4_5_6 : checkBlock residualExpression4 5 6 = true := by
  decide +kernel

private theorem block_4_5_7 : checkBlock residualExpression4 5 7 = true := by
  decide +kernel

private theorem block_4_6_0 : checkBlock residualExpression4 6 0 = true := by
  decide +kernel

private theorem block_4_6_1 : checkBlock residualExpression4 6 1 = true := by
  decide +kernel

private theorem block_4_6_2 : checkBlock residualExpression4 6 2 = true := by
  decide +kernel

private theorem block_4_6_3 : checkBlock residualExpression4 6 3 = true := by
  decide +kernel

private theorem block_4_6_4 : checkBlock residualExpression4 6 4 = true := by
  decide +kernel

private theorem block_4_6_5 : checkBlock residualExpression4 6 5 = true := by
  decide +kernel

private theorem block_4_6_6 : checkBlock residualExpression4 6 6 = true := by
  decide +kernel

private theorem block_4_6_7 : checkBlock residualExpression4 6 7 = true := by
  decide +kernel

private theorem block_4_6_8 : checkBlock residualExpression4 6 8 = true := by
  decide +kernel

private theorem block_4_6_9 : checkBlock residualExpression4 6 9 = true := by
  decide +kernel

private theorem block_4_7_0 : checkBlock residualExpression4 7 0 = true := by
  decide +kernel

private theorem block_4_7_1 : checkBlock residualExpression4 7 1 = true := by
  decide +kernel

private theorem block_4_7_2 : checkBlock residualExpression4 7 2 = true := by
  decide +kernel

private theorem block_4_7_3 : checkBlock residualExpression4 7 3 = true := by
  decide +kernel

private theorem block_4_7_4 : checkBlock residualExpression4 7 4 = true := by
  decide +kernel

private theorem block_4_7_5 : checkBlock residualExpression4 7 5 = true := by
  decide +kernel

private theorem block_4_8_0 : checkBlock residualExpression4 8 0 = true := by
  decide +kernel

private theorem block_4_8_1 : checkBlock residualExpression4 8 1 = true := by
  decide +kernel

private theorem block_4_8_2 : checkBlock residualExpression4 8 2 = true := by
  decide +kernel

private theorem block_4_8_3 : checkBlock residualExpression4 8 3 = true := by
  decide +kernel

private theorem block_4_8_4 : checkBlock residualExpression4 8 4 = true := by
  decide +kernel

private theorem block_4_9_0 : checkBlock residualExpression4 9 0 = true := by
  decide +kernel

private theorem block_4_9_1 : checkBlock residualExpression4 9 1 = true := by
  decide +kernel

private theorem block_4_9_2 : checkBlock residualExpression4 9 2 = true := by
  decide +kernel

private theorem block_4_9_3 : checkBlock residualExpression4 9 3 = true := by
  decide +kernel

private theorem block_4_9_4 : checkBlock residualExpression4 9 4 = true := by
  decide +kernel

private theorem block_4_10_0 : checkBlock residualExpression4 10 0 = true := by
  decide +kernel

private theorem block_4_10_1 : checkBlock residualExpression4 10 1 = true := by
  decide +kernel

private theorem block_4_10_2 : checkBlock residualExpression4 10 2 = true := by
  decide +kernel

private theorem block_4_10_3 : checkBlock residualExpression4 10 3 = true := by
  decide +kernel

private theorem block_4_10_4 : checkBlock residualExpression4 10 4 = true := by
  decide +kernel

private theorem block_4_11_0 : checkBlock residualExpression4 11 0 = true := by
  decide +kernel

private theorem block_4_11_1 : checkBlock residualExpression4 11 1 = true := by
  decide +kernel

private theorem block_4_11_2 : checkBlock residualExpression4 11 2 = true := by
  decide +kernel

private theorem block_4_11_3 : checkBlock residualExpression4 11 3 = true := by
  decide +kernel

private theorem block_4_11_4 : checkBlock residualExpression4 11 4 = true := by
  decide +kernel

private theorem block_4_12_0 : checkBlock residualExpression4 12 0 = true := by
  decide +kernel

private theorem block_4_12_1 : checkBlock residualExpression4 12 1 = true := by
  decide +kernel

private theorem block_4_12_2 : checkBlock residualExpression4 12 2 = true := by
  decide +kernel

private theorem block_4_12_3 : checkBlock residualExpression4 12 3 = true := by
  decide +kernel

private theorem block_4_12_4 : checkBlock residualExpression4 12 4 = true := by
  decide +kernel

private theorem block_4_12_5 : checkBlock residualExpression4 12 5 = true := by
  decide +kernel

private theorem block_4_12_6 : checkBlock residualExpression4 12 6 = true := by
  decide +kernel

private theorem block_4_13_0 : checkBlock residualExpression4 13 0 = true := by
  decide +kernel

private theorem block_4_13_1 : checkBlock residualExpression4 13 1 = true := by
  decide +kernel

private theorem block_4_13_2 : checkBlock residualExpression4 13 2 = true := by
  decide +kernel

private theorem block_4_13_3 : checkBlock residualExpression4 13 3 = true := by
  decide +kernel

private theorem block_4_14_0 : checkBlock residualExpression4 14 0 = true := by
  decide +kernel

private theorem block_4_14_1 : checkBlock residualExpression4 14 1 = true := by
  decide +kernel

private theorem block_4_14_2 : checkBlock residualExpression4 14 2 = true := by
  decide +kernel

private theorem block_4_14_3 : checkBlock residualExpression4 14 3 = true := by
  decide +kernel

private theorem block_4_15_0 : checkBlock residualExpression4 15 0 = true := by
  decide +kernel

private theorem block_4_15_1 : checkBlock residualExpression4 15 1 = true := by
  decide +kernel

private theorem block_4_15_2 : checkBlock residualExpression4 15 2 = true := by
  decide +kernel

private theorem block_4_15_3 : checkBlock residualExpression4 15 3 = true := by
  decide +kernel

private theorem block_4_16_0 : checkBlock residualExpression4 16 0 = true := by
  decide +kernel

private theorem block_4_16_1 : checkBlock residualExpression4 16 1 = true := by
  decide +kernel

private theorem block_4_16_2 : checkBlock residualExpression4 16 2 = true := by
  decide +kernel

private theorem block_4_16_3 : checkBlock residualExpression4 16 3 = true := by
  decide +kernel

private theorem block_4_17_0 : checkBlock residualExpression4 17 0 = true := by
  decide +kernel

private theorem block_4_17_1 : checkBlock residualExpression4 17 1 = true := by
  decide +kernel

private theorem block_4_17_2 : checkBlock residualExpression4 17 2 = true := by
  decide +kernel

private theorem block_4_17_3 : checkBlock residualExpression4 17 3 = true := by
  decide +kernel

private theorem block_4_18_0 : checkBlock residualExpression4 18 0 = true := by
  decide +kernel

private theorem block_4_18_1 : checkBlock residualExpression4 18 1 = true := by
  decide +kernel

private theorem block_4_18_2 : checkBlock residualExpression4 18 2 = true := by
  decide +kernel

private theorem block_4_18_3 : checkBlock residualExpression4 18 3 = true := by
  decide +kernel

private theorem block_4_19_0 : checkBlock residualExpression4 19 0 = true := by
  decide +kernel

private theorem block_4_20_0 : checkBlock residualExpression4 20 0 = true := by
  decide +kernel

private theorem block_4_21_0 : checkBlock residualExpression4 21 0 = true := by
  decide +kernel

private theorem block_4_22_0 : checkBlock residualExpression4 22 0 = true := by
  decide +kernel

private theorem block_4_23_0 : checkBlock residualExpression4 23 0 = true := by
  decide +kernel

private theorem block_4_24_0 : checkBlock residualExpression4 24 0 = true := by
  decide +kernel

theorem identity4 {R : Type*} [CommRing R] [CharP R 109]
    (x : Fin 5 → R) (z w : R) :
    evalBlocks x z w residualExpression4 = 0 := by
  apply evalBlocks_eq_zero_of_checks x z w 25 13 residualExpression4
  · decide +kernel
  · intro n
    fin_cases n <;> decide +kernel
  · intro n m
    fin_cases n <;> fin_cases m
    · exact block_4_0_0
    · exact block_4_0_1
    · exact block_4_0_2
    · exact block_4_0_3
    · exact block_4_0_4
    · exact block_4_0_5
    · exact block_4_0_6
    · exact block_4_0_7
    · exact block_4_0_8
    · exact block_4_0_9
    · exact block_4_0_10
    · exact block_4_0_11
    · exact block_4_0_12
    · exact block_4_1_0
    · exact block_4_1_1
    · exact block_4_1_2
    · exact block_4_1_3
    · exact block_4_1_4
    · exact block_4_1_5
    · exact block_4_1_6
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact block_4_2_0
    · exact block_4_2_1
    · exact block_4_2_2
    · exact block_4_2_3
    · exact block_4_2_4
    · exact block_4_2_5
    · exact block_4_2_6
    · exact block_4_2_7
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact block_4_3_0
    · exact block_4_3_1
    · exact block_4_3_2
    · exact block_4_3_3
    · exact block_4_3_4
    · exact block_4_3_5
    · exact block_4_3_6
    · exact block_4_3_7
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact block_4_4_0
    · exact block_4_4_1
    · exact block_4_4_2
    · exact block_4_4_3
    · exact block_4_4_4
    · exact block_4_4_5
    · exact block_4_4_6
    · exact block_4_4_7
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact block_4_5_0
    · exact block_4_5_1
    · exact block_4_5_2
    · exact block_4_5_3
    · exact block_4_5_4
    · exact block_4_5_5
    · exact block_4_5_6
    · exact block_4_5_7
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact block_4_6_0
    · exact block_4_6_1
    · exact block_4_6_2
    · exact block_4_6_3
    · exact block_4_6_4
    · exact block_4_6_5
    · exact block_4_6_6
    · exact block_4_6_7
    · exact block_4_6_8
    · exact block_4_6_9
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact block_4_7_0
    · exact block_4_7_1
    · exact block_4_7_2
    · exact block_4_7_3
    · exact block_4_7_4
    · exact block_4_7_5
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact block_4_8_0
    · exact block_4_8_1
    · exact block_4_8_2
    · exact block_4_8_3
    · exact block_4_8_4
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact block_4_9_0
    · exact block_4_9_1
    · exact block_4_9_2
    · exact block_4_9_3
    · exact block_4_9_4
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact block_4_10_0
    · exact block_4_10_1
    · exact block_4_10_2
    · exact block_4_10_3
    · exact block_4_10_4
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact block_4_11_0
    · exact block_4_11_1
    · exact block_4_11_2
    · exact block_4_11_3
    · exact block_4_11_4
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact block_4_12_0
    · exact block_4_12_1
    · exact block_4_12_2
    · exact block_4_12_3
    · exact block_4_12_4
    · exact block_4_12_5
    · exact block_4_12_6
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact block_4_13_0
    · exact block_4_13_1
    · exact block_4_13_2
    · exact block_4_13_3
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact block_4_14_0
    · exact block_4_14_1
    · exact block_4_14_2
    · exact block_4_14_3
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact block_4_15_0
    · exact block_4_15_1
    · exact block_4_15_2
    · exact block_4_15_3
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact block_4_16_0
    · exact block_4_16_1
    · exact block_4_16_2
    · exact block_4_16_3
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact block_4_17_0
    · exact block_4_17_1
    · exact block_4_17_2
    · exact block_4_17_3
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact block_4_18_0
    · exact block_4_18_1
    · exact block_4_18_2
    · exact block_4_18_3
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact block_4_19_0
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact block_4_20_0
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact block_4_21_0
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact block_4_22_0
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact block_4_23_0
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact block_4_24_0
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
end CycleQ2SegreModularBasepointData
#print axioms CycleQ2SegreModularBasepointData.identity4
end


/- Component: continuation_3/SegreModularDetectorData.lean -/
section
namespace CycleQ2SegreModularDetectorData
open CycleQ2SparseModularFunctional

def packed0_00_02 : ℕ := 3074245135513804443104647116663660201692189225819114778313877349557345948601742132861873346731757992334462147354753909234222275918194168959062804006487923968143296824282346524101881190440282757244496065768249628890982420065130185050130909842796139604314625247797867926234062471859558487403985614692904576849532377603547996825698252543777804740211666009858855456160310099466930641011486640746021399390532253386445634977183469332331007301074285828985315559094264359154019416938610885768159116585800344704013535914210507016877089759573158378755485737962124300839565117023046008473722907544718484542123155987664462638180011297060575444632081255697728137116939390606742461350588969667097630564034580410125626908492759250182065510927716873207144407155587562578907726172652058332716850534757567831200775921043981623025831452360114378769398144301875614479345080142826979969634741791229877210822657652177034621308354808430124258265900703709627342234346216815246552023622363754769585588262094509338409404058078785231592101625188734748282054885785579518608428850136380661262363103208753988443864990114844341687777690919795383076860022155440746347746769889421884603312138299032133407155964178197907139507385488581930987809825164493876025968842337928203011750780864879568687100553803708616794891556821443527901126506604785428848543245984682014282953091503629531005248104962618333634704220684348306085418663587272180684551450326239435627146534361252989251387104958465161081602142247303719843208276978679934576961455275853829098950000544773954751096190854181954315092552223182813704807015065894391544910483031321478992619251058537253435336663836094496580119714471522725232046634516896367752796160
def packed0_00_12 : ℕ := 494307126364651103513675511269288422660984571183586820063678565598700187440789968330878503246779659188635179587553344998356675484836794730965182182160553556848082299081190686582688881559888384920411650796852498375162105273695129485737387441022806850174938096209015638759302444720642706961580282197496612941533333129839700096301348554434986401036505559092022438741049275250320598477494316087474946137658830261489827107304320290865609976404129456968438154218860096879025437656820852477224311390522838404044557186893896355930968528861077455297031493387332838218513879051301963039734752108572595664201966476330014015229671292643960395118923002682786941476515845271068142296043961810273154812858396511228748204019192894004417345476481057912123375935345316429168474221347635434984823349355628477957587413918680716844085184862002109255982184751174598949305577465981568033927752507431150528530515570930032631622858765425151216111381654229613310264774177729995097403274459912108192731141512299108959587004194632397370340816645440321231929729607237574123367527603737641483594636665510583907357690879462581275491065754964550016874324915255444934588678915758788550066249370871869615624314005362732167431881687082846159918596451747373245595814968123807380361506805335763470706541663007450959682774305131181209546089010085338911290394790712697088798372603618354240554021287786316543695470821620365823849827997264600875723764190809893104279845867835725874767007223093778306276563730156834494645952222825707726980434533446416861565495977911790934369812965991631223291137624830497092937977947573529133275427052811305917353984
def packed0_00_22 : ℕ := 3668679017892958560880060424976981737966747523525430990516812079797103641897133363503893881882449844410297807452808680814723250563047115260823338320636068650357242997154305511539258637768954656451097993131200098325807248356701179679101058009093949488532491927318097426081146741146270999873636611595548183405188550356888417494724895412216047709432136434536936244975868161048960595229752305815181339392952707028522404687832926385813583819099141157962841208213004454444006001116160672740200340450139893091320813034913366780615588285071391935122670672787622344867808233990279494490601339700806906979830889151225727932593037172339488744346088031529987851087178515464915967804698959792405724130452457931391259630631782444195193155744921278214871100472372006941458675865073590095183912363112192333213876986943263572753137507782527139734086310059474370486456223560490804490853240887025963974684144141889510626432461250192694980890574064667148293293984855353840542058969290309047689761641847188859746197445418943811722491092654225084663109200694393298670555149704285668190124547555307444762174954036678879382174076947070931585704625684558628263329835670832844103777630040852189711672156183518341594946193257190731445900143337587833353669867759746263898022209136665143107984474080269488475846402694086238963335001758656041436815554541895020417148475107773628076641021129399187308913609149014192934517364236800
def weights0_00 : ℕ → ℕ → ℕ
  | 0, 2 => packed0_00_02
  | 1, 2 => packed0_00_12
  | 2, 2 => packed0_00_22
  | _, _ => 0

def packed0_01_00 : ℕ := 2871261933145704442355881278911294156100413327390046286261959260256116960183229674311323593754704015553520740859556979035240498503596596579832365784863720254186363399381753699632758713871174051450425721672169037247762086025441755309136857456307256329531712500854617817625120596891213740777652551052775775637793471555799642505629101248198998002715860901901040657598460564068234338323309549555003830984371592335287009202813153121896006200981681078463363918102495850299579122478792600918051046788456443993436242625138851866446732607795085420987805689828569876733229415665575884202103991458187062019987098856689682230387867616168517809398882025654348294888468447762529419702230870845030459436415355975562151968152045988523900203875834187595973187710096939058904333282786211463376638874085281254136231456815945254937176949807167415430781030753093200140001491662366992297563880730773050223390653502292121471489659398648979372800300617796971327932814391050226677149076947274359705561236532544060871483677172912567548631760484102589508689347283473358196605843274575831303630641413249797736729483157122956151582363309204009403586550447342136347060901401641116836308685995507573405085405593392842163011210656139218112622312114572191436781038152392877799352241978244721839531467498446242217430186439046891492503948863696403704624857265509109708514712318532380554209972795367519505105394821921582725452572596791501644502211876903523348766264882054171223490927603587050469953609593690591036158279759028530562368996063226382563313463650006760443447887183071193503767693529877754601379172949665302383824383723625862297786915229809840574518217399526121862927257793756382696673852724548766758916055744690248006269546125584015717689172469598785250873912002664475767787638253554231899285813542190957439971385699097765189933021194593063134045881441618377290735784072829653427222973853534299983687992863621133
def packed0_01_01 : ℕ := 53684598170754195088719444583158894390670855714384046381209007375808070511378539295179539318217220055787387437012115935064504166022297124809014364672213859650550099806705538079607856489691012355270225467694492146881385672400202965619701131896706854425141313052241610383594221572736304841977557069743230013139766472290414939130043244649621751597083299262644548581022097090475040229671437492764747983854843369649461383519046224083921143658974249470114019305021285560951077121247372450958943836769696723793935508683759891443806875120055022550903928745455922452353483091314154200669897075816714995614820909123899337424348128799492466718052715645144608823536753203480653537537956959016972603715976183447283589809621711718727954109909139470716225129714537254011536370679965867283059437798397901320396284244849228839309325746573279261952729665910745605016958946743511467440667734237282266852501633774678337446593378839096468714691453368338934884378800208356493589025198148225507258902463356375311483984583153420363768855697097577682389387217774063035462843639850196818142843805763773588467840187779157154045606572074033823802726306255197694951170175006350567516822214877846734006543943314757779895927034266829119184748980556211046901996787895226622342352146592066812186126925310028197897070057031085640283687329163796101682345678468346967493646692340181626495913203539031556305924020008091689973556874975155720771353182081961640136186626696021981477256668367146478984288489013567236382552007558018600038478181769660976626336085933714876536655698099301860781364012093992203757326073294933879199309015917344400396071454170812084253343126384815324815549663126020440050377979876771858680588213346733935452413133784627690881431487332178034357039588411936669696
def packed0_01_02 : ℕ := 31513771674941185032272935684538579832796199279049712448927096974495748542796547740430215651542880256429367292436723850005332137531213652315065116502978222302389009457700867646854900089673845254288362203253053552307175914183688770193382029695690061682567264860641010405903402426840756168762722335185791727840535765088586925449402682080652803821160810050033278754138782923902685056490806006833620459767363948583501195777378025151997360619956307866160264869809190958557876077573360020362881058427378479749273625057359716751231313488545638868694763739315861142007309679490614810378972657639425279235069533167995809043202912801122470092469011071281739132799685999176292939573793461046661067945056185442461780163881071678607687772617002212213074999820533295121377629308301633644841455502953652056563409226008084394632580103215912523967203112644640017295791478684214260893517585500479327432836331943169423967757411418424527901205378897809857398234512324466273601343503919910154320690876617398871789341056393764959679901738521620896420438155324922074014147779930903787186917753262413537216871838749329064457033648460926491746591747715609097650403447461981342073994785687379563197679089308349423007558955692780149078409198441428371873828361950923891993040332995622638242528202298414238607639339012810489156115114786880448785262512297484634690456781891247468883830295380153249889343146379184442162448543675129557634720417560534385524209071712538497860302529433085624378864206469481758459552983462494690187821372767094956181814148835690009072914047717618875264282862281304277731396117532671845615951614111139236475096134601216
def packed0_01_10 : ℕ := 3957435588152535904209639843006309741169810349287745408873510437626782283052242410298984680147411482210633017885198873916048009808408240729621546117608378310190244146868860155459944012102649654730694632745875519719564446879993193939486163911546638597786760942460221388420950205520994357105146791519284052308168725567368621730308638771992776699101358257307356478867721343217262538707574340152084387653531243615814908495445557797071359205344615409876734318523106074445603381231554782459735922585349291414118589754308623670030595565960650986515888719721313964664786052576502539388933562691291310365719630964905884987387252359374908306289316041014466216786258717370068387031682121615039417955079911628773222752655825131760106843371227447152812566652327782235510301007265452670672976720469634772614527508290846549468785880802313298760064395812888234582462975762203470642671582599958749084171234256122984047433581580434569649126999776741608295116878914726122502821005379526906962691417640569277745881848598676975193860290033609512866792248176296627361147757924942267822815710458746305801656684792018611047999992750981449719134670793091112294239348726243984053491154402537236653225920913754608551365666081360465241756435677690492824283475829603825472250665047706579537278643390655957765471988930854554810267028795772574300312219303294622616814337599578422497165452465090732907723278897144757320669478362917716835588539858270120532805060234793274802628452501742587919089336000826717807385690989990213882023781446682839696928060677541694995380514872661195923425167323723767135978259128887898558833622570083172303755219799647913934712784862913988997028932383971250137530634728248845533273
def packed0_01_11 : ℕ := 303702298438441637998802234123850806882908920535195742247124110703841395226647473317005100397754531079584235539678288714057956222164972485461371662306753286050408324787030978971179936352733687082014672317548852426317721147984612421636651335886694186329749774452210773407350676523080146515369618308622459049826135996834762309155085749539199895692114187768525521636436747568840558180319769926541222285676701882414396706303298755800988609049248265047043335561742723724704968213970143086562069637540385157045792224230775907518748390404580110817363915720464765683508524559609743435935539793565352798745203213033447339812401124993865085362934390003239128766090730927043396816311790025579857320272754936507647118007405020708781880282051268420150007629013354567573730845099502594787158891808381244536127569136210477398536796691428618220225879268092377693137090633103901256048279528946860467507010235348483809034170289131485909840063607356869119508294864250846259464797788674011443810483243976663455282691126703860632636002335267474629346633945603299054910043936679563952865413967021410720932836451022483461871766346776714258650241507996131132647819215761570980333099361743277074634207046460013883362691932755729316345514713195830424916398954109768522443564469330609311458540892248106548673763246875133706391686403470498265561491024015325793691591559574328566281458611943568987096481650598666414999157775763885742721515940197084580638338898912872186295083184353946188820547717260494567393830529444734624797329309543014149073145753104325519426904116627785844941454650977819896190995874026706663417052520708195345692360704
def packed0_01_12 : ℕ := 1482921379093953310541026533807865267982953713550760460191035696805112517789136101592025089806428616750184099233541394712481028036075042630709869880574954858946519194248314342955546982207249140252264794380541993150516149846183710294833396091858469282888605366606799338639545725797598770372525540197564064050916297288493863560182320063699887035363902605269183199112675842224742069656511795694572600843791366769529258501165019151404793861059760464811015773751273656422101537370751387611622130157340792613424747364441440188600772525295935545051824524124192327496667107451332344316328785113697472058448093241200686302705984120898217289111266241228829806686478206998708938813022982845350704274944341961300156287280254744952991473496119149442484407922967531189808605020293650388028247590236967219654324164225696546114716203026223013404777515134523140893676801694593293280430234894948695809647257918148454584726181380935582714273507561963394259727854624549981616977232768681311657050627670622410325374731450622688252684698561085524175313504317261107087759552847724923148813934839804957253900808903998055734374358807512995332588389410597097143153695524314541084958634625978138460877388738263775322994279287815637687786032023197156639323242149813170223290830507604534738904561744570063923163690249835253215969351970723969100601292297242317159419164126102647135838000066647785700589027582706988821120092950607725316469162955606574253068179091097923413727728366225147210467232069796311669308997596735303497706969916904852817395507656005526477334178653886324012191837302500328232285762219598628989601607945908293619163392
def packed0_01_20 : ℕ := 49137452496202406588468576206706203234591760379968351323774178545315113571863256892602958048779505004999772293034908695890628943933529918658697424540994259432339151678294983721297073621533997144256827663299399345605774715292970286196805386528940432819648095803392794866383091861823272160618782008324687736895788469061009370967707634307918450209121577357028494615926144884356539163629949543365821294737759916648873704746488022284767213831387033171264333702498637446506901172837416301763913957068951235090369297520296154291425456484508995074191859339532348435280191287296737185729621841496401847733276075674048184815492454964526170601955370567139773927236352394048239794985834344356596956031911959092907288133804893098544127316471502689471717183188428097998676956844992118840659634759646166623761580680981267287833217312206958791329712673116332918831806943179273368104860723577441356968413953350283145910178237518089853821089293749526507080112521345215067585963302578117512384405807001685299818086538481470170708032028149468787887015193961562705331712143089056087162266901389549667754442113809691806374342970748843175483963443216204300080341701391642254416515569289640072775021007787180239968702147143164742356814526556880516645584121292699057375724229324915283996496448789107075032037798632132732706311987251232047347381509501329208519216195295593237588563653070590623297431553350684192437840800153316227611394252226021871305133461049444264001460332066521900359263722343975236823731848082664164962646235326118681238052533451893141004502433845
def packed0_01_21 : ℕ := 51566822815510921093308906933343730073615420174873503021684655656230879404087622716835558164818056742323650676174699699311401755317225268095337907632612342590928848428393977204398503697041480265866551581241709244511872421098484191717957735860519943442048747975232140803785401097078601305828012065525792807510187793956264783377923907842356703895198344633472854953275463660673704077952015189329830875318350553935976344165830583401703018449478266780480895171068516935639329530044939617812038541193772791940485348610581005511037010494882625858836157811697850264327708438060388714825247697583214728125115883652658882901899153399171343696602539451383840948071010867916886130522684086130302910522605690733196839569576749537051946020415452441136064410931280697026090972854229818119984362648335185662947276740643122572436296616052227540792614221833853634973951403912426599898732598382779210692426302261326274767154030476406236787626044540766129110465635800266182598859661950622204767236343621721451454537748122859814977801671765672241500608146437651683581620101448331437068916484580772166516993290536264021967547122421815158929375498757863898428180040488224340303596411590512896323252552247712845422758190973323213426913187103154720080146511187499768254161460145755081727157638674027355891510230818631362204937800226935911243658998789825235563560969063756711536408471111754027162564464299430279650941590669305615903417264802059155242299614504151727155485300450179661709364667931181773714758115449882578386669260651822029634084248019207687677280256
def packed0_01_22 : ℕ := 6375732545290052023636250029587099837903671823912910642554529294714110563054167700791461024652449319994374822661706791245922532112971630615052634711025740753856635433834612019463388343076716517293057605243829674958005802392652525218757579789291964054954368067601777914647476053787237643101219360415688837824763578883527590963035736093155182189375910832549693295268588188345034587290089113198668718594248136628766444481513582970031824396343506811933750398570225975354816098972721800463907883197619200811193845331668287483037034959860761164401865312241823290421188488319115980296637574217361723434275504766980837843266876692833420731011511222134175578233810368052610089589055550008709917813538770802074212550295612116905076308408510740059036297594225301620603333828676156139861405748974571938742611373047013279059458725503406666569364655333552465951419720264697756235369302639840254999838890676494147045400783068899317101439214948447347611307345006994746343041528809215199509230235408623261064230192019702081780158554094125691701023287545721618403274922401206632661288942223343103491721901953373997561276087209422129509882861909708514924570240968065136781064096889600670386283321884187732475564871822972348503506018085530720524421114059172218825334204287719011904988076756140394123298852122095632185578601391816442840107294478807557876828031179800664828045729697961652930216767132853432774015843799081709070939999469252506427325181732177504912845127345253003338138332980736
def weights0_01 : ℕ → ℕ → ℕ
  | 0, 0 => packed0_01_00
  | 0, 1 => packed0_01_01
  | 0, 2 => packed0_01_02
  | 1, 0 => packed0_01_10
  | 1, 1 => packed0_01_11
  | 1, 2 => packed0_01_12
  | 2, 0 => packed0_01_20
  | 2, 1 => packed0_01_21
  | 2, 2 => packed0_01_22
  | _, _ => 0

def weights0_02 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights0_10 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights0_11 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights0_12 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights0_20 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights0_21 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights0_22 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights0 : WeightData :=
  ![![weights0_00, weights0_01, weights0_02], ![weights0_10, weights0_11, weights0_12], ![weights0_20, weights0_21, weights0_22]]

def packed1_00_02 : ℕ := 1676860983007529696238898427271087382741194123174062606353024008849461427347667057509848786353223589460573552957206896569762907408739406955831665266841141226948643769606084220070094059512367937530491584724304684258659014309855831920707821229929724962487008275757472898439145281110515269120545650024641420828693400542959032649209859652879498354257684331268944035786320617608353097157573618831192943814818777289843463064486317407819029443066023886782092190776155570869854606833994166636366260774499230978105344470721657905564818030430505337421213941814983526002732117880696930576086423193485711060383734617590368588395105118881767471373395965623421767937786758922532803357967871598850325591117829779772722825781593837363018961743286474470630689525867491985361811404516053409975509226034848497716488366396157256304179115154517134553561512112192087166728529418943982045869148436292460606330219450115586026711586013861992003536148240819476030892227674871998839527602058800057329844147094495247872996702087176227348684400176493221806003358677409461560920463216405697736128453138002189297015750467769866181982762160173435890180058484132231389560330031789211020437917790199629425008283020465970067284496598449267882716039174817324098992656999502100205686658219672718032293934992267345039839224374532242515370197227198556522908886540442405710306232024508291560452447473133008945482578202685551216723982017929631167350324282812094754718073014182543884987661286582580154189512110819746112836405994136779407609635963821380274069077196045584085726680236819173835910800820633764381484115084280243813036418905864882176499972370387852796063678445967915414568141280331236645334516726533355846250496
def packed1_00_12 : ℕ := 949069682620130118746256981637033771509090376672486694522262845949504359886316739195286726233816945642179544808102422396844816930886645887733391571819651087682787200765359142751427670381853043748797702714696358000931987977604080816846513800711598200861879900043547144622816194184888701361524195177040402328601011299711490784396068980959574117450099990116599422844155311917241462176460358815514293728159634571160365337718686160879182891596100750486754938030055937764445253417590916476771526099136153893183779603897343572692583243870384941402558340947842943069868309894018883487397310973804743257457854956910167830956418119761206364615734682007921067199449167755914590257768802625421278039976638040602933065334645079707203151667088683370647379258508902129589003073969892650671606470747105418684139135868779233041193748817977682611201538898894474020801887316725119657214860756178217399411295523658962901774402675936560453012680273657781372320172155175615037731096439467189067603648713889932094988827953111696842649283441434027495561807150199551469573573434026437710099692385453556763851443379356052225178255165220185795903756188159668304325337193906820394689428672602502895513402663200925921306896937638554572740708762338651624928411121620820722696703498027556534170003378202882734862351169575148028665604780326249544657941637047453632746263553164914541017450724657734279098435330165814886656867965544088846046833407263050420314784072904200373159997178388613887617174063333638199467005319891663591443893703575552939211172941629066923315178031874004708293531602853261404904153600811055562450333193912773597218560
def packed1_00_22 : ℕ := 1202845579637035593731167352451469422284179515909977373939938386818722505540043725738981600617196670298458297525511042890073196905917086973946288705718273481965704526544535500624797582902923223722670566841695163720653664360488958259366095673861379052102688795261870287010282258329153650310815542456221439437575492744352567556794963602224536553597967346747473148095597897771306625133825964078105451087492449922285847685746796840902974474517584890346533385413203483571998471283118498681559438256000912296888502777520396002858739205111717770202470165586741270902641246334695578133634766838318403600547854481593061299620161769131803368923617483662102184191239758945275024220047212612640030076973576793283779817257126946524616463426622972200217499341075970564800719348363244844694569033357631474030806861144785655600190614098852126278320721599088516472059629300826127725698504919214365187315089544610762959084923532173796697034280948734419551259071888919674288803498870409240102383872501888884243936450967258230800274268515588938025435222243712385203323664633904752452468789482337837049241161806875006248138383872651927797333539297665960549592202527627130714587104219484700146849386840009332005027631902479193702207102422005755267946718461611523193764122600215560032904596233233949630927795207228691135526653355963833782197713517780347947116859365323072801904736337313572900228406380608231721590339933440
def weights1_00 : ℕ → ℕ → ℕ
  | 0, 2 => packed1_00_02
  | 1, 2 => packed1_00_12
  | 2, 2 => packed1_00_22
  | _, _ => 0

def packed1_01_00 : ℕ := 4441483302834761559269253853315908147717826865806477849061468230708680922783433402450328684089307774059352396017127201945137646122750985320440056577284904014551352094838371315694098213238211714280953121094081670328395036721317196661680756467315473123604772759265461813742881543917209386827183825852104571820256914123549353506088589266545786638395931619588726558477293909508897251599835085810277845919564543968251551485559911022054447018561127558741879567831156778642273917954116496889361157387092575778027625788698330353698942753099892324103294838378067633471005706937132558379961715407358348647290056592028573697017714060648853367293627657424763072999672102861651152852722295852737382748927115538245250227150035706036729348813574071014714861373304171177004505026828019035787538912008705999813217266946318582584979923974845714221188802275148967530085053031398517066449087939977202804086275835881079306118816021969215898557211073276203491917127349194689296539100456199694034453041428325942797557174859616258891753255916642074697084644886446614037165926739997038520528992614873275595998082428939838576383962315353508675330137987444308821697432391531779890920315520114314608822332171555406739008221799334762599067442435746956247466288183682855938653873706720557300122124635969052646257765368913535044397149657171843472203835377126361919320114358817631383557746558776832733102179119215246955454046535963077542993428637209630360716020050239564366418523586017856789660006878412408216586481292410769834202371609663854024437534277277040801789868588600678259633435019232272522270591150117639024686596334252887748777687152422706649016442005037259685125278475532429392221080506459256839976345063366457434412449590373825732082827993561260078929918981822186933572625560582515611959048207645216840978077684850031375533720709964326677544545916234522852931546506591610930690909219483107241089593797247025
def packed1_01_01 : ℕ := 6592845389390866063526949334773899311135017368433128502955492133987115116970937756298824916295993908684602429764120180665922475831019132054769146628636894862534121105258679997980349842609322728283091528598314581788573204481518128300830787347165420176768626756881709371483917797321621295499539604143509576443952005118008916461980687042043204054622824286830951305609682794855578799683583067088677150413151286978030558358267438326934713049578577871453618037949556371001107871701663592526749612693661658273865809443034331689397236388079978624108458907495533207447439096068742473525093307654572214040563622703625462702240256508175226624063835679136781769582692596267103237701280612240717036203501558995236994217360641649813356071139624305628890079370246064581354897567826438361000402509506817238927937208628264815201713486828886119884789802861849655232049039731044256038901275456026888509951123047113330407397569856638539366395662934880970732223145758699032563715724993357211594719910095379112548199726503671783170336394147552181145800702302851671708433452246594002965911857058738397345746955848921551600580447046826229846587945646085499788576146876455148936679534166035613938939994803176259000151496600034546337761177045519477273082910066456270190922634649392167064750220452495823571029910682706846553843124264809668991061667180405166813356058846285264082312807734630303971430622516901233264941193213367843094457891481245832316963432948751218820994853778288313633049062751386600439218530609220295384267601109291280959890955754464098221248592033108390337156153259651273090639794576663851278328932117704097542068553459595204911724811031727174401173500010562041039743591049459264413970780585087199857278032998953739921036010126768137384662730792933982208
def packed1_01_02 : ℕ := 23884122158564572737764890961863439386805398428144750736823382264128606903591531752000406794770865804899529280904917019071763234477196152414449867478772017739802738888140640320437451127486212173858061074294441308734073276331034436338444218780071621385288396574227751819182315624171752258883551343944104646858037887610758968736130137461506303834883521526109582904741366879488730268659187890637908330505629214704494733015749876219864846930017160802009205443112248953085837729641020853326408635104104511178598240166431251562102757218895194272939855090829933821548067845625593573224946080472464495477590485550357203090013364994453016994535128655876321221421621481712091919108006517746635986744730436696403650815832335042676046829190262071586785816573586847038848243260013029380375778112260601339892101685925841207183049958517971375760010099999998111888367713568285804590593549994052586803801426693973267912345725151066400845739651843987694385174083256838793718754034621780808405232022604875876140119586795633372080440158468672985406503088242690457112665194956708156016445894844321895960738943987895246587213594350940900966647085073675178380918664240643815647914970029085748531206765085689710125128653540729633189885379797611673526448109273687423896936628775384110398813782056300874212345392697141851401475547654300640316905273975799538503021503548502800510418868113587191475432765002229268798908449864782859355422524165357532689517656987602664576563162968638030472388678410191810510428776399990535818650292847208461120508737561955504223182400957695262409214411501820309481079317567479510988786815818854744963693978599424
def packed1_01_10 : ℕ := 12145233356743989499126136069915916102210797278848597978956635480901832977612922483081241751125111797519465636599558312287764893405935465100913690867287383458843361925517618307221334845418975930308141254534202017344409729520115447937265936537741389651463662667933752517230606113348505327432527580508986863930041545595330528709214032501851093481314305507618502297123502766623884860131099482362475076645242312411500092025343136314482989272864927070640625318160490248273439484549783219607104018304988748420257249330183610856671155395239274171958150845580632176068084230810007476441814986214152103075025714465671561155263568189344540740464022421605779869488471002733668948388752121674680102154171878517045406953196777908287459611147921917626672817886087060846251470568025575431279737055713377865296123041271087027116173080213310452576693233593162449870124680458526659596867906091685673455127761384702041237185145211510729332412074449719372439547715386600766757623927202257859040801387968235766225549301730961442446611718349144966679646482041086270638254492501794732713740327854149286729829279994931857747712659783658056078349532760175833337927734568343400683449346495116964945497392861863872869534889976713433050812865990447674836322965333941482796819998877273430455716609030991139618712814788862783706923131839544270340528435223096303178324987298664221851879482944651080473331859437674241755990179540290054441048780732629237137684827296945293559648740884879405019002068642039131176174901050848993792387088976782279341688567129061576015298377221375650465814194969146469011427389720840762422460884947767427627603293915425866626670085528319349641122863383883730220016119097714699927565
def packed1_01_11 : ℕ := 399874692943948156698422941596403562395830078704674393958713412426724503766748156799225990174599241200969165626920751093151429645723507677868366296371966145957954312635150373078483932688800824573483973556214064908877765140484759994489822879060673108363250492927696315142833150121310019407299652198851783655072940884441641431146663472991142799175042487459409414761118974642110446057648997348856923338634081441830869622986981017592915602018317673873913206445548010650785928310814846947931561114758800883322917636551674051596332368833732109468914528407064350028987458848855527425391708737095515622839224883197062705362247344163924360876569735690502188911932475675135386663429838156019675062200899152291183001593186688808805313698986123229856678737276608975725010980347706664986523716051305670767725437361776421998099574638956381579861842220881036588090977936302552911313396820580986819899551915526509539080510584059263099181984648324716420437222256977066890347369694400355796300934735638836804487500936414728174113795883571661468936495133070969624473333689268161187823764985589036126512909549066743980946661502035181848922914087580395906504425247325439312585780943580642575460314191310441488799109729681782596669642727139606570411944375484289826215186565285604548804662562382095710511563684581999530105962361613434371599868604776974593437575702692004044258905228992846726519912683101773477340669110973754338874034794696364838644782031440066852747110912781156141911487613037751968980249106398519186802118995165626264093504197571933914604820890118089618985582530816856586387770485280543502432484788836388992531628032
def packed1_01_12 : ℕ := 1087475678002232427730086124792434529854166056603891004140092844322209637319793915915089345930090672256154085357488123837428374456271068775341382677080706488518267799987486710318601826216376611489887234890712861840365917102825599414739708692616325036813867754594694632343148083157679232498161280261321220983801790088664851076076618402587319886333779522008670248056175459599087425196512748097465305124712755685401514192612773797462338594267878038977213535086843584569937344905093309404696548222617113953711980654180512729374495694208061973743120200779719537554812054533425507702509524329616288387444820212201972933315497901924366803825624384626317072030256178722829219019810311642350314669082725205537833179087341919163962228504035997545541960314445801014718894703703516506114817235546404828993962906927728880564851239195597560844047929240720146924273587900334489216055781481842325245317472091106907075842587989520996239283001173177434197517300597441861059549666712757862321482486383896077787052565298879134275513621661405646869000621541417742348300090559475519841646803049443915778727203182636201408025210763011888838452676249624100473427483401799483997649516389109961638498558082180864881824002644260828051752608281624139320778165410244055682010868019667202557781296918376609946138778813142143594327893803046102028893124181074315843303901379560775852290060543408435514571981742588814198386065544123951369951441929128983512547342239942664801987549648592530654634220984381196749308913615726963053585351221859158990065095175619865057723817343766145017699521970576322048308027954773603888944433812839125414317312
def packed1_01_20 : ℕ := 73339481337615532221594889860755527215808597582042315408618176933306139633867340103363260204001625967115417262023990809002152061600021632469101199458340108848924565873008943017158689737417663682380336242940037371911359114862492145330791477104259591797157201234245534657099023098558177547925484777238273655091343120085150412955860083005985663292241212002327426226731642086600521089685872297320578231818329526249492004264971430812430429443539540628837761724095772221362411479511890764490549519680196836641160521335951819536987871669449287855835151261123700268692424768721841526110880316739820242717923240169418625382244086786777623722126162513304035128205047223940899507140646487492921096143412398018479948687932439771717070860060940056466222476837652926116958382384190566679620938539101830571733174575864089064255003793388302742948708474988622026508111234600708949379295000689632960708990145124454136630952775484995381850761744776990047633040610056850351326656407565625832034459496345548411163681581497392751712442371456233590959267834794440006447674575385783733389391929587184650483490064311939464744227646441089568374866891940200282893860205318592941596717124901848169102501420265518974688867309930877554548124681112400619521407359576483873966792889051359988837019090319574029266473344412948795558738253386154846933854644163758880217522069954715178670776251434633511771931868140905708716007352257986739587631714859318398376933772174701708481958299698513472174482989527618230376852815930556304979111828160303811302773880833189914175099371628
def packed1_01_21 : ℕ := 183348703344038830553987224651888818039521493955105788521545442333265348992311547437637540141575312861595202404176710041996095130016800951467543705080919083417530190788868135083485208705759264541112574426097727560884970045930055711368886769012462964911968573794657859506422013163963501268345003345495861994830447976681065871647210414983776538835159103222792348351851752149790779158497591224547115855783948611659555976645232054325799016352465498833832711750177798386722457060929029073239040413094951334257363572045103245427326376588717699897489676555703125416669885879621107867878913034238895096871268826573069118557146953392303862685515837088625891281606532432777702009964529178822226498584440504419342490854181116116042833654053910929631720639951120447456701424820971303218226797616441237773332933144609877022239088362662469907966246825672578297661601285361420805315184203883598542016218264893913196259624896187429558593311040041131539067671032577571018424635487702019354577571038370750999174244746951781095078875860788151949438557390055811042909334549903955525923820948580119216151470990989617508898188234522747977830005182066445280301629124979084213716063549461724851018872482331814600601504513867627018792041119327674792395422058358965287882728201643860857693164201132708732471958141549587873572483769504336302171983730718693093246305110322367514778944486482553117556174445671379343093577244734658173578645536256431679011493989590892892786086539056555957055414167119153009814859942427892928879110618638383091658095744208776384006127616
def packed1_01_22 : ℕ := 9351074399758742967999833376727746428925385341738935609079976298914028826374107231658092779898137100469102136969787067918675821604329638750814366828191491783847812257649210434493508415084337574063976377412115564827489685822805162996963504600212611287811050076908759835082302543638888543974807203635782544146155503538144219585432852176393660348462258881940862005443742551922063447818037257978657955520004852518198102048573901850917070372771994146446117974458369280033457410445958779089297765475323688558676981773106342410638547649846607545310097934401351819596756597352199114885344231741531715698375901138771408048389117779163132604836237153326580410436155477800981621211139125497202572951317916071289960818523825804273508806686055971639102951248379381517125283336251124826814774561930866387320457735862716403877886297816071154104091679376785064975430271732908616377105749334100322741286582177896932870891012517190887523479434775862699463542353751175809342985370479538409224302889285445998004715412834484885178536733726247776529411689471967470484283428980555094661182183055601090821806186287352120350772831893123042166513718429751888115608135932177816256460599675302646741138412905850745563160579697816642126496939019243428312759206309567544427236794975580717593506871912047446185395903366149400376738966996139172094002407985304399254317493603545091509225655679259542286932386606630354699552047355845429137654292436662334097418903094825106994290724054565399401425446918912
def weights1_01 : ℕ → ℕ → ℕ
  | 0, 0 => packed1_01_00
  | 0, 1 => packed1_01_01
  | 0, 2 => packed1_01_02
  | 1, 0 => packed1_01_10
  | 1, 1 => packed1_01_11
  | 1, 2 => packed1_01_12
  | 2, 0 => packed1_01_20
  | 2, 1 => packed1_01_21
  | 2, 2 => packed1_01_22
  | _, _ => 0

def weights1_02 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights1_10 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights1_11 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights1_12 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights1_20 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights1_21 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights1_22 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights1 : WeightData :=
  ![![weights1_00, weights1_01, weights1_02], ![weights1_10, weights1_11, weights1_12], ![weights1_20, weights1_21, weights1_22]]

def packed2_00_02 : ℕ := 2969441324075833837089715964959217240270864593120735865416813349004254610324281874964875127707959856735784977010884394879673250025182052177873178253199442945164985208861623830924813834258815083051173630640338650789316418944274832999233456578187790816282025484062881787647518834230870261381995652560981917715376803047702251682439703734071033388989737492547150257469208984552538380050792629690188117270216070585062518929016321627551567452706351819260080724995278391481755797511929364796604807808404192884836168474452706193320472616468999051787397196672831423378579456959332147072484037490296336432686623122623190361856533926319179714874702075732735402169407848454272311217235222897646779290611484562180987017216887458224165834860057806746130239572133127276341997649400112012772950988718294765416646748903158207010642347114758357023491119660051267637426912318696109961073717814722926749745894609593212909709900491979407913325023882687528253004387375346268370911403375181720555173991770448169381751780115513114866087122327475822635753907884123813494209783934401215091106814940772660648234226655262971798661771211476614137479817608356617264454610168110856194253942065454096604286125319616715905732998802364444533142146169910824788986144774693047800817853891063759735853768978988230832897006455705555397385317767586981440822594122925954053723748180230620545591600373291952243755382813737440423509459185910520913336898780493946895177994146777905162468633309784820742425385950077503583181732961966298526675933503346051619444816178218607527306954242009598822750736027857565707267176053327264605332125154888421337347901007781956925705345362319630174357381814323566065097405271292559566591232
def packed2_00_12 : ℕ := 889752827456371986324615920284719160789772228130456276114621418077660337393421942995581305844203386539543323257596020997042015872706230517565037924205477982435606480161111856047892576329500143722372702585712863574194741550259014280419282249363273459223820222728274744657885388216984647323770891304415998850150038435862004598451603727625222085892855271005953270742011536265413429840991869513619303151131048729271817010589367069319091776386126654010277809148648305610146714353292728260211508223059481954571488687940663850372838129956787596008478479660553648807998245659667306535917905612778594341894220280080832084301398406218714474310249544134568565742231472946843222412846822628153050890443173622471175983825139449997528634721745619908434641235844523881816305197936805726706711361761785433089730035053804941204229348795104725941928094920527165787185068381004029502243635707051136400630921616972805034363224837990532528559717350317870393984552972459388851180516974580396863827386864432305124671960505476670488085368225459064393369152072236696042600162970384750913485903343951981602159918248221420209730042705699763689257830613401727415206536608516834036529620995394968242236146821898739260646425594899690771402734601454142582157846112205552251128245716354946653701174543623231112855627692024340243299689142482789256131959448993931187151785483476558033054748918422344140901315063079888690432372996491128794490583915420203799890276701289972041749232970329723878516727745607878326033373633946524503602466146418985126049178057913724020115301272399766427771070425987327370128402878277641117720943356321729081257472
def packed2_00_22 : ℕ := 2165122043346664068716101234412644960111523128637959273091889096273700509972078706330166881110954006537224935545919877202131754430650756567389763152681119014892893330783442677470516859267034979902626914475779331558431049972790514321052867175123086092928060785558859809361927208868351991276110799831966915787531733638653469051802747495459803876814059977331635065722739441311306238614603624812356053422634673154528925685591853036174709428490757151173046954914528952085626464546700447611487020615044965195763859179979452903644539053430184638243091955200580798550593250298868496729409546194992617261743166927356501580328330316657947752692563393280237798999548987296103436559815855370136711402239234148228322273655484300670324293346432430976417426956829917744881237256410034618162927719477948981627776225521901364495753046054990565784334419399623055085155246387304360504346301265759120689347273151976445990613577545608552889203065162956592707978395774302550913929176684936728181937602542418686690614811981631569563434739589017407656646874978170793069370846688598149678436130909997345665647850940269466016471411637567107667741287686914012983834881380344988551175077075314611384326699606961854193128921778495484589465459424351319333991461783973752601243412408687962287019644622030877498173424701556808691528221736815278020945312428258418729641339702108889885612914170097376829247756006031325526665115750912
def weights2_00 : ℕ → ℕ → ℕ
  | 0, 2 => packed2_00_02
  | 1, 2 => packed2_00_12
  | 2, 2 => packed2_00_22
  | _, _ => 0

def packed2_01_00 : ℕ := 1884265643626868540296047089285536789940896246099717875359410764543076755120244473766806108401524510206997986189084267491876577142985266519687723963395923920231734350798223984521103814575346215903519826888337070181601910530074591147101166122501445684334313021342372429055449780847865767887575347560766069860556024368076322738831849887516889007397644449561923553310580932589816273937574315257652187180826444781424972623273151409377223094974381909924797935522279564353301467685438880931595697851457734361095485075045202282082216180062629928967620876304000069593628326227329867740048403834579385448564244573175222326375138505573426420310353007929193163944776436973462432544463529534850254684412674905447564821509496471112196530915797617361664405932152070643752877169799667490507958413774314914142041709895974881819286422527376071288603920345210307800891382039124917794057998820342518945082384771446927402247137442821051678841557663977376076970039593111867641838584250538044396216485370253362412275878270513457141664418826969047666584238310607059284649217497433268864301896960665887452530131844759731835494283020826921400819941207203235800661345624874030970727591798627223183000350962187250909758402069082456481011225503675405270750741175947256777992330901560952720521685550464054106397177414328662179216546847019915563193193045042957540053554594149652864151029112840309462650438291583830499658912020783617991480019275222409473328500518748862235604127276446333235367707959218139458612817665814159113809191922890630760852139438219849518081968042636478820170387239795279303939609170575175758964173707104814369389389595971574368659528519215549710758776659250697689527990060579499648601423312584083814166274579679161649897855248651842251588112484131270334262075939678704567320087512440329653046804811994729572149940308406266082570349430808415064883867579090825028808348170611816392670227841679408
def packed2_01_01 : ℕ := 15069360890036265288061598479483198425451468270704293721041124877692500203284463578722977630058368190743051012595356127722579483082784124789850704496110984365522449389099216405172849260168855611113449238112872775085343740455178940098060298173003809023365273653874011939336220350609251740605862572807350829179808589755933696757697888963763231316965014187141195494388914222631031083713695286185814662773790146463531175527693271012140299531544594652441901156880517104385346247035099249440159597704111908870344610482944450887199135210198349981135092845080995984160500727198980551299284129267349912502730603436053183568698770510496466367152319877608816080114400930128999094671380677860769414052758885276272589970445548541830772342040553889187425346646481034550425360666242284522890296214422502614040300195743948887629024052362486071341196014164279677049471991222382300011687862795221321817162606215187184081856174329082528000068442849491582114086151997748706041937866711906909357707482822999351622995020846789838639618497541738818109229035671644192148923701248014725493704797211949954087041682227280687650574867387182208378794277872726327632883512876266910315198038967916990479442622248452258048849352276907534497820660175760066544151524463029692055657893256910885471691170343946684552858008596593185130595407855787256155348493204928061894899166805162277971480971944844423559115029877830034145678991958391253651877535622993656218758154858463986672982506047977324330375967432874009794806422364351158938469741017564308017582739572173344751862837718056222916586146416358241436816809582299838569629730415471149345132555710334986569323840241918696335478127952264902793864910846335613415736907568434491838629359576661761256363920829124483272499828029614391296
def packed2_01_02 : ℕ := 29855152465881366530820095050901808936941189384518189964743422400231832803591986955389874430703711082911345660392359654632960471666186801256967419802182154396605447292136253140029349757429366249171464373059670383913703488354988013888257449190243531646120743996360328453902651016459415203643868458923633227110796619273979282704150245815791616409982215279994068177447962280764571172736466294210022769258009482158877151877382647892307131786772520281104682891382499453022325808497035639979466047094000960298695387065597211409017343133431191414651678001132089854434679683070431304076323938930033704567073603512412719854802813394094852393935027482847887317483402205731139684178327400669147997558819160973785452125772182651592639261931362119111708555913990950883163125363780895562021892397324106958714174704214853113669831700412593778616718947004870774729276039203078406088734522264861334718535557158430686119489974874072107096129910230162001429868737576542150652699133409236083524322996331028563373970012429443865162250244499607614703900634883294643440314431967777831300202579421922543675726544714876658151436481679831369314374749767107596945652391163733703536937086482131247243468586855035104542003583596688983372422431419674669336700814210628483514737251823334012216135890950342345794953163644879908606800053436934459355489141679811336808970580574738960869787929089972958730037413750968626691106963766001362247948949364446043838014907258631201143981674119369629897973850867700402068574647617629353169764243085155375554835326903658457168761715316368828949555473041056739125419997979290653016474202479752351879103414021120
def packed2_01_10 : ℕ := 545853184572763572994433081793973757402732461970723504672208336229566949072969046755039514011448637523992406664747645115874781577861639052230386410943817127584781543447696323851049375123770020033691929936865019281159653341664366920286793344723709487260494343429218531856319435550116074867830330220179962490392184331165519220904529717147655740653235991472456669493255046833921342939404455934950612032403248431393775380241872836436606090203463978232516058193245983335402721489598977153129203740398664105671000616610256843015510705158575115281754527309941073651193956429260886518358879297889378826378701553797199021271648063962066758382159994810939907395205510514861140637235108427202483402533446944533052390409322198142872177769181623154686299731344019930215605115655162887397298578761823898781354355079961752667207403309719049702559042303077636603142039368454120912729477466271359699967303409906140746047778382512936113778629798167961913922975606159891419672522279590962054584583450580116782978064075401782286693392127831460207012908801666483806709341713113732328863368393012017873815319758175931844649939893734112608820513674006130908473630457715160961729185112296731543755610449710432737614136456282417352145471160238187465565178569784777334919951936166469576682463688780108798131057334666312215919379838370822093547762501033765012885373992833703491039329071079233874101825979852335773619334612263872598085714180041700860611462003807946626565743240820120574599526028463813697503939101249734912976216924905738327325112061897537084314330895357260743679243044567120225563560913809669046455691948604168191160183382145894143205109723898514928470449099586489783925646844701307830334
def packed2_01_11 : ℕ := 293578888490493583398842159653055779986811956517355884172219973680380015396454565234840528833478634814958275407327766237637195345182957539784353610387842552261880738270592826422372492410218325604557761557493159581191778071712800092587214467314725023601536332330002698119450602946668924530861158658320381512175137236608385526779367337500028118135423238737766545313686057596000869452513833027969728013148809590503410138576125527341501796132717305514972526166096074043434593189619306556488776338002616434867623399702103137491075302050478450622069118316781312227547118297358352160959623492222379832713815947539351929634656682717896910327066135476267016144067918271831773242343645091689443613256011446787169039388747812722696850287909957456161476296859600099762969546516002913825390344694400077191085967554665907786336408873448857282617333351470958765624679410368110972667781426092372133247422397669516843878558644533219181435994260999580914176937430235389373773941591974885348892906464662923907059251231568610312942632362923673342356371284345603062227082247567859683260224246377556258928080439713287982401826106866846676246659537160331213584406756313107642597628548833592625965315519941500497368503619858633643076452586214501182155158459459914149630285089438973053703841055138230992872849510010492765875721682499472572095538678383643451405538491464784722939142139482176999440289667260955258328176222040793319833907674677923788778593404962173292528279449476505384416587213211569478628067660687502520619883410053886425070569244215796957007287870668288332983011814542427007316525962668927136632756242485345185163051008
def packed2_01_12 : ℕ := 98861425272930220702735102253857684532196914236717364012735713125184760582662570778306905272618422178228666202001490495607148552496006754097956070849262945759216136846945493720405000914657777526232350073607884014213935638233879760768129067054726531164008020166379593791368332748256161809234834344152384460873596141555696684100024855509613963368326477869797780091418138487451687674270155958034989662106484472951032662773814304720009699297711499675179989023909401633188238509934519130646489727166992480184757367291108850966373689201866564421813262272395694985761158984420443013820290092279360470681819731947526007779548919489129994387441811710462063306291523077851675605393813305244067552076668477395766257593123629451685119243484501856191491895279277852725414498335658603217317002254850309317764010799157303081821512024050921485541842854974137584900786670762430035396502190454230411295092518857896289039022357150504119124094643660154541772744965142872363316200501255286751567654277581736430652912366200835240075801476414378462407452451829921652822356962856917355178638170125201668278102157051746876301795874977523305991581475752105998441970505213554034249829533199649376489565063186662502762850856690331411448556060282716674914544878213443859733797171517288312027612941694703986081075025210220812873714254313719335819610602065133023897958801805310238229486824651951096374036585164063027334716395774392545959107207891451713696605717594094056852070868388151848633166567327261293102697538686307343117245205336855724550293244103176651897127931696391797971712106872444473824643217967723211092136938957750445023488
def packed2_01_20 : ℕ := 74806270964367842866026787657970637760124769533683161716790540471972262398410106702321168236072216624126109265265064620962332905413662976678411417983183779337947635379081896664270172983900522245028988636428935352434893566547635221228493922930315295771022554459150436625843020462057480179521192675230180663919182924192947927325033101800207069220689156949054436904869820793018791351924527183286144921732179033595783326476404860671047917381967360943467570730591917212369491826201713272366544885160900932853521707188488991543140425990231475614098879235962140571666619818724423014603116467025818884485308981022287397836553662869584701993498667841301735998840234615115748778326920291713294129929927595402808540746854936591504455369018054529987055462287327031234032428508014137777939906057556254036523035181895516445919557735358056935654110916557935778469441315414328091660561717865678860164730453468220616961244918368119992706189248427791339723901049585076930615449500321817006887202201881437886635851629434752745765748709705205243313999140332541405734474058924221897619771592754933309888210493381953324654031513870231569306711329547275261700432083426110691729019337208920574951695753582667983615905724914195936726234597494739141988886400559021147064995952202388855179512667671668155798531199011114118998396250045156250656295933142906903319694128054018925917274313445652186320867439952076914476880111898951563952058758139615459156509829757748477754113560883280133438938449129399689644194622781681191326169758611548539744538519962270203382614458414
def packed2_01_21 : ℕ := 226321055690297931465077980429675259767534344100833707706282655380124415162384566368333838612257026813531577967655626458088929926114488673971936313032873421857526646574513408378138258038078918629893231011452985856546870052912363489121089351373895217918314876563572745873737741396617166424313737636325262093894012594939622607482403283794292341344196828234017754215177123940475487124850871586721951549076209269326304670689808624618078506821523864123214347183406420288798887640943202395962612745783348511731325304121821420188197277252956375978364877730183790457502581019932664735540481117992776768055936360449581281593052483957405153940338529169620616328510905356274826144536529564037554718557201428367918486032176660639501296412031414154471487147776799274423144363049948572026067210470869457587309374366252443011769503275886341628628951043875314370482811124175517371279506623374442597966250489224916099897501471459420357933473941296699571661562750291629043626150318243382914819322233977347699632562834811051880695438350898052791560035487826025147034171942834126247129493593115481835531980541130053375752493915475082581885890169560483678054654642943730100588268472176663135222346015051685685928215288888401938141492805098001745185112655272674642821431587935426337138260496275317154651082135394845144234243607185567297792631422372712650242103773618763484356331220997132052628271537607726884046145852781380467089116099831544488667256550742059397334667441675639893760540669807837669473403013899350906170693225073486400419017541107369487839854592
def packed2_01_22 : ℕ := 1487670927234345472181791673570323295510856758913012483262723502099959131088618115105723970600539397822915681569054868279137392124208270350688909136411356445498159142503345448535850848383484734743497557796588828028273285454330439620225807061384553823098664085608124373531256165572028510543467477305944954584995898396995707036112938459888477490336903912936532808233887626153140525225670625141348834006606016357614182651908699342133491970282101082044796058551443102583433863462712827037074157123023015521813347871537874856232152098033937664355727350876310802042784156642708566113684983646159252604114297341814323083999692961097178076268664155586497375711027785697916827269192682571526921013359518003214202794894972871795746803688595313603757506846223558096882171352353649926480080871772608294292518004644597653436889713499546281501794701448934637439676214882953251340917403492511502076646196417383655920515578514249501013689965547604337915650845741719656026838206647858167499339022218291536525273410255321754613136373980437942242263722800633510079067559086735251576643659219631563267811696027032491337267573865354495210603043523113508980612960413733866254580701769016598603455531583159977491443482618984855856125511506952425732442185832030973012518122709367027151256866667804191144243615154700278563860653687460852825844661178689031626205324125378561723443981776744717322108823920297289027144650281384718969483986646453395677182707833005327800378148986069875069164397275136
def weights2_01 : ℕ → ℕ → ℕ
  | 0, 0 => packed2_01_00
  | 0, 1 => packed2_01_01
  | 0, 2 => packed2_01_02
  | 1, 0 => packed2_01_10
  | 1, 1 => packed2_01_11
  | 1, 2 => packed2_01_12
  | 2, 0 => packed2_01_20
  | 2, 1 => packed2_01_21
  | 2, 2 => packed2_01_22
  | _, _ => 0

def weights2_02 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights2_10 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights2_11 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights2_12 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights2_20 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights2_21 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights2_22 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights2 : WeightData :=
  ![![weights2_00, weights2_01, weights2_02], ![weights2_10, weights2_11, weights2_12], ![weights2_20, weights2_21, weights2_22]]

def packed3_00_02 : ℕ := 2655029889761922019044922509845888356006890695025599126725621347344980592743553478686420335100529607282509835984201636035283452792092877105531258822541775956545572310504550662582013258917813869608090629564027021770991603252414801149216891094082553384278135641420682575247877120299501859529752331719551919648684104760443042327421142266539060467785160031400959251468465737583960148722663842637591984762481554683549521878891719860352013332249907770676168605348531586279559765830047286601148608878086332571484554943183082654142150116032084256363959674276833439897382104608273528687353392236393246127964387447391500070689670375836465901211419018434590903735119006616895946588141327017638071101175694223674373283719304937583994867772114963855145613167270913653020552944736080690035173728781496876647682624301248108709607491439386771568874105487817011756522686894549820363125767502941249105549757333201982946744082783615027593650113461739152923686246018633945256148383497888726149952609732449249619622756434853357084003977459976702705061348782782173808463889011625443278258111468223910736048701637974227571326211809760283765841167069379083803461471889535695285799679636940981484629319511510522958274121802455087815921185978364191311228730771100264511997460115399989865944422829603532514253541253793252308679676810446298210229584407169853538011924012411039012987965622646327430488080347437649951606361088141273114123820160162749293124146570247198595266698132147223382818847825426904464911759806379779978020454931511145276632001408960537599735114011136521939032136991087847958786328962465362589730512902422876942863424448872784654128854069781296200899000060915476219110461963766828669881344
def packed3_00_12 : ℕ := 1008386537783888251167898042989348382228408525214517112929904273821348382379211535394992146623430504744815766358608823796647617989067061251313488255967437101839176224129603263621168546390864946468875764972432269332017705137910085180257333346734134274646267618512815608082269350191027093766407770102829734313147197294060399901704668410685627413325420002191861854098307951890447513194985721675688980067751784775306374072752998603463425626881598284265742316718260919086880185765428671516319889648360286716003391093762889719475556392780090698105529561273937975736870735277725706675190207569811287242058136878415182868808597379004448493927676974702633552998365959292328768392005402631624070981776585243146171040122462391979009549994378002087230308395442530631827131949485391724337792195820964814878130212879766749083321204942099483013964315286912808588519817037555731136654641332872177204343778513628435317335688934656370507992481242639201145169087148321308696873408212133403900152073011941664810308799141519156927110016096274538135720999194037047132629664977944205188056520681654443230226541192275185418272549799616885067867948758370362250474810958845534978099922065193776192456629412176773551914540012139760884334883839219398022210764800537141895164323497267630940324745917256840690189405052679626741720436991250161358745627137052815851862164065437480982332868934328274435785511995963389168007114252831134125728093766734327837366756220255050584291433033083869048262402830518261661637972257520622342074198675303282349478764189412773432128203647985213204039475197041884711068689315187028845819826586169225773064704
def packed3_00_22 : ℕ := 5232378271421104832730577983163891986936180894208401576638731982661442899099190206964569962684805515798293594235973036571818406540739328325886878717439028967268535282026210260497617486648233320485908968696661645550714769974544969572100050517014225651231507051966698946104279399053275337175488187426766720621433831202867139778566204491082948683370682773867188457341224039183694750497304498076973381981782308326282843993648861680487913389243362842035621656848550363062990754160492665985478077538645348136940691793116242502268626040613874996324626684216090212104781065181302054793231563829389470178752090984424070594780383747326968113901476127335925257280931607574767176632303548717048634771976046535623022749374811955596038031140572347623751469162884031487010440787416371981682473879196863513272445213869946203358661462141852759862964777741701520904980224224150098504631495373372198479441325418523084511693574904125441758483693203771880436713023573614944854901526743262561151747759480671394696714276335084260086853343707173938367192753944866503127907935296790106418234059648878321706415624026437888256364247394200542401603695498966079392539273927211187561480809375491904053578337330448841569026470119070676146041213157240833392297048328665722374546226012215646463450798203177078826235733511012987697177300976527473833078211145528501444026158461756545950220886323752026054785171265636013987356590750208
def weights3_00 : ℕ → ℕ → ℕ
  | 0, 2 => packed3_00_02
  | 1, 2 => packed3_00_12
  | 2, 2 => packed3_00_22
  | _, _ => 0

def packed3_01_00 : ℕ := 3454487013315925657209419663690150781558309784516149438158919734995640717720448201905811198736128268712829641346654490401773724762139655248963255366509836183974400989683476384642939174372755000511121318696163982702986065258052179789265651377177516875334387526115073892305390711380527936020218117772807037952795976553909971643154869000504590688399076468931934476738780966883564856033753795383627759901227389361627679238979945867684623710221595464908479701604128497417284564823351708934640510914320156531147183010512493636419215310355976140917114250097412214007373767147809557045539646195828090910740201331876250461102281290863032184898429392061311559971505176749451340496310568732772101800290140708996640280407877343959070060729330771349501810841176222444549261099778779766079393363258405718816901114006300637528053577741885336376300751251466537024739430316640652564114448688990032146500294536885071604834628544042995485575258260720169123920238646114734144407811885513592928473455939491716164480158654047701514789544067178493774893838331365116856226636105279679543166953988988635793227485422043778322229851345560722398408059418213191705948326010078693551480766633913140217656603336920366864842891868806098458138722698511254744999497065596384351748722368773116894426557709735850716223751999249000009513556042184619332619233920130815657874417433057584494416190531231836343769081176404739968906658617852528141300014124216543353815137650054072923441329919589361690339655876627663217565809262159483328708271366659761959384425157614249625056375822241041265096701470624713338926167424588540368851059091317485573024552415593157004039896642173265434128840316803702731512386710545847458812923747156599571173138571857465321636540654296382638846632874125979017008476861628465300337937241210730400173936315412727011683878779816870266310691485459580337841209643144262184501351451878151516115443472400469
def packed3_01_01 : ℕ := 68753959060790460376781043062642092816122323985088340102250132252337947099777782284510214038700967661163210524206788655715653669636121327292884894676635051883587346050835289836058304115878401759912885773985200370481277853034485893925915385168691269507920858194411341198289454026501417261420969216092622802288116700470662666152612684452153655036705365038061896385238473880776486781718765469968104812850010494446798427178356209675598922792969305474197889490545010979371095004955414977993369546243942020139971736374340367879148727220250885132174689777388453925046289636953932131023050376039627864615793441252516599573478638554233643330483974781491686089687677020671534480358908804361341061429567184008858491481393252113055162351257825788382394176722829710800052704741516877044736001440930964622599882390448841218023830991661561825764114292003817964936614297075414835278091925171341413086146623176891370230720424449881133934164326397513754961487742851912763803460787792614438146866951084055479812963180785908680536528758042147669339020160419140137363709868614094636714101190409943805193912815381738878927411317635044108983139173858208295925005766641666762206535392585968355099294487805210977775045270424643620347874475460541502296425146574087806336609000144593763620717083874132873146205987007160583994159376430851474581954223309059087263092874430504342973424666043838316080109433920361134024368366993902619293071942434972190824858370954264094056973091936020897838584474173543793399120810411312844041306764685890734485254070446400319090112718049015515842073436346998394927516696901210419855890687507995822651596409358129534881497301936853428399178897297827254792985359663328469204264114367971064544686114047714323570332240109241762822099139478172336128
def packed3_01_02 : ℕ := 27864808173310082901073114264184799553462659786687120170552920911154577127317119325351924016388529629951552799323897219609313002777222333078062594996553758165512846694053796578662926752968999938933319894983565815209488347646468602013205910033994358702732685440430198463583833855823420734362891296869980933138074657775166373600205670112038931488755643015775123713569079945931824672563224368736123482329961007263015318618258713866031388935164256883392435418937704930855682514336496369441476954087111377391065740039593328751853072210569637748565740797364885700467498544094597337848537456562171605112749163229474642389188102018824046879442109950091188994992133049723058591392884391990471157415739661223088379089120652570548460983365058778233852957545300730751487364060515842548231401155728434685753296213226390666440181565771848244389612126009601737157298789952105652450539085348576956518145920711503783941716607938592563197845957880185864947670990388947291138370980538763327893402303163027179527899315596911524110182156771481991509342632788038958015389988804665980728312391426533952412827161782682372144842045142266111976210820211795515819387862530058719797725958429888198408355926304874866841527358833654484495126974924310987224190963261214834255854248427845237120803300530710385789398411921869508012770236351376526660044282892704123150235080316506966781131765840933545034496912671693244589378214553562674144371297755623168872215495587256254939993382699685937574925566418211532076654506998500589717733366452023464518439583956024624843038865512447286629505551458600738034700900865668278611556391388687912746176848331520
def packed3_01_10 : ℕ := 5867921734157208409690155629285217892079373966185277675226239614382322135294152087356212066493796466164691219623326063978863752387810882278846008977061731569420296979111571938559321875828382550168901677507204623553847620350094180959985608630862886486204030320132334280273110755835336263386444789674976475008608199994027072459941362761351720975405408840495076730571157557052994814040744118386212152652552801199469986321554619336640093046542118784950998001888531302228536369346208397787874399321277103733015788629342146703008990819044837791838859914491598317051787782217927107287250406158219975454913873120086018902041984065904790973642376838535553626303836345127776842062099560254480000155627325910805665308818756405203190588677392378485995936354941158950764023847995523834811778389442237324191668530164000016288728887488436181802656446006353811095618988583516337155717854138441114193355885254458582235034219945608225050238340464474315855357862497451570615656193213876689088406889265368506686314417323763828025078722802332278489239815210475022282790428351979420775706566943371054094600237413821398217466215120476071509327379179888329604361237437031399294404482516532172944937599546650961343001332147890149495937365356815807816679660905466058432982207230312626607388965128543685948647323001717160535174917200194454905514235114795138330255449941452704911355108660042042252165225703460833790993282847289121792772506715788593709846885123670758863836226757002877258739149448723797032069881919992217759693454921429879976888226330443646696864908544733370185005841524823742918419086525499998401271730670295576922431390027614046446635150503740015361800874946208464919470200476582639829039
def packed3_01_11 : ℕ := 167036264141142900899341228768117943785599906294357658235918260887112767443125391729392306003769596299711060033456866691591693823205360987402186285576333412281491870935048326839203570258371763241467930213548051731077806620874929695424243346190700278714470236331408335089448585167481839905352304629360482500935349825859980659623633111854127758127830448047778566459653736606935837218046962821229980965417174905572556152573769234277155588649098173493048249030646165867010422325532226982192417246372014243285428199902526340089768187011729739664486924932610057177979154072095275627180649516285752876033755741587934841962198196538758474011363724467296967322703227898013744285534560707519347762472870545214863153494135435822986041258958168063136760900581134556432390418448060852456577138435731267494683165306879493390371759606149350164822633398373774102095617668723951808456168514149594820174144287945707206779868912079432170469322685698823410634379179615394265886301249675730899743817015269654674672154132536936879054502736783549850045932091050750060608639205134775816099270670752955250005738788949078535285013444152860425666918661053104950396844796972688126064137678105809868836538572126400199854873614863587596940184121483244371064240875521099473668222498769710917266868776177519053595424815509837457408906143839425203986705479797347745932031783936202497556607318304959116778815044955903362640867960254760318730439438757585896252499236647174329418186756653082294359413040991204208665969381376212280166630767897445869074031803889710576081039069310965490032108943680079770484715394286672561441269792157724120315592704
def packed3_01_12 : ℕ := 11828191550130633036698823836742651429365610618031784629101939575803614197273606611853731467704160764294327952485022633120492232928999688827717101969610565057825053168507033322736436799816380679828316667840702475515995814798221854627263593338338033297237833407771515888962192830779550627033785071173840575969804447057528481201964858256541191045760634715823110991848554021885702217334360618053145280087855791548232034349443426710146035037548792556312144332550773659655778691636797843183822174468261029854567306583024647888056936034100989111687147984422406000217886852190346312348115758520899354448550045041044433749159573180435902491105415036500835071010428160612985099437107705459292276122254473610150606125956950440961904430137355197523616911047687608208924240017618430488142693796224540861015472053700163391151442043775725740534685400465440098366781580926788964828913011096249979479486044898818752618140948945334981237947494895900149661339276676491829674644309150886684712296448690435777410881236474711186778961077951762151889295703665775378893411157645942950327215967262920311778364406349700075722023954667261456027933850787491061104917381079714455514639032037432603106190095002264143443785899921471060941661581257605234453803991087105391280546017554872372281635739692440823056153783488086111803662324510790766183741013066644625386688136571249632784845532990753056855159574984357024935409100116025896000611120200538768227603378611885530467175763608057499921648793352285697042868148017716578230278447483551449811544127927867015769562246285312
def packed3_01_20 : ℕ := 71139296897487066254947043164932861399334339654581045946359631625306955442638907500106374293325508655699660334265707880210224627042669346652803051847483236843227895836153157543003278656828546113893549454772665936621136085810989200090324523339413663164258684322619254899075008306414725045159793669771134140456052319133053945976627267737442076182994588959418030489705709992567983387948944678105185556259892328229869229206140879261755835457947094751704204520855082003428324632934819615291271119402165077262692059813565830038653965544219064990563752244684703265952551252964729664877569316160633217858783394582637425880370750342068616539048437358664946143361462865719574967879286453806983504280079563849495823317040953379287685818496295148320045631098665607923598440923779856797672038776386562933487963268075771445600832690134888308070295789130329726560472152499433679042302654535722228935517329852814629960485723677316314467772040618994509734590988707093156057356822141597888471700723165264197827955957312905177031045736308998295870522884919261389970427383706995524566745115161893676316679909131794306200399158321109699544980670818930321165415910180418621808021928620784087155389878131864142910159670307974991968518253782631451771372309824827070209197835004051730186337509054011022636349291692595065436942167736567658647166640078291366630862956925950069923687129477624462521973775533768070821046952379049350315227653825387878305578510412475738110966052286461164286025121343705342971833177367147719409494527686553724459177592752706343562668671054
def packed3_01_21 : ℕ := 77350234223266381639963360400015595110423130262310254532526983484346319106131434075253337247227085113485476014262049548967102632975837902497124600094061792680848941204303563727060205029459559286717688443619086158727029377939161638134017029818424724183432261594077864241455141845741396523297727348469419802972856661781588098680627736094633217302544675443377178795873535961578390930862619565503149707165797093010300241075889854154275604544304616921680545901096529051725484663400520045280266995415624667489564205384872063661756108720933795426091008810014375015270297898202327692978765400168281358619204175282708826210789483282571298372856207977509607368085018506341145171037448567874961586322505123153146804815234612037188452238042075800264999545118969398131965303289769184294017182713279174825293006152964215490133379909106590081513414818415399767466221044418212361878411930437805129597902950645845330555560235251090459720048715503225444038232973047310295295789520010712120905237335024668643438625666596653842923334228209870689009519206457477067831402789494199161537134998941108691095257839052029874084266388783468963078990313291040020877542833105183895215262292656971302708677355815594238614721660880677215832424328298459938668426632650416023241376794894544199691160257777487737815456022004879990180047142511575245426143936657680802109870147833313061234267526339091363470828060054932396033458730117100573229137846921023011784194550185306237543417149428422902879703266888720342358238497506753021371214927155001902777125175858414925053689856
def packed3_01_22 : ℕ := 10626220908816753372727083382645166396506119706521517737590882157856850936098111380687499559873825318584450488020097587983914630571071836483763136758203092137725704046153691389383819021739323691813139143039765326797969470255608355878840031207191404996119636734082606663887842511650730384253961320178744345583483977979995925235319024422243028899093402811508366941018468864407895363943526504811251359597933185721928232244783484308773659977107611637041231400394546786858097013387428050247801338092607180782136025706694127118877233537708239867068100599536409393508294426285057477604682681100464263125465816488624386366052398349467909089301204921950734081163677264779860792683197260286561331744761827030219111719560007210239389534331530394069089227879153470583902563520330213866393093243657731350573356853097495417367699775733272080731345348823870892287342500495360088657684525271445840318137980735150597132773267405674298942208495361635444826670801337164059445463005195784982108876631753968505676522118546733983643140984740832118648208908049409842186533292486731205949910657636878512255911464467892688267382869296897900600107658951500010876865719487092742550981102046469106530188544006185366084005742351116451206853483411043164392228534671955106594490801397357111635470198159706238561497934021225550221661635291645181585493807503344613161172761229317709428503773306782191231064836584412039720873377612998330496910056390508237440580237409591965240588284137343146963232855429888
def weights3_01 : ℕ → ℕ → ℕ
  | 0, 0 => packed3_01_00
  | 0, 1 => packed3_01_01
  | 0, 2 => packed3_01_02
  | 1, 0 => packed3_01_10
  | 1, 1 => packed3_01_11
  | 1, 2 => packed3_01_12
  | 2, 0 => packed3_01_20
  | 2, 1 => packed3_01_21
  | 2, 2 => packed3_01_22
  | _, _ => 0

def weights3_02 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights3_10 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights3_11 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights3_12 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights3_20 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights3_21 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights3_22 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights3 : WeightData :=
  ![![weights3_00, weights3_01, weights3_02], ![weights3_10, weights3_11, weights3_12], ![weights3_20, weights3_21, weights3_22]]

def packed4_00_02 : ℕ := 3493460381265686867164371723481432047377487756612630429902133351769711305646267890312489006795807604432706673111669153273769467197124018249474799048329995973849429130331324438346180132090779640936922665580779586246941645077540810259242427450623477364454463293644365851309461118834854132739919660736327171027744380498331501219763671470690646365532614539055345362979106937130649959967667749883988779261799916476692963430420467143674562957101243176247645657019762125777574826350125930380116360638260151990599660779416546259672573065743071034580868278971291662667598026799153916974605612118808449941274698452167121828513894949137411900250171195374437241658174479462974042228816604347307750484701235168049174999802022125349218373772996358877953395862542708089219752451128639433398124756417372231530988496743113337732831275221781712517178098425420518830484783824593995268274716057847992306213450642689263823220945548895166252883350822607273763016255898760080932275021221596895291219271898066705145138129968245612988494210679632900641773858959907117676382739383008471653887062692974772420250246001370720474688683166521393363330477800208800620831749920669807500416064318343641869841230245111749909293884927395138154192874539056281882205368548039818460859611832348637083832556056372223683011394755463762419986570526711103397791261339422805129530817925785353515788843629831168738966664988945316669380405100611638302812964674057337974980481867872156870149640765763539917116273377357655606174001287206030829928997443363987986100380758478415040938130344241536836290828480329134389241996294078974865101556442123059684223580327225446244345790595218347557602386230436744031330682583657577046893568
def packed4_00_12 : ℕ := 1680644229639813751946496738315580637047347542024195188216507123035580637298685892324986911039050841241359610597681372994412696648445102087151834299297630686883446492221597620166219265651407630545394872492104258138559527548554300631370285108328944823751651791476136413130117715073803659213636416670668581691344126525056778865952927386279902830959925110425225550228087223119005817540975363438168922063575883430875288061965836215038235321630536735886499471179617084917412644315951278197865044546301881693385812469359015040215557786531611417191483597865485217105954276107866760785008112998028584211108586634157656890581042029765012595977625404707103569383745175165469122628676296028992276114587560884768767460503210375643414259756234063168287961376457160049866062488445283282298063402338597064913785826822787395029100159081810809262181949802951543583114252467467654449180820540667494864174193493871749840002810344042925330479288930151666374079089837196899691059201136643256092418247431237793408840107297489119880087391776952631393151101832166101647915697689226308115789540426662534394812545068377634930947625671228890229671466889580130267679775356832696714640055389663654859118133766649837801060460531949997606833566085157022136239355232807435154163524555491881719463822293241519665335093831386272564625130375961605155571746111243596381597666441419048149451248776553212493406464434215136094682198509127333993149313628559331586254238432216748075763554314969152917714741552238944254878979001646762768466165538186221298352638792261388624551169932429120334871404629886644208734025112370248466630639553679485516662784
def packed4_00_22 : ℕ := 3428109901965551442133826954486687853509911620343435515728824402433359140789124618356097561759010510350606147947706472236708611181863697861250384571814908165257123523780952124312058354025061346037176222894562988537170852203102683906246319650502482905764973504140655047799477247934806208304521455284671654824233586109656274850812566423218025799112925048003923507476965514093190381544813555867989810961957009217734452370330313012771545375079968793454806029146532373693794576273834469658525065840091363175765470346353244618526014973016508537097292040991350983896564108430110089638138996766129948927069099257375560032337927515201868747946169606814891641073907692889331204034241531952469387218746305349906853502411535957525178003806358488822829148897062898311155693613938905618039072218131041286253089623616929267684252782889873777659030270616161878924826763644350746262411068087416016803676576235487944915279847282481913995749644642715875019648804517148479296399018756255019804026803601014904538521139064531063427633222717149777075553653585001793673990475778539616582785377232687196747820126053305819074432889455088795735191421153840203822249392265103153262789893725456679801764873022541868682256316043437319981266321211422452184779089560254713140143500382974029023041160655470778854837460188508419098153250991849422276511437765660637960112104486952184280735434064184290014734200385899678997482523594496
def weights4_00 : ℕ → ℕ → ℕ
  | 0, 2 => packed4_00_02
  | 1, 2 => packed4_00_12
  | 2, 2 => packed4_00_22
  | _, _ => 0

def packed4_01_00 : ℕ := 1704811772805262012648804509353580905184620413137839982468038310777069445108792619122348383791855509234902939885361956302174045986510479214566291906626500998403903743544416751203366651765917805223338748145429599979150809653773518664202910465206824712070804436442767580967105581193562405803171215090515443347849249357168910731976465343046681557081350675195487262699971173404778493880644006269643941317822370545757654131454886201274326367106617425915876288534613953832425058911200173385882436579498847556071652888194536537011292995003326458238556208666562055960902837639348255623210887540567201688423429248833909772548724500900999982555842318872942474021888421262447479993955006338321807900109521540861719448967875190045838523579601203441330683234926111216255241655648074890672056305511532591756383356925332928702106564749550296963350356128030958924024304237015507217923909370524483304183045191274461304824552606665226573267890171151194021591902532042061526296284516447837464190357970785143096948157026286428971597581328982850896110223849974714035840727806693270491196271281180003324163780483525157082155565302015351435134805816777334653597441878881954882893247801595618411450838428597425862980043334021745836268856071040343965281271694869834660946848577147574018487682855812027335833213655743235618414082108222083166501167846894092716659902609082869330925413093539690568409720511206920957697166934254230686187654196047161120983942510479377622834387288365942768154825045272815379766596334658620058082364400977407090680776191783783712610705699092076521533604682062335709825020114406028995054997877601265009660382823079916159683506313799009463892711721829284329470672043527003627883622993081796025179732065520467847805236112563558651247978161385325379221091941881206992802205442731992069765558495872866570670350627561250388836578308626172034951259629699269590576269684129987016385260536463363
def packed4_01_01 : ℕ := 88532495228963058567361891066963790749527376090387725611116608653968391883377109693348879497940788143689422173192800843393091026049551667876170015093851007287291788576120241857179540774059682766950840451559984725155313071387545800788242742795727152671178301646198761118986889099217920382997334238386090066864160043114257872223488805132874069988161010769697426315579451978988341555400987167208752902285782535286261301312907846516108846499981409866821351870682850809759243549387562635123144723432483967392775216196549798769336622505905091080529915941561921190385395974532291931942411722235190135766126710171961981373789052406131240316408750980777726311968958841343069234675697053552087646076264599673659325806069900843697381412358822865711588662852884803921072707603944103738394268619791522430993408891749563797969580805382904663582283992074792739267109083332732747836333763722208498403409729543400700690817837742799655754053220575631860435676364255790481495691244340134633620225169211799384559593059921139772735323512675377879820698727787624500102960165724978248787676975121221453356325123879265648546074356873924973722615606617864535940535993409391025337420024651290763884409807560833312907474991898782317850778618661805414156298481915194216550912973225931707152908600070694945001821212819376524116203367727175987016386994147647290510950138975363007164659058260783430815186268438279269757517162889208507783705797018674147461004953729513728351941840224279750359346582989381490652026667842103307681282093886666040732741515597667747637230522774629734163830970151139367015754337655719031590374499395814687354413082765096714788539824454653002198136614703182115641606512071760087665382900413337860053156937289626317704770716972597414786252061123828252672
def packed4_01_02 : ℕ := 15922748547290748044264913113459082991767923195909384081886480766305256544242487311479684704957269044014789983556252143836554579503095431577892250595292311421229286198218140944631513869714731754217980271729369147393356025476013079704989849959304971474275348776952598197206906904905460398155847212812675222496444629089471589027110969849077681236479375358408944378084956701885965176089060665969831835227323808424804627741794442443524214352189321457010732240757688682340238170577467967581970974739862478687422243762259436924034193462400578583543237456228546790416304888890490570908937857086839376598488790138216905927471359131020701838183648141881815325682333600747500944636650911170495291618724097179070943610094258535112852718700153308124553811453728853975109779095146871565937779963445971173675683436774120564765545248448104529632907267594982585309427295047673849462878029792345167716133589892610807352078135755517588393554368954881919530350422318513920138274955788669925214896700918258227028549391826286346958577233287433771098954323895849085756735799208214877886189240959151462682725896524606615533330116059273851157190173906018004539984239508243380845724242335118872936231833885942780360470210445482527057813396453962142276903871111149489443410179834268567683944099611219190922400090729294390141756964870534806679807270865505943564280718245121345236729356994756070217684375964622307869379212082286766633737749740289926339495070468178047784120914301554780888341634309155774141984022642851868790648469788588737917105859382564666471746607886894456728529459543984735170232363508134145129479104339655297680511781052160
def packed4_01_10 : ℕ := 12145233356743989499126136069915916102210797278848597978956635480844817932786079039574266611705594206040647535251084231609904793689800973793858563862498615976392719459478917467533069667537585944993803598788207419614000473458100372806837302317093452301532161803273632889107095092560538308539724902852026378819122689968876483720399380458517292829914621007834632980673856800915453634409244815760750477813391518181985686862929728088375812461300799652583645784992594470692748873304875409734984439338852622826868978334453698113219593794847092350901333516261255978697051395148942626746941611962709623992370465572928184354096471936822279993047391168746273011451649579231412140190566713370356832355095254480577258171883750879967123595903283921371151195358804561512437903752510695990989350084597466629167086615094101012407161296447911615451847879025314692667834871029512117215467497487259709402257529428245631985727819467757780210325867277954725589129803655376152149216487817484944077638974166960985903056705721335733844385147327595107043957038458401955009137687448367900874889876892608398155599814905941141332817548342021483038987228662821315401670955052021906475506586780173727060680591701888244101551817758914813079885250331907424211154987172826730949171846863461325784454979001017664542702834458956721568883361898325018775009582167341703274053684394568808416987652873407907924256722212903540398230350729725537458498182852705653942857489342094366965048442956224645652547790566149419719930137485967332531180514002827792925181053639894003541616225533575540672315023920859904987198394068328540168236281781983511830190703093851991882618386837066478428163385539487923149363638463345339662444
def packed4_01_11 : ℕ := 131604329323324709799480968120335349649260532231918154973753781304997938030288154717439788710288833410555792615561229666497710889645439833927562548693310600845518228255996983519777108939510032609840698265628412937508577845638353656122444086539475219269180722764728588566387279215005655995090559685453629463050331365228721118473109747981692911964344609187264295314980153528682263634352498342873987418297403165153768523468711141141666545001257700591302495473275180952611725424350667370834214001413236274867941475971906929120532401428842015596980723591129653780238800083592889210738293885077505726849610590229150289063017566398593551409099632383025544288376750008175950736641219396813781981536344591241464637976260874878261827719990212284491531703384937939510403386501318141182074219354554513215740411700396026057163308146549543324869117689340808148109475181371647632389588691992877868603520287141686934917480280987742568977653430076310153673960488647819256574595236908556078492736140253085598372382701417035220239271932764531358149174247075114369575711660913968661879929728859423282014849885904259234305615368803052907386629791171693547323028102436433282617680414630359174681322688166299971301801827982806637561298202428783688103140622214187800497613002454643900223154464131064877001587293162035682515620118837321559728926954627402927982457532315315736381137528277289129347596327269899119255184131316669003746199446777380228514241693428134237151785040293785865286967396169577885863260541145651662828590863667942029475741923399321493011476072935796944423902669409408868145112893659391229355747791585381286140116992
def packed4_01_12 : ℕ := 336128845927962750389299347663116127409469508404839037643301424610120112615325910664793908896506714643031442276496727838019539856877239905266542023730260751928809270524571067353003115762486151104339941095007880034660499398698390109071946330600335844721557834284951867051355214591748507405579822830133628983033542313747387176672790449461652733300903839818791076055130814026294766494288570327893628109287225024472097941794024704219981304803745538873097856243496987792091319767195190380174913644212326630377233874216051255651452644417511385461638377770760033212207417732510434284084564742348961111805037172566420883690818891012837660604420842575865343812304648132741813188832365263642456143399618902862500759952375967436749296239256491800609735185513980888195396822412100872506849313020733940044421073338246145199713153410504081271402326385785013357724742185691974416620477241282351365238723650603613337262579485396613762044562162379193726229227943149243683812683169370467557791120524683686449993586159635368142114502174411004239009826533254219552584198402387902015391917993357840026109731988676032838127006430021465471597847589594434478567563112885276916759664839750452036866750553546538859703305014093330606151603654330397596020303854896965659868611152726842471888059467197949072166300194399681816750499788975537095366417714769798900197367214551712646232335132347749789402163373189102788572480656245382759410984731399088197742306459671966674355480027582634755977337129509184997867983153187946480108214253554009465102081470983382343713135985768085007324341399935993068748068541933268018312665308299462994581760
def packed4_01_20 : ℕ := 52804426563083183199548320699743979595382190259070467094205087391980420550049140824353091137122404483693369091664361692586563700035290600484547452744444124586411687250305384172975859100604297433745934139323311738299558249132411829862084671510780121068458233075291308942772336475101704747781208248026680271435104722646340952348804182786094291621547045072545002114158107122126041536098883604036094939084278412694723297670681774070667457772430004778091783809803355907698882669341711777553355119574756933621422780819322898964805484942006025587447639324586243646380409428383376396578648864987909550996364306438847780076609014676420205302472153816671046350648301453192150173202279901608209447820370279893062642770176473424958824442963782453213250450050143544199578079081138479501378493699414198812131407375949619972776526888693867403986289197640362911108827885760626202918429804543744276408723837232174949964945132596792355177557358136438738964334677399765406535116227046260414519281800846659872297094929525651582396315497705817097001231451205993063042036632652093610228794745441575166330825204184317061607446995888180747803076110300467299832787704493417808438840561421403191052938491318393737011525309049748416558572384994183890015121026307450664747896271853872610987586290759150004122847866935935188266575078729340049915160893523040781978219930976603732469878142596217103179860540432625816018908931248852180046435649083894571535527314609711628309762616140647511920548652754529463451917416196191132497415128630999566112259837934686693647252979811
def packed4_01_21 : ℕ := 877596134903181169186259700348592090498537374807919492026579047031127016623193351551971633625067540596887397501122468132858629623524329154090996421474710886551836315411867899175443277344331033118119257977254645957759556097431723981477709291489304501942097230292306021756168627542014178542006600474654652440052972679468096272393214893913560994653496495979426276061385550749109217081828805842210521268117023699966937655838638391256352629000464492235704854327952647865821825773528172037701358163809662315285354129273670417735743362146948014569206325081851426338285212820618210967011346479932824072034667323585129971892414706361240984103056571530227606024719729230380114367255443520953001313861078427372097458190666441392544039194873089853610212699396276706732816218611405268219396530737074911873750301054760575344871458532857900871447545893739684362332226405965038219544639366226308009685422287672633896696426052809416176628212047773848319947310233466128304538791630990668711403497590816529361149364569137811151984783973180685739765231045391568359131361684251821856963277972119259981886352712411245570240734123949965539685454342418412600692385579795918557385637478555683034002359749848222748961628510828286870910915159229044726318766175945172281022352441352297007327263222316929537044386262727810002485811197666302625904776640151377329478387642054746497420014438438037383423995545714138338107889895473152
def packed4_01_22 : ℕ := 9351074399758742967999833376727746428925385341738935609079976298914028829802217133623644222031964054955789990479698688262111337333154041181889167279489873228732865487842408718490342453633186697178607906213513245656687205028045442241459948473782783873156836928847041314491337059956906221813998082276909399361063984550515764680595559202713777406236933661071718276249103431844701121436612815467210331712581216260710802345713512628931970672406265531568673611265250774459633953324018765195014724702127381096583704388261408814251694693460899637700588696179919606738585140893394179994472624859995204510328304949990416904048434537786487832205428865002367545154598564172622836595118853043345922199545552964215484646770366976679312228166971977104401972581451773418738176879375452409613465674798329071834802380430673524496007579325205722595641693328019245615399582644364809729523626853887053478298817592085840857901085866421730939312320563699989745125339794846603172296734441410013179950109559581842303163958015413183662470733446422255723042737806588058956491711305775292836688361270168484282163800667165249030231860029625906667143008971624257952224121140610814977387785802414156518515605619317205202781013613932956959888073778836280087289623803044490713754318917867440200125163552728712294326378952875985627068352020543930278532192773588991988496278605310248348928560159172694738480779511756755058880204275104909208805026955722924618196615526275516230234706184354030400173435266560
def weights4_01 : ℕ → ℕ → ℕ
  | 0, 0 => packed4_01_00
  | 0, 1 => packed4_01_01
  | 0, 2 => packed4_01_02
  | 1, 0 => packed4_01_10
  | 1, 1 => packed4_01_11
  | 1, 2 => packed4_01_12
  | 2, 0 => packed4_01_20
  | 2, 1 => packed4_01_21
  | 2, 2 => packed4_01_22
  | _, _ => 0

def weights4_02 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights4_10 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights4_11 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights4_12 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights4_20 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights4_21 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights4_22 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights4 : WeightData :=
  ![![weights4_00, weights4_01, weights4_02], ![weights4_10, weights4_11, weights4_12], ![weights4_20, weights4_21, weights4_22]]

def packed5_00_01 : ℕ := 3093410953446125983753716017769473080908612593046087642780022984528631175316768503603960739794385948025393299550763990523993751864287324013082568765920626317317821216323497307587518885038286368298312113139378148914687270420931828510167469509135488269448155364255416582295242349480946829557895185538149812681189678088992327910311272037154116410200022917360745028543140729224297263258546200490416251751379617221530091720715040380211410377884290747409522858707431163881322506928160159993582577320054458169098181488936246479426156730516433311801421659739178289892786986705954372177130237131991696304981231512416839609780888914812014162079084805333478828774783499746519503319764412321118702796710366515399264960993515871031996844729007262187741086866566504046094826694089092498665170520428703981622047187771860691588994269552370217418411166729550980775936941806432861285261508608
def packed5_00_02 : ℕ := 2096076228759412120298623034088859228426492653967578257941280011061826784570143380451738843682196385615761910872076586235401353910593539874542664698619713680906275671456061619951018319763995286963573599792029654338529376747347921649872025493554474312226940785590159286167846210288231790058481707344500229915334630809264865040959131799036727659598207048563586036167998653922071864551237904594232014347577202981524908434151367443144778749823319317304788952854743624661965258489999497519731084752009413979294435441759594985910056519547436407797910421766671272584338137337782990488658704254575385970776839850493144886374469883258025960369819199508989327256224323142417432403927287732590437658203828500817493831094183109053495513673816608615052311312933401323480308138865356439982078909963915529034691978484286804687693094769478993716269893345093648005696406052297018823818849308181877102129366431140122626044892592810883529532266468609640131203110888431671501843930462637248527432288606200833626806666855257928928055546629492939475358146274233422117089481298312645976295464266716648930165099612024249449529958129460475672825025803769454119681499337931879427996514729505835669303228158605325775521200314210714900681245600240570380375593220595547422715651678156252166664713454323188196681159590978188172610133173923026558644554687380098473475383354186944220346083910964195901836374526176222053482054302634983032062112979805518127025262145031669330542215019845947004202452362076540502084721503133558389152872738844308201731796178104605350270930494668804471844035363065605995245413465539305807071543824723409956837487872841335881383476470099247765079980475305363423545094961473021030701568
def packed5_00_11 : ℕ := 1844974894017725293856123278421727170390082681666462218934714020733109819881957815087738414003816556750589050950060191717174229265588999202850470616356655046487846349505160515555547449389884033493790591479456070792626777009962096436032433958373695279325626046694691225724913628463657820377270044509095099966284712554601037631307760403285403557500894609964995253498035352744578029152202766483752292642471614901426556998273854000606388043716968857004357945294963679865301859820724157813978399267369047439307938786780949286579690301921332335410165308631632190985872564937404440808054254173275838165741852612987305141186465568728575442489523281198271457923347202965504
def packed5_00_12 : ℕ := 1423604523930195178119385472455550657263635565008730041783394268924256539829475108792930089350725418463269317212153633595267225396329968823471028362484660301387962013424486420799959930083818496366171703382184968863148705911050187581785927582382229300440725434048957414023998130901535896396927861322332198696422895822873914115028040459609200598388082691997549326586316578408819958339137384465781035097235066620573774892834912194772393065337911717205763679357323937962016461231087546318978810901271345599454472384923444514399709556954220654378750635582079506821509588270888070536064862865261597944823059694218707645729796610126580414246611118284166415416051898801071747973072280279808029540412672486160348456304372031337714682702838880766330582059327745023393202309988524125888514741898666053935096254784277502473820108452825411418540787333394163388277583800726989270772147072241760288697130392505645047517320146456113014225310739519406887905015306388667348361280780873197907771495256695212680958371773057287905648436483664926771583858766352691019226710382855890765528893146174715512435759852128054910815613908667997241692287844417516282059570651425485441200029846333391248624049865272403542963999938418885192910382364220313254922746275777985700358065328453039920602511965897212008976861171596033316485128256964020939708850077705329442225751179630595563024555618370986164493711031223971462225210431985392380298602422563485919216112879927176885450609139284728267966603538535632115452725187329705259672575958023559800348769940182676817847014340892899668371039404160071630122618608716098411503541835713755228407040
def packed5_00_21 : ℕ := 14873175311499358194983742396185903422137354220157958867928878960357667861483843274490071879221410330372573838178377488576619306881680627282337876579612906056721302698360626811560737913504235314093709671349101235223165793866019086126074253357293902027874573405857221259237139379930442938498572612554560013747869993580403092994979138155365725503927694423215948820623352711612773293565249591825652264074198431740489608524473950476700525240888057011345496932956284567033706985472694976134828698455537574766319192123296295604453376
def packed5_00_22 : ℕ := 4510670923638883476491877571693010333565673184662415152274768950602190160504731288278156121717929882551749010448873134428090203536644928973824295034075537365072612758311359480634234583945811010759862098891253192149502419321165986118143179482544927838478831056925365005053821738773693552108451888293213583923740966939002361600135387067431513859523386544294275584523940854106578223551871421154312662371360947843967824684676562770801511920375684519782209474334514352788120919294262089044005554540938786774053582432578665888250101705846797182002660447636362869144601541018018364559238983109769894904889016835865109758373852002192456415557898883565240495949257604896298931874875434213248937609056381471572686887077295037572219887946920793558856929848818830566024867501721023174180870932715139835483118139269749704681910315916732363541962723589771172352556299727949323230457417729478110666211888947883943639284431110448686719336830587226542078115934488929066615817128849449063735076828605343111192385741657715396245588175590396976877554952966819414739031193840560493939527293839409624036900589943784306486523348199744271646999029704803442102278856523785868445819111426658818447179628908012942973664492272565248218561945741966622436631722521982244493398628663128347406379314198319534041012318484110982310831162700743396543201421589800021764745267820372484335810044708416976698184226114607297353816895131648
def weights5_00 : ℕ → ℕ → ℕ
  | 0, 1 => packed5_00_01
  | 0, 2 => packed5_00_02
  | 1, 1 => packed5_00_11
  | 1, 2 => packed5_00_12
  | 2, 1 => packed5_00_21
  | 2, 2 => packed5_00_22
  | _, _ => 0

def packed5_01_00 : ℕ := 3678804351842933816768472888605095637503654575718496804273135302203149855234763020211383354498214519927948449226307379388901888707733139353421028166086772501205051167434776641582885359865263340639816386677388575819249354310563132355973689385183604000377396281776147302511630495322350314096291357903886970800526420259256334005943452639832036932905013852620511074311484767078945481907227509810546297175713355590605811169782714854921364367219233023062797647234764994650828559910164788155430106942176897705329629112079751869180263419216882149495080087408969185671810042092832502399842793015035902126517340679588221975374250535812241865902388384027318320644867348160832864881229015711167619501330930420613422034245090552394081627024199366769814402786879265910015198651745591348417022498673203589271865827120669421864150539082805043228061564250007046701877814222129698172308303501371339711671871493799450430576362404024304454010970487357382399898659793175454015881675668715807383865028625849461492534927531286185003557731806736877795219896203749494200667452496573911992625765620651067554646914221814245343172781439976132662378006537611608082937625269465138845750670263026167724112734479628806289308649625090392867397358635220753494748286982213862487264121499916480760923030468116218638940290620300445717885947839666666850926875893491798507542864362096246209644951314345682681007794792437691450244233726930831295854473476955953364350140319692110349142082659650013645314324285472697530026367490919056697246771089222475238917057313612140899996495388942118548752777507382589694813705988396286190712109168620738659105446981295675366862739119866084350218853406492249356518196713128113615774818754198252899866527383189677950723473073519182741659252273994847576682486335655598558811988014003903693098602782016150726627865207154300234750824947015957343139929730739037335024763892661154961304824760500332
def packed5_01_01 : ℕ := 31080556835699797156627046863934096752493653308327605799647320059519731446580968361733415038268816818828829240513075092696019860052973844082004446150652327481117622699615211231874322107769356418136115745166786721697312683279309472246177320941838567836028400160808643726561039255156398386940093972443158781781688010230719459863858457076094334834166192709248802824874156892637332512352437169442301521999709096794363996447049818388953223002857788739456986468484393220328041309442724810614997457802463542532275203962339771132811702281194665608019766007150418568562048400673020773878300144002342047041535652164401715815949704640863738712925381356002242544636575738933934113379639744830082573967155119193388165242753353301347617968923650531928288336151817169619839605168828781398489074982117414464634823346719099194368854708130755610209073954913005508121765807557070787402792461061139759111493750621804428846586529808362142077215282942309832064200653027143467566058892731565041136071151977506547063603744349773573204517344191056545601657752998679090961053956939448012087183872507024619280520402380390594790372664535581513316629802413040619377666155448664535843118526771018789950683183541432277804259686941965221438199777338269112419651841763799687874786479105401087559968630512395243969259055461655071468157494784689368804991862320083485767012365777775996392410478233419802905795613004916116097122602608116517150742898685505660304468728212059985754967735403272187418910708496778077017919736443247683509083953691453435796947799437813529466578552949013156504625167640295473173588699650808892203660057137880122400059956431039393122769213746477898302503363152162902643510250841652191010696845914678389693363244619491643067586146658911481743693413008718102528
def packed5_01_02 : ℕ := 3648963798215377949990483528559087040906593088953334988526268101548310768128323351701920946626550443021914767757484039577034673155807957053906423405964486656830813245630728420220267488906037431073556699415383981706849004905500792735521806367742266654422537521551821271360085691427374809617552204254945811736317468788321629036466004108464736702382743699834146376920658066354221448371664395554459245980905101413279097469681841351803897184186770088481394788882158957684285365027429135373942713908528274442127483994478585242691815374866926178235504632883051832815613396985949629660946007772850979605128639688125344131423799294366771241284700081563459618435888956173069442859458554978497617250109029477034145446769197036082374047917924764349624285495303387891548139412435996042666989595310624823632059229448783827070428121110881437218700799019893999759895655784188581205242612302010359797818169196736409079235131642004291937130832190758002399129977796696715699681278156129860178767176156517890408291507914404593044023752230060891095174609541006723907066022957085974015662331093843555547955463752118257865505661760750898938396529644055606083539696169685887972948138372555189338854214167456777514091674557828340006828358078001751487089848663468524620263206582332168620100052048390951136238358310169871803050818045079963195660036230462194265474471663308097445972603649666454943042683944193297959193590014502200087356818892558198714485698324976625132130154664475857412969070082419395504980033719785380474516709031312537377506865407438092377507949476349061767318739009436105141266147538514560271461593276571738643300775645952
def packed5_01_10 : ℕ := 13782792910462280218109435315297837374418994664760768492973260489422080283297973994803024653965428462540389375336946009268984398069123021492295424083409577270946029754657770616201963850863283869493605275149684169459666971621024453338130900106652216638367284674313401874725779674744211268817904153609037584066425822156204957434359627452845256545776261560762464490058326847287634707811224677933320705064953198089148335471382264320895975339127457624335282383627669748438876192908942156834433206488453850564661141483375696662374504844418653784268253427295775719879646678476014647798971965974888467596934260638583581007277921643555419784745549303106196813146461298442580137808114993504564722025502584869634263440067615185657733254965232619146538361116590611607154398992126882479297854730596343564609827183303483790323458104865327071271124678492120857524306400678166215020673748174147617793081135314769541111660202180845383570635673518035738168236516582935373441944915158143520359800583167313603594917142128244788839851556615323966454644416132064333699972945249338705193649809248178588267383484380624002901928954715709680163133688313680063714684004175454680733882367955134399072344766141933798942239347043042439314398666904361099959010276826060902661672751038400166522705363508851970015322102002941941371941026512835355166041107049340872410740425351117616642548174350786936091943744969493854706464094748912914924567197783180278815038603777502121799625015397871090647099977346780528341048250652751595443408298430011836822729716870011889488189620577330670168318081446552274431063240260701577351400314386705113823875458856372439049844032150245049088197724965527012376733224573989059297321
def packed5_01_11 : ℕ := 217653313880883173899141601122093078266084726383556948610438946004419666671440166363481545465112438022856455805632609336005752740642419207260814539263893978632976417152090208533301413791110496552811597796855169919814542512134175827771441018767595554948142998567138355598829533930506444508545121073689041791508355141311202485311479098693802076748251831474307551181236417020481328165144943443900933048701965155482695696994554007979253715476940255585212048073637956525014695247475427570216520998544963527435373560385874314237683869542389171208788546885131918349386380603321021728472263093875137228091181305553661849199244982472421748591046295649737165189389123503278480377256889898531719398528197929190521993172637700566713574349833969872484511770400509862896643311764371874664468204439489722285764755986875738177142268857268927484912074620844084097846057308451767388273892692282983453505877597651370585628639048478136297075295593395838574111010527926964804667396690948510758253649711822092720352106939037307422073083494588489599367858143103983382308082231651490985758347861634875631927102551434170955900929393004730223501312936934489291619232621771053373713411660256034997033743682430616056417818989370575053662961343061242565731227709336032638909398054105439555347147544652348499992628265854073537918236672244940899011293086569993883936014283077214249615287131241717067376849465375367280400977333488109814459994189863672379886474274176993177939751248455805813741380609490715977000142024344508955938350293325285018746963230187177922013670560256655131962682717884927471463155614579914575994991064488424843225530368
def packed5_01_12 : ℕ := 1542238234257711442962667595160179878702271862092790878598677124686719492037694277441069221934305951635788761294169269139479080807617171300514175906238923088652364657833878056429664029423709260356833299451814445187758734146412376864068805414108554603067176248968823569519239561087014270081588418470088385343190390123471357710752197359843779285914721179604901051049425061390949145644533759952374470960522688519307902117804477157112121346119559989700647182192282970411738727451478611946506521273986945078757532138743854766074386374735772724632684736538331996701024410978324106674353319711132767842421509486561414951120385082956426234551632194808391984984881721321156601707082667533393405767666671221699471539625200271505244237160798746803911860179594615274423739781898155327897881688510056702789314012571926759376410637685000565913227761525761354152948332075770360403331418400194069964294202425253932500736019775058588117267599892640466381056156727834738362016000946806674387529700914363137580968159774455565443154027647265541671434812079506861909454765992181514891393265451366085251758893259472145207046950629471861749263756582034467846620967674493758223005760391318343872819965150436774552116011355339692392548174919394084177089979353431457586284672770901937101712664248847699242139772876123252028582582482376868458339695817442746648062873757931654783246676308196491647120765805479883078007474729287251551769119495255383423232305262092612242032086016565457660862016664036937158373805847713875646425750173985075792859009956024304068163433361096542878080680449767823461968723307903801885785132719620609911306240
def packed5_01_20 : ℕ := 63071953950349357710571605280249753405595393920556391251411632162643280062071994157811056809767093211714862686670714576202589243843300047279766458297689958131767522232620106724138371437797357669020705303031016847398835610322850037595387682629165682323494054193520853733769614962738310026575460645595849163405559258138386578953964259969890003430285839971172683023237655798686492317890909097618290106021954119652863407636951100403027018967905891455009233457863069402894858363712211189885713270644034225353203313331644274471097437305237926278967775834799436857683567736347422160843159631115229763913476308679461788528478420511549006723015647881345495634630610219055702122323834369789863145521791213405998517751961380928170076681911371418875774266852791447119121267611653031954001580562336291545187173672696743472016702109555985214181697945792085230305107963323582949888600682663877881982545680684122900758778742796976043078524171842230211621655473668772275501942059597384115437383062066932893145876818019371945142287250796739200585806842751325937066022618031736765002135065096608638626678597174431504512979153193497214569501732577063019308171430802892496486846725814056920818884560752313621082769304115677729936671094799519114263214826057600693987804780353590351021113618583793893166053297984158271284996348550451979865179725889729249961690482526477813831875056009187175765751386517426255406312867793447741616219064816243297090845474106640689180897645191665070943278556578149525970152862142547755348914145287406119929948333281623284816864608275
def packed5_01_21 : ℕ := 237780349649300358374702181970418310895004437473027819488879245525953499474404038083186184871105483867381278117916670835713685871740538734313367100112483148332427182201526230705911427551924418992835961815837038821672408904746325361469704836660323724729437288780921074488688808722987841664609985176308389535018850137757170146330241147939468875041770993713386430740777522549813735572157477964386546160761845308472992195007981945464939617000069291909141412385164769691239180676099474226448811093017087057338301252427095582214789909418217277066306714988442691327323970246858413086532719765887438639831453525102037680712895299804289744688053445871322452466105730560652093776965183705555716715284770192809246716322950701436981403724302668028184030126489107566313559181639447916109121056071966492643884863600484877491946041399568879690952289569227010450685329279855515011483509994860890161933679249279607914366323261510965344415035199839034410263574190999876545618891454149717742441344317070946116207220791239749023488076559047298296598325526873985708275803546327438816416518306086422147544005431801770298131316847963587691461999680745157319335600076357326408973264454477474869519841699133220535071421178819563669234229049980734376198089600088137050303295973060170267860880711061391255144038728236497222643504076854458302253671361899299806626938353277906123281313812303611615281458241507092802022703499224276902058585118577520055833752679713827551460150638537727697136269762919394008096861249601635885697868580438046267855148260086661887752273920
def packed5_01_22 : ℕ := 3400390690821361079272666682446453246881958306086885676029082290514192301959492492253345117809421141554865939579358619006627384410499638125337217488051639870153412023071894572459184944181842619074773336081432483125473242771186870582151664150911421191927242937197806579845582453650883583587443447990873298155440514010253089131606328370135488467612207890787067274669958695942764263304189132050022134929137393209668306112263654168537551225090638952469856137871430126733989469238679411057941714201476081100207671427762263546914865790200105177024694625276940452546920996378929558940681836529872326641017925976883327465821271568428416989229998093020813116701605508658867538066558103478956807752345109414570317678555042926058278271658944766683702022190976722817615588324107738156609869361324166363039798447878725686876614509645794931201172325469645693248322157799415617633573864684357935715159160350584580429095249324906800885238391482203321181936194856031686554792788473720591410783325912635151842871572586329824358828740884553820494398248338143830556887523860904364147071552254294778249338425316217312550039385019624938526067826337447030889018398793500988090122791725599557690193728245138473140793159824996874270559247439318751533019616205572102233598329627823405979872520049224591372278118728641528762790661958954363571111302903981809392459388939946395967713008765738825753974278735679246414207003261279936562729648272232521906502546932545600131099034218262247286239267935232
def weights5_01 : ℕ → ℕ → ℕ
  | 0, 0 => packed5_01_00
  | 0, 1 => packed5_01_01
  | 0, 2 => packed5_01_02
  | 1, 0 => packed5_01_10
  | 1, 1 => packed5_01_11
  | 1, 2 => packed5_01_12
  | 2, 0 => packed5_01_20
  | 2, 1 => packed5_01_21
  | 2, 2 => packed5_01_22
  | _, _ => 0

def packed5_02_00 : ℕ := 3589077416432130552944851598639117695125516659237557857827449075320146200229037092889154492193380019441900926074446223794050623129495745706044172283874536299384325740750093283279321863582826175337872804904903203545786546754808574199933091996130028981351122012436575414663168767472529145156267583174601184878444008361070264749367709505443799157716126143067055976866393261548092512326671873059800798409354072255836988844873305087536562774285653215956671673331169388290710538848100999416783034549924060226282098923175257501373853706296576241804489853515267351882196138497568934503664451026749839423824994714321716549091825577900545884812481609752462552731356725259709245035478214232117555344964652334240029062548532289009891121719203070177582382551397213796864721169237118089861817221417288595203232210611359865481096572030789833161227012275033422449565178843925863759590194887610266067116987000230051172926962933611477874834714048664959837355540867045185150640028757664683493607003520487027347040531151205844863730730658567898828912644226748917908007639128585848655847824313762425455057900821060679393480737103905902707146728418472141597756177049583471641591459073936208242559553485410622096523140624094387655266712836115376757600069240087748709784195430953819782475839944336970129225929718135135494365678362643580494394283666505435999139892831757159845725398241652575214213410284440785154967990723232045233898125347381066743577264481449552262185500233047625183220057854979739395383302202583677258831143722549398363814956493137366619322716054478052485886496899856748917841159321194056994737920635151620418429039387603520572147008247917836142247980045636592317046723410820530967329367861459840738569290308300105219096865148387912856864256313776924985088610032104502812497461186786306159591821387725354679084930284365464547716930433989338881771871474419357367066947635915607613677590594715725
def packed5_02_10 : ℕ := 8733650953164217167910929308703580118443719391531576074755333379426869855233408060209603213053443146270800341722096973472327892835205466157493400386330877908498871532816257518484481199190481012395093275326504835476815909872976406886061278914013234849953989558743534479951195055387304874846838420678550094830866768585558563746676717531461092023155226340129564329515944990802275714002974782014299462567889171202885540725814825859899179067984293142896936973438912165343515433943396200116115540858299511035990435334380382362456695431446394661053480165256784416420683693461326113328911943688625282652231416169056738334422470266659449897520630157183845344718954717707835429634572557818531737831922806119247819276440540902544389389124533490330804158358359977466718765906795542042701463586011210742580643971016439861936924070383348609401545177049979171780190855380800751368525960529992817537746515286848910791101399907005225621246632889497372833685202401077238608226096792721534567288456363962541202654844704202763316326899930194536805397427487012907904339962601330123539000317462988248952053511896218453251301700597831283054086199430788790224669206760981638897912098937502607233103734191348333461431221720687581604411049607598516035316533244030464386846491682885242922817341311240245817369648426050921858780658771451178733345448130768622587619746764194982053949487401899505922033187659915430527496986172393302059539731071135702469673131450311121607134719883940085919977744632367565149832873972185699500317840970277820415500587506594368579477370774383193341868190690537743040961320597673450326072114580225816428606020165832890298748699496892418506990782794718852286599791167815846723622
def packed5_02_20 : ℕ := 13100476429746325751866393963055370177665579087297364112133000069136417393430100037348020150983379429078099278400294954707728650635799029405281355310670169354084702338353563932041915382003901849632453676401273627788391576798721386688013980433427272914783375408292927437562736657605826635439171063182763226229221064840223462243160229229768021538438190820318248216006757331447317344727253626311932281058275812531454671058447581434085226057177464178911405025734510752452498203966240189741626461958298395001701318238691674925843620973277163877615590454690371502788321327056336328760875839656448699643854784511060539107025034746683615265929719777673803718052508431007407867477171016333601727852441709420815305753999276330584745682657924151236824143060466976293172799607276592409150939642186779015542545045928317396622059170795955263773693976846154830032522603862772797796720453232769924098371002560319534019224240115759518123278136433089587564118843308579666747825271510688902411383043393039934022080369580806097915265375406844951470331721432986331716470368709803272136864729494881532974860090828311536092674862372817380347025839092998432775964397737133014830225299814660481514929180455905612603645322059344315817441495964140880473101314657699603374165701861524674882875880342364922604680980274767080983423104812931603758127210678075567776766942448987359635662783779806330363822805952711068025730209443422605369393539029977115505609504007662271166971476224720476151174905565261478889633545953209898056911914531105784775272083533391699605110973856520834276162482408701143005020396478775696652064458743333655669432066145549833691874176343935778293432297225544699276538011881178103021568
def weights5_02 : ℕ → ℕ → ℕ
  | 0, 0 => packed5_02_00
  | 1, 0 => packed5_02_10
  | 2, 0 => packed5_02_20
  | _, _ => 0

def weights5_10 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights5_11 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights5_12 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights5_20 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights5_21 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights5_22 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights5 : WeightData :=
  ![![weights5_00, weights5_01, weights5_02], ![weights5_10, weights5_11, weights5_12], ![weights5_20, weights5_21, weights5_22]]

def packed6_00_01 : ℕ := 2911445603243412690591732722606562899678694205219847193204727514850476400298135062215492460982951480494487811341895520493170589989917481423099775236864492646212668281019297681104588016449338692168865890244921053224578764541123690405584533651249475166822401339525255767952177834266061972446250483169662242317251653959268377804534030891505825838959792895012301576263072153541691263577238360427348990876660878080227706732705391103150198446916917066398269052162944927366296008134991543030856920664570416484844310046172125370106725764130677717538693430355259367860157255654994610586271586397567405788177314621900331653443257667387758873483167151009141861422039805773607912871165422469919151410051444522940374079857235205882792166295195745619943286957900470305126554796186573308521227520530117645171484302688487654071877812436982888876117371282971495818423407038285026940967452672
def packed6_00_02 : ℕ := 1397384152506274746865748689392572818950995102645052171960853340707884521985649622371708193578774159552435459935804178016167862203699039109396566880015582457034110090568311918166143970179896454010575224250278619537174911451797535682493511223478274613945966384838390135924375881475736684923107931519395975492816455350908362187659204983031682608530754514592861464573457980026715827954458638777947694244250372709776923422770173490092668711601296796766593887964797146260573702992572275451741981901459752822700883858702144884087749419078021961119253612544803003906206673954631585035478947097494846682683844985289911292901428389729931986198127399047803673125164366767999395527126572674926001016402408434333716436269605178965174511813373292148931214189288498079261110045478878455127423414461668693478370376962124274062601728389451263297592559780025150528358129782456208834419257116633768174277363559777835998783946925755530540951249298889153087316226301559577467654719889224048853742545222670214161739918556968124841184452203552813507229567582072600450372914331202115227130436904971194429662718754836118652028801671577614396186853416844051018245581948827552891840134811462992244436829713236673607911255481809048626643160168135511712105279226040264967460300772343479519490792185563766389236910621715974467930451900459541246791853371160210513621461011965907557153102706880754724466327502526124317357373432489674848784898506854886092510812500984335537982851212019220278668058761529542705217609823119122743403263834469981060943571376916126121215723543403375883983488188378480181781945158677967412267976661740864482952766600107030987378375863444671081313830812366687202572619323196764451768576
def packed6_00_11 : ℕ := 10700854385302806704365515014846017588262479553665480869821341319511680461444963539879495425096512850369493978263824161212155969525314842870218379360037042540099225270312622605542038882644992534781103595263053687707019393714685562207915298778347052313259934475092524349357566028776084232979275961586044503031359218551661501779992246383382411949986882154790213940518681685234212018918096881619155582527942176539075400120613824775720739977403029196365286353734974111819510915626160236364788933422605255245338482476254785533524925156513025143956484053390284673902883355837693865421371255505589369101104538257374911857236370906356070714381511039506892236662451214483456
def packed6_00_12 : ℕ := 1759733369858157928508684820118666784673105073413569079426695693531372667289212287257927471558535586711541239331689908194149764726018989246278263002205463645364555503487260141465300354713987997696237049714802572251782086737709600538903229365392473515578343631076407191637009228234839338359482173404598053317946296480838976075224062741454814006074928407632546588900256363667268025727639092574221605263806339417894998732840390985630868156263177417194871515573061636444768286636836055845854016719667327979551664673066422003892475689282314466812812988634713780727472008985868209173784276317945437060620428273974941163566192813293605313565567542960930277861269046029356305860129821588670941887646713512749320200261075381967716014416779967615961308374961930366640522260352345621383939890018802795929561895211858676795739900769099101842170764657096494820086657521626341609827147487903651166937382228379673466655825823172297806308730584544812671022151052228146843023934005276646556288529508251703875021501366075905758339157816734821213528516364659739832263961535609817083307577043897165219917706153200603662894354324316222552549230008729523409703940862111871250045221540134882722344022801845818789764498328406939356755051841385127458219163751229297402044125340578673030228714431272377491455593401026428094624649815182975836731599288199226404947333302347025876356431617266491787005923628921703993430738435293622727027534618471227347361125068453572338550841922736303855227866465982039824255960800795742744960436175268747671266522306631263035340658590530346650364862798669270058777936198212340714839307934654069001429760
def packed6_00_21 : ℕ := 60484246266764056659600552411156007250025240495309032729577441105454515970034295982926292308833735343515133608592068453544918514652167883820738492429251183834693111456619609092679966916989419621352351065567583457019910191919836500940065818245198045638347655607394122016952268978570332352953844027494579344598988474937835061910389467818849719727286857773517458699378458301954950622871690288783083754794466187280098053529496189891409061180222227770631433669737210021091088865326493085345469506587277405411940594517542555814461440
def packed6_00_22 : ℕ := 300711394909258898432791838112867355571044878977494343484984596719528838580881471357626705591611696007575114790902310960879166969798060570827899973045810879615767159522402838274267906202026727477392919820336471885277316168719114698230928802187464717010846901043996343776084898233625758938579598319919492937008035629037637191650067601576645529320318650045943778831767800366418388956215669488802880503185000364160259025215747101130815401166036354329769032705281249217268630268815665810978061514727476883574350270386806395031439875145888560271900692186016068017646971137483975932105079946405770313941183528911009648262890399934172683177575025290565302779641898350767391231347790735891678832445618653516839782644219275557524822804582915009134299055343018699542090480157562272539729911841570922832241125150740406231415533115145169139176818809897914234901642976547471834210809801563723966286182644696556978991554626112938054394349687565175786629129711478590918595115468861121411611546697549217645553650688584356594235796563389559562231152551711283589885883070140818729262866378525762714866741865081972929044580420716040358379227217180296521854188739595543034052053398783618295434021949977245145838259312195417562472522628776740430420540805830900372958859052212133581034298111081598041145460081599858718939936423221687689309718817167910501627746284400276783154024124354572969988479021121659100534793070848
def weights6_00 : ℕ → ℕ → ℕ
  | 0, 1 => packed6_00_01
  | 0, 2 => packed6_00_02
  | 1, 1 => packed6_00_11
  | 1, 2 => packed6_00_12
  | 2, 1 => packed6_00_21
  | 2, 2 => packed6_00_22
  | _, _ => 0

def packed6_01_00 : ℕ := 1570221369689057116913372574404613991617413538416431562799508970452563962600203728139005090334603758505831655157570222909897147619154388747599874245398010854025570389936821685470820776973829949393609342542735994461390678207128857252775268065279551906995314701913366761463798522757087629890784644014423240515246696038515935617265235507677629936603217681991201918147391053267337673837476504659114398574843420041198853948050870916372346646798597006165739072692735239176213063091616062726854136723987154048159674678082988385696708769560378881947739587088501812417787666064690005692905474403880278951699267005484059956000601326113246217187520170551493711544602752012737542731558629104731558996738913043642699328248749596888611986528988835352628505800648046973705990903429112367206180733834342600311265701395164111652397832512135049721547857728361953029861576975839538861164833052911729438946728614592653638111258142314908068880201833847218666395731422830799961540769308392497343626492783690207449296193137262046556995969974299263861375191040472718134969134382719357944833381813269374553389500159645446475158272625560316341169417294810798260779713088714555675561685580868474875240540226999584138851097919890785517355614315004178617879019303680667808027828518348467398454998587080434289789731484787531567938210739253534340778564852655036037370465978249209372768287824599312885240387388606953384266089864683526840998460823133576727441275270102568582686804239081993515153984198194009417823486727292801969551165378113645747614744870315245794015530206609584219578833208305830999656794627561998670314974578127209986481266349869178066140900670928745378419240437745307318751628124659164951323968782799680367159278193981175876988800160539215552518431909212727617149315781795819928580578827384728747853475275249782602369894091572015791184409217711314366138147558368249992413253111043930152840544963788863
def packed6_01_01 : ℕ := 76288639505808593020811842302383692028848058120440486962770694691148424167115853440351939687281701892369590555876753383974745565655391546300049955163450237239252711403798296764680658649715673968253191707441974540728440249814740151845815866054812542202713007198273810214830280484542358094385508692549850262298686953356169868445357465987581640574556069097114162961286807841064983973664694932617321474639734362026258321611598781175924912732589358903584397971595857927757898720923629204638839607380793916384920125539635756781461878750620284651118160965360909166196487367288690847727109934974802739346946628310833275690518331657959883089706529484531523576506242358591303929328074490203484633813155688863893636721404820141839911816392928863261520397575067022829352654459445322409592064371890281044692531235838371892635291848029367915682208955512315591844323461118369756689687744693214475308136268125379754979698119814017621794653505167872886373160981632216904239217489216617344581257684182165166189314365232231277630414598348301714694226083781698258073589343039496834345954980727860706930798549649830760862354948910527481623677778714875868581464030727574853439150197941494987760278836061906185455074895975006649789194787550750793977272431508174658784039873547143159764906593428260274185026365864824713333614154431272955993707578361624618746685476995748464760115669565989521137399743590167511114482255722397702116815544204769115830580848369355129158067106441189365497717279678175108415552283914501630545358279834540013753414380187891450107376136362559024964657367857787327272796536793927951980821403187225291408174316530102229131812098140560044457032267004821504033827724328360027093580952798915150923765265379931249390994336800852565961830255023266070528
def packed6_01_02 : ℕ := 24215845739382373717519676433370123615792113242051201648726276185359107425306995582603906324558301165219490318289819557811578428648403619530575658440831399246863396000529380841421917999378150804505459628626081027717246825020251086108584701374475166803816634858836186243556349326596715241011542300919120001575770365884993727769708177941153939203219334841227345073500885004713470989723548710994708567423583838631227379818010600814610382351107733636170365336283714947513292157657365654296969390797862735085760419612937518407970902834511135723975268813935122737986794786015830856406723792468322833735852625407646153315541645337774167292347441743128855683413973329961808022346465114646320750279741545847723105457135892481418991050655761997468480145366461498541808198537715299364238467636277106865769877086208211103440426701724635231087781225397098468064150226927754053574534182841839637134686035981774254797363761336842080589640672522684329502840681739642280697616086046758930878972791267996580024038548799417216831778839758690911037673727380696184814324588205244339120213976678186712581126252229380924326655901408193562535478774130309705615122456820835452427150108390998608508549837877854487113749168057480772952744965241335446431181264156616419284823651162081009574611616985178859806801662958055487554702085912773258277681542854118111275367711964930308102152169621039671711783575657006497923700597339871443429617239405558171494629829358771676399723874296966028251982565086076932913960252563837380248156905964664667942388783324053092923292174105673795624466749160157348929086975587762072267303172972368123694596763962368
def packed6_01_10 : ℕ := 3411582403579772331215206761212335983767077887317021904201302101419243874026008330353458288184412823212547604923270759971164630393598564301200426360070666188833917710114542628027914809925832609324950589704433584694280875968125203041455013308256704789306513604223110782887488292072231099681750437623820784602978538760390984008234113218524966941965408791461646755157464990070969377989720412687178681164750513807881444198728873187202547028922517516701111579769826080020510348266790930625391759748752153005296836532883070157394243138517291573773976588098266699701426683018242233393485624811215605231297477671514196465153007953743285916239338478218051474828984536127815997012114972587174661437524865517266928559639211752059648489730099860349830264295674369731290364586708707676232519941774358672828344258613203131225856275450244752678455048640400415843102017639179621369688186487707826157674341870013611007174525361990966838471214671779628137096614607920383520693602654452489978743450131044528672434450167967971646400426881175205778043440126147461159149552004913578423035178403541268480674321719234588167995098243906465891558263371905952599564489890711250151732748335710155655007243521528594054862861661877176767098934114265981944971330639968557170413580442863111500848628698710813548281532825806561042964091032986403215231870112342457177424819703051571848547737922837201725686624689547716333777863994745173183930976578054444038489477342507135670857339216268495940706552997228421832423215896549740472577236651007233432889325563099938607048311481964934747030767500838347934632667517506628778317598560810048029881983300190577341693457639793070484757491445343858035938493461882485080144
def packed6_01_11 : ℕ := 131604329323324709799480968120335349649260532231918154973753781304997938147745917797214664533936899203172066672129686731487356661260488830171848650854294552962040721729121214107265303793444600716385348741579424344456829814950267113492550044527680769641360388984974944434561275792824910303568092645017711223464839544509993272908041269378464593776228851262626836910520274105529941753431585924686110384854988573832683745808426417734745302226815003337045304999951847285343645306386691400067571931834582421749402062184524300606918695471361850040284138637628544394208156629576885319085607978741626164938177470713249285825299806756810255467122951053096134778491106418551837527093051902066654235371914484149303854450468407275800897130728764448640291405459691209953687906193835478336730552110128898639026616657745795057538293093783505868128241116079952287878127177108194528760581384164359680050064996979497721492591934445403916992516070555271957503066535652092212681354980295886262578705826236506538633827205272925742817024668648639259364183903227166731681474174790866774309153067893244037628855473040676162016663943309475862863301469022846068338858249026067662627024488336518171102121687802902431691122646007144514044123103368248119565803661377725779756106950838269415860110736361259641560613590976179950749767427055089719576734309962164780664913443980941662016175294200396440217625976118304640838366900531331879522799186181264410384874200826185982793106969492659885181215954649977335666340803449071059563051455169287210636379283339488578879333798458659445384342277678343311363218619129593427279173372993107831523115008
def packed6_01_12 : ℕ := 177950565491274397264923184056943832157954445626091255222924283617597307273151641986476373267319552954305834759429515801315091036983146999216689613240382825896288141703813612759905408635368813353790171678677972084767774856371544276635000181274371754253571700008067347715208104929104588902845199151222210159050449056700055649378957577822797401510572866580393610162974362189512895001369645043998100143913761345121506058514270640646662648561922393616490947985274897492832264453989197433502458959633864893576033886608227372176874501777179379914199635407003705726820980358781751082110906799083345294459685519908454214207384251111630923115891142858500808468240967137599185228091251349205173608423599032006228490963392649935583405354645340172802165977777415006409688328163378933686664240017335204021940405384037598649219858455990119459922162859822346296712046120595816222778785383979793273712186143149062803417979350554900748586632891830009115078273450112336125299857463761747610344408418020124604960014617455861937877408373189374138985726684608373487131197245638929406786615342207914501575858846273881229919039893923344905610043964324417657799119830679701052003382017197599164256890879871762214410769378967169427165843359223939118186152733826060845007450137529285121510409077112250338189154291227920805597470041429125770696250059060591952061147596180129959176683880279448875905442925961452410080294834379309099474262540652943179426589651236903199349836482898472902703076982549746299398411386699116073927006102713407418251875251897163668540793245653915530845363804277930928023240034113781768670862964404243178477824
def packed6_01_20 : ℕ := 58671585070092425777275911888604421772646878065633852326894541546644911682520736231051865988769920451325386517698790825870711881101102316009354561285048416699951767839841685627016482965412742721117611481530816202261038528325051790576199710656829480152795559247634070655164890069164635661767254976956716519598237469453126628624487524630496421108959020641831380833342590428420495317131437246933992380161008315148198148434516232731315300397167293667378671536580881692945765663151528594809513615052441887558877444713267975660426018418822081253097117086075290076480988472809080980602080164474229616743526491855302578830705834233862782290965989863595438812272384651387811663722807822266690702084971179410333616319299138924511607669304141318245532556689077125781610429172420679128833202450249261416213413228767983168133704093933738367997088493536845797606797706531077647914608677226611032572490006261055948863122246227670832468468738952355662163724473346468414557023961633023337546029524030096394776053465427820369844647344967378882242589543585094021606530698978533855290884699936904810621365509711407828909721243796083360483828363662685552708317333986138657195443223567261771096900002282042036143302962043988248994054318446228737308590121560919347329981668510294045581610516714037715397728608414774601832828167143569242483685772413794484328095223766836519137383847828717832527146323746687212792155833329752091482492355245975756900374720778874695182683471814256791232590712055061475484889018257290208324533809452765996656310018908180117640588558409
def packed6_01_21 : ℕ := 54431646305261527820714957318529492855482943517922030967333803192688150482092490645548644729530171005786075713739960793717590741723737782630273467160607286518271801853354775149101249595097209041686428462906173615280174826405037627753795006650547908865132096876843380493137271681176557222404480695050995698765927045346304867325281622109169069180300397113408627108118054769281825944121658775986824973619167809449805842039144693117928810996569069612308457826421551090622178483865956832811803499450585322805655382820310594622733646024117404166118458759851680781024417482802707784804996597468037369140542971931220511190716229990028216149802191464821963005054456766095526936626541690550007380614596255043204103819860667147244255399929552956620371381761630936862018529528129299598044375526284254193776903193929543065604682020356081606812652760165041643933875252580456860942300569340147648579698586034378363411749001985354684223214955019440338104260628058073209585011077628304410016069269390040362422827301094493325036638906299315859239089525319500701743107884810252442250841206590514429624323730186741698722803264717882756518817872284049728563035419260073927268997637080379095159139761138111863224510412371207517187126430220511561503073787077895199516914274307503823441055384441801073232043110659240320302321174962560045981360648503655396242366119888313645786981699301154140346786486739127006878400142722299462666847907382391382708918593812807269948082150521675302983233659624124431781871140083522584317737616612057184846020122817518556811689984
def packed6_01_22 : ℕ := 1700195345410680539636333341223226623440979153043442838014541145257096155159634635365371247120517120546289212227203127290485066646535713277431750909429060237245654217343693147877508839726294707289820421790363742912471497807968866358086875953587431493464159163682012805251785182330097703383995277318441125258748651811245990615012137357843147303481947215579837390125155424182753769971941889103413609829102396345001799947889681659381349017109562641268777340685618454272060116734416065866508199861992851024037808167529043489823677790250024612078806598336342408558072403054040608679694493216373685339582723947037292529001179482448943150230950036042101136791322821378496778419074197251654787897911339692393017115980982063426662625559534479681780923984485218061006042629036980700796106163507321821940481564351130587513280982143579379757903183507832390358210493725436109551527549483084512502738288873107610586796498608232092919832520362530514453996855306451048940863805560218339347710982194688441168288367743773857840453314441370692865862024413703027039168294955220775346389263260689160853530044295656826583934762415547633390967409326312785205531280225559229714553694572541880294311346466257387499622478537188214127560629601844891427843781401042064175718704431512553314029350034303428817517304577538496856144202172484980174434626690886363660048875889983463788360855597987835448885186849047335567417036786958156664252564404192590628354543322909670561244045439086081428028659881216
def weights6_01 : ℕ → ℕ → ℕ
  | 0, 0 => packed6_01_00
  | 0, 1 => packed6_01_01
  | 0, 2 => packed6_01_02
  | 1, 0 => packed6_01_10
  | 1, 1 => packed6_01_11
  | 1, 2 => packed6_01_12
  | 2, 0 => packed6_01_20
  | 2, 1 => packed6_01_21
  | 2, 2 => packed6_01_22
  | _, _ => 0

def packed6_02_00 : ℕ := 3678804351842933816768472888605095637503654575718496804273135302203149855234763020211383354498214519927948449226307379388901888707733139348357722907034587364416354078328421970631192020908620650369998427738652585544810179765181883379242958586478500106227301015060024284188287883311459342494766922452714748249828320358405782984515361205583495496540064148305953810613844000511151534191997894495465502765680229081917352869029148584966678721089884799247177289282382086519721597135665531036534712424858922818348845886606481526561306520989243355795591700570406036701043422673098697217400254549651369850327064363836043370478582410521302907122184595030084455168506702359326681922898343307614541120808161679905411166794544001252530095569573688076846669502097915203603358156918859810724333236299947505496743373362286571532432889761116007955187163693732964600364906901636839297725455502262934655475517268157130614645441666649077257021897399821638470933262583626897468351271840784589643407989760681891476000918924223354887252343766247363217806458613667380435669820293972577106995508953776097316571622314506568448097451879178830237493587062715825486089474546969946062892662379984180309022477650795833478130600610035345207800332633444584586458389375365243380437520313741884961330734679304431703188354437564900493627456146093817280764917881435711014352332940433215158437378971997182654664011458666319752566678160088915327250760326623329034150710066650855969411626646253364387906998508271200632618579484890099209955378747668325410868089015865880177347579422942869151687765729407964114713785550223257791434238621668704026222394054381011681757630047745329658001722210239488893023073724369550874910731885409996181055713895514594173736971425364491160851163815944482636141722784808509896395213864315773180029614664791491482869295338559904028023549904065416784088429803057506637613388975702515057113825942700062
def packed6_02_10 : ℕ := 6277311622586781089435980440630698210131423312663320303730395866585596462458975296153569050776665266932495398084690841821875347507280470423606190528018808332639235578905842603743434386515731600308192120347144703009039468863839610838646583534159202460929331038423141334998633039925036240975888880638998191967494238401987737293793446805711085750641675866440705111134252778502204345866638700466193598010038283205088669929599889876412689809918282115371670248364862009180716428471235574316462076385008255884979776803946397896994681814363978679735976690964181738899218541242583788720779732964709746213212152849742554320314255545181836069371136445579616893592401571620145732065573976047357697056636898773255155784501168883430406070507063454079193956766252702955862460938783553754614003814617606897823686854286718679126202538112888195891709037036508831777292373177733326393104628666281576487415536898198774384716843857775779612453899825565618384137289835243390572363183358615630750136568934588762404578327185093173427179976894618910931529522079126775519678835656877817347300505716698246573289174786655076931756143257621018197093744415240389729993671558575305887294858507578349195186142252671596971763703406654117002841649766618847224596856530068492643035546075760628539965853658505220769821580267761005764638157742545506648671985209019512302851712124879063719814031166165605954377536105270507681437007720181442674808562026086086146933322766939879387562573137583322499197540546898988946909997792285281596531981350641874579102282809509188960892058711404618189097135976797497506317950957599033805313250806684024126820373702936037650079757738270845524884152396555148589038282277745911136348
def packed6_02_20 : ℕ := 14192182798891852897855260126643317692471044011238811121477416741564452176215941707127021830231994381501274218266986200933372704855448948515909814068403311454017545595516289355648982210757155809340552520326004121837597119667194122409517988042025673006761433768612175600123230755015625087136281421623537220475840311297136184541269529151873394962761311086998333881862580203337230364796215190382531785721636055823458700520229006363148719329596526997672410798693248813092263699375236104473084690856549271857364756409505009355930565470692899465574586156828949498866108085077865748600108199737438589894159445309943523881183390807524220489428042110111664152851189407886871763676987862319460244234879782831118771757419371089424785293412877872876495872346760308754351018187558978813287162549046315984372755647068979753246863294254400694098574510696192444275950999044054469243720427400712237222011140669695665095182294601014792415851269070048334735726568945749418108123498701975754625873914574896101722695007314761911970522072552401018765521831988104315007257735543404035976361819854623155777474261764361444667196290872261489271883823351642423801153990528787473393905160056169804716953914589509836104344890187075206660908029910185342215340884192249078403884473919313681255363089068701613832050847197906509271022940286664504216211272857940725563571706661770223284146564807419160791089934247138355660490136736101764012179332415409041737341161332437366778187834381190963854576726383040559774745787451079309758783676988612382611777609667329330257151606720798438859808847477089465030080967191502840911885273554808170417528892657209837730543681183254205984626472527561984707295462588591372238956
def weights6_02 : ℕ → ℕ → ℕ
  | 0, 0 => packed6_02_00
  | 1, 0 => packed6_02_10
  | 2, 0 => packed6_02_20
  | _, _ => 0

def weights6_10 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights6_11 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights6_12 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights6_20 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights6_21 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights6_22 : ℕ → ℕ → ℕ
  | _, _ => 0

def weights6 : WeightData :=
  ![![weights6_00, weights6_01, weights6_02], ![weights6_10, weights6_11, weights6_12], ![weights6_20, weights6_21, weights6_22]]

def weights : Fin 7 → WeightData := ![weights0, weights1, weights2, weights3, weights4, weights5, weights6]

def cubicExponents : Fin 9 → CycleQ2SparseGaussianPolynomial.Exponent :=
  ![(0,0,0,1,1), (0,0,0,3,0), (0,0,3,0,0), (0,1,1,1,0), (0,3,0,0,0), (1,0,1,1,0), (1,2,0,0,0), (2,1,0,0,0), (3,0,0,0,0)]

def cubicPairing : Fin 7 → Fin 9 → ℕ :=
  ![![82, 74, 106, 61, 9, 61, 89, 65, 59], ![83, 106, 27, 64, 21, 64, 4, 41, 2], ![58, 27, 19, 84, 71, 84, 84, 20, 102], ![60, 67, 43, 36, 30, 36, 76, 0, 0], ![54, 48, 29, 10, 25, 10, 84, 3, 48], ![81, 32, 41, 106, 40, 52, 89, 74, 94], ![98, 38, 79, 94, 22, 40, 20, 100, 74]]

def pairingRightInverse : Fin 9 → Fin 7 → ℕ :=
  ![![39, 63, 86, 102, 46, 0, 0], ![36, 78, 22, 103, 73, 58, 51], ![99, 29, 15, 103, 105, 85, 24], ![0, 2, 37, 74, 7, 36, 71], ![43, 28, 36, 106, 9, 81, 28], ![36, 71, 40, 20, 64, 83, 28], ![64, 102, 7, 1, 15, 29, 80], ![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0]]

end CycleQ2SegreModularDetectorData
end


/- Component: continuation_3/cylinder_bridge/SegreRelationsLocal.lean -/
section
/-! # Local exactness at the actual sixteen Segre relations

The literal relation rows first identify two scalar matrix products.  On a
unit-entry chart of the rank-one locus both scalars vanish.  A concrete lift
then proves exactness at the cofactor-variation term over an arbitrary
commutative ring.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace CycleQ2SegreRelationsLocal

open Matrix CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal
open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- The same row-major order as the nine published cofactor equations. -/
def vector (C : Matrix (Fin 3) (Fin 3) R) : Fin 9 → R :=
  ![C 0 0,C 0 1,C 0 2,C 1 0,C 1 1,C 1 2,C 2 0,C 2 1,C 2 2]

def leftProduct (M C : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) : R :=
  ∑ k, M i k*C j k

def rightProduct (M C : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) : R :=
  ∑ k, M k i*C k j

def ScalarProducts (M C : Matrix (Fin 3) (Fin 3) R) : Prop :=
  ∃ a b : R, (∀ i j, leftProduct M C i j=if i=j then a else 0) ∧
    (∀ i j, rightProduct M C i j=if i=j then b else 0)

theorem relations_mul_vector (M C : Matrix (Fin 3) (Fin 3) R) :
    CycleQ2SegreRelations.relations M *ᵥ vector C=
      ![leftProduct M C 0 1,
        leftProduct M C 0 2,
        leftProduct M C 1 0,
        leftProduct M C 1 2,
        leftProduct M C 2 0,
        leftProduct M C 2 1,
        rightProduct M C 1 0,
        rightProduct M C 2 0,
        rightProduct M C 0 1,
        rightProduct M C 2 1,
        rightProduct M C 0 2,
        rightProduct M C 1 2,
        leftProduct M C 1 1-leftProduct M C 0 0,
        leftProduct M C 2 2-leftProduct M C 0 0,
        rightProduct M C 1 1-rightProduct M C 0 0,
        rightProduct M C 2 2-rightProduct M C 0 0] := by
  funext k
  fin_cases k <;>
    norm_num [CycleQ2SegreRelations.relations,vector,Matrix.mulVec,dotProduct,
      leftProduct,rightProduct,Fin.sum_univ_succ,Matrix.cons_val_succ] <;> ring

/-- The sixteen concrete rows are exactly the off-diagonal vanishing and
same-diagonal identities for `M*Cᵀ` and `Mᵀ*C`. -/
theorem relations_zero_iff_scalarProducts (M C : Matrix (Fin 3) (Fin 3) R) :
    CycleQ2SegreRelations.relations M *ᵥ vector C=0 ↔ ScalarProducts M C := by
  constructor
  · intro h
    rw [relations_mul_vector] at h
    have h0 : leftProduct M C 0 1=0 := congrFun h 0
    have h1 : leftProduct M C 0 2=0 := congrFun h 1
    have h2 : leftProduct M C 1 0=0 := congrFun h 2
    have h3 : leftProduct M C 1 2=0 := congrFun h 3
    have h4 : leftProduct M C 2 0=0 := congrFun h 4
    have h5 : leftProduct M C 2 1=0 := congrFun h 5
    have h6 : rightProduct M C 1 0=0 := congrFun h 6
    have h7 : rightProduct M C 2 0=0 := congrFun h 7
    have h8 : rightProduct M C 0 1=0 := congrFun h 8
    have h9 : rightProduct M C 2 1=0 := congrFun h 9
    have h10 : rightProduct M C 0 2=0 := congrFun h 10
    have h11 : rightProduct M C 1 2=0 := congrFun h 11
    have h12 : leftProduct M C 1 1-leftProduct M C 0 0=0 := congrFun h 12
    have h13 : leftProduct M C 2 2-leftProduct M C 0 0=0 := congrFun h 13
    have h14 : rightProduct M C 1 1-rightProduct M C 0 0=0 := congrFun h 14
    have h15 : rightProduct M C 2 2-rightProduct M C 0 0=0 := congrFun h 15
    refine ⟨leftProduct M C 0 0,rightProduct M C 0 0,?_,?_⟩
    · intro i j
      fin_cases i <;> fin_cases j <;> norm_num <;> solve
        | exact h0 | exact h1 | exact h2 | exact h3 | exact h4 | exact h5
        | exact sub_eq_zero.mp h12 | exact sub_eq_zero.mp h13
    · intro i j
      fin_cases i <;> fin_cases j <;> norm_num <;> solve
        | exact h6 | exact h7 | exact h8 | exact h9 | exact h10 | exact h11
        | exact sub_eq_zero.mp h14 | exact sub_eq_zero.mp h15
  · rintro ⟨a,b,hl,hr⟩
    rw [relations_mul_vector]
    funext k
    fin_cases k <;>
      simp [hl,hr]

/-- Rank-one factorization with a unit pivot forces both scalar products to
vanish; no invertibility of 2 or 3 is used. -/
theorem products_zero_of_scalarProducts (M C : Matrix (Fin 3) (Fin 3) R)
    (hM : CycleQ2SegreLocal.cofactors M=0) (hs : ScalarProducts M C)
    (i0 j0 : Fin 3) (u : Rˣ) (hu : (u : R)=M i0 j0) :
    (∀ i j, leftProduct M C i j=0) ∧ (∀ i j, rightProduct M C i j=0) := by
  obtain ⟨a,b,hl,hr⟩ := hs
  have hlf (i j : Fin 3) : leftProduct M C i j=
      (M i j0*(↑(u⁻¹) : R))*leftProduct M C i0 j := by
    simp only [leftProduct,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [CycleQ2SegreLocal.unit_pivot_factorization M hM i0 j0 u hu i k]
    ring
  have hrf (i j : Fin 3) : rightProduct M C i j=
      (M i0 i*(↑(u⁻¹) : R))*rightProduct M C j0 j := by
    simp only [rightProduct,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [CycleQ2SegreLocal.unit_pivot_factorization M hM i0 j0 u hu k i]
    ring
  obtain ⟨i1,hi1⟩ : ∃ i1 : Fin 3, i1≠i0 := exists_ne i0
  obtain ⟨j1,hj1⟩ : ∃ j1 : Fin 3, j1≠j0 := exists_ne j0
  have ha : a=0 := by
    have hh := hlf i1 i1
    rw [hl i1 i1,hl i0 i1] at hh
    simpa [Ne.symm hi1] using hh
  have hb : b=0 := by
    have hh := hrf j1 j1
    rw [hr j1 j1,hr j0 j1] at hh
    simpa [Ne.symm hj1] using hh
  constructor
  · intro i j
    simp [hl,ha]
  · intro i j
    simp [hr,hb]

/-- On a unit chart the literal sixteen relations are equivalent to the two
actual annihilator identities. -/
theorem relations_zero_iff_products_zero (M C : Matrix (Fin 3) (Fin 3) R)
    (hM : CycleQ2SegreLocal.cofactors M=0)
    (i0 j0 : Fin 3) (u : Rˣ) (hu : (u : R)=M i0 j0) :
    CycleQ2SegreRelations.relations M *ᵥ vector C=0 ↔
      (∀ i j, leftProduct M C i j=0) ∧ (∀ i j, rightProduct M C i j=0) := by
  rw [relations_zero_iff_scalarProducts]
  constructor
  · exact fun hs => products_zero_of_scalarProducts M C hM hs i0 j0 u hu
  · rintro ⟨hl,hr⟩
    exact ⟨0,0,by simpa using hl,by simpa using hr⟩

/-- An explicit lift at the `(0,0)` pivot. -/
def pivotLift (u : Rˣ) (C : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  fun i j => if i=1 then
    if j=1 then (↑(u⁻¹) : R)*C 2 2 else if j=2 then -((↑(u⁻¹) : R)*C 2 1) else 0
  else if i=2 then
    if j=1 then -((↑(u⁻¹) : R)*C 1 2) else if j=2 then (↑(u⁻¹) : R)*C 1 1 else 0
  else 0

theorem pivotLift_differential (M C : Matrix (Fin 3) (Fin 3) R)
    (hl : ∀ i j, leftProduct M C i j=0)
    (hr : ∀ i j, rightProduct M C i j=0)
    (u : Rˣ) (hu : (u : R)=M 0 0) :
    cofactorDifferential M (pivotLift u C)=C := by
  have h01 := hl 0 1
  have h02 := hl 0 2
  have h11 := hl 1 1
  have h22 := hl 2 2
  have k00 := hr 0 0
  have k01 := hr 0 1
  have k02 := hr 0 2
  norm_num [leftProduct,rightProduct,Fin.sum_univ_succ,← hu] at h01 h02 h11 h22 k00 k01 k02
  have hunit : (u : R)*(↑(u⁻¹) : R)=1 := u.mul_inv
  have hfin2 (h : 2<3) : (⟨2,h⟩ : Fin 3)=2 := rfl
  have hn01 : (0 : Fin 3)≠1 := by decide
  have hn02 : (0 : Fin 3)≠2 := by decide
  have hn12 : (1 : Fin 3)≠2 := by decide
  have hn21 : (2 : Fin 3)≠1 := by decide
  rw [cofactorDifferential_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pivotLift,Matrix.cons_val_succ,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Fin.reduceFinMk,hfin2,hn01,hn02,hn12,hn21,← hu] <;> solve
    | linear_combination (↑(u⁻¹) : R)*(h11+h22-k00)+C 0 0*hunit
    | linear_combination -(↑(u⁻¹) : R)*k01+C 0 1*hunit
    | linear_combination -(↑(u⁻¹) : R)*k02+C 0 2*hunit
    | linear_combination -(↑(u⁻¹) : R)*h01+C 1 0*hunit
    | linear_combination C 1 1*hunit
    | linear_combination C 1 2*hunit
    | linear_combination -(↑(u⁻¹) : R)*h02+C 2 0*hunit

end CycleQ2SegreRelationsLocal
end
end


/- Component: continuation_3/SparseGaussianAction.lean -/
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false

namespace CycleQ2SparseGaussianPolynomial

def applyBlock (action : ℕ → ℕ → Towers) (b : ℕ) : ℕ → Blocks → Towers
  | _, [] => []
  | a, c::p => addTowers (scaleTower c (action a b)) (applyBlock action b (a+1) p)

def applyTowersFrom (action : ℕ → ℕ → Towers) : ℕ → Towers → Towers
  | _, [] => []
  | b, q::p => addTowers (applyBlock action b 0 q) (applyTowersFrom action (b+1) p)

def applyTowers (action : ℕ → ℕ → Towers) (p : Towers) : Towers :=
  applyTowersFrom action 0 p

def checkLayers (p : Layers) : Bool := p.all checkZero
def checkBlocks (p : Blocks) : Bool := p.all checkLayers
def checkTowers (p : Towers) : Bool := p.all checkBlocks
def checkTowerBlock (p : Towers) (b a : ℕ) : Bool :=
  checkLayers ((p[b]?.getD [])[a]?.getD [])

section Soundness
variable {R : Type*} [CommRing R]
variable (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)

theorem evalLayers_eq_zero_of_checkLayers (p : Layers) (h : checkLayers p = true) :
    evalLayers φ x v p = 0 := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    simp only [checkLayers, List.all_cons, Bool.and_eq_true] at h
    rw [evalLayers, eval_eq_zero_of_check φ x c h.1, ih h.2, mul_zero, add_zero]

theorem evalBlocks_eq_zero_of_checkBlocks (p : Blocks) (h : checkBlocks p = true) :
    evalBlocks φ x z v p = 0 := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    simp only [checkBlocks, List.all_cons, Bool.and_eq_true] at h
    rw [evalBlocks, evalLayers_eq_zero_of_checkLayers φ x v c h.1,
      ih h.2, mul_zero, add_zero]

theorem evalTowers_eq_zero_of_checkTowers (p : Towers) (h : checkTowers p = true) :
    evalTowers φ x w z v p = 0 := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    simp only [checkTowers, List.all_cons, Bool.and_eq_true] at h
    rw [evalTowers, evalBlocks_eq_zero_of_checkBlocks φ x z v c h.1,
      ih h.2, mul_zero, add_zero]

theorem evalBlocks_eq_zero_of_layer_checks (N : ℕ) (p : Blocks)
    (hlen : p.length ≤ N)
    (h : ∀ n : Fin N, checkLayers (p[n.val]?.getD []) = true) :
    evalBlocks φ x z v p = 0 := by
  induction N generalizing p with
  | zero =>
    have hp : p = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    rw [hp, evalBlocks]
  | succ N ih =>
    cases p with
    | nil => rfl
    | cons a p =>
      have ha : checkLayers a = true := by
        simpa only [Fin.val_zero, List.getElem?_cons_zero, Option.getD_some] using h 0
      have hp : p.length ≤ N := Nat.succ_le_succ_iff.mp hlen
      have hh : ∀ n : Fin N, checkLayers (p[n.val]?.getD []) = true := by
        intro n
        simpa only [Fin.val_succ, List.getElem?_cons_succ] using h n.succ
      rw [evalBlocks, evalLayers_eq_zero_of_checkLayers φ x v a ha,
        ih p hp hh, mul_zero, add_zero]

theorem evalTowers_eq_zero_of_block_checks (N M : ℕ) (p : Towers)
    (hlen : p.length ≤ N)
    (hinner : ∀ n : Fin N, (p[n.val]?.getD []).length ≤ M)
    (h : ∀ n : Fin N, ∀ m : Fin M, checkTowerBlock p n m = true) :
    evalTowers φ x w z v p = 0 := by
  induction N generalizing p with
  | zero =>
    have hp : p = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    rw [hp, evalTowers]
  | succ N ih =>
    cases p with
    | nil => rfl
    | cons a p =>
      have hla : a.length ≤ M := by
        simpa only [Fin.val_zero, List.getElem?_cons_zero, Option.getD_some] using hinner 0
      have ha : evalBlocks φ x z v a = 0 :=
        evalBlocks_eq_zero_of_layer_checks φ x z v M a hla (fun m => by
          simpa only [checkTowerBlock, Fin.val_zero, List.getElem?_cons_zero,
            Option.getD_some] using h 0 m)
      have hp : p.length ≤ N := Nat.succ_le_succ_iff.mp hlen
      have hli : ∀ n : Fin N, (p[n.val]?.getD []).length ≤ M := by
        intro n
        simpa only [Fin.val_succ, List.getElem?_cons_succ] using hinner n.succ
      have hh : ∀ n : Fin N, ∀ m : Fin M, checkTowerBlock p n m = true := by
        intro n m
        simpa only [checkTowerBlock, Fin.val_succ, List.getElem?_cons_succ] using h n.succ m
      rw [evalTowers, ha, ih p hp hli hh, mul_zero, add_zero]

variable (action : ℕ → ℕ → Towers) (c : R)
variable (haction : ∀ a b, evalTowers φ x w z v (action a b) = c * z^a * w^b)
include haction

theorem eval_applyBlock (b a : ℕ) (p : Blocks) :
    evalTowers φ x w z v (applyBlock action b a p) =
      c * z^a * w^b * evalBlocks φ x z v p := by
  induction p generalizing a with
  | nil => simp [applyBlock, evalTowers, evalBlocks]
  | cons q p ih =>
    simp only [applyBlock, eval_addTowers, eval_scaleTower, haction, ih,
      evalBlocks, pow_succ]
    ring

theorem eval_applyTowersFrom (b : ℕ) (p : Towers) :
    evalTowers φ x w z v (applyTowersFrom action b p) =
      c * w^b * evalTowers φ x w z v p := by
  induction p generalizing b with
  | nil => simp [applyTowersFrom, evalTowers]
  | cons q p ih =>
    simp only [applyTowersFrom, eval_addTowers,
      eval_applyBlock φ x w z v action c haction, ih, evalTowers, pow_zero, pow_succ]
    ring

theorem eval_applyTowers (p : Towers) :
    evalTowers φ x w z v (applyTowers action p) = c * evalTowers φ x w z v p := by
  simpa only [applyTowers, pow_zero, mul_one] using
    eval_applyTowersFrom φ x w z v action c haction 0 p

end Soundness
end CycleQ2SparseGaussianPolynomial

#print axioms CycleQ2SparseGaussianPolynomial.eval_applyTowers
#print axioms CycleQ2SparseGaussianPolynomial.evalTowers_eq_zero_of_block_checks
end


/- Component: continuation_3/SparseGaussianGrading.lean -/
section
/-! The concrete sparse witnesses are standard homogeneous chart polynomials. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SparseGaussianPolynomial

open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations

def shift (e : Exponent) (p : Sparse) : Sparse :=
  p.map (fun a => (exponentAdd e a.1, a.2))

def flattenLayers : Layers → Sparse
  | [] => []
  | a::p => a ++ shift (0,1,0,0,0) (flattenLayers p)

def flattenBlocks : Blocks → Sparse
  | [] => []
  | a::p => flattenLayers a ++ shift (1,0,0,0,0) (flattenBlocks p)

def flattenTowers : Towers → Sparse
  | [] => []
  | a::p => flattenBlocks a ++ shift (0,0,0,0,1) (flattenTowers p)

def tupleFun (e : Exponent) : Fin 5 → ℕ := ![e.1, e.2.1, e.2.2.1, e.2.2.2.1, e.2.2.2.2]

def goodTerm (d : ℕ) (a : Term) : Bool :=
  decide (fullDegree (tupleFun a.1) = d ∧ fullCharacter (tupleFun a.1) = 0 ∧
    a.1.1 < 3 ∧ a.1.2.2.2.2 < 3)

def goodPolynomial (d : ℕ) (p : Sparse) : Bool := p.all (goodTerm d)
def goodTowers (d : ℕ) (p : Towers) : Bool := goodPolynomial d (flattenTowers p)

noncomputable section
variable {R : Type*} [CommRing R]
variable (φ : GaussianInt →+* R)

theorem termValue_shift (x : Fin 5 → R) (e : Exponent) (a : Term) :
    termValue φ x (exponentAdd e a.1, a.2) = monomial x e * termValue φ x a := by
  simp only [termValue, monomial_exponentAdd]
  ring

theorem eval_shift (x : Fin 5 → R) (e : Exponent) (p : Sparse) :
    eval φ x (shift e p) = monomial x e * eval φ x p := by
  simp only [eval, shift, List.map_map, Function.comp_def, termValue_shift,
    List.sum_map_mul_left]

theorem eval_flattenLayers (x : Fin 5 → R) (p : Layers) :
    eval φ x (flattenLayers p) = evalLayers φ x (x 1) p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [flattenLayers, eval_append, eval_shift, ih, evalLayers]
    simp [monomial]

theorem eval_flattenBlocks (x : Fin 5 → R) (p : Blocks) :
    eval φ x (flattenBlocks p) = evalBlocks φ x (x 0) (x 1) p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [flattenBlocks, eval_append, eval_shift, eval_flattenLayers, ih, evalBlocks]
    simp [monomial]

theorem eval_flattenTowers (x : Fin 5 → R) (p : Towers) :
    eval φ x (flattenTowers p) = evalTowers φ x (x 4) (x 0) (x 1) p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [flattenTowers, eval_append, eval_shift, eval_flattenBlocks, ih, evalTowers]
    simp [monomial]

def tupleExponent (e : Exponent) : Fin 5 →₀ ℕ := Finsupp.equivFunOnFinite.symm (tupleFun e)

@[simp] theorem tupleExponent_apply (e : Exponent) (i : Fin 5) :
    tupleExponent e i = tupleFun e i := rfl

theorem monomial_variables (e : Exponent) :
    monomial (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R) e =
      MvPolynomial.monomial (tupleExponent e) 1 := by
  simp only [monomial, MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, one_mul]
  apply congrArg (fun d : Fin 5 →₀ ℕ => MvPolynomial.monomial d (1 : R))
  ext i
  fin_cases i <;>
    simp [tupleExponent, tupleFun, Finsupp.single_apply, Fin.ext_iff]

theorem termValue_variables (a : Term) :
    termValue (MvPolynomial.C.comp φ) (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R) a =
      MvPolynomial.monomial (tupleExponent a.1) (φ a.2) := by
  rw [termValue, monomial_variables]
  simp only [RingHom.comp_apply, MvPolynomial.C_mul_monomial, mul_one]

theorem goodTerm_evaluation (d : ℕ) (a : Term) (h : goodTerm d a = true) :
    FullStandard (termValue (MvPolynomial.C.comp φ) (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R) a) ∧
      HG (termValue (MvPolynomial.C.comp φ) (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R) a) (d,0) := by
  have ha : fullDegree (tupleFun a.1) = d ∧ fullCharacter (tupleFun a.1) = 0 ∧
      a.1.1 < 3 ∧ a.1.2.2.2.2 < 3 := of_decide_eq_true h
  rw [termValue_variables]
  constructor
  · intro e he
    have heq : e = tupleExponent a.1 :=
      Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset he)
    subst e
    change a.1.1 < 3 ∧ a.1.2.2.2.2 < 3
    exact ha.2.2
  · apply MvPolynomial.isWeightedHomogeneous_monomial
    apply (fullGrading_eq_iff _ _).mpr
    exact ⟨ha.1, ha.2.1⟩

theorem goodPolynomial_evaluation (d : ℕ) (p : Sparse) (h : goodPolynomial d p = true) :
    FullStandard (eval (MvPolynomial.C.comp φ) (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R) p) ∧
      HG (eval (MvPolynomial.C.comp φ) (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R) p) (d,0) := by
  induction p with
  | nil =>
    constructor
    · simp [FullStandard]
    · exact (MvPolynomial.weightedHomogeneousSubmodule R fullGrading (d,0)).zero_mem
  | cons a p ih =>
    simp only [goodPolynomial, List.all_cons, Bool.and_eq_true] at h
    have ha := goodTerm_evaluation (R := R) φ d a h.1
    have hp := ih h.2
    rw [eval_cons]
    exact ⟨CycleQ2IncidenceJacobian.fullStandard_add ha.1 hp.1, ha.2.add hp.2⟩

/-- Degree, invariant character, and standardness of the literal three-level data. -/
theorem goodTowers_evaluation (d : ℕ) (p : Towers) (h : goodTowers d p = true) :
    FullStandard (evalTowers (MvPolynomial.C.comp φ)
      (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R)
      (MvPolynomial.X 4) (MvPolynomial.X 0) (MvPolynomial.X 1) p) ∧
    HG (evalTowers (MvPolynomial.C.comp φ)
      (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R)
      (MvPolynomial.X 4) (MvPolynomial.X 0) (MvPolynomial.X 1) p) (d,0) := by
  rw [← eval_flattenTowers]
  exact goodPolynomial_evaluation φ d (flattenTowers p) h

end
end CycleQ2SparseGaussianPolynomial

#print axioms CycleQ2SparseGaussianPolynomial.goodTowers_evaluation
end


/- Component: continuation_3/SparseModularFastDot.lean -/
section
/-! A compact, proved encoding for coefficient-functional evaluation.
The coefficient is reduced once when a table is encoded; subsequent shifts
only add to its one-dimensional coefficient index. -/

namespace CycleQ2SparseModularFastDot
open CycleQ2SparseModularFunctional CycleQ2SparseGaussianPolynomial

abbrev FastTerm := ℕ × ℕ × ℕ × ℕ

def encodeTerm (t : Term) : FastTerm :=
  (t.1.2.2.2.2,t.1.1,t.1.2.1+29*t.1.2.2.1,gmod t.2)

def encode (p : Sparse) : List FastTerm := p.map encodeTerm

def fastDot (W : WeightData) (i j : Fin 3) (s : ℕ) : List FastTerm → ℕ
  | [] => 0
  | t::p =>
    let c := slot (W i j t.1 t.2.1) (s+t.2.2.1)
    if c=0 then fastDot W i j s p else (t.2.2.2*c+fastDot W i j s p)%109

theorem fastDot_encode (W : WeightData) (i j : Fin 3) (u v c : ℕ) (p : Sparse) :
    fastDot W i j (u+29*v) (encode p)=dot W i j (0,u,v,c,0) p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    have h : (u+29*v)+(t.1.2.1+29*t.1.2.2.1)=
        (u+t.1.2.1)+29*(v+t.1.2.2.1) := by omega
    simp only [encode,List.map_cons,fastDot,encodeTerm,dot,weight,exponentAdd,
      zero_add,h] at ⊢
    change (if slot (W i j t.1.2.2.2.2 t.1.1)
        (u+t.1.2.1+29*(v+t.1.2.2.1))=0 then
          fastDot W i j (u+29*v) (encode p)
        else (gmod t.2 * slot (W i j t.1.2.2.2.2 t.1.1)
          (u+t.1.2.1+29*(v+t.1.2.2.1))+fastDot W i j (u+29*v) (encode p))%109)=_
    rw [ih]

abbrev WordTerm := ℕ × ℕ
abbrev FastBlock := ℕ × ℕ × List WordTerm

def dotWord (n s tail : ℕ) : List WordTerm → ℕ
  | [] => tail
  | t::p =>
    let c := slot n (s+t.1)
    if c=0 then dotWord n s tail p else (t.2*c+dotWord n s tail p)%109

def groupedDot (W : WeightData) (i j : Fin 3) (s : ℕ) : List FastBlock → ℕ
  | [] => 0
  | b::bs =>
    let n := W i j b.1 b.2.1
    if n=0 then groupedDot W i j s bs
    else dotWord n s (groupedDot W i j s bs) b.2.2

def flattenBlock (b : FastBlock) : List FastTerm :=
  b.2.2.map (fun t => (b.1,b.2.1,t.1,t.2))

def flattenGrouped (bs : List FastBlock) : List FastTerm := bs.flatMap flattenBlock

theorem dotWord_zero (s tail : ℕ) (p : List WordTerm) : dotWord 0 s tail p=tail := by
  induction p with
  | nil => rfl
  | cons t p ih => simp [dotWord,slot,ih]

theorem fastDot_block_append (W : WeightData) (i j : Fin 3) (s w z : ℕ)
    (p : List WordTerm) (q : List FastTerm) :
    fastDot W i j s (flattenBlock (w,z,p)++q)=
      dotWord (W i j w z) s (fastDot W i j s q) p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    simp only [flattenBlock,List.map_cons,List.cons_append,fastDot,dotWord] at ⊢
    change (if slot (W i j w z) (s+t.1)=0 then
      fastDot W i j s (flattenBlock (w,z,p)++q) else
      (t.2*slot (W i j w z) (s+t.1)+fastDot W i j s (flattenBlock (w,z,p)++q))%109)=_
    rw [ih]

theorem groupedDot_eq (W : WeightData) (i j : Fin 3) (s : ℕ) (bs : List FastBlock) :
    groupedDot W i j s bs=fastDot W i j s (flattenGrouped bs) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rcases b with ⟨w,z,p⟩
    simp only [groupedDot,flattenGrouped,List.flatMap_cons]
    rw [fastDot_block_append]
    change _ = dotWord (W i j w z) s (fastDot W i j s (flattenGrouped bs)) p
    rw [←ih]
    split_ifs with h
    · rw [h,dotWord_zero]
    · rfl

end CycleQ2SparseModularFastDot

#print axioms CycleQ2SparseModularFastDot.fastDot_encode
end


/- Component: continuation_3/SparseModularGrading.lean -/
section
/-! The concrete sparse witnesses are standard homogeneous chart polynomials. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SparseModularPolynomial

open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations

def shift (e : Exponent) (p : Sparse) : Sparse :=
  p.map (fun a => (exponentAdd e a.1, a.2))

def flattenLayers : Layers → Sparse
  | [] => []
  | a::p => a ++ shift (0,0,0,0,1) (flattenLayers p)

def flattenBlocks : Blocks → Sparse
  | [] => []
  | a::p => flattenLayers a ++ shift (1,0,0,0,0) (flattenBlocks p)

def tupleFun (e : Exponent) : Fin 5 → ℕ := ![e.1, e.2.1, e.2.2.1, e.2.2.2.1, e.2.2.2.2]

def goodTerm (d : ℕ) (a : Term) : Bool :=
  decide (fullDegree (tupleFun a.1) = d ∧ fullCharacter (tupleFun a.1) = 0 ∧
    a.1.1 < 3 ∧ a.1.2.2.2.2 < 3)

def goodPolynomial (d : ℕ) (p : Sparse) : Bool := p.all (goodTerm d)
def goodBlocks (d : ℕ) (p : Blocks) : Bool := goodPolynomial d (flattenBlocks p)

noncomputable section
variable {R : Type*} [CommRing R] [CharP R 109]

theorem termValue_shift (x : Fin 5 → R) (e : Exponent) (a : Term) :
    termValue x (exponentAdd e a.1, a.2) = monomial x e * termValue x a := by
  simp only [termValue, monomial_exponentAdd]
  ring

theorem eval_shift (x : Fin 5 → R) (e : Exponent) (p : Sparse) :
    eval x (shift e p) = monomial x e * eval x p := by
  simp only [eval, shift, List.map_map, Function.comp_def, termValue_shift,
    List.sum_map_mul_left]

theorem eval_flattenLayers (x : Fin 5 → R) (p : Layers) :
    eval x (flattenLayers p) = evalLayers x (x 4) p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [flattenLayers, eval_append, eval_shift, ih, evalLayers]
    simp [monomial]

theorem eval_flattenBlocks (x : Fin 5 → R) (p : Blocks) :
    eval x (flattenBlocks p) = evalBlocks x (x 0) (x 4) p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [flattenBlocks, eval_append, eval_shift, eval_flattenLayers, ih, evalBlocks]
    simp [monomial]

def tupleExponent (e : Exponent) : Fin 5 →₀ ℕ := Finsupp.equivFunOnFinite.symm (tupleFun e)

@[simp] theorem tupleExponent_apply (e : Exponent) (i : Fin 5) :
    tupleExponent e i = tupleFun e i := rfl

theorem monomial_variables (e : Exponent) :
    monomial (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R) e =
      MvPolynomial.monomial (tupleExponent e) 1 := by
  simp only [monomial, MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, one_mul]
  apply congrArg (fun d : Fin 5 →₀ ℕ => MvPolynomial.monomial d (1 : R))
  ext i
  fin_cases i <;>
    simp [tupleExponent, tupleFun, Finsupp.single_apply, Fin.ext_iff]

theorem termValue_variables (a : Term) :
    termValue (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R) a =
      MvPolynomial.monomial (tupleExponent a.1) (a.2 : R) := by
  rw [termValue, monomial_variables]
  rw [← map_natCast (MvPolynomial.C : R →+* MvPolynomial (Fin 5) R) a.2,
    MvPolynomial.C_mul_monomial, mul_one]

theorem goodTerm_evaluation (d : ℕ) (a : Term) (h : goodTerm d a = true) :
    FullStandard (termValue (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R) a) ∧
      HG (termValue (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R) a) (d,0) := by
  have ha : fullDegree (tupleFun a.1) = d ∧ fullCharacter (tupleFun a.1) = 0 ∧
      a.1.1 < 3 ∧ a.1.2.2.2.2 < 3 := of_decide_eq_true h
  rw [termValue_variables]
  constructor
  · intro e he
    have heq : e = tupleExponent a.1 :=
      Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset he)
    subst e
    change a.1.1 < 3 ∧ a.1.2.2.2.2 < 3
    exact ha.2.2
  · apply MvPolynomial.isWeightedHomogeneous_monomial
    apply (fullGrading_eq_iff _ _).mpr
    exact ⟨ha.1, ha.2.1⟩

theorem goodPolynomial_evaluation (d : ℕ) (p : Sparse) (h : goodPolynomial d p = true) :
    FullStandard (eval (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R) p) ∧
      HG (eval (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R) p) (d,0) := by
  induction p with
  | nil =>
    constructor
    · simp [FullStandard]
    · exact (MvPolynomial.weightedHomogeneousSubmodule R fullGrading (d,0)).zero_mem
  | cons a p ih =>
    simp only [goodPolynomial, List.all_cons, Bool.and_eq_true] at h
    have ha := goodTerm_evaluation (R := R) d a h.1
    have hp := ih h.2
    rw [eval_cons]
    exact ⟨CycleQ2IncidenceJacobian.fullStandard_add ha.1 hp.1, ha.2.add hp.2⟩

/-- This checks both the invariant weighted degree and the two standard-monomial
bounds of the literal chart, directly from the numerical witness coefficients. -/
theorem goodBlocks_evaluation (d : ℕ) (p : Blocks) (h : goodBlocks d p = true) :
    FullStandard (evalBlocks (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R)
      (MvPolynomial.X 0) (MvPolynomial.X 4) p) ∧
    HG (evalBlocks (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R)
      (MvPolynomial.X 0) (MvPolynomial.X 4) p) (d,0) := by
  rw [← eval_flattenBlocks]
  exact goodPolynomial_evaluation d (flattenBlocks p) h

end
end CycleQ2SparseModularPolynomial

#print axioms CycleQ2SparseModularPolynomial.goodBlocks_evaluation
end


/- Component: continuation_3/CurveQuotientFiniteFree.lean -/
section
/-!
# The actual two curve quotients are finite free over two base coordinates

Both quotients retain their original checked equations. Their six basis
vectors are x0^a*x2^b, with the respective bounds(2,3) and(3,2).
-/

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveQuotientFiniteFree

open MvPolynomial CycleQ2CurveRestriction CycleQ2IncidenceNormalForm
open scoped MonomialOrder

variable (R : Type*) [CommRing R]

abbrev Base := MvPolynomial (Fin 2) R
abbrev Nested := MvPolynomial (Fin 2) (Base R)
abbrev ShiftIndex (s : Side) := Fin (xBound s) × Fin (zBound s)

def splitIndex : Fin 4 ≃ Fin 2 ⊕ Fin 2 where
  toFun := ![Sum.inl 0,Sum.inr 0,Sum.inl 1,Sum.inr 1]
  invFun := Sum.elim ![0,2] ![1,3]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by cases i with
    | inl i => fin_cases i <;> rfl
    | inr i => fin_cases i <;> rfl

def remainingIndex (i : Fin 2) : Fin 4 := ![1,3] i

def regroup : CurvePoly R ≃ₐ[R] Nested R :=
  (renameEquiv R splitIndex).trans (sumAlgEquiv R (Fin 2) (Fin 2))

@[simp] theorem regroup_C (c : R) : regroup R (C c)=C (C c) := by simp [regroup]
@[simp] theorem regroup_X_zero : regroup R (X 0)=X 0 := by simp [regroup,splitIndex]
@[simp] theorem regroup_X_one : regroup R (X 1)=C (X 0) := by simp [regroup,splitIndex]
@[simp] theorem regroup_X_two : regroup R (X 2)=X 1 := by simp [regroup,splitIndex]
@[simp] theorem regroup_X_three : regroup R (X 3)=C (X 1) := by simp [regroup,splitIndex]

def remainingInclusion : Base R →ₐ[R] CurvePoly R := rename remainingIndex

theorem regroup_remaining (p : Base R) : regroup R (remainingInclusion R p)=C p := by
  have h : (regroup R).toAlgHom.comp (remainingInclusion R)=
      IsScalarTower.toAlgHom R (Base R) (Nested R) := by
    ext i
    fin_cases i <;> simp [remainingInclusion,remainingIndex]
  exact congrArg (fun f : Base R →ₐ[R] Nested R => f p) h

instance remainingAlgebra : Algebra (Base R) (CurvePoly R) :=
  (remainingInclusion R).toRingHom.toAlgebra

def regroupOverBase : CurvePoly R ≃ₐ[Base R] Nested R where
  toRingEquiv := (regroup R).toRingEquiv
  commutes' p := regroup_remaining R p

def nestedWeight : (Fin 2 →₀ ℕ) →+ ℕ where
  toFun e := 3*e 0+4*e 1
  map_zero' := by simp
  map_add' a b := by simp only [Finsupp.add_apply]; omega

def nestedOrder : MonomialOrder (Fin 2) := weightedOrder MonomialOrder.lex nestedWeight

def qLead : Side → (Fin 2 →₀ ℕ)
  | .left => Finsupp.single 0 2
  | .right => Finsupp.single 1 2

def hLead : Side → (Fin 2 →₀ ℕ)
  | .left => Finsupp.single 1 3
  | .right => Finsupp.single 0 3

def qTail : Side → (Fin 2 →₀ ℕ)
  | .left => 0
  | .right => Finsupp.single 0 2

def qCoefficient (s : Side) (r : R) : Base R :=
  match s with
  | .left => -(C r*X 0*X 1)
  | .right => 1

def hTail (s : Side) : Fin 4 → (Fin 2 →₀ ℕ) :=
  match s with
  | .left => ![Finsupp.single 0 1+Finsupp.single 1 1,Finsupp.single 1 1,Finsupp.single 0 1,0]
  | .right => ![Finsupp.single 0 2,Finsupp.single 0 1,Finsupp.single 1 1,0]

def hCoefficient (s : Side) (r ι : R) : Fin 4 → Base R :=
  match s with
  | .left => ![X 1,X 0*X 1,X 0^2+C r*X 0*X 1,C (1-ι)*X 1^3-C ι*X 0^3]
  | .right => ![-X 1,-X 0*X 1-X 0^2,X 0*X 1-X 0^2,-C (2*(1-ι))*X 1^3+C (2*ι)*X 0^3]

def nestedQ (s : Side) (r : R) : Nested R :=
  monomial (qLead s) 1 + ∑ _j : Fin 1, monomial (qTail s) (qCoefficient R s r)

def nestedH (s : Side) (r ι : R) : Nested R :=
  monomial (hLead s) 1 + ∑ j : Fin 4, monomial (hTail s j) (hCoefficient R s r ι j)

theorem regroup_quadric (s : Side) (r : R) : regroup R (quadric s r)=nestedQ R s r := by
  cases s <;> simp [quadric,nestedQ,qLead,qTail,qCoefficient,← X_pow_eq_monomial] <;> ring

theorem regroup_cubic (s : Side) (r ι : R) : regroup R (cubic s r ι)=nestedH R s r ι := by
  cases s <;>
    simp [cubic,nestedH,hLead,hTail,hCoefficient,Fin.sum_univ_succ,
      Matrix.cons_val_succ,Fin.reduceSucc,MvPolynomial.monomial_single_add,
      ← X_pow_eq_monomial,← C_mul_X_pow_eq_monomial] <;> ring

theorem nestedQ_leading [Nontrivial R] (s : Side) (r : R) :
    nestedOrder.degree (nestedQ R s r)=qLead s ∧ nestedOrder.Monic (nestedQ R s r) := by
  unfold nestedQ
  apply degree_monic_add_sum
  · apply weightedOrder_lt_of_weight_lt
    cases s <;> norm_num [nestedWeight,qLead,Finsupp.single_apply,Fin.ext_iff]
  · intro j
    apply weightedOrder_lt_of_weight_lt
    cases s <;> norm_num [nestedWeight,qLead,qTail,Finsupp.single_apply,Fin.ext_iff]

theorem nestedH_leading [Nontrivial R] (s : Side) (r ι : R) :
    nestedOrder.degree (nestedH R s r ι)=hLead s ∧ nestedOrder.Monic (nestedH R s r ι) := by
  unfold nestedH
  apply degree_monic_add_sum
  · apply weightedOrder_lt_of_weight_lt
    cases s <;> norm_num [nestedWeight,hLead,Finsupp.single_apply,Fin.ext_iff]
  · intro j
    apply weightedOrder_lt_of_weight_lt
    cases s <;> fin_cases j <;>
      norm_num [nestedWeight,hLead,hTail,Finsupp.single_apply,Fin.ext_iff]

theorem nested_coprime [Nontrivial R] (s : Side) (r ι : R) :
    ∀ j, nestedOrder.degree (nestedQ R s r) j=0 ∨ nestedOrder.degree (nestedH R s r ι) j=0 := by
  intro j
  rw [(nestedQ_leading R s r).1,(nestedH_leading R s r ι).1]
  cases s <;> fin_cases j <;> simp [qLead,hLead]

def nestedIdeal (s : Side) (r ι : R) : Ideal (Nested R) :=
  equationsIdeal (nestedQ R s r) (nestedH R s r ι)

theorem nestedIdeal_map (s : Side) (r ι : R) : nestedIdeal R s r ι=
    (curveIdeal s r ι).map (regroupOverBase R).toRingHom := by
  simp only [nestedIdeal,curveIdeal,equationsIdeal,Ideal.map_span,Set.image_insert_eq,
    Set.image_singleton]
  change Ideal.span {nestedQ R s r,nestedH R s r ι}=
    Ideal.span {regroup R (quadric s r),regroup R (cubic s r ι)}
  rw [regroup_quadric,regroup_cubic]

instance curveModule (s : Side) (r ι : R) : Module (Base R) (CurveRing s r ι) :=
  (inferInstance : Algebra (Base R) (CurveRing s r ι)).toModule

def quotientRegroup (s : Side) (r ι : R) :
    CurveRing s r ι ≃ₐ[Base R] (Nested R ⧸ nestedIdeal R s r ι) :=
  Ideal.quotientEquivAlg _ _ (regroupOverBase R) (nestedIdeal_map R s r ι)

theorem reduced_iff [Nontrivial R] (s : Side) (r ι : R) (e : Fin 2 →₀ ℕ) :
    e∈reducedExponents nestedOrder (nestedQ R s r) (nestedH R s r ι) ↔
      e 0<xBound s ∧ e 1<zBound s := by
  change (¬nestedOrder.degree (nestedQ R s r)≤e) ∧
    (¬nestedOrder.degree (nestedH R s r ι)≤e) ↔ _
  rw [(nestedQ_leading R s r).1,(nestedH_leading R s r ι).1]
  cases s <;> simp [qLead,hLead,xBound,zBound,Finsupp.single_le_iff,and_comm]

def nestedExponentEquiv [Nontrivial R] (s : Side) (r ι : R) :
    reducedExponents nestedOrder (nestedQ R s r) (nestedH R s r ι) ≃ ShiftIndex s where
  toFun e := (⟨e.val 0,((reduced_iff R s r ι e.val).mp e.property).1⟩,
    ⟨e.val 1,((reduced_iff R s r ι e.val).mp e.property).2⟩)
  invFun ab := ⟨Finsupp.single 0 ab.1.val+Finsupp.single 1 ab.2.val,
    (reduced_iff R s r ι _).mpr (by simpa using And.intro ab.1.isLt ab.2.isLt)⟩
  left_inv e := by apply Subtype.ext; ext j; fin_cases j <;> simp
  right_inv ab := by apply Prod.ext <;> apply Fin.ext <;> simp

def nestedBasis [Nontrivial R] (s : Side) (r ι : R) :
    Module.Basis (ShiftIndex s) (Base R) (Nested R ⧸ nestedIdeal R s r ι) :=
  (quotientBasis nestedOrder (nestedQ R s r) (nestedH R s r ι)
    (nestedQ_leading R s r).2 (nestedH_leading R s r ι).2 (nested_coprime R s r ι)).reindex
      (nestedExponentEquiv R s r ι)

theorem nestedBasis_apply [Nontrivial R] (s : Side) (r ι : R) (ab : ShiftIndex s) :
    nestedBasis R s r ι ab=Ideal.Quotient.mk (nestedIdeal R s r ι)
      (X 0^ab.1.val*X 1^ab.2.val) := by
  unfold nestedBasis
  erw [Module.Basis.reindex_apply,quotientBasis_apply]
  congr 1
  change monomial (Finsupp.single 0 ab.1.val+Finsupp.single 1 ab.2.val) 1=_
  rw [MvPolynomial.monomial_single_add,← X_pow_eq_monomial]

def curveBasis [Nontrivial R] (s : Side) (r ι : R) :
    Module.Basis (ShiftIndex s) (Base R) (CurveRing s r ι) :=
  (nestedBasis R s r ι).map (quotientRegroup R s r ι).symm.toLinearEquiv

theorem curveBasis_apply [Nontrivial R] (s : Side) (r ι : R) (ab : ShiftIndex s) :
    curveBasis R s r ι ab=Ideal.Quotient.mk (curveIdeal s r ι)
      ((X 0:CurvePoly R)^ab.1.val*X 2^ab.2.val) := by
  apply (quotientRegroup R s r ι).injective
  simp only [curveBasis,Module.Basis.map_apply,AlgEquiv.toLinearEquiv_apply,
    AlgEquiv.apply_symm_apply,nestedBasis_apply]
  change Ideal.Quotient.mk _ (X 0^ab.1.val*X 1^ab.2.val)=
    Ideal.Quotient.mk _ (regroup R ((X 0:CurvePoly R)^ab.1.val*X 2^ab.2.val))
  simp

theorem curveQuotient_free [Nontrivial R] (s : Side) (r ι : R) : Module.Free (Base R) (CurveRing s r ι) :=
  Module.Free.of_basis (curveBasis R s r ι)

theorem curveQuotient_finite [Nontrivial R] (s : Side) (r ι : R) : Module.Finite (Base R) (CurveRing s r ι) :=
  Module.Finite.of_basis (curveBasis R s r ι)

theorem curveQuotient_rank_six [Nontrivial R] (s : Side) (r ι : R) :
    Module.finrank (Base R) (CurveRing s r ι)=6 := by
  rw [Module.finrank_eq_card_basis (curveBasis R s r ι)]
  cases s <;> decide

theorem basis_degree_bound (s : Side) (ab : ShiftIndex s) : ab.1.val+ab.2.val≤3 := by
  have ha := ab.1.isLt
  have hb := ab.2.isLt
  cases s <;> simp only [xBound,zBound] at ha hb <;> omega

theorem basisMonomial_homogeneous (s : Side) (ab : ShiftIndex s) :
    ((X 0:CurvePoly R)^ab.1.val*X 2^ab.2.val).IsWeightedHomogeneous
      (fun _ => 1:Fin 4→ℕ) (ab.1.val+ab.2.val) := by
  convert ((isWeightedHomogeneous_X R (fun _ : Fin 4 => 1) 0).pow ab.1.val).mul
    ((isWeightedHomogeneous_X R (fun _ : Fin 4 => 1) 2).pow ab.2.val) using 1 <;> simp

end CycleQ2CurveQuotientFiniteFree

#print axioms CycleQ2CurveQuotientFiniteFree.curveQuotient_rank_six
#print axioms CycleQ2CurveQuotientFiniteFree.curveBasis_apply
end
end


