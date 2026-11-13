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

end CycleQ2SegreModularDetectorData
end

/- Component: continuation_3/SegreModularDetectorData.lean -/
section
namespace CycleQ2SegreModularDetectorData
open CycleQ2SparseModularFunctional

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

end CycleQ2SegreModularDetectorData
end

/- Component: continuation_3/SegreModularDetectorData.lean -/
section
namespace CycleQ2SegreModularDetectorData
open CycleQ2SparseModularFunctional

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

end CycleQ2SegreModularDetectorData
end

