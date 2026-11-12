import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Tactic.FinCases
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Dual.Defs
import HodgeTarget
import Proposal.GeometricTarget
import Proposal.GeometricSeed
import Proposal.GeometricFormalInputs
import Proposal.Normalization
import Proposal.SolutionSupport03

/-! Source partition of Solution.lean. See solution.md for verification status. -/

set_option Elab.async false

/- Component: continuation_3/SeedLinkageModularLeft.lean -/
section
set_option maxRecDepth 100000

set_option maxHeartbeats 0

set_option Elab.async false

set_option backward.isDefEq.respectTransparency false

set_option linter.unusedSimpArgs false

namespace CycleQ2SeedLinkageModularChecks

open MvPolynomial CycleQ2IncidenceEquations CycleQ2CurveRestriction CycleQ2CurveRestrictionReflection

open CycleQ2SparseModularPolynomial CycleQ2SeedLinkageIdeals CycleQ2SeedLinkageSections

open CycleQ2SeedLinkageReflection CycleQ2CurveRestrictionMatrixCheck CycleQ2SeedLinkageModularData

noncomputable section

variable {R : Type*} [CommRing R] [CharP R 109]

private theorem left_normal_good_0 : fullGood 10 0 leftNormal0=true := by decide +kernel

private theorem left_normal_check_0 :

    checkZero (residual leftInput0 leftNormal0 leftH0 leftG0 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_0 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(0,0,2,4,0))) = fullValue leftNormal0 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(0,0,2,4,0)) = fullValue leftInput0 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput0, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput0 leftNormal0 leftH0 leftG0

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_0 left_normal_check_0

private theorem left_normal_good_1 : fullGood 10 0 leftNormal1=true := by decide +kernel

private theorem left_normal_check_1 :

    checkZero (residual leftInput1 leftNormal1 leftH1 leftG1 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_1 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(0,0,5,1,0))) = fullValue leftNormal1 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(0,0,5,1,0)) = fullValue leftInput1 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput1, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput1 leftNormal1 leftH1 leftG1

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_1 left_normal_check_1

private theorem left_normal_good_2 : fullGood 10 0 leftNormal2=true := by decide +kernel

private theorem left_normal_check_2 :

    checkZero (residual leftInput2 leftNormal2 leftH2 leftG2 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_2 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(0,1,0,5,0))) = fullValue leftNormal2 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(0,1,0,5,0)) = fullValue leftInput2 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput2, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput2 leftNormal2 leftH2 leftG2

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_2 left_normal_check_2

private theorem left_normal_good_3 : fullGood 10 0 leftNormal3=true := by decide +kernel

private theorem left_normal_check_3 :

    checkZero (residual leftInput3 leftNormal3 leftH3 leftG3 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_3 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(0,1,3,2,0))) = fullValue leftNormal3 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(0,1,3,2,0)) = fullValue leftInput3 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput3, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput3 leftNormal3 leftH3 leftG3

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_3 left_normal_check_3

private theorem left_normal_good_4 : fullGood 10 0 leftNormal4=true := by decide +kernel

private theorem left_normal_check_4 :

    checkZero (residual leftInput4 leftNormal4 leftH4 leftG4 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_4 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(0,2,1,3,0))) = fullValue leftNormal4 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(0,2,1,3,0)) = fullValue leftInput4 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput4, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput4 leftNormal4 leftH4 leftG4

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_4 left_normal_check_4

private theorem left_normal_good_5 : fullGood 10 0 leftNormal5=true := by decide +kernel

private theorem left_normal_check_5 :

    checkZero (residual leftInput5 leftNormal5 leftH5 leftG5 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_5 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(0,2,4,0,0))) = fullValue leftNormal5 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(0,2,4,0,0)) = fullValue leftInput5 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput5, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput5 leftNormal5 leftH5 leftG5

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_5 left_normal_check_5

private theorem left_normal_good_6 : fullGood 10 0 leftNormal6=true := by decide +kernel

private theorem left_normal_check_6 :

    checkZero (residual leftInput6 leftNormal6 leftH6 leftG6 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_6 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(0,3,2,1,0))) = fullValue leftNormal6 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(0,3,2,1,0)) = fullValue leftInput6 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput6, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput6 leftNormal6 leftH6 leftG6

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_6 left_normal_check_6

private theorem left_normal_good_7 : fullGood 10 0 leftNormal7=true := by decide +kernel

private theorem left_normal_check_7 :

    checkZero (residual leftInput7 leftNormal7 leftH7 leftG7 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_7 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(0,4,0,2,0))) = fullValue leftNormal7 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(0,4,0,2,0)) = fullValue leftInput7 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput7, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput7 leftNormal7 leftH7 leftG7

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_7 left_normal_check_7

private theorem left_normal_good_8 : fullGood 10 0 leftNormal8=true := by decide +kernel

private theorem left_normal_check_8 :

    checkZero (residual leftInput8 leftNormal8 leftH8 leftG8 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_8 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(0,5,1,0,0))) = fullValue leftNormal8 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(0,5,1,0,0)) = fullValue leftInput8 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput8, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput8 leftNormal8 leftH8 leftG8

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_8 left_normal_check_8

private theorem left_normal_good_9 : fullGood 10 0 leftNormal9=true := by decide +kernel

private theorem left_normal_check_9 :

    checkZero (residual leftInput9 leftNormal9 leftH9 leftG9 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_9 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(0,0,2,2,1))) = fullValue leftNormal9 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(0,0,2,2,1)) = fullValue leftInput9 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput9, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput9 leftNormal9 leftH9 leftG9

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_9 left_normal_check_9

private theorem left_normal_good_10 : fullGood 10 0 leftNormal10=true := by decide +kernel

private theorem left_normal_check_10 :

    checkZero (residual leftInput10 leftNormal10 leftH10 leftG10 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_10 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(0,1,0,3,1))) = fullValue leftNormal10 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(0,1,0,3,1)) = fullValue leftInput10 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput10, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput10 leftNormal10 leftH10 leftG10

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_10 left_normal_check_10

private theorem left_normal_good_11 : fullGood 10 0 leftNormal11=true := by decide +kernel

private theorem left_normal_check_11 :

    checkZero (residual leftInput11 leftNormal11 leftH11 leftG11 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_11 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(0,1,3,0,1))) = fullValue leftNormal11 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(0,1,3,0,1)) = fullValue leftInput11 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput11, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput11 leftNormal11 leftH11 leftG11

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_11 left_normal_check_11

private theorem left_normal_good_12 : fullGood 10 0 leftNormal12=true := by decide +kernel

private theorem left_normal_check_12 :

    checkZero (residual leftInput12 leftNormal12 leftH12 leftG12 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_12 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(0,2,1,1,1))) = fullValue leftNormal12 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(0,2,1,1,1)) = fullValue leftInput12 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput12, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput12 leftNormal12 leftH12 leftG12

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_12 left_normal_check_12

private theorem left_normal_good_13 : fullGood 10 0 leftNormal13=true := by decide +kernel

private theorem left_normal_check_13 :

    checkZero (residual leftInput13 leftNormal13 leftH13 leftG13 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_13 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(0,4,0,0,1))) = fullValue leftNormal13 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(0,4,0,0,1)) = fullValue leftInput13 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput13, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput13 leftNormal13 leftH13 leftG13

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_13 left_normal_check_13

private theorem left_normal_good_14 : fullGood 10 0 leftNormal14=true := by decide +kernel

private theorem left_normal_check_14 :

    checkZero (residual leftInput14 leftNormal14 leftH14 leftG14 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_14 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(0,0,2,0,2))) = fullValue leftNormal14 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(0,0,2,0,2)) = fullValue leftInput14 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput14, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput14 leftNormal14 leftH14 leftG14

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_14 left_normal_check_14

private theorem left_normal_good_15 : fullGood 10 0 leftNormal15=true := by decide +kernel

private theorem left_normal_check_15 :

    checkZero (residual leftInput15 leftNormal15 leftH15 leftG15 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_15 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(0,1,0,1,2))) = fullValue leftNormal15 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(0,1,0,1,2)) = fullValue leftInput15 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput15, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput15 leftNormal15 leftH15 leftG15

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_15 left_normal_check_15

private theorem left_normal_good_16 : fullGood 10 0 leftNormal16=true := by decide +kernel

private theorem left_normal_check_16 :

    checkZero (residual leftInput16 leftNormal16 leftH16 leftG16 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_16 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(1,0,0,5,0))) = fullValue leftNormal16 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(1,0,0,5,0)) = fullValue leftInput16 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput16, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput16 leftNormal16 leftH16 leftG16

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_16 left_normal_check_16

private theorem left_normal_good_17 : fullGood 10 0 leftNormal17=true := by decide +kernel

private theorem left_normal_check_17 :

    checkZero (residual leftInput17 leftNormal17 leftH17 leftG17 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_17 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(1,0,3,2,0))) = fullValue leftNormal17 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(1,0,3,2,0)) = fullValue leftInput17 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput17, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput17 leftNormal17 leftH17 leftG17

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_17 left_normal_check_17

private theorem left_normal_good_18 : fullGood 10 0 leftNormal18=true := by decide +kernel

private theorem left_normal_check_18 :

    checkZero (residual leftInput18 leftNormal18 leftH18 leftG18 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_18 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(1,1,1,3,0))) = fullValue leftNormal18 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(1,1,1,3,0)) = fullValue leftInput18 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput18, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput18 leftNormal18 leftH18 leftG18

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_18 left_normal_check_18

private theorem left_normal_good_19 : fullGood 10 0 leftNormal19=true := by decide +kernel

private theorem left_normal_check_19 :

    checkZero (residual leftInput19 leftNormal19 leftH19 leftG19 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_19 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(1,1,4,0,0))) = fullValue leftNormal19 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(1,1,4,0,0)) = fullValue leftInput19 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput19, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput19 leftNormal19 leftH19 leftG19

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_19 left_normal_check_19

private theorem left_normal_good_20 : fullGood 10 0 leftNormal20=true := by decide +kernel

private theorem left_normal_check_20 :

    checkZero (residual leftInput20 leftNormal20 leftH20 leftG20 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_20 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(1,2,2,1,0))) = fullValue leftNormal20 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(1,2,2,1,0)) = fullValue leftInput20 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput20, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput20 leftNormal20 leftH20 leftG20

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_20 left_normal_check_20

private theorem left_normal_good_21 : fullGood 10 0 leftNormal21=true := by decide +kernel

private theorem left_normal_check_21 :

    checkZero (residual leftInput21 leftNormal21 leftH21 leftG21 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_21 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(1,3,0,2,0))) = fullValue leftNormal21 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(1,3,0,2,0)) = fullValue leftInput21 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput21, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput21 leftNormal21 leftH21 leftG21

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_21 left_normal_check_21

private theorem left_normal_good_22 : fullGood 10 0 leftNormal22=true := by decide +kernel

private theorem left_normal_check_22 :

    checkZero (residual leftInput22 leftNormal22 leftH22 leftG22 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_22 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(1,4,1,0,0))) = fullValue leftNormal22 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(1,4,1,0,0)) = fullValue leftInput22 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput22, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput22 leftNormal22 leftH22 leftG22

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_22 left_normal_check_22

private theorem left_normal_good_23 : fullGood 10 0 leftNormal23=true := by decide +kernel

private theorem left_normal_check_23 :

    checkZero (residual leftInput23 leftNormal23 leftH23 leftG23 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_23 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(1,0,0,3,1))) = fullValue leftNormal23 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(1,0,0,3,1)) = fullValue leftInput23 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput23, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput23 leftNormal23 leftH23 leftG23

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_23 left_normal_check_23

private theorem left_normal_good_24 : fullGood 10 0 leftNormal24=true := by decide +kernel

private theorem left_normal_check_24 :

    checkZero (residual leftInput24 leftNormal24 leftH24 leftG24 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_24 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(1,0,3,0,1))) = fullValue leftNormal24 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(1,0,3,0,1)) = fullValue leftInput24 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput24, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput24 leftNormal24 leftH24 leftG24

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_24 left_normal_check_24

private theorem left_normal_good_25 : fullGood 10 0 leftNormal25=true := by decide +kernel

private theorem left_normal_check_25 :

    checkZero (residual leftInput25 leftNormal25 leftH25 leftG25 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_25 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(1,1,1,1,1))) = fullValue leftNormal25 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(1,1,1,1,1)) = fullValue leftInput25 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput25, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput25 leftNormal25 leftH25 leftG25

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_25 left_normal_check_25

private theorem left_normal_good_26 : fullGood 10 0 leftNormal26=true := by decide +kernel

private theorem left_normal_check_26 :

    checkZero (residual leftInput26 leftNormal26 leftH26 leftG26 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_26 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(1,3,0,0,1))) = fullValue leftNormal26 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(1,3,0,0,1)) = fullValue leftInput26 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput26, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput26 leftNormal26 leftH26 leftG26

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_26 left_normal_check_26

private theorem left_normal_good_27 : fullGood 10 0 leftNormal27=true := by decide +kernel

private theorem left_normal_check_27 :

    checkZero (residual leftInput27 leftNormal27 leftH27 leftG27 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_27 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(1,0,0,1,2))) = fullValue leftNormal27 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(1,0,0,1,2)) = fullValue leftInput27 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput27, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput27 leftNormal27 leftH27 leftG27

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_27 left_normal_check_27

private theorem left_normal_good_28 : fullGood 10 0 leftNormal28=true := by decide +kernel

private theorem left_normal_check_28 :

    checkZero (residual leftInput28 leftNormal28 leftH28 leftG28 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_28 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(2,0,1,3,0))) = fullValue leftNormal28 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(2,0,1,3,0)) = fullValue leftInput28 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput28, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput28 leftNormal28 leftH28 leftG28

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_28 left_normal_check_28

private theorem left_normal_good_29 : fullGood 10 0 leftNormal29=true := by decide +kernel

private theorem left_normal_check_29 :

    checkZero (residual leftInput29 leftNormal29 leftH29 leftG29 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_29 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(2,0,4,0,0))) = fullValue leftNormal29 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(2,0,4,0,0)) = fullValue leftInput29 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput29, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput29 leftNormal29 leftH29 leftG29

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_29 left_normal_check_29

private theorem left_normal_good_30 : fullGood 10 0 leftNormal30=true := by decide +kernel

private theorem left_normal_check_30 :

    checkZero (residual leftInput30 leftNormal30 leftH30 leftG30 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_30 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(2,1,2,1,0))) = fullValue leftNormal30 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(2,1,2,1,0)) = fullValue leftInput30 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput30, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput30 leftNormal30 leftH30 leftG30

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_30 left_normal_check_30

private theorem left_normal_good_31 : fullGood 10 0 leftNormal31=true := by decide +kernel

private theorem left_normal_check_31 :

    checkZero (residual leftInput31 leftNormal31 leftH31 leftG31 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_31 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(2,2,0,2,0))) = fullValue leftNormal31 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(2,2,0,2,0)) = fullValue leftInput31 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput31, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput31 leftNormal31 leftH31 leftG31

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_31 left_normal_check_31

private theorem left_normal_good_32 : fullGood 10 0 leftNormal32=true := by decide +kernel

private theorem left_normal_check_32 :

    checkZero (residual leftInput32 leftNormal32 leftH32 leftG32 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_32 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(2,3,1,0,0))) = fullValue leftNormal32 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(2,3,1,0,0)) = fullValue leftInput32 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput32, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput32 leftNormal32 leftH32 leftG32

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_32 left_normal_check_32

private theorem left_normal_good_33 : fullGood 10 0 leftNormal33=true := by decide +kernel

private theorem left_normal_check_33 :

    checkZero (residual leftInput33 leftNormal33 leftH33 leftG33 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_33 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(2,0,1,1,1))) = fullValue leftNormal33 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(2,0,1,1,1)) = fullValue leftInput33 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput33, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput33 leftNormal33 leftH33 leftG33

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_33 left_normal_check_33

private theorem left_normal_good_34 : fullGood 10 0 leftNormal34=true := by decide +kernel

private theorem left_normal_check_34 :

    checkZero (residual leftInput34 leftNormal34 leftH34 leftG34 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_34 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (0,(2,2,0,0,1))) = fullValue leftNormal34 := by

  have hinput : sectionPolynomial .left (57 : R) (0,(2,2,0,0,1)) = fullValue leftInput34 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput34, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput34 leftNormal34 leftH34 leftG34

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_34 left_normal_check_34

private theorem left_normal_good_35 : fullGood 10 0 leftNormal35=true := by decide +kernel

private theorem left_normal_check_35 :

    checkZero (residual leftInput35 leftNormal35 leftH35 leftG35 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_35 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (1,(0,0,0,4,0))) = fullValue leftNormal35 := by

  have hinput : sectionPolynomial .left (57 : R) (1,(0,0,0,4,0)) = fullValue leftInput35 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput35, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput35 leftNormal35 leftH35 leftG35

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_35 left_normal_check_35

private theorem left_normal_good_36 : fullGood 10 0 leftNormal36=true := by decide +kernel

private theorem left_normal_check_36 :

    checkZero (residual leftInput36 leftNormal36 leftH36 leftG36 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_36 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (1,(0,0,3,1,0))) = fullValue leftNormal36 := by

  have hinput : sectionPolynomial .left (57 : R) (1,(0,0,3,1,0)) = fullValue leftInput36 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput36, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput36 leftNormal36 leftH36 leftG36

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_36 left_normal_check_36

private theorem left_normal_good_37 : fullGood 10 0 leftNormal37=true := by decide +kernel

private theorem left_normal_check_37 :

    checkZero (residual leftInput37 leftNormal37 leftH37 leftG37 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_37 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (1,(0,1,1,2,0))) = fullValue leftNormal37 := by

  have hinput : sectionPolynomial .left (57 : R) (1,(0,1,1,2,0)) = fullValue leftInput37 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput37, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput37 leftNormal37 leftH37 leftG37

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_37 left_normal_check_37

private theorem left_normal_good_38 : fullGood 10 0 leftNormal38=true := by decide +kernel

private theorem left_normal_check_38 :

    checkZero (residual leftInput38 leftNormal38 leftH38 leftG38 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_38 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (1,(0,2,2,0,0))) = fullValue leftNormal38 := by

  have hinput : sectionPolynomial .left (57 : R) (1,(0,2,2,0,0)) = fullValue leftInput38 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput38, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput38 leftNormal38 leftH38 leftG38

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_38 left_normal_check_38

private theorem left_normal_good_39 : fullGood 10 0 leftNormal39=true := by decide +kernel

private theorem left_normal_check_39 :

    checkZero (residual leftInput39 leftNormal39 leftH39 leftG39 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_39 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (1,(0,3,0,1,0))) = fullValue leftNormal39 := by

  have hinput : sectionPolynomial .left (57 : R) (1,(0,3,0,1,0)) = fullValue leftInput39 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput39, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput39 leftNormal39 leftH39 leftG39

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_39 left_normal_check_39

private theorem left_normal_good_40 : fullGood 10 0 leftNormal40=true := by decide +kernel

private theorem left_normal_check_40 :

    checkZero (residual leftInput40 leftNormal40 leftH40 leftG40 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_40 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (1,(0,0,0,2,1))) = fullValue leftNormal40 := by

  have hinput : sectionPolynomial .left (57 : R) (1,(0,0,0,2,1)) = fullValue leftInput40 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput40, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput40 leftNormal40 leftH40 leftG40

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_40 left_normal_check_40

private theorem left_normal_good_41 : fullGood 10 0 leftNormal41=true := by decide +kernel

private theorem left_normal_check_41 :

    checkZero (residual leftInput41 leftNormal41 leftH41 leftG41 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_41 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (1,(0,1,1,0,1))) = fullValue leftNormal41 := by

  have hinput : sectionPolynomial .left (57 : R) (1,(0,1,1,0,1)) = fullValue leftInput41 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput41, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput41 leftNormal41 leftH41 leftG41

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_41 left_normal_check_41

private theorem left_normal_good_42 : fullGood 10 0 leftNormal42=true := by decide +kernel

private theorem left_normal_check_42 :

    checkZero (residual leftInput42 leftNormal42 leftH42 leftG42 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_42 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (1,(0,0,0,0,2))) = fullValue leftNormal42 := by

  have hinput : sectionPolynomial .left (57 : R) (1,(0,0,0,0,2)) = fullValue leftInput42 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput42, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput42 leftNormal42 leftH42 leftG42

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_42 left_normal_check_42

private theorem left_normal_good_43 : fullGood 10 0 leftNormal43=true := by decide +kernel

private theorem left_normal_check_43 :

    checkZero (residual leftInput43 leftNormal43 leftH43 leftG43 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_43 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (1,(1,0,1,2,0))) = fullValue leftNormal43 := by

  have hinput : sectionPolynomial .left (57 : R) (1,(1,0,1,2,0)) = fullValue leftInput43 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput43, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput43 leftNormal43 leftH43 leftG43

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_43 left_normal_check_43

private theorem left_normal_good_44 : fullGood 10 0 leftNormal44=true := by decide +kernel

private theorem left_normal_check_44 :

    checkZero (residual leftInput44 leftNormal44 leftH44 leftG44 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_44 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (1,(1,1,2,0,0))) = fullValue leftNormal44 := by

  have hinput : sectionPolynomial .left (57 : R) (1,(1,1,2,0,0)) = fullValue leftInput44 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput44, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput44 leftNormal44 leftH44 leftG44

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_44 left_normal_check_44

private theorem left_normal_good_45 : fullGood 10 0 leftNormal45=true := by decide +kernel

private theorem left_normal_check_45 :

    checkZero (residual leftInput45 leftNormal45 leftH45 leftG45 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_45 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (1,(1,2,0,1,0))) = fullValue leftNormal45 := by

  have hinput : sectionPolynomial .left (57 : R) (1,(1,2,0,1,0)) = fullValue leftInput45 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput45, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput45 leftNormal45 leftH45 leftG45

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_45 left_normal_check_45

private theorem left_normal_good_46 : fullGood 10 0 leftNormal46=true := by decide +kernel

private theorem left_normal_check_46 :

    checkZero (residual leftInput46 leftNormal46 leftH46 leftG46 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_46 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (1,(1,0,1,0,1))) = fullValue leftNormal46 := by

  have hinput : sectionPolynomial .left (57 : R) (1,(1,0,1,0,1)) = fullValue leftInput46 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput46, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput46 leftNormal46 leftH46 leftG46

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_46 left_normal_check_46

private theorem left_normal_good_47 : fullGood 10 0 leftNormal47=true := by decide +kernel

private theorem left_normal_check_47 :

    checkZero (residual leftInput47 leftNormal47 leftH47 leftG47 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_47 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (1,(2,0,2,0,0))) = fullValue leftNormal47 := by

  have hinput : sectionPolynomial .left (57 : R) (1,(2,0,2,0,0)) = fullValue leftInput47 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput47, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput47 leftNormal47 leftH47 leftG47

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_47 left_normal_check_47

private theorem left_normal_good_48 : fullGood 10 0 leftNormal48=true := by decide +kernel

private theorem left_normal_check_48 :

    checkZero (residual leftInput48 leftNormal48 leftH48 leftG48 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_48 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (1,(2,1,0,1,0))) = fullValue leftNormal48 := by

  have hinput : sectionPolynomial .left (57 : R) (1,(2,1,0,1,0)) = fullValue leftInput48 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput48, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput48 leftNormal48 leftH48 leftG48

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_48 left_normal_check_48

private theorem left_normal_good_49 : fullGood 10 0 leftNormal49=true := by decide +kernel

private theorem left_normal_check_49 :

    checkZero (residual leftInput49 leftNormal49 leftH49 leftG49 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_49 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (2,(0,0,2,2,0))) = fullValue leftNormal49 := by

  have hinput : sectionPolynomial .left (57 : R) (2,(0,0,2,2,0)) = fullValue leftInput49 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput49, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput49 leftNormal49 leftH49 leftG49

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_49 left_normal_check_49

private theorem left_normal_good_50 : fullGood 10 0 leftNormal50=true := by decide +kernel

private theorem left_normal_check_50 :

    checkZero (residual leftInput50 leftNormal50 leftH50 leftG50 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_50 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (2,(0,1,3,0,0))) = fullValue leftNormal50 := by

  have hinput : sectionPolynomial .left (57 : R) (2,(0,1,3,0,0)) = fullValue leftInput50 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput50, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput50 leftNormal50 leftH50 leftG50

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_50 left_normal_check_50

private theorem left_normal_good_51 : fullGood 10 0 leftNormal51=true := by decide +kernel

private theorem left_normal_check_51 :

    checkZero (residual leftInput51 leftNormal51 leftH51 leftG51 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_51 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (2,(0,4,0,0,0))) = fullValue leftNormal51 := by

  have hinput : sectionPolynomial .left (57 : R) (2,(0,4,0,0,0)) = fullValue leftInput51 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput51, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput51 leftNormal51 leftH51 leftG51

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_51 left_normal_check_51

private theorem left_normal_good_52 : fullGood 10 0 leftNormal52=true := by decide +kernel

private theorem left_normal_check_52 :

    checkZero (residual leftInput52 leftNormal52 leftH52 leftG52 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_52 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (2,(1,0,0,3,0))) = fullValue leftNormal52 := by

  have hinput : sectionPolynomial .left (57 : R) (2,(1,0,0,3,0)) = fullValue leftInput52 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput52, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput52 leftNormal52 leftH52 leftG52

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_52 left_normal_check_52

private theorem left_normal_good_53 : fullGood 10 0 leftNormal53=true := by decide +kernel

private theorem left_normal_check_53 :

    checkZero (residual leftInput53 leftNormal53 leftH53 leftG53 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_53 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (2,(1,0,0,1,1))) = fullValue leftNormal53 := by

  have hinput : sectionPolynomial .left (57 : R) (2,(1,0,0,1,1)) = fullValue leftInput53 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput53, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput53 leftNormal53 leftH53 leftG53

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_53 left_normal_check_53

private theorem left_normal_good_54 : fullGood 10 0 leftNormal54=true := by decide +kernel

private theorem left_normal_check_54 :

    checkZero (residual leftInput54 leftNormal54 leftH54 leftG54 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_54 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (3,(0,0,1,3,0))) = fullValue leftNormal54 := by

  have hinput : sectionPolynomial .left (57 : R) (3,(0,0,1,3,0)) = fullValue leftInput54 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput54, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput54 leftNormal54 leftH54 leftG54

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_54 left_normal_check_54

private theorem left_normal_good_55 : fullGood 10 0 leftNormal55=true := by decide +kernel

private theorem left_normal_check_55 :

    checkZero (residual leftInput55 leftNormal55 leftH55 leftG55 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem left_column_55 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (3,(0,3,1,0,0))) = fullValue leftNormal55 := by

  have hinput : sectionPolynomial .left (57 : R) (3,(0,3,1,0,0)) = fullValue leftInput55 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, leftInput55, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 10 0 leftInput55 leftNormal55 leftH55 leftG55

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    left_normal_good_55 left_normal_check_55

theorem left_columns [Nontrivial R] (j : Fin 56) :

    seedNormal (57 : R) 33 (sectionPolynomial .left 57 (leftColumns j)) = fullValue (leftNormals j) := by

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

private theorem left_coefficient_row_0 : ∀ j : Fin 56,

    fullCoefficient (leftRows 0) (leftNormals j) = (leftMinorRows 0).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_1 : ∀ j : Fin 56,

    fullCoefficient (leftRows 1) (leftNormals j) = (leftMinorRows 1).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_2 : ∀ j : Fin 56,

    fullCoefficient (leftRows 2) (leftNormals j) = (leftMinorRows 2).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_3 : ∀ j : Fin 56,

    fullCoefficient (leftRows 3) (leftNormals j) = (leftMinorRows 3).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_4 : ∀ j : Fin 56,

    fullCoefficient (leftRows 4) (leftNormals j) = (leftMinorRows 4).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_5 : ∀ j : Fin 56,

    fullCoefficient (leftRows 5) (leftNormals j) = (leftMinorRows 5).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_6 : ∀ j : Fin 56,

    fullCoefficient (leftRows 6) (leftNormals j) = (leftMinorRows 6).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_7 : ∀ j : Fin 56,

    fullCoefficient (leftRows 7) (leftNormals j) = (leftMinorRows 7).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_8 : ∀ j : Fin 56,

    fullCoefficient (leftRows 8) (leftNormals j) = (leftMinorRows 8).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_9 : ∀ j : Fin 56,

    fullCoefficient (leftRows 9) (leftNormals j) = (leftMinorRows 9).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_10 : ∀ j : Fin 56,

    fullCoefficient (leftRows 10) (leftNormals j) = (leftMinorRows 10).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_11 : ∀ j : Fin 56,

    fullCoefficient (leftRows 11) (leftNormals j) = (leftMinorRows 11).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_12 : ∀ j : Fin 56,

    fullCoefficient (leftRows 12) (leftNormals j) = (leftMinorRows 12).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_13 : ∀ j : Fin 56,

    fullCoefficient (leftRows 13) (leftNormals j) = (leftMinorRows 13).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_14 : ∀ j : Fin 56,

    fullCoefficient (leftRows 14) (leftNormals j) = (leftMinorRows 14).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_15 : ∀ j : Fin 56,

    fullCoefficient (leftRows 15) (leftNormals j) = (leftMinorRows 15).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_16 : ∀ j : Fin 56,

    fullCoefficient (leftRows 16) (leftNormals j) = (leftMinorRows 16).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_17 : ∀ j : Fin 56,

    fullCoefficient (leftRows 17) (leftNormals j) = (leftMinorRows 17).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_18 : ∀ j : Fin 56,

    fullCoefficient (leftRows 18) (leftNormals j) = (leftMinorRows 18).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_19 : ∀ j : Fin 56,

    fullCoefficient (leftRows 19) (leftNormals j) = (leftMinorRows 19).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_20 : ∀ j : Fin 56,

    fullCoefficient (leftRows 20) (leftNormals j) = (leftMinorRows 20).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_21 : ∀ j : Fin 56,

    fullCoefficient (leftRows 21) (leftNormals j) = (leftMinorRows 21).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_22 : ∀ j : Fin 56,

    fullCoefficient (leftRows 22) (leftNormals j) = (leftMinorRows 22).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_23 : ∀ j : Fin 56,

    fullCoefficient (leftRows 23) (leftNormals j) = (leftMinorRows 23).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_24 : ∀ j : Fin 56,

    fullCoefficient (leftRows 24) (leftNormals j) = (leftMinorRows 24).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_25 : ∀ j : Fin 56,

    fullCoefficient (leftRows 25) (leftNormals j) = (leftMinorRows 25).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_26 : ∀ j : Fin 56,

    fullCoefficient (leftRows 26) (leftNormals j) = (leftMinorRows 26).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_27 : ∀ j : Fin 56,

    fullCoefficient (leftRows 27) (leftNormals j) = (leftMinorRows 27).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_28 : ∀ j : Fin 56,

    fullCoefficient (leftRows 28) (leftNormals j) = (leftMinorRows 28).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_29 : ∀ j : Fin 56,

    fullCoefficient (leftRows 29) (leftNormals j) = (leftMinorRows 29).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_30 : ∀ j : Fin 56,

    fullCoefficient (leftRows 30) (leftNormals j) = (leftMinorRows 30).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_31 : ∀ j : Fin 56,

    fullCoefficient (leftRows 31) (leftNormals j) = (leftMinorRows 31).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_32 : ∀ j : Fin 56,

    fullCoefficient (leftRows 32) (leftNormals j) = (leftMinorRows 32).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_33 : ∀ j : Fin 56,

    fullCoefficient (leftRows 33) (leftNormals j) = (leftMinorRows 33).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_34 : ∀ j : Fin 56,

    fullCoefficient (leftRows 34) (leftNormals j) = (leftMinorRows 34).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_35 : ∀ j : Fin 56,

    fullCoefficient (leftRows 35) (leftNormals j) = (leftMinorRows 35).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_36 : ∀ j : Fin 56,

    fullCoefficient (leftRows 36) (leftNormals j) = (leftMinorRows 36).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_37 : ∀ j : Fin 56,

    fullCoefficient (leftRows 37) (leftNormals j) = (leftMinorRows 37).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_38 : ∀ j : Fin 56,

    fullCoefficient (leftRows 38) (leftNormals j) = (leftMinorRows 38).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_39 : ∀ j : Fin 56,

    fullCoefficient (leftRows 39) (leftNormals j) = (leftMinorRows 39).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_40 : ∀ j : Fin 56,

    fullCoefficient (leftRows 40) (leftNormals j) = (leftMinorRows 40).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_41 : ∀ j : Fin 56,

    fullCoefficient (leftRows 41) (leftNormals j) = (leftMinorRows 41).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_42 : ∀ j : Fin 56,

    fullCoefficient (leftRows 42) (leftNormals j) = (leftMinorRows 42).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_43 : ∀ j : Fin 56,

    fullCoefficient (leftRows 43) (leftNormals j) = (leftMinorRows 43).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_44 : ∀ j : Fin 56,

    fullCoefficient (leftRows 44) (leftNormals j) = (leftMinorRows 44).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_45 : ∀ j : Fin 56,

    fullCoefficient (leftRows 45) (leftNormals j) = (leftMinorRows 45).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_46 : ∀ j : Fin 56,

    fullCoefficient (leftRows 46) (leftNormals j) = (leftMinorRows 46).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_47 : ∀ j : Fin 56,

    fullCoefficient (leftRows 47) (leftNormals j) = (leftMinorRows 47).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_48 : ∀ j : Fin 56,

    fullCoefficient (leftRows 48) (leftNormals j) = (leftMinorRows 48).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_49 : ∀ j : Fin 56,

    fullCoefficient (leftRows 49) (leftNormals j) = (leftMinorRows 49).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_50 : ∀ j : Fin 56,

    fullCoefficient (leftRows 50) (leftNormals j) = (leftMinorRows 50).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_51 : ∀ j : Fin 56,

    fullCoefficient (leftRows 51) (leftNormals j) = (leftMinorRows 51).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_52 : ∀ j : Fin 56,

    fullCoefficient (leftRows 52) (leftNormals j) = (leftMinorRows 52).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_53 : ∀ j : Fin 56,

    fullCoefficient (leftRows 53) (leftNormals j) = (leftMinorRows 53).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_54 : ∀ j : Fin 56,

    fullCoefficient (leftRows 54) (leftNormals j) = (leftMinorRows 54).getD j.val 0 := by

  decide +kernel

private theorem left_coefficient_row_55 : ∀ j : Fin 56,

    fullCoefficient (leftRows 55) (leftNormals j) = (leftMinorRows 55).getD j.val 0 := by

  decide +kernel

theorem left_coefficient_table (i j : Fin 56) :

    fullCoefficient (leftRows i) (leftNormals j) = (leftMinorRows i).getD j.val 0 := by

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

theorem left_matrix_coefficients [Nontrivial R] (i j : Fin 56) :

    sectionCoefficient .left (57 : R) 33 (leftRows i) (leftColumns j) =

      ((leftMinorRows i).getD j.val 0 : R) := by

  rw [sectionCoefficient,left_columns,fullValue_coefficient,left_coefficient_table]

private theorem left_inverse_row_0 : ∀ j : Fin 56,

    dotMod (leftMinorRows 0) (leftInverseColumns j) = if (0 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_1 : ∀ j : Fin 56,

    dotMod (leftMinorRows 1) (leftInverseColumns j) = if (1 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_2 : ∀ j : Fin 56,

    dotMod (leftMinorRows 2) (leftInverseColumns j) = if (2 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_3 : ∀ j : Fin 56,

    dotMod (leftMinorRows 3) (leftInverseColumns j) = if (3 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_4 : ∀ j : Fin 56,

    dotMod (leftMinorRows 4) (leftInverseColumns j) = if (4 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_5 : ∀ j : Fin 56,

    dotMod (leftMinorRows 5) (leftInverseColumns j) = if (5 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_6 : ∀ j : Fin 56,

    dotMod (leftMinorRows 6) (leftInverseColumns j) = if (6 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_7 : ∀ j : Fin 56,

    dotMod (leftMinorRows 7) (leftInverseColumns j) = if (7 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_8 : ∀ j : Fin 56,

    dotMod (leftMinorRows 8) (leftInverseColumns j) = if (8 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_9 : ∀ j : Fin 56,

    dotMod (leftMinorRows 9) (leftInverseColumns j) = if (9 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_10 : ∀ j : Fin 56,

    dotMod (leftMinorRows 10) (leftInverseColumns j) = if (10 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_11 : ∀ j : Fin 56,

    dotMod (leftMinorRows 11) (leftInverseColumns j) = if (11 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_12 : ∀ j : Fin 56,

    dotMod (leftMinorRows 12) (leftInverseColumns j) = if (12 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_13 : ∀ j : Fin 56,

    dotMod (leftMinorRows 13) (leftInverseColumns j) = if (13 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_14 : ∀ j : Fin 56,

    dotMod (leftMinorRows 14) (leftInverseColumns j) = if (14 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_15 : ∀ j : Fin 56,

    dotMod (leftMinorRows 15) (leftInverseColumns j) = if (15 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_16 : ∀ j : Fin 56,

    dotMod (leftMinorRows 16) (leftInverseColumns j) = if (16 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_17 : ∀ j : Fin 56,

    dotMod (leftMinorRows 17) (leftInverseColumns j) = if (17 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_18 : ∀ j : Fin 56,

    dotMod (leftMinorRows 18) (leftInverseColumns j) = if (18 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_19 : ∀ j : Fin 56,

    dotMod (leftMinorRows 19) (leftInverseColumns j) = if (19 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_20 : ∀ j : Fin 56,

    dotMod (leftMinorRows 20) (leftInverseColumns j) = if (20 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_21 : ∀ j : Fin 56,

    dotMod (leftMinorRows 21) (leftInverseColumns j) = if (21 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_22 : ∀ j : Fin 56,

    dotMod (leftMinorRows 22) (leftInverseColumns j) = if (22 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_23 : ∀ j : Fin 56,

    dotMod (leftMinorRows 23) (leftInverseColumns j) = if (23 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_24 : ∀ j : Fin 56,

    dotMod (leftMinorRows 24) (leftInverseColumns j) = if (24 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_25 : ∀ j : Fin 56,

    dotMod (leftMinorRows 25) (leftInverseColumns j) = if (25 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_26 : ∀ j : Fin 56,

    dotMod (leftMinorRows 26) (leftInverseColumns j) = if (26 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_27 : ∀ j : Fin 56,

    dotMod (leftMinorRows 27) (leftInverseColumns j) = if (27 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_28 : ∀ j : Fin 56,

    dotMod (leftMinorRows 28) (leftInverseColumns j) = if (28 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_29 : ∀ j : Fin 56,

    dotMod (leftMinorRows 29) (leftInverseColumns j) = if (29 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_30 : ∀ j : Fin 56,

    dotMod (leftMinorRows 30) (leftInverseColumns j) = if (30 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_31 : ∀ j : Fin 56,

    dotMod (leftMinorRows 31) (leftInverseColumns j) = if (31 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_32 : ∀ j : Fin 56,

    dotMod (leftMinorRows 32) (leftInverseColumns j) = if (32 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_33 : ∀ j : Fin 56,

    dotMod (leftMinorRows 33) (leftInverseColumns j) = if (33 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_34 : ∀ j : Fin 56,

    dotMod (leftMinorRows 34) (leftInverseColumns j) = if (34 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_35 : ∀ j : Fin 56,

    dotMod (leftMinorRows 35) (leftInverseColumns j) = if (35 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_36 : ∀ j : Fin 56,

    dotMod (leftMinorRows 36) (leftInverseColumns j) = if (36 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_37 : ∀ j : Fin 56,

    dotMod (leftMinorRows 37) (leftInverseColumns j) = if (37 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_38 : ∀ j : Fin 56,

    dotMod (leftMinorRows 38) (leftInverseColumns j) = if (38 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_39 : ∀ j : Fin 56,

    dotMod (leftMinorRows 39) (leftInverseColumns j) = if (39 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_40 : ∀ j : Fin 56,

    dotMod (leftMinorRows 40) (leftInverseColumns j) = if (40 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_41 : ∀ j : Fin 56,

    dotMod (leftMinorRows 41) (leftInverseColumns j) = if (41 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_42 : ∀ j : Fin 56,

    dotMod (leftMinorRows 42) (leftInverseColumns j) = if (42 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_43 : ∀ j : Fin 56,

    dotMod (leftMinorRows 43) (leftInverseColumns j) = if (43 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_44 : ∀ j : Fin 56,

    dotMod (leftMinorRows 44) (leftInverseColumns j) = if (44 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_45 : ∀ j : Fin 56,

    dotMod (leftMinorRows 45) (leftInverseColumns j) = if (45 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_46 : ∀ j : Fin 56,

    dotMod (leftMinorRows 46) (leftInverseColumns j) = if (46 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_47 : ∀ j : Fin 56,

    dotMod (leftMinorRows 47) (leftInverseColumns j) = if (47 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_48 : ∀ j : Fin 56,

    dotMod (leftMinorRows 48) (leftInverseColumns j) = if (48 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_49 : ∀ j : Fin 56,

    dotMod (leftMinorRows 49) (leftInverseColumns j) = if (49 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_50 : ∀ j : Fin 56,

    dotMod (leftMinorRows 50) (leftInverseColumns j) = if (50 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_51 : ∀ j : Fin 56,

    dotMod (leftMinorRows 51) (leftInverseColumns j) = if (51 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_52 : ∀ j : Fin 56,

    dotMod (leftMinorRows 52) (leftInverseColumns j) = if (52 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_53 : ∀ j : Fin 56,

    dotMod (leftMinorRows 53) (leftInverseColumns j) = if (53 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_54 : ∀ j : Fin 56,

    dotMod (leftMinorRows 54) (leftInverseColumns j) = if (54 : Fin 56)=j then 1 else 0 := by

  decide +kernel

private theorem left_inverse_row_55 : ∀ j : Fin 56,

    dotMod (leftMinorRows 55) (leftInverseColumns j) = if (55 : Fin 56)=j then 1 else 0 := by

  decide +kernel

theorem left_inverse_checks (i j : Fin 56) :

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

theorem left_minor_det_ne_zero [Nontrivial R] :

    Matrix.det (fun i j : Fin 56 => sectionCoefficient .left (57 : R) 33 (leftRows i) (leftColumns j)) ≠ 0 := by

  have hm : (fun i j : Fin 56 => sectionCoefficient .left (57 : R) 33 (leftRows i) (leftColumns j)) =

      matrixOfRows leftMinorRows := by ext i j; exact left_matrix_coefficients i j

  rw [hm]

  apply determinant_ne_zero_of_dot_checks leftMinorRows leftInverseColumns

  · decide +kernel

  · decide +kernel

  · exact left_inverse_checks

end

end CycleQ2SeedLinkageModularChecks

#print axioms CycleQ2SeedLinkageModularChecks.left_minor_det_ne_zero
end


/- Component: continuation_3/SeedLinkageModularRight.lean -/
section
set_option maxRecDepth 100000

set_option maxHeartbeats 0

set_option Elab.async false

set_option backward.isDefEq.respectTransparency false

set_option linter.unusedSimpArgs false

namespace CycleQ2SeedLinkageModularChecks

open MvPolynomial CycleQ2IncidenceEquations CycleQ2CurveRestriction CycleQ2CurveRestrictionReflection

open CycleQ2SparseModularPolynomial CycleQ2SeedLinkageIdeals CycleQ2SeedLinkageSections

open CycleQ2SeedLinkageReflection CycleQ2CurveRestrictionMatrixCheck CycleQ2SeedLinkageModularData

noncomputable section

variable {R : Type*} [CommRing R] [CharP R 109]

private theorem right_normal_good_0 : fullGood 8 1 rightNormal0=true := by decide +kernel

private theorem right_normal_check_0 :

    checkZero (residual rightInput0 rightNormal0 rightH0 rightG0 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem right_column_0 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .right 57 (0,(0,0,0,4,0))) = fullValue rightNormal0 := by

  have hinput : sectionPolynomial .right (57 : R) (0,(0,0,0,4,0)) = fullValue rightInput0 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, rightInput0, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 8 1 rightInput0 rightNormal0 rightH0 rightG0

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    right_normal_good_0 right_normal_check_0

private theorem right_normal_good_1 : fullGood 8 1 rightNormal1=true := by decide +kernel

private theorem right_normal_check_1 :

    checkZero (residual rightInput1 rightNormal1 rightH1 rightG1 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem right_column_1 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .right 57 (0,(0,0,3,1,0))) = fullValue rightNormal1 := by

  have hinput : sectionPolynomial .right (57 : R) (0,(0,0,3,1,0)) = fullValue rightInput1 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, rightInput1, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 8 1 rightInput1 rightNormal1 rightH1 rightG1

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    right_normal_good_1 right_normal_check_1

private theorem right_normal_good_2 : fullGood 8 1 rightNormal2=true := by decide +kernel

private theorem right_normal_check_2 :

    checkZero (residual rightInput2 rightNormal2 rightH2 rightG2 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem right_column_2 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .right 57 (0,(0,1,1,2,0))) = fullValue rightNormal2 := by

  have hinput : sectionPolynomial .right (57 : R) (0,(0,1,1,2,0)) = fullValue rightInput2 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, rightInput2, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 8 1 rightInput2 rightNormal2 rightH2 rightG2

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    right_normal_good_2 right_normal_check_2

private theorem right_normal_good_3 : fullGood 8 1 rightNormal3=true := by decide +kernel

private theorem right_normal_check_3 :

    checkZero (residual rightInput3 rightNormal3 rightH3 rightG3 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem right_column_3 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .right 57 (0,(0,2,2,0,0))) = fullValue rightNormal3 := by

  have hinput : sectionPolynomial .right (57 : R) (0,(0,2,2,0,0)) = fullValue rightInput3 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, rightInput3, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 8 1 rightInput3 rightNormal3 rightH3 rightG3

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    right_normal_good_3 right_normal_check_3

private theorem right_normal_good_4 : fullGood 8 1 rightNormal4=true := by decide +kernel

private theorem right_normal_check_4 :

    checkZero (residual rightInput4 rightNormal4 rightH4 rightG4 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem right_column_4 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .right 57 (0,(0,3,0,1,0))) = fullValue rightNormal4 := by

  have hinput : sectionPolynomial .right (57 : R) (0,(0,3,0,1,0)) = fullValue rightInput4 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, rightInput4, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 8 1 rightInput4 rightNormal4 rightH4 rightG4

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    right_normal_good_4 right_normal_check_4

private theorem right_normal_good_5 : fullGood 8 1 rightNormal5=true := by decide +kernel

private theorem right_normal_check_5 :

    checkZero (residual rightInput5 rightNormal5 rightH5 rightG5 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem right_column_5 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .right 57 (0,(0,0,0,2,1))) = fullValue rightNormal5 := by

  have hinput : sectionPolynomial .right (57 : R) (0,(0,0,0,2,1)) = fullValue rightInput5 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, rightInput5, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 8 1 rightInput5 rightNormal5 rightH5 rightG5

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    right_normal_good_5 right_normal_check_5

private theorem right_normal_good_6 : fullGood 8 1 rightNormal6=true := by decide +kernel

private theorem right_normal_check_6 :

    checkZero (residual rightInput6 rightNormal6 rightH6 rightG6 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem right_column_6 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .right 57 (0,(0,1,1,0,1))) = fullValue rightNormal6 := by

  have hinput : sectionPolynomial .right (57 : R) (0,(0,1,1,0,1)) = fullValue rightInput6 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, rightInput6, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 8 1 rightInput6 rightNormal6 rightH6 rightG6

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    right_normal_good_6 right_normal_check_6

private theorem right_normal_good_7 : fullGood 8 1 rightNormal7=true := by decide +kernel

private theorem right_normal_check_7 :

    checkZero (residual rightInput7 rightNormal7 rightH7 rightG7 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem right_column_7 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .right 57 (0,(0,0,0,0,2))) = fullValue rightNormal7 := by

  have hinput : sectionPolynomial .right (57 : R) (0,(0,0,0,0,2)) = fullValue rightInput7 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, rightInput7, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 8 1 rightInput7 rightNormal7 rightH7 rightG7

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    right_normal_good_7 right_normal_check_7

private theorem right_normal_good_8 : fullGood 8 1 rightNormal8=true := by decide +kernel

private theorem right_normal_check_8 :

    checkZero (residual rightInput8 rightNormal8 rightH8 rightG8 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem right_column_8 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .right 57 (0,(1,0,1,2,0))) = fullValue rightNormal8 := by

  have hinput : sectionPolynomial .right (57 : R) (0,(1,0,1,2,0)) = fullValue rightInput8 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, rightInput8, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 8 1 rightInput8 rightNormal8 rightH8 rightG8

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    right_normal_good_8 right_normal_check_8

private theorem right_normal_good_9 : fullGood 8 1 rightNormal9=true := by decide +kernel

private theorem right_normal_check_9 :

    checkZero (residual rightInput9 rightNormal9 rightH9 rightG9 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem right_column_9 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .right 57 (0,(1,1,2,0,0))) = fullValue rightNormal9 := by

  have hinput : sectionPolynomial .right (57 : R) (0,(1,1,2,0,0)) = fullValue rightInput9 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, rightInput9, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 8 1 rightInput9 rightNormal9 rightH9 rightG9

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    right_normal_good_9 right_normal_check_9

private theorem right_normal_good_10 : fullGood 8 1 rightNormal10=true := by decide +kernel

private theorem right_normal_check_10 :

    checkZero (residual rightInput10 rightNormal10 rightH10 rightG10 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem right_column_10 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .right 57 (0,(1,2,0,1,0))) = fullValue rightNormal10 := by

  have hinput : sectionPolynomial .right (57 : R) (0,(1,2,0,1,0)) = fullValue rightInput10 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, rightInput10, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 8 1 rightInput10 rightNormal10 rightH10 rightG10

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    right_normal_good_10 right_normal_check_10

private theorem right_normal_good_11 : fullGood 8 1 rightNormal11=true := by decide +kernel

private theorem right_normal_check_11 :

    checkZero (residual rightInput11 rightNormal11 rightH11 rightG11 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem right_column_11 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .right 57 (0,(1,0,1,0,1))) = fullValue rightNormal11 := by

  have hinput : sectionPolynomial .right (57 : R) (0,(1,0,1,0,1)) = fullValue rightInput11 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, rightInput11, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 8 1 rightInput11 rightNormal11 rightH11 rightG11

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    right_normal_good_11 right_normal_check_11

private theorem right_normal_good_12 : fullGood 8 1 rightNormal12=true := by decide +kernel

private theorem right_normal_check_12 :

    checkZero (residual rightInput12 rightNormal12 rightH12 rightG12 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem right_column_12 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .right 57 (0,(2,0,2,0,0))) = fullValue rightNormal12 := by

  have hinput : sectionPolynomial .right (57 : R) (0,(2,0,2,0,0)) = fullValue rightInput12 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, rightInput12, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 8 1 rightInput12 rightNormal12 rightH12 rightG12

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    right_normal_good_12 right_normal_check_12

private theorem right_normal_good_13 : fullGood 8 1 rightNormal13=true := by decide +kernel

private theorem right_normal_check_13 :

    checkZero (residual rightInput13 rightNormal13 rightH13 rightG13 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem right_column_13 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .right 57 (0,(2,1,0,1,0))) = fullValue rightNormal13 := by

  have hinput : sectionPolynomial .right (57 : R) (0,(2,1,0,1,0)) = fullValue rightInput13 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, rightInput13, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 8 1 rightInput13 rightNormal13 rightH13 rightG13

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    right_normal_good_13 right_normal_check_13

private theorem right_normal_good_14 : fullGood 8 1 rightNormal14=true := by decide +kernel

private theorem right_normal_check_14 :

    checkZero (residual rightInput14 rightNormal14 rightH14 rightG14 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem right_column_14 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .right 57 (1,(0,0,1,1,0))) = fullValue rightNormal14 := by

  have hinput : sectionPolynomial .right (57 : R) (1,(0,0,1,1,0)) = fullValue rightInput14 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, rightInput14, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 8 1 rightInput14 rightNormal14 rightH14 rightG14

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    right_normal_good_14 right_normal_check_14

private theorem right_normal_good_15 : fullGood 8 1 rightNormal15=true := by decide +kernel

private theorem right_normal_check_15 :

    checkZero (residual rightInput15 rightNormal15 rightH15 rightG15 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem right_column_15 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .right 57 (1,(0,2,0,0,0))) = fullValue rightNormal15 := by

  have hinput : sectionPolynomial .right (57 : R) (1,(0,2,0,0,0)) = fullValue rightInput15 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, rightInput15, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 8 1 rightInput15 rightNormal15 rightH15 rightG15

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    right_normal_good_15 right_normal_check_15

private theorem right_normal_good_16 : fullGood 8 1 rightNormal16=true := by decide +kernel

private theorem right_normal_check_16 :

    checkZero (residual rightInput16 rightNormal16 rightH16 rightG16 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem right_column_16 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .right 57 (1,(1,1,0,0,0))) = fullValue rightNormal16 := by

  have hinput : sectionPolynomial .right (57 : R) (1,(1,1,0,0,0)) = fullValue rightInput16 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, rightInput16, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 8 1 rightInput16 rightNormal16 rightH16 rightG16

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    right_normal_good_16 right_normal_check_16

private theorem right_normal_good_17 : fullGood 8 1 rightNormal17=true := by decide +kernel

private theorem right_normal_check_17 :

    checkZero (residual rightInput17 rightNormal17 rightH17 rightG17 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem right_column_17 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .right 57 (1,(2,0,0,0,0))) = fullValue rightNormal17 := by

  have hinput : sectionPolynomial .right (57 : R) (1,(2,0,0,0,0)) = fullValue rightInput17 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, rightInput17, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 8 1 rightInput17 rightNormal17 rightH17 rightG17

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    right_normal_good_17 right_normal_check_17

private theorem right_normal_good_18 : fullGood 8 1 rightNormal18=true := by decide +kernel

private theorem right_normal_check_18 :

    checkZero (residual rightInput18 rightNormal18 rightH18 rightG18 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem right_column_18 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .right 57 (2,(0,0,0,2,0))) = fullValue rightNormal18 := by

  have hinput : sectionPolynomial .right (57 : R) (2,(0,0,0,2,0)) = fullValue rightInput18 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, rightInput18, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 8 1 rightInput18 rightNormal18 rightH18 rightG18

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    right_normal_good_18 right_normal_check_18

private theorem right_normal_good_19 : fullGood 8 1 rightNormal19=true := by decide +kernel

private theorem right_normal_check_19 :

    checkZero (residual rightInput19 rightNormal19 rightH19 rightG19 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem right_column_19 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .right 57 (2,(0,1,1,0,0))) = fullValue rightNormal19 := by

  have hinput : sectionPolynomial .right (57 : R) (2,(0,1,1,0,0)) = fullValue rightInput19 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, rightInput19, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 8 1 rightInput19 rightNormal19 rightH19 rightG19

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    right_normal_good_19 right_normal_check_19

private theorem right_normal_good_20 : fullGood 8 1 rightNormal20=true := by decide +kernel

private theorem right_normal_check_20 :

    checkZero (residual rightInput20 rightNormal20 rightH20 rightG20 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem right_column_20 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .right 57 (2,(0,0,0,0,1))) = fullValue rightNormal20 := by

  have hinput : sectionPolynomial .right (57 : R) (2,(0,0,0,0,1)) = fullValue rightInput20 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, rightInput20, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 8 1 rightInput20 rightNormal20 rightH20 rightG20

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    right_normal_good_20 right_normal_check_20

private theorem right_normal_good_21 : fullGood 8 1 rightNormal21=true := by decide +kernel

private theorem right_normal_check_21 :

    checkZero (residual rightInput21 rightNormal21 rightH21 rightG21 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem right_column_21 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .right 57 (2,(1,0,1,0,0))) = fullValue rightNormal21 := by

  have hinput : sectionPolynomial .right (57 : R) (2,(1,0,1,0,0)) = fullValue rightInput21 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, rightInput21, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 8 1 rightInput21 rightNormal21 rightH21 rightG21

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    right_normal_good_21 right_normal_check_21

private theorem right_normal_good_22 : fullGood 8 1 rightNormal22=true := by decide +kernel

private theorem right_normal_check_22 :

    checkZero (residual rightInput22 rightNormal22 rightH22 rightG22 seedH CycleQ2SeedLinkageModularData.seedG)=true := by

  decide +kernel

theorem right_column_22 [Nontrivial R] :

    seedNormal (57 : R) 33 (sectionPolynomial .right 57 (3,(1,0,0,1,0))) = fullValue rightNormal22 := by

  have hinput : sectionPolynomial .right (57 : R) (3,(1,0,0,1,0)) = fullValue rightInput22 := by

    have hc : CharP (Poly R) 109 := inferInstance

    simp only [sectionPolynomial, sourceMonomial, linkageGenerator,

      CycleQ2SegreSeed.linkageE, CycleQ2SegreSeed.linkageEprime, rightInput22, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [hinput]

  exact checked_seedNormal 57 33 8 1 rightInput22 rightNormal22 rightH22 rightG22

    seedH CycleQ2SeedLinkageModularData.seedG seedH_value seedG_value

    right_normal_good_22 right_normal_check_22

theorem right_columns [Nontrivial R] (j : Fin 23) :

    seedNormal (57 : R) 33 (sectionPolynomial .right 57 (rightColumns j)) = fullValue (rightNormals j) := by

  fin_cases j

  · exact right_column_0

  · exact right_column_1

  · exact right_column_2

  · exact right_column_3

  · exact right_column_4

  · exact right_column_5

  · exact right_column_6

  · exact right_column_7

  · exact right_column_8

  · exact right_column_9

  · exact right_column_10

  · exact right_column_11

  · exact right_column_12

  · exact right_column_13

  · exact right_column_14

  · exact right_column_15

  · exact right_column_16

  · exact right_column_17

  · exact right_column_18

  · exact right_column_19

  · exact right_column_20

  · exact right_column_21

  · exact right_column_22

private theorem right_coefficient_row_0 : ∀ j : Fin 23,

    fullCoefficient (rightRows 0) (rightNormals j) = (rightMinorRows 0).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_1 : ∀ j : Fin 23,

    fullCoefficient (rightRows 1) (rightNormals j) = (rightMinorRows 1).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_2 : ∀ j : Fin 23,

    fullCoefficient (rightRows 2) (rightNormals j) = (rightMinorRows 2).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_3 : ∀ j : Fin 23,

    fullCoefficient (rightRows 3) (rightNormals j) = (rightMinorRows 3).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_4 : ∀ j : Fin 23,

    fullCoefficient (rightRows 4) (rightNormals j) = (rightMinorRows 4).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_5 : ∀ j : Fin 23,

    fullCoefficient (rightRows 5) (rightNormals j) = (rightMinorRows 5).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_6 : ∀ j : Fin 23,

    fullCoefficient (rightRows 6) (rightNormals j) = (rightMinorRows 6).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_7 : ∀ j : Fin 23,

    fullCoefficient (rightRows 7) (rightNormals j) = (rightMinorRows 7).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_8 : ∀ j : Fin 23,

    fullCoefficient (rightRows 8) (rightNormals j) = (rightMinorRows 8).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_9 : ∀ j : Fin 23,

    fullCoefficient (rightRows 9) (rightNormals j) = (rightMinorRows 9).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_10 : ∀ j : Fin 23,

    fullCoefficient (rightRows 10) (rightNormals j) = (rightMinorRows 10).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_11 : ∀ j : Fin 23,

    fullCoefficient (rightRows 11) (rightNormals j) = (rightMinorRows 11).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_12 : ∀ j : Fin 23,

    fullCoefficient (rightRows 12) (rightNormals j) = (rightMinorRows 12).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_13 : ∀ j : Fin 23,

    fullCoefficient (rightRows 13) (rightNormals j) = (rightMinorRows 13).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_14 : ∀ j : Fin 23,

    fullCoefficient (rightRows 14) (rightNormals j) = (rightMinorRows 14).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_15 : ∀ j : Fin 23,

    fullCoefficient (rightRows 15) (rightNormals j) = (rightMinorRows 15).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_16 : ∀ j : Fin 23,

    fullCoefficient (rightRows 16) (rightNormals j) = (rightMinorRows 16).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_17 : ∀ j : Fin 23,

    fullCoefficient (rightRows 17) (rightNormals j) = (rightMinorRows 17).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_18 : ∀ j : Fin 23,

    fullCoefficient (rightRows 18) (rightNormals j) = (rightMinorRows 18).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_19 : ∀ j : Fin 23,

    fullCoefficient (rightRows 19) (rightNormals j) = (rightMinorRows 19).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_20 : ∀ j : Fin 23,

    fullCoefficient (rightRows 20) (rightNormals j) = (rightMinorRows 20).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_21 : ∀ j : Fin 23,

    fullCoefficient (rightRows 21) (rightNormals j) = (rightMinorRows 21).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_22 : ∀ j : Fin 23,

    fullCoefficient (rightRows 22) (rightNormals j) = (rightMinorRows 22).getD j.val 0 := by

  decide +kernel

theorem right_coefficient_table (i j : Fin 23) :

    fullCoefficient (rightRows i) (rightNormals j) = (rightMinorRows i).getD j.val 0 := by

  fin_cases i

  · exact right_coefficient_row_0 j

  · exact right_coefficient_row_1 j

  · exact right_coefficient_row_2 j

  · exact right_coefficient_row_3 j

  · exact right_coefficient_row_4 j

  · exact right_coefficient_row_5 j

  · exact right_coefficient_row_6 j

  · exact right_coefficient_row_7 j

  · exact right_coefficient_row_8 j

  · exact right_coefficient_row_9 j

  · exact right_coefficient_row_10 j

  · exact right_coefficient_row_11 j

  · exact right_coefficient_row_12 j

  · exact right_coefficient_row_13 j

  · exact right_coefficient_row_14 j

  · exact right_coefficient_row_15 j

  · exact right_coefficient_row_16 j

  · exact right_coefficient_row_17 j

  · exact right_coefficient_row_18 j

  · exact right_coefficient_row_19 j

  · exact right_coefficient_row_20 j

  · exact right_coefficient_row_21 j

  · exact right_coefficient_row_22 j

theorem right_matrix_coefficients [Nontrivial R] (i j : Fin 23) :

    sectionCoefficient .right (57 : R) 33 (rightRows i) (rightColumns j) =

      ((rightMinorRows i).getD j.val 0 : R) := by

  rw [sectionCoefficient,right_columns,fullValue_coefficient,right_coefficient_table]

private theorem right_inverse_row_0 : ∀ j : Fin 23,

    dotMod (rightMinorRows 0) (rightInverseColumns j) = if (0 : Fin 23)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_1 : ∀ j : Fin 23,

    dotMod (rightMinorRows 1) (rightInverseColumns j) = if (1 : Fin 23)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_2 : ∀ j : Fin 23,

    dotMod (rightMinorRows 2) (rightInverseColumns j) = if (2 : Fin 23)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_3 : ∀ j : Fin 23,

    dotMod (rightMinorRows 3) (rightInverseColumns j) = if (3 : Fin 23)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_4 : ∀ j : Fin 23,

    dotMod (rightMinorRows 4) (rightInverseColumns j) = if (4 : Fin 23)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_5 : ∀ j : Fin 23,

    dotMod (rightMinorRows 5) (rightInverseColumns j) = if (5 : Fin 23)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_6 : ∀ j : Fin 23,

    dotMod (rightMinorRows 6) (rightInverseColumns j) = if (6 : Fin 23)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_7 : ∀ j : Fin 23,

    dotMod (rightMinorRows 7) (rightInverseColumns j) = if (7 : Fin 23)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_8 : ∀ j : Fin 23,

    dotMod (rightMinorRows 8) (rightInverseColumns j) = if (8 : Fin 23)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_9 : ∀ j : Fin 23,

    dotMod (rightMinorRows 9) (rightInverseColumns j) = if (9 : Fin 23)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_10 : ∀ j : Fin 23,

    dotMod (rightMinorRows 10) (rightInverseColumns j) = if (10 : Fin 23)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_11 : ∀ j : Fin 23,

    dotMod (rightMinorRows 11) (rightInverseColumns j) = if (11 : Fin 23)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_12 : ∀ j : Fin 23,

    dotMod (rightMinorRows 12) (rightInverseColumns j) = if (12 : Fin 23)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_13 : ∀ j : Fin 23,

    dotMod (rightMinorRows 13) (rightInverseColumns j) = if (13 : Fin 23)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_14 : ∀ j : Fin 23,

    dotMod (rightMinorRows 14) (rightInverseColumns j) = if (14 : Fin 23)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_15 : ∀ j : Fin 23,

    dotMod (rightMinorRows 15) (rightInverseColumns j) = if (15 : Fin 23)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_16 : ∀ j : Fin 23,

    dotMod (rightMinorRows 16) (rightInverseColumns j) = if (16 : Fin 23)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_17 : ∀ j : Fin 23,

    dotMod (rightMinorRows 17) (rightInverseColumns j) = if (17 : Fin 23)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_18 : ∀ j : Fin 23,

    dotMod (rightMinorRows 18) (rightInverseColumns j) = if (18 : Fin 23)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_19 : ∀ j : Fin 23,

    dotMod (rightMinorRows 19) (rightInverseColumns j) = if (19 : Fin 23)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_20 : ∀ j : Fin 23,

    dotMod (rightMinorRows 20) (rightInverseColumns j) = if (20 : Fin 23)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_21 : ∀ j : Fin 23,

    dotMod (rightMinorRows 21) (rightInverseColumns j) = if (21 : Fin 23)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_22 : ∀ j : Fin 23,

    dotMod (rightMinorRows 22) (rightInverseColumns j) = if (22 : Fin 23)=j then 1 else 0 := by

  decide +kernel

theorem right_inverse_checks (i j : Fin 23) :

    dotMod (rightMinorRows i) (rightInverseColumns j) = if i=j then 1 else 0 := by

  fin_cases i

  · exact right_inverse_row_0 j

  · exact right_inverse_row_1 j

  · exact right_inverse_row_2 j

  · exact right_inverse_row_3 j

  · exact right_inverse_row_4 j

  · exact right_inverse_row_5 j

  · exact right_inverse_row_6 j

  · exact right_inverse_row_7 j

  · exact right_inverse_row_8 j

  · exact right_inverse_row_9 j

  · exact right_inverse_row_10 j

  · exact right_inverse_row_11 j

  · exact right_inverse_row_12 j

  · exact right_inverse_row_13 j

  · exact right_inverse_row_14 j

  · exact right_inverse_row_15 j

  · exact right_inverse_row_16 j

  · exact right_inverse_row_17 j

  · exact right_inverse_row_18 j

  · exact right_inverse_row_19 j

  · exact right_inverse_row_20 j

  · exact right_inverse_row_21 j

  · exact right_inverse_row_22 j

theorem right_minor_det_ne_zero [Nontrivial R] :

    Matrix.det (fun i j : Fin 23 => sectionCoefficient .right (57 : R) 33 (rightRows i) (rightColumns j)) ≠ 0 := by

  have hm : (fun i j : Fin 23 => sectionCoefficient .right (57 : R) 33 (rightRows i) (rightColumns j)) =

      matrixOfRows rightMinorRows := by ext i j; exact right_matrix_coefficients i j

  rw [hm]

  apply determinant_ne_zero_of_dot_checks rightMinorRows rightInverseColumns

  · decide +kernel

  · decide +kernel

  · exact right_inverse_checks

end

end CycleQ2SeedLinkageModularChecks

#print axioms CycleQ2SeedLinkageModularChecks.right_minor_det_ne_zero
end


/- Component: continuation_3/SeedLinkageOrbitKernel.lean -/
section
/-! On a fixed graded piece, vanishing on the chosen component is exactly
membership in the actual three-component linkage ideal on every coordinate
chart.  The orbit transfer uses the literal diagonal action. -/

noncomputable section
set_option maxHeartbeats 100000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedLinkageOrbitKernel

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2CurveRestriction CycleQ2SeedLinkageIdeals
  CycleQ2SeedLinkagePrincipal CycleQ2SeedLinkageOrbitCover CycleQ2SeedLinkageComponents
  CycleQ2LinkageComponentDecomposition CycleQ2LinkageComponentAlgebra
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalizedBasis CycleQ2SeedCyclicAction
  CycleQ2SeedCyclicLocalization

section Generic
variable {A : Type*} [CommRing A]

theorem map_component_one_le (T : A →+* A) (z a b c d : A)
    (ha : T a=z*a) (hb : T b=z^2*b) (hc : T c=c) (hd : T d=z^2*d) :
    (CycleQ2LinkageComponentDecomposition.componentIdeal 1 a b c d).map T≤
      CycleQ2LinkageComponentDecomposition.componentIdeal z a b c d := by
  rw [CycleQ2LinkageComponentDecomposition.componentIdeal,Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro x ⟨y,⟨i,rfl⟩,rfl⟩
  fin_cases i
  · change T (a-1*b)∈CycleQ2LinkageComponentDecomposition.componentIdeal z a b c d
    rw [one_mul,map_sub,ha,hb]
    have he : z*a-z^2*b=z*(a-z*b) := by ring
    rw [he]
    exact (CycleQ2LinkageComponentDecomposition.componentIdeal z a b c d).mul_mem_left z
      (componentGenerator_mem z a b c d 0)
  · change T (c+1^2*d)∈CycleQ2LinkageComponentDecomposition.componentIdeal z a b c d
    rw [one_pow,one_mul,map_add,hc,hd]
    exact componentGenerator_mem z a b c d 1

theorem polynomialAction_A (ζ : A) (hζ : ζ^3=1) :
    polynomialAction ζ (X 0^2)=C ζ*(X 0^2) := by
  rw [map_pow,polynomialAction_X]
  change (C (ζ^2)*X 0)^2=C ζ*(X 0^2)
  rw [mul_pow,←map_pow]
  have h4 : (ζ^2)^2=ζ := by linear_combination ζ*hζ
  rw [h4]

theorem polynomialAction_B (ζ r : A) :
    polynomialAction ζ (C r*X 1*X 3)=C (ζ^2)*(C r*X 1*X 3) := by
  simp only [map_mul,polynomialAction_C,polynomialAction_X]
  change C r*(C (ζ^2)*X 1)*X 3=C (ζ^2)*(C r*X 1*X 3)
  ring

theorem polynomialAction_D (ζ : A) :
    polynomialAction ζ (X 2^2)=C (ζ^2)*(X 2^2) := by
  rw [map_pow,polynomialAction_X]
  change (C ζ*X 2)^2=C (ζ^2)*(X 2^2)
  rw [mul_pow,map_pow]

end Generic

variable {K : Type*} [Field K]

theorem localAction_component_map_le (s : Side) (r ι ζ : K) (hζ : ζ^3=1)
    (t : Finset (Fin 3)) :
    (localComponent s r ι t 1).map (localAction ζ hζ r ι t)≤localComponent s r ι t ζ := by
  let φ := algebraMap (SeedRing r ι) (SeedLocal K r ι t)
  let T := localAction ζ hζ r ι t
  have hA : T (φ (linkageA r ι))=localScalar r ι t ζ*φ (linkageA r ι) := by
    change localAction ζ hζ r ι t (φ (Ideal.Quotient.mk _ (X 0^2)))=_
    rw [localAction_mk,polynomialAction_A ζ hζ,map_mul,map_mul]
    rfl
  have hB : T (φ (linkageB r ι))=localScalar r ι t ζ^2*φ (linkageB r ι) := by
    change localAction ζ hζ r ι t (φ (Ideal.Quotient.mk _ (C r*X 1*X 3)))=_
    rw [localAction_mk,polynomialAction_B,map_mul,map_mul]
    change localScalar r ι t (ζ^2)*φ (linkageB r ι)=_
    rw [map_pow]
  have hC : T (φ (linkageC r ι))=φ (linkageC r ι) := by
    change localAction ζ hζ r ι t (φ (Ideal.Quotient.mk _ (X 4)))=_
    rw [localAction_mk,polynomialAction_X]
    rfl
  have hD : T (φ (linkageD r ι))=localScalar r ι t ζ^2*φ (linkageD r ι) := by
    change localAction ζ hζ r ι t (φ (Ideal.Quotient.mk _ (X 2^2)))=_
    rw [localAction_mk,polynomialAction_D,map_mul,map_mul]
    change localScalar r ι t (ζ^2)*φ (linkageD r ι)=_
    rw [map_pow]
  have hoB : T (φ (orbitB s r ι))=localScalar r ι t ζ^2*φ (orbitB s r ι) := by
    cases s
    · exact hB
    · simpa only [orbitB,map_neg,mul_neg] using congrArg Neg.neg hD
  have hoD : T (φ (orbitD s r ι))=localScalar r ι t ζ^2*φ (orbitD s r ι) := by
    cases s
    · exact hD
    · simpa only [orbitD,map_neg,mul_neg] using congrArg Neg.neg hB
  simpa only [localComponent,map_one] using
    map_component_one_le T (localScalar r ι t ζ) (φ (linkageA r ι)) (φ (orbitB s r ι))
      (φ (linkageC r ι)) (φ (orbitD s r ι)) hA hoB hC hoD

theorem homogeneous_mem_component_of_mem_one (s : Side) (r ι ζ : K) (hζ : ζ^3=1)
    (t : Finset (Fin 3)) (q : SeedLocal K r ι t) (g : LaurentGrade)
    (hq : ∀ ab, HasGrade ab g (localizedCoordinates K r ι t q ab))
    (hzero : q∈localComponent s r ι t 1) : q∈localComponent s r ι t ζ := by
  apply homogeneous_mem_of_action_mem ζ hζ r ι t q g hq
  exact localAction_component_map_le s r ι ζ hζ t
    (Ideal.mem_map_of_mem (localAction ζ hζ r ι t) hzero)

theorem homogeneous_mem_linkage_iff_component (s : Side) (r ι : ℂ)
    (hr : r≠0) (hι : ι≠0) (hι1 : ι≠1) (t : Finset (Fin 3)) (ht : t.Nonempty)
    (q : SeedLocal ℂ r ι t) (g : LaurentGrade)
    (hq : ∀ ab, HasGrade ab g (localizedCoordinates ℂ r ι t q ab)) :
    q∈localLinkageIdeal s r ι t ↔ q∈localComponent s r ι t 1 := by
  rw [localized_linkageIdeal_eq_components s r ι hr hι hι1 t ht]
  constructor
  · exact fun h => h.1.1
  · intro hzero
    refine ⟨⟨hzero,?_⟩,?_⟩
    · exact homogeneous_mem_component_of_mem_one s r ι complexRoot complexRoot_cube t q g hq hzero
    · exact homogeneous_mem_component_of_mem_one s r ι (complexRoot^2)
        (rootValues_cube complexRoot complexRoot_quadratic 2) t q g hq hzero

end CycleQ2SeedLinkageOrbitKernel

#print axioms CycleQ2SeedLinkageOrbitKernel.homogeneous_mem_linkage_iff_component
end
end


