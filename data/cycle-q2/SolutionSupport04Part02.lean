import Proposal.SolutionSupport04Part01

/-! Components extracted from SolutionSupport04.lean, in their original order.
See solution.md for the mathematical and verification status. -/

set_option Elab.async false

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


