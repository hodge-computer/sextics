import Proposal.Workspace
import Proposal.GeometricTarget11Part04
import Proposal.Assembly01Part01

/-! Source partition of Assembly01.lean; declarations and proofs are preserved. -/

set_option Elab.async false

/- Component: continuation_3/CurveRestrictionModularRight.lean -/
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

theorem right_quadric_value : value (R:=R) rightQuadric = quadric .right (57 : R) := by

  have hc : CharP (CurvePoly R) 109 := inferInstance

  simp only [rightQuadric, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg, quadric, cubic]

  apply sub_eq_zero.mp

  ring_nf <;> reduce_mod_char!

theorem right_cubic_value : value (R:=R) rightCubic = cubic .right (57 : R) 33 := by

  have hc : CharP (CurvePoly R) 109 := inferInstance

  simp only [rightCubic, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg, quadric, cubic]

  apply sub_eq_zero.mp

  ring_nf <;> reduce_mod_char!

private theorem right_normal_good_0 : goodPolynomial .right 8 rightNormal0=true := by decide +kernel

private theorem right_normal_check_0 :

    checkZero (residual rightInput0 rightNormal0 rightQ0 rightH0 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_0 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (0,0,1,7,0)) = value rightNormal0 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (0,0,1,7,0)) = value rightInput0 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput0, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput0 rightNormal0 rightQ0 rightH0

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_0 right_normal_check_0

private theorem right_normal_good_1 : goodPolynomial .right 8 rightNormal1=true := by decide +kernel

private theorem right_normal_check_1 :

    checkZero (residual rightInput1 rightNormal1 rightQ1 rightH1 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_1 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (0,0,4,4,0)) = value rightNormal1 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (0,0,4,4,0)) = value rightInput1 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput1, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput1 rightNormal1 rightQ1 rightH1

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_1 right_normal_check_1

private theorem right_normal_good_2 : goodPolynomial .right 8 rightNormal2=true := by decide +kernel

private theorem right_normal_check_2 :

    checkZero (residual rightInput2 rightNormal2 rightQ2 rightH2 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_2 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (0,0,7,1,0)) = value rightNormal2 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (0,0,7,1,0)) = value rightInput2 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput2, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput2 rightNormal2 rightQ2 rightH2

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_2 right_normal_check_2

private theorem right_normal_good_3 : goodPolynomial .right 8 rightNormal3=true := by decide +kernel

private theorem right_normal_check_3 :

    checkZero (residual rightInput3 rightNormal3 rightQ3 rightH3 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_3 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (0,1,2,5,0)) = value rightNormal3 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (0,1,2,5,0)) = value rightInput3 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput3, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput3 rightNormal3 rightQ3 rightH3

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_3 right_normal_check_3

private theorem right_normal_good_4 : goodPolynomial .right 8 rightNormal4=true := by decide +kernel

private theorem right_normal_check_4 :

    checkZero (residual rightInput4 rightNormal4 rightQ4 rightH4 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_4 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (0,1,5,2,0)) = value rightNormal4 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (0,1,5,2,0)) = value rightInput4 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput4, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput4 rightNormal4 rightQ4 rightH4

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_4 right_normal_check_4

private theorem right_normal_good_5 : goodPolynomial .right 8 rightNormal5=true := by decide +kernel

private theorem right_normal_check_5 :

    checkZero (residual rightInput5 rightNormal5 rightQ5 rightH5 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_5 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (0,2,0,6,0)) = value rightNormal5 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (0,2,0,6,0)) = value rightInput5 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput5, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput5 rightNormal5 rightQ5 rightH5

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_5 right_normal_check_5

private theorem right_normal_good_6 : goodPolynomial .right 8 rightNormal6=true := by decide +kernel

private theorem right_normal_check_6 :

    checkZero (residual rightInput6 rightNormal6 rightQ6 rightH6 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_6 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (0,2,3,3,0)) = value rightNormal6 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (0,2,3,3,0)) = value rightInput6 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput6, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput6 rightNormal6 rightQ6 rightH6

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_6 right_normal_check_6

private theorem right_normal_good_7 : goodPolynomial .right 8 rightNormal7=true := by decide +kernel

private theorem right_normal_check_7 :

    checkZero (residual rightInput7 rightNormal7 rightQ7 rightH7 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_7 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (0,2,6,0,0)) = value rightNormal7 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (0,2,6,0,0)) = value rightInput7 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput7, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput7 rightNormal7 rightQ7 rightH7

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_7 right_normal_check_7

private theorem right_normal_good_8 : goodPolynomial .right 8 rightNormal8=true := by decide +kernel

private theorem right_normal_check_8 :

    checkZero (residual rightInput8 rightNormal8 rightQ8 rightH8 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_8 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (0,3,1,4,0)) = value rightNormal8 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (0,3,1,4,0)) = value rightInput8 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput8, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput8 rightNormal8 rightQ8 rightH8

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_8 right_normal_check_8

private theorem right_normal_good_9 : goodPolynomial .right 8 rightNormal9=true := by decide +kernel

private theorem right_normal_check_9 :

    checkZero (residual rightInput9 rightNormal9 rightQ9 rightH9 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_9 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (0,3,4,1,0)) = value rightNormal9 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (0,3,4,1,0)) = value rightInput9 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput9, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput9 rightNormal9 rightQ9 rightH9

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_9 right_normal_check_9

private theorem right_normal_good_10 : goodPolynomial .right 8 rightNormal10=true := by decide +kernel

private theorem right_normal_check_10 :

    checkZero (residual rightInput10 rightNormal10 rightQ10 rightH10 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_10 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (0,4,2,2,0)) = value rightNormal10 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (0,4,2,2,0)) = value rightInput10 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput10, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput10 rightNormal10 rightQ10 rightH10

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_10 right_normal_check_10

private theorem right_normal_good_11 : goodPolynomial .right 8 rightNormal11=true := by decide +kernel

private theorem right_normal_check_11 :

    checkZero (residual rightInput11 rightNormal11 rightQ11 rightH11 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_11 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (0,5,0,3,0)) = value rightNormal11 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (0,5,0,3,0)) = value rightInput11 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput11, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput11 rightNormal11 rightQ11 rightH11

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_11 right_normal_check_11

private theorem right_normal_good_12 : goodPolynomial .right 8 rightNormal12=true := by decide +kernel

private theorem right_normal_check_12 :

    checkZero (residual rightInput12 rightNormal12 rightQ12 rightH12 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_12 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (0,5,3,0,0)) = value rightNormal12 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (0,5,3,0,0)) = value rightInput12 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput12, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput12 rightNormal12 rightQ12 rightH12

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_12 right_normal_check_12

private theorem right_normal_good_13 : goodPolynomial .right 8 rightNormal13=true := by decide +kernel

private theorem right_normal_check_13 :

    checkZero (residual rightInput13 rightNormal13 rightQ13 rightH13 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_13 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (0,6,1,1,0)) = value rightNormal13 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (0,6,1,1,0)) = value rightInput13 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput13, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput13 rightNormal13 rightQ13 rightH13

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_13 right_normal_check_13

private theorem right_normal_good_14 : goodPolynomial .right 8 rightNormal14=true := by decide +kernel

private theorem right_normal_check_14 :

    checkZero (residual rightInput14 rightNormal14 rightQ14 rightH14 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_14 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (0,8,0,0,0)) = value rightNormal14 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (0,8,0,0,0)) = value rightInput14 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput14, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput14 rightNormal14 rightQ14 rightH14

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_14 right_normal_check_14

private theorem right_normal_good_15 : goodPolynomial .right 8 rightNormal15=true := by decide +kernel

private theorem right_normal_check_15 :

    checkZero (residual rightInput15 rightNormal15 rightQ15 rightH15 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_15 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (0,0,1,5,1)) = value rightNormal15 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (0,0,1,5,1)) = value rightInput15 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput15, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput15 rightNormal15 rightQ15 rightH15

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_15 right_normal_check_15

private theorem right_normal_good_16 : goodPolynomial .right 8 rightNormal16=true := by decide +kernel

private theorem right_normal_check_16 :

    checkZero (residual rightInput16 rightNormal16 rightQ16 rightH16 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_16 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (0,0,4,2,1)) = value rightNormal16 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (0,0,4,2,1)) = value rightInput16 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput16, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput16 rightNormal16 rightQ16 rightH16

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_16 right_normal_check_16

private theorem right_normal_good_17 : goodPolynomial .right 8 rightNormal17=true := by decide +kernel

private theorem right_normal_check_17 :

    checkZero (residual rightInput17 rightNormal17 rightQ17 rightH17 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_17 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (0,1,2,3,1)) = value rightNormal17 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (0,1,2,3,1)) = value rightInput17 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput17, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput17 rightNormal17 rightQ17 rightH17

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_17 right_normal_check_17

private theorem right_normal_good_18 : goodPolynomial .right 8 rightNormal18=true := by decide +kernel

private theorem right_normal_check_18 :

    checkZero (residual rightInput18 rightNormal18 rightQ18 rightH18 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_18 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (0,1,5,0,1)) = value rightNormal18 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (0,1,5,0,1)) = value rightInput18 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput18, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput18 rightNormal18 rightQ18 rightH18

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_18 right_normal_check_18

private theorem right_normal_good_19 : goodPolynomial .right 8 rightNormal19=true := by decide +kernel

private theorem right_normal_check_19 :

    checkZero (residual rightInput19 rightNormal19 rightQ19 rightH19 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_19 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (0,2,0,4,1)) = value rightNormal19 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (0,2,0,4,1)) = value rightInput19 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput19, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput19 rightNormal19 rightQ19 rightH19

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_19 right_normal_check_19

private theorem right_normal_good_20 : goodPolynomial .right 8 rightNormal20=true := by decide +kernel

private theorem right_normal_check_20 :

    checkZero (residual rightInput20 rightNormal20 rightQ20 rightH20 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_20 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (0,2,3,1,1)) = value rightNormal20 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (0,2,3,1,1)) = value rightInput20 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput20, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput20 rightNormal20 rightQ20 rightH20

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_20 right_normal_check_20

private theorem right_normal_good_21 : goodPolynomial .right 8 rightNormal21=true := by decide +kernel

private theorem right_normal_check_21 :

    checkZero (residual rightInput21 rightNormal21 rightQ21 rightH21 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_21 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (0,3,1,2,1)) = value rightNormal21 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (0,3,1,2,1)) = value rightInput21 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput21, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput21 rightNormal21 rightQ21 rightH21

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_21 right_normal_check_21

private theorem right_normal_good_22 : goodPolynomial .right 8 rightNormal22=true := by decide +kernel

private theorem right_normal_check_22 :

    checkZero (residual rightInput22 rightNormal22 rightQ22 rightH22 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_22 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (0,4,2,0,1)) = value rightNormal22 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (0,4,2,0,1)) = value rightInput22 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput22, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput22 rightNormal22 rightQ22 rightH22

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_22 right_normal_check_22

private theorem right_normal_good_23 : goodPolynomial .right 8 rightNormal23=true := by decide +kernel

private theorem right_normal_check_23 :

    checkZero (residual rightInput23 rightNormal23 rightQ23 rightH23 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_23 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (0,5,0,1,1)) = value rightNormal23 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (0,5,0,1,1)) = value rightInput23 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput23, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput23 rightNormal23 rightQ23 rightH23

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_23 right_normal_check_23

private theorem right_normal_good_24 : goodPolynomial .right 8 rightNormal24=true := by decide +kernel

private theorem right_normal_check_24 :

    checkZero (residual rightInput24 rightNormal24 rightQ24 rightH24 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_24 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (0,0,1,3,2)) = value rightNormal24 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (0,0,1,3,2)) = value rightInput24 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput24, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput24 rightNormal24 rightQ24 rightH24

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_24 right_normal_check_24

private theorem right_normal_good_25 : goodPolynomial .right 8 rightNormal25=true := by decide +kernel

private theorem right_normal_check_25 :

    checkZero (residual rightInput25 rightNormal25 rightQ25 rightH25 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_25 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (0,0,4,0,2)) = value rightNormal25 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (0,0,4,0,2)) = value rightInput25 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput25, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput25 rightNormal25 rightQ25 rightH25

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_25 right_normal_check_25

private theorem right_normal_good_26 : goodPolynomial .right 8 rightNormal26=true := by decide +kernel

private theorem right_normal_check_26 :

    checkZero (residual rightInput26 rightNormal26 rightQ26 rightH26 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_26 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (0,1,2,1,2)) = value rightNormal26 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (0,1,2,1,2)) = value rightInput26 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput26, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput26 rightNormal26 rightQ26 rightH26

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_26 right_normal_check_26

private theorem right_normal_good_27 : goodPolynomial .right 8 rightNormal27=true := by decide +kernel

private theorem right_normal_check_27 :

    checkZero (residual rightInput27 rightNormal27 rightQ27 rightH27 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_27 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (0,2,0,2,2)) = value rightNormal27 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (0,2,0,2,2)) = value rightInput27 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput27, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput27 rightNormal27 rightQ27 rightH27

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_27 right_normal_check_27

private theorem right_normal_good_28 : goodPolynomial .right 8 rightNormal28=true := by decide +kernel

private theorem right_normal_check_28 :

    checkZero (residual rightInput28 rightNormal28 rightQ28 rightH28 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_28 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (0,3,1,0,2)) = value rightNormal28 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (0,3,1,0,2)) = value rightInput28 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput28, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput28 rightNormal28 rightQ28 rightH28

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_28 right_normal_check_28

private theorem right_normal_good_29 : goodPolynomial .right 8 rightNormal29=true := by decide +kernel

private theorem right_normal_check_29 :

    checkZero (residual rightInput29 rightNormal29 rightQ29 rightH29 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_29 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (1,0,2,5,0)) = value rightNormal29 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (1,0,2,5,0)) = value rightInput29 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput29, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput29 rightNormal29 rightQ29 rightH29

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_29 right_normal_check_29

private theorem right_normal_good_30 : goodPolynomial .right 8 rightNormal30=true := by decide +kernel

private theorem right_normal_check_30 :

    checkZero (residual rightInput30 rightNormal30 rightQ30 rightH30 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_30 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (1,0,5,2,0)) = value rightNormal30 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (1,0,5,2,0)) = value rightInput30 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput30, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput30 rightNormal30 rightQ30 rightH30

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_30 right_normal_check_30

private theorem right_normal_good_31 : goodPolynomial .right 8 rightNormal31=true := by decide +kernel

private theorem right_normal_check_31 :

    checkZero (residual rightInput31 rightNormal31 rightQ31 rightH31 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_31 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (1,1,0,6,0)) = value rightNormal31 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (1,1,0,6,0)) = value rightInput31 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput31, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput31 rightNormal31 rightQ31 rightH31

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_31 right_normal_check_31

private theorem right_normal_good_32 : goodPolynomial .right 8 rightNormal32=true := by decide +kernel

private theorem right_normal_check_32 :

    checkZero (residual rightInput32 rightNormal32 rightQ32 rightH32 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_32 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (1,1,3,3,0)) = value rightNormal32 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (1,1,3,3,0)) = value rightInput32 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput32, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput32 rightNormal32 rightQ32 rightH32

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_32 right_normal_check_32

private theorem right_normal_good_33 : goodPolynomial .right 8 rightNormal33=true := by decide +kernel

private theorem right_normal_check_33 :

    checkZero (residual rightInput33 rightNormal33 rightQ33 rightH33 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_33 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (1,1,6,0,0)) = value rightNormal33 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (1,1,6,0,0)) = value rightInput33 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput33, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput33 rightNormal33 rightQ33 rightH33

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_33 right_normal_check_33

private theorem right_normal_good_34 : goodPolynomial .right 8 rightNormal34=true := by decide +kernel

private theorem right_normal_check_34 :

    checkZero (residual rightInput34 rightNormal34 rightQ34 rightH34 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_34 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (1,2,1,4,0)) = value rightNormal34 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (1,2,1,4,0)) = value rightInput34 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput34, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput34 rightNormal34 rightQ34 rightH34

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_34 right_normal_check_34

private theorem right_normal_good_35 : goodPolynomial .right 8 rightNormal35=true := by decide +kernel

private theorem right_normal_check_35 :

    checkZero (residual rightInput35 rightNormal35 rightQ35 rightH35 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_35 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (1,2,4,1,0)) = value rightNormal35 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (1,2,4,1,0)) = value rightInput35 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput35, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput35 rightNormal35 rightQ35 rightH35

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_35 right_normal_check_35

private theorem right_normal_good_36 : goodPolynomial .right 8 rightNormal36=true := by decide +kernel

private theorem right_normal_check_36 :

    checkZero (residual rightInput36 rightNormal36 rightQ36 rightH36 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_36 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (1,3,2,2,0)) = value rightNormal36 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (1,3,2,2,0)) = value rightInput36 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput36, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput36 rightNormal36 rightQ36 rightH36

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_36 right_normal_check_36

private theorem right_normal_good_37 : goodPolynomial .right 8 rightNormal37=true := by decide +kernel

private theorem right_normal_check_37 :

    checkZero (residual rightInput37 rightNormal37 rightQ37 rightH37 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_37 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (1,4,0,3,0)) = value rightNormal37 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (1,4,0,3,0)) = value rightInput37 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput37, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput37 rightNormal37 rightQ37 rightH37

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_37 right_normal_check_37

private theorem right_normal_good_38 : goodPolynomial .right 8 rightNormal38=true := by decide +kernel

private theorem right_normal_check_38 :

    checkZero (residual rightInput38 rightNormal38 rightQ38 rightH38 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_38 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (1,4,3,0,0)) = value rightNormal38 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (1,4,3,0,0)) = value rightInput38 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput38, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput38 rightNormal38 rightQ38 rightH38

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_38 right_normal_check_38

private theorem right_normal_good_39 : goodPolynomial .right 8 rightNormal39=true := by decide +kernel

private theorem right_normal_check_39 :

    checkZero (residual rightInput39 rightNormal39 rightQ39 rightH39 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_39 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (1,5,1,1,0)) = value rightNormal39 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (1,5,1,1,0)) = value rightInput39 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput39, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput39 rightNormal39 rightQ39 rightH39

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_39 right_normal_check_39

private theorem right_normal_good_40 : goodPolynomial .right 8 rightNormal40=true := by decide +kernel

private theorem right_normal_check_40 :

    checkZero (residual rightInput40 rightNormal40 rightQ40 rightH40 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_40 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (1,7,0,0,0)) = value rightNormal40 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (1,7,0,0,0)) = value rightInput40 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput40, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput40 rightNormal40 rightQ40 rightH40

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_40 right_normal_check_40

private theorem right_normal_good_41 : goodPolynomial .right 8 rightNormal41=true := by decide +kernel

private theorem right_normal_check_41 :

    checkZero (residual rightInput41 rightNormal41 rightQ41 rightH41 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_41 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (1,0,2,3,1)) = value rightNormal41 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (1,0,2,3,1)) = value rightInput41 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput41, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput41 rightNormal41 rightQ41 rightH41

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_41 right_normal_check_41

private theorem right_normal_good_42 : goodPolynomial .right 8 rightNormal42=true := by decide +kernel

private theorem right_normal_check_42 :

    checkZero (residual rightInput42 rightNormal42 rightQ42 rightH42 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_42 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (1,0,5,0,1)) = value rightNormal42 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (1,0,5,0,1)) = value rightInput42 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput42, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput42 rightNormal42 rightQ42 rightH42

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_42 right_normal_check_42

private theorem right_normal_good_43 : goodPolynomial .right 8 rightNormal43=true := by decide +kernel

private theorem right_normal_check_43 :

    checkZero (residual rightInput43 rightNormal43 rightQ43 rightH43 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_43 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (1,1,0,2,2)) = value rightNormal43 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (1,1,0,2,2)) = value rightInput43 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput43, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput43 rightNormal43 rightQ43 rightH43

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_43 right_normal_check_43

private theorem right_normal_good_44 : goodPolynomial .right 8 rightNormal44=true := by decide +kernel

private theorem right_normal_check_44 :

    checkZero (residual rightInput44 rightNormal44 rightQ44 rightH44 rightQuadric rightCubic)=true := by

  decide +kernel

theorem right_column_44 [Nontrivial R] :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (2,0,0,6,0)) = value rightNormal44 := by

  have hinput : substitution .right (57 : R) (sourceMonomial (2,0,0,6,0)) = value rightInput44 := by

    have hc : CharP (CurvePoly R) 109 := inferInstance

    simp only [sourceMonomial, map_mul, map_pow, substitution_X, restrictionValues, rightInput44, value, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      curveVariables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg]

    apply sub_eq_zero.mp

    ring_nf <;> reduce_mod_char!

  rw [restrictionNormal_apply,hinput]

  exact checked_normal .right 57 33 8 rightInput44 rightNormal44 rightQ44 rightH44

    rightQuadric rightCubic right_quadric_value right_cubic_value

    right_normal_good_44 right_normal_check_44

theorem right_columns [Nontrivial R] (j : Fin 45) :

    restrictionNormal .right (57 : R) 33 (sourceMonomial (rightSources j)) = value (rightNormals j) := by

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

  · exact right_column_23

  · exact right_column_24

  · exact right_column_25

  · exact right_column_26

  · exact right_column_27

  · exact right_column_28

  · exact right_column_29

  · exact right_column_30

  · exact right_column_31

  · exact right_column_32

  · exact right_column_33

  · exact right_column_34

  · exact right_column_35

  · exact right_column_36

  · exact right_column_37

  · exact right_column_38

  · exact right_column_39

  · exact right_column_40

  · exact right_column_41

  · exact right_column_42

  · exact right_column_43

  · exact right_column_44

private theorem right_coefficient_row_0 : ∀ j : Fin 45,

    coefficient (rightRows 0) (rightNormals j) = (rightMinorRows 0).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_1 : ∀ j : Fin 45,

    coefficient (rightRows 1) (rightNormals j) = (rightMinorRows 1).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_2 : ∀ j : Fin 45,

    coefficient (rightRows 2) (rightNormals j) = (rightMinorRows 2).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_3 : ∀ j : Fin 45,

    coefficient (rightRows 3) (rightNormals j) = (rightMinorRows 3).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_4 : ∀ j : Fin 45,

    coefficient (rightRows 4) (rightNormals j) = (rightMinorRows 4).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_5 : ∀ j : Fin 45,

    coefficient (rightRows 5) (rightNormals j) = (rightMinorRows 5).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_6 : ∀ j : Fin 45,

    coefficient (rightRows 6) (rightNormals j) = (rightMinorRows 6).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_7 : ∀ j : Fin 45,

    coefficient (rightRows 7) (rightNormals j) = (rightMinorRows 7).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_8 : ∀ j : Fin 45,

    coefficient (rightRows 8) (rightNormals j) = (rightMinorRows 8).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_9 : ∀ j : Fin 45,

    coefficient (rightRows 9) (rightNormals j) = (rightMinorRows 9).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_10 : ∀ j : Fin 45,

    coefficient (rightRows 10) (rightNormals j) = (rightMinorRows 10).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_11 : ∀ j : Fin 45,

    coefficient (rightRows 11) (rightNormals j) = (rightMinorRows 11).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_12 : ∀ j : Fin 45,

    coefficient (rightRows 12) (rightNormals j) = (rightMinorRows 12).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_13 : ∀ j : Fin 45,

    coefficient (rightRows 13) (rightNormals j) = (rightMinorRows 13).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_14 : ∀ j : Fin 45,

    coefficient (rightRows 14) (rightNormals j) = (rightMinorRows 14).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_15 : ∀ j : Fin 45,

    coefficient (rightRows 15) (rightNormals j) = (rightMinorRows 15).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_16 : ∀ j : Fin 45,

    coefficient (rightRows 16) (rightNormals j) = (rightMinorRows 16).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_17 : ∀ j : Fin 45,

    coefficient (rightRows 17) (rightNormals j) = (rightMinorRows 17).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_18 : ∀ j : Fin 45,

    coefficient (rightRows 18) (rightNormals j) = (rightMinorRows 18).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_19 : ∀ j : Fin 45,

    coefficient (rightRows 19) (rightNormals j) = (rightMinorRows 19).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_20 : ∀ j : Fin 45,

    coefficient (rightRows 20) (rightNormals j) = (rightMinorRows 20).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_21 : ∀ j : Fin 45,

    coefficient (rightRows 21) (rightNormals j) = (rightMinorRows 21).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_22 : ∀ j : Fin 45,

    coefficient (rightRows 22) (rightNormals j) = (rightMinorRows 22).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_23 : ∀ j : Fin 45,

    coefficient (rightRows 23) (rightNormals j) = (rightMinorRows 23).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_24 : ∀ j : Fin 45,

    coefficient (rightRows 24) (rightNormals j) = (rightMinorRows 24).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_25 : ∀ j : Fin 45,

    coefficient (rightRows 25) (rightNormals j) = (rightMinorRows 25).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_26 : ∀ j : Fin 45,

    coefficient (rightRows 26) (rightNormals j) = (rightMinorRows 26).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_27 : ∀ j : Fin 45,

    coefficient (rightRows 27) (rightNormals j) = (rightMinorRows 27).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_28 : ∀ j : Fin 45,

    coefficient (rightRows 28) (rightNormals j) = (rightMinorRows 28).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_29 : ∀ j : Fin 45,

    coefficient (rightRows 29) (rightNormals j) = (rightMinorRows 29).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_30 : ∀ j : Fin 45,

    coefficient (rightRows 30) (rightNormals j) = (rightMinorRows 30).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_31 : ∀ j : Fin 45,

    coefficient (rightRows 31) (rightNormals j) = (rightMinorRows 31).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_32 : ∀ j : Fin 45,

    coefficient (rightRows 32) (rightNormals j) = (rightMinorRows 32).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_33 : ∀ j : Fin 45,

    coefficient (rightRows 33) (rightNormals j) = (rightMinorRows 33).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_34 : ∀ j : Fin 45,

    coefficient (rightRows 34) (rightNormals j) = (rightMinorRows 34).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_35 : ∀ j : Fin 45,

    coefficient (rightRows 35) (rightNormals j) = (rightMinorRows 35).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_36 : ∀ j : Fin 45,

    coefficient (rightRows 36) (rightNormals j) = (rightMinorRows 36).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_37 : ∀ j : Fin 45,

    coefficient (rightRows 37) (rightNormals j) = (rightMinorRows 37).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_38 : ∀ j : Fin 45,

    coefficient (rightRows 38) (rightNormals j) = (rightMinorRows 38).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_39 : ∀ j : Fin 45,

    coefficient (rightRows 39) (rightNormals j) = (rightMinorRows 39).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_40 : ∀ j : Fin 45,

    coefficient (rightRows 40) (rightNormals j) = (rightMinorRows 40).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_41 : ∀ j : Fin 45,

    coefficient (rightRows 41) (rightNormals j) = (rightMinorRows 41).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_42 : ∀ j : Fin 45,

    coefficient (rightRows 42) (rightNormals j) = (rightMinorRows 42).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_43 : ∀ j : Fin 45,

    coefficient (rightRows 43) (rightNormals j) = (rightMinorRows 43).getD j.val 0 := by

  decide +kernel

private theorem right_coefficient_row_44 : ∀ j : Fin 45,

    coefficient (rightRows 44) (rightNormals j) = (rightMinorRows 44).getD j.val 0 := by

  decide +kernel

theorem right_coefficient_table (i j : Fin 45) :

    coefficient (rightRows i) (rightNormals j) = (rightMinorRows i).getD j.val 0 := by

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

  · exact right_coefficient_row_23 j

  · exact right_coefficient_row_24 j

  · exact right_coefficient_row_25 j

  · exact right_coefficient_row_26 j

  · exact right_coefficient_row_27 j

  · exact right_coefficient_row_28 j

  · exact right_coefficient_row_29 j

  · exact right_coefficient_row_30 j

  · exact right_coefficient_row_31 j

  · exact right_coefficient_row_32 j

  · exact right_coefficient_row_33 j

  · exact right_coefficient_row_34 j

  · exact right_coefficient_row_35 j

  · exact right_coefficient_row_36 j

  · exact right_coefficient_row_37 j

  · exact right_coefficient_row_38 j

  · exact right_coefficient_row_39 j

  · exact right_coefficient_row_40 j

  · exact right_coefficient_row_41 j

  · exact right_coefficient_row_42 j

  · exact right_coefficient_row_43 j

  · exact right_coefficient_row_44 j

theorem right_matrix_coefficients [Nontrivial R] (i j : Fin 45) :

    matrixCoefficient .right (57 : R) 33 (rightRows i) (rightSources j) =

      ((rightMinorRows i).getD j.val 0 : R) := by

  rw [matrixCoefficient,right_columns,value_coefficient,right_coefficient_table]

private theorem right_inverse_row_0 : ∀ j : Fin 45,

    dotMod (rightMinorRows 0) (rightInverseColumns j) = if (0 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_1 : ∀ j : Fin 45,

    dotMod (rightMinorRows 1) (rightInverseColumns j) = if (1 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_2 : ∀ j : Fin 45,

    dotMod (rightMinorRows 2) (rightInverseColumns j) = if (2 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_3 : ∀ j : Fin 45,

    dotMod (rightMinorRows 3) (rightInverseColumns j) = if (3 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_4 : ∀ j : Fin 45,

    dotMod (rightMinorRows 4) (rightInverseColumns j) = if (4 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_5 : ∀ j : Fin 45,

    dotMod (rightMinorRows 5) (rightInverseColumns j) = if (5 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_6 : ∀ j : Fin 45,

    dotMod (rightMinorRows 6) (rightInverseColumns j) = if (6 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_7 : ∀ j : Fin 45,

    dotMod (rightMinorRows 7) (rightInverseColumns j) = if (7 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_8 : ∀ j : Fin 45,

    dotMod (rightMinorRows 8) (rightInverseColumns j) = if (8 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_9 : ∀ j : Fin 45,

    dotMod (rightMinorRows 9) (rightInverseColumns j) = if (9 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_10 : ∀ j : Fin 45,

    dotMod (rightMinorRows 10) (rightInverseColumns j) = if (10 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_11 : ∀ j : Fin 45,

    dotMod (rightMinorRows 11) (rightInverseColumns j) = if (11 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_12 : ∀ j : Fin 45,

    dotMod (rightMinorRows 12) (rightInverseColumns j) = if (12 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_13 : ∀ j : Fin 45,

    dotMod (rightMinorRows 13) (rightInverseColumns j) = if (13 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_14 : ∀ j : Fin 45,

    dotMod (rightMinorRows 14) (rightInverseColumns j) = if (14 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_15 : ∀ j : Fin 45,

    dotMod (rightMinorRows 15) (rightInverseColumns j) = if (15 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_16 : ∀ j : Fin 45,

    dotMod (rightMinorRows 16) (rightInverseColumns j) = if (16 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_17 : ∀ j : Fin 45,

    dotMod (rightMinorRows 17) (rightInverseColumns j) = if (17 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_18 : ∀ j : Fin 45,

    dotMod (rightMinorRows 18) (rightInverseColumns j) = if (18 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_19 : ∀ j : Fin 45,

    dotMod (rightMinorRows 19) (rightInverseColumns j) = if (19 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_20 : ∀ j : Fin 45,

    dotMod (rightMinorRows 20) (rightInverseColumns j) = if (20 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_21 : ∀ j : Fin 45,

    dotMod (rightMinorRows 21) (rightInverseColumns j) = if (21 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_22 : ∀ j : Fin 45,

    dotMod (rightMinorRows 22) (rightInverseColumns j) = if (22 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_23 : ∀ j : Fin 45,

    dotMod (rightMinorRows 23) (rightInverseColumns j) = if (23 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_24 : ∀ j : Fin 45,

    dotMod (rightMinorRows 24) (rightInverseColumns j) = if (24 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_25 : ∀ j : Fin 45,

    dotMod (rightMinorRows 25) (rightInverseColumns j) = if (25 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_26 : ∀ j : Fin 45,

    dotMod (rightMinorRows 26) (rightInverseColumns j) = if (26 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_27 : ∀ j : Fin 45,

    dotMod (rightMinorRows 27) (rightInverseColumns j) = if (27 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_28 : ∀ j : Fin 45,

    dotMod (rightMinorRows 28) (rightInverseColumns j) = if (28 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_29 : ∀ j : Fin 45,

    dotMod (rightMinorRows 29) (rightInverseColumns j) = if (29 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_30 : ∀ j : Fin 45,

    dotMod (rightMinorRows 30) (rightInverseColumns j) = if (30 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_31 : ∀ j : Fin 45,

    dotMod (rightMinorRows 31) (rightInverseColumns j) = if (31 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_32 : ∀ j : Fin 45,

    dotMod (rightMinorRows 32) (rightInverseColumns j) = if (32 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_33 : ∀ j : Fin 45,

    dotMod (rightMinorRows 33) (rightInverseColumns j) = if (33 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_34 : ∀ j : Fin 45,

    dotMod (rightMinorRows 34) (rightInverseColumns j) = if (34 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_35 : ∀ j : Fin 45,

    dotMod (rightMinorRows 35) (rightInverseColumns j) = if (35 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_36 : ∀ j : Fin 45,

    dotMod (rightMinorRows 36) (rightInverseColumns j) = if (36 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_37 : ∀ j : Fin 45,

    dotMod (rightMinorRows 37) (rightInverseColumns j) = if (37 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_38 : ∀ j : Fin 45,

    dotMod (rightMinorRows 38) (rightInverseColumns j) = if (38 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_39 : ∀ j : Fin 45,

    dotMod (rightMinorRows 39) (rightInverseColumns j) = if (39 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_40 : ∀ j : Fin 45,

    dotMod (rightMinorRows 40) (rightInverseColumns j) = if (40 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_41 : ∀ j : Fin 45,

    dotMod (rightMinorRows 41) (rightInverseColumns j) = if (41 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_42 : ∀ j : Fin 45,

    dotMod (rightMinorRows 42) (rightInverseColumns j) = if (42 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_43 : ∀ j : Fin 45,

    dotMod (rightMinorRows 43) (rightInverseColumns j) = if (43 : Fin 45)=j then 1 else 0 := by

  decide +kernel

private theorem right_inverse_row_44 : ∀ j : Fin 45,

    dotMod (rightMinorRows 44) (rightInverseColumns j) = if (44 : Fin 45)=j then 1 else 0 := by

  decide +kernel

theorem right_inverse_checks (i j : Fin 45) :

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

  · exact right_inverse_row_23 j

  · exact right_inverse_row_24 j

  · exact right_inverse_row_25 j

  · exact right_inverse_row_26 j

  · exact right_inverse_row_27 j

  · exact right_inverse_row_28 j

  · exact right_inverse_row_29 j

  · exact right_inverse_row_30 j

  · exact right_inverse_row_31 j

  · exact right_inverse_row_32 j

  · exact right_inverse_row_33 j

  · exact right_inverse_row_34 j

  · exact right_inverse_row_35 j

  · exact right_inverse_row_36 j

  · exact right_inverse_row_37 j

  · exact right_inverse_row_38 j

  · exact right_inverse_row_39 j

  · exact right_inverse_row_40 j

  · exact right_inverse_row_41 j

  · exact right_inverse_row_42 j

  · exact right_inverse_row_43 j

  · exact right_inverse_row_44 j

theorem right_minor_det_ne_zero [Nontrivial R] :

    Matrix.det (fun i j : Fin 45 => matrixCoefficient .right (57 : R) 33 (rightRows i) (rightSources j)) ≠ 0 := by

  have hm : (fun i j : Fin 45 => matrixCoefficient .right (57 : R) 33 (rightRows i) (rightSources j)) =

      matrixOfRows rightMinorRows := by ext i j; exact right_matrix_coefficients i j

  rw [hm]

  apply determinant_ne_zero_of_dot_checks rightMinorRows rightInverseColumns

  · decide +kernel

  · decide +kernel

  · exact right_inverse_checks

end

end CycleQ2CurveRestrictionModularChecks

#print axioms CycleQ2CurveRestrictionModularChecks.right_minor_det_ne_zero
end


