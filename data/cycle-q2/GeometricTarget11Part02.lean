import Proposal.GeometricTarget11Part01

/-! Continuation of GeometricTarget11.lean; complete source components and declarations. -/

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

end
end CycleQ2CurveRestrictionModularChecks
end

