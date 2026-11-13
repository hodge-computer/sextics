import Proposal.Workspace
import Proposal.GeometricTarget

/-! Source partition of Assembly.lean. See solution.md for verification status. -/

set_option Elab.async false

/- Preserved original module body. -/
section
/-!
Conditional assembly for the unchanged cycle-q2 target.
This module contains no admitted existence claim. The large compiled-current
transport is not formalized here; the input below explicitly includes all
legality, grading, and normalized equation obligations.
-/

noncomputable section
namespace CycleQ2Assembly
open MvPolynomial HodgeComputer CycleQ2Workspace

/-- A legal homogeneous rational solution, represented by common-denominator
polynomials and the two normalized equations. No denominator degree or support
is fixed, and the quotient polynomial is unrestricted. -/
structure NormalizedRationalSolution where
  degree : ℕ
  denominator : Poly
  numerators : Fin 6 → Poly
  quotient : Poly
  denominator_ne_zero : denominator ≠ 0
  denominator_homogeneous : denominator.IsHomogeneous degree
  numerator_homogeneous : ∀ i, (numerators i).IsHomogeneous (degree + 7)
  denominator_legal : IsRelPrime originalF denominator
  first_normal :
    (2 : Poly) * HodgeTestbed.directional originalF numerators =
      originalA * denominator
  second_normal :
    HodgeTestbed.divergenceNumerator denominator numerators =
      originalF ^ 2 * quotient

/-- A normalized solution yields the exact, unchanged protected existential goal.
This theorem proves the assembly only; it does not produce the input solution. -/
theorem certificate_of_normalized_solution (s : NormalizedRationalSolution) :
    OriginalGoal := by
  change HasCertificate originalF 2 originalA
  apply HodgeComputer.Verify.hasCertificate (d := 6)
    (D := s.denominator) (N := s.numerators) (Q := s.quotient)
  have hdegree : s.denominator.totalDegree = s.degree :=
    s.denominator_homogeneous.totalDegree s.denominator_ne_zero
  refine {
    hypersurface_ne_zero := originalF_ne_zero
    hypersurface_homogeneous := originalF_homogeneous
    source_homogeneous := ?_
    denominator_ne_zero := s.denominator_ne_zero
    denominator_homogeneous := ?_
    numerator_homogeneous := ?_
    denominator_legal := s.denominator_legal
    identity := ?_
  }
  · simpa using HodgeComputer.Homogeneous.of_isHomogeneous originalA_homogeneous
  · rw [hdegree]
    exact s.denominator_homogeneous
  · intro i
    rw [hdegree]
    convert HodgeComputer.Homogeneous.of_isHomogeneous (s.numerator_homogeneous i) using 1 <;>
      omega
  · simpa using
      (HodgeComputer.normalized_identity (q := 2) s.first_normal s.second_normal)

/-- Exact remainder-repair identity for a chosen common denominator.
A genuine correction must satisfy hcorrection; this theorem does not assert it.
All numerator and denominator derivatives are retained by fixedOperator. -/
theorem close_partial_identity
    (F A D R Q S : Poly) (N M : Fin 6 → Poly)
    (hpartial : defect F A D 2 N = -(F ^ 2 * R) + F ^ 3 * Q)
    (hcorrection : fixedOperator F D M S = F ^ 2 * R) :
    defect F A D 2 (fun i => N i + M i) = F ^ 3 * (Q + S) := by
  have hadd :
      defect F A D 2 (fun i => N i + M i) =
        defect F A D 2 N + fixedOperator F D M S + F ^ 3 * S := by
    unfold defect fixedOperator
    rw [CycleQ2Workspace.directional_add,
        CycleQ2Workspace.divergenceNumerator_add]
    ring
  rw [hadd, hpartial, hcorrection]
  ring

end CycleQ2Assembly

end
end

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


/- Component: continuation_3/IncidenceJacobianNaturality.lean -/
section
/-! The literal first-order incidence system commutes with coefficient maps.
This supplies a single integral matrix whose modular and complex versions
are obtained by applying ring homomorphisms, rather than comparing unrelated
numerical matrices. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CycleQ2IncidenceJacobianNaturality

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations CycleQ2IncidenceFirstOrder CycleQ2IncidenceJacobian
  CycleQ2IncidenceUniversalChart
  CycleQ2IncidenceCoefficientRelations

variable {R S : Type*} [CommRing R] [CommRing S]

theorem map_smoothH (φ : R →+* S) (ι : R) :
    map φ (smoothH ι) = smoothH (φ ι) := by
  simp [smoothH, smoothA, smoothB]

theorem map_smoothK (φ : R →+* S) (ι : R) :
    map φ (smoothK ι) = smoothK (φ ι) := by
  simp [smoothK, smoothA, smoothB]

theorem map_seedG (φ : R →+* S) (r : R) :
    map φ (seedG r) = seedG (φ r) := by
  simp [seedG, CycleQ2SegreSeed.seedG_expanded]

theorem map_smoothF (φ : R →+* S) (r ι : R) :
    map φ (smoothF r ι) = smoothF (φ r) (φ ι) := by
  simp only [smoothF, map_add, map_mul, map_seedG, map_smoothH, map_smoothK]

theorem map_seedCubicCoefficients (φ : R →+* S) (ι : R) :
    φ ∘ seedCubicCoefficients ι = seedCubicCoefficients (φ ι) := by
  funext e
  simp only [Function.comp_apply, seedCubicCoefficients, ← coeff_map, map_smoothH]

theorem map_seedSexticCoefficients (φ : R →+* S) (r ι : R) :
    φ ∘ seedSexticCoefficients r ι = seedSexticCoefficients (φ r) (φ ι) := by
  funext e
  simp only [Function.comp_apply, seedSexticCoefficients, ← coeff_map, map_smoothF]

theorem seedG_ne_zero [Nontrivial R] (r : R) : seedG r ≠ 0 := by
  intro hz
  have h := congrArg (eval (fun j : Fin 5 => if j = 4 then (1 : R) else 0)) hz
  norm_num [seedG, CycleQ2SegreSeed.seedG_expanded] at h
  norm_num [Fin.ext_iff] at h

theorem map_rawCofactorQuotient [IsDomain S] (φ : R →+* S) (r : R) (i j : Fin 3) :
    map φ (rawCofactorQuotient r i j) = rawCofactorQuotient (φ r) i j := by
  apply mul_left_cancel₀ (seedG_ne_zero (φ r))
  have h := congrArg (map φ) (rawSeedMatrix_cofactor r i j)
  rw [map_cofactors, map_rawSeedMatrix, map_mul, map_seedG,
    rawSeedMatrix_cofactor] at h
  exact h.symm

theorem map_cofactorDifferential (φ : R →+* S)
    (M N : Matrix (Fin 3) (Fin 3) (Poly R)) (i j : Fin 3) :
    map φ (cofactorDifferential M N i j) =
      cofactorDifferential ((map φ).mapMatrix M) ((map φ).mapMatrix N) i j := by
  simp only [cofactorDifferential, Matrix.sub_apply, map_sub, map_cofactors, map_add]

theorem map_fullFirstOrderResidual [IsDomain S] (φ : R →+* S) (r ι : R)
    (H J : Poly R) (N : Matrix (Fin 3) (Fin 3) (Poly R)) (i j : Fin 3) :
    map φ (fullFirstOrderResidual r ι H J N i j) =
      fullFirstOrderResidual (φ r) (φ ι) (map φ H) (map φ J)
        ((map φ).mapMatrix N) i j := by
  simp only [fullFirstOrderResidual, firstOrderResidual, map_sub, map_add, map_mul,
    map_cofactorDifferential, map_rawSeedMatrix, map_smoothK, map_rawCofactorQuotient]

theorem linearizedEquations_map [Nontrivial R] [IsDomain S]
    (φ : R →+* S) (r ι : R)
    (η : FullInvariantIndex 3 → R) (ζ : FullInvariantIndex 6 → R)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) (q : EquationIndex) :
    φ (linearizedEquations r ι η ζ δ q) =
      linearizedEquations (φ r) (φ ι) (φ ∘ η) (φ ∘ ζ)
        (fun i j e => φ (δ i j e)) q := by
  unfold linearizedEquations
  rw [← coeff_map, fullRemainder_map, map_fullFirstOrderResidual,
    map_fullInvariantPolynomial, map_fullInvariantPolynomial, map_perturbation]
  simp only [map_seedCubicCoefficients, map_seedSexticCoefficients]

def linearizedMatrix [Nontrivial R] (r ι : R) : Matrix EquationIndex ParameterIndex R := by
  classical
  exact fun q j => linearizedEquations r ι
    (fun e => if j = Sum.inl e then 1 else 0)
    (fun e => if j = Sum.inr (Sum.inl e) then 1 else 0)
    (fun i k e => if j = Sum.inr (Sum.inr ((i, k), e)) then 1 else 0) q

theorem linearizedMatrix_map [Nontrivial R] [IsDomain S]
    (φ : R →+* S) (r ι : R) :
    (linearizedMatrix r ι).map φ = linearizedMatrix (φ r) (φ ι) := by
  classical
  ext q j
  simp only [Matrix.map_apply, linearizedMatrix, linearizedEquations_map]
  congr 1 <;> funext <;> split_ifs <;> simp_all

theorem segreRelations_map (φ : R →+* S) (M : Matrix (Fin 3) (Fin 3) R)
    (k : Fin 16) (j : Fin 9) :
    φ (CycleQ2SegreRelations.relations M k j) =
      CycleQ2SegreRelations.relations (φ.mapMatrix M) k j := by
  fin_cases k <;> fin_cases j <;>
    simp [CycleQ2SegreRelations.relations, RingHom.mapMatrix_apply]

theorem coefficientRelations_map [Nontrivial R] [Nontrivial S] (φ : R →+* S)
    (hc : FullInvariantIndex 3 → R) (Fc : FullInvariantIndex 6 → R)
    (hu : IsUnit (hc fullCubicLeadingIndex)) (Fu : IsUnit (Fc fullSexticLeadingIndex))
    (M : Matrix (Fin 3) (Fin 3) (Poly R)) (row : RelationIndex) (col : ColumnIndex) :
    φ (coefficientRelations hc Fc hu Fu M row col) =
      coefficientRelations (φ ∘ hc) (φ ∘ Fc) (hu.map φ) (Fu.map φ)
        ((map φ).mapMatrix M) row col := by
  unfold coefficientRelations
  rw [← coeff_map, fullRemainder_map, map_mul, segreRelations_map, map_monomial, map_one]

def seedCoefficientRelations [Nontrivial R] (r ι : R) : Matrix RelationIndex ColumnIndex R :=
  coefficientRelations (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
    (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι) (rawSeedMatrix r)

theorem seedCoefficientRelations_map [Nontrivial R] [Nontrivial S]
    (φ : R →+* S) (r ι : R) :
    (seedCoefficientRelations r ι).map φ = seedCoefficientRelations (φ r) (φ ι) := by
  ext row col
  simp only [Matrix.map_apply, seedCoefficientRelations, coefficientRelations_map,
    map_rawSeedMatrix, map_seedCubicCoefficients, map_seedSexticCoefficients]

end CycleQ2IncidenceJacobianNaturality

#print axioms CycleQ2IncidenceJacobianNaturality.linearizedEquations_map
#print axioms CycleQ2IncidenceJacobianNaturality.linearizedMatrix_map
#print axioms CycleQ2IncidenceJacobianNaturality.seedCoefficientRelations_map
end
end


/- Component: continuation_3/IncidencePolynomialRelations.lean -/
section
/-!
# Polynomial equations and relations for the actual incidence family

A single power of the two leading coefficients clears both the entire
equation vector and the entire coefficient-relation matrix.  Injectivity
of the actual localization then proves the polynomial relation identity
before evaluation.  Thus no relation is inferred from a pointwise seed
calculation.  At the literal seed the clearing factor is one.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace CycleQ2UniformDenominators

open scoped BigOperators
open Matrix

variable {P L : Type*} [CommRing P] [CommRing L] [Algebra P L]
variable (a : P) [IsLocalization.Away a L]

theorem exists_uniform_numerators {ι : Type*} [Finite ι] (v : ι → L) :
    ∃ n : ℕ, ∃ p : ι → P, ∀ i,
      algebraMap P L (p i) = algebraMap P L (a ^ n) * v i := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers a) v
  obtain ⟨n, hn⟩ := d.property
  have hd' : ∀ i, ∃ p : P, algebraMap P L p = (d.val : P) • v i := hd
  choose p hp using hd'
  refine ⟨n, p, fun i => ?_⟩
  simpa only [Algebra.smul_def, hn] using hp i

/-- Equations and all their linear relations can be cleared simultaneously
without losing the relation identity in the original polynomial ring. -/
theorem exists_polynomial_relations [IsDomain P] (ha : a ≠ 0)
    {ι κ : Type*} [Fintype ι] [Finite κ]
    (e : ι → L) (B : Matrix κ ι L) (hB : B *ᵥ e = 0) :
    ∃ n : ℕ, ∃ p : ι → P, ∃ A : Matrix κ ι P,
      (∀ i, algebraMap P L (p i) = algebraMap P L (a ^ n) * e i) ∧
      (∀ k i, algebraMap P L (A k i) = algebraMap P L (a ^ n) * B k i) ∧
      A *ᵥ p = 0 := by
  classical
  obtain ⟨n, v, hv⟩ := exists_uniform_numerators a
    (Sum.elim e (fun q : κ × ι => B q.1 q.2))
  let p : ι → P := fun i => v (Sum.inl i)
  let A : Matrix κ ι P := fun k i => v (Sum.inr (k, i))
  have hp (i : ι) : algebraMap P L (p i) = algebraMap P L (a ^ n) * e i := hv (.inl i)
  have hA (k : κ) (i : ι) :
      algebraMap P L (A k i) = algebraMap P L (a ^ n) * B k i := hv (.inr (k, i))
  refine ⟨n, p, A, hp, hA, ?_⟩
  funext k
  apply IsLocalization.injective L (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  change algebraMap P L (∑ i, A k i * p i) = algebraMap P L 0
  simp only [map_sum, map_mul, map_zero, hp, hA]
  have hk : (∑ i, B k i * e i) = 0 := congrFun hB k
  calc
    (∑ i, (algebraMap P L (a ^ n) * B k i) *
        (algebraMap P L (a ^ n) * e i)) =
      (algebraMap P L (a ^ n)) ^ 2 * ∑ i, B k i * e i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ = 0 := by rw [hk, mul_zero]

end CycleQ2UniformDenominators

namespace CycleQ2IncidencePolynomialRelations

open Matrix MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations CycleQ2IncidenceUniversalChart
  CycleQ2IncidenceCoefficientRelations

variable (R : Type*) [CommRing R] [IsDomain R]

def universalRelations (r : R) : Matrix RelationIndex ColumnIndex (ParameterRing R) :=
  coefficientRelations (cubicCoefficient R) (sexticCoefficient R)
    (leading_coefficients_units R).1 (leading_coefficients_units R).2
    (incidenceMatrix (algebraMap R (ParameterRing R) r) (matrixCoefficient R))

def orderedEquations (r : R) : ColumnIndex → ParameterRing R :=
  fun q => equations R r (columnEquiv q)

theorem universal_relation_identity (r : R) :
    universalRelations R r *ᵥ orderedEquations R r = 0 :=
  coefficientRelations_incidenceEquations (cubicCoefficient R) (sexticCoefficient R)
    (leading_coefficients_units R).1 (leading_coefficients_units R).2
    (algebraMap R (ParameterRing R) r) (matrixCoefficient R)

structure Presentation (r : R) where
  exponent : ℕ
  equation : ColumnIndex → ParameterPolynomial R
  relation : Matrix RelationIndex ColumnIndex (ParameterPolynomial R)
  equation_spec : ∀ q,
    algebraMap (ParameterPolynomial R) (ParameterRing R) (equation q) =
      algebraMap (ParameterPolynomial R) (ParameterRing R) (leadingProduct R ^ exponent) *
        orderedEquations R r q
  relation_spec : ∀ k q,
    algebraMap (ParameterPolynomial R) (ParameterRing R) (relation k q) =
      algebraMap (ParameterPolynomial R) (ParameterRing R) (leadingProduct R ^ exponent) *
        universalRelations R r k q
  relation_identity : relation *ᵥ equation = 0

theorem presentation_nonempty (r : R) : Nonempty (Presentation R r) := by
  obtain ⟨n, p, A, hp, hA, hrel⟩ :=
    CycleQ2UniformDenominators.exists_polynomial_relations (leadingProduct R)
      (leadingProduct_ne_zero R) (orderedEquations R r) (universalRelations R r)
      (universal_relation_identity R r)
  exact ⟨⟨n, p, A, hp, hA, hrel⟩⟩

def presentation (r : R) : Presentation R r := (presentation_nonempty R r).some

section Specialization

variable {R} {S : Type*} [CommRing S] [Nontrivial S] [Algebra R S]

theorem equation_specialization
    (hcoeff : FullInvariantIndex 3 → S) (Fcoeff : FullInvariantIndex 6 → S)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S) (r : R) (q : ColumnIndex) :
    polynomialSpecialization hcoeff Fcoeff δ ((presentation R r).equation q) =
      (hcoeff fullCubicLeadingIndex * Fcoeff fullSexticLeadingIndex) ^
          (presentation R r).exponent *
        incidenceEquations hcoeff Fcoeff hu Fu (algebraMap R S r) δ (columnEquiv q) := by
  have h := congrArg (specialization hcoeff Fcoeff hu Fu δ)
    ((presentation R r).equation_spec q)
  simpa only [orderedEquations, map_mul, specialization_polynomial, map_pow,
    polynomialSpecialization_leadingProduct, specialization_equations] using h

theorem equations_zero_iff
    (hcoeff : FullInvariantIndex 3 → S) (Fcoeff : FullInvariantIndex 6 → S)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S) (r : R) :
    (∀ q, polynomialSpecialization hcoeff Fcoeff δ ((presentation R r).equation q) = 0) ↔
      ∀ i j, CycleQ2SegreLocal.cofactors (incidenceMatrix (algebraMap R S r) δ) i j ∈
        equationsIdeal (fullInvariantPolynomial 3 hcoeff) (fullInvariantPolynomial 6 Fcoeff) := by
  rw [← incidenceEquations_zero_iff hcoeff Fcoeff hu Fu (algebraMap R S r) δ]
  have hz (q : ColumnIndex) :
      polynomialSpecialization hcoeff Fcoeff δ ((presentation R r).equation q) = 0 ↔
        incidenceEquations hcoeff Fcoeff hu Fu (algebraMap R S r) δ (columnEquiv q) = 0 := by
    rw [equation_specialization hcoeff Fcoeff hu Fu δ r q]
    exact ((hu.mul Fu).pow _).mul_right_eq_zero
  simp only [hz]
  exact columnEquiv.forall_congr (fun _ => Iff.rfl)

end Specialization

theorem seed_equations_zero (r ι : R) (q : ColumnIndex) :
    polynomialSpecialization (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
      (fun _ _ _ => 0) ((presentation R r).equation q) = 0 := by
  rw [equation_specialization _ _ (seedCubicCoefficients_unit ι)
    (seedSexticCoefficients_unit r ι)]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, smoothSeed_equations_zero, mul_zero]

theorem seed_leadingProduct (r ι : R) :
    seedSpecialization R r ι
      (algebraMap (ParameterPolynomial R) (ParameterRing R) (leadingProduct R)) = 1 := by
  rw [seedSpecialization, specialization_polynomial,
    polynomialSpecialization_leadingProduct]
  simp only [seedCubicCoefficients, seedSexticCoefficients,
    fullCubicLeadingIndex_exponent, fullSexticLeadingIndex_exponent,
    smoothH_leading_coefficient, smoothF_leading_coefficient, one_mul]

/-- Every cleared relation has exactly the original localized value at the
literal seed, because both of its leading coefficients are one. -/
theorem seed_relation_value (r ι : R) (k : RelationIndex) (q : ColumnIndex) :
    polynomialSpecialization (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
      (fun _ _ _ => 0) ((presentation R r).relation k q) =
        seedSpecialization R r ι (universalRelations R r k q) := by
  have h := congrArg (seedSpecialization R r ι) ((presentation R r).relation_spec k q)
  rw [map_mul, map_pow, map_pow, seed_leadingProduct, one_pow, one_mul] at h
  simpa only [seedSpecialization, specialization_polynomial] using h

section Derivative

variable {S : Type*} [CommRing S] [Algebra (ParameterRing R) S]

theorem differential_at_solution (r : R) (q : ColumnIndex)
    (D : Derivation ℤ (ParameterRing R) S)
    (hzero : algebraMap (ParameterRing R) S (orderedEquations R r q) = 0) :
    D (algebraMap (ParameterPolynomial R) (ParameterRing R)
        ((presentation R r).equation q)) =
      algebraMap (ParameterRing R) S
        (algebraMap (ParameterPolynomial R) (ParameterRing R)
          (leadingProduct R ^ (presentation R r).exponent)) *
        D (orderedEquations R r q) := by
  rw [(presentation R r).equation_spec, Derivation.leibniz]
  simp only [Algebra.smul_def, hzero, zero_mul, add_zero]

end Derivative

def seedRelationMatrix (r ι : R) : Matrix RelationIndex ColumnIndex R :=
  fun k q => polynomialSpecialization (seedCubicCoefficients ι)
    (seedSexticCoefficients r ι) (fun _ _ _ => 0) ((presentation R r).relation k q)

def seedJacobian (r ι : R) : Matrix ColumnIndex ParameterIndex R :=
  fun q j => polynomialSpecialization (seedCubicCoefficients ι)
    (seedSexticCoefficients r ι) (fun _ _ _ => 0)
      (pderiv j ((presentation R r).equation q))

/-- Differentiating the actual polynomial relation identity at the literal
smooth seed yields the genuine relation matrix times the genuine parameter
Jacobian.  No numerical rank calculation is used for this identity. -/
theorem seed_relations_jacobian (r ι : R) :
    seedRelationMatrix R r ι * seedJacobian R r ι = 0 := by
  classical
  ext k j
  let ev : ParameterPolynomial R →ₐ[R] R := polynomialSpecialization (seedCubicCoefficients ι)
    (seedSexticCoefficients r ι) (fun _ _ _ => 0)
  have h := congrArg (fun p : ParameterPolynomial R => ev (pderiv j p))
    (congrFun (presentation R r).relation_identity k)
  change ev (pderiv j (∑ q, (presentation R r).relation k q *
    (presentation R r).equation q)) = ev (pderiv j 0) at h
  have he (q : ColumnIndex) : ev ((presentation R r).equation q) = 0 :=
    seed_equations_zero R r ι q
  simpa only [seedRelationMatrix, seedJacobian, Matrix.mul_apply, Matrix.zero_apply,
    map_sum, pderiv_mul, map_add, map_mul, he, mul_zero, zero_add, map_zero] using h

end CycleQ2IncidencePolynomialRelations

#print axioms CycleQ2UniformDenominators.exists_polynomial_relations
#print axioms CycleQ2IncidencePolynomialRelations.presentation_nonempty
#print axioms CycleQ2IncidencePolynomialRelations.equations_zero_iff
#print axioms CycleQ2IncidencePolynomialRelations.seed_relation_value
#print axioms CycleQ2IncidencePolynomialRelations.differential_at_solution
#print axioms CycleQ2IncidencePolynomialRelations.seed_relations_jacobian
end
end


/- Component: continuation_3/cylinder_bridge/SeedCechMatrixBinding.lean -/
section
/-! The literal published 72-entry array is an actual normalized Čech
residue matrix.  Its selected tangent produces seven coboundaries and one
non-coboundary on the actual sparse seed curve. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace CycleQ2SeedCech
open MvPolynomial CycleQ2SeedTrace CycleQ2GeometricSeed

theorem curveK_homogeneous : k.IsHomogeneous 3 := by
  have hm (a b c d : ℕ) (hd : a+b+c+d=3) : (mon a b c d).IsHomogeneous 3 := by
    simpa only [hd] using mon_homogeneous a b c d
  rw [k_eq_monomials]
  exact (((((hm 0 0 0 3 (by omega)).add (hm 0 0 3 0 (by omega))).add
    (hm 0 1 1 1 (by omega))).add (hm 1 0 1 1 (by omega))).add
    (hm 1 2 0 0 (by omega))).add
    (((hm 0 3 0 0 (by omega)).add (hm 0 0 0 3 (by omega))).C_mul Complex.I)

theorem columnPolynomial_homogeneous (j : Fin 9) :
    (columnPolynomial j).IsHomogeneous 3 := by
  fin_cases j
  · exact mon_homogeneous 0 0 0 3
  · exact mon_homogeneous 0 0 3 0
  · exact mon_homogeneous 0 1 1 1
  · exact mon_homogeneous 0 3 0 0
  · exact mon_homogeneous 1 0 1 1
  · exact mon_homogeneous 1 2 0 0
  · exact mon_homogeneous 2 1 0 0
  · exact mon_homogeneous 3 0 0 0
  · exact (mon_homogeneous 0 0 2 1).neg

theorem rowPolynomial_homogeneous (i : Fin 8) :
    (rowPolynomial i).IsHomogeneous 6 := by
  fin_cases i
  · exact curveK_homogeneous.mul (mon_homogeneous 0 0 1 2)
  · exact curveK_homogeneous.mul (mon_homogeneous 0 1 2 0)
  · exact curveK_homogeneous.mul (mon_homogeneous 0 2 0 1)
  · exact curveK_homogeneous.mul (mon_homogeneous 1 0 2 0)
  · exact curveK_homogeneous.mul (mon_homogeneous 1 1 0 1)
  · exact curveK_homogeneous.mul (mon_homogeneous 2 0 0 1)
  · exact (curveK_homogeneous.mul (mon_homogeneous 0 0 3 0)).neg
  · exact (mon_homogeneous 0 0 3 3).neg

def actualCechTraceMatrix (r : ℂ) : Matrix (Fin 8) (Fin 9) ℂ :=
  fun i j => rowScale r i * (cechResidue r (rowPolynomial i * columnPolynomial j) 2 4 / (3*r))

theorem actualCechTraceMatrix_eq_actualSeedTraceMatrix (r : ℂ) (hr : r^3=2) :
    actualCechTraceMatrix r = actualSeedTraceMatrix r hr := by
  have hr0 : r ≠ 0 := by intro hh; simp [hh] at hr
  rw [actualSeedTraceMatrix_eq_polynomial]
  ext i j
  unfold actualCechTraceMatrix polynomialTraceMatrix
  rw [cechResidue_eq_trace r hr ((rowPolynomial_homogeneous i).mul
    (columnPolynomial_homogeneous j))]
  congr 1
  exact mul_div_cancel_left₀ _ (mul_ne_zero (by norm_num) hr0)

theorem actualCechTraceMatrix_eq_seedMatrix (r : ℂ) (hr : r^3=2) :
    actualCechTraceMatrix r = seedMatrix := by
  rw [actualCechTraceMatrix_eq_actualSeedTraceMatrix r hr,
    actualSeedTraceMatrix_eq_seedMatrix r hr]

theorem actualCechTraceMatrix_right_inverse (r : ℂ) (hr : r^3=2) :
    actualCechTraceMatrix r * seedRightInverse = 1 := by
  rw [actualCechTraceMatrix_eq_seedMatrix r hr, seed_right_inverse]

theorem actualCechTraceMatrix_tangent (r : ℂ) (hr : r^3=2) :
    (actualCechTraceMatrix r).mulVec seedTangent = tangentImage := by
  rw [actualCechTraceMatrix_eq_seedMatrix r hr, seed_tangent_image]

def projectedTangentPolynomial : Poly := ∑ j : Fin 9, C (seedTangent j) * columnPolynomial j

theorem projectedTangentPolynomial_explicit : projectedTangentPolynomial =
    C Complex.I * mon 2 1 0 0 + C (Complex.I-1) * mon 3 0 0 0 := by
  norm_num [projectedTangentPolynomial, seedTangent, columnPolynomial,
    Fin.sum_univ_succ, Matrix.head_cons, Matrix.tail_cons]

theorem projectedTangentPolynomial_homogeneous : projectedTangentPolynomial.IsHomogeneous 3 := by
  apply IsHomogeneous.sum
  intro j hj
  exact (columnPolynomial_homogeneous j).C_mul _

theorem projectedTangent_trace (r : ℂ) (hr : r^3=2) (i : Fin 8) :
    rowScale r i * traceLinear r (rowPolynomial i * projectedTangentPolynomial) = tangentImage i := by
  have hh := congrArg (fun v : Fin 8 → ℂ => v i) (actualSeedTraceMatrix_tangent r hr)
  rw [actualSeedTraceMatrix_eq_polynomial] at hh
  change (∑ j : Fin 9, (rowScale r i * traceLinear r (rowPolynomial i * columnPolynomial j)) *
    seedTangent j) = tangentImage i at hh
  calc
    _ = rowScale r i * ∑ j : Fin 9,
        seedTangent j * traceLinear r (rowPolynomial i * columnPolynomial j) := by
      congr 1
      simp only [projectedTangentPolynomial, Finset.mul_sum, map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [show rowPolynomial i * (C (seedTangent j) * columnPolynomial j) =
        C (seedTangent j) * (rowPolynomial i * columnPolynomial j) by ring,
        traceLinear_C_mul]
    _ = _ := by
      rw [Finset.mul_sum]
      convert hh using 1
      apply Finset.sum_congr rfl
      intro j hj
      ring

def selectedTangentNumerator : Poly := rowPolynomial 7 * projectedTangentPolynomial

theorem selectedTangentNumerator_homogeneous : selectedTangentNumerator.IsHomogeneous 9 :=
  (rowPolynomial_homogeneous 7).mul projectedTangentPolynomial_homogeneous

theorem selectedTangent_trace (r : ℂ) (hr : r^3=2) :
    traceLinear r selectedTangentNumerator = 1/3 := by
  have hh := projectedTangent_trace r hr 7
  change 6 * traceLinear r selectedTangentNumerator = 2 at hh
  linear_combination (1/6 : ℂ) * hh

theorem selectedTangent_residue (r : ℂ) (hr : r^3=2) :
    cechResidue r selectedTangentNumerator 2 4 = r := by
  rw [cechResidue_eq_trace r hr selectedTangentNumerator_homogeneous, selectedTangent_trace r hr]
  ring

/-- The specified tangent yields an actual nonzero Čech class.  This is
still not an Abel--Jacobi or cylinder-image comparison theorem. -/
theorem selectedTangent_not_boundary (r : ℂ) (hr : r^3=2) :
    ¬ CechBoundary r selectedTangentNumerator 2 4 := by
  rw [cechBoundary_iff_trace_zero r hr selectedTangentNumerator_homogeneous,
    selectedTangent_trace r hr]
  norm_num

theorem first_seven_tangent_boundaries (r : ℂ) (hr : r^3=2) (i : Fin 7) :
    CechBoundary r (rowPolynomial i.castSucc * projectedTangentPolynomial) 2 4 := by
  rw [cechBoundary_iff_trace_zero r hr
    ((rowPolynomial_homogeneous i.castSucc).mul projectedTangentPolynomial_homogeneous)]
  have hh := projectedTangent_trace r hr i.castSucc
  have hz : tangentImage i.castSucc = 0 := by fin_cases i <;> rfl
  rw [hz] at hh
  have hr0 : r ≠ 0 := by intro hh; simp [hh] at hr
  have hs : rowScale r i.castSucc ≠ 0 := by
    fin_cases i <;> simp [rowScale, hr0]
  exact (mul_eq_zero.mp hh).resolve_left hs

end CycleQ2SeedCech

#print axioms CycleQ2SeedCech.actualCechTraceMatrix_eq_actualSeedTraceMatrix
#print axioms CycleQ2SeedCech.selectedTangent_not_boundary
#print axioms CycleQ2SeedCech.first_seven_tangent_boundaries
end
end


/- Component: continuation_3/cylinder_bridge/SeedCechThetaFractions.lean -/
section
/-! Arbitrary denominator-clearing cochains for the actual h+θx₀³ curve. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace CycleQ2SeedCechTheta
open MvPolynomial CycleQ2SeedTrace CycleQ2CechLinearCubic
open CycleQ2SeedCech (PS LS seriesMap curveA curveB unit_pow_cancel)

def endpointResidue (r θ : ℂ) (e : Bool) : LaurentChart r θ e →+ ℂ :=
  (HahnSeries.coeff.addMonoidHom (-1 : ℤ)).comp (laurentCoefficient r θ e).toAddMonoidHom

theorem fractionResidue_eq_endpointResidue (r θ : ℂ) (e : Bool) (p : Poly) (n m : ℕ) :
    fractionResidue r θ e p n m = endpointResidue r θ e (fraction r θ e p n m) := rfl

theorem laurentEval_curveA_shared (r θ : ℂ) (e : Bool) :
    laurentEval r θ e curveA = (chartAUnit r θ e : LaurentChart r θ e) := by
  simpa only [curveA] using laurentEval_curveA r θ e

theorem endpointResidue_integral (r θ : ℂ) (e : Bool) (z : PowerChart r θ e) :
    endpointResidue r θ e (chartEmbedding r θ e z) = 0 := by
  change (laurentCoefficient r θ e (chartEmbedding r θ e z)).coeff (-1) = 0
  unfold laurentCoefficient chartEmbedding
  rw [coefficient_curveMap]
  exact PowerSeries.coeff_coe _ _ |>.trans (by norm_num)

theorem endpointResidue_x2_open (r θ : ℂ) (e : Bool) (z : PowerChart r θ e) (n : ℕ) :
    endpointResidue r θ e
      (chartEmbedding r θ e z * ((laurentX2Unit r θ e)⁻¹ : (LaurentChart r θ e)ˣ)^n) = 0 := by
  have heq : chartEmbedding r θ e z * ((laurentX2Unit r θ e)⁻¹ : (LaurentChart r θ e)ˣ)^n =
      chartEmbedding r θ e (z * ((powerX2Unit r θ e)⁻¹ : (PowerChart r θ e)ˣ)^n) := by
    simp [laurentX2Unit]
  rw [heq]
  exact endpointResidue_integral r θ e _

theorem laurentEval_curveB (r θ : ℂ) (e : Bool) :
    laurentEval r θ e curveB = (laurentX2Unit r θ e : LaurentChart r θ e) := by
  change chartEmbedding r θ e (powerEval r θ e (X 2)) =
    chartEmbedding r θ e (powerX2Unit r θ e : PowerChart r θ e)
  rw [powerEval_X_two, coe_powerX2Unit]

theorem laurentEval_zero_of_curveIdeal (r θ : ℂ) (e : Bool) {p : Poly}
    (hp : p ∈ curveIdeal r θ) : laurentEval r θ e p = 0 := by
  change chartEmbedding r θ e (powerEval r θ e p) = 0
  rw [powerEval_zero_of_curveIdeal r θ e hp, map_zero]

theorem fraction_add (r θ : ℂ) (e : Bool) (p q : Poly) (n m : ℕ) :
    fraction r θ e (p+q) n m = fraction r θ e p n m + fraction r θ e q n m := by
  simp [fraction, add_mul]

theorem fraction_sub (r θ : ℂ) (e : Bool) (p q : Poly) (n m : ℕ) :
    fraction r θ e (p-q) n m = fraction r θ e p n m - fraction r θ e q n m := by
  simp [fraction, sub_mul]

theorem cechResidue_add (r θ : ℂ) (p q : Poly) (n m : ℕ) :
    cechResidue r θ (p+q) n m = cechResidue r θ p n m + cechResidue r θ q n m := by
  simp only [cechResidue, fractionResidue_eq_endpointResidue, fraction_add, map_add]
  ring

theorem fraction_change_denominator (r θ : ℂ) (e : Bool) (p : Poly)
    (n m N M : ℕ) (hn : n ≤ N) (hm : m ≤ M) :
    fraction r θ e (p * curveA ^ (N-n) * curveB ^ (M-m)) N M =
      fraction r θ e p n m := by
  unfold fraction
  simp only [map_mul, map_pow, laurentEval_curveA_shared, laurentEval_curveB]
  calc
    _ = laurentEval r θ e p *
        (((chartAUnit r θ e : (LaurentChart r θ e)ˣ) : LaurentChart r θ e) ^ (N-n) *
          (((chartAUnit r θ e)⁻¹ : (LaurentChart r θ e)ˣ) : LaurentChart r θ e) ^ N) *
        (((laurentX2Unit r θ e : (LaurentChart r θ e)ˣ) : LaurentChart r θ e) ^ (M-m) *
          (((laurentX2Unit r θ e)⁻¹ : (LaurentChart r θ e)ˣ) : LaurentChart r θ e) ^ M) := by ring
    _ = _ := by rw [unit_pow_cancel _ n N hn, unit_pow_cancel _ m M hm]

theorem fraction_first_open_term (r θ : ℂ) (e : Bool) (p : Poly) (N M : ℕ) :
    fraction r θ e (p * curveA^N) N M = fraction r θ e p 0 M := by
  simpa using fraction_change_denominator r θ e p 0 M N M (Nat.zero_le _) le_rfl

theorem fraction_second_open_term (r θ : ℂ) (e : Bool) (p : Poly) (N M : ℕ) :
    fraction r θ e (p * curveB^M) N M = fraction r θ e p N 0 := by
  simpa using fraction_change_denominator r θ e p N 0 N M le_rfl (Nat.zero_le _)

theorem fractionResidue_x2_open (r θ : ℂ) (e : Bool) (p : Poly) (m : ℕ) :
    fractionResidue r θ e p 0 m = 0 := by
  simpa [fractionResidue_eq_endpointResidue, fraction, laurentEval] using
    endpointResidue_x2_open r θ e (powerEval r θ e p) m

theorem cechResidue_x2_open (r θ : ℂ) (p : Poly) (m : ℕ) : cechResidue r θ p 0 m = 0 := by
  simp [cechResidue, fractionResidue_x2_open]

theorem fraction_zero_of_curveIdeal (r θ : ℂ) (e : Bool) {p : Poly}
    (hp : p ∈ curveIdeal r θ) (n m : ℕ) : fraction r θ e p n m = 0 := by
  simp [fraction, laurentEval_zero_of_curveIdeal r θ e hp]

/-- Exact denominator-clearing definition of the degree-one Čech coboundaries
for the cover D₊(x₁x₃), D₊(x₂) of the projective θ-family curve.  The two numerator
degrees enforce sections of its canonical bundle O(1). -/
def CechBoundary (r θ : ℂ) (p : Poly) (n m : ℕ) : Prop :=
  ∃ N M q s, n ≤ N ∧ m ≤ M ∧ q.IsHomogeneous (M + 1) ∧
    s.IsHomogeneous (2 * N + 1) ∧
    p * curveA ^ (N - n) * curveB ^ (M - m) -
      (q * curveA ^ N + s * curveB ^ M) ∈ curveIdeal r θ

/-- Clearing arbitrary powers gives exactly the same two endpoint values as
the sum of the two single-open cochains. -/
theorem fraction_of_boundary_witness (r θ : ℂ) (e : Bool) (p q s : Poly)
    (n m N M : ℕ) (hn : n ≤ N) (hm : m ≤ M)
    (hmem : p * curveA^(N-n) * curveB^(M-m) -
      (q * curveA^N + s * curveB^M) ∈ curveIdeal r θ) :
    fraction r θ e p n m = fraction r θ e q 0 M + fraction r θ e s N 0 := by
  have hz := fraction_zero_of_curveIdeal r θ e hmem N M
  rw [fraction_sub, fraction_add, fraction_change_denominator r θ e p n m N M hn hm,
    fraction_first_open_term, fraction_second_open_term, sub_eq_zero] at hz
  exact hz

end CycleQ2SeedCechTheta
end
end


/- Component: continuation_3/cylinder_bridge/SeedCechThetaJets.lean -/
section
/-! Exact first jets in the genuine h+θx₀³ quotient chart.  These identities
compute the two nonzero entries of the smooth incidence derivative row. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace CycleQ2SeedCechTheta
open CycleQ2CechLinearCubic
open CycleQ2SeedCech (PS Jet firstJet firstJet_X_sq endpointX endpointY)

def kappa : ℂ := (1+Complex.I)/2

theorem one_sub_I_mul_kappa : (1-Complex.I)*kappa=1 := by
  norm_num [kappa, Complex.ext_iff]

def jetScalar (r θ : ℂ) (e : Bool) : ℂ →+* JetChart r θ e :=
  (jetBase r θ e).comp (firstJet.comp PowerSeries.C)

def jetT (r θ : ℂ) (e : Bool) : JetChart r θ e :=
  jetBase r θ e (firstJet PowerSeries.X)

theorem jetT_sq (r θ : ℂ) (e : Bool) : jetT r θ e ^ 2 = 0 := by
  unfold jetT
  rw [← map_pow, firstJet_X_sq, map_zero]

theorem firstJet_X_cube : firstJet (PowerSeries.X : PS)^3=0 := by
  rw [pow_succ, firstJet_X_sq, zero_mul]

theorem beta_true_firstJet (r θ : ℂ) :
    firstJet (betaCoefficient r θ true) =
      firstJet (PowerSeries.C θ) * firstJet (PowerSeries.C r) * firstJet PowerSeries.X := by
  simp [betaCoefficient, endpointX, endpointY, firstJet_X_sq]

theorem true_jet_relations (r θ : ℂ) :
    jetX0 r θ true ^ 2 = jetScalar r θ true r * jetT r θ true ∧
    jetX2 r θ true ^ 3 + (jetX0 r θ true + jetT r θ true) * jetX2 r θ true +
      jetScalar r θ true (1-Complex.I) +
      jetScalar r θ true θ * jetScalar r θ true r * jetT r θ true * jetX0 r θ true = 0 := by
  constructor
  · have hh := x0_sq (firstJet (PowerSeries.C r)) (firstJet (PowerSeries.C Complex.I))
      (firstJet (endpointX true)) (firstJet (endpointY true)) (firstJet (betaCoefficient r θ true))
    change jetX0 r θ true^2 = jetBase r θ true
      (firstJet (PowerSeries.C r)*firstJet (endpointX true)*firstJet (endpointY true)) at hh
    simpa only [endpointX, endpointY, map_one, mul_one, map_mul,
      jetScalar, RingHom.comp_apply, jetT] using hh
  · have hh := x2_cubic (firstJet (PowerSeries.C r)) (firstJet (PowerSeries.C Complex.I))
      (firstJet (endpointX true)) (firstJet (endpointY true)) (firstJet (betaCoefficient r θ true))
    change jetX2 r θ true ^ 3 +
      (jetX0 r θ true + jetBase r θ true (firstJet (endpointX true))) *
        jetBase r θ true (firstJet (endpointY true)) * jetX2 r θ true +
      jetX0 r θ true * jetBase r θ true (firstJet (betaCoefficient r θ true)) +
      jetBase r θ true ((1-firstJet (PowerSeries.C Complex.I)) *
        firstJet (endpointY true)^3 - firstJet (PowerSeries.C Complex.I)*
        firstJet (endpointX true)^3) = 0 at hh
    simp only [endpointX, endpointY, map_one, one_pow, mul_one,
      beta_true_firstJet, firstJet_X_cube, mul_zero, sub_zero, map_sub, map_mul] at hh
    change jetX2 r θ true ^ 3 + (jetX0 r θ true+jetT r θ true)*jetX2 r θ true +
      jetScalar r θ true (1-Complex.I) +
      jetScalar r θ true θ * jetScalar r θ true r * jetT r θ true * jetX0 r θ true = 0
    simp only [jetScalar, RingHom.comp_apply, map_sub, map_one, jetT]
    linear_combination hh

theorem true_jet_t_mul_a_sq (r θ : ℂ) : jetT r θ true * jetX0 r θ true ^ 2 = 0 := by
  rw [(true_jet_relations r θ).1]
  calc
    _ = jetScalar r θ true r * jetT r θ true ^ 2 := by ring
    _ = 0 := by rw [jetT_sq, mul_zero]

theorem true_jet_c_mul_k (r θ : ℂ) :
    jetScalar r θ true (1-Complex.I) * jetScalar r θ true kappa = 1 := by
  rw [← map_mul, one_sub_I_mul_kappa, map_one]

/-- A universal inverse identity; all its hypotheses are discharged below
by the actual monic polynomial quotient and its first-jet map. -/
theorem inverse_first_jet_identity {A : Type*} [CommRing A]
    (a b t c k u r : A)
    (hb : b^3+(a+t)*b+c+u*r*t*a=0) (ht : t^2=0) (hc : c*k=1) :
    b * ((b^2+a+t)*(k-u*r*t*a*k^2)) = -1 := by
  have hb' : b*(b^2+a+t) = -c-u*r*t*a := by linear_combination hb
  calc
    _ = (-c-u*r*t*a)*(k-u*r*t*a*k^2) := by rw [← mul_assoc, hb']
    _ = -1 + u*r*t*a*k*(c*k-1) - (c*k-1) + u^2*r^2*a^2*k^2*t^2 := by ring
    _ = -1 := by rw [hc, ht]; ring

def inverseJetNormal (r θ : ℂ) : JetChart r θ true :=
  jetScalar r θ true kappa * jetX2 r θ true ^ 2 +
    jetScalar r θ true kappa * jetX0 r θ true +
    jetScalar r θ true kappa * jetT r θ true -
    jetScalar r θ true θ * jetScalar r θ true r * jetT r θ true * jetX0 r θ true *
      jetScalar r θ true kappa ^ 2 * jetX2 r θ true ^ 2

theorem neg_inverse_jet_normal (r θ : ℂ) :
    -(((jetX2Unit r θ true)⁻¹ : (JetChart r θ true)ˣ) : JetChart r θ true) =
      inverseJetNormal r θ := by
  let A := jetX0 r θ true
  let B := jetX2 r θ true
  let T := jetT r θ true
  let C := jetScalar r θ true (1-Complex.I)
  let K := jetScalar r θ true kappa
  let U := jetScalar r θ true θ
  let R := jetScalar r θ true r
  have hh := inverse_first_jet_identity A B T C K U R
    (true_jet_relations r θ).2 (jetT_sq r θ true) (true_jet_c_mul_k r θ)
  have hta : T*A^2=0 := true_jet_t_mul_a_sq r θ
  have ht : T^2=0 := jetT_sq r θ true
  have he : (B^2+A+T)*(K-U*R*T*A*K^2) = inverseJetNormal r θ := by
    change _ = K*B^2+K*A+K*T-U*R*T*A*K^2*B^2
    calc
      _ = K*B^2+K*A+K*T-U*R*T*A*K^2*B^2-U*R*K^2*(T*A^2+A*T^2) := by ring
      _ = _ := by rw [hta, ht]; ring
  rw [he] at hh
  change jetX2 r θ true * inverseJetNormal r θ = -1 at hh
  have hc := congrArg (fun z : JetChart r θ true =>
    (((jetX2Unit r θ true)⁻¹ : (JetChart r θ true)ˣ) : JetChart r θ true) * z) hh
  rw [← coe_jetX2Unit, ← mul_assoc, (jetX2Unit r θ true).inv_mul, one_mul] at hc
  simpa using hc.symm

theorem jetCoefficient_small (r θ : ℂ) (e : Bool) (z : Jet) (j k : ℕ)
    (hj : j<2) (hk : k<3) :
    jetCoefficient r θ e (jetBase r θ e z * jetX0 r θ e ^ j * jetX2 r θ e ^ k) =
      if j=1 ∧ k=2 then z else 0 :=
  coefficient_small_monomial _ _ _ _ _ _ j k hj hk

theorem jetCoefficient_neg_inverse (r θ : ℂ) :
    jetCoefficient r θ true
      (-(((jetX2Unit r θ true)⁻¹ : (JetChart r θ true)ˣ) : JetChart r θ true)) =
      -firstJet (PowerSeries.C θ) * firstJet (PowerSeries.C r) * firstJet PowerSeries.X *
        firstJet (PowerSeries.C kappa)^2 := by
  rw [neg_inverse_jet_normal]
  let U := firstJet (PowerSeries.C θ)
  let R := firstJet (PowerSeries.C r)
  let T := firstJet (PowerSeries.X : PS)
  let K := firstJet (PowerSeries.C kappa)
  have he : inverseJetNormal r θ =
      jetBase r θ true K * jetX0 r θ true^0 * jetX2 r θ true^2 +
      jetBase r θ true K * jetX0 r θ true^1 * jetX2 r θ true^0 +
      jetBase r θ true (K*T) * jetX0 r θ true^0 * jetX2 r θ true^0 +
      jetBase r θ true (-U*R*T*K^2) * jetX0 r θ true^1 * jetX2 r θ true^2 := by
    simp only [inverseJetNormal, jetScalar, jetT, RingHom.comp_apply,
      map_mul, map_pow, map_neg, pow_zero, pow_one, mul_one, U, R, T, K]
    ring
  rw [he, map_add, map_add, map_add,
    jetCoefficient_small _ _ _ _ 0 2 (by decide) (by decide),
    jetCoefficient_small _ _ _ _ 1 0 (by decide) (by decide),
    jetCoefficient_small _ _ _ _ 0 0 (by decide) (by decide),
    jetCoefficient_small _ _ _ _ 1 2 (by decide) (by decide)]
  simp [U,R,T,K]

theorem a_cube_mul_inverseJetNormal (r θ : ℂ) :
    jetX0 r θ true^3 * inverseJetNormal r θ =
      jetScalar r θ true r * jetT r θ true * jetScalar r θ true kappa *
        jetX0 r θ true * jetX2 r θ true^2 := by
  let A := jetX0 r θ true
  let B := jetX2 r θ true
  let T := jetT r θ true
  let K := jetScalar r θ true kappa
  let U := jetScalar r θ true θ
  let R := jetScalar r θ true r
  have ha : A^2=R*T := (true_jet_relations r θ).1
  have ht : T^2=0 := jetT_sq r θ true
  have hta : T*A^2=0 := true_jet_t_mul_a_sq r θ
  have ha3 : A^3=R*T*A := by rw [pow_succ, ha]
  change A^3*(K*B^2+K*A+K*T-U*R*T*A*K^2*B^2) = R*T*K*A*B^2
  rw [ha3]
  calc
    _ = R*T*K*A*B^2 + R*K*(T*A^2) + R*K*A*T^2 - U*R^2*K^2*B^2*(T^2*A^2) := by ring
    _ = _ := by rw [hta, ht]; ring

theorem jetCoefficient_a_cube_neg_inverse (r θ : ℂ) :
    jetCoefficient r θ true
      (jetX0 r θ true^3 *
        -(((jetX2Unit r θ true)⁻¹ : (JetChart r θ true)ˣ) : JetChart r θ true)) =
      firstJet (PowerSeries.C r) * firstJet PowerSeries.X * firstJet (PowerSeries.C kappa) := by
  rw [neg_inverse_jet_normal, a_cube_mul_inverseJetNormal]
  have he : jetScalar r θ true r * jetT r θ true * jetScalar r θ true kappa *
      jetX0 r θ true * jetX2 r θ true^2 =
      jetBase r θ true (firstJet (PowerSeries.C r) * firstJet PowerSeries.X *
        firstJet (PowerSeries.C kappa)) * jetX0 r θ true^1 * jetX2 r θ true^2 := by
    simp [jetScalar, jetT]
  rw [he, jetCoefficient_small _ _ _ _ 1 2 (by decide) (by decide)]
  simp

end CycleQ2SeedCechTheta

#print axioms CycleQ2SeedCechTheta.jetCoefficient_neg_inverse
#print axioms CycleQ2SeedCechTheta.jetCoefficient_a_cube_neg_inverse
end
end


/- Component: continuation_3/cylinder_bridge/SeedCechThetaNormal.lean -/
section
/-! Homogeneous normal forms throughout the actual `h + θ*x₀³` family. -/

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedCechTheta

open MvPolynomial CycleQ2SeedTrace CycleQ2IncidenceNormalForm
open CycleQ2SeedCech
open scoped MonomialOrder

/-- Reduction of the actual cubic by `x₀²-r*x₁*x₃`.  Its leading monomial
remains `x₂³` for every parameter value, including both θ=0 and θ=1. -/
def reducedCurveH (r θ : ℂ) : Poly :=
  CycleQ2SeedCech.curveH + C (θ * r) * mon 1 1 0 1

theorem curveH_reduction_identity (r θ : ℂ) :
    curveH θ = reducedCurveH r θ + C θ * X 0 * curveF1 r := by
  simp only [curveH, reducedCurveH, CycleQ2SeedCech.curveH,
    curveF1, relation, mon, map_mul, Matrix.cons_val_zero, Matrix.cons_val_zero']
  ring

theorem reducedCurveH_leading_data (r θ : ℂ) :
    curveOrder.degree (reducedCurveH r θ) = exponent ![0,0,3,0] ∧
      curveOrder.Monic (reducedCurveH r θ) := by
  have hlt : curveOrder.degree (C (θ * r) * mon 1 1 0 1) ≺[curveOrder]
      curveOrder.degree CycleQ2SeedCech.curveH := by
    rw [mon_eq_monomial, C_mul_monomial, mul_one,
      CycleQ2SeedCech.curveH_leading_data.1]
    apply lt_of_le_of_lt (curveOrder.degree_monomial_le (θ * r))
    apply weightedOrder_lt_of_weight_lt
    change (5 : ℕ) < 9
    decide
  exact ⟨(curveOrder.degree_add_of_lt hlt).trans CycleQ2SeedCech.curveH_leading_data.1,
    CycleQ2SeedCech.curveH_leading_data.2.add_of_lt hlt⟩

theorem reducedCurveH_homogeneous (r θ : ℂ) :
    (reducedCurveH r θ).IsHomogeneous 3 := by
  have hm : (mon 1 1 0 1).IsHomogeneous 3 := by
    simpa using CycleQ2SeedCech.mon_homogeneous 1 1 0 1
  exact CycleQ2SeedCech.curveH_homogeneous.add (hm.C_mul (θ * r))

theorem curveH_homogeneous (θ : ℂ) : (curveH θ).IsHomogeneous 3 := by
  have hm : (mon 3 0 0 0).IsHomogeneous 3 := by
    simpa using CycleQ2SeedCech.mon_homogeneous 3 0 0 0
  simpa only [curveH, CycleQ2SeedCech.curveH, mon, pow_zero, mul_one]
    using CycleQ2SeedCech.curveH_homogeneous.add (hm.C_mul θ)

/-- The reduction step changes the second generator by an explicit multiple
of the first, so this is the actual θ-curve ideal. -/
theorem curveIdeal_eq_reduced (r θ : ℂ) :
    curveIdeal r θ = equationsIdeal (curveF1 r) (reducedCurveH r θ) := by
  ext p
  change p ∈ Ideal.span {curveF1 r, curveH θ} ↔
    p ∈ Ideal.span {curveF1 r, reducedCurveH r θ}
  rw [Ideal.mem_span_pair, Ideal.mem_span_pair]
  constructor
  · rintro ⟨a, b, hab⟩
    refine ⟨a + b * C θ * X 0, b, ?_⟩
    rw [← hab, curveH_reduction_identity]
    ring
  · rintro ⟨a, b, hab⟩
    refine ⟨a - b * C θ * X 0, b, ?_⟩
    rw [← hab, curveH_reduction_identity]
    ring

theorem theta_curve_leading_coprime (r θ : ℂ) :
    ∀ j, curveOrder.degree (curveF1 r) j = 0 ∨
      curveOrder.degree (reducedCurveH r θ) j = 0 := by
  rw [(curveF1_leading_data r).1, (reducedCurveH_leading_data r θ).1]
  intro j
  fin_cases j <;> simp

theorem theta_curveReduced_iff (r θ : ℂ) (p : Poly) :
    CurveReduced p ↔ Reduced curveOrder (curveF1 r) (reducedCurveH r θ) p := by
  rw [CycleQ2SeedCech.curveReduced_iff r p]
  simp only [Reduced, CycleQ2SeedCech.curveH_leading_data.1,
    (reducedCurveH_leading_data r θ).1]

/-- Every homogeneous function on every actual θ-curve has a homogeneous
representative with x₀ exponent below 2 and x₂ exponent below 3. -/
theorem exists_homogeneous_curve_normal (r θ : ℂ) (p : Poly) (d : ℕ)
    (hp : p.IsHomogeneous d) :
    ∃ q : Poly, CurveReduced q ∧ q.IsHomogeneous d ∧ p - q ∈ curveIdeal r θ := by
  obtain ⟨u, v, q, hpq, hq⟩ := exists_reduced_representation curveOrder
    (curveF1 r) (reducedCurveH r θ) p
    (curveF1_leading_data r).2 (reducedCurveH_leading_data r θ).2
  refine ⟨q, (theta_curveReduced_iff r θ q).mpr hq, ?_, ?_⟩
  · exact reduced_isHomogeneous curveOrder (curveF1_leading_data r).2
      (reducedCurveH_leading_data r θ).2 (theta_curve_leading_coprime r θ)
      (curveF1_homogeneous r) (reducedCurveH_homogeneous r θ) hp hq hpq
  · rw [curveIdeal_eq_reduced]
    apply Ideal.mem_span_pair.mpr
    exact ⟨u, v, by rw [hpq]; ring⟩

end CycleQ2SeedCechTheta

#print axioms CycleQ2SeedCechTheta.reducedCurveH_leading_data
#print axioms CycleQ2SeedCechTheta.curveIdeal_eq_reduced
#print axioms CycleQ2SeedCechTheta.exists_homogeneous_curve_normal
end
end


/- Component: continuation_3/SeedCechThreeOpen.lean -/
section
/-!
# The explicit three-open Čech kernel for the nine shifted free summands

Laurent coefficients record the three remaining coordinates.  A section on a
coordinate open may have negative exponents only in the inverted coordinates.
The proof splits the first exponent into its nonnegative and negative parts.
It works over every commutative coefficient ring and preserves the actual
weighted degree and cubic character of every one of the nine summands.
-/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedCechThreeOpen

open MvPolynomial CycleQ2SeedQuotientFiniteFree
open scoped BigOperators

variable {R : Type*} [CommRing R]

abbrev LaurentExponent := Fin 3 → ℤ
abbrev Laurent := AddMonoidAlgebra R LaurentExponent
abbrev ShiftIndex := Fin 3 × Fin 3
abbrev LaurentGrade := ℤ × ZMod 3

/-- Only coordinates in `s` may have poles. -/
def HasPoles (s : Finset (Fin 3)) (p : Laurent (R := R)) : Prop :=
  ∀ e i, i ∉ s → e i < 0 → p.coeff e = 0

/-- The degree and character of `x₀^a*w^b` times a base Laurent monomial. -/
def shiftedGrade (ab : ShiftIndex) (e : LaurentExponent) : LaurentGrade :=
  ((ab.1.val : ℤ) + 2 * ab.2.val + ∑ i, e i,
    (2 * ab.1.val : ℕ) + (2 * e 0 + e 1 : ℤ))

def HasGrade (ab : ShiftIndex) (g : LaurentGrade) (p : Laurent (R := R)) : Prop :=
  ∀ e, shiftedGrade ab e ≠ g → p.coeff e = 0

/-- Projection onto nonnegative exponent of the first base coordinate. -/
def nonnegativePart (p : Laurent (R := R)) : Laurent (R := R) :=
  AddMonoidAlgebra.ofCoeff (p.coeff.filter (fun e ↦ 0 ≤ e 0))

@[simp] theorem nonnegativePart_apply (p : Laurent (R := R)) (e : LaurentExponent) :
    (nonnegativePart p).coeff e = if 0 ≤ e 0 then p.coeff e else 0 := rfl

theorem hasGrade_nonnegativePart (ab : ShiftIndex) (g : LaurentGrade)
    {p : Laurent (R := R)} (hp : HasGrade ab g p) : HasGrade ab g (nonnegativePart p) := by
  intro e he
  simp only [nonnegativePart_apply]
  split <;> simp [hp e he]

theorem hasGrade_add (ab : ShiftIndex) (g : LaurentGrade)
    {p q : Laurent (R := R)} (hp : HasGrade ab g p) (hq : HasGrade ab g q) :
    HasGrade ab g (p + q) := by
  intro e he
  simp [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp e he, hq e he]

theorem hasGrade_sub (ab : ShiftIndex) (g : LaurentGrade)
    {p q : Laurent (R := R)} (hp : HasGrade ab g p) (hq : HasGrade ab g q) :
    HasGrade ab g (p - q) := by
  intro e he
  simp [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, hp e he, hq e he]

/-- A concrete contraction, before imposing any degree. -/
theorem threeOpen_kernel (p01 p02 p12 : Laurent (R := R))
    (h01 : HasPoles {0, 1} p01) (h02 : HasPoles {0, 2} p02)
    (h12 : HasPoles {1, 2} p12) (hc : p01 - p02 + p12 = 0) :
    HasPoles {0} (nonnegativePart p01 - p01) ∧
    HasPoles {1} (nonnegativePart p01) ∧
    HasPoles {2} (p12 + nonnegativePart p01) ∧
    p01 = nonnegativePart p01 - (nonnegativePart p01 - p01) ∧
    p02 = (p12 + nonnegativePart p01) - (nonnegativePart p01 - p01) ∧
    p12 = (p12 + nonnegativePart p01) - nonnegativePart p01 := by
  have heq (e : LaurentExponent) : p01.coeff e - p02.coeff e + p12.coeff e = 0 := by
    have hh := congrArg (fun p : Laurent (R := R) ↦ p.coeff e) hc
    simpa only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_zero, Finsupp.add_apply, Finsupp.sub_apply, Finsupp.zero_apply] using hh
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e i hi hneg
    fin_cases i
    · simp at hi
    · by_cases h0 : 0 ≤ e 0
      · simp [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, h0]
      · have hz02 := h02 e 1 (by decide) hneg
        have hz12 := h12 e 0 (by decide) (lt_of_not_ge h0)
        have hz01 : p01.coeff e = 0 := by
          have hh := heq e
          simpa [hz02, hz12] using hh
        simp [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, h0, hz01]
    · have hz := h01 e 2 (by decide) hneg
      simp [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, hz]
  · intro e i hi hneg
    fin_cases i
    · change e 0 < 0 at hneg
      simp [not_le.mpr hneg]
    · simp at hi
    · simp [h01 e 2 (by decide) hneg]
  · intro e i hi hneg
    fin_cases i
    · change e 0 < 0 at hneg
      simp [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
        not_le.mpr hneg, h12 e 0 (by decide) hneg]
    · by_cases h0 : 0 ≤ e 0
      · have hz02 := h02 e 1 (by decide) hneg
        have hh := heq e
        simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
          nonnegativePart_apply, if_pos h0]
        linear_combination hh + hz02
      · simp [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, h0,
          h12 e 0 (by decide) (lt_of_not_ge h0)]
    · simp at hi
  · abel
  · linear_combination -hc
  · abel

/-- Every graded one-cocycle is a coboundary with the same degree and character. -/
theorem exists_graded_primitives (ab : ShiftIndex) (g : LaurentGrade)
    (p01 p02 p12 : Laurent (R := R))
    (h01 : HasPoles {0, 1} p01) (h02 : HasPoles {0, 2} p02)
    (h12 : HasPoles {1, 2} p12)
    (hg01 : HasGrade ab g p01) (_hg02 : HasGrade ab g p02)
    (hg12 : HasGrade ab g p12) (hc : p01 - p02 + p12 = 0) :
    ∃ q0 q1 q2 : Laurent (R := R),
      HasPoles {0} q0 ∧ HasPoles {1} q1 ∧ HasPoles {2} q2 ∧
      HasGrade ab g q0 ∧ HasGrade ab g q1 ∧ HasGrade ab g q2 ∧
      p01 = q1 - q0 ∧ p02 = q2 - q0 ∧ p12 = q2 - q1 := by
  have hh := threeOpen_kernel p01 p02 p12 h01 h02 h12 hc
  have hn := hasGrade_nonnegativePart ab g hg01
  exact ⟨nonnegativePart p01 - p01, nonnegativePart p01,
    p12 + nonnegativePart p01, hh.1, hh.2.1, hh.2.2.1,
    hasGrade_sub ab g hn hg01, hn, hasGrade_add ab g hg12 hn,
    hh.2.2.2⟩

/-- The same exactness for the actual nine degree-shifted summands. -/
theorem nineSummand_kernel (g : LaurentGrade)
    (p01 p02 p12 : ShiftIndex → Laurent (R := R))
    (h01 : ∀ ab, HasPoles {0, 1} (p01 ab))
    (h02 : ∀ ab, HasPoles {0, 2} (p02 ab))
    (h12 : ∀ ab, HasPoles {1, 2} (p12 ab))
    (hg01 : ∀ ab, HasGrade ab g (p01 ab))
    (hg02 : ∀ ab, HasGrade ab g (p02 ab))
    (hg12 : ∀ ab, HasGrade ab g (p12 ab))
    (hc : ∀ ab, p01 ab - p02 ab + p12 ab = 0) :
    ∃ q0 q1 q2 : ShiftIndex → Laurent (R := R),
      (∀ ab, HasPoles {0} (q0 ab)) ∧ (∀ ab, HasPoles {1} (q1 ab)) ∧
      (∀ ab, HasPoles {2} (q2 ab)) ∧
      (∀ ab, HasGrade ab g (q0 ab)) ∧ (∀ ab, HasGrade ab g (q1 ab)) ∧
      (∀ ab, HasGrade ab g (q2 ab)) ∧
      (∀ ab, p01 ab = q1 ab - q0 ab) ∧
      (∀ ab, p02 ab = q2 ab - q0 ab) ∧
      (∀ ab, p12 ab = q2 ab - q1 ab) := by
  choose q0 q1 q2 h0 h1 h2 hg0 hg1 hg2 he01 he02 he12 using
    fun ab ↦ exists_graded_primitives ab g (p01 ab) (p02 ab) (p12 ab)
      (h01 ab) (h02 ab) (h12 ab) (hg01 ab) (hg02 ab) (hg12 ab) (hc ab)
  exact ⟨q0, q1, q2, h0, h1, h2, hg0, hg1, hg2, he01, he02, he12⟩

end CycleQ2SeedCechThreeOpen

#print axioms CycleQ2SeedCechThreeOpen.nineSummand_kernel
end
end


/- Component: continuation_3/SeedCoordinateCover.lean -/
section
/-! # The three base-coordinate opens cover every relevant seed prime -/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedCoordinateCover

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree

variable {R : Type*} [CommRing R]

theorem seedPrime_contains_all_of_base (r ι : R) (P : Ideal (Poly R)) [P.IsPrime]
    (hh : smoothH ι ∈ P) (hF : smoothF r ι ∈ P)
    (h1 : X 1 ∈ P) (h2 : X 2 ∈ P) (h3 : X 3 ∈ P) :
    ∀ i : Fin 5, X i ∈ P := by
  have hz1 : Ideal.Quotient.mk P (X 1) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h1
  have hz2 : Ideal.Quotient.mk P (X 2) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h2
  have hz3 : Ideal.Quotient.mk P (X 3) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h3
  have hzh : Ideal.Quotient.mk P (smoothH ι) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hh
  have hzF : Ideal.Quotient.mk P (smoothF r ι) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hF
  have hz0pow : Ideal.Quotient.mk P (X 0) ^ 3 = 0 := by
    simpa [smoothH, smoothB, smoothA, hz1, hz2, hz3] using hzh
  have hz0 : Ideal.Quotient.mk P (X 0) = 0 := eq_zero_of_pow_eq_zero hz0pow
  have hzG : Ideal.Quotient.mk P (seedG r) = 0 := by
    simpa only [smoothF, map_add, map_mul, hzh, zero_mul, add_zero] using hzF
  have hzwpow : Ideal.Quotient.mk P (X 4) ^ 3 = 0 := by
    simpa [seedG, CycleQ2SegreSeed.seedG_expanded, hz0, hz1, hz2, hz3] using hzG
  have hzw : Ideal.Quotient.mk P (X 4) = 0 := eq_zero_of_pow_eq_zero hzwpow
  intro i
  fin_cases i
  · exact Ideal.Quotient.eq_zero_iff_mem.mp hz0
  · exact h1
  · exact h2
  · exact h3
  · exact Ideal.Quotient.eq_zero_iff_mem.mp hzw

theorem seedPrime_coordinate_cover (r ι : R) (P : Ideal (Poly R)) [P.IsPrime]
    (hh : smoothH ι ∈ P) (hF : smoothF r ι ∈ P)
    (hrelevant : ∃ i : Fin 5, X i ∉ P) :
    X 1 ∉ P ∨ X 2 ∉ P ∨ X 3 ∉ P := by
  by_contra h
  push Not at h
  obtain ⟨i, hi⟩ := hrelevant
  exact hi (seedPrime_contains_all_of_base r ι P hh hF h.1 h.2.1 h.2.2 i)

/-- The same cover criterion in the existing actual seed quotient. -/
theorem seedQuotient_coordinate_cover (r ι : R) (P : Ideal (SeedRing r ι)) [P.IsPrime]
    (hrelevant : ∃ i : Fin 5,
      Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) (X i) ∉ P) :
    ∃ i : Fin 3, algebraMap (Base R) (SeedRing r ι) (X i) ∉ P := by
  let f := Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι))
  let Q := P.comap f
  have hh : smoothH ι ∈ Q := by
    change f (smoothH ι) ∈ P
    have hz : f (smoothH ι) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (by simp [equationsIdeal]))
    rw [hz]
    exact P.zero_mem
  have hF : smoothF r ι ∈ Q := by
    change f (smoothF r ι) ∈ P
    have hz : f (smoothF r ι) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (by simp [equationsIdeal]))
    rw [hz]
    exact P.zero_mem
  rcases seedPrime_coordinate_cover r ι Q hh hF hrelevant with h1 | h2 | h3
  · refine ⟨0, ?_⟩
    change f (X 1) ∉ P at h1
    change f (remainingInclusion R (X 0)) ∉ P
    simpa [remainingInclusion, remainingIndex] using h1
  · refine ⟨1, ?_⟩
    change f (X 2) ∉ P at h2
    change f (remainingInclusion R (X 1)) ∉ P
    simpa [remainingInclusion, remainingIndex] using h2
  · refine ⟨2, ?_⟩
    change f (X 3) ∉ P at h3
    change f (remainingInclusion R (X 2)) ∉ P
    simpa [remainingInclusion, remainingIndex] using h3

end CycleQ2SeedCoordinateCover

#print axioms CycleQ2SeedCoordinateCover.seedQuotient_coordinate_cover
end
end


/- Component: continuation_3/SeedLinkageRegular.lean -/
section
/-!
# Regularity of the actual linkage denominator on the seed surface

Specializing the remaining base coordinates to (0,0,1) gives x0^3=ι-1
and w^3=-x0^6. If ι≠1, both x0 and w are units in that fiber, so the
linkage denominator x0^2*w+r*x1*x3*x2^2 is a unit there. Finite freeness
over the three-coordinate polynomial ring proves it is a nonzerodivisor
in the original seed quotient. No irreducibility of the seed is assumed.
-/

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedLinkageRegular

open MvPolynomial CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree
  CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations CycleQ2IncidenceFirstOrder
open scoped TensorProduct

variable {K : Type*} [Field K]

def basePoint : Base K →+* K := eval (fun j : Fin 3 => if j=2 then 1 else 0)

local instance basePointAlgebra : Algebra (Base K) K := (basePoint (K := K)).toAlgebra

abbrev Fiber (r ι : K) := K ⊗[Base K] SeedRing r ι

local instance fiberCommRing (r ι : K) : CommRing (Fiber r ι) :=
  Algebra.TensorProduct.instCommRing

local instance fiberAlgebra (r ι : K) : Algebra K (Fiber r ι) :=
  Algebra.TensorProduct.leftAlgebra

def toFiber (r ι : K) : SeedRing r ι →+* Fiber r ι :=
  (Algebra.TensorProduct.includeRight : SeedRing r ι →ₐ[Base K] Fiber r ι).toRingHom

def ambientToFiber (r ι : K) : Poly K →+* Fiber r ι :=
  (toFiber r ι).comp (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)))

def z (r ι : K) (j : Fin 5) : Fiber r ι := ambientToFiber r ι (X j)
theorem ambient_X (r ι : K) (j : Fin 5) : ambientToFiber r ι (X j) = z r ι j := rfl

def coefficientMap (r ι : K) : K →+* Fiber r ι := (ambientToFiber r ι).comp C

theorem remainingCoordinate (r ι : K) (j : Fin 3) :
    ambientToFiber r ι (X (remainingIndex j)) =
      algebraMap K (Fiber r ι) ((basePoint (K := K)) (X j)) := by
  have he : Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι))
      (X (remainingIndex j)) = algebraMap (Base K) (SeedRing r ι) (X j) := by
    change Ideal.Quotient.mk _ (X (remainingIndex j)) =
      Ideal.Quotient.mk _ (remainingInclusion K (X j))
    simp [remainingInclusion]
  change toFiber r ι (Ideal.Quotient.mk _ (X (remainingIndex j))) = _
  rw [he]
  change Algebra.TensorProduct.includeRight (algebraMap (Base K) (SeedRing r ι) (X j)) = _
  rw [AlgHom.commutes]
  rfl

theorem z_one (r ι : K) : z r ι 1 = 0 := by
  have h := remainingCoordinate r ι 0
  simpa [remainingIndex, basePoint, z, ← Algebra.TensorProduct.one_def] using h

theorem z_two (r ι : K) : z r ι 2 = 0 := by
  have h := remainingCoordinate r ι 1
  simpa [remainingIndex, basePoint, z, ← Algebra.TensorProduct.one_def] using h

theorem z_three (r ι : K) : z r ι 3 = 1 := by
  have h := remainingCoordinate r ι 2
  simpa [remainingIndex, basePoint, z, ← Algebra.TensorProduct.one_def] using h

theorem ambient_h (r ι : K) : ambientToFiber r ι (smoothH ι) = 0 := by
  have h : Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) (smoothH ι) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp [equationsIdeal]))
  change toFiber r ι (Ideal.Quotient.mk _ (smoothH ι)) = 0
  rw [h, map_zero]

theorem ambient_g (r ι : K) : ambientToFiber r ι (seedG r) = 0 := by
  have h : Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) (seedG r) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply (smoothSeed_mem_iff_linkage r ι).mpr
    exact ⟨0,1,by simp⟩
  change toFiber r ι (Ideal.Quotient.mk _ (seedG r)) = 0
  rw [h, map_zero]

theorem x0_cubed (r ι : K) : z r ι 0^3 = coefficientMap r ι (ι-1) := by
  have hh := ambient_h r ι
  change z r ι 0^3 = ambientToFiber r ι (C (ι-1))
  simp only [smoothH, smoothB, smoothA, map_sub, map_add, map_mul, map_pow,
    ambient_X, z_one, z_two, z_three, zero_pow (by decide : 3≠0),
    zero_pow (by decide : 2≠0), one_pow, zero_mul, mul_zero, add_zero, zero_add,
    mul_one] at hh
  rw [map_sub, map_sub, map_one, map_one]
  linear_combination hh

theorem w_cubed (r ι : K) : z r ι 4^3 = -(z r ι 0^6) := by
  have hg := ambient_g r ι
  simp only [seedG, CycleQ2SegreSeed.seedG_expanded, map_sub, map_add, map_mul,
    map_pow, ambient_X, z_one, z_two, z_three, zero_pow (by decide : 3≠0),
    zero_pow (by decide : 6≠0), one_pow, zero_mul, mul_zero, sub_zero,
    add_zero, zero_add] at hg
  linear_combination hg

theorem x0_unit (r ι : K) (hι : ι≠1) : IsUnit (z r ι 0) := by
  apply (isUnit_pow_iff (by decide : 3≠0)).mp
  rw [x0_cubed]
  exact (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hι)).map (coefficientMap r ι)

theorem w_unit (r ι : K) (hι : ι≠1) : IsUnit (z r ι 4) := by
  apply (isUnit_pow_iff (by decide : 3≠0)).mp
  rw [w_cubed]
  exact (IsUnit.neg_iff _).mpr ((x0_unit r ι hι).pow 6)

def linkagePolynomial (r : K) : Poly K :=
  CycleQ2SegreSeed.seedP (C r) (X 0) (X 1) (X 2) (X 3) (X 4)

def linkageElement (r ι : K) : SeedRing r ι :=
  Ideal.Quotient.mk _ (linkagePolynomial r)

theorem linkage_fiber (r ι : K) :
    toFiber r ι (linkageElement r ι) = z r ι 0^2*z r ι 4 := by
  change ambientToFiber r ι (linkagePolynomial r) = _
  simp only [linkagePolynomial, CycleQ2SegreSeed.seedP, CycleQ2SegreSeed.linkageP,
    map_add, map_mul, map_pow, ambient_X, z_one, z_two, z_three, zero_mul, mul_zero,
    add_zero]

theorem linkage_unit_fiber (r ι : K) (hι : ι≠1) :
    IsUnit (toFiber r ι (linkageElement r ι)) := by
  rw [linkage_fiber]
  exact ((x0_unit r ι hι).pow 2).mul (w_unit r ι hι)

/-- The actual linkage element is a nonzerodivisor over every field at
every r and every ι≠1, including both the complex and modular seeds. -/
theorem linkage_mul_injective (r ι : K) (hι : ι≠1) :
    Function.Injective (fun x : SeedRing r ι => linkageElement r ι*x) := by
  letI : Module.Free (Base K) (SeedRing r ι) := seedQuotient_free K r ι
  letI : Module.Finite (Base K) (SeedRing r ι) := seedQuotient_finite K r ι
  exact CycleQ2UnitFiberRegular.injective_mul_of_unit_fiber (A := K)
    (linkageElement r ι) (linkage_unit_fiber r ι hι)

end CycleQ2SeedLinkageRegular

#print axioms CycleQ2SeedLinkageRegular.linkage_unit_fiber
#print axioms CycleQ2SeedLinkageRegular.linkage_mul_injective
end
end


