import Proposal.GeometricTarget09Part03

/-! Continuation of GeometricTarget09.lean; complete source components and declarations. -/

set_option Elab.async false

/- Component: continuation_3/SegreModularBasepointChecks3.lean -/
section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularBasepointData
open CycleQ2SparseModularPolynomial CycleQ2SegreModularTangentData
def residualExpression3 : Blocks :=
  addBlocks target3 (negBlocks (addBlocks (mulBlocks m00 witness3_00) (addBlocks (mulBlocks m01 witness3_01) (addBlocks (mulBlocks m02 witness3_02) (addBlocks (mulBlocks m10 witness3_10) (addBlocks (mulBlocks m11 witness3_11) (addBlocks (mulBlocks m12 witness3_12) (addBlocks (mulBlocks m20 witness3_20) (addBlocks (mulBlocks m21 witness3_21) (addBlocks (mulBlocks m22 witness3_22) (addBlocks (mulBlocks h hWitness3) (addBlocks (mulBlocks g gWitness3) []))))))))))))

private theorem block_3_0_0 : checkBlock residualExpression3 0 0 = true := by
  decide +kernel

private theorem block_3_0_1 : checkBlock residualExpression3 0 1 = true := by
  decide +kernel

private theorem block_3_0_2 : checkBlock residualExpression3 0 2 = true := by
  decide +kernel

private theorem block_3_0_3 : checkBlock residualExpression3 0 3 = true := by
  decide +kernel

private theorem block_3_0_4 : checkBlock residualExpression3 0 4 = true := by
  decide +kernel

private theorem block_3_0_5 : checkBlock residualExpression3 0 5 = true := by
  decide +kernel

private theorem block_3_0_6 : checkBlock residualExpression3 0 6 = true := by
  decide +kernel

private theorem block_3_1_0 : checkBlock residualExpression3 1 0 = true := by
  decide +kernel

private theorem block_3_1_1 : checkBlock residualExpression3 1 1 = true := by
  decide +kernel

private theorem block_3_1_2 : checkBlock residualExpression3 1 2 = true := by
  decide +kernel

private theorem block_3_1_3 : checkBlock residualExpression3 1 3 = true := by
  decide +kernel

private theorem block_3_1_4 : checkBlock residualExpression3 1 4 = true := by
  decide +kernel

private theorem block_3_1_5 : checkBlock residualExpression3 1 5 = true := by
  decide +kernel

private theorem block_3_1_6 : checkBlock residualExpression3 1 6 = true := by
  decide +kernel

private theorem block_3_2_0 : checkBlock residualExpression3 2 0 = true := by
  decide +kernel

private theorem block_3_2_1 : checkBlock residualExpression3 2 1 = true := by
  decide +kernel

private theorem block_3_2_2 : checkBlock residualExpression3 2 2 = true := by
  decide +kernel

private theorem block_3_2_3 : checkBlock residualExpression3 2 3 = true := by
  decide +kernel

private theorem block_3_2_4 : checkBlock residualExpression3 2 4 = true := by
  decide +kernel

private theorem block_3_2_5 : checkBlock residualExpression3 2 5 = true := by
  decide +kernel

private theorem block_3_2_6 : checkBlock residualExpression3 2 6 = true := by
  decide +kernel

private theorem block_3_2_7 : checkBlock residualExpression3 2 7 = true := by
  decide +kernel

private theorem block_3_3_0 : checkBlock residualExpression3 3 0 = true := by
  decide +kernel

private theorem block_3_3_1 : checkBlock residualExpression3 3 1 = true := by
  decide +kernel

private theorem block_3_3_2 : checkBlock residualExpression3 3 2 = true := by
  decide +kernel

private theorem block_3_3_3 : checkBlock residualExpression3 3 3 = true := by
  decide +kernel

private theorem block_3_3_4 : checkBlock residualExpression3 3 4 = true := by
  decide +kernel

private theorem block_3_3_5 : checkBlock residualExpression3 3 5 = true := by
  decide +kernel

private theorem block_3_3_6 : checkBlock residualExpression3 3 6 = true := by
  decide +kernel

private theorem block_3_3_7 : checkBlock residualExpression3 3 7 = true := by
  decide +kernel

private theorem block_3_4_0 : checkBlock residualExpression3 4 0 = true := by
  decide +kernel

private theorem block_3_4_1 : checkBlock residualExpression3 4 1 = true := by
  decide +kernel

private theorem block_3_4_2 : checkBlock residualExpression3 4 2 = true := by
  decide +kernel

private theorem block_3_4_3 : checkBlock residualExpression3 4 3 = true := by
  decide +kernel

private theorem block_3_4_4 : checkBlock residualExpression3 4 4 = true := by
  decide +kernel

private theorem block_3_4_5 : checkBlock residualExpression3 4 5 = true := by
  decide +kernel

private theorem block_3_4_6 : checkBlock residualExpression3 4 6 = true := by
  decide +kernel

private theorem block_3_4_7 : checkBlock residualExpression3 4 7 = true := by
  decide +kernel

private theorem block_3_5_0 : checkBlock residualExpression3 5 0 = true := by
  decide +kernel

private theorem block_3_5_1 : checkBlock residualExpression3 5 1 = true := by
  decide +kernel

private theorem block_3_5_2 : checkBlock residualExpression3 5 2 = true := by
  decide +kernel

private theorem block_3_5_3 : checkBlock residualExpression3 5 3 = true := by
  decide +kernel

private theorem block_3_5_4 : checkBlock residualExpression3 5 4 = true := by
  decide +kernel

private theorem block_3_5_5 : checkBlock residualExpression3 5 5 = true := by
  decide +kernel

private theorem block_3_5_6 : checkBlock residualExpression3 5 6 = true := by
  decide +kernel

private theorem block_3_5_7 : checkBlock residualExpression3 5 7 = true := by
  decide +kernel

private theorem block_3_6_0 : checkBlock residualExpression3 6 0 = true := by
  decide +kernel

private theorem block_3_6_1 : checkBlock residualExpression3 6 1 = true := by
  decide +kernel

private theorem block_3_6_2 : checkBlock residualExpression3 6 2 = true := by
  decide +kernel

private theorem block_3_6_3 : checkBlock residualExpression3 6 3 = true := by
  decide +kernel

private theorem block_3_6_4 : checkBlock residualExpression3 6 4 = true := by
  decide +kernel

private theorem block_3_6_5 : checkBlock residualExpression3 6 5 = true := by
  decide +kernel

private theorem block_3_7_0 : checkBlock residualExpression3 7 0 = true := by
  decide +kernel

private theorem block_3_7_1 : checkBlock residualExpression3 7 1 = true := by
  decide +kernel

private theorem block_3_7_2 : checkBlock residualExpression3 7 2 = true := by
  decide +kernel

private theorem block_3_7_3 : checkBlock residualExpression3 7 3 = true := by
  decide +kernel

private theorem block_3_7_4 : checkBlock residualExpression3 7 4 = true := by
  decide +kernel

private theorem block_3_7_5 : checkBlock residualExpression3 7 5 = true := by
  decide +kernel

private theorem block_3_8_0 : checkBlock residualExpression3 8 0 = true := by
  decide +kernel

private theorem block_3_8_1 : checkBlock residualExpression3 8 1 = true := by
  decide +kernel

private theorem block_3_8_2 : checkBlock residualExpression3 8 2 = true := by
  decide +kernel

private theorem block_3_8_3 : checkBlock residualExpression3 8 3 = true := by
  decide +kernel

private theorem block_3_8_4 : checkBlock residualExpression3 8 4 = true := by
  decide +kernel

private theorem block_3_9_0 : checkBlock residualExpression3 9 0 = true := by
  decide +kernel

private theorem block_3_9_1 : checkBlock residualExpression3 9 1 = true := by
  decide +kernel

private theorem block_3_9_2 : checkBlock residualExpression3 9 2 = true := by
  decide +kernel

private theorem block_3_9_3 : checkBlock residualExpression3 9 3 = true := by
  decide +kernel

private theorem block_3_9_4 : checkBlock residualExpression3 9 4 = true := by
  decide +kernel

private theorem block_3_10_0 : checkBlock residualExpression3 10 0 = true := by
  decide +kernel

private theorem block_3_10_1 : checkBlock residualExpression3 10 1 = true := by
  decide +kernel

private theorem block_3_10_2 : checkBlock residualExpression3 10 2 = true := by
  decide +kernel

private theorem block_3_10_3 : checkBlock residualExpression3 10 3 = true := by
  decide +kernel

private theorem block_3_10_4 : checkBlock residualExpression3 10 4 = true := by
  decide +kernel

private theorem block_3_11_0 : checkBlock residualExpression3 11 0 = true := by
  decide +kernel

private theorem block_3_11_1 : checkBlock residualExpression3 11 1 = true := by
  decide +kernel

private theorem block_3_11_2 : checkBlock residualExpression3 11 2 = true := by
  decide +kernel

private theorem block_3_11_3 : checkBlock residualExpression3 11 3 = true := by
  decide +kernel

private theorem block_3_11_4 : checkBlock residualExpression3 11 4 = true := by
  decide +kernel

private theorem block_3_12_0 : checkBlock residualExpression3 12 0 = true := by
  decide +kernel

private theorem block_3_12_1 : checkBlock residualExpression3 12 1 = true := by
  decide +kernel

private theorem block_3_12_2 : checkBlock residualExpression3 12 2 = true := by
  decide +kernel

private theorem block_3_13_0 : checkBlock residualExpression3 13 0 = true := by
  decide +kernel

private theorem block_3_13_1 : checkBlock residualExpression3 13 1 = true := by
  decide +kernel

private theorem block_3_13_2 : checkBlock residualExpression3 13 2 = true := by
  decide +kernel

private theorem block_3_14_0 : checkBlock residualExpression3 14 0 = true := by
  decide +kernel

private theorem block_3_14_1 : checkBlock residualExpression3 14 1 = true := by
  decide +kernel

private theorem block_3_15_0 : checkBlock residualExpression3 15 0 = true := by
  decide +kernel

private theorem block_3_15_1 : checkBlock residualExpression3 15 1 = true := by
  decide +kernel

private theorem block_3_16_0 : checkBlock residualExpression3 16 0 = true := by
  decide +kernel

private theorem block_3_16_1 : checkBlock residualExpression3 16 1 = true := by
  decide +kernel

private theorem block_3_17_0 : checkBlock residualExpression3 17 0 = true := by
  decide +kernel

private theorem block_3_17_1 : checkBlock residualExpression3 17 1 = true := by
  decide +kernel

theorem identity3 {R : Type*} [CommRing R] [CharP R 109]
    (x : Fin 5 → R) (z w : R) :
    evalBlocks x z w residualExpression3 = 0 := by
  apply evalBlocks_eq_zero_of_checks x z w 18 8 residualExpression3
  · decide +kernel
  · intro n
    fin_cases n <;> decide +kernel
  · intro n m
    fin_cases n <;> fin_cases m
    · exact block_3_0_0
    · exact block_3_0_1
    · exact block_3_0_2
    · exact block_3_0_3
    · exact block_3_0_4
    · exact block_3_0_5
    · exact block_3_0_6
    · decide +kernel
    · exact block_3_1_0
    · exact block_3_1_1
    · exact block_3_1_2
    · exact block_3_1_3
    · exact block_3_1_4
    · exact block_3_1_5
    · exact block_3_1_6
    · decide +kernel
    · exact block_3_2_0
    · exact block_3_2_1
    · exact block_3_2_2
    · exact block_3_2_3
    · exact block_3_2_4
    · exact block_3_2_5
    · exact block_3_2_6
    · exact block_3_2_7
    · exact block_3_3_0
    · exact block_3_3_1
    · exact block_3_3_2
    · exact block_3_3_3
    · exact block_3_3_4
    · exact block_3_3_5
    · exact block_3_3_6
    · exact block_3_3_7
    · exact block_3_4_0
    · exact block_3_4_1
    · exact block_3_4_2
    · exact block_3_4_3
    · exact block_3_4_4
    · exact block_3_4_5
    · exact block_3_4_6
    · exact block_3_4_7
    · exact block_3_5_0
    · exact block_3_5_1
    · exact block_3_5_2
    · exact block_3_5_3
    · exact block_3_5_4
    · exact block_3_5_5
    · exact block_3_5_6
    · exact block_3_5_7
    · exact block_3_6_0
    · exact block_3_6_1
    · exact block_3_6_2
    · exact block_3_6_3
    · exact block_3_6_4
    · exact block_3_6_5
    · decide +kernel
    · decide +kernel
    · exact block_3_7_0
    · exact block_3_7_1
    · exact block_3_7_2
    · exact block_3_7_3
    · exact block_3_7_4
    · exact block_3_7_5
    · decide +kernel
    · decide +kernel
    · exact block_3_8_0
    · exact block_3_8_1
    · exact block_3_8_2
    · exact block_3_8_3
    · exact block_3_8_4
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact block_3_9_0
    · exact block_3_9_1
    · exact block_3_9_2
    · exact block_3_9_3
    · exact block_3_9_4
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact block_3_10_0
    · exact block_3_10_1
    · exact block_3_10_2
    · exact block_3_10_3
    · exact block_3_10_4
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact block_3_11_0
    · exact block_3_11_1
    · exact block_3_11_2
    · exact block_3_11_3
    · exact block_3_11_4
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact block_3_12_0
    · exact block_3_12_1
    · exact block_3_12_2
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact block_3_13_0
    · exact block_3_13_1
    · exact block_3_13_2
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact block_3_14_0
    · exact block_3_14_1
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact block_3_15_0
    · exact block_3_15_1
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact block_3_16_0
    · exact block_3_16_1
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact block_3_17_0
    · exact block_3_17_1
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
end CycleQ2SegreModularBasepointData
#print axioms CycleQ2SegreModularBasepointData.identity3
end


