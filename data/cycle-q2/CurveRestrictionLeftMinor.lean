import Proposal.CurveRestrictionLeftColumns

/-! # The coefficient matrix and inverse checks for the left restriction minor -/

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
