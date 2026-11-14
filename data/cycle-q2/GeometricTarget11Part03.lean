import Proposal.GeometricTarget11Part02

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


/- Uncompiled continuation: GeometricBridgeAlgebra.lean (2026-11-12). -/
section Q2UncompiledHiggsBridge

/-!
# Self-adjoint projectors on the actual Fermat Jacobian component

This file supplies an algebraic step in the reconstructed geometric argument.
The existing finite theorem `CycleQ2FermatHiggs.compatible_projector_trivial`
concerns matrices. Here it is applied to endomorphisms of the actual
`CycleQ2FermatJacobian.gradedPiece 6 1`, using the actual socle triple-product
pairings and the already constructed monomial basis.

In particular, the compatibility premise below is an equality in the actual
Fermat derivative quotient, not a premise asserting geometric support or
existence of a residue primitive. Interpreting a geometric polarized sub-VHS
projector as one of these endomorphisms remains a separate geometric theorem.

Written against the recorded project sources and the pinned mathlib source
at 0df444a360eaa60ab8c11dca51a86af692955474. Development compilation status
is recorded in solution.md.
-/

set_option autoImplicit false

noncomputable section

namespace CycleQ2GeometricBridgeAlgebra

open CycleQ2FermatJacobian

open scoped BigOperators

/-- The actual degree-six character-one component of the Fermat quotient. -/
abbrev InvariantHodgeModel := gradedPiece 6 1

/-- The actual degree-six character-zero deformation component. -/
abbrev InvariantTangentModel := gradedPiece 6 0

/-- The triple-product form on the actual quotient, linear in both inputs.
The names of the models indicate their intended geometric interpretation;
no Hodge-theoretic comparison is assumed or asserted in this definition. -/
def actualTracePairing (t : InvariantTangentModel) :
    InvariantHodgeModel →ₗ[ℂ] InvariantHodgeModel →ₗ[ℂ] ℂ where
  toFun u :=
    { toFun := fun v =>
        socleTrace ((u : JacobianRing) * (v : JacobianRing) * (t : JacobianRing))
      map_add' := by
        intro v w
        simp [mul_add, add_mul]
      map_smul' := by
        intro c v
        simp [mul_smul_comm, smul_mul_assoc] }
  map_add' := by
    intro u v
    ext w
    simp [add_mul]
  map_smul' := by
    intro c u
    ext v
    simp [smul_mul_assoc]

@[simp] theorem actualTracePairing_apply (t : InvariantTangentModel)
    (u v : InvariantHodgeModel) :
    actualTracePairing t u v =
      socleTrace ((u : JacobianRing) * (v : JacobianRing) * (t : JacobianRing)) :=
  rfl

theorem actualTracePairing_symmetric (t : InvariantTangentModel)
    (u v : InvariantHodgeModel) :
    actualTracePairing t u v = actualTracePairing t v u := by
  change socleTrace ((u : JacobianRing) * (v : JacobianRing) * (t : JacobianRing)) =
    socleTrace ((v : JacobianRing) * (u : JacobianRing) * (t : JacobianRing))
  rw [mul_comm (u : JacobianRing) (v : JacobianRing)]

@[simp] theorem actualTracePairing_flip_apply (t : InvariantTangentModel)
    (u v : InvariantHodgeModel) :
    (actualTracePairing t).flip v u = actualTracePairing t u v :=
  rfl

/-- Its matrices are the already proved finite Fermat Higgs matrices. -/
theorem actualTracePairing_basis (m : Fin 35) (i j : Fin 33) :
    actualTracePairing (degreeSixCharacterZeroBasis m)
      (degreeSixCharacterOneBasis i) (degreeSixCharacterOneBasis j) =
        CycleQ2FermatHiggs.higgsMatrix ℂ m i j :=
  actual_component_trace_matrix m i j

/-- The matrix of an actual endomorphism, with the established quotient basis. -/
def actualEndomorphismMatrix
    (P : Module.End ℂ InvariantHodgeModel) : Matrix (Fin 33) (Fin 33) ℂ :=
  LinearMap.toMatrixAlgEquiv degreeSixCharacterOneBasis P

theorem actualEndomorphismMatrix_apply
    (P : Module.End ℂ InvariantHodgeModel) (i j : Fin 33) :
    actualEndomorphismMatrix P i j =
      degreeSixCharacterOneBasis.repr (P (degreeSixCharacterOneBasis j)) i :=
  LinearMap.toMatrixAlgEquiv_apply degreeSixCharacterOneBasis P i j

theorem actualTracePairing_expand_left (t : InvariantTangentModel)
    (u v : InvariantHodgeModel) :
    actualTracePairing t u v =
      ∑ i : Fin 33, degreeSixCharacterOneBasis.repr u i *
        actualTracePairing t (degreeSixCharacterOneBasis i) v := by
  have h := congrArg ((actualTracePairing t).flip v)
    (degreeSixCharacterOneBasis.sum_repr u)
  simpa only [map_sum, map_smul, actualTracePairing_flip_apply, smul_eq_mul]
    using h.symm

theorem actualTracePairing_expand_right (t : InvariantTangentModel)
    (u v : InvariantHodgeModel) :
    actualTracePairing t u v =
      ∑ i : Fin 33, degreeSixCharacterOneBasis.repr v i *
        actualTracePairing t u (degreeSixCharacterOneBasis i) := by
  have h := congrArg (actualTracePairing t u)
    (degreeSixCharacterOneBasis.sum_repr v)
  simpa only [map_sum, map_smul, smul_eq_mul] using h.symm

/-- The left side of the finite commutant equation is evaluation of the
actual trace pairing after applying the endomorphism to its first input. -/
theorem transpose_mul_higgs_eq_actualTracePairing
    (P : Module.End ℂ InvariantHodgeModel) (m : Fin 35) (i j : Fin 33) :
    ((actualEndomorphismMatrix P).transpose *
        CycleQ2FermatHiggs.higgsMatrix ℂ m) i j =
      actualTracePairing (degreeSixCharacterZeroBasis m)
        (P (degreeSixCharacterOneBasis i)) (degreeSixCharacterOneBasis j) := by
  rw [actualTracePairing_expand_left]
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    actualEndomorphismMatrix_apply, actualTracePairing_basis]

/-- The right side of the finite commutant equation is evaluation after
applying the actual endomorphism to the second input. -/
theorem higgs_mul_eq_actualTracePairing
    (P : Module.End ℂ InvariantHodgeModel) (m : Fin 35) (i j : Fin 33) :
    (CycleQ2FermatHiggs.higgsMatrix ℂ m * actualEndomorphismMatrix P) i j =
      actualTracePairing (degreeSixCharacterZeroBasis m)
        (degreeSixCharacterOneBasis i) (P (degreeSixCharacterOneBasis j)) := by
  rw [actualTracePairing_expand_right]
  simp only [Matrix.mul_apply, actualEndomorphismMatrix_apply,
    actualTracePairing_basis]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

/-- Self-adjointness for the genuine triple-product pairings implies the
finite matrix compatibility equations, with no geometric comparison premise. -/
theorem higgs_equations_of_actual_trace_selfAdjoint
    (P : Module.End ℂ InvariantHodgeModel)
    (hP : ∀ (t : InvariantTangentModel) (u v : InvariantHodgeModel),
      actualTracePairing t (P u) v = actualTracePairing t u (P v)) :
    ∀ m : Fin 35,
      (actualEndomorphismMatrix P).transpose *
          CycleQ2FermatHiggs.higgsMatrix ℂ m =
        CycleQ2FermatHiggs.higgsMatrix ℂ m * actualEndomorphismMatrix P := by
  intro m
  ext i j
  rw [transpose_mul_higgs_eq_actualTracePairing,
    higgs_mul_eq_actualTracePairing]
  exact hP (degreeSixCharacterZeroBasis m)
    (degreeSixCharacterOneBasis i) (degreeSixCharacterOneBasis j)

/-- An idempotent on the actual Fermat component that is self-adjoint for
every actual trace pairing is zero or the identity. This is the algebraic
projector conclusion needed at the Fermat point in the geometric Higgs
argument. It does not assert existence of a geometric subvariation projector. -/
theorem actual_trace_selfAdjoint_projector_trivial
    (P : Module.End ℂ InvariantHodgeModel)
    (hP : ∀ (t : InvariantTangentModel) (u v : InvariantHodgeModel),
      actualTracePairing t (P u) v = actualTracePairing t u (P v))
    (hIdempotent : P * P = P) : P = 0 ∨ P = 1 := by
  let e := LinearMap.toMatrixAlgEquiv degreeSixCharacterOneBasis
  have hMatrix : actualEndomorphismMatrix P * actualEndomorphismMatrix P =
      actualEndomorphismMatrix P := by
    change e P * e P = e P
    rw [← map_mul, hIdempotent]
  rcases CycleQ2FermatHiggs.compatible_projector_trivial
      (actualEndomorphismMatrix P)
      (higgs_equations_of_actual_trace_selfAdjoint P hP) hMatrix with hZero | hOne
  · left
    apply e.injective
    simpa only [actualEndomorphismMatrix, e, map_zero] using hZero
  · right
    apply e.injective
    simpa only [actualEndomorphismMatrix, e, map_one] using hOne

/-- Consequently no proper nonzero image can occur for such a projector. -/
theorem actual_trace_selfAdjoint_projector_range
    (P : Module.End ℂ InvariantHodgeModel)
    (hP : ∀ (t : InvariantTangentModel) (u v : InvariantHodgeModel),
      actualTracePairing t (P u) v = actualTracePairing t u (P v))
    (hIdempotent : P * P = P) :
    LinearMap.range P = ⊥ ∨ LinearMap.range P = ⊤ := by
  rcases actual_trace_selfAdjoint_projector_trivial P hP hIdempotent with hZero | hOne
  · left
    rw [hZero]
    simp
  · right
    rw [hOne]
    simp [Module.End.one_eq_id]

end CycleQ2GeometricBridgeAlgebra

end

end Q2UncompiledHiggsBridge


/- Component: continuation_20261112/SupportedProjectorAlgebra.lean -/
section Q2UncompiledProjectorConstruction

/-!
# Orthogonal generation and polynomial projectors for cycle-q2

DEVELOPMENT CONTINUATION, 12 November 2026. Compilation status is recorded
in solution.md. These lemmas extend the existing actual Fermat trace-pairing
bridge. They do not define a geometric variation of Hodge structure or an
algebraic cycle class map, and they do not prove residue exactness.

This component continues the actual Fermat trace-pairing bridge above.
-/

set_option autoImplicit false

noncomputable section

namespace CycleQ2GeometricBridgeAlgebra

/-- A common orthogonal direct sum for the actual socle pairings gives an
actual self-adjoint projection. The projection is constructed from the two
submodules; it is not supplied as an additional hypothesis. -/
theorem actual_trace_projection_selfAdjoint
    (U W : Submodule ℂ InvariantHodgeModel) (hUW : IsCompl U W)
    (horth : ∀ (t : InvariantTangentModel) (u : U) (w : W),
      actualTracePairing t (u : InvariantHodgeModel)
        (w : InvariantHodgeModel) = 0) :
    ∀ (t : InvariantTangentModel) (u v : InvariantHodgeModel),
      actualTracePairing t (U.projection W hUW u) v =
        actualTracePairing t u (U.projection W hUW v) := by
  intro t u v
  obtain ⟨u₁, u₂, hu, _⟩ := Submodule.existsUnique_add_of_isCompl hUW u
  obtain ⟨v₁, v₂, hv, _⟩ := Submodule.existsUnique_add_of_isCompl hUW v
  have hcross : actualTracePairing t (u₂ : InvariantHodgeModel)
      (v₁ : InvariantHodgeModel) = 0 := by
    rw [actualTracePairing_symmetric]
    exact horth t v₁ u₂
  rw [← hu, ← hv]
  simp only [map_add, LinearMap.add_apply,
    Submodule.projection_apply_left, Submodule.projection_apply_right,
    add_zero, horth t u₁ v₂, hcross]

/-- The finite Higgs result rules out a proper nonzero submodule having a
complement orthogonal for every actual socle pairing. -/
theorem actual_trace_orthogonal_direct_sum_trivial
    (U W : Submodule ℂ InvariantHodgeModel) (hUW : IsCompl U W)
    (horth : ∀ (t : InvariantTangentModel) (u : U) (w : W),
      actualTracePairing t (u : InvariantHodgeModel)
        (w : InvariantHodgeModel) = 0) :
    U = ⊥ ∨ U = ⊤ := by
  have hIdempotent : U.projection W hUW * U.projection W hUW =
      U.projection W hUW :=
    Submodule.isIdempotentElem_projection hUW
  have h := actual_trace_selfAdjoint_projector_range
    (U.projection W hUW)
    (actual_trace_projection_selfAdjoint U W hUW horth) hIdempotent
  simpa only [Submodule.range_projection] using h

/-- Once a geometric construction supplies the common orthogonal complement
of its image in the actual Fermat component, one nonzero image suffices for
surjectivity. The needed orthogonality remains an explicit algebraic premise. -/
theorem actual_trace_orthogonal_range_surjective
    {A : Type*} [AddCommGroup A] [Module ℂ A]
    (f : A →ₗ[ℂ] InvariantHodgeModel)
    (W : Submodule ℂ InvariantHodgeModel)
    (hW : IsCompl (LinearMap.range f) W)
    (horth : ∀ (t : InvariantTangentModel)
      (u : LinearMap.range f) (w : W),
      actualTracePairing t (u : InvariantHodgeModel)
        (w : InvariantHodgeModel) = 0)
    (hf : f ≠ 0) : Function.Surjective f := by
  rcases actual_trace_orthogonal_direct_sum_trivial
      (LinearMap.range f) W hW horth with hZero | hTop
  · exfalso
    apply hf
    apply LinearMap.ext
    intro x
    have hx : f x ∈ LinearMap.range f := ⟨x, rfl⟩
    rw [hZero] at hx
    simpa only [Submodule.mem_bot, LinearMap.zero_apply] using hx
  · exact LinearMap.range_eq_top.mp hTop

end CycleQ2GeometricBridgeAlgebra

namespace CycleQ2SupportedProjectorAlgebra

variable {K : Type*} [Field K]

/-- Normalization of an annihilating polynomial. Its constant coefficient
vanishes if the original constant coefficient is nonzero. -/
def projectorPolynomial (q : Polynomial K) : Polynomial K :=
  1 - Polynomial.C ((q.coeff 0)⁻¹) * q

theorem projectorPolynomial_coeff_zero (q : Polynomial K)
    (hq : q.coeff 0 ≠ 0) : (projectorPolynomial q).coeff 0 = 0 := by
  simp [projectorPolynomial, hq]

/-- Evaluation of the normalized annihilator is the identity. This is valid
in a possibly noncommutative algebra, including an endomorphism algebra. -/
theorem projectorPolynomial_aeval
    {A : Type*} [Ring A] [Algebra K A]
    (M : A) (q : Polynomial K) (hq : Polynomial.aeval M q = 0) :
    Polynomial.aeval M (projectorPolynomial q) = 1 := by
  simp [projectorPolynomial, hq]

section Endomorphisms

variable {V : Type*} [AddCommGroup V] [Module K V]

/-- A polynomial with zero constant coefficient kills every vector killed
by the endomorphism. Factoring by X makes the composition order explicit. -/
theorem aeval_apply_zero_of_coeff_zero
    (M : Module.End K V) (p : Polynomial K) (hp : p.coeff 0 = 0)
    (v : V) (hv : M v = 0) : Polynomial.aeval M p v = 0 := by
  obtain ⟨r, hr⟩ := Polynomial.X_dvd_iff.mpr hp
  rw [hr, mul_comm (Polynomial.X : Polynomial K) r, map_mul,
    Polynomial.aeval_X]
  change Polynomial.aeval M r (M v) = 0
  rw [hv, map_zero]

/-- On the kernel of the chosen annihilator, the normalized polynomial acts
as the identity even if that annihilator does not vanish on the whole space. -/
theorem projectorPolynomial_apply_of_annihilator
    (M : Module.End K V) (q : Polynomial K) (v : V)
    (hv : Polynomial.aeval M q v = 0) :
    Polynomial.aeval M (projectorPolynomial q) v = v := by
  simp only [projectorPolynomial, map_sub, map_one, map_mul,
    Polynomial.aeval_C]
  change v - (algebraMap K (Module.End K V) ((q.coeff 0)⁻¹))
    (Polynomial.aeval M q v) = v
  rw [hv, map_zero, sub_zero]

/-- The normalized polynomial selects one direct summand: its restriction
there is the identity and its restriction to the other summand is zero. -/
theorem projectorPolynomial_aeval_eq_projection
    (M : Module.End K V)
    (U W : Submodule K V) (hUW : IsCompl U W)
    (q : Polynomial K) (hq : q.coeff 0 ≠ 0)
    (hU : ∀ u : U, Polynomial.aeval M q (u : V) = 0)
    (hW : ∀ w : W, M (w : V) = 0) :
    Polynomial.aeval M (projectorPolynomial q) = U.projection W hUW := by
  ext v
  obtain ⟨u, w, hv, _⟩ := Submodule.existsUnique_add_of_isCompl hUW v
  rw [← hv, map_add, map_add, Submodule.projection_apply_left,
    Submodule.projection_apply_right]
  rw [projectorPolynomial_apply_of_annihilator M q (u : V) (hU u),
    aeval_apply_zero_of_coeff_zero M (projectorPolynomial q)
      (projectorPolynomial_coeff_zero q hq) (w : V) (hW w)]

end Endomorphisms

/-- The algebraic support argument needs only closure under sums, scalars,
and composition on the right by M. A zero-constant polynomial in M then
belongs to the same submodule. No algebraic cycle support is defined here. -/
theorem aeval_mem_of_coeff_zero
    {A : Type*} [Ring A] [Algebra K A]
    (S : Submodule K A) (M : A) (hM : M ∈ S)
    (hmul : ∀ N ∈ S, N * M ∈ S)
    (p : Polynomial K) (hp : p.coeff 0 = 0) :
    Polynomial.aeval M p ∈ S := by
  have hpowers (n : ℕ) : M ^ (n + 1) ∈ S := by
    induction n with
    | zero => simpa only [Nat.zero_add, pow_one] using hM
    | succ n ih =>
      simpa only [Nat.succ_eq_add_one, pow_succ] using hmul (M ^ (n + 1)) ih
  rw [Polynomial.aeval_eq_sum_range]
  apply S.sum_mem
  intro n hn
  cases n with
  | zero => simpa only [hp, zero_smul] using S.zero_mem
  | succ n => exact S.smul_mem (p.coeff (n + 1)) (hpowers n)

/-- A supplied algebraic correspondence operator, with its two summands and
annihilator, yields an actual idempotent in any composition-stable submodule
containing that operator. In a geometric application the submodule must be
proved to consist of classes represented on the required divisor square. -/
theorem projection_mem_of_annihilator
    {V : Type*} [AddCommGroup V] [Module K V]
    (S : Submodule K (Module.End K V))
    (M : Module.End K V) (hM : M ∈ S)
    (hmul : ∀ N ∈ S, N * M ∈ S)
    (U W : Submodule K V) (hUW : IsCompl U W)
    (q : Polynomial K) (hq : q.coeff 0 ≠ 0)
    (hU : ∀ u : U, Polynomial.aeval M q (u : V) = 0)
    (hW : ∀ w : W, M (w : V) = 0) :
    U.projection W hUW ∈ S := by
  rw [← projectorPolynomial_aeval_eq_projection M U W hUW q hq hU hW]
  exact aeval_mem_of_coeff_zero S M hM hmul
    (projectorPolynomial q) (projectorPolynomial_coeff_zero q hq)

end CycleQ2SupportedProjectorAlgebra

namespace CycleQ2GeometricBridgeAlgebra

open CycleQ2FermatJacobian
open CycleQ2SupportedProjectorAlgebra

/-- An explicit polynomial in an actual Fermat-component endomorphism.
The minimal polynomial is supplied by Mathlib's algebraic definition; its
annihilation and the nonzero constant term are established below. -/
def actualProjectorPolynomial (M : Module.End ℂ InvariantHodgeModel) :
    Polynomial ℂ :=
  projectorPolynomial (minpoly ℂ M)

theorem actualProjectorPolynomial_coeff_zero
    (M : Module.End ℂ InvariantHodgeModel) (hM : Function.Injective M) :
    (actualProjectorPolynomial M).coeff 0 = 0 := by
  letI : Module.Free ℂ InvariantHodgeModel :=
    Module.Free.of_basis degreeSixCharacterOneBasis
  letI : Module.Finite ℂ InvariantHodgeModel :=
    Module.Finite.of_basis degreeSixCharacterOneBasis
  apply projectorPolynomial_coeff_zero
  exact LinearMap.minpoly_coeff_zero_of_injective hM

theorem actualProjectorPolynomial_aeval
    (M : Module.End ℂ InvariantHodgeModel) :
    Polynomial.aeval M (actualProjectorPolynomial M) = 1 := by
  exact projectorPolynomial_aeval M (minpoly ℂ M) (minpoly.aeval ℂ M)

/-- Injectivity on the actual 33-dimensional quotient component supplies an
identity polynomial with no constant term. This is the finite-dimensional
algebra needed to keep the projector inside a divisor-supported span. -/
theorem actual_zero_constant_polynomial_identity
    (M : Module.End ℂ InvariantHodgeModel) (hM : Function.Injective M) :
    ∃ p : Polynomial ℂ, p.coeff 0 = 0 ∧ Polynomial.aeval M p = 1 :=
  ⟨actualProjectorPolynomial M, actualProjectorPolynomial_coeff_zero M hM,
    actualProjectorPolynomial_aeval M⟩

/-- The actual identity is in every composition-stable submodule of
endomorphisms containing an injective operator. Establishing the geometric
support interpretation of such a submodule remains a separate theorem. -/
theorem actual_identity_mem_of_composition_stable
    (S : Submodule ℂ (Module.End ℂ InvariantHodgeModel))
    (M : Module.End ℂ InvariantHodgeModel) (hM : M ∈ S)
    (hmul : ∀ N ∈ S, N * M ∈ S)
    (hInjective : Function.Injective M) :
    (1 : Module.End ℂ InvariantHodgeModel) ∈ S := by
  obtain ⟨p, hp, hEval⟩ := actual_zero_constant_polynomial_identity M hInjective
  rw [← hEval]
  exact aeval_mem_of_coeff_zero S M hM hmul p hp

end CycleQ2GeometricBridgeAlgebra

end

end Q2UncompiledProjectorConstruction


