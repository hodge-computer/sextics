import WeightedPolynomialRowsQ0
import WeightedPolynomialRowsQ1
import WeightedPolynomialRowsQ2
import WeightedPolynomialRowsQ3
import WeightedPolynomialRowsQ4
import WeightedPolynomialRowsQ5
import WeightedPolynomialRowsQ6
import WeightedPolynomialRowsQ7
import WeightedPolynomialRowsQ8
import WeightedPolynomialRowsQ9
import WeightedPolynomialRowsQ10
import WeightedPolynomialRowsQ11
import WeightedPolynomialRowsHQ0
import WeightedPolynomialRowsHQ1
import WeightedPolynomialRowsHQ2
import WeightedPolynomialRowsHQ3
import WeightedPolynomialRowsHQ4
import WeightedPolynomialRowsHQ5
import WeightedPolynomialRowsHQ6
import WeightedPolynomialRowsHQ7
import WeightedRank
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace WeightedSupport.PolynomialModel
open MvPolynomial

theorem Q_arithmetic_binding (i : Fin 120) (j : Fin 82) :
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent i) = CheckedRank.QMatrix i j := by
  fin_cases i
  · exact Q_coefficient_row_0 j
  · exact Q_coefficient_row_1 j
  · exact Q_coefficient_row_2 j
  · exact Q_coefficient_row_3 j
  · exact Q_coefficient_row_4 j
  · exact Q_coefficient_row_5 j
  · exact Q_coefficient_row_6 j
  · exact Q_coefficient_row_7 j
  · exact Q_coefficient_row_8 j
  · exact Q_coefficient_row_9 j
  · exact Q_coefficient_row_10 j
  · exact Q_coefficient_row_11 j
  · exact Q_coefficient_row_12 j
  · exact Q_coefficient_row_13 j
  · exact Q_coefficient_row_14 j
  · exact Q_coefficient_row_15 j
  · exact Q_coefficient_row_16 j
  · exact Q_coefficient_row_17 j
  · exact Q_coefficient_row_18 j
  · exact Q_coefficient_row_19 j
  · exact Q_coefficient_row_20 j
  · exact Q_coefficient_row_21 j
  · exact Q_coefficient_row_22 j
  · exact Q_coefficient_row_23 j
  · exact Q_coefficient_row_24 j
  · exact Q_coefficient_row_25 j
  · exact Q_coefficient_row_26 j
  · exact Q_coefficient_row_27 j
  · exact Q_coefficient_row_28 j
  · exact Q_coefficient_row_29 j
  · exact Q_coefficient_row_30 j
  · exact Q_coefficient_row_31 j
  · exact Q_coefficient_row_32 j
  · exact Q_coefficient_row_33 j
  · exact Q_coefficient_row_34 j
  · exact Q_coefficient_row_35 j
  · exact Q_coefficient_row_36 j
  · exact Q_coefficient_row_37 j
  · exact Q_coefficient_row_38 j
  · exact Q_coefficient_row_39 j
  · exact Q_coefficient_row_40 j
  · exact Q_coefficient_row_41 j
  · exact Q_coefficient_row_42 j
  · exact Q_coefficient_row_43 j
  · exact Q_coefficient_row_44 j
  · exact Q_coefficient_row_45 j
  · exact Q_coefficient_row_46 j
  · exact Q_coefficient_row_47 j
  · exact Q_coefficient_row_48 j
  · exact Q_coefficient_row_49 j
  · exact Q_coefficient_row_50 j
  · exact Q_coefficient_row_51 j
  · exact Q_coefficient_row_52 j
  · exact Q_coefficient_row_53 j
  · exact Q_coefficient_row_54 j
  · exact Q_coefficient_row_55 j
  · exact Q_coefficient_row_56 j
  · exact Q_coefficient_row_57 j
  · exact Q_coefficient_row_58 j
  · exact Q_coefficient_row_59 j
  · exact Q_coefficient_row_60 j
  · exact Q_coefficient_row_61 j
  · exact Q_coefficient_row_62 j
  · exact Q_coefficient_row_63 j
  · exact Q_coefficient_row_64 j
  · exact Q_coefficient_row_65 j
  · exact Q_coefficient_row_66 j
  · exact Q_coefficient_row_67 j
  · exact Q_coefficient_row_68 j
  · exact Q_coefficient_row_69 j
  · exact Q_coefficient_row_70 j
  · exact Q_coefficient_row_71 j
  · exact Q_coefficient_row_72 j
  · exact Q_coefficient_row_73 j
  · exact Q_coefficient_row_74 j
  · exact Q_coefficient_row_75 j
  · exact Q_coefficient_row_76 j
  · exact Q_coefficient_row_77 j
  · exact Q_coefficient_row_78 j
  · exact Q_coefficient_row_79 j
  · exact Q_coefficient_row_80 j
  · exact Q_coefficient_row_81 j
  · exact Q_coefficient_row_82 j
  · exact Q_coefficient_row_83 j
  · exact Q_coefficient_row_84 j
  · exact Q_coefficient_row_85 j
  · exact Q_coefficient_row_86 j
  · exact Q_coefficient_row_87 j
  · exact Q_coefficient_row_88 j
  · exact Q_coefficient_row_89 j
  · exact Q_coefficient_row_90 j
  · exact Q_coefficient_row_91 j
  · exact Q_coefficient_row_92 j
  · exact Q_coefficient_row_93 j
  · exact Q_coefficient_row_94 j
  · exact Q_coefficient_row_95 j
  · exact Q_coefficient_row_96 j
  · exact Q_coefficient_row_97 j
  · exact Q_coefficient_row_98 j
  · exact Q_coefficient_row_99 j
  · exact Q_coefficient_row_100 j
  · exact Q_coefficient_row_101 j
  · exact Q_coefficient_row_102 j
  · exact Q_coefficient_row_103 j
  · exact Q_coefficient_row_104 j
  · exact Q_coefficient_row_105 j
  · exact Q_coefficient_row_106 j
  · exact Q_coefficient_row_107 j
  · exact Q_coefficient_row_108 j
  · exact Q_coefficient_row_109 j
  · exact Q_coefficient_row_110 j
  · exact Q_coefficient_row_111 j
  · exact Q_coefficient_row_112 j
  · exact Q_coefficient_row_113 j
  · exact Q_coefficient_row_114 j
  · exact Q_coefficient_row_115 j
  · exact Q_coefficient_row_116 j
  · exact Q_coefficient_row_117 j
  · exact Q_coefficient_row_118 j
  · exact Q_coefficient_row_119 j

noncomputable def QCoefficientMatrix : Matrix (Fin 120) (Fin 82) ℤ :=
  fun i j => coeff (exponent (qTargetExponent i)) (Q * orbitPolynomial (sourceExponent j))

theorem Q_polynomial_matrix_eq : QCoefficientMatrix = CheckedRank.QMatrix := by
  ext i j
  change coeff (exponent (qTargetExponent i)) (Q * orbitPolynomial (sourceExponent j)) = _
  rw [coeff_Q_orbit]
  exact Q_arithmetic_binding i j

theorem Q_polynomial_rational_rank :
    (QCoefficientMatrix.map (Int.castRingHom ℚ)).rank = 82 := by
  rw [Q_polynomial_matrix_eq]
  exact CheckedRank.Q_rational_rank

#print axioms Q_polynomial_matrix_eq
#print axioms Q_polynomial_rational_rank

theorem HQ_arithmetic_binding (i : Fin 74) (j : Fin 82) :
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent i) = CheckedRank.HQMatrix i j := by
  fin_cases i
  · exact HQ_coefficient_row_0 j
  · exact HQ_coefficient_row_1 j
  · exact HQ_coefficient_row_2 j
  · exact HQ_coefficient_row_3 j
  · exact HQ_coefficient_row_4 j
  · exact HQ_coefficient_row_5 j
  · exact HQ_coefficient_row_6 j
  · exact HQ_coefficient_row_7 j
  · exact HQ_coefficient_row_8 j
  · exact HQ_coefficient_row_9 j
  · exact HQ_coefficient_row_10 j
  · exact HQ_coefficient_row_11 j
  · exact HQ_coefficient_row_12 j
  · exact HQ_coefficient_row_13 j
  · exact HQ_coefficient_row_14 j
  · exact HQ_coefficient_row_15 j
  · exact HQ_coefficient_row_16 j
  · exact HQ_coefficient_row_17 j
  · exact HQ_coefficient_row_18 j
  · exact HQ_coefficient_row_19 j
  · exact HQ_coefficient_row_20 j
  · exact HQ_coefficient_row_21 j
  · exact HQ_coefficient_row_22 j
  · exact HQ_coefficient_row_23 j
  · exact HQ_coefficient_row_24 j
  · exact HQ_coefficient_row_25 j
  · exact HQ_coefficient_row_26 j
  · exact HQ_coefficient_row_27 j
  · exact HQ_coefficient_row_28 j
  · exact HQ_coefficient_row_29 j
  · exact HQ_coefficient_row_30 j
  · exact HQ_coefficient_row_31 j
  · exact HQ_coefficient_row_32 j
  · exact HQ_coefficient_row_33 j
  · exact HQ_coefficient_row_34 j
  · exact HQ_coefficient_row_35 j
  · exact HQ_coefficient_row_36 j
  · exact HQ_coefficient_row_37 j
  · exact HQ_coefficient_row_38 j
  · exact HQ_coefficient_row_39 j
  · exact HQ_coefficient_row_40 j
  · exact HQ_coefficient_row_41 j
  · exact HQ_coefficient_row_42 j
  · exact HQ_coefficient_row_43 j
  · exact HQ_coefficient_row_44 j
  · exact HQ_coefficient_row_45 j
  · exact HQ_coefficient_row_46 j
  · exact HQ_coefficient_row_47 j
  · exact HQ_coefficient_row_48 j
  · exact HQ_coefficient_row_49 j
  · exact HQ_coefficient_row_50 j
  · exact HQ_coefficient_row_51 j
  · exact HQ_coefficient_row_52 j
  · exact HQ_coefficient_row_53 j
  · exact HQ_coefficient_row_54 j
  · exact HQ_coefficient_row_55 j
  · exact HQ_coefficient_row_56 j
  · exact HQ_coefficient_row_57 j
  · exact HQ_coefficient_row_58 j
  · exact HQ_coefficient_row_59 j
  · exact HQ_coefficient_row_60 j
  · exact HQ_coefficient_row_61 j
  · exact HQ_coefficient_row_62 j
  · exact HQ_coefficient_row_63 j
  · exact HQ_coefficient_row_64 j
  · exact HQ_coefficient_row_65 j
  · exact HQ_coefficient_row_66 j
  · exact HQ_coefficient_row_67 j
  · exact HQ_coefficient_row_68 j
  · exact HQ_coefficient_row_69 j
  · exact HQ_coefficient_row_70 j
  · exact HQ_coefficient_row_71 j
  · exact HQ_coefficient_row_72 j
  · exact HQ_coefficient_row_73 j

noncomputable def HQCoefficientMatrix : Matrix (Fin 74) (Fin 82) ℤ :=
  fun i j => coeff (exponent (hqTargetExponent i)) ((H * Q) * orbitPolynomial (sourceExponent j))

theorem HQ_polynomial_matrix_eq : HQCoefficientMatrix = CheckedRank.HQMatrix := by
  ext i j
  change coeff (exponent (hqTargetExponent i)) ((H * Q) * orbitPolynomial (sourceExponent j)) = _
  rw [coeff_HQ_orbit]
  exact HQ_arithmetic_binding i j

theorem HQ_polynomial_rational_rank :
    (HQCoefficientMatrix.map (Int.castRingHom ℚ)).rank = 74 := by
  rw [HQ_polynomial_matrix_eq]
  exact CheckedRank.HQ_rational_rank

#print axioms HQ_polynomial_matrix_eq
#print axioms HQ_polynomial_rational_rank

end WeightedSupport.PolynomialModel
