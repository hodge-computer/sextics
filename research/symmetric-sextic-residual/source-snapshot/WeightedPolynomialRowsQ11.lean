import WeightedPolynomialData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace WeightedSupport.PolynomialModel

theorem Q_coefficient_row_110 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 110) = CheckedRank.QMatrix 110 j := by
  decide +kernel

theorem Q_coefficient_row_111 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 111) = CheckedRank.QMatrix 111 j := by
  decide +kernel

theorem Q_coefficient_row_112 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 112) = CheckedRank.QMatrix 112 j := by
  decide +kernel

theorem Q_coefficient_row_113 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 113) = CheckedRank.QMatrix 113 j := by
  decide +kernel

theorem Q_coefficient_row_114 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 114) = CheckedRank.QMatrix 114 j := by
  decide +kernel

theorem Q_coefficient_row_115 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 115) = CheckedRank.QMatrix 115 j := by
  decide +kernel

theorem Q_coefficient_row_116 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 116) = CheckedRank.QMatrix 116 j := by
  decide +kernel

theorem Q_coefficient_row_117 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 117) = CheckedRank.QMatrix 117 j := by
  decide +kernel

theorem Q_coefficient_row_118 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 118) = CheckedRank.QMatrix 118 j := by
  decide +kernel

theorem Q_coefficient_row_119 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 119) = CheckedRank.QMatrix 119 j := by
  decide +kernel

#print axioms Q_coefficient_row_110
end WeightedSupport.PolynomialModel
