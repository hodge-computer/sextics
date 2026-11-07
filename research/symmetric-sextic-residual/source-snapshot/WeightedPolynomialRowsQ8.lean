import WeightedPolynomialData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace WeightedSupport.PolynomialModel

theorem Q_coefficient_row_80 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 80) = CheckedRank.QMatrix 80 j := by
  decide +kernel

theorem Q_coefficient_row_81 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 81) = CheckedRank.QMatrix 81 j := by
  decide +kernel

theorem Q_coefficient_row_82 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 82) = CheckedRank.QMatrix 82 j := by
  decide +kernel

theorem Q_coefficient_row_83 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 83) = CheckedRank.QMatrix 83 j := by
  decide +kernel

theorem Q_coefficient_row_84 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 84) = CheckedRank.QMatrix 84 j := by
  decide +kernel

theorem Q_coefficient_row_85 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 85) = CheckedRank.QMatrix 85 j := by
  decide +kernel

theorem Q_coefficient_row_86 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 86) = CheckedRank.QMatrix 86 j := by
  decide +kernel

theorem Q_coefficient_row_87 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 87) = CheckedRank.QMatrix 87 j := by
  decide +kernel

theorem Q_coefficient_row_88 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 88) = CheckedRank.QMatrix 88 j := by
  decide +kernel

theorem Q_coefficient_row_89 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 89) = CheckedRank.QMatrix 89 j := by
  decide +kernel

#print axioms Q_coefficient_row_80
end WeightedSupport.PolynomialModel
