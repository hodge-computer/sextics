import WeightedPolynomialData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace WeightedSupport.PolynomialModel

theorem Q_coefficient_row_90 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 90) = CheckedRank.QMatrix 90 j := by
  decide +kernel

theorem Q_coefficient_row_91 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 91) = CheckedRank.QMatrix 91 j := by
  decide +kernel

theorem Q_coefficient_row_92 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 92) = CheckedRank.QMatrix 92 j := by
  decide +kernel

theorem Q_coefficient_row_93 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 93) = CheckedRank.QMatrix 93 j := by
  decide +kernel

theorem Q_coefficient_row_94 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 94) = CheckedRank.QMatrix 94 j := by
  decide +kernel

theorem Q_coefficient_row_95 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 95) = CheckedRank.QMatrix 95 j := by
  decide +kernel

theorem Q_coefficient_row_96 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 96) = CheckedRank.QMatrix 96 j := by
  decide +kernel

theorem Q_coefficient_row_97 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 97) = CheckedRank.QMatrix 97 j := by
  decide +kernel

theorem Q_coefficient_row_98 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 98) = CheckedRank.QMatrix 98 j := by
  decide +kernel

theorem Q_coefficient_row_99 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 99) = CheckedRank.QMatrix 99 j := by
  decide +kernel

#print axioms Q_coefficient_row_90
end WeightedSupport.PolynomialModel
