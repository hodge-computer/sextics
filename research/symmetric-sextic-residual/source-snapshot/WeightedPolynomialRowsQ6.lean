import WeightedPolynomialData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace WeightedSupport.PolynomialModel

theorem Q_coefficient_row_60 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 60) = CheckedRank.QMatrix 60 j := by
  decide +kernel

theorem Q_coefficient_row_61 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 61) = CheckedRank.QMatrix 61 j := by
  decide +kernel

theorem Q_coefficient_row_62 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 62) = CheckedRank.QMatrix 62 j := by
  decide +kernel

theorem Q_coefficient_row_63 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 63) = CheckedRank.QMatrix 63 j := by
  decide +kernel

theorem Q_coefficient_row_64 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 64) = CheckedRank.QMatrix 64 j := by
  decide +kernel

theorem Q_coefficient_row_65 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 65) = CheckedRank.QMatrix 65 j := by
  decide +kernel

theorem Q_coefficient_row_66 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 66) = CheckedRank.QMatrix 66 j := by
  decide +kernel

theorem Q_coefficient_row_67 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 67) = CheckedRank.QMatrix 67 j := by
  decide +kernel

theorem Q_coefficient_row_68 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 68) = CheckedRank.QMatrix 68 j := by
  decide +kernel

theorem Q_coefficient_row_69 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 69) = CheckedRank.QMatrix 69 j := by
  decide +kernel

#print axioms Q_coefficient_row_60
end WeightedSupport.PolynomialModel
