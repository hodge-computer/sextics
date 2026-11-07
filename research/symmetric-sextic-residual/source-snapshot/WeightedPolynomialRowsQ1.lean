import WeightedPolynomialData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace WeightedSupport.PolynomialModel

theorem Q_coefficient_row_10 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 10) = CheckedRank.QMatrix 10 j := by
  decide +kernel

theorem Q_coefficient_row_11 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 11) = CheckedRank.QMatrix 11 j := by
  decide +kernel

theorem Q_coefficient_row_12 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 12) = CheckedRank.QMatrix 12 j := by
  decide +kernel

theorem Q_coefficient_row_13 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 13) = CheckedRank.QMatrix 13 j := by
  decide +kernel

theorem Q_coefficient_row_14 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 14) = CheckedRank.QMatrix 14 j := by
  decide +kernel

theorem Q_coefficient_row_15 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 15) = CheckedRank.QMatrix 15 j := by
  decide +kernel

theorem Q_coefficient_row_16 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 16) = CheckedRank.QMatrix 16 j := by
  decide +kernel

theorem Q_coefficient_row_17 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 17) = CheckedRank.QMatrix 17 j := by
  decide +kernel

theorem Q_coefficient_row_18 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 18) = CheckedRank.QMatrix 18 j := by
  decide +kernel

theorem Q_coefficient_row_19 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 19) = CheckedRank.QMatrix 19 j := by
  decide +kernel

#print axioms Q_coefficient_row_10
end WeightedSupport.PolynomialModel
