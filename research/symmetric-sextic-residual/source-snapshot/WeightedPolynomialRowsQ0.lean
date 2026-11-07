import WeightedPolynomialData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace WeightedSupport.PolynomialModel

theorem Q_coefficient_row_0 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 0) = CheckedRank.QMatrix 0 j := by
  decide +kernel

theorem Q_coefficient_row_1 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 1) = CheckedRank.QMatrix 1 j := by
  decide +kernel

theorem Q_coefficient_row_2 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 2) = CheckedRank.QMatrix 2 j := by
  decide +kernel

theorem Q_coefficient_row_3 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 3) = CheckedRank.QMatrix 3 j := by
  decide +kernel

theorem Q_coefficient_row_4 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 4) = CheckedRank.QMatrix 4 j := by
  decide +kernel

theorem Q_coefficient_row_5 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 5) = CheckedRank.QMatrix 5 j := by
  decide +kernel

theorem Q_coefficient_row_6 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 6) = CheckedRank.QMatrix 6 j := by
  decide +kernel

theorem Q_coefficient_row_7 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 7) = CheckedRank.QMatrix 7 j := by
  decide +kernel

theorem Q_coefficient_row_8 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 8) = CheckedRank.QMatrix 8 j := by
  decide +kernel

theorem Q_coefficient_row_9 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 9) = CheckedRank.QMatrix 9 j := by
  decide +kernel

#print axioms Q_coefficient_row_0
end WeightedSupport.PolynomialModel
