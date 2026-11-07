import WeightedPolynomialData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace WeightedSupport.PolynomialModel

theorem Q_coefficient_row_20 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 20) = CheckedRank.QMatrix 20 j := by
  decide +kernel

theorem Q_coefficient_row_21 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 21) = CheckedRank.QMatrix 21 j := by
  decide +kernel

theorem Q_coefficient_row_22 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 22) = CheckedRank.QMatrix 22 j := by
  decide +kernel

theorem Q_coefficient_row_23 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 23) = CheckedRank.QMatrix 23 j := by
  decide +kernel

theorem Q_coefficient_row_24 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 24) = CheckedRank.QMatrix 24 j := by
  decide +kernel

theorem Q_coefficient_row_25 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 25) = CheckedRank.QMatrix 25 j := by
  decide +kernel

theorem Q_coefficient_row_26 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 26) = CheckedRank.QMatrix 26 j := by
  decide +kernel

theorem Q_coefficient_row_27 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 27) = CheckedRank.QMatrix 27 j := by
  decide +kernel

theorem Q_coefficient_row_28 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 28) = CheckedRank.QMatrix 28 j := by
  decide +kernel

theorem Q_coefficient_row_29 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 29) = CheckedRank.QMatrix 29 j := by
  decide +kernel

#print axioms Q_coefficient_row_20
end WeightedSupport.PolynomialModel
