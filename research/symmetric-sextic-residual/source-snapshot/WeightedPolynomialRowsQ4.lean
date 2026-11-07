import WeightedPolynomialData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace WeightedSupport.PolynomialModel

theorem Q_coefficient_row_40 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 40) = CheckedRank.QMatrix 40 j := by
  decide +kernel

theorem Q_coefficient_row_41 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 41) = CheckedRank.QMatrix 41 j := by
  decide +kernel

theorem Q_coefficient_row_42 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 42) = CheckedRank.QMatrix 42 j := by
  decide +kernel

theorem Q_coefficient_row_43 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 43) = CheckedRank.QMatrix 43 j := by
  decide +kernel

theorem Q_coefficient_row_44 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 44) = CheckedRank.QMatrix 44 j := by
  decide +kernel

theorem Q_coefficient_row_45 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 45) = CheckedRank.QMatrix 45 j := by
  decide +kernel

theorem Q_coefficient_row_46 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 46) = CheckedRank.QMatrix 46 j := by
  decide +kernel

theorem Q_coefficient_row_47 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 47) = CheckedRank.QMatrix 47 j := by
  decide +kernel

theorem Q_coefficient_row_48 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 48) = CheckedRank.QMatrix 48 j := by
  decide +kernel

theorem Q_coefficient_row_49 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 49) = CheckedRank.QMatrix 49 j := by
  decide +kernel

#print axioms Q_coefficient_row_40
end WeightedSupport.PolynomialModel
