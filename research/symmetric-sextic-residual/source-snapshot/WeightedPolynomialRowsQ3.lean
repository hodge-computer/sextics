import WeightedPolynomialData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace WeightedSupport.PolynomialModel

theorem Q_coefficient_row_30 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 30) = CheckedRank.QMatrix 30 j := by
  decide +kernel

theorem Q_coefficient_row_31 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 31) = CheckedRank.QMatrix 31 j := by
  decide +kernel

theorem Q_coefficient_row_32 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 32) = CheckedRank.QMatrix 32 j := by
  decide +kernel

theorem Q_coefficient_row_33 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 33) = CheckedRank.QMatrix 33 j := by
  decide +kernel

theorem Q_coefficient_row_34 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 34) = CheckedRank.QMatrix 34 j := by
  decide +kernel

theorem Q_coefficient_row_35 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 35) = CheckedRank.QMatrix 35 j := by
  decide +kernel

theorem Q_coefficient_row_36 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 36) = CheckedRank.QMatrix 36 j := by
  decide +kernel

theorem Q_coefficient_row_37 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 37) = CheckedRank.QMatrix 37 j := by
  decide +kernel

theorem Q_coefficient_row_38 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 38) = CheckedRank.QMatrix 38 j := by
  decide +kernel

theorem Q_coefficient_row_39 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 39) = CheckedRank.QMatrix 39 j := by
  decide +kernel

#print axioms Q_coefficient_row_30
end WeightedSupport.PolynomialModel
