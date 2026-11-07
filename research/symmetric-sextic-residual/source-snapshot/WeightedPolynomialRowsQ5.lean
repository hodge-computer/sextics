import WeightedPolynomialData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace WeightedSupport.PolynomialModel

theorem Q_coefficient_row_50 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 50) = CheckedRank.QMatrix 50 j := by
  decide +kernel

theorem Q_coefficient_row_51 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 51) = CheckedRank.QMatrix 51 j := by
  decide +kernel

theorem Q_coefficient_row_52 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 52) = CheckedRank.QMatrix 52 j := by
  decide +kernel

theorem Q_coefficient_row_53 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 53) = CheckedRank.QMatrix 53 j := by
  decide +kernel

theorem Q_coefficient_row_54 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 54) = CheckedRank.QMatrix 54 j := by
  decide +kernel

theorem Q_coefficient_row_55 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 55) = CheckedRank.QMatrix 55 j := by
  decide +kernel

theorem Q_coefficient_row_56 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 56) = CheckedRank.QMatrix 56 j := by
  decide +kernel

theorem Q_coefficient_row_57 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 57) = CheckedRank.QMatrix 57 j := by
  decide +kernel

theorem Q_coefficient_row_58 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 58) = CheckedRank.QMatrix 58 j := by
  decide +kernel

theorem Q_coefficient_row_59 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 59) = CheckedRank.QMatrix 59 j := by
  decide +kernel

#print axioms Q_coefficient_row_50
end WeightedSupport.PolynomialModel
