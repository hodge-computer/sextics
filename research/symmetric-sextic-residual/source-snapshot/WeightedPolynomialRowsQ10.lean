import WeightedPolynomialData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace WeightedSupport.PolynomialModel

theorem Q_coefficient_row_100 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 100) = CheckedRank.QMatrix 100 j := by
  decide +kernel

theorem Q_coefficient_row_101 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 101) = CheckedRank.QMatrix 101 j := by
  decide +kernel

theorem Q_coefficient_row_102 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 102) = CheckedRank.QMatrix 102 j := by
  decide +kernel

theorem Q_coefficient_row_103 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 103) = CheckedRank.QMatrix 103 j := by
  decide +kernel

theorem Q_coefficient_row_104 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 104) = CheckedRank.QMatrix 104 j := by
  decide +kernel

theorem Q_coefficient_row_105 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 105) = CheckedRank.QMatrix 105 j := by
  decide +kernel

theorem Q_coefficient_row_106 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 106) = CheckedRank.QMatrix 106 j := by
  decide +kernel

theorem Q_coefficient_row_107 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 107) = CheckedRank.QMatrix 107 j := by
  decide +kernel

theorem Q_coefficient_row_108 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 108) = CheckedRank.QMatrix 108 j := by
  decide +kernel

theorem Q_coefficient_row_109 : ∀ j : Fin 82,
    orbitCoeff qCoeff (sourceExponent j) (qTargetExponent 109) = CheckedRank.QMatrix 109 j := by
  decide +kernel

#print axioms Q_coefficient_row_100
end WeightedSupport.PolynomialModel
