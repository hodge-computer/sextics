import WeightedPolynomialData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace WeightedSupport.PolynomialModel

theorem HQ_coefficient_row_10 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 10) = CheckedRank.HQMatrix 10 j := by
  decide +kernel

theorem HQ_coefficient_row_11 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 11) = CheckedRank.HQMatrix 11 j := by
  decide +kernel

theorem HQ_coefficient_row_12 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 12) = CheckedRank.HQMatrix 12 j := by
  decide +kernel

theorem HQ_coefficient_row_13 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 13) = CheckedRank.HQMatrix 13 j := by
  decide +kernel

theorem HQ_coefficient_row_14 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 14) = CheckedRank.HQMatrix 14 j := by
  decide +kernel

theorem HQ_coefficient_row_15 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 15) = CheckedRank.HQMatrix 15 j := by
  decide +kernel

theorem HQ_coefficient_row_16 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 16) = CheckedRank.HQMatrix 16 j := by
  decide +kernel

theorem HQ_coefficient_row_17 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 17) = CheckedRank.HQMatrix 17 j := by
  decide +kernel

theorem HQ_coefficient_row_18 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 18) = CheckedRank.HQMatrix 18 j := by
  decide +kernel

theorem HQ_coefficient_row_19 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 19) = CheckedRank.HQMatrix 19 j := by
  decide +kernel

#print axioms HQ_coefficient_row_10
end WeightedSupport.PolynomialModel
