import WeightedPolynomialData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace WeightedSupport.PolynomialModel

theorem HQ_coefficient_row_60 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 60) = CheckedRank.HQMatrix 60 j := by
  decide +kernel

theorem HQ_coefficient_row_61 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 61) = CheckedRank.HQMatrix 61 j := by
  decide +kernel

theorem HQ_coefficient_row_62 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 62) = CheckedRank.HQMatrix 62 j := by
  decide +kernel

theorem HQ_coefficient_row_63 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 63) = CheckedRank.HQMatrix 63 j := by
  decide +kernel

theorem HQ_coefficient_row_64 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 64) = CheckedRank.HQMatrix 64 j := by
  decide +kernel

theorem HQ_coefficient_row_65 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 65) = CheckedRank.HQMatrix 65 j := by
  decide +kernel

theorem HQ_coefficient_row_66 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 66) = CheckedRank.HQMatrix 66 j := by
  decide +kernel

theorem HQ_coefficient_row_67 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 67) = CheckedRank.HQMatrix 67 j := by
  decide +kernel

theorem HQ_coefficient_row_68 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 68) = CheckedRank.HQMatrix 68 j := by
  decide +kernel

theorem HQ_coefficient_row_69 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 69) = CheckedRank.HQMatrix 69 j := by
  decide +kernel

#print axioms HQ_coefficient_row_60
end WeightedSupport.PolynomialModel
