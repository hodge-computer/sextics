import WeightedPolynomialData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace WeightedSupport.PolynomialModel

theorem HQ_coefficient_row_0 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 0) = CheckedRank.HQMatrix 0 j := by
  decide +kernel

theorem HQ_coefficient_row_1 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 1) = CheckedRank.HQMatrix 1 j := by
  decide +kernel

theorem HQ_coefficient_row_2 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 2) = CheckedRank.HQMatrix 2 j := by
  decide +kernel

theorem HQ_coefficient_row_3 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 3) = CheckedRank.HQMatrix 3 j := by
  decide +kernel

theorem HQ_coefficient_row_4 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 4) = CheckedRank.HQMatrix 4 j := by
  decide +kernel

theorem HQ_coefficient_row_5 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 5) = CheckedRank.HQMatrix 5 j := by
  decide +kernel

theorem HQ_coefficient_row_6 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 6) = CheckedRank.HQMatrix 6 j := by
  decide +kernel

theorem HQ_coefficient_row_7 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 7) = CheckedRank.HQMatrix 7 j := by
  decide +kernel

theorem HQ_coefficient_row_8 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 8) = CheckedRank.HQMatrix 8 j := by
  decide +kernel

theorem HQ_coefficient_row_9 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 9) = CheckedRank.HQMatrix 9 j := by
  decide +kernel

#print axioms HQ_coefficient_row_0
end WeightedSupport.PolynomialModel
