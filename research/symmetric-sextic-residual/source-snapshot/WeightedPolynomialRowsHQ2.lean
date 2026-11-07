import WeightedPolynomialData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace WeightedSupport.PolynomialModel

theorem HQ_coefficient_row_20 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 20) = CheckedRank.HQMatrix 20 j := by
  decide +kernel

theorem HQ_coefficient_row_21 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 21) = CheckedRank.HQMatrix 21 j := by
  decide +kernel

theorem HQ_coefficient_row_22 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 22) = CheckedRank.HQMatrix 22 j := by
  decide +kernel

theorem HQ_coefficient_row_23 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 23) = CheckedRank.HQMatrix 23 j := by
  decide +kernel

theorem HQ_coefficient_row_24 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 24) = CheckedRank.HQMatrix 24 j := by
  decide +kernel

theorem HQ_coefficient_row_25 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 25) = CheckedRank.HQMatrix 25 j := by
  decide +kernel

theorem HQ_coefficient_row_26 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 26) = CheckedRank.HQMatrix 26 j := by
  decide +kernel

theorem HQ_coefficient_row_27 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 27) = CheckedRank.HQMatrix 27 j := by
  decide +kernel

theorem HQ_coefficient_row_28 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 28) = CheckedRank.HQMatrix 28 j := by
  decide +kernel

theorem HQ_coefficient_row_29 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 29) = CheckedRank.HQMatrix 29 j := by
  decide +kernel

#print axioms HQ_coefficient_row_20
end WeightedSupport.PolynomialModel
