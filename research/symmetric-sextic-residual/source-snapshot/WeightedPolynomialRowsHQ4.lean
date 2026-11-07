import WeightedPolynomialData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace WeightedSupport.PolynomialModel

theorem HQ_coefficient_row_40 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 40) = CheckedRank.HQMatrix 40 j := by
  decide +kernel

theorem HQ_coefficient_row_41 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 41) = CheckedRank.HQMatrix 41 j := by
  decide +kernel

theorem HQ_coefficient_row_42 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 42) = CheckedRank.HQMatrix 42 j := by
  decide +kernel

theorem HQ_coefficient_row_43 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 43) = CheckedRank.HQMatrix 43 j := by
  decide +kernel

theorem HQ_coefficient_row_44 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 44) = CheckedRank.HQMatrix 44 j := by
  decide +kernel

theorem HQ_coefficient_row_45 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 45) = CheckedRank.HQMatrix 45 j := by
  decide +kernel

theorem HQ_coefficient_row_46 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 46) = CheckedRank.HQMatrix 46 j := by
  decide +kernel

theorem HQ_coefficient_row_47 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 47) = CheckedRank.HQMatrix 47 j := by
  decide +kernel

theorem HQ_coefficient_row_48 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 48) = CheckedRank.HQMatrix 48 j := by
  decide +kernel

theorem HQ_coefficient_row_49 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 49) = CheckedRank.HQMatrix 49 j := by
  decide +kernel

#print axioms HQ_coefficient_row_40
end WeightedSupport.PolynomialModel
