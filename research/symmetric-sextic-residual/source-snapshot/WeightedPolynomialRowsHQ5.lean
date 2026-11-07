import WeightedPolynomialData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace WeightedSupport.PolynomialModel

theorem HQ_coefficient_row_50 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 50) = CheckedRank.HQMatrix 50 j := by
  decide +kernel

theorem HQ_coefficient_row_51 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 51) = CheckedRank.HQMatrix 51 j := by
  decide +kernel

theorem HQ_coefficient_row_52 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 52) = CheckedRank.HQMatrix 52 j := by
  decide +kernel

theorem HQ_coefficient_row_53 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 53) = CheckedRank.HQMatrix 53 j := by
  decide +kernel

theorem HQ_coefficient_row_54 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 54) = CheckedRank.HQMatrix 54 j := by
  decide +kernel

theorem HQ_coefficient_row_55 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 55) = CheckedRank.HQMatrix 55 j := by
  decide +kernel

theorem HQ_coefficient_row_56 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 56) = CheckedRank.HQMatrix 56 j := by
  decide +kernel

theorem HQ_coefficient_row_57 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 57) = CheckedRank.HQMatrix 57 j := by
  decide +kernel

theorem HQ_coefficient_row_58 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 58) = CheckedRank.HQMatrix 58 j := by
  decide +kernel

theorem HQ_coefficient_row_59 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 59) = CheckedRank.HQMatrix 59 j := by
  decide +kernel

#print axioms HQ_coefficient_row_50
end WeightedSupport.PolynomialModel
