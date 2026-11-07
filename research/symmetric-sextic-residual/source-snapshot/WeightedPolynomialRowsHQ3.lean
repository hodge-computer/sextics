import WeightedPolynomialData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace WeightedSupport.PolynomialModel

theorem HQ_coefficient_row_30 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 30) = CheckedRank.HQMatrix 30 j := by
  decide +kernel

theorem HQ_coefficient_row_31 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 31) = CheckedRank.HQMatrix 31 j := by
  decide +kernel

theorem HQ_coefficient_row_32 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 32) = CheckedRank.HQMatrix 32 j := by
  decide +kernel

theorem HQ_coefficient_row_33 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 33) = CheckedRank.HQMatrix 33 j := by
  decide +kernel

theorem HQ_coefficient_row_34 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 34) = CheckedRank.HQMatrix 34 j := by
  decide +kernel

theorem HQ_coefficient_row_35 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 35) = CheckedRank.HQMatrix 35 j := by
  decide +kernel

theorem HQ_coefficient_row_36 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 36) = CheckedRank.HQMatrix 36 j := by
  decide +kernel

theorem HQ_coefficient_row_37 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 37) = CheckedRank.HQMatrix 37 j := by
  decide +kernel

theorem HQ_coefficient_row_38 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 38) = CheckedRank.HQMatrix 38 j := by
  decide +kernel

theorem HQ_coefficient_row_39 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 39) = CheckedRank.HQMatrix 39 j := by
  decide +kernel

#print axioms HQ_coefficient_row_30
end WeightedSupport.PolynomialModel
