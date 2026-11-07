import WeightedPolynomialData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace WeightedSupport.PolynomialModel

theorem HQ_coefficient_row_70 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 70) = CheckedRank.HQMatrix 70 j := by
  decide +kernel

theorem HQ_coefficient_row_71 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 71) = CheckedRank.HQMatrix 71 j := by
  decide +kernel

theorem HQ_coefficient_row_72 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 72) = CheckedRank.HQMatrix 72 j := by
  decide +kernel

theorem HQ_coefficient_row_73 : ∀ j : Fin 82,
    orbitCoeff hqCoeff (sourceExponent j) (hqTargetExponent 73) = CheckedRank.HQMatrix 73 j := by
  decide +kernel

#print axioms HQ_coefficient_row_70
end WeightedSupport.PolynomialModel
