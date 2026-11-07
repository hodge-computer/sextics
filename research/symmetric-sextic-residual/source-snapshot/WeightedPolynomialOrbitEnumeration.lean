import WeightedPolynomialOrbitBlocksSource
import WeightedPolynomialOrbitBlocksQ
import WeightedPolynomialOrbitBlocksHQ
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace WeightedSupport.PolynomialModel

theorem source_orbit_enumeration : sourceCodes.toList = orbitCodes 5 false := by
  change sourceCodes.toList = (orbitBlock 5 false 0 ++ (orbitBlock 5 false 1 ++ (orbitBlock 5 false 2 ++ (orbitBlock 5 false 3 ++ (orbitBlock 5 false 4 ++ (orbitBlock 5 false 5 ++ (orbitBlock 5 false 6 ++ (orbitBlock 5 false 7 ++ (orbitBlock 5 false 8 ++ (orbitBlock 5 false 9 ++ (orbitBlock 5 false 10 ++ (orbitBlock 5 false 11 ++ (orbitBlock 5 false 12 ++ (orbitBlock 5 false 13 ++ (orbitBlock 5 false 14 ++ (orbitBlock 5 false 15 ++ (orbitBlock 5 false 16 ++ (orbitBlock 5 false 17 ++ (orbitBlock 5 false 18 ++ (orbitBlock 5 false 19 ++ (orbitBlock 5 false 20 ++ (orbitBlock 5 false 21 ++ (orbitBlock 5 false 22 ++ (orbitBlock 5 false 23 ++ (orbitBlock 5 false 24 ++ [])))))))))))))))))))))))))
  rw [Source_orbit_block_0, Source_orbit_block_1, Source_orbit_block_2, Source_orbit_block_3, Source_orbit_block_4, Source_orbit_block_5, Source_orbit_block_6, Source_orbit_block_7, Source_orbit_block_8, Source_orbit_block_9, Source_orbit_block_10, Source_orbit_block_11, Source_orbit_block_12, Source_orbit_block_13, Source_orbit_block_14, Source_orbit_block_15, Source_orbit_block_16, Source_orbit_block_17, Source_orbit_block_18, Source_orbit_block_19, Source_orbit_block_20, Source_orbit_block_21, Source_orbit_block_22, Source_orbit_block_23, Source_orbit_block_24]
  decide +kernel
#print axioms source_orbit_enumeration

theorem q_target_orbit_enumeration : qTargetCodes.toList = orbitCodes 16 true := by
  change qTargetCodes.toList = (orbitBlock 16 true 0 ++ (orbitBlock 16 true 1 ++ (orbitBlock 16 true 2 ++ (orbitBlock 16 true 3 ++ (orbitBlock 16 true 4 ++ (orbitBlock 16 true 5 ++ (orbitBlock 16 true 6 ++ (orbitBlock 16 true 7 ++ (orbitBlock 16 true 8 ++ (orbitBlock 16 true 9 ++ (orbitBlock 16 true 10 ++ (orbitBlock 16 true 11 ++ (orbitBlock 16 true 12 ++ (orbitBlock 16 true 13 ++ (orbitBlock 16 true 14 ++ (orbitBlock 16 true 15 ++ (orbitBlock 16 true 16 ++ (orbitBlock 16 true 17 ++ (orbitBlock 16 true 18 ++ (orbitBlock 16 true 19 ++ (orbitBlock 16 true 20 ++ (orbitBlock 16 true 21 ++ (orbitBlock 16 true 22 ++ (orbitBlock 16 true 23 ++ (orbitBlock 16 true 24 ++ [])))))))))))))))))))))))))
  rw [Q_orbit_block_0, Q_orbit_block_1, Q_orbit_block_2, Q_orbit_block_3, Q_orbit_block_4, Q_orbit_block_5, Q_orbit_block_6, Q_orbit_block_7, Q_orbit_block_8, Q_orbit_block_9, Q_orbit_block_10, Q_orbit_block_11, Q_orbit_block_12, Q_orbit_block_13, Q_orbit_block_14, Q_orbit_block_15, Q_orbit_block_16, Q_orbit_block_17, Q_orbit_block_18, Q_orbit_block_19, Q_orbit_block_20, Q_orbit_block_21, Q_orbit_block_22, Q_orbit_block_23, Q_orbit_block_24]
  decide +kernel
#print axioms q_target_orbit_enumeration

theorem hq_target_orbit_enumeration : hqTargetCodes.toList = orbitCodes 17 true := by
  change hqTargetCodes.toList = (orbitBlock 17 true 0 ++ (orbitBlock 17 true 1 ++ (orbitBlock 17 true 2 ++ (orbitBlock 17 true 3 ++ (orbitBlock 17 true 4 ++ (orbitBlock 17 true 5 ++ (orbitBlock 17 true 6 ++ (orbitBlock 17 true 7 ++ (orbitBlock 17 true 8 ++ (orbitBlock 17 true 9 ++ (orbitBlock 17 true 10 ++ (orbitBlock 17 true 11 ++ (orbitBlock 17 true 12 ++ (orbitBlock 17 true 13 ++ (orbitBlock 17 true 14 ++ (orbitBlock 17 true 15 ++ (orbitBlock 17 true 16 ++ (orbitBlock 17 true 17 ++ (orbitBlock 17 true 18 ++ (orbitBlock 17 true 19 ++ (orbitBlock 17 true 20 ++ (orbitBlock 17 true 21 ++ (orbitBlock 17 true 22 ++ (orbitBlock 17 true 23 ++ (orbitBlock 17 true 24 ++ [])))))))))))))))))))))))))
  rw [HQ_orbit_block_0, HQ_orbit_block_1, HQ_orbit_block_2, HQ_orbit_block_3, HQ_orbit_block_4, HQ_orbit_block_5, HQ_orbit_block_6, HQ_orbit_block_7, HQ_orbit_block_8, HQ_orbit_block_9, HQ_orbit_block_10, HQ_orbit_block_11, HQ_orbit_block_12, HQ_orbit_block_13, HQ_orbit_block_14, HQ_orbit_block_15, HQ_orbit_block_16, HQ_orbit_block_17, HQ_orbit_block_18, HQ_orbit_block_19, HQ_orbit_block_20, HQ_orbit_block_21, HQ_orbit_block_22, HQ_orbit_block_23, HQ_orbit_block_24]
  decide +kernel
#print axioms hq_target_orbit_enumeration

end WeightedSupport.PolynomialModel
