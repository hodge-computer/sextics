import HodgeComputer.Constructions.CyclicCubic.IdentityData
import HodgeComputer.Constructions.CyclicCubic.EncodingCheck
namespace CycleCovariants.IdentityData
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions CycleCubicEncodingCheck
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000
theorem coefficient_1_2 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_1_2=ringEval v Right_1_2 := by
  apply identity_of_encoding_context v Left_1_2 Right_1_2 (19,20,33) (2^42)
  all_goals decide +kernel
theorem coefficient_1_1 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_1_1=ringEval v Right_1_1 := by
  apply identity_of_encoding_context v Left_1_1 Right_1_1 (19,19,34) (2^42)
  all_goals decide +kernel
theorem coefficient_1_0 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_1_0=ringEval v Right_1_0 := by
  apply identity_of_encoding_context v Left_1_0 Right_1_0 (19,18,35) (2^42)
  all_goals decide +kernel
theorem coefficient_0_18 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_0_18=ringEval v Right_0_18 := by
  apply identity_of_encoding_context v Left_0_18 Right_0_18 (18,36,18) (2^42)
  all_goals decide +kernel
theorem coefficient_0_17 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_0_17=ringEval v Right_0_17 := by
  apply identity_of_encoding_context v Left_0_17 Right_0_17 (18,35,19) (2^42)
  all_goals decide +kernel
theorem coefficient_0_16 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_0_16=ringEval v Right_0_16 := by
  apply identity_of_encoding_context v Left_0_16 Right_0_16 (18,34,20) (2^42)
  all_goals decide +kernel
theorem coefficient_0_15 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_0_15=ringEval v Right_0_15 := by
  apply identity_of_encoding_context v Left_0_15 Right_0_15 (18,33,21) (2^42)
  all_goals decide +kernel
theorem coefficient_0_14 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_0_14=ringEval v Right_0_14 := by
  apply identity_of_encoding_context v Left_0_14 Right_0_14 (18,32,22) (2^42)
  all_goals decide +kernel
theorem coefficient_0_13 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_0_13=ringEval v Right_0_13 := by
  apply identity_of_encoding_context v Left_0_13 Right_0_13 (18,31,23) (2^42)
  all_goals decide +kernel
theorem coefficient_0_12 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_0_12=ringEval v Right_0_12 := by
  apply identity_of_encoding_context v Left_0_12 Right_0_12 (18,30,24) (2^42)
  all_goals decide +kernel
theorem coefficient_0_11 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_0_11=ringEval v Right_0_11 := by
  apply identity_of_encoding_context v Left_0_11 Right_0_11 (18,29,25) (2^42)
  all_goals decide +kernel
theorem coefficient_0_10 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_0_10=ringEval v Right_0_10 := by
  apply identity_of_encoding_context v Left_0_10 Right_0_10 (18,28,26) (2^42)
  all_goals decide +kernel
theorem coefficient_0_9 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_0_9=ringEval v Right_0_9 := by
  apply identity_of_encoding_context v Left_0_9 Right_0_9 (18,27,27) (2^42)
  all_goals decide +kernel
theorem coefficient_0_8 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_0_8=ringEval v Right_0_8 := by
  apply identity_of_encoding_context v Left_0_8 Right_0_8 (18,26,28) (2^42)
  all_goals decide +kernel
theorem coefficient_0_7 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_0_7=ringEval v Right_0_7 := by
  apply identity_of_encoding_context v Left_0_7 Right_0_7 (18,25,29) (2^42)
  all_goals decide +kernel
theorem coefficient_0_6 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_0_6=ringEval v Right_0_6 := by
  apply identity_of_encoding_context v Left_0_6 Right_0_6 (18,24,30) (2^42)
  all_goals decide +kernel
theorem coefficient_0_5 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_0_5=ringEval v Right_0_5 := by
  apply identity_of_encoding_context v Left_0_5 Right_0_5 (18,23,31) (2^42)
  all_goals decide +kernel
theorem coefficient_0_4 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_0_4=ringEval v Right_0_4 := by
  apply identity_of_encoding_context v Left_0_4 Right_0_4 (18,22,32) (2^42)
  all_goals decide +kernel
theorem coefficient_0_3 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_0_3=ringEval v Right_0_3 := by
  apply identity_of_encoding_context v Left_0_3 Right_0_3 (18,21,33) (2^42)
  all_goals decide +kernel
theorem coefficient_0_2 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_0_2=ringEval v Right_0_2 := by
  apply identity_of_encoding_context v Left_0_2 Right_0_2 (18,20,34) (2^42)
  all_goals decide +kernel
theorem coefficient_0_1 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_0_1=ringEval v Right_0_1 := by
  apply identity_of_encoding_context v Left_0_1 Right_0_1 (18,19,35) (2^42)
  all_goals decide +kernel
theorem coefficient_0_0 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_0_0=ringEval v Right_0_0 := by
  apply identity_of_encoding_context v Left_0_0 Right_0_0 (18,18,36) (2^42)
  all_goals decide +kernel
#print axioms coefficient_0_0
end CycleCovariants.IdentityData
