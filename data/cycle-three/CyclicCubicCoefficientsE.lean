import Proposal.CyclicCubicIdentityData
import Proposal.CyclicCubicEncodingCheck
namespace CycleCovariants.IdentityData
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions CycleCubicEncodingCheck
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000
theorem coefficient_5_8 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_5_8=ringEval v Right_5_8 := by
  apply identity_of_encoding_context v Left_5_8 Right_5_8 (23,26,23) (2^42)
  all_goals decide +kernel
theorem coefficient_5_7 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_5_7=ringEval v Right_5_7 := by
  apply identity_of_encoding_context v Left_5_7 Right_5_7 (23,25,24) (2^42)
  all_goals decide +kernel
theorem coefficient_5_6 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_5_6=ringEval v Right_5_6 := by
  apply identity_of_encoding_context v Left_5_6 Right_5_6 (23,24,25) (2^42)
  all_goals decide +kernel
theorem coefficient_5_5 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_5_5=ringEval v Right_5_5 := by
  apply identity_of_encoding_context v Left_5_5 Right_5_5 (23,23,26) (2^42)
  all_goals decide +kernel
theorem coefficient_5_4 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_5_4=ringEval v Right_5_4 := by
  apply identity_of_encoding_context v Left_5_4 Right_5_4 (23,22,27) (2^42)
  all_goals decide +kernel
theorem coefficient_5_3 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_5_3=ringEval v Right_5_3 := by
  apply identity_of_encoding_context v Left_5_3 Right_5_3 (23,21,28) (2^42)
  all_goals decide +kernel
theorem coefficient_5_2 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_5_2=ringEval v Right_5_2 := by
  apply identity_of_encoding_context v Left_5_2 Right_5_2 (23,20,29) (2^42)
  all_goals decide +kernel
theorem coefficient_5_1 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_5_1=ringEval v Right_5_1 := by
  apply identity_of_encoding_context v Left_5_1 Right_5_1 (23,19,30) (2^42)
  all_goals decide +kernel
theorem coefficient_5_0 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_5_0=ringEval v Right_5_0 := by
  apply identity_of_encoding_context v Left_5_0 Right_5_0 (23,18,31) (2^42)
  all_goals decide +kernel
theorem coefficient_4_14 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_4_14=ringEval v Right_4_14 := by
  apply identity_of_encoding_context v Left_4_14 Right_4_14 (22,32,18) (2^42)
  all_goals decide +kernel
theorem coefficient_4_13 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_4_13=ringEval v Right_4_13 := by
  apply identity_of_encoding_context v Left_4_13 Right_4_13 (22,31,19) (2^42)
  all_goals decide +kernel
theorem coefficient_4_12 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_4_12=ringEval v Right_4_12 := by
  apply identity_of_encoding_context v Left_4_12 Right_4_12 (22,30,20) (2^42)
  all_goals decide +kernel
theorem coefficient_4_11 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_4_11=ringEval v Right_4_11 := by
  apply identity_of_encoding_context v Left_4_11 Right_4_11 (22,29,21) (2^42)
  all_goals decide +kernel
theorem coefficient_4_10 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_4_10=ringEval v Right_4_10 := by
  apply identity_of_encoding_context v Left_4_10 Right_4_10 (22,28,22) (2^42)
  all_goals decide +kernel
theorem coefficient_4_9 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_4_9=ringEval v Right_4_9 := by
  apply identity_of_encoding_context v Left_4_9 Right_4_9 (22,27,23) (2^42)
  all_goals decide +kernel
theorem coefficient_4_8 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_4_8=ringEval v Right_4_8 := by
  apply identity_of_encoding_context v Left_4_8 Right_4_8 (22,26,24) (2^42)
  all_goals decide +kernel
theorem coefficient_4_7 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_4_7=ringEval v Right_4_7 := by
  apply identity_of_encoding_context v Left_4_7 Right_4_7 (22,25,25) (2^42)
  all_goals decide +kernel
theorem coefficient_4_6 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_4_6=ringEval v Right_4_6 := by
  apply identity_of_encoding_context v Left_4_6 Right_4_6 (22,24,26) (2^42)
  all_goals decide +kernel
theorem coefficient_4_5 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_4_5=ringEval v Right_4_5 := by
  apply identity_of_encoding_context v Left_4_5 Right_4_5 (22,23,27) (2^42)
  all_goals decide +kernel
theorem coefficient_4_4 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_4_4=ringEval v Right_4_4 := by
  apply identity_of_encoding_context v Left_4_4 Right_4_4 (22,22,28) (2^42)
  all_goals decide +kernel
theorem coefficient_4_3 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_4_3=ringEval v Right_4_3 := by
  apply identity_of_encoding_context v Left_4_3 Right_4_3 (22,21,29) (2^42)
  all_goals decide +kernel
theorem coefficient_4_2 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_4_2=ringEval v Right_4_2 := by
  apply identity_of_encoding_context v Left_4_2 Right_4_2 (22,20,30) (2^42)
  all_goals decide +kernel
theorem coefficient_4_1 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_4_1=ringEval v Right_4_1 := by
  apply identity_of_encoding_context v Left_4_1 Right_4_1 (22,19,31) (2^42)
  all_goals decide +kernel
theorem coefficient_4_0 {K : Type*} [CommRing K] (v : ℕ → K) :
    ringEval v Left_4_0=ringEval v Right_4_0 := by
  apply identity_of_encoding_context v Left_4_0 Right_4_0 (22,18,32) (2^42)
  all_goals decide +kernel
#print axioms coefficient_4_0
end CycleCovariants.IdentityData
