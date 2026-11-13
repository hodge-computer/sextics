import Proposal.PolarCubicDifferentialTables
namespace PolarCovariants.DifferentialData
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions PolynomialEncoding.BivariateExpressions
open PolarCovariants.IdentityData PolarCubicEncodingCheck ResidueFirstJets TrivSqZeroExt
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 131072
set_option maxHeartbeats 32000000
variable {K : Type*} [CommRing K]
theorem coefficient0_9_1 (v : ℕ → K) :
    ringEval v FinalL0_9_1=ringEval v FinalR0_9_1 := by
  apply identity_of_encoding_context v FinalL0_9_1 FinalR0_9_1 (18,10,8) (2^17)
  all_goals decide +kernel
theorem coefficient0_9_0 (v : ℕ → K) :
    ringEval v FinalL0_9_0=ringEval v FinalR0_9_0 := by
  apply identity_of_encoding_context v FinalL0_9_0 FinalR0_9_0 (18,9,9) (2^21)
  all_goals decide +kernel
theorem coefficient0_8_2 (v : ℕ → K) :
    ringEval v FinalL0_8_2=ringEval v FinalR0_8_2 := by
  apply identity_of_encoding_context v FinalL0_8_2 FinalR0_8_2 (17,11,8) (2^21)
  all_goals decide +kernel
theorem coefficient0_8_1 (v : ℕ → K) :
    ringEval v FinalL0_8_1=ringEval v FinalR0_8_1 := by
  apply identity_of_encoding_context v FinalL0_8_1 FinalR0_8_1 (17,10,9) (2^24)
  all_goals decide +kernel
theorem coefficient0_8_0 (v : ℕ → K) :
    ringEval v FinalL0_8_0=ringEval v FinalR0_8_0 := by
  apply identity_of_encoding_context v FinalL0_8_0 FinalR0_8_0 (17,9,10) (2^22)
  all_goals decide +kernel
theorem coefficient0_7_3 (v : ℕ → K) :
    ringEval v FinalL0_7_3=ringEval v FinalR0_7_3 := by
  apply identity_of_encoding_context v FinalL0_7_3 FinalR0_7_3 (16,12,8) (2^23)
  all_goals decide +kernel
theorem coefficient0_7_2 (v : ℕ → K) :
    ringEval v FinalL0_7_2=ringEval v FinalR0_7_2 := by
  apply identity_of_encoding_context v FinalL0_7_2 FinalR0_7_2 (16,11,9) (2^26)
  all_goals decide +kernel
theorem coefficient0_7_1 (v : ℕ → K) :
    ringEval v FinalL0_7_1=ringEval v FinalR0_7_1 := by
  apply identity_of_encoding_context v FinalL0_7_1 FinalR0_7_1 (16,10,10) (2^25)
  all_goals decide +kernel
theorem coefficient0_7_0 (v : ℕ → K) :
    ringEval v FinalL0_7_0=ringEval v FinalR0_7_0 := by
  apply identity_of_encoding_context v FinalL0_7_0 FinalR0_7_0 (16,9,11) (2^22)
  all_goals decide +kernel
theorem coefficient0_6_4 (v : ℕ → K) :
    ringEval v FinalL0_6_4=ringEval v FinalR0_6_4 := by
  apply identity_of_encoding_context v FinalL0_6_4 FinalR0_6_4 (15,13,8) (2^24)
  all_goals decide +kernel
theorem coefficient0_6_3 (v : ℕ → K) :
    ringEval v FinalL0_6_3=ringEval v FinalR0_6_3 := by
  apply identity_of_encoding_context v FinalL0_6_3 FinalR0_6_3 (15,12,9) (2^27)
  all_goals decide +kernel
theorem coefficient0_6_2 (v : ℕ → K) :
    ringEval v FinalL0_6_2=ringEval v FinalR0_6_2 := by
  apply identity_of_encoding_context v FinalL0_6_2 FinalR0_6_2 (15,11,10) (2^27)
  all_goals decide +kernel
theorem coefficient0_6_1 (v : ℕ → K) :
    ringEval v FinalL0_6_1=ringEval v FinalR0_6_1 := by
  apply identity_of_encoding_context v FinalL0_6_1 FinalR0_6_1 (15,10,11) (2^25)
  all_goals decide +kernel
theorem coefficient0_6_0 (v : ℕ → K) :
    ringEval v FinalL0_6_0=ringEval v FinalR0_6_0 := by
  apply identity_of_encoding_context v FinalL0_6_0 FinalR0_6_0 (15,9,12) (2^25)
  all_goals decide +kernel
theorem coefficient0_5_5 (v : ℕ → K) :
    ringEval v FinalL0_5_5=ringEval v FinalR0_5_5 := by
  apply identity_of_encoding_context v FinalL0_5_5 FinalR0_5_5 (14,14,8) (2^24)
  all_goals decide +kernel
theorem coefficient0_5_4 (v : ℕ → K) :
    ringEval v FinalL0_5_4=ringEval v FinalR0_5_4 := by
  apply identity_of_encoding_context v FinalL0_5_4 FinalR0_5_4 (14,13,9) (2^28)
  all_goals decide +kernel
theorem coefficient0_5_3 (v : ℕ → K) :
    ringEval v FinalL0_5_3=ringEval v FinalR0_5_3 := by
  apply identity_of_encoding_context v FinalL0_5_3 FinalR0_5_3 (14,12,10) (2^27)
  all_goals decide +kernel
theorem coefficient0_5_2 (v : ℕ → K) :
    ringEval v FinalL0_5_2=ringEval v FinalR0_5_2 := by
  apply identity_of_encoding_context v FinalL0_5_2 FinalR0_5_2 (14,11,11) (2^26)
  all_goals decide +kernel
theorem coefficient0_5_1 (v : ℕ → K) :
    ringEval v FinalL0_5_1=ringEval v FinalR0_5_1 := by
  apply identity_of_encoding_context v FinalL0_5_1 FinalR0_5_1 (14,10,12) (2^27)
  all_goals decide +kernel
theorem coefficient0_5_0 (v : ℕ → K) :
    ringEval v FinalL0_5_0=ringEval v FinalR0_5_0 := by
  apply identity_of_encoding_context v FinalL0_5_0 FinalR0_5_0 (14,9,13) (2^24)
  all_goals decide +kernel
theorem coefficient0_4_6 (v : ℕ → K) :
    ringEval v FinalL0_4_6=ringEval v FinalR0_4_6 := by
  apply identity_of_encoding_context v FinalL0_4_6 FinalR0_4_6 (13,15,8) (2^24)
  all_goals decide +kernel
theorem coefficient0_4_5 (v : ℕ → K) :
    ringEval v FinalL0_4_5=ringEval v FinalR0_4_5 := by
  apply identity_of_encoding_context v FinalL0_4_5 FinalR0_4_5 (13,14,9) (2^28)
  all_goals decide +kernel
theorem coefficient0_4_4 (v : ℕ → K) :
    ringEval v FinalL0_4_4=ringEval v FinalR0_4_4 := by
  apply identity_of_encoding_context v FinalL0_4_4 FinalR0_4_4 (13,13,10) (2^28)
  all_goals decide +kernel
theorem coefficient0_4_3 (v : ℕ → K) :
    ringEval v FinalL0_4_3=ringEval v FinalR0_4_3 := by
  apply identity_of_encoding_context v FinalL0_4_3 FinalR0_4_3 (13,12,11) (2^27)
  all_goals decide +kernel
theorem coefficient0_4_2 (v : ℕ → K) :
    ringEval v FinalL0_4_2=ringEval v FinalR0_4_2 := by
  apply identity_of_encoding_context v FinalL0_4_2 FinalR0_4_2 (13,11,12) (2^28)
  all_goals decide +kernel
theorem coefficient0_4_1 (v : ℕ → K) :
    ringEval v FinalL0_4_1=ringEval v FinalR0_4_1 := by
  apply identity_of_encoding_context v FinalL0_4_1 FinalR0_4_1 (13,10,13) (2^26)
  all_goals decide +kernel
theorem coefficient0_4_0 (v : ℕ → K) :
    ringEval v FinalL0_4_0=ringEval v FinalR0_4_0 := by
  apply identity_of_encoding_context v FinalL0_4_0 FinalR0_4_0 (13,9,14) (2^22)
  all_goals decide +kernel
theorem coefficient0_3_7 (v : ℕ → K) :
    ringEval v FinalL0_3_7=ringEval v FinalR0_3_7 := by
  apply identity_of_encoding_context v FinalL0_3_7 FinalR0_3_7 (12,16,8) (2^24)
  all_goals decide +kernel
theorem coefficient0_3_6 (v : ℕ → K) :
    ringEval v FinalL0_3_6=ringEval v FinalR0_3_6 := by
  apply identity_of_encoding_context v FinalL0_3_6 FinalR0_3_6 (12,15,9) (2^27)
  all_goals decide +kernel
theorem coefficient0_3_5 (v : ℕ → K) :
    ringEval v FinalL0_3_5=ringEval v FinalR0_3_5 := by
  apply identity_of_encoding_context v FinalL0_3_5 FinalR0_3_5 (12,14,10) (2^28)
  all_goals decide +kernel
theorem coefficient0_3_4 (v : ℕ → K) :
    ringEval v FinalL0_3_4=ringEval v FinalR0_3_4 := by
  apply identity_of_encoding_context v FinalL0_3_4 FinalR0_3_4 (12,13,11) (2^27)
  all_goals decide +kernel
theorem coefficient0_3_3 (v : ℕ → K) :
    ringEval v FinalL0_3_3=ringEval v FinalR0_3_3 := by
  apply identity_of_encoding_context v FinalL0_3_3 FinalR0_3_3 (12,12,12) (2^28)
  all_goals decide +kernel
theorem coefficient0_3_2 (v : ℕ → K) :
    ringEval v FinalL0_3_2=ringEval v FinalR0_3_2 := by
  apply identity_of_encoding_context v FinalL0_3_2 FinalR0_3_2 (12,11,13) (2^27)
  all_goals decide +kernel
theorem coefficient0_3_1 (v : ℕ → K) :
    ringEval v FinalL0_3_1=ringEval v FinalR0_3_1 := by
  apply identity_of_encoding_context v FinalL0_3_1 FinalR0_3_1 (12,10,14) (2^25)
  all_goals decide +kernel
theorem coefficient0_3_0 (v : ℕ → K) :
    ringEval v FinalL0_3_0=ringEval v FinalR0_3_0 := by
  apply identity_of_encoding_context v FinalL0_3_0 FinalR0_3_0 (12,9,15) (2^24)
  all_goals decide +kernel
theorem coefficient0_2_8 (v : ℕ → K) :
    ringEval v FinalL0_2_8=ringEval v FinalR0_2_8 := by
  apply identity_of_encoding_context v FinalL0_2_8 FinalR0_2_8 (11,17,8) (2^23)
  all_goals decide +kernel
theorem coefficient0_2_7 (v : ℕ → K) :
    ringEval v FinalL0_2_7=ringEval v FinalR0_2_7 := by
  apply identity_of_encoding_context v FinalL0_2_7 FinalR0_2_7 (11,16,9) (2^26)
  all_goals decide +kernel
theorem coefficient0_2_6 (v : ℕ → K) :
    ringEval v FinalL0_2_6=ringEval v FinalR0_2_6 := by
  apply identity_of_encoding_context v FinalL0_2_6 FinalR0_2_6 (11,15,10) (2^27)
  all_goals decide +kernel
theorem coefficient0_2_5 (v : ℕ → K) :
    ringEval v FinalL0_2_5=ringEval v FinalR0_2_5 := by
  apply identity_of_encoding_context v FinalL0_2_5 FinalR0_2_5 (11,14,11) (2^27)
  all_goals decide +kernel
theorem coefficient0_2_4 (v : ℕ → K) :
    ringEval v FinalL0_2_4=ringEval v FinalR0_2_4 := by
  apply identity_of_encoding_context v FinalL0_2_4 FinalR0_2_4 (11,13,12) (2^28)
  all_goals decide +kernel
theorem coefficient0_2_3 (v : ℕ → K) :
    ringEval v FinalL0_2_3=ringEval v FinalR0_2_3 := by
  apply identity_of_encoding_context v FinalL0_2_3 FinalR0_2_3 (11,12,13) (2^27)
  all_goals decide +kernel
theorem coefficient0_2_2 (v : ℕ → K) :
    ringEval v FinalL0_2_2=ringEval v FinalR0_2_2 := by
  apply identity_of_encoding_context v FinalL0_2_2 FinalR0_2_2 (11,11,14) (2^25)
  all_goals decide +kernel
theorem coefficient0_2_1 (v : ℕ → K) :
    ringEval v FinalL0_2_1=ringEval v FinalR0_2_1 := by
  apply identity_of_encoding_context v FinalL0_2_1 FinalR0_2_1 (11,10,15) (2^25)
  all_goals decide +kernel
theorem coefficient0_2_0 (v : ℕ → K) :
    ringEval v FinalL0_2_0=ringEval v FinalR0_2_0 := by
  apply identity_of_encoding_context v FinalL0_2_0 FinalR0_2_0 (11,9,16) (2^21)
  all_goals decide +kernel
theorem coefficient0_1_9 (v : ℕ → K) :
    ringEval v FinalL0_1_9=ringEval v FinalR0_1_9 := by
  apply identity_of_encoding_context v FinalL0_1_9 FinalR0_1_9 (10,18,8) (2^21)
  all_goals decide +kernel
theorem coefficient0_1_8 (v : ℕ → K) :
    ringEval v FinalL0_1_8=ringEval v FinalR0_1_8 := by
  apply identity_of_encoding_context v FinalL0_1_8 FinalR0_1_8 (10,17,9) (2^25)
  all_goals decide +kernel
theorem coefficient0_1_7 (v : ℕ → K) :
    ringEval v FinalL0_1_7=ringEval v FinalR0_1_7 := by
  apply identity_of_encoding_context v FinalL0_1_7 FinalR0_1_7 (10,16,10) (2^25)
  all_goals decide +kernel
theorem coefficient0_1_6 (v : ℕ → K) :
    ringEval v FinalL0_1_6=ringEval v FinalR0_1_6 := by
  apply identity_of_encoding_context v FinalL0_1_6 FinalR0_1_6 (10,15,11) (2^26)
  all_goals decide +kernel
theorem coefficient0_1_5 (v : ℕ → K) :
    ringEval v FinalL0_1_5=ringEval v FinalR0_1_5 := by
  apply identity_of_encoding_context v FinalL0_1_5 FinalR0_1_5 (10,14,12) (2^27)
  all_goals decide +kernel
theorem coefficient0_1_4 (v : ℕ → K) :
    ringEval v FinalL0_1_4=ringEval v FinalR0_1_4 := by
  apply identity_of_encoding_context v FinalL0_1_4 FinalR0_1_4 (10,13,13) (2^27)
  all_goals decide +kernel
theorem coefficient0_1_3 (v : ℕ → K) :
    ringEval v FinalL0_1_3=ringEval v FinalR0_1_3 := by
  apply identity_of_encoding_context v FinalL0_1_3 FinalR0_1_3 (10,12,14) (2^26)
  all_goals decide +kernel
theorem coefficient0_1_2 (v : ℕ → K) :
    ringEval v FinalL0_1_2=ringEval v FinalR0_1_2 := by
  apply identity_of_encoding_context v FinalL0_1_2 FinalR0_1_2 (10,11,15) (2^25)
  all_goals decide +kernel
theorem coefficient0_1_1 (v : ℕ → K) :
    ringEval v FinalL0_1_1=ringEval v FinalR0_1_1 := by
  apply identity_of_encoding_context v FinalL0_1_1 FinalR0_1_1 (10,10,16) (2^23)
  all_goals decide +kernel
theorem coefficient0_1_0 (v : ℕ → K) :
    ringEval v FinalL0_1_0=ringEval v FinalR0_1_0 := by
  apply identity_of_encoding_context v FinalL0_1_0 FinalR0_1_0 (10,9,17) (2^20)
  all_goals decide +kernel
theorem coefficient0_0_10 (v : ℕ → K) :
    ringEval v FinalL0_0_10=ringEval v FinalR0_0_10 := by
  apply identity_of_encoding_context v FinalL0_0_10 FinalR0_0_10 (9,19,8) (2^18)
  all_goals decide +kernel
theorem coefficient0_0_9 (v : ℕ → K) :
    ringEval v FinalL0_0_9=ringEval v FinalR0_0_9 := by
  apply identity_of_encoding_context v FinalL0_0_9 FinalR0_0_9 (9,18,9) (2^22)
  all_goals decide +kernel
theorem coefficient0_0_8 (v : ℕ → K) :
    ringEval v FinalL0_0_8=ringEval v FinalR0_0_8 := by
  apply identity_of_encoding_context v FinalL0_0_8 FinalR0_0_8 (9,17,10) (2^23)
  all_goals decide +kernel
theorem coefficient0_0_7 (v : ℕ → K) :
    ringEval v FinalL0_0_7=ringEval v FinalR0_0_7 := by
  apply identity_of_encoding_context v FinalL0_0_7 FinalR0_0_7 (9,16,11) (2^24)
  all_goals decide +kernel
theorem coefficient0_0_6 (v : ℕ → K) :
    ringEval v FinalL0_0_6=ringEval v FinalR0_0_6 := by
  apply identity_of_encoding_context v FinalL0_0_6 FinalR0_0_6 (9,15,12) (2^25)
  all_goals decide +kernel
theorem coefficient0_0_5 (v : ℕ → K) :
    ringEval v FinalL0_0_5=ringEval v FinalR0_0_5 := by
  apply identity_of_encoding_context v FinalL0_0_5 FinalR0_0_5 (9,14,13) (2^26)
  all_goals decide +kernel
theorem coefficient0_0_4 (v : ℕ → K) :
    ringEval v FinalL0_0_4=ringEval v FinalR0_0_4 := by
  apply identity_of_encoding_context v FinalL0_0_4 FinalR0_0_4 (9,13,14) (2^25)
  all_goals decide +kernel
theorem coefficient0_0_3 (v : ℕ → K) :
    ringEval v FinalL0_0_3=ringEval v FinalR0_0_3 := by
  apply identity_of_encoding_context v FinalL0_0_3 FinalR0_0_3 (9,12,15) (2^25)
  all_goals decide +kernel
theorem coefficient0_0_2 (v : ℕ → K) :
    ringEval v FinalL0_0_2=ringEval v FinalR0_0_2 := by
  apply identity_of_encoding_context v FinalL0_0_2 FinalR0_0_2 (9,11,16) (2^23)
  all_goals decide +kernel
theorem coefficient0_0_1 (v : ℕ → K) :
    ringEval v FinalL0_0_1=ringEval v FinalR0_0_1 := by
  apply identity_of_encoding_context v FinalL0_0_1 FinalR0_0_1 (9,10,17) (2^21)
  all_goals decide +kernel
theorem coefficient0_0_0 (v : ℕ → K) :
    ringEval v FinalL0_0_0=ringEval v FinalR0_0_0 := by
  apply identity_of_encoding_context v FinalL0_0_0 FinalR0_0_0 (9,9,18) (2^18)
  all_goals decide +kernel
theorem coefficient1_10_0 (v : ℕ → K) :
    ringEval v FinalL1_10_0=ringEval v FinalR1_10_0 := by
  apply identity_of_encoding_context v FinalL1_10_0 FinalR1_10_0 (18,8,7) (2^17)
  all_goals decide +kernel
theorem coefficient1_9_1 (v : ℕ → K) :
    ringEval v FinalL1_9_1=ringEval v FinalR1_9_1 := by
  apply identity_of_encoding_context v FinalL1_9_1 FinalR1_9_1 (17,9,7) (2^21)
  all_goals decide +kernel
theorem coefficient1_9_0 (v : ℕ → K) :
    ringEval v FinalL1_9_0=ringEval v FinalR1_9_0 := by
  apply identity_of_encoding_context v FinalL1_9_0 FinalR1_9_0 (17,8,8) (2^19)
  all_goals decide +kernel
theorem coefficient1_8_2 (v : ℕ → K) :
    ringEval v FinalL1_8_2=ringEval v FinalR1_8_2 := by
  apply identity_of_encoding_context v FinalL1_8_2 FinalR1_8_2 (16,10,7) (2^23)
  all_goals decide +kernel
theorem coefficient1_8_1 (v : ℕ → K) :
    ringEval v FinalL1_8_1=ringEval v FinalR1_8_1 := by
  apply identity_of_encoding_context v FinalL1_8_1 FinalR1_8_1 (16,9,8) (2^23)
  all_goals decide +kernel
theorem coefficient1_8_0 (v : ℕ → K) :
    ringEval v FinalL1_8_0=ringEval v FinalR1_8_0 := by
  apply identity_of_encoding_context v FinalL1_8_0 FinalR1_8_0 (16,8,9) (2^23)
  all_goals decide +kernel
theorem coefficient1_7_3 (v : ℕ → K) :
    ringEval v FinalL1_7_3=ringEval v FinalR1_7_3 := by
  apply identity_of_encoding_context v FinalL1_7_3 FinalR1_7_3 (15,11,7) (2^24)
  all_goals decide +kernel
theorem coefficient1_7_2 (v : ℕ → K) :
    ringEval v FinalL1_7_2=ringEval v FinalR1_7_2 := by
  apply identity_of_encoding_context v FinalL1_7_2 FinalR1_7_2 (15,10,8) (2^25)
  all_goals decide +kernel
theorem coefficient1_7_1 (v : ℕ → K) :
    ringEval v FinalL1_7_1=ringEval v FinalR1_7_1 := by
  apply identity_of_encoding_context v FinalL1_7_1 FinalR1_7_1 (15,9,9) (2^26)
  all_goals decide +kernel
theorem coefficient1_7_0 (v : ℕ → K) :
    ringEval v FinalL1_7_0=ringEval v FinalR1_7_0 := by
  apply identity_of_encoding_context v FinalL1_7_0 FinalR1_7_0 (15,8,10) (2^24)
  all_goals decide +kernel
theorem coefficient1_6_4 (v : ℕ → K) :
    ringEval v FinalL1_6_4=ringEval v FinalR1_6_4 := by
  apply identity_of_encoding_context v FinalL1_6_4 FinalR1_6_4 (14,12,7) (2^25)
  all_goals decide +kernel
theorem coefficient1_6_3 (v : ℕ → K) :
    ringEval v FinalL1_6_3=ringEval v FinalR1_6_3 := by
  apply identity_of_encoding_context v FinalL1_6_3 FinalR1_6_3 (14,11,8) (2^26)
  all_goals decide +kernel
theorem coefficient1_6_2 (v : ℕ → K) :
    ringEval v FinalL1_6_2=ringEval v FinalR1_6_2 := by
  apply identity_of_encoding_context v FinalL1_6_2 FinalR1_6_2 (14,10,9) (2^27)
  all_goals decide +kernel
theorem coefficient1_6_1 (v : ℕ → K) :
    ringEval v FinalL1_6_1=ringEval v FinalR1_6_1 := by
  apply identity_of_encoding_context v FinalL1_6_1 FinalR1_6_1 (14,9,10) (2^26)
  all_goals decide +kernel
theorem coefficient1_6_0 (v : ℕ → K) :
    ringEval v FinalL1_6_0=ringEval v FinalR1_6_0 := by
  apply identity_of_encoding_context v FinalL1_6_0 FinalR1_6_0 (14,8,11) (2^23)
  all_goals decide +kernel
theorem coefficient1_5_5 (v : ℕ → K) :
    ringEval v FinalL1_5_5=ringEval v FinalR1_5_5 := by
  apply identity_of_encoding_context v FinalL1_5_5 FinalR1_5_5 (13,13,7) (2^25)
  all_goals decide +kernel
theorem coefficient1_5_4 (v : ℕ → K) :
    ringEval v FinalL1_5_4=ringEval v FinalR1_5_4 := by
  apply identity_of_encoding_context v FinalL1_5_4 FinalR1_5_4 (13,12,8) (2^26)
  all_goals decide +kernel
theorem coefficient1_5_3 (v : ℕ → K) :
    ringEval v FinalL1_5_3=ringEval v FinalR1_5_3 := by
  apply identity_of_encoding_context v FinalL1_5_3 FinalR1_5_3 (13,11,9) (2^28)
  all_goals decide +kernel
theorem coefficient1_5_2 (v : ℕ → K) :
    ringEval v FinalL1_5_2=ringEval v FinalR1_5_2 := by
  apply identity_of_encoding_context v FinalL1_5_2 FinalR1_5_2 (13,10,10) (2^28)
  all_goals decide +kernel
theorem coefficient1_5_1 (v : ℕ → K) :
    ringEval v FinalL1_5_1=ringEval v FinalR1_5_1 := by
  apply identity_of_encoding_context v FinalL1_5_1 FinalR1_5_1 (13,9,11) (2^26)
  all_goals decide +kernel
theorem coefficient1_5_0 (v : ℕ → K) :
    ringEval v FinalL1_5_0=ringEval v FinalR1_5_0 := by
  apply identity_of_encoding_context v FinalL1_5_0 FinalR1_5_0 (13,8,12) (2^25)
  all_goals decide +kernel
theorem coefficient1_4_6 (v : ℕ → K) :
    ringEval v FinalL1_4_6=ringEval v FinalR1_4_6 := by
  apply identity_of_encoding_context v FinalL1_4_6 FinalR1_4_6 (12,14,7) (2^25)
  all_goals decide +kernel
theorem coefficient1_4_5 (v : ℕ → K) :
    ringEval v FinalL1_4_5=ringEval v FinalR1_4_5 := by
  apply identity_of_encoding_context v FinalL1_4_5 FinalR1_4_5 (12,13,8) (2^27)
  all_goals decide +kernel
theorem coefficient1_4_4 (v : ℕ → K) :
    ringEval v FinalL1_4_4=ringEval v FinalR1_4_4 := by
  apply identity_of_encoding_context v FinalL1_4_4 FinalR1_4_4 (12,12,9) (2^28)
  all_goals decide +kernel
theorem coefficient1_4_3 (v : ℕ → K) :
    ringEval v FinalL1_4_3=ringEval v FinalR1_4_3 := by
  apply identity_of_encoding_context v FinalL1_4_3 FinalR1_4_3 (12,11,10) (2^28)
  all_goals decide +kernel
theorem coefficient1_4_2 (v : ℕ → K) :
    ringEval v FinalL1_4_2=ringEval v FinalR1_4_2 := by
  apply identity_of_encoding_context v FinalL1_4_2 FinalR1_4_2 (12,10,11) (2^27)
  all_goals decide +kernel
theorem coefficient1_4_1 (v : ℕ → K) :
    ringEval v FinalL1_4_1=ringEval v FinalR1_4_1 := by
  apply identity_of_encoding_context v FinalL1_4_1 FinalR1_4_1 (12,9,12) (2^27)
  all_goals decide +kernel
theorem coefficient1_4_0 (v : ℕ → K) :
    ringEval v FinalL1_4_0=ringEval v FinalR1_4_0 := by
  apply identity_of_encoding_context v FinalL1_4_0 FinalR1_4_0 (12,8,13) (2^25)
  all_goals decide +kernel
theorem coefficient1_3_7 (v : ℕ → K) :
    ringEval v FinalL1_3_7=ringEval v FinalR1_3_7 := by
  apply identity_of_encoding_context v FinalL1_3_7 FinalR1_3_7 (11,15,7) (2^25)
  all_goals decide +kernel
theorem coefficient1_3_6 (v : ℕ → K) :
    ringEval v FinalL1_3_6=ringEval v FinalR1_3_6 := by
  apply identity_of_encoding_context v FinalL1_3_6 FinalR1_3_6 (11,14,8) (2^26)
  all_goals decide +kernel
theorem coefficient1_3_5 (v : ℕ → K) :
    ringEval v FinalL1_3_5=ringEval v FinalR1_3_5 := by
  apply identity_of_encoding_context v FinalL1_3_5 FinalR1_3_5 (11,13,9) (2^28)
  all_goals decide +kernel
theorem coefficient1_3_4 (v : ℕ → K) :
    ringEval v FinalL1_3_4=ringEval v FinalR1_3_4 := by
  apply identity_of_encoding_context v FinalL1_3_4 FinalR1_3_4 (11,12,10) (2^28)
  all_goals decide +kernel
theorem coefficient1_3_3 (v : ℕ → K) :
    ringEval v FinalL1_3_3=ringEval v FinalR1_3_3 := by
  apply identity_of_encoding_context v FinalL1_3_3 FinalR1_3_3 (11,11,11) (2^27)
  all_goals decide +kernel
theorem coefficient1_3_2 (v : ℕ → K) :
    ringEval v FinalL1_3_2=ringEval v FinalR1_3_2 := by
  apply identity_of_encoding_context v FinalL1_3_2 FinalR1_3_2 (11,10,12) (2^28)
  all_goals decide +kernel
theorem coefficient1_3_1 (v : ℕ → K) :
    ringEval v FinalL1_3_1=ringEval v FinalR1_3_1 := by
  apply identity_of_encoding_context v FinalL1_3_1 FinalR1_3_1 (11,9,13) (2^26)
  all_goals decide +kernel
theorem coefficient1_3_0 (v : ℕ → K) :
    ringEval v FinalL1_3_0=ringEval v FinalR1_3_0 := by
  apply identity_of_encoding_context v FinalL1_3_0 FinalR1_3_0 (11,8,14) (2^23)
  all_goals decide +kernel
theorem coefficient1_2_8 (v : ℕ → K) :
    ringEval v FinalL1_2_8=ringEval v FinalR1_2_8 := by
  apply identity_of_encoding_context v FinalL1_2_8 FinalR1_2_8 (10,16,7) (2^23)
  all_goals decide +kernel
theorem coefficient1_2_7 (v : ℕ → K) :
    ringEval v FinalL1_2_7=ringEval v FinalR1_2_7 := by
  apply identity_of_encoding_context v FinalL1_2_7 FinalR1_2_7 (10,15,8) (2^25)
  all_goals decide +kernel
theorem coefficient1_2_6 (v : ℕ → K) :
    ringEval v FinalL1_2_6=ringEval v FinalR1_2_6 := by
  apply identity_of_encoding_context v FinalL1_2_6 FinalR1_2_6 (10,14,9) (2^27)
  all_goals decide +kernel
theorem coefficient1_2_5 (v : ℕ → K) :
    ringEval v FinalL1_2_5=ringEval v FinalR1_2_5 := by
  apply identity_of_encoding_context v FinalL1_2_5 FinalR1_2_5 (10,13,10) (2^28)
  all_goals decide +kernel
theorem coefficient1_2_4 (v : ℕ → K) :
    ringEval v FinalL1_2_4=ringEval v FinalR1_2_4 := by
  apply identity_of_encoding_context v FinalL1_2_4 FinalR1_2_4 (10,12,11) (2^27)
  all_goals decide +kernel
theorem coefficient1_2_3 (v : ℕ → K) :
    ringEval v FinalL1_2_3=ringEval v FinalR1_2_3 := by
  apply identity_of_encoding_context v FinalL1_2_3 FinalR1_2_3 (10,11,12) (2^28)
  all_goals decide +kernel
theorem coefficient1_2_2 (v : ℕ → K) :
    ringEval v FinalL1_2_2=ringEval v FinalR1_2_2 := by
  apply identity_of_encoding_context v FinalL1_2_2 FinalR1_2_2 (10,10,13) (2^27)
  all_goals decide +kernel
theorem coefficient1_2_1 (v : ℕ → K) :
    ringEval v FinalL1_2_1=ringEval v FinalR1_2_1 := by
  apply identity_of_encoding_context v FinalL1_2_1 FinalR1_2_1 (10,9,14) (2^24)
  all_goals decide +kernel
theorem coefficient1_2_0 (v : ℕ → K) :
    ringEval v FinalL1_2_0=ringEval v FinalR1_2_0 := by
  apply identity_of_encoding_context v FinalL1_2_0 FinalR1_2_0 (10,8,15) (2^23)
  all_goals decide +kernel
theorem coefficient1_1_9 (v : ℕ → K) :
    ringEval v FinalL1_1_9=ringEval v FinalR1_1_9 := by
  apply identity_of_encoding_context v FinalL1_1_9 FinalR1_1_9 (9,17,7) (2^22)
  all_goals decide +kernel
theorem coefficient1_1_8 (v : ℕ → K) :
    ringEval v FinalL1_1_8=ringEval v FinalR1_1_8 := by
  apply identity_of_encoding_context v FinalL1_1_8 FinalR1_1_8 (9,16,8) (2^24)
  all_goals decide +kernel
theorem coefficient1_1_7 (v : ℕ → K) :
    ringEval v FinalL1_1_7=ringEval v FinalR1_1_7 := by
  apply identity_of_encoding_context v FinalL1_1_7 FinalR1_1_7 (9,15,9) (2^26)
  all_goals decide +kernel
theorem coefficient1_1_6 (v : ℕ → K) :
    ringEval v FinalL1_1_6=ringEval v FinalR1_1_6 := by
  apply identity_of_encoding_context v FinalL1_1_6 FinalR1_1_6 (9,14,10) (2^27)
  all_goals decide +kernel
theorem coefficient1_1_5 (v : ℕ → K) :
    ringEval v FinalL1_1_5=ringEval v FinalR1_1_5 := by
  apply identity_of_encoding_context v FinalL1_1_5 FinalR1_1_5 (9,13,11) (2^27)
  all_goals decide +kernel
theorem coefficient1_1_4 (v : ℕ → K) :
    ringEval v FinalL1_1_4=ringEval v FinalR1_1_4 := by
  apply identity_of_encoding_context v FinalL1_1_4 FinalR1_1_4 (9,12,12) (2^27)
  all_goals decide +kernel
theorem coefficient1_1_3 (v : ℕ → K) :
    ringEval v FinalL1_1_3=ringEval v FinalR1_1_3 := by
  apply identity_of_encoding_context v FinalL1_1_3 FinalR1_1_3 (9,11,13) (2^27)
  all_goals decide +kernel
theorem coefficient1_1_2 (v : ℕ → K) :
    ringEval v FinalL1_1_2=ringEval v FinalR1_1_2 := by
  apply identity_of_encoding_context v FinalL1_1_2 FinalR1_1_2 (9,10,14) (2^25)
  all_goals decide +kernel
theorem coefficient1_1_1 (v : ℕ → K) :
    ringEval v FinalL1_1_1=ringEval v FinalR1_1_1 := by
  apply identity_of_encoding_context v FinalL1_1_1 FinalR1_1_1 (9,9,15) (2^23)
  all_goals decide +kernel
theorem coefficient1_1_0 (v : ℕ → K) :
    ringEval v FinalL1_1_0=ringEval v FinalR1_1_0 := by
  apply identity_of_encoding_context v FinalL1_1_0 FinalR1_1_0 (9,8,16) (2^21)
  all_goals decide +kernel
theorem coefficient1_0_10 (v : ℕ → K) :
    ringEval v FinalL1_0_10=ringEval v FinalR1_0_10 := by
  apply identity_of_encoding_context v FinalL1_0_10 FinalR1_0_10 (8,18,7) (2^19)
  all_goals decide +kernel
theorem coefficient1_0_9 (v : ℕ → K) :
    ringEval v FinalL1_0_9=ringEval v FinalR1_0_9 := by
  apply identity_of_encoding_context v FinalL1_0_9 FinalR1_0_9 (8,17,8) (2^22)
  all_goals decide +kernel
theorem coefficient1_0_8 (v : ℕ → K) :
    ringEval v FinalL1_0_8=ringEval v FinalR1_0_8 := by
  apply identity_of_encoding_context v FinalL1_0_8 FinalR1_0_8 (8,16,9) (2^24)
  all_goals decide +kernel
theorem coefficient1_0_7 (v : ℕ → K) :
    ringEval v FinalL1_0_7=ringEval v FinalR1_0_7 := by
  apply identity_of_encoding_context v FinalL1_0_7 FinalR1_0_7 (8,15,10) (2^25)
  all_goals decide +kernel
theorem coefficient1_0_6 (v : ℕ → K) :
    ringEval v FinalL1_0_6=ringEval v FinalR1_0_6 := by
  apply identity_of_encoding_context v FinalL1_0_6 FinalR1_0_6 (8,14,11) (2^25)
  all_goals decide +kernel
theorem coefficient1_0_5 (v : ℕ → K) :
    ringEval v FinalL1_0_5=ringEval v FinalR1_0_5 := by
  apply identity_of_encoding_context v FinalL1_0_5 FinalR1_0_5 (8,13,12) (2^26)
  all_goals decide +kernel
theorem coefficient1_0_4 (v : ℕ → K) :
    ringEval v FinalL1_0_4=ringEval v FinalR1_0_4 := by
  apply identity_of_encoding_context v FinalL1_0_4 FinalR1_0_4 (8,12,13) (2^26)
  all_goals decide +kernel
theorem coefficient1_0_3 (v : ℕ → K) :
    ringEval v FinalL1_0_3=ringEval v FinalR1_0_3 := by
  apply identity_of_encoding_context v FinalL1_0_3 FinalR1_0_3 (8,11,14) (2^24)
  all_goals decide +kernel
theorem coefficient1_0_2 (v : ℕ → K) :
    ringEval v FinalL1_0_2=ringEval v FinalR1_0_2 := by
  apply identity_of_encoding_context v FinalL1_0_2 FinalR1_0_2 (8,10,15) (2^24)
  all_goals decide +kernel
theorem coefficient1_0_1 (v : ℕ → K) :
    ringEval v FinalL1_0_1=ringEval v FinalR1_0_1 := by
  apply identity_of_encoding_context v FinalL1_0_1 FinalR1_0_1 (8,9,16) (2^22)
  all_goals decide +kernel
theorem coefficient1_0_0 (v : ℕ → K) :
    ringEval v FinalL1_0_0=ringEval v FinalR1_0_0 := by
  apply identity_of_encoding_context v FinalL1_0_0 FinalR1_0_0 (8,8,17) (2^19)
  all_goals decide +kernel
theorem data_identity0 (v : ℕ → K) (x y : K) :
    denote v x y FinalL0Data=denote v x y FinalR0Data := by
  simp only [FinalL0Data,FinalR0Data,denote,coefficient0_9_1,coefficient0_9_0,coefficient0_8_2,coefficient0_8_1,coefficient0_8_0,coefficient0_7_3,coefficient0_7_2,coefficient0_7_1,coefficient0_7_0,coefficient0_6_4,coefficient0_6_3,coefficient0_6_2,coefficient0_6_1,coefficient0_6_0,coefficient0_5_5,coefficient0_5_4,coefficient0_5_3,coefficient0_5_2,coefficient0_5_1,coefficient0_5_0,coefficient0_4_6,coefficient0_4_5,coefficient0_4_4,coefficient0_4_3,coefficient0_4_2,coefficient0_4_1,coefficient0_4_0,coefficient0_3_7,coefficient0_3_6,coefficient0_3_5,coefficient0_3_4,coefficient0_3_3,coefficient0_3_2,coefficient0_3_1,coefficient0_3_0,coefficient0_2_8,coefficient0_2_7,coefficient0_2_6,coefficient0_2_5,coefficient0_2_4,coefficient0_2_3,coefficient0_2_2,coefficient0_2_1,coefficient0_2_0,coefficient0_1_9,coefficient0_1_8,coefficient0_1_7,coefficient0_1_6,coefficient0_1_5,coefficient0_1_4,coefficient0_1_3,coefficient0_1_2,coefficient0_1_1,coefficient0_1_0,coefficient0_0_10,coefficient0_0_9,coefficient0_0_8,coefficient0_0_7,coefficient0_0_6,coefficient0_0_5,coefficient0_0_4,coefficient0_0_3,coefficient0_0_2,coefficient0_0_1,coefficient0_0_0]
theorem data_identity1 (v : ℕ → K) (x y : K) :
    denote v x y FinalL1Data=denote v x y FinalR1Data := by
  simp only [FinalL1Data,FinalR1Data,denote,coefficient1_10_0,coefficient1_9_1,coefficient1_9_0,coefficient1_8_2,coefficient1_8_1,coefficient1_8_0,coefficient1_7_3,coefficient1_7_2,coefficient1_7_1,coefficient1_7_0,coefficient1_6_4,coefficient1_6_3,coefficient1_6_2,coefficient1_6_1,coefficient1_6_0,coefficient1_5_5,coefficient1_5_4,coefficient1_5_3,coefficient1_5_2,coefficient1_5_1,coefficient1_5_0,coefficient1_4_6,coefficient1_4_5,coefficient1_4_4,coefficient1_4_3,coefficient1_4_2,coefficient1_4_1,coefficient1_4_0,coefficient1_3_7,coefficient1_3_6,coefficient1_3_5,coefficient1_3_4,coefficient1_3_3,coefficient1_3_2,coefficient1_3_1,coefficient1_3_0,coefficient1_2_8,coefficient1_2_7,coefficient1_2_6,coefficient1_2_5,coefficient1_2_4,coefficient1_2_3,coefficient1_2_2,coefficient1_2_1,coefficient1_2_0,coefficient1_1_9,coefficient1_1_8,coefficient1_1_7,coefficient1_1_6,coefficient1_1_5,coefficient1_1_4,coefficient1_1_3,coefficient1_1_2,coefficient1_1_1,coefficient1_1_0,coefficient1_0_10,coefficient1_0_9,coefficient1_0_8,coefficient1_0_7,coefficient1_0_6,coefficient1_0_5,coefficient1_0_4,coefficient1_0_3,coefficient1_0_2,coefficient1_0_1,coefficient1_0_0]
theorem semantic_identity0 (v : ℕ → K) (x y : K) :
    let u := denote v x y UData
    let h := denote v x y HData
    let q := denote v x y ThetaData
    let j := denote v x y JData
    let ux := denote v x y UxData
    let uy := denote v x y UyData
    let hx := denote v x y HxData
    let hy := denote v x y HyData
    let qx := denote v x y ThetaxData
    let qy := denote v x y ThetayData
    ((3*j)+(h*qy*ux)+((-1)*h*qx*uy)+((-2)*hy*q*ux)+(2*hx*q*uy))=((hx*qy*u)+((-1)*hy*qx*u)) := by
  dsimp only
  have h := data_identity0 v x y
  rw [FinalL0_evaluation,FinalR0_evaluation] at h
  simp only [← Right1S0_generated,← Right1S1_generated,← Right1S2_generated,← Right1S3_generated,← Right1S4_generated,← Right1T5_generated,← Right1T5p1_generated,← Right1T5p0_generated,← Right1T4_generated,← Right1T4p1_generated,← Right1T4p0_generated,← Right1T3_generated,← Right1T3p1_generated,← Right1T3p0_generated,← Right1T2_generated,← Right1T2p1_generated,← Right1T2p0_generated,← Right1T1_generated,← Right1T1p1_generated,← Right1T1p0_generated,← Right1T0_generated,← Right1T0p1_generated,← Right1T0p0_generated,← Left1S0_generated,← Left1S1_generated,← Left1S2_generated,← Left1S3_generated,← Left1S4_generated,← Left1S5_generated,← Left1S6_generated,← Left1S7_generated,← Left1S8_generated,← Left1S9_generated,← Left1S10_generated,← Left1S11_generated,← Left1T12_generated,← Left1T11_generated,← Left1T11p1_generated,← Left1T11p0_generated,← Left1T10_generated,← Left1T10p1_generated,← Left1T10p0_generated,← Left1T9_generated,← Left1T9p1_generated,← Left1T9p0_generated,← Left1T8_generated,← Left1T8p1_generated,← Left1T8p0_generated,← Left1T7_generated,← Left1T7p1_generated,← Left1T7p0_generated,← Left1T6_generated,← Left1T6p1_generated,← Left1T6p0_generated,← Left1T5_generated,← Left1T5p1_generated,← Left1T5p0_generated,← Left1T4_generated,← Left1T4p1_generated,← Left1T4p0_generated,← Left1T3_generated,← Left1T3p1_generated,← Left1T3p0_generated,← Left1T2_generated,← Left1T2p1_generated,← Left1T2p0_generated,← Left1T1_generated,← Left1T1p1_generated,← Left1T1p0_generated,← Left1T0_generated,← Left1T0p1_generated,← Left1T0p0_generated,← Right0S0_generated,← Right0T1_generated,← Right0T1p1_generated,← Right0T1p0_generated,← Right0T0_generated,← Right0T0p1_generated,← Right0T0p0_generated,← Left0S0_generated,← Left0S1_generated,← Left0S2_generated,← Left0S3_generated,← Left0T4_generated,← Left0T3_generated,← Left0T3p1_generated,← Left0T3p0_generated,← Left0T2_generated,← Left0T2p1_generated,← Left0T2p0_generated,← Left0T1_generated,← Left0T1p1_generated,← Left0T1p0_generated,← Left0T0_generated,← Left0T0p1_generated,← Left0T0p0_generated,multiply_denote,scale_denote,merge_denote,ringEval,Int.cast_ofNat,Int.cast_neg] at h
  linear_combination h
theorem semantic_identity1 (v : ℕ → K) (x y : K) :
    let u := denote v x y UData
    let h := denote v x y HData
    let q := denote v x y ThetaData
    let j := denote v x y JData
    let ux := denote v x y UxData
    let uy := denote v x y UyData
    let hx := denote v x y HxData
    let hy := denote v x y HyData
    let qx := denote v x y ThetaxData
    let qy := denote v x y ThetayData
    let uk := denote v x y UkData
    let hk := denote v x y HkData
    let qk := denote v x y ThetakData
    let jk := denote v x y JkData
    let uxk := denote v x y UkxData
    let uyk := denote v x y UkyData
    let hxk := denote v x y HkxData
    let hyk := denote v x y HkyData
    let qxk := denote v x y ThetakxData
    let qyk := denote v x y ThetakyData
    ((3*jk)+(h*qy*uxk)+(h*qyk*ux)+(hk*qy*ux)+((-1)*h*qx*uyk)+((-1)*h*qxk*uy)+((-1)*hk*qx*uy)+((-2)*hy*q*uxk)+((-2)*hy*qk*ux)+((-2)*hyk*q*ux)+(2*hx*q*uyk)+(2*hx*qk*uy)+(2*hxk*q*uy))=((hx*qy*uk)+(hx*qyk*u)+(hxk*qy*u)+((-1)*hy*qx*uk)+((-1)*hy*qxk*u)+((-1)*hyk*qx*u)) := by
  dsimp only
  have h := data_identity1 v x y
  rw [FinalL1_evaluation,FinalR1_evaluation] at h
  simp only [← Right1S0_generated,← Right1S1_generated,← Right1S2_generated,← Right1S3_generated,← Right1S4_generated,← Right1T5_generated,← Right1T5p1_generated,← Right1T5p0_generated,← Right1T4_generated,← Right1T4p1_generated,← Right1T4p0_generated,← Right1T3_generated,← Right1T3p1_generated,← Right1T3p0_generated,← Right1T2_generated,← Right1T2p1_generated,← Right1T2p0_generated,← Right1T1_generated,← Right1T1p1_generated,← Right1T1p0_generated,← Right1T0_generated,← Right1T0p1_generated,← Right1T0p0_generated,← Left1S0_generated,← Left1S1_generated,← Left1S2_generated,← Left1S3_generated,← Left1S4_generated,← Left1S5_generated,← Left1S6_generated,← Left1S7_generated,← Left1S8_generated,← Left1S9_generated,← Left1S10_generated,← Left1S11_generated,← Left1T12_generated,← Left1T11_generated,← Left1T11p1_generated,← Left1T11p0_generated,← Left1T10_generated,← Left1T10p1_generated,← Left1T10p0_generated,← Left1T9_generated,← Left1T9p1_generated,← Left1T9p0_generated,← Left1T8_generated,← Left1T8p1_generated,← Left1T8p0_generated,← Left1T7_generated,← Left1T7p1_generated,← Left1T7p0_generated,← Left1T6_generated,← Left1T6p1_generated,← Left1T6p0_generated,← Left1T5_generated,← Left1T5p1_generated,← Left1T5p0_generated,← Left1T4_generated,← Left1T4p1_generated,← Left1T4p0_generated,← Left1T3_generated,← Left1T3p1_generated,← Left1T3p0_generated,← Left1T2_generated,← Left1T2p1_generated,← Left1T2p0_generated,← Left1T1_generated,← Left1T1p1_generated,← Left1T1p0_generated,← Left1T0_generated,← Left1T0p1_generated,← Left1T0p0_generated,← Right0S0_generated,← Right0T1_generated,← Right0T1p1_generated,← Right0T1p0_generated,← Right0T0_generated,← Right0T0p1_generated,← Right0T0p0_generated,← Left0S0_generated,← Left0S1_generated,← Left0S2_generated,← Left0S3_generated,← Left0T4_generated,← Left0T3_generated,← Left0T3p1_generated,← Left0T3p0_generated,← Left0T2_generated,← Left0T2p1_generated,← Left0T2p0_generated,← Left0T1_generated,← Left0T1p1_generated,← Left0T1p0_generated,← Left0T0_generated,← Left0T0p1_generated,← Left0T0p0_generated,multiply_denote,scale_denote,merge_denote,ringEval,Int.cast_ofNat,Int.cast_neg] at h
  linear_combination h
end PolarCovariants.DifferentialData
