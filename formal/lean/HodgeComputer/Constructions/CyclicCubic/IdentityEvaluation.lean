import HodgeComputer.Constructions.CyclicCubic.IdentityProducts
namespace CycleCovariants.IdentityData
open Lean.Grind.CommRing CycleSignedExpressions CycleBivariateExpressions
open CycleCovariants.Reflection
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000
variable {K : Type*} [CommRing K]
lemma H_evaluation (a b c d e f x y : K) :
    denote (fun i => (context a b c d e f x y 1).get i) x y HData=
      H a b c d e f x y 1 := by
  simp only [HData,denote,ringEval_denote,H_3_0,H_2_1,H_2_0,H_1_2,H_1_1,H_1_0,H_0_3,H_0_2,H_0_1,H_0_0,HCoeff300_denote,HCoeff210_denote,HCoeff201_denote,HCoeff120_denote,HCoeff111_denote,HCoeff102_denote,HCoeff030_denote,HCoeff021_denote,HCoeff012_denote,HCoeff003_denote,H,pow_zero,pow_one,one_pow,mul_one,add_zero,add_assoc,mul_assoc]
lemma Theta_evaluation (a b c d e f x y : K) :
    denote (fun i => (context a b c d e f x y 1).get i) x y ThetaData=
      Theta a b c d e f x y 1 := by
  simp only [ThetaData,denote,ringEval_denote,Theta_6_0,Theta_5_1,Theta_5_0,Theta_4_2,Theta_4_1,Theta_4_0,Theta_3_3,Theta_3_2,Theta_3_1,Theta_3_0,Theta_2_4,Theta_2_3,Theta_2_2,Theta_2_1,Theta_2_0,Theta_1_5,Theta_1_4,Theta_1_3,Theta_1_2,Theta_1_1,Theta_1_0,Theta_0_6,Theta_0_5,Theta_0_4,Theta_0_3,Theta_0_2,Theta_0_1,Theta_0_0,ThetaCoeff600_denote,ThetaCoeff510_denote,ThetaCoeff501_denote,ThetaCoeff420_denote,ThetaCoeff411_denote,ThetaCoeff402_denote,ThetaCoeff330_denote,ThetaCoeff321_denote,ThetaCoeff312_denote,ThetaCoeff303_denote,ThetaCoeff240_denote,ThetaCoeff231_denote,ThetaCoeff222_denote,ThetaCoeff213_denote,ThetaCoeff204_denote,ThetaCoeff150_denote,ThetaCoeff141_denote,ThetaCoeff132_denote,ThetaCoeff123_denote,ThetaCoeff114_denote,ThetaCoeff105_denote,ThetaCoeff060_denote,ThetaCoeff051_denote,ThetaCoeff042_denote,ThetaCoeff033_denote,ThetaCoeff024_denote,ThetaCoeff015_denote,ThetaCoeff006_denote,Theta,pow_zero,pow_one,one_pow,mul_one,add_zero,add_assoc,mul_assoc]
lemma J_evaluation (a b c d e f x y : K) :
    denote (fun i => (context a b c d e f x y 1).get i) x y JData=
      J a b c d e f x y 1 := by
  simp only [JData,denote,ringEval_denote,J_9_0,J_8_1,J_8_0,J_7_2,J_7_1,J_7_0,J_6_3,J_6_2,J_6_1,J_6_0,J_5_4,J_5_3,J_5_2,J_5_1,J_5_0,J_4_5,J_4_4,J_4_3,J_4_2,J_4_1,J_4_0,J_3_6,J_3_5,J_3_4,J_3_3,J_3_2,J_3_1,J_3_0,J_2_7,J_2_6,J_2_5,J_2_4,J_2_3,J_2_2,J_2_1,J_2_0,J_1_8,J_1_7,J_1_6,J_1_5,J_1_4,J_1_3,J_1_2,J_1_1,J_1_0,J_0_9,J_0_8,J_0_7,J_0_6,J_0_5,J_0_4,J_0_3,J_0_2,J_0_1,J_0_0,JCoeff900_denote,JCoeff810_denote,JCoeff801_denote,JCoeff720_denote,JCoeff711_denote,JCoeff702_denote,JCoeff630_denote,JCoeff621_denote,JCoeff612_denote,JCoeff603_denote,JCoeff540_denote,JCoeff531_denote,JCoeff522_denote,JCoeff513_denote,JCoeff504_denote,JCoeff450_denote,JCoeff441_denote,JCoeff432_denote,JCoeff423_denote,JCoeff414_denote,JCoeff405_denote,JCoeff360_denote,JCoeff351_denote,JCoeff342_denote,JCoeff333_denote,JCoeff324_denote,JCoeff315_denote,JCoeff306_denote,JCoeff270_denote,JCoeff261_denote,JCoeff252_denote,JCoeff243_denote,JCoeff234_denote,JCoeff225_denote,JCoeff216_denote,JCoeff207_denote,JCoeff180_denote,JCoeff171_denote,JCoeff162_denote,JCoeff153_denote,JCoeff144_denote,JCoeff135_denote,JCoeff126_denote,JCoeff117_denote,JCoeff108_denote,JCoeff090_denote,JCoeff081_denote,JCoeff072_denote,JCoeff063_denote,JCoeff054_denote,JCoeff045_denote,JCoeff036_denote,JCoeff027_denote,JCoeff018_denote,JCoeff009_denote,J,pow_zero,pow_one,one_pow,mul_one,add_zero,add_assoc,mul_assoc]
lemma U_evaluation (a b c d e f x y : K) :
    denote (fun i => (context a b c d e f x y 1).get i) x y UData=
      CycleCubic.cubic a b c d e f x y 1 := by
  have h0 : ringEval (fun i => (context a b c d e f x y 1).get i) (.var 0)=a := rfl
  have h1 : ringEval (fun i => (context a b c d e f x y 1).get i) (.var 1)=b := rfl
  have h2 : ringEval (fun i => (context a b c d e f x y 1).get i) (.var 2)=c := rfl
  have h3 : ringEval (fun i => (context a b c d e f x y 1).get i) (.var 3)=d := rfl
  have h4 : ringEval (fun i => (context a b c d e f x y 1).get i) (.var 4)=e := rfl
  have h5 : ringEval (fun i => (context a b c d e f x y 1).get i) (.var 5)=f := rfl
  simp only [UData,U_3_0,U_2_1,U_1_0,U_0_3,U_0_2,U_0_0,denote,
    h0,h1,h2,h3,h4,h5,CycleCubic.cubic]
  ring
end CycleCovariants.IdentityData
