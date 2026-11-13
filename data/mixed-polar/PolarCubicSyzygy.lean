import Proposal.PolarCubicCoefficientsA
import Proposal.PolarCubicCoefficientsB
import Proposal.PolarCubicCoefficientsC
import Proposal.PolarCubicCoefficientsD
import HodgeComputer.Constructions.ResidueTransport.FirstJets
namespace PolarCovariants.IdentityData
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions PolynomialEncoding.BivariateExpressions
open ResidueFirstJets TrivSqZeroExt
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 131072
set_option maxHeartbeats 8000000
variable {K : Type*} [CommRing K]
theorem data_identity0 (v : ℕ → K) (x y : K) :
    denote v x y FinalL0Data=denote v x y FinalR0Data := by
  simp only [FinalL0Data,FinalR0Data,denote,coefficient0_18_0,coefficient0_17_1,coefficient0_17_0,coefficient0_16_2,coefficient0_16_1,coefficient0_16_0,coefficient0_15_3,coefficient0_15_2,coefficient0_15_1,coefficient0_15_0,coefficient0_14_4,coefficient0_14_3,coefficient0_14_2,coefficient0_14_1,coefficient0_14_0,coefficient0_13_5,coefficient0_13_4,coefficient0_13_3,coefficient0_13_2,coefficient0_13_1,coefficient0_13_0,coefficient0_12_6,coefficient0_12_5,coefficient0_12_4,coefficient0_12_3,coefficient0_12_2,coefficient0_12_1,coefficient0_12_0,coefficient0_11_7,coefficient0_11_6,coefficient0_11_5,coefficient0_11_4,coefficient0_11_3,coefficient0_11_2,coefficient0_11_1,coefficient0_11_0,coefficient0_10_8,coefficient0_10_7,coefficient0_10_6,coefficient0_10_5,coefficient0_10_4,coefficient0_10_3,coefficient0_10_2,coefficient0_10_1,coefficient0_10_0,coefficient0_9_9,coefficient0_9_8,coefficient0_9_7,coefficient0_9_6,coefficient0_9_5,coefficient0_9_4,coefficient0_9_3,coefficient0_9_2,coefficient0_9_1,coefficient0_9_0,coefficient0_8_10,coefficient0_8_9,coefficient0_8_8,coefficient0_8_7,coefficient0_8_6,coefficient0_8_5,coefficient0_8_4,coefficient0_8_3,coefficient0_8_2,coefficient0_8_1,coefficient0_8_0,coefficient0_7_11,coefficient0_7_10,coefficient0_7_9,coefficient0_7_8,coefficient0_7_7,coefficient0_7_6,coefficient0_7_5,coefficient0_7_4,coefficient0_7_3,coefficient0_7_2,coefficient0_7_1,coefficient0_7_0,coefficient0_6_12,coefficient0_6_11,coefficient0_6_10,coefficient0_6_9,coefficient0_6_8,coefficient0_6_7,coefficient0_6_6,coefficient0_6_5,coefficient0_6_4,coefficient0_6_3,coefficient0_6_2,coefficient0_6_1,coefficient0_6_0,coefficient0_5_13,coefficient0_5_12,coefficient0_5_11,coefficient0_5_10,coefficient0_5_9,coefficient0_5_8,coefficient0_5_7,coefficient0_5_6,coefficient0_5_5,coefficient0_5_4,coefficient0_5_3,coefficient0_5_2,coefficient0_5_1,coefficient0_5_0,coefficient0_4_14,coefficient0_4_13,coefficient0_4_12,coefficient0_4_11,coefficient0_4_10,coefficient0_4_9,coefficient0_4_8,coefficient0_4_7,coefficient0_4_6,coefficient0_4_5,coefficient0_4_4,coefficient0_4_3,coefficient0_4_2,coefficient0_4_1,coefficient0_4_0,coefficient0_3_15,coefficient0_3_14,coefficient0_3_13,coefficient0_3_12,coefficient0_3_11,coefficient0_3_10,coefficient0_3_9,coefficient0_3_8,coefficient0_3_7,coefficient0_3_6,coefficient0_3_5,coefficient0_3_4,coefficient0_3_3,coefficient0_3_2,coefficient0_3_1,coefficient0_3_0,coefficient0_2_16,coefficient0_2_15,coefficient0_2_14,coefficient0_2_13,coefficient0_2_12,coefficient0_2_11,coefficient0_2_10,coefficient0_2_9,coefficient0_2_8,coefficient0_2_7,coefficient0_2_6,coefficient0_2_5,coefficient0_2_4,coefficient0_2_3,coefficient0_2_2,coefficient0_2_1,coefficient0_2_0,coefficient0_1_17,coefficient0_1_16,coefficient0_1_15,coefficient0_1_14,coefficient0_1_13,coefficient0_1_12,coefficient0_1_11,coefficient0_1_10,coefficient0_1_9,coefficient0_1_8,coefficient0_1_7,coefficient0_1_6,coefficient0_1_5,coefficient0_1_4,coefficient0_1_3,coefficient0_1_2,coefficient0_1_1,coefficient0_1_0,coefficient0_0_18,coefficient0_0_17,coefficient0_0_16,coefficient0_0_15,coefficient0_0_14,coefficient0_0_13,coefficient0_0_12,coefficient0_0_11,coefficient0_0_10,coefficient0_0_9,coefficient0_0_8,coefficient0_0_7,coefficient0_0_6,coefficient0_0_5,coefficient0_0_4,coefficient0_0_3,coefficient0_0_2,coefficient0_0_1,coefficient0_0_0]
theorem data_identity1 (v : ℕ → K) (x y : K) :
    denote v x y FinalL1Data=denote v x y FinalR1Data := by
  simp only [FinalL1Data,FinalR1Data,denote,coefficient1_18_0,coefficient1_17_1,coefficient1_17_0,coefficient1_16_2,coefficient1_16_1,coefficient1_16_0,coefficient1_15_3,coefficient1_15_2,coefficient1_15_1,coefficient1_15_0,coefficient1_14_4,coefficient1_14_3,coefficient1_14_2,coefficient1_14_1,coefficient1_14_0,coefficient1_13_5,coefficient1_13_4,coefficient1_13_3,coefficient1_13_2,coefficient1_13_1,coefficient1_13_0,coefficient1_12_6,coefficient1_12_5,coefficient1_12_4,coefficient1_12_3,coefficient1_12_2,coefficient1_12_1,coefficient1_12_0,coefficient1_11_7,coefficient1_11_6,coefficient1_11_5,coefficient1_11_4,coefficient1_11_3,coefficient1_11_2,coefficient1_11_1,coefficient1_11_0,coefficient1_10_8,coefficient1_10_7,coefficient1_10_6,coefficient1_10_5,coefficient1_10_4,coefficient1_10_3,coefficient1_10_2,coefficient1_10_1,coefficient1_10_0,coefficient1_9_9,coefficient1_9_8,coefficient1_9_7,coefficient1_9_6,coefficient1_9_5,coefficient1_9_4,coefficient1_9_3,coefficient1_9_2,coefficient1_9_1,coefficient1_9_0,coefficient1_8_10,coefficient1_8_9,coefficient1_8_8,coefficient1_8_7,coefficient1_8_6,coefficient1_8_5,coefficient1_8_4,coefficient1_8_3,coefficient1_8_2,coefficient1_8_1,coefficient1_8_0,coefficient1_7_11,coefficient1_7_10,coefficient1_7_9,coefficient1_7_8,coefficient1_7_7,coefficient1_7_6,coefficient1_7_5,coefficient1_7_4,coefficient1_7_3,coefficient1_7_2,coefficient1_7_1,coefficient1_7_0,coefficient1_6_12,coefficient1_6_11,coefficient1_6_10,coefficient1_6_9,coefficient1_6_8,coefficient1_6_7,coefficient1_6_6,coefficient1_6_5,coefficient1_6_4,coefficient1_6_3,coefficient1_6_2,coefficient1_6_1,coefficient1_6_0,coefficient1_5_13,coefficient1_5_12,coefficient1_5_11,coefficient1_5_10,coefficient1_5_9,coefficient1_5_8,coefficient1_5_7,coefficient1_5_6,coefficient1_5_5,coefficient1_5_4,coefficient1_5_3,coefficient1_5_2,coefficient1_5_1,coefficient1_5_0,coefficient1_4_14,coefficient1_4_13,coefficient1_4_12,coefficient1_4_11,coefficient1_4_10,coefficient1_4_9,coefficient1_4_8,coefficient1_4_7,coefficient1_4_6,coefficient1_4_5,coefficient1_4_4,coefficient1_4_3,coefficient1_4_2,coefficient1_4_1,coefficient1_4_0,coefficient1_3_15,coefficient1_3_14,coefficient1_3_13,coefficient1_3_12,coefficient1_3_11,coefficient1_3_10,coefficient1_3_9,coefficient1_3_8,coefficient1_3_7,coefficient1_3_6,coefficient1_3_5,coefficient1_3_4,coefficient1_3_3,coefficient1_3_2,coefficient1_3_1,coefficient1_3_0,coefficient1_2_16,coefficient1_2_15,coefficient1_2_14,coefficient1_2_13,coefficient1_2_12,coefficient1_2_11,coefficient1_2_10,coefficient1_2_9,coefficient1_2_8,coefficient1_2_7,coefficient1_2_6,coefficient1_2_5,coefficient1_2_4,coefficient1_2_3,coefficient1_2_2,coefficient1_2_1,coefficient1_2_0,coefficient1_1_17,coefficient1_1_16,coefficient1_1_15,coefficient1_1_14,coefficient1_1_13,coefficient1_1_12,coefficient1_1_11,coefficient1_1_10,coefficient1_1_9,coefficient1_1_8,coefficient1_1_7,coefficient1_1_6,coefficient1_1_5,coefficient1_1_4,coefficient1_1_3,coefficient1_1_2,coefficient1_1_1,coefficient1_1_0,coefficient1_0_18,coefficient1_0_17,coefficient1_0_16,coefficient1_0_15,coefficient1_0_14,coefficient1_0_13,coefficient1_0_12,coefficient1_0_11,coefficient1_0_10,coefficient1_0_9,coefficient1_0_8,coefficient1_0_7,coefficient1_0_6,coefficient1_0_5,coefficient1_0_4,coefficient1_0_3,coefficient1_0_2,coefficient1_0_1,coefficient1_0_0]
theorem full_syzygy (a b c d e f x y : K) :
    let u := PolarCubic.cubic a b c d e f x y 1
    let h := H a b c d e f x y 1
    let q := Theta a b c d e f x y 1
    let j := J a b c d e f x y 1
    let s := PolarCubic.s4Numerator a b c d e f
    let t := PolarCubic.s6Numerator a b c d e f
    27*j^2=108*q^3+36*s*q*h^4-t*h^6+
      u*(243*t*u*q^2-8748*s^3*q*u^3+486*s*t*q*u^2*h-1944*s^2*q*u*h^2-
        54*t*q*h^3-34992*s^4*u^4*h-2673*s^2*t*u^3*h^2-108*t^2*u^2*h^3+
        162*s*t*u*h^4-144*s^2*h^5) := by
  dsimp only
  let v : ℕ → K := fun i => match i with | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | 5 => f | _ => 0
  have h := data_identity0 v x y
  rw [FinalL0_evaluation,FinalR0_evaluation] at h
  simp only [← Right1Sum0_generated,← Right1Sum1_generated,← Right1Sum2_generated,← Right1Sum3_generated,← Right1Sum4_generated,← Right1Sum5_generated,← Right1Sum6_generated,← Right1Sum7_generated,← Right1Sum8_generated,← Right1Sum9_generated,← Right1Sum10_generated,← Right1Sum11_generated,← Right1Sum12_generated,← Right1Sum13_generated,← Right1Sum14_generated,← Right1Sum15_generated,← Right1Sum16_generated,← Right1Sum17_generated,← Right1Sum18_generated,← Right1Sum19_generated,← Right1Sum20_generated,← Right1Sum21_generated,← Right1Sum22_generated,← Right1Sum23_generated,← Right1Sum24_generated,← Right1Sum25_generated,← Right1Sum26_generated,← Right1Sum27_generated,← Right1Sum28_generated,← Right1Sum29_generated,← Right1Sum30_generated,← Right1Sum31_generated,← Right1Sum32_generated,← Right1Sum33_generated,← Right1Sum34_generated,← Right1Sum35_generated,← Right1Sum36_generated,← Right1Sum37_generated,← Right1Sum38_generated,← Right1Sum39_generated,← Right1Sum40_generated,← Right1Term41_generated,← Right1Term41p0_generated,← Right1Term40_generated,← Right1Term39_generated,← Right1Term39p1_generated,← Right1Term39p0_generated,← Right1Term38_generated,← Right1Term38p0_generated,← Right1Term37_generated,← Right1Term37p0_generated,← Right1Term36_generated,← Right1Term36p1_generated,← Right1Term36p0_generated,← Right1Term35_generated,← Right1Term35p0_generated,← Right1Term34_generated,← Right1Term34p1_generated,← Right1Term34p0_generated,← Right1Term33_generated,← Right1Term33p2_generated,← Right1Term33p1_generated,← Right1Term33p0_generated,← Right1Term32_generated,← Right1Term32p1_generated,← Right1Term32p0_generated,← Right1Term31_generated,← Right1Term31p1_generated,← Right1Term31p0_generated,← Right1Term30_generated,← Right1Term30p0_generated,← Right1Term29_generated,← Right1Term29p0_generated,← Right1Term28_generated,← Right1Term28p1_generated,← Right1Term28p0_generated,← Right1Term27_generated,← Right1Term27p1_generated,← Right1Term27p0_generated,← Right1Term26_generated,← Right1Term26p1_generated,← Right1Term26p0_generated,← Right1Term25_generated,← Right1Term25p1_generated,← Right1Term25p0_generated,← Right1Term24_generated,← Right1Term24p0_generated,← Right1Term23_generated,← Right1Term23p0_generated,← Right1Term22_generated,← Right1Term22p1_generated,← Right1Term22p0_generated,← Right1Term21_generated,← Right1Term21p0_generated,← Right1Term20_generated,← Right1Term20p1_generated,← Right1Term20p0_generated,← Right1Term19_generated,← Right1Term19p1_generated,← Right1Term19p0_generated,← Right1Term18_generated,← Right1Term18p2_generated,← Right1Term18p1_generated,← Right1Term18p0_generated,← Right1Term17_generated,← Right1Term17p1_generated,← Right1Term17p0_generated,← Right1Term16_generated,← Right1Term16p1_generated,← Right1Term16p0_generated,← Right1Term15_generated,← Right1Term15p1_generated,← Right1Term15p0_generated,← Right1Term14_generated,← Right1Term14p0_generated,← Right1Term13_generated,← Right1Term13p0_generated,← Right1Term12_generated,← Right1Term12p2_generated,← Right1Term12p1_generated,← Right1Term12p0_generated,← Right1Term11_generated,← Right1Term11p1_generated,← Right1Term11p0_generated,← Right1Term10_generated,← Right1Term10p2_generated,← Right1Term10p1_generated,← Right1Term10p0_generated,← Right1Term9_generated,← Right1Term9p1_generated,← Right1Term9p0_generated,← Right1Term8_generated,← Right1Term8p0_generated,← Right1Term7_generated,← Right1Term7p0_generated,← Right1Term6_generated,← Right1Term6p1_generated,← Right1Term6p0_generated,← Right1Term5_generated,← Right1Term5p1_generated,← Right1Term5p0_generated,← Right1Term4_generated,← Right1Term4p1_generated,← Right1Term4p0_generated,← Right1Term3_generated,← Right1Term3p0_generated,← Right1Term2_generated,← Right1Term2p0_generated,← Right1Term1_generated,← Right1Term1p1_generated,← Right1Term1p0_generated,← Right1Term0_generated,← Right1Term0p0_generated,← Left1_generated,← JJk_generated,← Right0Sum0_generated,← Right0Sum1_generated,← Right0Sum2_generated,← Right0Sum3_generated,← Right0Sum4_generated,← Right0Sum5_generated,← Right0Sum6_generated,← Right0Sum7_generated,← Right0Sum8_generated,← Right0Sum9_generated,← Right0Sum10_generated,← Right0Sum11_generated,← Right0Term12_generated,← Right0Term11_generated,← Right0Term10_generated,← Right0Term10p1_generated,← Right0Term10p0_generated,← Right0Term9_generated,← Right0Term9p0_generated,← Right0Term8_generated,← Right0Term8p0_generated,← Right0Term7_generated,← Right0Term7p0_generated,← Right0Term6_generated,← Right0Term6p0_generated,← Right0Term5_generated,← Right0Term5p1_generated,← Right0Term5p0_generated,← Right0Term4_generated,← Right0Term4p0_generated,← Right0Term3_generated,← Right0Term3p1_generated,← Right0Term3p0_generated,← Right0Term2_generated,← Right0Term2p0_generated,← Right0Term1_generated,← Right0Term1p0_generated,← Right0Term0_generated,← Right0Term0p0_generated,← Left0_generated,← Jp2_generated,← Thetap3_generated,← Thetap2_generated,← Hp6_generated,← Hp5_generated,← Hp4_generated,← Hp3_generated,← Hp2_generated,← Up5_generated,← Up4_generated,← Up3_generated,← Up2_generated,multiply_denote,scale_denote,merge_denote] at h
  simp only [H_evaluation,Theta_evaluation,J_evaluation,Hk_evaluation,Thetak_evaluation,Jk_evaluation,U_evaluation,Uk_evaluation,S_evaluation,T_evaluation,Sk_evaluation,Tk_evaluation,ringEval,Int.cast_ofNat,Int.cast_neg,pow_zero,mul_one,v] at h
  linear_combination h
theorem full_syzygy_first (a b c d e f x y : K) :
    let u := PolarCubic.cubic a b c d e f x y 1
    let h := H a b c d e f x y 1
    let q := Theta a b c d e f x y 1
    let j := J a b c d e f x y 1
    let s := PolarCubic.s4Numerator a b c d e f
    let t := PolarCubic.s6Numerator a b c d e f
    let uk := 2*x*y
    let hk := Hk a b c d e f x y 1
    let qk := Thetak a b c d e f x y 1
    let jk := Jk a b c d e f x y 1
    let sk := PolarCubic.s4NumeratorK a b c d e f
    let tk := PolarCubic.s6NumeratorK a b c d e f
    54*j*jk=(((-1)*tk*(h^6))+(324*qk*(q^2))+((-34992)*hk*(s^4)*(u^5))+((-8748)*qk*(s^3)*(u^4))+((-144)*uk*(h^5)*(s^2))+((-6)*hk*t*(h^5))+(36*q*sk*(h^4))+(36*qk*s*(h^4))+(243*tk*(q^2)*(u^2))+((-174960)*h*uk*(s^4)*(u^4))+((-139968)*h*sk*(s^3)*(u^5))+((-34992)*q*uk*(s^3)*(u^3))+((-26244)*q*sk*(s^2)*(u^4))+((-2673)*tk*(h^2)*(s^2)*(u^4))+((-1944)*qk*(h^2)*(s^2)*(u^2))+((-720)*hk*u*(h^4)*(s^2))+((-324)*hk*(h^2)*(t^2)*(u^3))+((-324)*uk*(h^3)*(t^2)*(u^2))+((-288)*s*sk*u*(h^5))+((-216)*t*tk*(h^3)*(u^3))+((-54)*q*t*uk*(h^3))+((-54)*q*tk*u*(h^3))+((-54)*qk*t*u*(h^3))+(144*hk*q*s*(h^3))+(162*s*tk*(h^4)*(u^2))+(162*sk*t*(h^4)*(u^2))+(486*q*qk*t*(u^2))+(486*t*u*uk*(q^2))+((-10692)*t*uk*(h^2)*(s^2)*(u^3))+((-5346)*h*hk*t*(s^2)*(u^4))+((-5346)*s*sk*t*(h^2)*(u^4))+((-3888)*h*hk*q*(s^2)*(u^2))+((-3888)*q*s*sk*(h^2)*(u^2))+((-3888)*q*u*uk*(h^2)*(s^2))+((-162)*hk*q*t*u*(h^2))+(324*s*t*u*uk*(h^4))+(486*h*q*s*tk*(u^3))+(486*h*q*sk*t*(u^3))+(486*h*qk*s*t*(u^3))+(486*hk*q*s*t*(u^3))+(648*hk*s*t*(h^3)*(u^2))+(1458*h*q*s*t*uk*(u^2))) := by
  dsimp only
  let v : ℕ → K := fun i => match i with | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | 5 => f | _ => 0
  have h := data_identity1 v x y
  rw [FinalL1_evaluation,FinalR1_evaluation] at h
  simp only [← Right1Sum0_generated,← Right1Sum1_generated,← Right1Sum2_generated,← Right1Sum3_generated,← Right1Sum4_generated,← Right1Sum5_generated,← Right1Sum6_generated,← Right1Sum7_generated,← Right1Sum8_generated,← Right1Sum9_generated,← Right1Sum10_generated,← Right1Sum11_generated,← Right1Sum12_generated,← Right1Sum13_generated,← Right1Sum14_generated,← Right1Sum15_generated,← Right1Sum16_generated,← Right1Sum17_generated,← Right1Sum18_generated,← Right1Sum19_generated,← Right1Sum20_generated,← Right1Sum21_generated,← Right1Sum22_generated,← Right1Sum23_generated,← Right1Sum24_generated,← Right1Sum25_generated,← Right1Sum26_generated,← Right1Sum27_generated,← Right1Sum28_generated,← Right1Sum29_generated,← Right1Sum30_generated,← Right1Sum31_generated,← Right1Sum32_generated,← Right1Sum33_generated,← Right1Sum34_generated,← Right1Sum35_generated,← Right1Sum36_generated,← Right1Sum37_generated,← Right1Sum38_generated,← Right1Sum39_generated,← Right1Sum40_generated,← Right1Term41_generated,← Right1Term41p0_generated,← Right1Term40_generated,← Right1Term39_generated,← Right1Term39p1_generated,← Right1Term39p0_generated,← Right1Term38_generated,← Right1Term38p0_generated,← Right1Term37_generated,← Right1Term37p0_generated,← Right1Term36_generated,← Right1Term36p1_generated,← Right1Term36p0_generated,← Right1Term35_generated,← Right1Term35p0_generated,← Right1Term34_generated,← Right1Term34p1_generated,← Right1Term34p0_generated,← Right1Term33_generated,← Right1Term33p2_generated,← Right1Term33p1_generated,← Right1Term33p0_generated,← Right1Term32_generated,← Right1Term32p1_generated,← Right1Term32p0_generated,← Right1Term31_generated,← Right1Term31p1_generated,← Right1Term31p0_generated,← Right1Term30_generated,← Right1Term30p0_generated,← Right1Term29_generated,← Right1Term29p0_generated,← Right1Term28_generated,← Right1Term28p1_generated,← Right1Term28p0_generated,← Right1Term27_generated,← Right1Term27p1_generated,← Right1Term27p0_generated,← Right1Term26_generated,← Right1Term26p1_generated,← Right1Term26p0_generated,← Right1Term25_generated,← Right1Term25p1_generated,← Right1Term25p0_generated,← Right1Term24_generated,← Right1Term24p0_generated,← Right1Term23_generated,← Right1Term23p0_generated,← Right1Term22_generated,← Right1Term22p1_generated,← Right1Term22p0_generated,← Right1Term21_generated,← Right1Term21p0_generated,← Right1Term20_generated,← Right1Term20p1_generated,← Right1Term20p0_generated,← Right1Term19_generated,← Right1Term19p1_generated,← Right1Term19p0_generated,← Right1Term18_generated,← Right1Term18p2_generated,← Right1Term18p1_generated,← Right1Term18p0_generated,← Right1Term17_generated,← Right1Term17p1_generated,← Right1Term17p0_generated,← Right1Term16_generated,← Right1Term16p1_generated,← Right1Term16p0_generated,← Right1Term15_generated,← Right1Term15p1_generated,← Right1Term15p0_generated,← Right1Term14_generated,← Right1Term14p0_generated,← Right1Term13_generated,← Right1Term13p0_generated,← Right1Term12_generated,← Right1Term12p2_generated,← Right1Term12p1_generated,← Right1Term12p0_generated,← Right1Term11_generated,← Right1Term11p1_generated,← Right1Term11p0_generated,← Right1Term10_generated,← Right1Term10p2_generated,← Right1Term10p1_generated,← Right1Term10p0_generated,← Right1Term9_generated,← Right1Term9p1_generated,← Right1Term9p0_generated,← Right1Term8_generated,← Right1Term8p0_generated,← Right1Term7_generated,← Right1Term7p0_generated,← Right1Term6_generated,← Right1Term6p1_generated,← Right1Term6p0_generated,← Right1Term5_generated,← Right1Term5p1_generated,← Right1Term5p0_generated,← Right1Term4_generated,← Right1Term4p1_generated,← Right1Term4p0_generated,← Right1Term3_generated,← Right1Term3p0_generated,← Right1Term2_generated,← Right1Term2p0_generated,← Right1Term1_generated,← Right1Term1p1_generated,← Right1Term1p0_generated,← Right1Term0_generated,← Right1Term0p0_generated,← Left1_generated,← JJk_generated,← Right0Sum0_generated,← Right0Sum1_generated,← Right0Sum2_generated,← Right0Sum3_generated,← Right0Sum4_generated,← Right0Sum5_generated,← Right0Sum6_generated,← Right0Sum7_generated,← Right0Sum8_generated,← Right0Sum9_generated,← Right0Sum10_generated,← Right0Sum11_generated,← Right0Term12_generated,← Right0Term11_generated,← Right0Term10_generated,← Right0Term10p1_generated,← Right0Term10p0_generated,← Right0Term9_generated,← Right0Term9p0_generated,← Right0Term8_generated,← Right0Term8p0_generated,← Right0Term7_generated,← Right0Term7p0_generated,← Right0Term6_generated,← Right0Term6p0_generated,← Right0Term5_generated,← Right0Term5p1_generated,← Right0Term5p0_generated,← Right0Term4_generated,← Right0Term4p0_generated,← Right0Term3_generated,← Right0Term3p1_generated,← Right0Term3p0_generated,← Right0Term2_generated,← Right0Term2p0_generated,← Right0Term1_generated,← Right0Term1p0_generated,← Right0Term0_generated,← Right0Term0p0_generated,← Left0_generated,← Jp2_generated,← Thetap3_generated,← Thetap2_generated,← Hp6_generated,← Hp5_generated,← Hp4_generated,← Hp3_generated,← Hp2_generated,← Up5_generated,← Up4_generated,← Up3_generated,← Up2_generated,multiply_denote,scale_denote,merge_denote] at h
  simp only [H_evaluation,Theta_evaluation,J_evaluation,Hk_evaluation,Thetak_evaluation,Jk_evaluation,U_evaluation,Uk_evaluation,S_evaluation,T_evaluation,Sk_evaluation,Tk_evaluation,ringEval,Int.cast_ofNat,Int.cast_neg,pow_zero,mul_one,v] at h
  linear_combination h
/- Package the scalar identity and its first variation over dual numbers before
specializing the covariants, so normalization never expands their coefficients. -/
namespace JetPackaging
private lemma fst_numeral (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : TrivSqZeroExt K K).fst=(ofNat(n) : K) := rfl
private lemma snd_numeral (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : TrivSqZeroExt K K).snd=0 := rfl

lemma package
    (u0 uk0 h0 hk0 q0 qk0 j0 jk0 s0 sk0 t0 tk0 k : K)
    (hkSquare : k^2=0)
    (hbase : 27*j0^2=108*q0^3+36*s0*q0*h0^4-t0*h0^6+
      u0*(243*t0*u0*q0^2-8748*s0^3*q0*u0^3+486*s0*t0*q0*u0^2*h0-1944*s0^2*q0*u0*h0^2-
        54*t0*q0*h0^3-34992*s0^4*u0^4*h0-2673*s0^2*t0*u0^3*h0^2-108*t0^2*u0^2*h0^3+
        162*s0*t0*u0*h0^4-144*s0^2*h0^5))
    (hfirst : 54*j0*jk0=(((-1)*tk0*(h0^6))+(324*qk0*(q0^2))+((-34992)*hk0*(s0^4)*(u0^5))+((-8748)*qk0*(s0^3)*(u0^4))+((-144)*uk0*(h0^5)*(s0^2))+((-6)*hk0*t0*(h0^5))+(36*q0*sk0*(h0^4))+(36*qk0*s0*(h0^4))+(243*tk0*(q0^2)*(u0^2))+((-174960)*h0*uk0*(s0^4)*(u0^4))+((-139968)*h0*sk0*(s0^3)*(u0^5))+((-34992)*q0*uk0*(s0^3)*(u0^3))+((-26244)*q0*sk0*(s0^2)*(u0^4))+((-2673)*tk0*(h0^2)*(s0^2)*(u0^4))+((-1944)*qk0*(h0^2)*(s0^2)*(u0^2))+((-720)*hk0*u0*(h0^4)*(s0^2))+((-324)*hk0*(h0^2)*(t0^2)*(u0^3))+((-324)*uk0*(h0^3)*(t0^2)*(u0^2))+((-288)*s0*sk0*u0*(h0^5))+((-216)*t0*tk0*(h0^3)*(u0^3))+((-54)*q0*t0*uk0*(h0^3))+((-54)*q0*tk0*u0*(h0^3))+((-54)*qk0*t0*u0*(h0^3))+(144*hk0*q0*s0*(h0^3))+(162*s0*tk0*(h0^4)*(u0^2))+(162*sk0*t0*(h0^4)*(u0^2))+(486*q0*qk0*t0*(u0^2))+(486*t0*u0*uk0*(q0^2))+((-10692)*t0*uk0*(h0^2)*(s0^2)*(u0^3))+((-5346)*h0*hk0*t0*(s0^2)*(u0^4))+((-5346)*s0*sk0*t0*(h0^2)*(u0^4))+((-3888)*h0*hk0*q0*(s0^2)*(u0^2))+((-3888)*q0*s0*sk0*(h0^2)*(u0^2))+((-3888)*q0*u0*uk0*(h0^2)*(s0^2))+((-162)*hk0*q0*t0*u0*(h0^2))+(324*s0*t0*u0*uk0*(h0^4))+(486*h0*q0*s0*tk0*(u0^3))+(486*h0*q0*sk0*t0*(u0^3))+(486*h0*qk0*s0*t0*(u0^3))+(486*hk0*q0*s0*t0*(u0^3))+(648*hk0*s0*t0*(h0^3)*(u0^2))+(1458*h0*q0*s0*t0*uk0*(u0^2)))) :
    let u := u0+k*uk0
    let h := h0+k*hk0
    let q := q0+k*qk0
    let j := j0+k*jk0
    let s := s0+k*sk0
    let t := t0+k*tk0
    27*j^2=108*q^3+36*s*q*h^4-t*h^6+
      u*(243*t*u*q^2-8748*s^3*q*u^3+486*s*t*q*u^2*h-1944*s^2*q*u*h^2-
        54*t*q*h^3-34992*s^4*u^4*h-2673*s^2*t*u^3*h^2-108*t^2*u^2*h^3+
        162*s*t*u*h^4-144*s^2*h^5) := by
  dsimp only
  let u : TrivSqZeroExt K K := (u0,uk0)
  let h : TrivSqZeroExt K K := (h0,hk0)
  let q : TrivSqZeroExt K K := (q0,qk0)
  let j : TrivSqZeroExt K K := (j0,jk0)
  let s : TrivSqZeroExt K K := (s0,sk0)
  let t : TrivSqZeroExt K K := (t0,tk0)
  have hjet : (27*j^2 : TrivSqZeroExt K K)=108*q^3+36*s*q*h^4-t*h^6+
      u*(243*t*u*q^2-8748*s^3*q*u^3+486*s*t*q*u^2*h-1944*s^2*q*u*h^2-
        54*t*q*h^3-34992*s^4*u^4*h-2673*s^2*t*u^3*h^2-108*t^2*u^2*h^3+
        162*s*t*u*h^4-144*s^2*h^5) := by
    apply TrivSqZeroExt.ext
    · simpa only [fst_mul,fst_pow,fst_sub,fst_add,fst_numeral,fst_mk,
        u,h,q,j,s,t] using hbase
    · simp only [snd_mul,snd_pow,snd_sub,snd_add,snd_numeral,
        fst_mul,fst_pow,fst_sub,fst_add,fst_numeral,fst_mk,snd_mk,
        smul_eq_mul,op_smul_eq_smul,nsmul_eq_mul,u,h,q,j,s,t]
      norm_num
      linear_combination hfirst
  have hresult := congrArg (squareZeroEval k hkSquare) hjet
  simpa only [map_add,map_sub,map_mul,map_pow,map_ofNat,squareZeroEval_mk,
    u,h,q,j,s,t] using hresult

end JetPackaging

theorem full_syzygyJet (a b c d e f k x y : K) (hkSquare : k^2=0) :
    let u := PolarCubic.cubicJet a b c d e f k x y 1
    let h := HJet a b c d e f k x y 1
    let q := ThetaJet a b c d e f k x y 1
    let j := JJet a b c d e f k x y 1
    let s := PolarCubic.s4NumeratorJet a b c d e f k
    let t := PolarCubic.s6NumeratorJet a b c d e f k
    27*j^2=108*q^3+36*s*q*h^4-t*h^6+
      u*(243*t*u*q^2-8748*s^3*q*u^3+486*s*t*q*u^2*h-1944*s^2*q*u*h^2-
        54*t*q*h^3-34992*s^4*u^4*h-2673*s^2*t*u^3*h^2-108*t^2*u^2*h^3+
        162*s*t*u*h^4-144*s^2*h^5) := by
  have hresult := JetPackaging.package
    (PolarCubic.cubic a b c d e f x y 1) (2*x*y)
    (H a b c d e f x y 1) (Hk a b c d e f x y 1)
    (Theta a b c d e f x y 1) (Thetak a b c d e f x y 1)
    (J a b c d e f x y 1) (Jk a b c d e f x y 1)
    (PolarCubic.s4Numerator a b c d e f) (PolarCubic.s4NumeratorK a b c d e f)
    (PolarCubic.s6Numerator a b c d e f) (PolarCubic.s6NumeratorK a b c d e f)
    k hkSquare (full_syzygy a b c d e f x y) (full_syzygy_first a b c d e f x y)
  have hu : PolarCubic.cubic a b c d e f x y 1+k*(2*x*y)=
      PolarCubic.cubicJet a b c d e f k x y 1 := by
    unfold PolarCubic.cubicJet
    ring
  simpa only [hu,HJet,ThetaJet,JJet,PolarCubic.s4NumeratorJet,
    PolarCubic.s6NumeratorJet] using hresult
end PolarCovariants.IdentityData
#print axioms PolarCovariants.IdentityData.full_syzygyJet
