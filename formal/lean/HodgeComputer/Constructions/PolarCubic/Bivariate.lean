import HodgeComputer.Constructions.PolarCubic.Covariants
import HodgeComputer.Constructions.TransitiveCubic.BivariateExpressions
import HodgeComputer.Constructions.TransitiveCubic.BivariateDifferentiation
namespace PolarCovariants.IdentityData
open Lean.Grind.CommRing TransitiveSignedExpressions TransitiveBivariateExpressions
set_option maxRecDepth 131072
set_option maxHeartbeats 32000000
variable {K : Type*} [CommRing K]
def H_2_0 : Expr := ExpressionData.HCoeff201Expr
def H_1_2 : Expr := ExpressionData.HCoeff120Expr
def H_1_1 : Expr := ExpressionData.HCoeff111Expr
def H_1_0 : Expr := ExpressionData.HCoeff102Expr
def H_0_3 : Expr := ExpressionData.HCoeff030Expr
def H_0_2 : Expr := ExpressionData.HCoeff021Expr
def H_0_1 : Expr := ExpressionData.HCoeff012Expr
def HData : Biv := (.cons H_2_0 2 0 (.cons H_1_2 1 2 (.cons H_1_1 1 1 (.cons H_1_0 1 0 (.cons H_0_3 0 3 (.cons H_0_2 0 2 (.cons H_0_1 0 1 .nil)))))))
lemma H_2_0_eval (v : ℕ → K) :
    ringEval v H_2_0=HCoeff201 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma H_1_2_eval (v : ℕ → K) :
    ringEval v H_1_2=HCoeff120 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma H_1_1_eval (v : ℕ → K) :
    ringEval v H_1_1=HCoeff111 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma H_1_0_eval (v : ℕ → K) :
    ringEval v H_1_0=HCoeff102 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma H_0_3_eval (v : ℕ → K) :
    ringEval v H_0_3=HCoeff030 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma H_0_2_eval (v : ℕ → K) :
    ringEval v H_0_2=HCoeff021 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma H_0_1_eval (v : ℕ → K) :
    ringEval v H_0_1=HCoeff012 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma H_evaluation (v : ℕ → K) (x y : K) :
    denote v x y HData=H (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) x y 1 := by
  simp only [HData,denote,H,H_2_0_eval,H_1_2_eval,H_1_1_eval,H_1_0_eval,H_0_3_eval,H_0_2_eval,H_0_1_eval,one_pow,mul_one]
  ring
def Theta_6_0 : Expr := ExpressionData.ThetaCoeff600Expr
def Theta_5_1 : Expr := ExpressionData.ThetaCoeff510Expr
def Theta_5_0 : Expr := ExpressionData.ThetaCoeff501Expr
def Theta_4_2 : Expr := ExpressionData.ThetaCoeff420Expr
def Theta_4_1 : Expr := ExpressionData.ThetaCoeff411Expr
def Theta_4_0 : Expr := ExpressionData.ThetaCoeff402Expr
def Theta_3_3 : Expr := ExpressionData.ThetaCoeff330Expr
def Theta_3_2 : Expr := ExpressionData.ThetaCoeff321Expr
def Theta_3_1 : Expr := ExpressionData.ThetaCoeff312Expr
def Theta_3_0 : Expr := ExpressionData.ThetaCoeff303Expr
def Theta_2_4 : Expr := ExpressionData.ThetaCoeff240Expr
def Theta_2_3 : Expr := ExpressionData.ThetaCoeff231Expr
def Theta_2_2 : Expr := ExpressionData.ThetaCoeff222Expr
def Theta_2_1 : Expr := ExpressionData.ThetaCoeff213Expr
def Theta_2_0 : Expr := ExpressionData.ThetaCoeff204Expr
def Theta_1_5 : Expr := ExpressionData.ThetaCoeff150Expr
def Theta_1_4 : Expr := ExpressionData.ThetaCoeff141Expr
def Theta_1_3 : Expr := ExpressionData.ThetaCoeff132Expr
def Theta_1_2 : Expr := ExpressionData.ThetaCoeff123Expr
def Theta_1_1 : Expr := ExpressionData.ThetaCoeff114Expr
def Theta_1_0 : Expr := ExpressionData.ThetaCoeff105Expr
def Theta_0_6 : Expr := ExpressionData.ThetaCoeff060Expr
def Theta_0_5 : Expr := ExpressionData.ThetaCoeff051Expr
def Theta_0_4 : Expr := ExpressionData.ThetaCoeff042Expr
def Theta_0_3 : Expr := ExpressionData.ThetaCoeff033Expr
def Theta_0_2 : Expr := ExpressionData.ThetaCoeff024Expr
def Theta_0_1 : Expr := ExpressionData.ThetaCoeff015Expr
def Theta_0_0 : Expr := ExpressionData.ThetaCoeff006Expr
def ThetaData : Biv := (.cons Theta_6_0 6 0 (.cons Theta_5_1 5 1 (.cons Theta_5_0 5 0 (.cons Theta_4_2 4 2 (.cons Theta_4_1 4 1 (.cons Theta_4_0 4 0 (.cons Theta_3_3 3 3 (.cons Theta_3_2 3 2 (.cons Theta_3_1 3 1 (.cons Theta_3_0 3 0 (.cons Theta_2_4 2 4 (.cons Theta_2_3 2 3 (.cons Theta_2_2 2 2 (.cons Theta_2_1 2 1 (.cons Theta_2_0 2 0 (.cons Theta_1_5 1 5 (.cons Theta_1_4 1 4 (.cons Theta_1_3 1 3 (.cons Theta_1_2 1 2 (.cons Theta_1_1 1 1 (.cons Theta_1_0 1 0 (.cons Theta_0_6 0 6 (.cons Theta_0_5 0 5 (.cons Theta_0_4 0 4 (.cons Theta_0_3 0 3 (.cons Theta_0_2 0 2 (.cons Theta_0_1 0 1 (.cons Theta_0_0 0 0 .nil))))))))))))))))))))))))))))
lemma Theta_6_0_eval (v : ℕ → K) :
    ringEval v Theta_6_0=ThetaCoeff600 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Theta_5_1_eval (v : ℕ → K) :
    ringEval v Theta_5_1=ThetaCoeff510 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Theta_5_0_eval (v : ℕ → K) :
    ringEval v Theta_5_0=ThetaCoeff501 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Theta_4_2_eval (v : ℕ → K) :
    ringEval v Theta_4_2=ThetaCoeff420 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Theta_4_1_eval (v : ℕ → K) :
    ringEval v Theta_4_1=ThetaCoeff411 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Theta_4_0_eval (v : ℕ → K) :
    ringEval v Theta_4_0=ThetaCoeff402 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Theta_3_3_eval (v : ℕ → K) :
    ringEval v Theta_3_3=ThetaCoeff330 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Theta_3_2_eval (v : ℕ → K) :
    ringEval v Theta_3_2=ThetaCoeff321 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Theta_3_1_eval (v : ℕ → K) :
    ringEval v Theta_3_1=ThetaCoeff312 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Theta_3_0_eval (v : ℕ → K) :
    ringEval v Theta_3_0=ThetaCoeff303 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Theta_2_4_eval (v : ℕ → K) :
    ringEval v Theta_2_4=ThetaCoeff240 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Theta_2_3_eval (v : ℕ → K) :
    ringEval v Theta_2_3=ThetaCoeff231 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Theta_2_2_eval (v : ℕ → K) :
    ringEval v Theta_2_2=ThetaCoeff222 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Theta_2_1_eval (v : ℕ → K) :
    ringEval v Theta_2_1=ThetaCoeff213 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Theta_2_0_eval (v : ℕ → K) :
    ringEval v Theta_2_0=ThetaCoeff204 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Theta_1_5_eval (v : ℕ → K) :
    ringEval v Theta_1_5=ThetaCoeff150 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Theta_1_4_eval (v : ℕ → K) :
    ringEval v Theta_1_4=ThetaCoeff141 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Theta_1_3_eval (v : ℕ → K) :
    ringEval v Theta_1_3=ThetaCoeff132 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Theta_1_2_eval (v : ℕ → K) :
    ringEval v Theta_1_2=ThetaCoeff123 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Theta_1_1_eval (v : ℕ → K) :
    ringEval v Theta_1_1=ThetaCoeff114 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Theta_1_0_eval (v : ℕ → K) :
    ringEval v Theta_1_0=ThetaCoeff105 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Theta_0_6_eval (v : ℕ → K) :
    ringEval v Theta_0_6=ThetaCoeff060 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Theta_0_5_eval (v : ℕ → K) :
    ringEval v Theta_0_5=ThetaCoeff051 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Theta_0_4_eval (v : ℕ → K) :
    ringEval v Theta_0_4=ThetaCoeff042 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Theta_0_3_eval (v : ℕ → K) :
    ringEval v Theta_0_3=ThetaCoeff033 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Theta_0_2_eval (v : ℕ → K) :
    ringEval v Theta_0_2=ThetaCoeff024 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Theta_0_1_eval (v : ℕ → K) :
    ringEval v Theta_0_1=ThetaCoeff015 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Theta_0_0_eval (v : ℕ → K) :
    ringEval v Theta_0_0=ThetaCoeff006 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Theta_evaluation (v : ℕ → K) (x y : K) :
    denote v x y ThetaData=Theta (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) x y 1 := by
  simp only [ThetaData,denote,Theta,Theta_6_0_eval,Theta_5_1_eval,Theta_5_0_eval,Theta_4_2_eval,Theta_4_1_eval,Theta_4_0_eval,Theta_3_3_eval,Theta_3_2_eval,Theta_3_1_eval,Theta_3_0_eval,Theta_2_4_eval,Theta_2_3_eval,Theta_2_2_eval,Theta_2_1_eval,Theta_2_0_eval,Theta_1_5_eval,Theta_1_4_eval,Theta_1_3_eval,Theta_1_2_eval,Theta_1_1_eval,Theta_1_0_eval,Theta_0_6_eval,Theta_0_5_eval,Theta_0_4_eval,Theta_0_3_eval,Theta_0_2_eval,Theta_0_1_eval,Theta_0_0_eval,one_pow,mul_one]
  ring
def J_9_0 : Expr := ExpressionData.JCoeff900Expr
def J_8_1 : Expr := ExpressionData.JCoeff810Expr
def J_8_0 : Expr := ExpressionData.JCoeff801Expr
def J_7_2 : Expr := ExpressionData.JCoeff720Expr
def J_7_1 : Expr := ExpressionData.JCoeff711Expr
def J_6_3 : Expr := ExpressionData.JCoeff630Expr
def J_6_2 : Expr := ExpressionData.JCoeff621Expr
def J_6_1 : Expr := ExpressionData.JCoeff612Expr
def J_6_0 : Expr := ExpressionData.JCoeff603Expr
def J_5_4 : Expr := ExpressionData.JCoeff540Expr
def J_5_3 : Expr := ExpressionData.JCoeff531Expr
def J_5_2 : Expr := ExpressionData.JCoeff522Expr
def J_5_1 : Expr := ExpressionData.JCoeff513Expr
def J_5_0 : Expr := ExpressionData.JCoeff504Expr
def J_4_5 : Expr := ExpressionData.JCoeff450Expr
def J_4_4 : Expr := ExpressionData.JCoeff441Expr
def J_4_3 : Expr := ExpressionData.JCoeff432Expr
def J_4_2 : Expr := ExpressionData.JCoeff423Expr
def J_4_1 : Expr := ExpressionData.JCoeff414Expr
def J_4_0 : Expr := ExpressionData.JCoeff405Expr
def J_3_6 : Expr := ExpressionData.JCoeff360Expr
def J_3_5 : Expr := ExpressionData.JCoeff351Expr
def J_3_4 : Expr := ExpressionData.JCoeff342Expr
def J_3_3 : Expr := ExpressionData.JCoeff333Expr
def J_3_2 : Expr := ExpressionData.JCoeff324Expr
def J_3_1 : Expr := ExpressionData.JCoeff315Expr
def J_3_0 : Expr := ExpressionData.JCoeff306Expr
def J_2_7 : Expr := ExpressionData.JCoeff270Expr
def J_2_6 : Expr := ExpressionData.JCoeff261Expr
def J_2_5 : Expr := ExpressionData.JCoeff252Expr
def J_2_4 : Expr := ExpressionData.JCoeff243Expr
def J_2_3 : Expr := ExpressionData.JCoeff234Expr
def J_2_2 : Expr := ExpressionData.JCoeff225Expr
def J_2_1 : Expr := ExpressionData.JCoeff216Expr
def J_1_8 : Expr := ExpressionData.JCoeff180Expr
def J_1_7 : Expr := ExpressionData.JCoeff171Expr
def J_1_6 : Expr := ExpressionData.JCoeff162Expr
def J_1_5 : Expr := ExpressionData.JCoeff153Expr
def J_1_4 : Expr := ExpressionData.JCoeff144Expr
def J_1_3 : Expr := ExpressionData.JCoeff135Expr
def J_1_2 : Expr := ExpressionData.JCoeff126Expr
def J_1_1 : Expr := ExpressionData.JCoeff117Expr
def J_1_0 : Expr := ExpressionData.JCoeff108Expr
def J_0_9 : Expr := ExpressionData.JCoeff090Expr
def J_0_8 : Expr := ExpressionData.JCoeff081Expr
def J_0_7 : Expr := ExpressionData.JCoeff072Expr
def J_0_6 : Expr := ExpressionData.JCoeff063Expr
def J_0_5 : Expr := ExpressionData.JCoeff054Expr
def J_0_4 : Expr := ExpressionData.JCoeff045Expr
def J_0_3 : Expr := ExpressionData.JCoeff036Expr
def J_0_2 : Expr := ExpressionData.JCoeff027Expr
def J_0_1 : Expr := ExpressionData.JCoeff018Expr
def J_0_0 : Expr := ExpressionData.JCoeff009Expr
def JData : Biv := (.cons J_9_0 9 0 (.cons J_8_1 8 1 (.cons J_8_0 8 0 (.cons J_7_2 7 2 (.cons J_7_1 7 1 (.cons J_6_3 6 3 (.cons J_6_2 6 2 (.cons J_6_1 6 1 (.cons J_6_0 6 0 (.cons J_5_4 5 4 (.cons J_5_3 5 3 (.cons J_5_2 5 2 (.cons J_5_1 5 1 (.cons J_5_0 5 0 (.cons J_4_5 4 5 (.cons J_4_4 4 4 (.cons J_4_3 4 3 (.cons J_4_2 4 2 (.cons J_4_1 4 1 (.cons J_4_0 4 0 (.cons J_3_6 3 6 (.cons J_3_5 3 5 (.cons J_3_4 3 4 (.cons J_3_3 3 3 (.cons J_3_2 3 2 (.cons J_3_1 3 1 (.cons J_3_0 3 0 (.cons J_2_7 2 7 (.cons J_2_6 2 6 (.cons J_2_5 2 5 (.cons J_2_4 2 4 (.cons J_2_3 2 3 (.cons J_2_2 2 2 (.cons J_2_1 2 1 (.cons J_1_8 1 8 (.cons J_1_7 1 7 (.cons J_1_6 1 6 (.cons J_1_5 1 5 (.cons J_1_4 1 4 (.cons J_1_3 1 3 (.cons J_1_2 1 2 (.cons J_1_1 1 1 (.cons J_1_0 1 0 (.cons J_0_9 0 9 (.cons J_0_8 0 8 (.cons J_0_7 0 7 (.cons J_0_6 0 6 (.cons J_0_5 0 5 (.cons J_0_4 0 4 (.cons J_0_3 0 3 (.cons J_0_2 0 2 (.cons J_0_1 0 1 (.cons J_0_0 0 0 .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))
lemma J_9_0_eval (v : ℕ → K) :
    ringEval v J_9_0=JCoeff900 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_8_1_eval (v : ℕ → K) :
    ringEval v J_8_1=JCoeff810 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_8_0_eval (v : ℕ → K) :
    ringEval v J_8_0=JCoeff801 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_7_2_eval (v : ℕ → K) :
    ringEval v J_7_2=JCoeff720 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_7_1_eval (v : ℕ → K) :
    ringEval v J_7_1=JCoeff711 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_6_3_eval (v : ℕ → K) :
    ringEval v J_6_3=JCoeff630 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_6_2_eval (v : ℕ → K) :
    ringEval v J_6_2=JCoeff621 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_6_1_eval (v : ℕ → K) :
    ringEval v J_6_1=JCoeff612 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_6_0_eval (v : ℕ → K) :
    ringEval v J_6_0=JCoeff603 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_5_4_eval (v : ℕ → K) :
    ringEval v J_5_4=JCoeff540 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_5_3_eval (v : ℕ → K) :
    ringEval v J_5_3=JCoeff531 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_5_2_eval (v : ℕ → K) :
    ringEval v J_5_2=JCoeff522 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_5_1_eval (v : ℕ → K) :
    ringEval v J_5_1=JCoeff513 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_5_0_eval (v : ℕ → K) :
    ringEval v J_5_0=JCoeff504 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_4_5_eval (v : ℕ → K) :
    ringEval v J_4_5=JCoeff450 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_4_4_eval (v : ℕ → K) :
    ringEval v J_4_4=JCoeff441 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_4_3_eval (v : ℕ → K) :
    ringEval v J_4_3=JCoeff432 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_4_2_eval (v : ℕ → K) :
    ringEval v J_4_2=JCoeff423 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_4_1_eval (v : ℕ → K) :
    ringEval v J_4_1=JCoeff414 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_4_0_eval (v : ℕ → K) :
    ringEval v J_4_0=JCoeff405 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_3_6_eval (v : ℕ → K) :
    ringEval v J_3_6=JCoeff360 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_3_5_eval (v : ℕ → K) :
    ringEval v J_3_5=JCoeff351 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_3_4_eval (v : ℕ → K) :
    ringEval v J_3_4=JCoeff342 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_3_3_eval (v : ℕ → K) :
    ringEval v J_3_3=JCoeff333 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_3_2_eval (v : ℕ → K) :
    ringEval v J_3_2=JCoeff324 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_3_1_eval (v : ℕ → K) :
    ringEval v J_3_1=JCoeff315 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_3_0_eval (v : ℕ → K) :
    ringEval v J_3_0=JCoeff306 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_2_7_eval (v : ℕ → K) :
    ringEval v J_2_7=JCoeff270 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_2_6_eval (v : ℕ → K) :
    ringEval v J_2_6=JCoeff261 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_2_5_eval (v : ℕ → K) :
    ringEval v J_2_5=JCoeff252 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_2_4_eval (v : ℕ → K) :
    ringEval v J_2_4=JCoeff243 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_2_3_eval (v : ℕ → K) :
    ringEval v J_2_3=JCoeff234 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_2_2_eval (v : ℕ → K) :
    ringEval v J_2_2=JCoeff225 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_2_1_eval (v : ℕ → K) :
    ringEval v J_2_1=JCoeff216 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_1_8_eval (v : ℕ → K) :
    ringEval v J_1_8=JCoeff180 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_1_7_eval (v : ℕ → K) :
    ringEval v J_1_7=JCoeff171 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_1_6_eval (v : ℕ → K) :
    ringEval v J_1_6=JCoeff162 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_1_5_eval (v : ℕ → K) :
    ringEval v J_1_5=JCoeff153 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_1_4_eval (v : ℕ → K) :
    ringEval v J_1_4=JCoeff144 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_1_3_eval (v : ℕ → K) :
    ringEval v J_1_3=JCoeff135 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_1_2_eval (v : ℕ → K) :
    ringEval v J_1_2=JCoeff126 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_1_1_eval (v : ℕ → K) :
    ringEval v J_1_1=JCoeff117 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_1_0_eval (v : ℕ → K) :
    ringEval v J_1_0=JCoeff108 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_0_9_eval (v : ℕ → K) :
    ringEval v J_0_9=JCoeff090 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_0_8_eval (v : ℕ → K) :
    ringEval v J_0_8=JCoeff081 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_0_7_eval (v : ℕ → K) :
    ringEval v J_0_7=JCoeff072 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_0_6_eval (v : ℕ → K) :
    ringEval v J_0_6=JCoeff063 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_0_5_eval (v : ℕ → K) :
    ringEval v J_0_5=JCoeff054 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_0_4_eval (v : ℕ → K) :
    ringEval v J_0_4=JCoeff045 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_0_3_eval (v : ℕ → K) :
    ringEval v J_0_3=JCoeff036 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_0_2_eval (v : ℕ → K) :
    ringEval v J_0_2=JCoeff027 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_0_1_eval (v : ℕ → K) :
    ringEval v J_0_1=JCoeff018 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_0_0_eval (v : ℕ → K) :
    ringEval v J_0_0=JCoeff009 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma J_evaluation (v : ℕ → K) (x y : K) :
    denote v x y JData=J (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) x y 1 := by
  simp only [JData,denote,J,J_9_0_eval,J_8_1_eval,J_8_0_eval,J_7_2_eval,J_7_1_eval,J_6_3_eval,J_6_2_eval,J_6_1_eval,J_6_0_eval,J_5_4_eval,J_5_3_eval,J_5_2_eval,J_5_1_eval,J_5_0_eval,J_4_5_eval,J_4_4_eval,J_4_3_eval,J_4_2_eval,J_4_1_eval,J_4_0_eval,J_3_6_eval,J_3_5_eval,J_3_4_eval,J_3_3_eval,J_3_2_eval,J_3_1_eval,J_3_0_eval,J_2_7_eval,J_2_6_eval,J_2_5_eval,J_2_4_eval,J_2_3_eval,J_2_2_eval,J_2_1_eval,J_1_8_eval,J_1_7_eval,J_1_6_eval,J_1_5_eval,J_1_4_eval,J_1_3_eval,J_1_2_eval,J_1_1_eval,J_1_0_eval,J_0_9_eval,J_0_8_eval,J_0_7_eval,J_0_6_eval,J_0_5_eval,J_0_4_eval,J_0_3_eval,J_0_2_eval,J_0_1_eval,J_0_0_eval,one_pow,mul_one]
  ring
def Hk_2_1 : Expr := ExpressionData.HkCoeff210Expr
def Hk_1_0 : Expr := ExpressionData.HkCoeff102Expr
def Hk_0_3 : Expr := ExpressionData.HkCoeff030Expr
def Hk_0_1 : Expr := ExpressionData.HkCoeff012Expr
def HkData : Biv := (.cons Hk_2_1 2 1 (.cons Hk_1_0 1 0 (.cons Hk_0_3 0 3 (.cons Hk_0_1 0 1 .nil))))
lemma Hk_2_1_eval (v : ℕ → K) :
    ringEval v Hk_2_1=HkCoeff210 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Hk_1_0_eval (v : ℕ → K) :
    ringEval v Hk_1_0=HkCoeff102 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Hk_0_3_eval (v : ℕ → K) :
    ringEval v Hk_0_3=HkCoeff030 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Hk_0_1_eval (v : ℕ → K) :
    ringEval v Hk_0_1=HkCoeff012 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Hk_evaluation (v : ℕ → K) (x y : K) :
    denote v x y HkData=Hk (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) x y 1 := by
  simp only [HkData,denote,Hk,Hk_2_1_eval,Hk_1_0_eval,Hk_0_3_eval,Hk_0_1_eval,one_pow,mul_one]
  ring
def Thetak_5_1 : Expr := ExpressionData.ThetakCoeff510Expr
def Thetak_5_0 : Expr := ExpressionData.ThetakCoeff501Expr
def Thetak_4_2 : Expr := ExpressionData.ThetakCoeff420Expr
def Thetak_4_1 : Expr := ExpressionData.ThetakCoeff411Expr
def Thetak_4_0 : Expr := ExpressionData.ThetakCoeff402Expr
def Thetak_3_3 : Expr := ExpressionData.ThetakCoeff330Expr
def Thetak_3_2 : Expr := ExpressionData.ThetakCoeff321Expr
def Thetak_3_1 : Expr := ExpressionData.ThetakCoeff312Expr
def Thetak_3_0 : Expr := ExpressionData.ThetakCoeff303Expr
def Thetak_2_4 : Expr := ExpressionData.ThetakCoeff240Expr
def Thetak_2_3 : Expr := ExpressionData.ThetakCoeff231Expr
def Thetak_2_2 : Expr := ExpressionData.ThetakCoeff222Expr
def Thetak_2_1 : Expr := ExpressionData.ThetakCoeff213Expr
def Thetak_2_0 : Expr := ExpressionData.ThetakCoeff204Expr
def Thetak_1_5 : Expr := ExpressionData.ThetakCoeff150Expr
def Thetak_1_4 : Expr := ExpressionData.ThetakCoeff141Expr
def Thetak_1_3 : Expr := ExpressionData.ThetakCoeff132Expr
def Thetak_1_2 : Expr := ExpressionData.ThetakCoeff123Expr
def Thetak_1_1 : Expr := ExpressionData.ThetakCoeff114Expr
def Thetak_1_0 : Expr := ExpressionData.ThetakCoeff105Expr
def Thetak_0_6 : Expr := ExpressionData.ThetakCoeff060Expr
def Thetak_0_5 : Expr := ExpressionData.ThetakCoeff051Expr
def Thetak_0_4 : Expr := ExpressionData.ThetakCoeff042Expr
def Thetak_0_3 : Expr := ExpressionData.ThetakCoeff033Expr
def Thetak_0_2 : Expr := ExpressionData.ThetakCoeff024Expr
def Thetak_0_1 : Expr := ExpressionData.ThetakCoeff015Expr
def Thetak_0_0 : Expr := ExpressionData.ThetakCoeff006Expr
def ThetakData : Biv := (.cons Thetak_5_1 5 1 (.cons Thetak_5_0 5 0 (.cons Thetak_4_2 4 2 (.cons Thetak_4_1 4 1 (.cons Thetak_4_0 4 0 (.cons Thetak_3_3 3 3 (.cons Thetak_3_2 3 2 (.cons Thetak_3_1 3 1 (.cons Thetak_3_0 3 0 (.cons Thetak_2_4 2 4 (.cons Thetak_2_3 2 3 (.cons Thetak_2_2 2 2 (.cons Thetak_2_1 2 1 (.cons Thetak_2_0 2 0 (.cons Thetak_1_5 1 5 (.cons Thetak_1_4 1 4 (.cons Thetak_1_3 1 3 (.cons Thetak_1_2 1 2 (.cons Thetak_1_1 1 1 (.cons Thetak_1_0 1 0 (.cons Thetak_0_6 0 6 (.cons Thetak_0_5 0 5 (.cons Thetak_0_4 0 4 (.cons Thetak_0_3 0 3 (.cons Thetak_0_2 0 2 (.cons Thetak_0_1 0 1 (.cons Thetak_0_0 0 0 .nil)))))))))))))))))))))))))))
lemma Thetak_5_1_eval (v : ℕ → K) :
    ringEval v Thetak_5_1=ThetakCoeff510 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Thetak_5_0_eval (v : ℕ → K) :
    ringEval v Thetak_5_0=ThetakCoeff501 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Thetak_4_2_eval (v : ℕ → K) :
    ringEval v Thetak_4_2=ThetakCoeff420 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Thetak_4_1_eval (v : ℕ → K) :
    ringEval v Thetak_4_1=ThetakCoeff411 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Thetak_4_0_eval (v : ℕ → K) :
    ringEval v Thetak_4_0=ThetakCoeff402 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Thetak_3_3_eval (v : ℕ → K) :
    ringEval v Thetak_3_3=ThetakCoeff330 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Thetak_3_2_eval (v : ℕ → K) :
    ringEval v Thetak_3_2=ThetakCoeff321 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Thetak_3_1_eval (v : ℕ → K) :
    ringEval v Thetak_3_1=ThetakCoeff312 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Thetak_3_0_eval (v : ℕ → K) :
    ringEval v Thetak_3_0=ThetakCoeff303 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Thetak_2_4_eval (v : ℕ → K) :
    ringEval v Thetak_2_4=ThetakCoeff240 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Thetak_2_3_eval (v : ℕ → K) :
    ringEval v Thetak_2_3=ThetakCoeff231 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Thetak_2_2_eval (v : ℕ → K) :
    ringEval v Thetak_2_2=ThetakCoeff222 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Thetak_2_1_eval (v : ℕ → K) :
    ringEval v Thetak_2_1=ThetakCoeff213 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Thetak_2_0_eval (v : ℕ → K) :
    ringEval v Thetak_2_0=ThetakCoeff204 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Thetak_1_5_eval (v : ℕ → K) :
    ringEval v Thetak_1_5=ThetakCoeff150 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Thetak_1_4_eval (v : ℕ → K) :
    ringEval v Thetak_1_4=ThetakCoeff141 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Thetak_1_3_eval (v : ℕ → K) :
    ringEval v Thetak_1_3=ThetakCoeff132 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Thetak_1_2_eval (v : ℕ → K) :
    ringEval v Thetak_1_2=ThetakCoeff123 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Thetak_1_1_eval (v : ℕ → K) :
    ringEval v Thetak_1_1=ThetakCoeff114 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Thetak_1_0_eval (v : ℕ → K) :
    ringEval v Thetak_1_0=ThetakCoeff105 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Thetak_0_6_eval (v : ℕ → K) :
    ringEval v Thetak_0_6=ThetakCoeff060 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Thetak_0_5_eval (v : ℕ → K) :
    ringEval v Thetak_0_5=ThetakCoeff051 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Thetak_0_4_eval (v : ℕ → K) :
    ringEval v Thetak_0_4=ThetakCoeff042 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Thetak_0_3_eval (v : ℕ → K) :
    ringEval v Thetak_0_3=ThetakCoeff033 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Thetak_0_2_eval (v : ℕ → K) :
    ringEval v Thetak_0_2=ThetakCoeff024 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Thetak_0_1_eval (v : ℕ → K) :
    ringEval v Thetak_0_1=ThetakCoeff015 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Thetak_0_0_eval (v : ℕ → K) :
    ringEval v Thetak_0_0=ThetakCoeff006 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Thetak_evaluation (v : ℕ → K) (x y : K) :
    denote v x y ThetakData=Thetak (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) x y 1 := by
  simp only [ThetakData,denote,Thetak,Thetak_5_1_eval,Thetak_5_0_eval,Thetak_4_2_eval,Thetak_4_1_eval,Thetak_4_0_eval,Thetak_3_3_eval,Thetak_3_2_eval,Thetak_3_1_eval,Thetak_3_0_eval,Thetak_2_4_eval,Thetak_2_3_eval,Thetak_2_2_eval,Thetak_2_1_eval,Thetak_2_0_eval,Thetak_1_5_eval,Thetak_1_4_eval,Thetak_1_3_eval,Thetak_1_2_eval,Thetak_1_1_eval,Thetak_1_0_eval,Thetak_0_6_eval,Thetak_0_5_eval,Thetak_0_4_eval,Thetak_0_3_eval,Thetak_0_2_eval,Thetak_0_1_eval,Thetak_0_0_eval,one_pow,mul_one]
  ring
def Jk_9_0 : Expr := ExpressionData.JkCoeff900Expr
def Jk_8_1 : Expr := ExpressionData.JkCoeff810Expr
def Jk_8_0 : Expr := ExpressionData.JkCoeff801Expr
def Jk_7_2 : Expr := ExpressionData.JkCoeff720Expr
def Jk_7_1 : Expr := ExpressionData.JkCoeff711Expr
def Jk_7_0 : Expr := ExpressionData.JkCoeff702Expr
def Jk_6_3 : Expr := ExpressionData.JkCoeff630Expr
def Jk_6_2 : Expr := ExpressionData.JkCoeff621Expr
def Jk_6_1 : Expr := ExpressionData.JkCoeff612Expr
def Jk_6_0 : Expr := ExpressionData.JkCoeff603Expr
def Jk_5_4 : Expr := ExpressionData.JkCoeff540Expr
def Jk_5_3 : Expr := ExpressionData.JkCoeff531Expr
def Jk_5_2 : Expr := ExpressionData.JkCoeff522Expr
def Jk_5_1 : Expr := ExpressionData.JkCoeff513Expr
def Jk_5_0 : Expr := ExpressionData.JkCoeff504Expr
def Jk_4_5 : Expr := ExpressionData.JkCoeff450Expr
def Jk_4_4 : Expr := ExpressionData.JkCoeff441Expr
def Jk_4_3 : Expr := ExpressionData.JkCoeff432Expr
def Jk_4_2 : Expr := ExpressionData.JkCoeff423Expr
def Jk_4_1 : Expr := ExpressionData.JkCoeff414Expr
def Jk_4_0 : Expr := ExpressionData.JkCoeff405Expr
def Jk_3_6 : Expr := ExpressionData.JkCoeff360Expr
def Jk_3_5 : Expr := ExpressionData.JkCoeff351Expr
def Jk_3_4 : Expr := ExpressionData.JkCoeff342Expr
def Jk_3_3 : Expr := ExpressionData.JkCoeff333Expr
def Jk_3_2 : Expr := ExpressionData.JkCoeff324Expr
def Jk_3_1 : Expr := ExpressionData.JkCoeff315Expr
def Jk_3_0 : Expr := ExpressionData.JkCoeff306Expr
def Jk_2_7 : Expr := ExpressionData.JkCoeff270Expr
def Jk_2_6 : Expr := ExpressionData.JkCoeff261Expr
def Jk_2_5 : Expr := ExpressionData.JkCoeff252Expr
def Jk_2_4 : Expr := ExpressionData.JkCoeff243Expr
def Jk_2_3 : Expr := ExpressionData.JkCoeff234Expr
def Jk_2_2 : Expr := ExpressionData.JkCoeff225Expr
def Jk_2_1 : Expr := ExpressionData.JkCoeff216Expr
def Jk_2_0 : Expr := ExpressionData.JkCoeff207Expr
def Jk_1_8 : Expr := ExpressionData.JkCoeff180Expr
def Jk_1_7 : Expr := ExpressionData.JkCoeff171Expr
def Jk_1_6 : Expr := ExpressionData.JkCoeff162Expr
def Jk_1_5 : Expr := ExpressionData.JkCoeff153Expr
def Jk_1_4 : Expr := ExpressionData.JkCoeff144Expr
def Jk_1_3 : Expr := ExpressionData.JkCoeff135Expr
def Jk_1_2 : Expr := ExpressionData.JkCoeff126Expr
def Jk_1_1 : Expr := ExpressionData.JkCoeff117Expr
def Jk_1_0 : Expr := ExpressionData.JkCoeff108Expr
def Jk_0_9 : Expr := ExpressionData.JkCoeff090Expr
def Jk_0_8 : Expr := ExpressionData.JkCoeff081Expr
def Jk_0_7 : Expr := ExpressionData.JkCoeff072Expr
def Jk_0_6 : Expr := ExpressionData.JkCoeff063Expr
def Jk_0_5 : Expr := ExpressionData.JkCoeff054Expr
def Jk_0_4 : Expr := ExpressionData.JkCoeff045Expr
def Jk_0_3 : Expr := ExpressionData.JkCoeff036Expr
def Jk_0_2 : Expr := ExpressionData.JkCoeff027Expr
def Jk_0_1 : Expr := ExpressionData.JkCoeff018Expr
def Jk_0_0 : Expr := ExpressionData.JkCoeff009Expr
def JkData : Biv := (.cons Jk_9_0 9 0 (.cons Jk_8_1 8 1 (.cons Jk_8_0 8 0 (.cons Jk_7_2 7 2 (.cons Jk_7_1 7 1 (.cons Jk_7_0 7 0 (.cons Jk_6_3 6 3 (.cons Jk_6_2 6 2 (.cons Jk_6_1 6 1 (.cons Jk_6_0 6 0 (.cons Jk_5_4 5 4 (.cons Jk_5_3 5 3 (.cons Jk_5_2 5 2 (.cons Jk_5_1 5 1 (.cons Jk_5_0 5 0 (.cons Jk_4_5 4 5 (.cons Jk_4_4 4 4 (.cons Jk_4_3 4 3 (.cons Jk_4_2 4 2 (.cons Jk_4_1 4 1 (.cons Jk_4_0 4 0 (.cons Jk_3_6 3 6 (.cons Jk_3_5 3 5 (.cons Jk_3_4 3 4 (.cons Jk_3_3 3 3 (.cons Jk_3_2 3 2 (.cons Jk_3_1 3 1 (.cons Jk_3_0 3 0 (.cons Jk_2_7 2 7 (.cons Jk_2_6 2 6 (.cons Jk_2_5 2 5 (.cons Jk_2_4 2 4 (.cons Jk_2_3 2 3 (.cons Jk_2_2 2 2 (.cons Jk_2_1 2 1 (.cons Jk_2_0 2 0 (.cons Jk_1_8 1 8 (.cons Jk_1_7 1 7 (.cons Jk_1_6 1 6 (.cons Jk_1_5 1 5 (.cons Jk_1_4 1 4 (.cons Jk_1_3 1 3 (.cons Jk_1_2 1 2 (.cons Jk_1_1 1 1 (.cons Jk_1_0 1 0 (.cons Jk_0_9 0 9 (.cons Jk_0_8 0 8 (.cons Jk_0_7 0 7 (.cons Jk_0_6 0 6 (.cons Jk_0_5 0 5 (.cons Jk_0_4 0 4 (.cons Jk_0_3 0 3 (.cons Jk_0_2 0 2 (.cons Jk_0_1 0 1 (.cons Jk_0_0 0 0 .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))
lemma Jk_9_0_eval (v : ℕ → K) :
    ringEval v Jk_9_0=JkCoeff900 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_8_1_eval (v : ℕ → K) :
    ringEval v Jk_8_1=JkCoeff810 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_8_0_eval (v : ℕ → K) :
    ringEval v Jk_8_0=JkCoeff801 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_7_2_eval (v : ℕ → K) :
    ringEval v Jk_7_2=JkCoeff720 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_7_1_eval (v : ℕ → K) :
    ringEval v Jk_7_1=JkCoeff711 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_7_0_eval (v : ℕ → K) :
    ringEval v Jk_7_0=JkCoeff702 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_6_3_eval (v : ℕ → K) :
    ringEval v Jk_6_3=JkCoeff630 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_6_2_eval (v : ℕ → K) :
    ringEval v Jk_6_2=JkCoeff621 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_6_1_eval (v : ℕ → K) :
    ringEval v Jk_6_1=JkCoeff612 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_6_0_eval (v : ℕ → K) :
    ringEval v Jk_6_0=JkCoeff603 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_5_4_eval (v : ℕ → K) :
    ringEval v Jk_5_4=JkCoeff540 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_5_3_eval (v : ℕ → K) :
    ringEval v Jk_5_3=JkCoeff531 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_5_2_eval (v : ℕ → K) :
    ringEval v Jk_5_2=JkCoeff522 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_5_1_eval (v : ℕ → K) :
    ringEval v Jk_5_1=JkCoeff513 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_5_0_eval (v : ℕ → K) :
    ringEval v Jk_5_0=JkCoeff504 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_4_5_eval (v : ℕ → K) :
    ringEval v Jk_4_5=JkCoeff450 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_4_4_eval (v : ℕ → K) :
    ringEval v Jk_4_4=JkCoeff441 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_4_3_eval (v : ℕ → K) :
    ringEval v Jk_4_3=JkCoeff432 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_4_2_eval (v : ℕ → K) :
    ringEval v Jk_4_2=JkCoeff423 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_4_1_eval (v : ℕ → K) :
    ringEval v Jk_4_1=JkCoeff414 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_4_0_eval (v : ℕ → K) :
    ringEval v Jk_4_0=JkCoeff405 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_3_6_eval (v : ℕ → K) :
    ringEval v Jk_3_6=JkCoeff360 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_3_5_eval (v : ℕ → K) :
    ringEval v Jk_3_5=JkCoeff351 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_3_4_eval (v : ℕ → K) :
    ringEval v Jk_3_4=JkCoeff342 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_3_3_eval (v : ℕ → K) :
    ringEval v Jk_3_3=JkCoeff333 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_3_2_eval (v : ℕ → K) :
    ringEval v Jk_3_2=JkCoeff324 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_3_1_eval (v : ℕ → K) :
    ringEval v Jk_3_1=JkCoeff315 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_3_0_eval (v : ℕ → K) :
    ringEval v Jk_3_0=JkCoeff306 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_2_7_eval (v : ℕ → K) :
    ringEval v Jk_2_7=JkCoeff270 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_2_6_eval (v : ℕ → K) :
    ringEval v Jk_2_6=JkCoeff261 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_2_5_eval (v : ℕ → K) :
    ringEval v Jk_2_5=JkCoeff252 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_2_4_eval (v : ℕ → K) :
    ringEval v Jk_2_4=JkCoeff243 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_2_3_eval (v : ℕ → K) :
    ringEval v Jk_2_3=JkCoeff234 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_2_2_eval (v : ℕ → K) :
    ringEval v Jk_2_2=JkCoeff225 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_2_1_eval (v : ℕ → K) :
    ringEval v Jk_2_1=JkCoeff216 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_2_0_eval (v : ℕ → K) :
    ringEval v Jk_2_0=JkCoeff207 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_1_8_eval (v : ℕ → K) :
    ringEval v Jk_1_8=JkCoeff180 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_1_7_eval (v : ℕ → K) :
    ringEval v Jk_1_7=JkCoeff171 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_1_6_eval (v : ℕ → K) :
    ringEval v Jk_1_6=JkCoeff162 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_1_5_eval (v : ℕ → K) :
    ringEval v Jk_1_5=JkCoeff153 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_1_4_eval (v : ℕ → K) :
    ringEval v Jk_1_4=JkCoeff144 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_1_3_eval (v : ℕ → K) :
    ringEval v Jk_1_3=JkCoeff135 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_1_2_eval (v : ℕ → K) :
    ringEval v Jk_1_2=JkCoeff126 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_1_1_eval (v : ℕ → K) :
    ringEval v Jk_1_1=JkCoeff117 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_1_0_eval (v : ℕ → K) :
    ringEval v Jk_1_0=JkCoeff108 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_0_9_eval (v : ℕ → K) :
    ringEval v Jk_0_9=JkCoeff090 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_0_8_eval (v : ℕ → K) :
    ringEval v Jk_0_8=JkCoeff081 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_0_7_eval (v : ℕ → K) :
    ringEval v Jk_0_7=JkCoeff072 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_0_6_eval (v : ℕ → K) :
    ringEval v Jk_0_6=JkCoeff063 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_0_5_eval (v : ℕ → K) :
    ringEval v Jk_0_5=JkCoeff054 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_0_4_eval (v : ℕ → K) :
    ringEval v Jk_0_4=JkCoeff045 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_0_3_eval (v : ℕ → K) :
    ringEval v Jk_0_3=JkCoeff036 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_0_2_eval (v : ℕ → K) :
    ringEval v Jk_0_2=JkCoeff027 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_0_1_eval (v : ℕ → K) :
    ringEval v Jk_0_1=JkCoeff018 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_0_0_eval (v : ℕ → K) :
    ringEval v Jk_0_0=JkCoeff009 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by rfl
lemma Jk_evaluation (v : ℕ → K) (x y : K) :
    denote v x y JkData=Jk (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) x y 1 := by
  simp only [JkData,denote,Jk,Jk_9_0_eval,Jk_8_1_eval,Jk_8_0_eval,Jk_7_2_eval,Jk_7_1_eval,Jk_7_0_eval,Jk_6_3_eval,Jk_6_2_eval,Jk_6_1_eval,Jk_6_0_eval,Jk_5_4_eval,Jk_5_3_eval,Jk_5_2_eval,Jk_5_1_eval,Jk_5_0_eval,Jk_4_5_eval,Jk_4_4_eval,Jk_4_3_eval,Jk_4_2_eval,Jk_4_1_eval,Jk_4_0_eval,Jk_3_6_eval,Jk_3_5_eval,Jk_3_4_eval,Jk_3_3_eval,Jk_3_2_eval,Jk_3_1_eval,Jk_3_0_eval,Jk_2_7_eval,Jk_2_6_eval,Jk_2_5_eval,Jk_2_4_eval,Jk_2_3_eval,Jk_2_2_eval,Jk_2_1_eval,Jk_2_0_eval,Jk_1_8_eval,Jk_1_7_eval,Jk_1_6_eval,Jk_1_5_eval,Jk_1_4_eval,Jk_1_3_eval,Jk_1_2_eval,Jk_1_1_eval,Jk_1_0_eval,Jk_0_9_eval,Jk_0_8_eval,Jk_0_7_eval,Jk_0_6_eval,Jk_0_5_eval,Jk_0_4_eval,Jk_0_3_eval,Jk_0_2_eval,Jk_0_1_eval,Jk_0_0_eval,one_pow,mul_one]
  ring
def U_3_0 : Expr := (.var 0)
def U_2_1 : Expr := (.var 3)
def U_1_2 : Expr := (.var 5)
def U_0_3 : Expr := (.var 1)
def U_0_2 : Expr := (.var 4)
def U_0_0 : Expr := (.var 2)
def UData : Biv := (.cons U_3_0 3 0 (.cons U_2_1 2 1 (.cons U_1_2 1 2 (.cons U_0_3 0 3 (.cons U_0_2 0 2 (.cons U_0_0 0 0 .nil))))))
def Uk_1_1 : Expr := (.num 2)
def UkData : Biv := (.cons Uk_1_1 1 1 .nil)
lemma U_evaluation (v : ℕ → K) (x y : K) :
    denote v x y UData=PolarCubic.cubic (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) x y 1 := by
  simp only [UData,denote,U_3_0,U_2_1,U_1_2,U_0_3,U_0_2,U_0_0,ringEval,PolarCubic.cubic]
  simp only [pow_zero,pow_one,mul_one,one_mul,add_zero,add_assoc,mul_assoc]
  ring
lemma Uk_evaluation (v : ℕ → K) (x y : K) :
    denote v x y UkData=2*x*y := by simp [UkData,Uk_1_1,denote,ringEval]
def SExpr : Expr := (.add (.mul (.mul (.num (-9)) (.var 0)) (.mul (.var 2) (.mul (.var 4) (.var 5)))) (.mul (.mul (.num 3) (.var 2)) (.mul (.pow (.var 3) 2) (.var 4))))
lemma S_evaluation (v : ℕ → K) :
    ringEval v SExpr=PolarCubic.s4Numerator (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by
  simp [SExpr,ringEval,PolarCubic.s4Numerator]
def TExpr : Expr := (.add (.add (.mul (.mul (.num 729) (.pow (.var 0) 2)) (.mul (.pow (.var 1) 2) (.pow (.var 2) 2))) (.add (.mul (.mul (.num 108) (.pow (.var 0) 2)) (.mul (.var 2) (.pow (.var 4) 3))) (.mul (.mul (.num (-486)) (.mul (.var 0) (.var 1))) (.mul (.pow (.var 2) 2) (.mul (.var 3) (.var 5)))))) (.add (.mul (.mul (.num 108) (.var 0)) (.mul (.pow (.var 2) 2) (.pow (.var 5) 3))) (.add (.mul (.mul (.num 108) (.var 1)) (.mul (.pow (.var 2) 2) (.pow (.var 3) 3))) (.mul (.mul (.num (-27)) (.pow (.var 2) 2)) (.mul (.pow (.var 3) 2) (.pow (.var 5) 2))))))
lemma T_evaluation (v : ℕ → K) :
    ringEval v TExpr=PolarCubic.s6Numerator (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by
  simp [TExpr,ringEval,PolarCubic.s6Numerator]
def SkExpr : Expr := (.add (.mul (.mul (.num 27) (.var 0)) (.mul (.var 1) (.var 2))) (.mul (.mul (.num (-3)) (.var 2)) (.mul (.var 3) (.var 5))))
lemma Sk_evaluation (v : ℕ → K) :
    ringEval v SkExpr=PolarCubic.s4NumeratorK (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by
  simp [SkExpr,ringEval,PolarCubic.s4NumeratorK]
def TkExpr : Expr := (.mul (.mul (.num (-216)) (.var 0)) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2))))
lemma Tk_evaluation (v : ℕ → K) :
    ringEval v TkExpr=PolarCubic.s6NumeratorK (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by
  simp [TkExpr,ringEval,PolarCubic.s6NumeratorK]
end PolarCovariants.IdentityData
