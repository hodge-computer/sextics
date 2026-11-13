import HodgeComputer.Constructions.PolarCubic.Covariants
namespace PolarCovariants
open PolynomialEncoding.SignedExpressions ExpressionData Lean.Grind.CommRing
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
variable {K L : Type*} [CommRing K] [CommRing L]
lemma map_ringEval (φ : K →+* L) (v : ℕ → K) (e : Expr) :
    φ (ringEval v e)=ringEval (fun i => φ (v i)) e := by
  induction e <;> simp_all [ringEval]
lemma map_coefficientContext (φ : K →+* L) (a b c d e f : K) :
    (fun i => φ (coefficientContext a b c d e f i))=
      coefficientContext (φ a) (φ b) (φ c) (φ d) (φ e) (φ f) := by
  funext i
  simp only [coefficientContext]
  split_ifs <;> simp only [map_zero]

theorem map_H (φ : K →+* L) (a b c d e f x y z : K) :
    φ (H a b c d e f x y z)=
      H (φ a) (φ b) (φ c) (φ d) (φ e) (φ f) (φ x) (φ y) (φ z) := by
  simp only [H,HCoeff201,HCoeff120,HCoeff111,HCoeff102,HCoeff030,HCoeff021,HCoeff012,map_add,map_mul,map_pow,map_neg,map_ofNat,map_ringEval,map_coefficientContext]
theorem map_Theta (φ : K →+* L) (a b c d e f x y z : K) :
    φ (Theta a b c d e f x y z)=
      Theta (φ a) (φ b) (φ c) (φ d) (φ e) (φ f) (φ x) (φ y) (φ z) := by
  simp only [Theta,ThetaCoeff600,ThetaCoeff510,ThetaCoeff501,ThetaCoeff420,ThetaCoeff411,ThetaCoeff402,ThetaCoeff330,ThetaCoeff321,ThetaCoeff312,ThetaCoeff303,ThetaCoeff240,ThetaCoeff231,ThetaCoeff222,ThetaCoeff213,ThetaCoeff204,ThetaCoeff150,ThetaCoeff141,ThetaCoeff132,ThetaCoeff123,ThetaCoeff114,ThetaCoeff105,ThetaCoeff060,ThetaCoeff051,ThetaCoeff042,ThetaCoeff033,ThetaCoeff024,ThetaCoeff015,ThetaCoeff006,map_add,map_mul,map_pow,map_neg,map_ofNat,map_ringEval,map_coefficientContext]
theorem map_J (φ : K →+* L) (a b c d e f x y z : K) :
    φ (J a b c d e f x y z)=
      J (φ a) (φ b) (φ c) (φ d) (φ e) (φ f) (φ x) (φ y) (φ z) := by
  simp only [J,JCoeff900,JCoeff810,JCoeff801,JCoeff720,JCoeff711,JCoeff630,JCoeff621,JCoeff612,JCoeff603,JCoeff540,JCoeff531,JCoeff522,JCoeff513,JCoeff504,JCoeff450,JCoeff441,JCoeff432,JCoeff423,JCoeff414,JCoeff405,JCoeff360,JCoeff351,JCoeff342,JCoeff333,JCoeff324,JCoeff315,JCoeff306,JCoeff270,JCoeff261,JCoeff252,JCoeff243,JCoeff234,JCoeff225,JCoeff216,JCoeff180,JCoeff171,JCoeff162,JCoeff153,JCoeff144,JCoeff135,JCoeff126,JCoeff117,JCoeff108,JCoeff090,JCoeff081,JCoeff072,JCoeff063,JCoeff054,JCoeff045,JCoeff036,JCoeff027,JCoeff018,JCoeff009,map_add,map_mul,map_pow,map_neg,map_ofNat,map_ringEval,map_coefficientContext]
theorem map_Hk (φ : K →+* L) (a b c d e f x y z : K) :
    φ (Hk a b c d e f x y z)=
      Hk (φ a) (φ b) (φ c) (φ d) (φ e) (φ f) (φ x) (φ y) (φ z) := by
  simp only [Hk,HkCoeff210,HkCoeff102,HkCoeff030,HkCoeff012,map_add,map_mul,map_pow,map_neg,map_ofNat,map_ringEval,map_coefficientContext]
theorem map_Thetak (φ : K →+* L) (a b c d e f x y z : K) :
    φ (Thetak a b c d e f x y z)=
      Thetak (φ a) (φ b) (φ c) (φ d) (φ e) (φ f) (φ x) (φ y) (φ z) := by
  simp only [Thetak,ThetakCoeff510,ThetakCoeff501,ThetakCoeff420,ThetakCoeff411,ThetakCoeff402,ThetakCoeff330,ThetakCoeff321,ThetakCoeff312,ThetakCoeff303,ThetakCoeff240,ThetakCoeff231,ThetakCoeff222,ThetakCoeff213,ThetakCoeff204,ThetakCoeff150,ThetakCoeff141,ThetakCoeff132,ThetakCoeff123,ThetakCoeff114,ThetakCoeff105,ThetakCoeff060,ThetakCoeff051,ThetakCoeff042,ThetakCoeff033,ThetakCoeff024,ThetakCoeff015,ThetakCoeff006,map_add,map_mul,map_pow,map_neg,map_ofNat,map_ringEval,map_coefficientContext]
theorem map_Jk (φ : K →+* L) (a b c d e f x y z : K) :
    φ (Jk a b c d e f x y z)=
      Jk (φ a) (φ b) (φ c) (φ d) (φ e) (φ f) (φ x) (φ y) (φ z) := by
  simp only [Jk,JkCoeff900,JkCoeff810,JkCoeff801,JkCoeff720,JkCoeff711,JkCoeff702,JkCoeff630,JkCoeff621,JkCoeff612,JkCoeff603,JkCoeff540,JkCoeff531,JkCoeff522,JkCoeff513,JkCoeff504,JkCoeff450,JkCoeff441,JkCoeff432,JkCoeff423,JkCoeff414,JkCoeff405,JkCoeff360,JkCoeff351,JkCoeff342,JkCoeff333,JkCoeff324,JkCoeff315,JkCoeff306,JkCoeff270,JkCoeff261,JkCoeff252,JkCoeff243,JkCoeff234,JkCoeff225,JkCoeff216,JkCoeff207,JkCoeff180,JkCoeff171,JkCoeff162,JkCoeff153,JkCoeff144,JkCoeff135,JkCoeff126,JkCoeff117,JkCoeff108,JkCoeff090,JkCoeff081,JkCoeff072,JkCoeff063,JkCoeff054,JkCoeff045,JkCoeff036,JkCoeff027,JkCoeff018,JkCoeff009,map_add,map_mul,map_pow,map_neg,map_ofNat,map_ringEval,map_coefficientContext]
theorem map_HJet (φ : K →+* L) (a b c d e f k x y z : K) :
    φ (HJet a b c d e f k x y z)=
      HJet (φ a) (φ b) (φ c) (φ d) (φ e) (φ f) (φ k) (φ x) (φ y) (φ z) := by
  simp only [HJet,map_add,map_mul,map_H,map_Hk]
theorem map_ThetaJet (φ : K →+* L) (a b c d e f k x y z : K) :
    φ (ThetaJet a b c d e f k x y z)=
      ThetaJet (φ a) (φ b) (φ c) (φ d) (φ e) (φ f) (φ k) (φ x) (φ y) (φ z) := by
  simp only [ThetaJet,map_add,map_mul,map_Theta,map_Thetak]
theorem map_JJet (φ : K →+* L) (a b c d e f k x y z : K) :
    φ (JJet a b c d e f k x y z)=
      JJet (φ a) (φ b) (φ c) (φ d) (φ e) (φ f) (φ k) (φ x) (φ y) (φ z) := by
  simp only [JJet,map_add,map_mul,map_J,map_Jk]
theorem H_diagonal (a b c x y z : K) :
    H a b c 0 0 0 x y z=81*a*b*c*x*y*z := by
  simp [H,HCoeff201,HCoeff120,HCoeff111,HCoeff102,HCoeff030,HCoeff021,HCoeff012,HCoeff201Expr,HCoeff120Expr,HCoeff111Expr,HCoeff102Expr,HCoeff030Expr,HCoeff021Expr,HCoeff012Expr,coefficientContext,ringEval]
  ring
theorem Theta_diagonal (a b c x y z : K) :
    Theta a b c 0 0 0 x y z=-6561*a^2*b^2*c^2*(a*b*x^3*y^3+a*c*x^3*z^3+b*c*y^3*z^3) := by
  simp [Theta,ThetaCoeff600,ThetaCoeff510,ThetaCoeff501,ThetaCoeff420,ThetaCoeff411,ThetaCoeff402,ThetaCoeff330,ThetaCoeff321,ThetaCoeff312,ThetaCoeff303,ThetaCoeff240,ThetaCoeff231,ThetaCoeff222,ThetaCoeff213,ThetaCoeff204,ThetaCoeff150,ThetaCoeff141,ThetaCoeff132,ThetaCoeff123,ThetaCoeff114,ThetaCoeff105,ThetaCoeff060,ThetaCoeff051,ThetaCoeff042,ThetaCoeff033,ThetaCoeff024,ThetaCoeff015,ThetaCoeff006,ThetaCoeff600Expr,ThetaCoeff510Expr,ThetaCoeff501Expr,ThetaCoeff420Expr,ThetaCoeff411Expr,ThetaCoeff402Expr,ThetaCoeff330Expr,ThetaCoeff321Expr,ThetaCoeff312Expr,ThetaCoeff303Expr,ThetaCoeff240Expr,ThetaCoeff231Expr,ThetaCoeff222Expr,ThetaCoeff213Expr,ThetaCoeff204Expr,ThetaCoeff150Expr,ThetaCoeff141Expr,ThetaCoeff132Expr,ThetaCoeff123Expr,ThetaCoeff114Expr,ThetaCoeff105Expr,ThetaCoeff060Expr,ThetaCoeff051Expr,ThetaCoeff042Expr,ThetaCoeff033Expr,ThetaCoeff024Expr,ThetaCoeff015Expr,ThetaCoeff006Expr,coefficientContext,ringEval]
  ring
theorem J_diagonal (a b c x y z : K) :
    J a b c 0 0 0 x y z=531441*a^3*b^3*c^3*(a*x^3-b*y^3)*(a*x^3-c*z^3)*(b*y^3-c*z^3) := by
  simp [J,JCoeff900,JCoeff810,JCoeff801,JCoeff720,JCoeff711,JCoeff630,JCoeff621,JCoeff612,JCoeff603,JCoeff540,JCoeff531,JCoeff522,JCoeff513,JCoeff504,JCoeff450,JCoeff441,JCoeff432,JCoeff423,JCoeff414,JCoeff405,JCoeff360,JCoeff351,JCoeff342,JCoeff333,JCoeff324,JCoeff315,JCoeff306,JCoeff270,JCoeff261,JCoeff252,JCoeff243,JCoeff234,JCoeff225,JCoeff216,JCoeff180,JCoeff171,JCoeff162,JCoeff153,JCoeff144,JCoeff135,JCoeff126,JCoeff117,JCoeff108,JCoeff090,JCoeff081,JCoeff072,JCoeff063,JCoeff054,JCoeff045,JCoeff036,JCoeff027,JCoeff018,JCoeff009,JCoeff900Expr,JCoeff810Expr,JCoeff801Expr,JCoeff720Expr,JCoeff711Expr,JCoeff630Expr,JCoeff621Expr,JCoeff612Expr,JCoeff603Expr,JCoeff540Expr,JCoeff531Expr,JCoeff522Expr,JCoeff513Expr,JCoeff504Expr,JCoeff450Expr,JCoeff441Expr,JCoeff432Expr,JCoeff423Expr,JCoeff414Expr,JCoeff405Expr,JCoeff360Expr,JCoeff351Expr,JCoeff342Expr,JCoeff333Expr,JCoeff324Expr,JCoeff315Expr,JCoeff306Expr,JCoeff270Expr,JCoeff261Expr,JCoeff252Expr,JCoeff243Expr,JCoeff234Expr,JCoeff225Expr,JCoeff216Expr,JCoeff180Expr,JCoeff171Expr,JCoeff162Expr,JCoeff153Expr,JCoeff144Expr,JCoeff135Expr,JCoeff126Expr,JCoeff117Expr,JCoeff108Expr,JCoeff090Expr,JCoeff081Expr,JCoeff072Expr,JCoeff063Expr,JCoeff054Expr,JCoeff045Expr,JCoeff036Expr,JCoeff027Expr,JCoeff018Expr,JCoeff009Expr,coefficientContext,ringEval]
  ring
end PolarCovariants
