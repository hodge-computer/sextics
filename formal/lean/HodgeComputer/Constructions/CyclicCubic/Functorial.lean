import HodgeComputer.Constructions.CyclicCubic.Covariants

/-! Naturality of the explicit classical covariants under ring homomorphisms.
Prepared with OpenAI Codex assistance for hodgepodgeconjecture; see
CubicCovariants for mathematical attribution. -/
namespace CycleCovariants
variable {K L : Type*} [CommRing K] [CommRing L]
lemma map_H (φ : K →+* L) (a b c d e f x y z : K) :
    φ (H a b c d e f x y z)=H (φ a) (φ b) (φ c) (φ d) (φ e) (φ f) (φ x) (φ y) (φ z) := by
  simp only [H,HCoeff300,HCoeff210,HCoeff201,HCoeff120,HCoeff111,HCoeff102,HCoeff030,HCoeff021,HCoeff012,HCoeff003,map_add,map_mul,map_pow,map_neg,map_ofNat]
lemma map_Theta (φ : K →+* L) (a b c d e f x y z : K) :
    φ (Theta a b c d e f x y z)=Theta (φ a) (φ b) (φ c) (φ d) (φ e) (φ f) (φ x) (φ y) (φ z) := by
  simp only [Theta,ThetaCoeff600,ThetaCoeff510,ThetaCoeff501,ThetaCoeff420,ThetaCoeff411,ThetaCoeff402,ThetaCoeff330,ThetaCoeff321,ThetaCoeff312,ThetaCoeff303,ThetaCoeff240,ThetaCoeff231,ThetaCoeff222,ThetaCoeff213,ThetaCoeff204,ThetaCoeff150,ThetaCoeff141,ThetaCoeff132,ThetaCoeff123,ThetaCoeff114,ThetaCoeff105,ThetaCoeff060,ThetaCoeff051,ThetaCoeff042,ThetaCoeff033,ThetaCoeff024,ThetaCoeff015,ThetaCoeff006,map_add,map_mul,map_pow,map_neg,map_ofNat]
lemma map_J (φ : K →+* L) (a b c d e f x y z : K) :
    φ (J a b c d e f x y z)=J (φ a) (φ b) (φ c) (φ d) (φ e) (φ f) (φ x) (φ y) (φ z) := by
  simp only [J,JCoeff900,JCoeff810,JCoeff801,JCoeff720,JCoeff711,JCoeff702,JCoeff630,JCoeff621,JCoeff612,JCoeff603,JCoeff540,JCoeff531,JCoeff522,JCoeff513,JCoeff504,JCoeff450,JCoeff441,JCoeff432,JCoeff423,JCoeff414,JCoeff405,JCoeff360,JCoeff351,JCoeff342,JCoeff333,JCoeff324,JCoeff315,JCoeff306,JCoeff270,JCoeff261,JCoeff252,JCoeff243,JCoeff234,JCoeff225,JCoeff216,JCoeff207,JCoeff180,JCoeff171,JCoeff162,JCoeff153,JCoeff144,JCoeff135,JCoeff126,JCoeff117,JCoeff108,JCoeff090,JCoeff081,JCoeff072,JCoeff063,JCoeff054,JCoeff045,JCoeff036,JCoeff027,JCoeff018,JCoeff009,map_add,map_mul,map_pow,map_neg,map_ofNat]
end CycleCovariants
