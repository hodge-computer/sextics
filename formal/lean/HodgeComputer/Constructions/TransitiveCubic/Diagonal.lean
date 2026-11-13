import HodgeComputer.Constructions.TransitiveCubic.Covariants

/-! Diagonal specializations of the classical cubic covariants. These small
formulas supply exact nonvanishing checks, with no numerical approximation.
See CubicCovariants for Fisher/SageMath normalization and attribution.
Original cyclic construction by hodgepodgeconjecture; transitive adaptation for fqlx with OpenAI Codex assistance. -/
namespace TransitiveCovariants
variable {K : Type*} [CommRing K]
lemma H_diagonal (a b c x y z : K) :
    H a b c 0 0 0 x y z=81*a*b*c*x*y*z := by
  simp only [H,HCoeff300,HCoeff210,HCoeff201,HCoeff120,HCoeff111,HCoeff102,HCoeff030,HCoeff021,HCoeff012,HCoeff003,zero_pow (by decide : (2:ℕ)≠0),mul_zero,zero_mul,zero_add,add_zero]
  ring
lemma Theta_diagonal (a b c x y z : K) :
    Theta a b c 0 0 0 x y z=-6561*a^2*b^2*c^2*(a*b*x^3*y^3+a*c*x^3*z^3+b*c*y^3*z^3) := by
  simp only [Theta,ThetaCoeff600,ThetaCoeff510,ThetaCoeff501,ThetaCoeff420,ThetaCoeff411,ThetaCoeff402,ThetaCoeff330,ThetaCoeff321,ThetaCoeff312,ThetaCoeff303,ThetaCoeff240,ThetaCoeff231,ThetaCoeff222,ThetaCoeff213,ThetaCoeff204,ThetaCoeff150,ThetaCoeff141,ThetaCoeff132,ThetaCoeff123,ThetaCoeff114,ThetaCoeff105,ThetaCoeff060,ThetaCoeff051,ThetaCoeff042,ThetaCoeff033,ThetaCoeff024,ThetaCoeff015,ThetaCoeff006,zero_pow (by decide : (2:ℕ)≠0),zero_pow (by decide : (3:ℕ)≠0),zero_pow (by decide : (4:ℕ)≠0),zero_pow (by decide : (5:ℕ)≠0),zero_pow (by decide : (6:ℕ)≠0),mul_zero,zero_mul,zero_add,add_zero]
  ring
lemma J_diagonal (a b c x y z : K) :
    J a b c 0 0 0 x y z=531441*a^3*b^3*c^3*(a*x^3-b*y^3)*(a*x^3-c*z^3)*(b*y^3-c*z^3) := by
  simp only [J,JCoeff900,JCoeff810,JCoeff801,JCoeff720,JCoeff711,JCoeff702,JCoeff630,JCoeff621,JCoeff612,JCoeff603,JCoeff540,JCoeff531,JCoeff522,JCoeff513,JCoeff504,JCoeff450,JCoeff441,JCoeff432,JCoeff423,JCoeff414,JCoeff405,JCoeff360,JCoeff351,JCoeff342,JCoeff333,JCoeff324,JCoeff315,JCoeff306,JCoeff270,JCoeff261,JCoeff252,JCoeff243,JCoeff234,JCoeff225,JCoeff216,JCoeff207,JCoeff180,JCoeff171,JCoeff162,JCoeff153,JCoeff144,JCoeff135,JCoeff126,JCoeff117,JCoeff108,JCoeff090,JCoeff081,JCoeff072,JCoeff063,JCoeff054,JCoeff045,JCoeff036,JCoeff027,JCoeff018,JCoeff009,zero_pow (by decide : (2:ℕ)≠0),zero_pow (by decide : (3:ℕ)≠0),zero_pow (by decide : (4:ℕ)≠0),zero_pow (by decide : (5:ℕ)≠0),zero_pow (by decide : (6:ℕ)≠0),zero_pow (by decide : (7:ℕ)≠0),mul_zero,zero_mul,zero_add,add_zero]
  ring
end TransitiveCovariants
#print axioms TransitiveCovariants.J_diagonal
