import HodgeComputer.Constructions.PolarCubic.DifferentialJets
import HodgeComputer.Constructions.PolarCubic.Functorial
import HodgeComputer.Constructions.HoldoutCover.PolynomialCalculus
noncomputable section
namespace PolarCovariants
open MvPolynomial
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000
variable {K : Type*} [CommRing K]
abbrev Affine (K : Type*) [CommRing K] := MvPolynomial (Fin 2) K
local notation "x" => (X (R := K) (0:Fin 2))
local notation "y" => (X (R := K) (1:Fin 2))
def Upoly (a b c d e f : K) : Affine K :=
  PolarCubic.cubic (C a) (C b) (C c) (C d) (C e) (C f) x y 1
def Hpoly (a b c d e f : K) : Affine K :=
  H (C a) (C b) (C c) (C d) (C e) (C f) x y 1
def Thetapoly (a b c d e f : K) : Affine K :=
  Theta (C a) (C b) (C c) (C d) (C e) (C f) x y 1
def Jpoly (a b c d e f : K) : Affine K :=
  J (C a) (C b) (C c) (C d) (C e) (C f) x y 1
def Hkpoly (a b c d e f : K) : Affine K :=
  Hk (C a) (C b) (C c) (C d) (C e) (C f) x y 1
def Thetakpoly (a b c d e f : K) : Affine K :=
  Thetak (C a) (C b) (C c) (C d) (C e) (C f) x y 1
def Jkpoly (a b c d e f : K) : Affine K :=
  Jk (C a) (C b) (C c) (C d) (C e) (C f) x y 1
def Ukpoly : Affine K := 2*x*y
def UJetpoly (a b c d e f k : K) : Affine K :=
  PolarCubic.cubicJet (C a) (C b) (C c) (C d) (C e) (C f) (C k) x y 1
def HJetpoly (a b c d e f k : K) : Affine K :=
  HJet (C a) (C b) (C c) (C d) (C e) (C f) (C k) x y 1
def ThetaJetpoly (a b c d e f k : K) : Affine K :=
  ThetaJet (C a) (C b) (C c) (C d) (C e) (C f) (C k) x y 1
def JJetpoly (a b c d e f k : K) : Affine K :=
  JJet (C a) (C b) (C c) (C d) (C e) (C f) (C k) x y 1
namespace DifferentialData
open TransitiveSignedExpressions TransitiveBivariateExpressions IdentityData
def baseCoefficients (a b c d e f : K) : ℕ → K :=
  fun i => match i with | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | 5 => f | _ => 0
lemma U_binding (a b c d e f : K) :
    denote (fun i => C (baseCoefficients a b c d e f i)) x y UData=
      Upoly a b c d e f := by
  simpa only [baseCoefficients,Upoly] using
    U_evaluation (fun i => C (baseCoefficients a b c d e f i)) x y
lemma H_binding (a b c d e f : K) :
    denote (fun i => C (baseCoefficients a b c d e f i)) x y HData=
      Hpoly a b c d e f := by
  simpa only [baseCoefficients,Hpoly] using
    H_evaluation (fun i => C (baseCoefficients a b c d e f i)) x y
lemma Theta_binding (a b c d e f : K) :
    denote (fun i => C (baseCoefficients a b c d e f i)) x y ThetaData=
      Thetapoly a b c d e f := by
  simpa only [baseCoefficients,Thetapoly] using
    Theta_evaluation (fun i => C (baseCoefficients a b c d e f i)) x y
lemma J_binding (a b c d e f : K) :
    denote (fun i => C (baseCoefficients a b c d e f i)) x y JData=
      Jpoly a b c d e f := by
  simpa only [baseCoefficients,Jpoly] using
    J_evaluation (fun i => C (baseCoefficients a b c d e f i)) x y
lemma Hk_binding (a b c d e f : K) :
    denote (fun i => C (baseCoefficients a b c d e f i)) x y HkData=
      Hkpoly a b c d e f := by
  simpa only [baseCoefficients,Hkpoly] using
    Hk_evaluation (fun i => C (baseCoefficients a b c d e f i)) x y
lemma Thetak_binding (a b c d e f : K) :
    denote (fun i => C (baseCoefficients a b c d e f i)) x y ThetakData=
      Thetakpoly a b c d e f := by
  simpa only [baseCoefficients,Thetakpoly] using
    Thetak_evaluation (fun i => C (baseCoefficients a b c d e f i)) x y
lemma Jk_binding (a b c d e f : K) :
    denote (fun i => C (baseCoefficients a b c d e f i)) x y JkData=
      Jkpoly a b c d e f := by
  simpa only [baseCoefficients,Jkpoly] using
    Jk_evaluation (fun i => C (baseCoefficients a b c d e f i)) x y
lemma Uk_binding (a b c d e f : K) :
    denote (fun i => C (baseCoefficients a b c d e f i)) x y UkData=Ukpoly (K:=K) :=
  Uk_evaluation _ x y
lemma Ux_binding (a b c d e f : K) :
    denote (fun i => C (baseCoefficients a b c d e f i)) x y UxData=
      pderiv 0 (Upoly a b c d e f) := by
  rw [← Ux_generated,← pderiv_denote_dx,U_binding]
lemma Uy_binding (a b c d e f : K) :
    denote (fun i => C (baseCoefficients a b c d e f i)) x y UyData=
      pderiv 1 (Upoly a b c d e f) := by
  rw [← Uy_generated,← pderiv_denote_dy,U_binding]
lemma Hx_binding (a b c d e f : K) :
    denote (fun i => C (baseCoefficients a b c d e f i)) x y HxData=
      pderiv 0 (Hpoly a b c d e f) := by
  rw [← Hx_generated,← pderiv_denote_dx,H_binding]
lemma Hy_binding (a b c d e f : K) :
    denote (fun i => C (baseCoefficients a b c d e f i)) x y HyData=
      pderiv 1 (Hpoly a b c d e f) := by
  rw [← Hy_generated,← pderiv_denote_dy,H_binding]
lemma Thetax_binding (a b c d e f : K) :
    denote (fun i => C (baseCoefficients a b c d e f i)) x y ThetaxData=
      pderiv 0 (Thetapoly a b c d e f) := by
  rw [← Thetax_generated,← pderiv_denote_dx,Theta_binding]
lemma Thetay_binding (a b c d e f : K) :
    denote (fun i => C (baseCoefficients a b c d e f i)) x y ThetayData=
      pderiv 1 (Thetapoly a b c d e f) := by
  rw [← Thetay_generated,← pderiv_denote_dy,Theta_binding]
lemma Ukx_binding (a b c d e f : K) :
    denote (fun i => C (baseCoefficients a b c d e f i)) x y UkxData=
      pderiv 0 (Ukpoly (K:=K)) := by
  rw [← Ukx_generated,← pderiv_denote_dx,Uk_binding]
lemma Uky_binding (a b c d e f : K) :
    denote (fun i => C (baseCoefficients a b c d e f i)) x y UkyData=
      pderiv 1 (Ukpoly (K:=K)) := by
  rw [← Uky_generated,← pderiv_denote_dy,Uk_binding]
lemma Hkx_binding (a b c d e f : K) :
    denote (fun i => C (baseCoefficients a b c d e f i)) x y HkxData=
      pderiv 0 (Hkpoly a b c d e f) := by
  rw [← Hkx_generated,← pderiv_denote_dx,Hk_binding]
lemma Hky_binding (a b c d e f : K) :
    denote (fun i => C (baseCoefficients a b c d e f i)) x y HkyData=
      pderiv 1 (Hkpoly a b c d e f) := by
  rw [← Hky_generated,← pderiv_denote_dy,Hk_binding]
lemma Thetakx_binding (a b c d e f : K) :
    denote (fun i => C (baseCoefficients a b c d e f i)) x y ThetakxData=
      pderiv 0 (Thetakpoly a b c d e f) := by
  rw [← Thetakx_generated,← pderiv_denote_dx,Thetak_binding]
lemma Thetaky_binding (a b c d e f : K) :
    denote (fun i => C (baseCoefficients a b c d e f i)) x y ThetakyData=
      pderiv 1 (Thetakpoly a b c d e f) := by
  rw [← Thetaky_generated,← pderiv_denote_dy,Thetak_binding]
end DifferentialData
lemma relative_identity (a b c d e f : K) :
    let u := Upoly a b c d e f
    let h := Hpoly a b c d e f
    let q := Thetapoly a b c d e f
    let j := Jpoly a b c d e f
    h*(pderiv 0 u*pderiv 1 q-pderiv 1 u*pderiv 0 q)-
      2*q*(pderiv 0 u*pderiv 1 h-pderiv 1 u*pderiv 0 h)+3*j=
      u*(pderiv 0 h*pderiv 1 q-pderiv 1 h*pderiv 0 q) := by
  dsimp only
  let v := DifferentialData.baseCoefficients a b c d e f
  have hh := DifferentialData.semantic_identity0 (fun i => C (v i)) x y
  dsimp only at hh
  simp only [v,DifferentialData.U_binding,DifferentialData.Ux_binding,DifferentialData.Uy_binding,DifferentialData.H_binding,DifferentialData.Hx_binding,DifferentialData.Hy_binding,DifferentialData.Theta_binding,DifferentialData.Thetax_binding,DifferentialData.Thetay_binding,DifferentialData.J_binding] at hh
  linear_combination hh
lemma relative_identityJet (a b c d e f k : K) (hkSquare : k^2=0) :
    let u := UJetpoly a b c d e f k
    let h := HJetpoly a b c d e f k
    let q := ThetaJetpoly a b c d e f k
    let j := JJetpoly a b c d e f k
    h*(pderiv 0 u*pderiv 1 q-pderiv 1 u*pderiv 0 q)-
      2*q*(pderiv 0 u*pderiv 1 h-pderiv 1 u*pderiv 0 h)+3*j=
      u*(pderiv 0 h*pderiv 1 q-pderiv 1 h*pderiv 0 q) := by
  dsimp only
  let v := DifferentialData.baseCoefficients a b c d e f
  have hks : (C k : Affine K)^2=0 := by rw [← map_pow,hkSquare,map_zero]
  have hh := DifferentialData.semantic_identityJet (fun i => C (v i)) x y (C k) hks
  dsimp only at hh
  simp only [v,DifferentialData.U_binding,DifferentialData.Ux_binding,DifferentialData.Uy_binding,DifferentialData.H_binding,DifferentialData.Hx_binding,DifferentialData.Hy_binding,DifferentialData.Theta_binding,DifferentialData.Thetax_binding,DifferentialData.Thetay_binding,DifferentialData.J_binding,DifferentialData.Uk_binding,DifferentialData.Ukx_binding,DifferentialData.Uky_binding,DifferentialData.Hk_binding,DifferentialData.Hkx_binding,DifferentialData.Hky_binding,DifferentialData.Thetak_binding,DifferentialData.Thetakx_binding,DifferentialData.Thetaky_binding,DifferentialData.Jk_binding] at hh
  have hU : UJetpoly a b c d e f k=Upoly a b c d e f+C k*Ukpoly := by
    simp only [UJetpoly,Upoly,PolarCubic.cubicJet,Ukpoly,mul_one]
    ring
  have hH : HJetpoly a b c d e f k=Hpoly a b c d e f+C k*Hkpoly a b c d e f := rfl
  have hQ : ThetaJetpoly a b c d e f k=Thetapoly a b c d e f+C k*Thetakpoly a b c d e f := rfl
  have hJ : JJetpoly a b c d e f k=Jpoly a b c d e f+C k*Jkpoly a b c d e f := rfl
  rw [hU,hH,hQ,hJ]
  simp only [map_add,pderiv_mul,pderiv_C,zero_mul,add_zero]
  linear_combination hh
end PolarCovariants
