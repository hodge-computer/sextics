import Proposal.PhysicalCubicTangent
import HodgeComputer.Constructions.PolarCubic.Map

/-! The covariant invariant differential on the exact physical field.
The universal polynomial identity is instantiated using the proved physical
tangent derivation and the actual coefficients. All nonvanishing assumptions
are supplied by the physical chart. Prepared with OpenAI Codex assistance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace CycleCubicFieldDifferential
open PolarCovariants MvPolynomial
section Evaluation
variable {R K : Type*} [CommRing R] [CommRing K]
lemma eval_Hpoly (φ : R →+* K) (a b c d e f : R) (x y : K) :
    MvPolynomial.eval₂Hom φ ![x,y] (Hpoly a b c d e f)=
      H (φ a) (φ b) (φ c) (φ d) (φ e) (φ f) x y 1 := by
  unfold Hpoly
  rw [map_H]
  simp only [MvPolynomial.eval₂Hom_C,MvPolynomial.eval₂Hom_X',
    Matrix.cons_val_zero,Matrix.cons_val_one,map_one]
lemma eval_Thetapoly (φ : R →+* K) (a b c d e f : R) (x y : K) :
    MvPolynomial.eval₂Hom φ ![x,y] (Thetapoly a b c d e f)=
      Theta (φ a) (φ b) (φ c) (φ d) (φ e) (φ f) x y 1 := by
  unfold Thetapoly
  rw [map_Theta]
  simp only [MvPolynomial.eval₂Hom_C,MvPolynomial.eval₂Hom_X',
    Matrix.cons_val_zero,Matrix.cons_val_one,map_one]
lemma eval_Jpoly (φ : R →+* K) (a b c d e f : R) (x y : K) :
    MvPolynomial.eval₂Hom φ ![x,y] (Jpoly a b c d e f)=
      J (φ a) (φ b) (φ c) (φ d) (φ e) (φ f) x y 1 := by
  unfold Jpoly
  rw [map_J]
  simp only [MvPolynomial.eval₂Hom_C,MvPolynomial.eval₂Hom_X',
    Matrix.cons_val_zero,Matrix.cons_val_one,map_one]
lemma eval_HJetpoly (φ : R →+* K) (a b c d e f k : R) (x y : K) :
    MvPolynomial.eval₂Hom φ ![x,y] (HJetpoly a b c d e f k)=
      HJet (φ a) (φ b) (φ c) (φ d) (φ e) (φ f) (φ k) x y 1 := by
  unfold HJetpoly
  rw [map_HJet]
  simp only [MvPolynomial.eval₂Hom_C,MvPolynomial.eval₂Hom_X',
    Matrix.cons_val_zero,Matrix.cons_val_one,map_one]
lemma eval_ThetaJetpoly (φ : R →+* K) (a b c d e f k : R) (x y : K) :
    MvPolynomial.eval₂Hom φ ![x,y] (ThetaJetpoly a b c d e f k)=
      ThetaJet (φ a) (φ b) (φ c) (φ d) (φ e) (φ f) (φ k) x y 1 := by
  unfold ThetaJetpoly
  rw [map_ThetaJet]
  simp only [MvPolynomial.eval₂Hom_C,MvPolynomial.eval₂Hom_X',
    Matrix.cons_val_zero,Matrix.cons_val_one,map_one]
lemma eval_JJetpoly (φ : R →+* K) (a b c d e f k : R) (x y : K) :
    MvPolynomial.eval₂Hom φ ![x,y] (JJetpoly a b c d e f k)=
      JJet (φ a) (φ b) (φ c) (φ d) (φ e) (φ f) (φ k) x y 1 := by
  unfold JJetpoly
  rw [map_JJet]
  simp only [MvPolynomial.eval₂Hom_C,MvPolynomial.eval₂Hom_X',
    Matrix.cons_val_zero,Matrix.cons_val_one,map_one]
end Evaluation
section Constants
variable {K : Type*} [CommRing K]
def constants (D : Derivation ℤ K K) : Subring K where
  carrier := {a | D a=0}
  zero_mem' := D.map_zero
  one_mem' := D.map_one_eq_zero
  add_mem' := by intro a b ha hb; change D (a+b)=0; rw [map_add,ha,hb,add_zero]
  neg_mem' := by intro a ha; change D (-a)=0; rw [map_neg,ha,neg_zero]
  mul_mem' := by
    intro a b ha hb
    change D (a*b)=0
    rw [Derivation.leibniz,ha,hb]
    simp

end Constants
section Differential
variable {K : Type*} [Field K] [CharZero K]
theorem differential_of_constants (D : Derivation ℤ K K)
    (a b c d e f x y : K)
    (ha : D a=0) (hb : D b=0) (hc : D c=0)
    (hd : D d=0) (he : D e=0) (hf : D f=0)
    (hu : PolarCubic.cubic a b c d e f x y 1=0)
    (hg : 3*a*x^2+2*d*x*y+f*y^2≠0)
    (hH : H a b c d e f x y 1≠0) (hJ : J a b c d e f x y 1≠0)
    (hx : D x= -(3*b*y^2+d*x^2+2*e*y+2*f*x*y)/(3*a*x^2+2*d*x*y+f*y^2))
    (hy : D y=1) :
    D (Theta a b c d e f x y 1/(H a b c d e f x y 1)^2)/
      (2*(-J a b c d e f x y 1/(2*(H a b c d e f x y 1)^3)))=
        3/(3*a*x^2+2*d*x*y+f*y^2) := by
  let R := constants D
  let a' : R := ⟨a,ha⟩; let b' : R := ⟨b,hb⟩; let c' : R := ⟨c,hc⟩
  let d' : R := ⟨d,hd⟩; let e' : R := ⟨e,he⟩; let f' : R := ⟨f,hf⟩
  let φ : R →+* K := (constants D).subtype
  let ρ : Affine R →+* K := MvPolynomial.eval₂Hom φ ![x,y]
  have hU : ρ (Upoly a' b' c' d' e' f')=0 := by
    simpa [ρ,φ,Upoly,PolarCubic.cubic,a',b',c',d',e',f',Subring.subtype] using hu
  have hPx : ρ (pderiv 0 (Upoly a' b' c' d' e' f'))=3*a*x^2+2*d*x*y+f*y^2 := by
    simp [ρ,φ,Upoly,PolarCubic.cubic,a',b',c',d',e',f',MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,
      Pi.single_apply,Fin.ext_iff,Subring.subtype]
    ring
  have hPy : ρ (pderiv 1 (Upoly a' b' c' d' e' f'))=3*b*y^2+d*x^2+2*e*y+2*f*x*y := by
    simp [ρ,φ,Upoly,PolarCubic.cubic,a',b',c',d',e',f',MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,
      Pi.single_apply,Fin.ext_iff,Subring.subtype]
    ring
  have hHmap : ρ (Hpoly a' b' c' d' e' f')=H a b c d e f x y 1 :=
    eval_Hpoly φ a' b' c' d' e' f' x y
  have hQmap : ρ (Thetapoly a' b' c' d' e' f')=Theta a b c d e f x y 1 :=
    eval_Thetapoly φ a' b' c' d' e' f' x y
  have hJmap : ρ (Jpoly a' b' c' d' e' f')=J a b c d e f x y 1 :=
    eval_Jpoly φ a' b' c' d' e' f' x y
  have hcompat (p : Affine R) : D (ρ p)=ρ (pderiv 1 p)-
      ρ (pderiv 1 (Upoly a' b' c' d' e' f'))/
        ρ (pderiv 0 (Upoly a' b' c' d' e' f'))*ρ (pderiv 0 p) := by
    rw [hPx,hPy]
    change D (MvPolynomial.eval₂Hom φ ![x,y] p)=_
    rw [HoldoutConstruction.derivation_eval₂_chain D φ ![x,y] (fun r=>r.property) p]
    simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.reduceSucc,Matrix.cons_val_one,
      Finset.univ_eq_empty,Finset.sum_empty,hx,hy,mul_one,add_zero]
    change ρ (pderiv 0 p)*(-(3*b*y^2+d*x^2+2*e*y+2*f*x*y)/(3*a*x^2+2*d*x*y+f*y^2))+
      ρ (pderiv 1 p)=_
    ring
  have result := PolarCubicMap.differential a' b' c' d' e' f' ρ D hU
    (hPx ▸ hg) (hHmap ▸ hH) (hJmap ▸ hJ) hcompat
  simpa only [hHmap,hQmap,hJmap,hPx] using result
end Differential

namespace Physical
open CyclePhysical CyclePhysicalCoordinates CyclePhysicalCubicTangent CyclePhysicalNormalTransport
local instance : Algebra ℤ FunctionField := Ring.toIntAlgebra _
def xi : FunctionField := Theta coeffA coeffB coeffC coeffD coeffE coeffF x y 1/
  (H coeffA coeffB coeffC coeffD coeffE coeffF x y 1)^2
def eta : FunctionField := -J coeffA coeffB coeffC coeffD coeffE coeffF x y 1/
  (2*(H coeffA coeffB coeffC coeffD coeffE coeffF x y 1)^3)
theorem invariant_differential : derivative xi/(2*eta)=3/cubicNormal := by
  obtain ⟨ha,hb,hc,hd,he,hf⟩ := coefficient_constants
  exact differential_of_constants derivative coeffA coeffB coeffC coeffD coeffE coeffF x y
    ha hb hc hd he hf cubic_equation cubic_normal_ne_zero
    CyclePhysicalChart.physical_hessian_ne_zero CyclePhysicalChart.physical_jacobian_ne_zero
    derivative_x passive_parameters.2.2.2.2.1
theorem xi_derivative_ne_zero : derivative xi≠0 := by
  intro hz
  have h := invariant_differential
  rw [hz,zero_div] at h
  exact (div_ne_zero (by norm_num : (3:FunctionField)≠0) cubic_normal_ne_zero) h.symm
end Physical
end CycleCubicFieldDifferential
#print axioms CycleCubicFieldDifferential.Physical.invariant_differential
#print axioms CycleCubicFieldDifferential.Physical.xi_derivative_ne_zero
