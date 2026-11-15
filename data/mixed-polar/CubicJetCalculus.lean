import HodgeComputer.Constructions.TransitiveCubic.Functorial
import HodgeComputer.Constructions.TransitiveCubic.Differential
import HodgeComputer.Constructions.TransitiveCubic.Syzygy
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-! Infinitesimal cubic calculus over dual numbers. Parameter derivatives
are represented by square-zero jets, so no parameter derivation on the
specialized physical function field is assumed.
Prepared with OpenAI Codex assistance. Adapted from the accepted mixed-biweight calculus of fqlx and the Hodge Computer collaborators; maintained TransitiveCubic polynomial identities are imported, not copied. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace MixedPolarCubicJetCalculus
open TransitiveCovariants MvPolynomial

open scoped BigOperators

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


/-- The shared polynomial chain rule, extended from fields to commutative rings.
The proof follows HoldoutConstruction.derivation_eval₂_chain (fqlx/project).
The extension is needed because dual numbers have zero divisors. -/
lemma ring_chain {R L σ : Type*} [CommRing R] [CommRing L] [Fintype σ] [DecidableEq σ]
    (D : Derivation ℤ L L) (φ : R →+* L) (x : σ → L)
    (hC : ∀ r, D (φ r)=0) (p : MvPolynomial σ R) :
    D (MvPolynomial.eval₂Hom φ x p)=
      ∑ i, MvPolynomial.eval₂Hom φ x (MvPolynomial.pderiv i p)*D (x i) := by
  let θ := MvPolynomial.eval₂Hom φ x
  change D (θ p)=∑ i, θ (MvPolynomial.pderiv i p)*D (x i)
  induction p using MvPolynomial.induction_on with
  | C r => simp [θ,hC]
  | add p q hp hq => simp only [map_add,hp,hq,add_mul,Finset.sum_add_distrib]
  | mul_X p j hp =>
    rw [map_mul,Derivation.leibniz]
    simp only [θ,MvPolynomial.eval₂Hom_X',smul_eq_mul] at hp ⊢
    rw [hp]
    simp only [MvPolynomial.pderiv_mul,map_add,map_mul,MvPolynomial.eval₂Hom_X',
      add_mul,Finset.sum_add_distrib]
    have hsum : (∑ i, MvPolynomial.eval₂Hom φ x (MvPolynomial.pderiv i p)*x j*D (x i))=
        x j*(∑ i, MvPolynomial.eval₂Hom φ x (MvPolynomial.pderiv i p)*D (x i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsum]
    have hdelta : (∑ i, MvPolynomial.eval₂Hom φ x p*
        MvPolynomial.eval₂Hom φ x (MvPolynomial.pderiv i (MvPolynomial.X j))*D (x i))=
        MvPolynomial.eval₂Hom φ x p*D (x j) := by
      simp [MvPolynomial.pderiv_X,Pi.single_apply,apply_ite,mul_ite,ite_mul]
    rw [hdelta]
    ring

section ClearedDifferential
variable {K : Type*} [CommRing K]
theorem cleared_differential (D : Derivation ℤ K K) (a b c d e f x y : K)
    (ha : D a=0) (hb : D b=0) (hc : D c=0)
    (hd : D d=0) (he : D e=0) (hf : D f=0)
    (hu : TransitiveCubic.cubic a b c d e f x y 1=0) (hy : D y=1) :
    (3*a*x^2+2*d*x*y+2*f*x)*
      (H a b c d e f x y 1*D (Theta a b c d e f x y 1)-
        2*Theta a b c d e f x y 1*D (H a b c d e f x y 1))+
      3*J a b c d e f x y 1=0 := by
  let R := constants D
  let a' : R := ⟨a,ha⟩; let b' : R := ⟨b,hb⟩; let c' : R := ⟨c,hc⟩
  let d' : R := ⟨d,hd⟩; let e' : R := ⟨e,he⟩; let f' : R := ⟨f,hf⟩
  let φ : R →+* K := R.subtype
  let ρ : Affine R →+* K := eval₂Hom φ ![x,y]
  have hU : ρ (Upoly a' b' c' d' e' f')=0 := by
    simpa [ρ,φ,Upoly,TransitiveCubic.cubic,a',b',c',d',e',f',Subring.subtype] using hu
  have hPx : ρ (pderiv 0 (Upoly a' b' c' d' e' f'))=3*a*x^2+2*d*x*y+2*f*x := by
    simp [ρ,φ,Upoly,a',b',c',d',e',f',MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,
      Pi.single_apply,Fin.ext_iff,Subring.subtype]
    ring
  have hHmap : ρ (Hpoly a' b' c' d' e' f')=H a b c d e f x y 1 :=
    eval_Hpoly φ a' b' c' d' e' f' x y
  have hQmap : ρ (Thetapoly a' b' c' d' e' f')=Theta a b c d e f x y 1 :=
    eval_Thetapoly φ a' b' c' d' e' f' x y
  have hJmap : ρ (Jpoly a' b' c' d' e' f')=J a b c d e f x y 1 :=
    eval_Jpoly φ a' b' c' d' e' f' x y
  have hcompat (p : Affine R) : D (ρ p)=ρ (pderiv 0 p)*D x+ρ (pderiv 1 p) := by
    change D (MvPolynomial.eval₂Hom φ ![x,y] p)=_
    rw [ring_chain D φ ![x,y] (fun r=>r.property) p]
    simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.reduceSucc,
      Finset.univ_eq_empty,Finset.sum_empty,hy,mul_one,add_zero]
    rfl
  have hnormal := hcompat (Upoly a' b' c' d' e' f')
  rw [hU,map_zero] at hnormal
  have hidentity := congrArg ρ (relative_identity a' b' c' d' e' f')
  simp only [map_add,map_sub,map_mul,map_ofNat,hU,zero_mul] at hidentity
  rw [← hHmap,← hQmap,← hJmap,← hPx,hcompat,hcompat]
  linear_combination hidentity-
    (ρ (Hpoly a' b' c' d' e' f')*ρ (pderiv 0 (Thetapoly a' b' c' d' e' f'))-
      2*ρ (Thetapoly a' b' c' d' e' f')*ρ (pderiv 0 (Hpoly a' b' c' d' e' f')))*hnormal
end ClearedDifferential

section InvertibleAlgebra
variable {R : Type*} [CommRing R]
lemma invariant_from_cleared (D : Derivation ℤ R R) (h q j g hi half : R)
    (hinv : hi*h=1) (hhalf : 2*half=1)
    (hc : g*(h*D q-2*q*D h)+3*j=0) :
    g*D (q*hi^2)=6*(-half*j*hi^3) := by
  have hd : D hi= -hi^2*D h := by
    simpa only [smul_eq_mul] using D.leibniz_of_mul_eq_one hinv
  rw [Derivation.leibniz,Derivation.leibniz_pow,hd]
  simp only [smul_eq_mul,nsmul_eq_mul]
  linear_combination hi^3*hc-g*D q*hi^2*hinv+3*j*hi^3*hhalf

lemma curve_from_syzygy (h q j s t hi half : R)
    (hinv : hi*h=1) (hhalf : 2*half=1)
    (hs : j^2=4*q^3+4*s*q*h^4-t*h^6) :
    (-half*j*hi^3)^2=(q*hi^2)^3+s*(q*hi^2)-half^2*t := by
  have h4 : (hi*h)^4=1 := by rw [hinv,one_pow]
  have h6 : (hi*h)^6=1 := by rw [hinv,one_pow]
  have hh : 4*half^2=1 := by
    calc
      _=(2*half)^2 := by ring
      _=1 := by rw [hhalf,one_pow]
  linear_combination half^2*hi^6*hs+q^3*hi^6*hh+
    s*q*hi^2*(hi*h)^4*hh+s*q*hi^2*h4-half^2*t*h6

lemma curve_from_syzygy27 (h q j SN TN hi half third inv27 : R)
    (hinv : hi*h=1) (hhalf : 2*half=1)
    (hthird : 3*third=1) (hinv27 : 27*inv27=1)
    (hs : 27*j^2=108*q^3+36*SN*q*h^4-TN*h^6) :
    (-half*j*hi^3)^2=(q*hi^2)^3+(third*SN)*(q*hi^2)-half^2*(inv27*TN) := by
  have h36 : 36*inv27=4*third := by
    linear_combination 4*third*hinv27-36*inv27*hthird
  have hs' : j^2=4*q^3+4*(third*SN)*q*h^4-(inv27*TN)*h^6 := by
    linear_combination inv27*hs-(j^2-4*q^3)*hinv27+SN*q*h^4*h36
  exact curve_from_syzygy h q j (third*SN) (inv27*TN) hi half hinv hhalf hs'
end InvertibleAlgebra

section Jets
variable {K : Type*} [Field K] [CharZero K]
abbrev Jet := TrivSqZeroExt K K
open TrivSqZeroExt

@[simp] lemma fst_numeral (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : Jet (K:=K)).fst=(ofNat(n) : K) := rfl
@[simp] lemma snd_numeral (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : Jet (K:=K)).snd=0 := rfl

def jetDerivation (D : Derivation ℤ K K) : Derivation ℤ (Jet (K:=K)) (Jet (K:=K)) where
  toFun z := (D z.fst,D z.snd)
  map_add' := by intro a b; ext <;> simp [map_add]
  map_smul' := by intro n a; ext <;> simp [map_smul]
  map_one_eq_zero' := by ext <;> simp
  leibniz' := by
    intro a b
    ext <;> simp [Derivation.leibniz,smul_eq_mul,op_smul_eq_smul] <;> ring

lemma jetDerivation_fst (D : Derivation ℤ K K) (a : Jet (K:=K)) :
    (jetDerivation D a).fst=D a.fst := rfl
lemma jetDerivation_snd (D : Derivation ℤ K K) (a : Jet (K:=K)) :
    (jetDerivation D a).snd=D a.snd := rfl

lemma jetDerivation_inv (D : Derivation ℤ K K) (a : Jet (K:=K)) (ha : a.fst≠0) :
    jetDerivation D a⁻¹= -a⁻¹^2*jetDerivation D a := by
  simpa only [smul_eq_mul] using
    (jetDerivation D).leibniz_of_mul_eq_one (TrivSqZeroExt.inv_mul_cancel ha)

lemma jet_cubic (a b c d e f x y : K)
    (hu : TransitiveCubic.cubic a b c d e f x y 1=0)
    (hg : 3*a*x^2+2*d*x*y+2*f*x≠0) :
    TransitiveCubic.cubic (K:=Jet (K:=K)) (a,1) (b,0) (c,0) (d,0) (e,0) (f,0)
      (x,-x^3/(3*a*x^2+2*d*x*y+2*f*x)) (y,0) (1 : Jet (K:=K))=0 := by
  apply TrivSqZeroExt.ext
  · simpa [TransitiveCubic.cubic] using hu
  · simp [TransitiveCubic.cubic,smul_eq_mul,op_smul_eq_smul]
    have ht : (-x^3/(3*a*x^2+2*d*x*y+2*f*x))*(3*a*x^2+2*d*x*y+2*f*x)= -x^3 :=
      div_mul_cancel₀ _ hg
    linear_combination ht

lemma curve_first_variation (ξ η a b : Jet (K:=K))
    (h : η^2=ξ^3+a*ξ+b) :
    2*η.fst*η.snd=(3*ξ.fst^2+a.fst)*ξ.snd+a.snd*ξ.fst+b.snd := by
  have hs := congrArg TrivSqZeroExt.snd h
  simp only [snd_pow,snd_add,snd_mul,smul_eq_mul,op_smul_eq_smul,nsmul_eq_mul] at hs
  norm_num at hs
  linear_combination hs

lemma differential_first_variation (D : Derivation ℤ K K) (ξ η g : Jet (K:=K))
    (h : g*jetDerivation D ξ=6*η) :
    g.fst*D ξ.snd+g.snd*D ξ.fst=6*η.snd := by
  have hs := congrArg TrivSqZeroExt.snd h
  simpa [jetDerivation,smul_eq_mul,op_smul_eq_smul,add_comm] using hs

lemma differential_jet_from_cleared (g η Dξ ξdotDerivative ηdot gdot : K)
    (hvalue : g*Dξ=6*η)
    (hjet : g*ξdotDerivative+gdot*Dξ=6*ηdot) :
    g^2*(2*η*ξdotDerivative-2*Dξ*ηdot)= -4*η^2*3*gdot := by
  linear_combination 2*η*g*hjet-(2*g*ηdot+2*η*gdot)*hvalue

end Jets
end MixedPolarCubicJetCalculus
#print axioms MixedPolarCubicJetCalculus.cleared_differential
#print axioms MixedPolarCubicJetCalculus.jet_cubic
