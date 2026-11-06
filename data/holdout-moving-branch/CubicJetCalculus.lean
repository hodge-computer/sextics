import HodgeComputer.Constructions.ResidueTransport.FirstJets
import Proposal.CubicFieldDifferential
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-! Infinitesimal cubic calculus over dual numbers. Parameter derivatives
are represented by square-zero jets, so no parameter derivation on the
specialized physical function field is assumed.
Prepared with OpenAI Codex assistance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace CycleCubicJetCalculus
open ResidueFirstJets
open TransitiveCovariants CycleCubicFieldDifferential MvPolynomial

open scoped BigOperators

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

section Jets
variable {K : Type*} [Field K] [CharZero K]
open TrivSqZeroExt
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

end Jets
end CycleCubicJetCalculus
#print axioms CycleCubicJetCalculus.cleared_differential
#print axioms CycleCubicJetCalculus.jet_cubic
