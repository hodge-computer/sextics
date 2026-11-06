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
set_option linter.unusedSimpArgs false
namespace CycleCubicJetCalculus
open ResidueFirstJets
open PolarCovariants CycleCubicFieldDifferential MvPolynomial

open scoped BigOperators

section ClearedDifferential
variable {K : Type*} [CommRing K]
theorem cleared_differential (D : Derivation ℤ K K) (a b c d e f k x y : K)
    (ha : D a=0) (hb : D b=0) (hc : D c=0)
    (hd : D d=0) (he : D e=0) (hf : D f=0)
    (hkSquare : k^2=0) (hDk : D k=0)
    (hu : PolarCubic.cubicJet a b c d e f k x y 1=0) (hy : D y=1) :
    (3*a*x^2+2*d*x*y+f*y^2+2*k*y)*
      (HJet a b c d e f k x y 1*D (ThetaJet a b c d e f k x y 1)-
        2*ThetaJet a b c d e f k x y 1*D (HJet a b c d e f k x y 1))+
      3*JJet a b c d e f k x y 1=0 := by
  let R := constants D
  let a' : R := ⟨a,ha⟩; let b' : R := ⟨b,hb⟩; let c' : R := ⟨c,hc⟩
  let d' : R := ⟨d,hd⟩; let e' : R := ⟨e,he⟩; let f' : R := ⟨f,hf⟩
  let k' : R := ⟨k,hDk⟩
  have hk' : k'^2=0 := Subtype.ext hkSquare
  let φ : R →+* K := R.subtype
  let ρ : Affine R →+* K := eval₂Hom φ ![x,y]
  have hU : ρ (UJetpoly a' b' c' d' e' f' k')=0 := by
    simpa [ρ,φ,UJetpoly,PolarCubic.cubicJet,PolarCubic.cubic,a',b',c',d',e',f',k',Subring.subtype] using hu
  have htwo : pderiv (0 : Fin 2) (2 : Affine R)=0 :=
    (pderiv (R:=R) (0 : Fin 2)).map_natCast 2
  have hPx : ρ (pderiv 0 (UJetpoly a' b' c' d' e' f' k'))=3*a*x^2+2*d*x*y+f*y^2+2*k*y := by
    simp [ρ,φ,UJetpoly,PolarCubic.cubicJet,PolarCubic.cubic,a',b',c',d',e',f',k',MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,
      Pi.single_apply,Fin.ext_iff,Subring.subtype,htwo]
    ring
  have hHmap : ρ (HJetpoly a' b' c' d' e' f' k')=HJet a b c d e f k x y 1 :=
    eval_HJetpoly φ a' b' c' d' e' f' k' x y
  have hQmap : ρ (ThetaJetpoly a' b' c' d' e' f' k')=ThetaJet a b c d e f k x y 1 :=
    eval_ThetaJetpoly φ a' b' c' d' e' f' k' x y
  have hJmap : ρ (JJetpoly a' b' c' d' e' f' k')=JJet a b c d e f k x y 1 :=
    eval_JJetpoly φ a' b' c' d' e' f' k' x y
  have hcompat (p : Affine R) : D (ρ p)=ρ (pderiv 0 p)*D x+ρ (pderiv 1 p) := by
    change D (MvPolynomial.eval₂Hom φ ![x,y] p)=_
    rw [ring_chain D φ ![x,y] (fun r=>r.property) p]
    simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.reduceSucc,
      Finset.univ_eq_empty,Finset.sum_empty,hy,mul_one,add_zero]
    rfl
  have hnormal := hcompat (UJetpoly a' b' c' d' e' f' k')
  rw [hU,map_zero] at hnormal
  have hidentity := congrArg ρ (relative_identityJet a' b' c' d' e' f' k' hk')
  simp only [map_add,map_sub,map_mul,map_ofNat,hU,zero_mul] at hidentity
  rw [← hHmap,← hQmap,← hJmap,← hPx,hcompat,hcompat]
  linear_combination hidentity-
    (ρ (HJetpoly a' b' c' d' e' f' k')*ρ (pderiv 0 (ThetaJetpoly a' b' c' d' e' f' k'))-
      2*ρ (ThetaJetpoly a' b' c' d' e' f' k')*ρ (pderiv 0 (HJetpoly a' b' c' d' e' f' k')))*hnormal
end ClearedDifferential

section Jets
variable {K : Type*} [Field K] [CharZero K]
open TrivSqZeroExt
lemma jet_cubic (a b c d e f x y : K)
    (hu : PolarCubic.cubic a b c d e f x y 1=0)
    (hg : 3*a*x^2+2*d*x*y+f*y^2≠0) :
    PolarCubic.cubicJet (K:=Jet (K:=K)) (a,0) (b,0) (c,0) (d,0) (e,0) (f,0)
      (0,1/2) (x,-x*y/(3*a*x^2+2*d*x*y+f*y^2)) (y,0) (1 : Jet (K:=K))=0 := by
  apply TrivSqZeroExt.ext
  · simpa [PolarCubic.cubicJet,PolarCubic.cubic] using hu
  · simp [PolarCubic.cubicJet,PolarCubic.cubic,smul_eq_mul,op_smul_eq_smul]
    have ht : (-x*y/(3*a*x^2+2*d*x*y+f*y^2))*(3*a*x^2+2*d*x*y+f*y^2)= -x*y :=
      div_mul_cancel₀ _ hg
    linear_combination ht

end Jets
end CycleCubicJetCalculus
#print axioms CycleCubicJetCalculus.cleared_differential
#print axioms CycleCubicJetCalculus.jet_cubic
