import HodgeComputer.Constructions.EllipticCompanions.Infinity
import HodgeComputer.Constructions.HoldoutCover.FiniteTrace
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic

/-!
Target-independent algebra extracted from the accepted crossed-ternary proof
by GitHub contributor `1337isnot1337`. Original declarations and namespaces
are retained. The accepted application imports the maintained shared modules.

The source explanation credits fqlx's moving-conic/Fermat-cover construction,
Benjamin Diamond's maintained library extraction, the project contributors,
classical elliptic-curve/residue methods, Lean/mathlib, and OpenAI Codex.
This extraction was prepared with Codex assistance for fqlx.

This module supplies reusable steps; it asserts no new instance certificate.
-/

/- Source component: RationalPoleSupport. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CrossedRationalResidue
open Polynomial CrossedElliptic
variable {K L : Type*} [Field K] [Field L]

lemma regular_iff_denom_eval (r : K) (f : RatFunc K) : RegularAt r f ↔ f.denom.eval r≠0 := by
  constructor
  · rintro ⟨P,Q,hQ,he⟩
    have hQ0 : Q≠0 := by intro h; rw [h,eval_zero] at hQ; exact hQ rfl
    have hd : f.denom ∣ Q := (RatFunc.denom_dvd hQ0).mpr ⟨P,he⟩
    obtain ⟨g,hg⟩ := hd
    intro hz
    apply hQ
    rw [hg,eval_mul,hz,zero_mul]
  · intro h
    exact ⟨f.num,f.denom,h,f.num_div_denom.symm⟩

lemma coefficientMap_denom_dvd (φ : K →+* L) (f : RatFunc K) :
    (CrossedRationalCoefficientMap.map φ f).denom ∣ f.denom.map φ := by
  apply (RatFunc.denom_dvd (Polynomial.map_ne_zero f.denom_ne_zero)).mpr
  refine ⟨f.num.map φ,?_⟩
  conv_lhs => rw [← f.num_div_denom]
  rw [map_div₀,CrossedRationalCoefficientMap.map_polynomial,CrossedRationalCoefficientMap.map_polynomial]

lemma coefficientMap_regular (φ : K →+* L) (r : L) (f : RatFunc K)
    (h : (f.denom.map φ).eval r≠0) : RegularAt r (CrossedRationalCoefficientMap.map φ f) := by
  apply (regular_iff_denom_eval r _).mpr
  obtain ⟨g,hg⟩ := coefficientMap_denom_dvd φ f
  intro hn
  apply h
  rw [hg,eval_mul,hn,zero_mul]

lemma eval_map_root_from_old (φ : K →+* L) (P : K[X]) (hp : P≠0) (hs : P.Splits)
    (r : L) (hr : (P.map φ).eval r=0) : ∃ a : K,P.eval a=0 ∧ φ a=r := by
  have hm : P.map φ≠0 := Polynomial.map_ne_zero hp
  have hroot : r∈(P.map φ).roots := (Polynomial.mem_roots hm).mpr hr
  rw [hs.roots_map φ] at hroot
  obtain ⟨a,ha,he⟩ := Multiset.mem_map.mp hroot
  exact ⟨a,(Polynomial.mem_roots hp).mp ha,he⟩

lemma coefficientMap_splits (φ : K →+* L) (f : RatFunc K) (hs : (f.denom.map φ).Splits) :
    (CrossedRationalCoefficientMap.map φ f).denom.Splits :=
  hs.of_dvd (Polynomial.map_ne_zero f.denom_ne_zero) (coefficientMap_denom_dvd φ f)

end CrossedRationalResidue
end
end

/- Source component: EllipticBaseChangeLemmas. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CrossedRationalCoefficientMap
open Polynomial
variable {K L M : Type*} [Field K] [Field L] [Field M]
lemma map_comp (φ : K →+* L) (ψ : L →+* M) (f : RatFunc K) :
    map ψ (map φ f)=map (ψ.comp φ) f := by
  induction f using RatFunc.induction_on with
  | f P Q hQ => simp only [map_div₀,map_polynomial,Polynomial.map_map]
end CrossedRationalCoefficientMap
namespace CrossedEllipticBaseChange
open Polynomial CrossedElliptic CrossedRationalResidue
variable {K L M : Type*} [Field K] [Field L] [Field M] [CharZero K] [CharZero L] [CharZero M]

lemma map_comp (φ : K →+* L) (ψ : L →+* M) (f : E K) : map ψ (map φ f)=map (ψ.comp φ) f := by
  conv_lhs => arg 2; rw [first_second_expansion K f]
  simp only [map_add,map_mul,map_rational,map_y,CrossedRationalCoefficientMap.map_comp]
  exact (map_expansion (ψ.comp φ) f).symm
lemma map_theta (φ : K →+* L) : map φ (thetaRatio (K:=K))=thetaRatio (K:=L) := by
  simp only [thetaRatio,map_div₀,map_pow,map_b,map_a]
lemma map_differentialTrace (φ : K →+* L) (f : E K) :
    differentialTrace (map φ f)=CrossedRationalCoefficientMap.map φ (differentialTrace f) := by
  rw [differentialTrace_second,differentialTrace_second,second_map,map_mul,map_neg,map_ofNat]
lemma map_regular (φ : K →+* L) {r : K} {f : E K} (hf : FibreRegular r f) :
    FibreRegular (φ r) (map φ f) := by
  rw [FibreRegular,first_map,second_map]
  exact ⟨CrossedRationalCoefficientMap.map_regular φ hf.1,CrossedRationalCoefficientMap.map_regular φ hf.2⟩

end CrossedEllipticBaseChange
end
end

/- Source component: EllipticPoleSelection. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CrossedElliptic
open Polynomial CrossedRationalResidue CrossedEllipticTheta
open scoped BigOperators
variable {K L : Type*} [Field K] [Field L] [CharZero K] [CharZero L]

def thetaPolynomial (K : Type*) [Field K] : K[X] := X^3-C 1728
lemma thetaPolynomial_ne_zero : thetaPolynomial K≠0 := (monic_X_pow_sub_C (1728 : K) (by decide : (3 : ℕ)≠0)).ne_zero
lemma thetaPolynomial_map (j : K →+* L) : (thetaPolynomial K).map j=thetaPolynomial L := by
  simp [thetaPolynomial,map_ofNat]
lemma thetaPolynomial_eval (r : K) : (thetaPolynomial K).eval r=r^3-1728 := by simp [thetaPolynomial]
lemma theta_roots_card [DecidableEq K] (hs : (thetaPolynomial K).Splits) : (thetaPolynomial K).roots.toFinset.card=3 := by
  have hsep : (thetaPolynomial K).Separable := separable_X_pow_sub_C 1728 (by norm_num) (by norm_num)
  rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep),← hs.natDegree_eq_card_roots]
  dsimp [thetaPolynomial]
  compute_degree <;> norm_num
lemma mem_theta_roots [DecidableEq K] (r : K) : r∈(thetaPolynomial K).roots.toFinset ↔ r^3=1728 := by
  rw [Multiset.mem_toFinset,Polynomial.mem_roots thetaPolynomial_ne_zero,Polynomial.IsRoot,thetaPolynomial_eval,sub_eq_zero]

lemma theta_trace_regular (r : L) (f : E L) (hf : FibreRegular r f) (hr : r^3≠1728) :
    RegularAt r (differentialTrace (thetaRatio*f)) := by
  have h0 : RegularAt r (kernelZero (K:=L)) := by
    refine ⟨-36*X*(X^3+3456),(X^3-C (1728 : L))^2,?_,?_⟩
    · simpa using pow_ne_zero 2 (sub_ne_zero.mpr hr)
    · simp [kernelZero,map_ofNat]
  have h1 : RegularAt r (kernelOne (K:=L)) := by
    refine ⟨3888*X^4,(X^3-C (1728 : L))^2,?_,?_⟩
    · simpa using pow_ne_zero 2 (sub_ne_zero.mpr hr)
    · simp [kernelOne,map_ofNat]
  rw [theta_trace]
  exact (hf.1.mul h0).add (hf.2.mul h1)

lemma coefficientMap_regular_of_dvd (j : K →+* L) (r : L) (f : RatFunc K) (G : K[X])
    (hd : f.denom∣G) (hG : (G.map j).eval r≠0) :
    RegularAt r (CrossedRationalCoefficientMap.map j f) := by
  apply coefficientMap_regular j r f
  obtain ⟨g,hg⟩ := hd
  intro hz
  apply hG
  rw [hg,Polynomial.map_mul,Polynomial.eval_mul,hz,zero_mul]

/-- Finite residue supports can be selected after a generic separation. -/
theorem separated_pole_sets [DecidableEq L] (j : K →+* L) (f : E L) (bg : E K) (G : K[X])
    (hG : G≠0) (hGsplit : G.Splits)
    (hden0 : (first K bg).denom∣G) (hden1 : (second K bg).denom∣G)
    (htsplit : (thetaPolynomial K).Splits)
    (hregG : ∀ r : K,G.eval r=0 → FibreRegular (j r) f)
    (hregT : ∀ r : K,r^3=1728 → FibreRegular (j r) f)
    (hsplit : (differentialTrace (thetaRatio*f)).denom.Splits) :
    ∃ s t : Finset L,Disjoint s t ∧ t.card=3 ∧ (∀ r∈t,r^3=1728) ∧
      (∀ r∈t,FibreRegular r f) ∧ (∀ r∉s∪t,residueAt r (thetaRatio*f)=0) ∧
      residueOn s (CrossedEllipticBaseChange.map j bg)=0 := by
  classical
  obtain ⟨v,hv,hvsum⟩ := exists_finite_residue_sum (differentialTrace (thetaRatio*f)) hsplit
  let t := (thetaPolynomial L).roots.toFinset
  let s := (v\t).filter (fun r => residueAt r (thetaRatio*f)≠0)
  have hmem (r : L) : r∈s ↔ r∈v ∧ r∉t ∧ residueAt r (thetaRatio*f)≠0 := by
    simp only [s,Finset.mem_filter,Finset.mem_sdiff,and_assoc]
  have hdis : Disjoint s t := by
    rw [Finset.disjoint_left]
    intro r hr hrt
    exact (hmem r).mp hr |>.2.1 hrt
  have htL : (thetaPolynomial L).Splits := by
    rw [← thetaPolynomial_map j]
    exact htsplit.map j
  refine ⟨s,t,hdis,theta_roots_card htL,?_,?_,?_,?_⟩
  · intro r hr
    exact (mem_theta_roots r).mp hr
  · intro r hr
    have hr0 : ((thetaPolynomial K).map j).eval r=0 := by
      rw [thetaPolynomial_map,thetaPolynomial_eval,(mem_theta_roots r).mp hr,sub_self]
    obtain ⟨a,ha,he⟩ := eval_map_root_from_old j (thetaPolynomial K) thetaPolynomial_ne_zero htsplit r hr0
    rw [← he]
    apply hregT a
    simpa only [thetaPolynomial_eval,sub_eq_zero] using ha
  · intro r hr
    by_contra hn
    have hrv : r∈v := by
      by_contra hnv
      exact hn (hv r hnv)
    have hrt : r∉t := by intro h; exact hr (Finset.mem_union_right s h)
    exact hr (Finset.mem_union_left t ((hmem r).mpr ⟨hrv,hrt,hn⟩))
  · simp only [residueOn,LinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro r hr
    obtain ⟨hrv,hrt,hn⟩ := (hmem r).mp hr
    have hgval : (G.map j).eval r≠0 := by
      intro hgr
      obtain ⟨a,ha,he⟩ := eval_map_root_from_old j G hG hGsplit r hgr
      have hrf : FibreRegular r f := by rw [← he]; exact hregG a ha
      have hrtheta : r^3≠1728 := by intro hh; exact hrt ((mem_theta_roots r).mpr hh)
      exact hn ((theta_trace_regular r f hrf hrtheta).residue_eq_zero)
    apply residueAt_regular
    rw [FibreRegular,CrossedEllipticBaseChange.first_map,CrossedEllipticBaseChange.second_map]
    exact ⟨coefficientMap_regular_of_dvd j r _ G hden0 hgval,
      coefficientMap_regular_of_dvd j r _ G hden1 hgval⟩

end CrossedElliptic
end
end

/- Source component: EllipticPoleFields. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CrossedEllipticPoleFields
open Polynomial CrossedElliptic CrossedRationalResidue
variable (K : Type*) [Field K] [CharZero K] (G : K[X])

abbrev First := (G*thetaPolynomial K).SplittingField

def pointPolynomial : (First K G)[X] := by
  classical
  exact ∏ r∈(G.map (algebraMap K (First K G))).roots.toFinset,
    (X^2-C (r^3-432))

abbrev Points := (pointPolynomial K G).SplittingField
instance (priority:=2000) pointsAlgebra : Algebra K (Points K G) :=
  ((algebraMap (First K G) (Points K G)).comp (algebraMap K (First K G))).toAlgebra
instance (priority:=2000) firstModule : Module K (First K G) := Algebra.toModule
instance (priority:=2000) firstSMul : SMul K (First K G) := (firstModule K G).toSMul
instance (priority:=2000) pointsFirstModule : Module (First K G) (Points K G) := Algebra.toModule
instance (priority:=2000) pointsFirstSMul : SMul (First K G) (Points K G) := (pointsFirstModule K G).toSMul
instance (priority:=2000) pointsModule : Module K (Points K G) := Algebra.toModule
instance (priority:=2000) pointsSMul : SMul K (Points K G) := (pointsModule K G).toSMul
instance pointsTower : IsScalarTower K (First K G) (Points K G) :=
  IsScalarTower.of_algebraMap_eq (R:=K) (S:=First K G) (A:=Points K G) (fun _ => rfl)
instance pointsFinite : FiniteDimensional K (Points K G) :=
  Module.Finite.trans (First K G) (Points K G)

def inclusion : K →+* Points K G := algebraMap K (Points K G)

lemma first_G_split (hG : G≠0) : (G.map (algebraMap K (First K G))).Splits := by
  have hs := IsSplittingField.splits (First K G) (G*thetaPolynomial K)
  rw [Polynomial.map_mul] at hs
  exact hs.of_dvd (mul_ne_zero (Polynomial.map_ne_zero hG)
    (Polynomial.map_ne_zero thetaPolynomial_ne_zero)) (dvd_mul_right _ _)
lemma first_theta_split (hG : G≠0) : ((thetaPolynomial K).map (algebraMap K (First K G))).Splits := by
  have hs := IsSplittingField.splits (First K G) (G*thetaPolynomial K)
  rw [Polynomial.map_mul] at hs
  exact hs.of_dvd (mul_ne_zero (Polynomial.map_ne_zero hG)
    (Polynomial.map_ne_zero thetaPolynomial_ne_zero)) (dvd_mul_left _ _)
lemma G_split (hG : G≠0) : (G.map (inclusion K G)).Splits := by
  have h := (first_G_split K G hG).map (algebraMap (First K G) (Points K G))
  simpa only [Polynomial.map_map,← IsScalarTower.algebraMap_eq K (First K G) (Points K G),inclusion] using h
lemma theta_split (hG : G≠0) : (thetaPolynomial (Points K G)).Splits := by
  have h := (first_theta_split K G hG).map (algebraMap (First K G) (Points K G))
  simpa only [Polynomial.map_map,thetaPolynomial_map] using h
lemma pointPolynomial_ne_zero : pointPolynomial K G≠0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro r hr
  exact (monic_X_pow_sub_C _ (by decide : (2 : ℕ)≠0)).ne_zero

lemma root_has_point (hG : G≠0) (r : Points K G) (hr : (G.map (inclusion K G)).eval r=0) :
    ∃ s : Points K G,s^2=r^3-432 := by
  classical
  have hr' : ((G.map (algebraMap K (First K G))).map (algebraMap (First K G) (Points K G))).eval r=0 := by
    simpa only [Polynomial.map_map,← IsScalarTower.algebraMap_eq K (First K G) (Points K G),inclusion] using hr
  obtain ⟨a,ha,hea⟩ := eval_map_root_from_old (algebraMap (First K G) (Points K G))
    (G.map (algebraMap K (First K G))) (Polynomial.map_ne_zero hG) (first_G_split K G hG) r hr'
  have hamem : a∈(G.map (algebraMap K (First K G))).roots.toFinset := by
    rw [Multiset.mem_toFinset,Polynomial.mem_roots (Polynomial.map_ne_zero hG)]
    exact ha
  have hd : (X^2-C (a^3-432))∣pointPolynomial K G := Finset.dvd_prod_of_mem _ hamem
  have hs := IsSplittingField.splits (Points K G) (pointPolynomial K G)
  have hf := hs.of_dvd (Polynomial.map_ne_zero (pointPolynomial_ne_zero K G))
    (Polynomial.map_dvd (algebraMap (First K G) (Points K G)) hd)
  have hdg : ((X^2-C (a^3-432)).map (algebraMap (First K G) (Points K G))).degree≠0 := by
    simp only [Polynomial.map_sub,Polynomial.map_pow,Polynomial.map_X,Polynomial.map_C]
    rw [degree_X_pow_sub_C (by decide : 0<2)]
    norm_num
  obtain ⟨s,hs⟩ := hf.exists_eval_eq_zero hdg
  refine ⟨s,?_⟩
  simp only [Polynomial.map_sub,Polynomial.map_pow,Polynomial.map_X,Polynomial.map_C,
    Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_ofNat,
    map_sub,map_pow,map_ofNat,hea,Polynomial.map_ofNat] at hs
  exact sub_eq_zero.mp hs

end CrossedEllipticPoleFields
end
end

/- Source component: EllipticContraction. -/
section

/- The algebraic contraction step, with every residue and pole-separation
   requirement exposed as a hypothesis. It is not an existence theorem. -/
noncomputable section
open scoped BigOperators
namespace CrossedEllipticContraction
variable {K L I J : Type*} [Field K] [CharZero K] [Field L] [Algebra K L]
  [Fintype I] [Fintype J]

theorem contraction
    (R : L →ₗ[K] K) (δ : Derivation ℤ L L)
    (DX : I → Derivation ℤ K K) (DY : J → Derivation ℤ K K)
    (EX : I → Derivation ℤ L L) (EY : J → Derivation ℤ L L)
    (hRX : ∀ i f, R (EX i f) = DX i (R f))
    (hRY : ∀ i f, R (EY i f) = DY i (R f))
    (hRδ : ∀ f, R (δ f) = 0)
    (α β : K) (h : L) (bf bg : L) (Cf : I → L) (Cg : J → L)
    (hfirst : δ bf + ∑ i, EX i (Cf i) = algebraMap K L α)
    (hsecond : δ bg + ∑ j, EY j (Cg j) = algebraMap K L β * h)
    (hindX : ∀ i, EX i bg = 0) (hindY : ∀ j, EY j bf = 0)
    (hβ : ∀ i, DX i β = 0) (hbg : R bg = 0)
    (ξ : I → K) (hpair : R (bf*h) = 3*α-∑ i, DX i (ξ i)) :
    ∃ (Ux : I → K) (Uy : J → K),
      (∀ i, Ux i = (R (Cf i*bg)+β*ξ i)/3) ∧
      (∀ j, Uy j = R (bf*Cg j)/3) ∧
      (∑ i, DX i (Ux i)) + (∑ j, DY j (Uy j)) = α*β := by
  have hrmul (c : K) (f : L) : R (algebraMap K L c*f) = c*R f := by
    simpa [Algebra.smul_def] using R.map_smul c f
  have hx (i : I) : DX i (R (Cf i*bg)) = R (EX i (Cf i)*bg) := by
    rw [← hRX,Derivation.leibniz,hindX]
    simp only [smul_eq_mul,mul_zero,zero_add]
    congr 1
    ring
  have hy (j : J) : DY j (R (bf*Cg j)) = R (bf*EY j (Cg j)) := by
    rw [← hRY,Derivation.leibniz,hindY]
    simp only [smul_eq_mul,mul_zero,add_zero]
  have hsx : (∑ i, EX i (Cf i)) = algebraMap K L α-δ bf := by
    linear_combination hfirst
  have hsy : (∑ j, EY j (Cg j)) = algebraMap K L β*h-δ bg := by
    linear_combination hsecond
  have hdiv : (∑ i, DX i (R (Cf i*bg))) + (∑ j, DY j (R (bf*Cg j))) =
      β*R (bf*h) := by
    simp_rw [hx,hy]
    rw [← map_sum,← map_sum,← map_add]
    rw [← Finset.sum_mul,← Finset.mul_sum,hsx,hsy]
    have he : (algebraMap K L α-δ bf)*bg + bf*(algebraMap K L β*h-δ bg) =
        algebraMap K L α*bg+algebraMap K L β*(bf*h)-δ (bf*bg) := by
      rw [Derivation.leibniz]
      simp only [smul_eq_mul]
      ring
    rw [he,map_sub,map_add,hrmul,hrmul,hRδ,hbg,mul_zero,zero_add,sub_zero]
  let Ux : I → K := fun i => (R (Cf i*bg)+β*ξ i)/3
  let Uy : J → K := fun j => R (bf*Cg j)/3
  refine ⟨Ux,Uy,fun _ => rfl,fun _ => rfl,?_⟩
  have hux (i : I) : DX i (Ux i) =
      (DX i (R (Cf i*bg))+β*DX i (ξ i))/3 := by
    have hc : DX i (3 : K) = 0 := (DX i).map_natCast 3
    dsimp [Ux]
    rw [Derivation.leibniz_div_const _ _ _ hc,map_add,Derivation.leibniz,hβ]
    simp only [smul_eq_mul,mul_zero,add_zero,div_eq_mul_inv]
    ring
  have huy (j : J) : DY j (Uy j) = DY j (R (bf*Cg j))/3 := by
    have hc : DY j (3 : K) = 0 := (DY j).map_natCast 3
    dsimp [Uy]
    rw [Derivation.leibniz_div_const _ _ _ hc]
    simp only [smul_eq_mul,div_eq_mul_inv]
    ring
  simp_rw [hux,huy]
  rw [← Finset.sum_div,← Finset.sum_div,← add_div]
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  rw [add_right_comm,hdiv,hpair]
  field_simp
  ring

end CrossedEllipticContraction
end
end

/- Source component: DivergenceLinearDescent. -/
section

noncomputable section
namespace CrossedDivergenceDescent
open HoldoutConstruction CrossedElliptic
open scoped BigOperators
variable {K L I J : Type*} [Field K] [Field L] [Algebra K L] [Fintype I] [Fintype J]

lemma linear_descent (T : L →ₗ[K] K) (hT : ∀ c,T (algebraMap K L c)=c)
    (DX : I → Derivation ℤ K K) (DY : J → Derivation ℤ K K)
    (EX : I → Derivation ℤ L L) (EY : J → Derivation ℤ L L)
    (hX : ∀ i x,T (EX i x)=DX i (T x)) (hY : ∀ j x,T (EY j x)=DY j (T x))
    (c : K) (vx : I → L) (vy : J → L)
    (he : (∑ i,EX i (vx i))+(∑ j,EY j (vy j))=algebraMap K L c) :
    (∑ i,DX i (T (vx i)))+(∑ j,DY j (T (vy j)))=c := by
  have h := congrArg T he
  simpa only [map_add,map_sum,hX,hY,hT] using h

lemma finite_descent [CharZero K] [FiniteDimensional K L]
    (DX : I → Derivation ℤ K K) (DY : J → Derivation ℤ K K)
    (EX : I → Derivation ℤ L L) (EY : J → Derivation ℤ L L)
    (hX : ∀ i x,EX i (algebraMap K L x)=algebraMap K L (DX i x))
    (hY : ∀ j x,EY j (algebraMap K L x)=algebraMap K L (DY j x))
    (c : K) (vx : I → L) (vy : J → L)
    (he : (∑ i,EX i (vx i))+(∑ j,EY j (vy j))=algebraMap K L c) :
    ∃ ux : I → K,∃ uy : J → K,(∑ i,DX i (ux i))+(∑ j,DY j (uy j))=c := by
  refine ⟨fun i => Algebra.normalizedTrace K L (vx i),fun j => Algebra.normalizedTrace K L (vy j),?_⟩
  exact linear_descent (Algebra.normalizedTrace K L) (Algebra.normalizedTrace_algebraMap_apply_eq_self K L)
    DX DY EX EY (fun i x => finiteNormalizedTrace_derivation _ _ (hX i) x)
    (fun j x => finiteNormalizedTrace_derivation _ _ (hY j) x) c vx vy he

lemma elliptic_descent [CharZero K]
    (DX : I → Derivation ℤ K K) (DY : J → Derivation ℤ K K)
    (c : K) (vx : I → E K) (vy : J → E K)
    (he : (∑ i,coefficient (DX i) (vx i))+(∑ j,coefficient (DY j) (vy j))=algebraMap K (E K) c) :
    ∃ ux : I → K,∃ uy : J → K,(∑ i,DX i (ux i))+(∑ j,DY j (uy j))=c := by
  refine ⟨fun i => ellipticConstantTerm (vx i),fun j => ellipticConstantTerm (vy j),?_⟩
  exact linear_descent ellipticConstantTerm ellipticConstantTerm_base DX DY
    (fun i => coefficient (DX i)) (fun j => coefficient (DY j))
    (fun i x => ellipticConstantTerm_derivation (DX i) x)
    (fun j x => ellipticConstantTerm_derivation (DY j) x) c vx vy he

end CrossedDivergenceDescent
end
end

/- Source component: EllipticProductAfterSplit. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CrossedElliptic
open Polynomial HoldoutConstruction CrossedRationalResidue CrossedDivergenceDescent
open scoped BigOperators
variable {K I J : Type*} [Field K] [CharZero K] [Fintype I] [Fintype J]
local instance : Algebra ℤ (E K) := Ring.toIntAlgebra _

theorem product_divergence_after_split
    (DX : I → Derivation ℤ K K) (DY : J → Derivation ℤ K K)
    (α β : K) (bf bg : E K) (Cf : I → E K) (Cg : J → E K)
    (hfirst : delta bf+∑ i,coefficient (DX i) (Cf i)=algebraMap K (E K) α)
    (hsecond : delta bg+∑ j,coefficient (DY j) (Cg j)=algebraMap K (E K) β*thetaRatio)
    (hindX : ∀ i,coefficient (DX i) bg=0) (hindY : ∀ j,coefficient (DY j) bf=0)
    (hβ : ∀ i,DX i β=0)
    (G : K[X]) (hG : G≠0) (hGs : G.Splits)
    (hd0 : (first K bg).denom∣G) (hd1 : (second K bg).denom∣G)
    (hts : (thetaPolynomial K).Splits)
    (hpoints : ∀ r : K,G.eval r=0 → ∃ s : K,s^2=r^3-432) :
    ∃ ux : I → K,∃ uy : J → K,(∑ i,DX i (ux i))+(∑ j,DY j (uy j))=α*β := by
  classical
  let L := E K
  let j : K →+* L := algebraMap K (E K)
  let f := genericTranslate K bf
  let g := CrossedEllipticBaseChange.map j bg
  let P := (differentialTrace (thetaRatio*f)).denom
  let N := P.SplittingField
  let l : L →+* N := algebraMap L N
  let κ : K →+* N := l.comp j
  let d (D : Derivation ℤ K K) : Derivation ℤ N N :=
    extendFiniteDerivation (L:=N) (coefficient D)
  let Φ : E K →+* E N := (CrossedEllipticBaseChange.map l).comp (genericTranslate K)
  let Ψ : E K →+* E N := (CrossedEllipticBaseChange.map l).comp (CrossedEllipticBaseChange.map j)
  have hd (D : Derivation ℤ K K) (x : L) : d D (l x)=l (coefficient D x) := extendFiniteDerivation_apply _ _
  have hΦc (c : K) : Φ (algebraMap K (E K) c)=algebraMap N (E N) (κ c) := by
    change CrossedEllipticBaseChange.map l (genericTranslate K (algebraMap K (E K) c))=_
    rw [genericTranslate_base,CrossedEllipticBaseChange.map_base]
    rfl
  have hΨc (c : K) : Ψ (algebraMap K (E K) c)=algebraMap N (E N) (κ c) := by
    change CrossedEllipticBaseChange.map l (CrossedEllipticBaseChange.map j (algebraMap K (E K) c))=_
    rw [CrossedEllipticBaseChange.map_base,CrossedEllipticBaseChange.map_base]
    rfl
  have hΦδ (z : E K) : delta (Φ z)=Φ (delta z) := by
    change delta (CrossedEllipticBaseChange.map l (genericTranslate K z))=_
    rw [CrossedEllipticBaseChange.map_delta,genericTranslate_delta]
    rfl
  have hΨδ (z : E K) : delta (Ψ z)=Ψ (delta z) := by
    change delta (CrossedEllipticBaseChange.map l (CrossedEllipticBaseChange.map j z))=_
    rw [CrossedEllipticBaseChange.map_delta,CrossedEllipticBaseChange.map_delta]
    rfl
  have hΦD (D : Derivation ℤ K K) (z : E K) : coefficient (d D) (Φ z)=Φ (coefficient D z) := by
    change coefficient (d D) (CrossedEllipticBaseChange.map l (genericTranslate K z))=_
    rw [CrossedEllipticBaseChange.map_coefficient l (coefficient D) (d D) (hd D),genericTranslate_coefficient]
    rfl
  have hΨD (D : Derivation ℤ K K) (z : E K) : coefficient (d D) (Ψ z)=Ψ (coefficient D z) := by
    change coefficient (d D) (CrossedEllipticBaseChange.map l (CrossedEllipticBaseChange.map j z))=_
    rw [CrossedEllipticBaseChange.map_coefficient l (coefficient D) (d D) (hd D),
      CrossedEllipticBaseChange.map_coefficient j D (coefficient D) (coefficient_scalar D)]
    rfl
  have hΨθ : Ψ (thetaRatio (K:=K))=thetaRatio (K:=N) := by
    change CrossedEllipticBaseChange.map l (CrossedEllipticBaseChange.map j thetaRatio)=_
    rw [CrossedEllipticBaseChange.map_theta,CrossedEllipticBaseChange.map_theta]
  have hF : delta (Φ bf)+∑ i,coefficient (d (DX i)) (Φ (Cf i))=algebraMap N (E N) (κ α) := by
    rw [hΦδ]
    simp_rw [hΦD]
    rw [← map_sum,← map_add,hfirst,hΦc]
  have hB : delta (Ψ bg)+∑ i,coefficient (d (DY i)) (Ψ (Cg i))=algebraMap N (E N) (κ β)*thetaRatio := by
    rw [hΨδ]
    simp_rw [hΨD]
    rw [← map_sum,← map_add,hsecond,map_mul,hΨc,hΨθ]
  have h0x (i : I) : coefficient (d (DX i)) (Ψ bg)=0 := by rw [hΨD,hindX,map_zero]
  have h0y (i : J) : coefficient (d (DY i)) (Φ bf)=0 := by rw [hΦD,hindY,map_zero]
  have hβN (i : I) : d (DX i) (κ β)=0 := by
    change d (DX i) (l (j β))=0
    rw [hd,coefficient_scalar,hβ,map_zero,map_zero]
  have hregG (r : K) (hr : G.eval r=0) : FibreRegular (κ r) (Φ bf) := by
    obtain ⟨s,hs⟩ := hpoints r hr
    exact CrossedEllipticBaseChange.map_regular l (genericTranslate_specializes K r s hs bf).1
  have hregT (r : K) (hr : r^3=1728) : FibreRegular (κ r) (Φ bf) := by
    have hs : (-36 : K)^2=r^3-432 := by rw [hr]; norm_num
    exact CrossedEllipticBaseChange.map_regular l (genericTranslate_specializes K r (-36) hs bf).1
  have hsplit : (differentialTrace (thetaRatio*Φ bf)).denom.Splits := by
    have he : differentialTrace (thetaRatio*Φ bf)=CrossedRationalCoefficientMap.map l
        (differentialTrace (thetaRatio*f)) := by
      rw [← CrossedEllipticBaseChange.map_differentialTrace l]
      rw [map_mul (CrossedEllipticBaseChange.map l),CrossedEllipticBaseChange.map_theta]
      rfl
    rw [he]
    exact coefficientMap_splits l _ (IsSplittingField.splits N P)
  obtain ⟨s,t,hst,htcard,ht,hreg,hout,hbg⟩ := separated_pole_sets κ (Φ bf) bg G hG hGs hd0 hd1 hts
    hregG hregT hsplit
  have hbg' : residueOn s (Ψ bg)=0 := by
    change residueOn s (CrossedEllipticBaseChange.map l (CrossedEllipticBaseChange.map j bg))=0
    rw [CrossedEllipticBaseChange.map_comp]
    exact hbg
  obtain ⟨ξ,hξ⟩ := theta_residue_pairing s t hst htcard ht (Φ bf) (fun i => Φ (Cf i))
    (fun i => d (DX i)) (κ α) hF hreg hsplit hout
  obtain ⟨vx,vy,hvx,hvy,hdiv⟩ := CrossedEllipticContraction.contraction
    (residueOn s) delta (fun i => d (DX i)) (fun i => d (DY i))
    (fun i => coefficient (d (DX i))) (fun i => coefficient (d (DY i)))
    (fun i z => residueOn_coefficient s (d (DX i)) z)
    (fun i z => residueOn_coefficient s (d (DY i)) z)
    (residueOn_delta s) (κ α) (κ β) thetaRatio (Φ bf) (Ψ bg)
    (fun i => Φ (Cf i)) (fun i => Ψ (Cg i)) hF hB h0x h0y hβN hbg' ξ hξ
  have hdivN : (∑ i,d (DX i) (vx i))+(∑ i,d (DY i) (vy i))=
      algebraMap L N (j (α*β)) := by
    rw [map_mul,map_mul]
    exact hdiv
  obtain ⟨vxL,vyL,hL⟩ := finite_descent (fun i => coefficient (DX i)) (fun i => coefficient (DY i))
    (fun i => d (DX i)) (fun i => d (DY i)) (fun i z => hd (DX i) z) (fun i z => hd (DY i) z)
    (j (α*β)) vx vy hdivN
  exact elliptic_descent DX DY (α*β) vxL vyL hL

end CrossedElliptic
end
end

/- Source component: EllipticProductDivergence. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CrossedElliptic
open Polynomial HoldoutConstruction CrossedRationalResidue CrossedDivergenceDescent
open scoped BigOperators
variable {K I J : Type*} [Field K] [CharZero K] [Fintype I] [Fintype J]

/-- Algebraic residue contraction, descended to the original coefficient field. -/
theorem product_divergence
    (DX : I → Derivation ℤ K K) (DY : J → Derivation ℤ K K)
    (α β : K) (bf bg : E K) (Cf : I → E K) (Cg : J → E K)
    (hfirst : delta bf+∑ i,coefficient (DX i) (Cf i)=algebraMap K (E K) α)
    (hsecond : delta bg+∑ j,coefficient (DY j) (Cg j)=algebraMap K (E K) β*thetaRatio)
    (hindX : ∀ i,coefficient (DX i) bg=0) (hindY : ∀ j,coefficient (DY j) bf=0)
    (hβ : ∀ i,DX i β=0) :
    ∃ ux : I → K,∃ uy : J → K,(∑ i,DX i (ux i))+(∑ j,DY j (uy j))=α*β := by
  let G := (first K bg).denom*(second K bg).denom
  have hG : G≠0 := mul_ne_zero (RatFunc.denom_ne_zero _) (RatFunc.denom_ne_zero _)
  let L := CrossedEllipticPoleFields.Points K G
  let κ : K →+* L := CrossedEllipticPoleFields.inclusion K G
  let d (D : Derivation ℤ K K) : Derivation ℤ L L := extendFiniteDerivation (L:=L) D
  let Φ : E K →+* E L := CrossedEllipticBaseChange.map κ
  have hd (D : Derivation ℤ K K) (x : K) : d D (κ x)=κ (D x) := extendFiniteDerivation_apply _ _
  have hc (c : K) : Φ (algebraMap K (E K) c)=algebraMap L (E L) (κ c) :=
    CrossedEllipticBaseChange.map_base κ c
  have hδ (f : E K) : delta (Φ f)=Φ (delta f) := CrossedEllipticBaseChange.map_delta κ f
  have hD (D : Derivation ℤ K K) (f : E K) : coefficient (d D) (Φ f)=Φ (coefficient D f) :=
    CrossedEllipticBaseChange.map_coefficient κ D (d D) (hd D) f
  have hF : delta (Φ bf)+∑ i,coefficient (d (DX i)) (Φ (Cf i))=algebraMap L (E L) (κ α) := by
    rw [hδ]
    simp_rw [hD]
    rw [← map_sum,← map_add,hfirst,hc]
  have hB : delta (Φ bg)+∑ i,coefficient (d (DY i)) (Φ (Cg i))=algebraMap L (E L) (κ β)*thetaRatio := by
    rw [hδ]
    simp_rw [hD]
    rw [← map_sum,← map_add,hsecond,map_mul,hc]
    exact congrArg _ (CrossedEllipticBaseChange.map_theta κ)
  have h0x (i : I) : coefficient (d (DX i)) (Φ bg)=0 := by rw [hD,hindX,map_zero]
  have h0y (i : J) : coefficient (d (DY i)) (Φ bf)=0 := by rw [hD,hindY,map_zero]
  have hβL (i : I) : d (DX i) (κ β)=0 := by rw [hd,hβ,map_zero]
  have hd0 : (first L (Φ bg)).denom∣G.map κ := by
    rw [CrossedEllipticBaseChange.first_map]
    exact (coefficientMap_denom_dvd κ _).trans (Polynomial.map_dvd κ (dvd_mul_right _ _))
  have hd1 : (second L (Φ bg)).denom∣G.map κ := by
    rw [CrossedEllipticBaseChange.second_map]
    exact (coefficientMap_denom_dvd κ _).trans (Polynomial.map_dvd κ (dvd_mul_left _ _))
  obtain ⟨vx,vy,hdiv⟩ := product_divergence_after_split (fun i => d (DX i)) (fun i => d (DY i))
    (κ α) (κ β) (Φ bf) (Φ bg) (fun i => Φ (Cf i)) (fun i => Φ (Cg i)) hF hB h0x h0y hβL
    (G.map κ) (Polynomial.map_ne_zero hG) (CrossedEllipticPoleFields.G_split K G hG) hd0 hd1
    (CrossedEllipticPoleFields.theta_split K G hG) (CrossedEllipticPoleFields.root_has_point K G hG)
  have hdiv' : (∑ i,d (DX i) (vx i))+(∑ i,d (DY i) (vy i))=algebraMap K L (α*β) := by
    rw [map_mul]
    exact hdiv
  exact finite_descent DX DY (fun i => d (DX i)) (fun i => d (DY i))
    (fun i x => hd (DX i) x) (fun i x => hd (DY i) x) (α*β) vx vy hdiv'

end CrossedElliptic
end
end
