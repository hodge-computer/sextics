import Proposal.PhysicalTransport
import HodgeComputer.Constructions.HoldoutCover.HomogeneousCertificate
import HodgeComputer.Constructions.HoldoutCover.HomogeneousField
import HodgeComputer.Constructions.HoldoutCover.PolynomialCalculus

/- Prepared with OpenAI Codex assistance for contributor 1337isnot1337.
See solution.md for the construction, provenance, and prior-work credit. -/

/- Source component: CompatibleFractions. -/
section

noncomputable section
namespace CrossedCompatibleFractions
variable {R M N : Type*} [CommRing R] [Field M] [Field N]

/-- A common fraction representative in an ambient field and on a hypersurface. -/
def Rel (θ : R →+* M) (ρ : R →+* N) (f : M) (g : N) : Prop :=
  ∃ A D : R,θ D≠0 ∧ ρ D≠0 ∧ f=θ A/θ D ∧ g=ρ A/ρ D

lemma polynomial (θ : R →+* M) (ρ : R →+* N) (A : R) : Rel θ ρ (θ A) (ρ A) :=
  ⟨A,1,by simp,by simp,by simp,by simp⟩
lemma zero (θ : R →+* M) (ρ : R →+* N) : Rel θ ρ 0 0 := by simpa using polynomial θ ρ (0 : R)
lemma one (θ : R →+* M) (ρ : R →+* N) : Rel θ ρ 1 1 := by simpa using polynomial θ ρ (1 : R)

lemma Rel.add {θ : R →+* M} {ρ : R →+* N} {f h : M} {g k : N}
    (hf : Rel θ ρ f g) (hh : Rel θ ρ h k) : Rel θ ρ (f+h) (g+k) := by
  obtain ⟨A,D,hd,hr,rfl,rfl⟩ := hf
  obtain ⟨B,E,he,hs,rfl,rfl⟩ := hh
  refine ⟨A*E+B*D,D*E,by simpa using mul_ne_zero hd he,by simpa using mul_ne_zero hr hs,?_,?_⟩
  all_goals simp only [map_add,map_mul]; field_simp <;> ring
lemma Rel.neg {θ : R →+* M} {ρ : R →+* N} {f : M} {g : N}
    (hf : Rel θ ρ f g) : Rel θ ρ (-f) (-g) := by
  obtain ⟨A,D,hd,hr,rfl,rfl⟩ := hf
  exact ⟨-A,D,hd,hr,by simp only [map_neg,neg_div],by simp only [map_neg,neg_div]⟩
lemma Rel.sub {θ : R →+* M} {ρ : R →+* N} {f h : M} {g k : N}
    (hf : Rel θ ρ f g) (hh : Rel θ ρ h k) : Rel θ ρ (f-h) (g-k) := by
  simpa only [sub_eq_add_neg] using hf.add hh.neg
lemma Rel.mul {θ : R →+* M} {ρ : R →+* N} {f h : M} {g k : N}
    (hf : Rel θ ρ f g) (hh : Rel θ ρ h k) : Rel θ ρ (f*h) (g*k) := by
  obtain ⟨A,D,hd,hr,rfl,rfl⟩ := hf
  obtain ⟨B,E,he,hs,rfl,rfl⟩ := hh
  refine ⟨A*B,D*E,by simpa using mul_ne_zero hd he,by simpa using mul_ne_zero hr hs,?_,?_⟩
  all_goals simp only [map_mul]; ring
lemma Rel.inv {θ : R →+* M} {ρ : R →+* N} {f : M} {g : N}
    (hθ : Function.Injective θ) (hf : Rel θ ρ f g) (hg : g≠0) : Rel θ ρ f⁻¹ g⁻¹ := by
  obtain ⟨A,D,hd,hr,rfl,rfl⟩ := hf
  have ha : ρ A≠0 := (div_ne_zero_iff.mp hg).1
  have ha0 : A≠0 := by intro h; exact ha (by rw [h,map_zero])
  have hθa : θ A≠0 := by simpa only [map_zero] using hθ.ne ha0
  exact ⟨D,A,hθa,ha,by rw [inv_div],by rw [inv_div]⟩
lemma Rel.div {θ : R →+* M} {ρ : R →+* N} {f h : M} {g k : N}
    (hθ : Function.Injective θ) (hf : Rel θ ρ f g) (hh : Rel θ ρ h k) (hk : k≠0) :
    Rel θ ρ (f/h) (g/k) := by
  simpa only [div_eq_mul_inv] using hf.mul (hh.inv hθ hk)
lemma Rel.pow {θ : R →+* M} {ρ : R →+* N} {f : M} {g : N}
    (hf : Rel θ ρ f g) (n : ℕ) : Rel θ ρ (f^n) (g^n) := by
  induction n with
  | zero => simpa using one θ ρ
  | succ n h => simpa only [pow_succ] using h.mul hf

lemma Rel.sum {ι : Type*} {θ : R →+* M} {ρ : R →+* N} (s : Finset ι) (f : ι → M) (g : ι → N)
    (h : ∀ i∈s,Rel θ ρ (f i) (g i)) : Rel θ ρ (∑ i∈s,f i) (∑ i∈s,g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero θ ρ
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma common_denominator {ι : Type*} [Fintype ι] (θ : R →+* M) (ρ : R →+* N)
    (f : ι → M) (g : ι → N) (h : ∀ i,Rel θ ρ (f i) (g i)) :
    ∃ D : R,∃ A : ι → R,θ D≠0 ∧ ρ D≠0 ∧ ∀ i,θ (A i)=f i*θ D := by
  classical
  choose A D hd hr hf hg using h
  let E : R := ∏ i,D i
  let B : ι → R := fun i => A i*∏ j∈Finset.univ.erase i,D j
  have hE : θ E≠0 := by simpa [E] using Finset.prod_ne_zero_iff.mpr (fun i _ => hd i)
  have hEr : ρ E≠0 := by simpa [E] using Finset.prod_ne_zero_iff.mpr (fun i _ => hr i)
  refine ⟨E,B,hE,hEr,?_⟩
  intro i
  have he : E=D i*∏ j∈Finset.univ.erase i,D j := (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  change θ (A i*(∏ j∈Finset.univ.erase i,D j))=f i*θ E
  rw [he,map_mul,map_mul,hf i]
  field_simp [hd i]

end CrossedCompatibleFractions
end
end

/- Source component: PhysicalHypersurfaceEvaluation. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace CrossedPhysicalChart
open MvPolynomial Polynomial HoldoutConstruction
open scoped BigOperators

abbrev B := CrossedProductField.Base
abbrev F4 := CrossedProductField.F

def rootPolynomial : F4[X] := Polynomial.X^6+Polynomial.C (CrossedProductField.p/CrossedProductField.q)
abbrev RootField := rootPolynomial.SplittingField
abbrev N := RatFunc RootField

def rootInclusion : F4 →+* RootField := algebraMap F4 RootField
lemma rootPolynomial_degree : (rootPolynomial.map rootInclusion).degree≠0 := by
  change ((Polynomial.X^6+Polynomial.C (CrossedProductField.p/CrossedProductField.q)).map rootInclusion).degree≠0
  simp only [Polynomial.map_add,Polynomial.map_pow,Polynomial.map_X,Polynomial.map_C]
  rw [Polynomial.degree_X_pow_add_C (by decide : 0<6)]
  norm_num
lemma rootPolynomial_splits : (rootPolynomial.map rootInclusion).Splits := IsSplittingField.splits RootField rootPolynomial

def rootValue : RootField := Polynomial.rootOfSplits rootPolynomial_splits rootPolynomial_degree
lemma rootValue_equation : rootValue^6= -rootInclusion (CrossedProductField.p/CrossedProductField.q) := by
  have h := Polynomial.eval_rootOfSplits rootPolynomial_splits rootPolynomial_degree
  change (rootPolynomial.map rootInclusion).eval rootValue=0 at h
  change ((Polynomial.X^6+Polynomial.C (CrossedProductField.p/CrossedProductField.q)).map rootInclusion).eval rootValue=0 at h
  simpa only [Polynomial.map_add,Polynomial.map_pow,Polynomial.map_X,Polynomial.map_C,
    Polynomial.eval_add,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_C,add_eq_zero_iff_eq_neg] using h
lemma rootValue_ne_zero : rootValue≠0 := by
  intro h
  have he := rootValue_equation
  rw [h,zero_pow (by decide : (6 : ℕ)≠0)] at he
  have hn : rootInclusion (CrossedProductField.p/CrossedProductField.q)≠0 :=
    (_root_.map_ne_zero _).mpr (div_ne_zero CrossedProductField.p_ne_zero CrossedProductField.q_ne_zero)
  exact hn (neg_eq_zero.mp he.symm)

def hypBase : F4 →+* N := (RatFunc.C : RootField →+* N).comp rootInclusion
def hypCoordinate (i : Fin 4) : N := hypBase (algebraMap B F4 (MvPolynomial.X i))
def hypLambda : N := RatFunc.C rootValue
def hypRadial : N := RatFunc.X
def hypConstant : ℂ →+* N := hypBase.comp ((algebraMap B F4).comp MvPolynomial.C)
def chartHyp : Fin 6 → N := ![hypCoordinate 0,hypCoordinate 1,hypCoordinate 2,hypCoordinate 3,hypLambda,hypRadial]
def rho : Poly →+* N := MvPolynomial.eval₂Hom hypConstant
  ![hypRadial*hypCoordinate 0,hypRadial*hypCoordinate 1,hypRadial*hypLambda,hypRadial,
    hypRadial*hypLambda*hypCoordinate 2,hypRadial*hypLambda*hypCoordinate 3]
lemma rho_C (c : ℂ) : rho (MvPolynomial.C c)=hypConstant c := MvPolynomial.eval₂Hom_C _ _ c
lemma rho_X (i : Fin 6) : rho (MvPolynomial.X i)=
    ![hypRadial*hypCoordinate 0,hypRadial*hypCoordinate 1,hypRadial*hypLambda,hypRadial,
      hypRadial*hypLambda*hypCoordinate 2,hypRadial*hypLambda*hypCoordinate 3] i := by
  rw [rho,MvPolynomial.eval₂Hom_X']
lemma hypRadial_ne_zero : hypRadial≠0 := CrossedRationalResidue.X_ne_zero
lemma hypLambda_ne_zero : hypLambda≠0 := (_root_.map_ne_zero _).mpr rootValue_ne_zero
lemma hypLambda_equation : hypLambda^6= -hypBase (CrossedProductField.p/CrossedProductField.q) := by
  have he := congrArg (RatFunc.C : RootField →+* N) rootValue_equation
  simpa only [hypLambda,hypBase,map_pow,map_neg,RingHom.comp_apply] using he

lemma hypBase_p : hypBase CrossedProductField.p=ternary (hypConstant (5/7 : ℂ)) (hypCoordinate 0) (hypCoordinate 1) 1 := by
  have hc := map_ratCast hypConstant (5/7 : ℚ)
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hc
  change hypBase (algebraMap B F4 (MvPolynomial.C (5/7 : ℂ)))=(5/7 : N) at hc
  simp [CrossedProductField.p,CrossedProductField.firstMap,CrossedProductField.firstIndex,
    CrossedFanoElliptic.basePolynomial,hypCoordinate,hypConstant,ternary,map_ofNat,hc]
lemma hypBase_q : hypBase CrossedProductField.q=ternary (hypConstant (5/7 : ℂ)) (hypCoordinate 2) (hypCoordinate 3) 1 := by
  have hc := map_ratCast hypConstant (5/7 : ℚ)
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hc
  change hypBase (algebraMap B F4 (MvPolynomial.C (5/7 : ℂ)))=(5/7 : N) at hc
  simp [CrossedProductField.q,CrossedProductField.secondMap,CrossedProductField.secondIndex,
    CrossedFanoElliptic.basePolynomial,hypCoordinate,hypConstant,ternary,map_ofNat,hc]
lemma rho_F : rho physicalF=0 := by
  have he : rho physicalF=hypRadial^6*(hypBase CrossedProductField.p+hypLambda^6*hypBase CrossedProductField.q) := by
    simp [physicalF,ternary,rho_X,rho_C,hypBase_p,hypBase_q,map_ofNat]
    ring
  rw [he,hypLambda_equation,map_div₀]
  have hq : hypBase CrossedProductField.q≠0 := (_root_.map_ne_zero _).mpr CrossedProductField.q_ne_zero
  field_simp
  ring

end CrossedPhysicalChart
end
end

/- Source component: PhysicalCompatibleFractions. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace CrossedPhysicalChart
open MvPolynomial CrossedCompatibleFractions

lemma ratio_relation (i j : Fin 6) (hj : rho (X j)≠0) :
    Rel θ rho (θ (X i)/θ (X j)) (rho (X i)/rho (X j)) :=
  (polynomial θ rho (X i)).div θ_injective (polynomial θ rho (X j)) hj

lemma coordinate_relation (i : Fin 6) : Rel θ rho (coordinate i) (chartHyp i) := by
  fin_cases i
  · have h := ratio_relation 0 3 (by simp [rho_X,hypRadial_ne_zero,hypLambda_ne_zero])
    convert h using 1 <;> simp [θ_X,rho_X,chartHyp] <;>
      field_simp [coordinate_ne_zero 4,coordinate_ne_zero 5,hypRadial_ne_zero,hypLambda_ne_zero] <;> ring
  · have h := ratio_relation 1 3 (by simp [rho_X,hypRadial_ne_zero,hypLambda_ne_zero])
    convert h using 1 <;> simp [θ_X,rho_X,chartHyp] <;>
      field_simp [coordinate_ne_zero 4,coordinate_ne_zero 5,hypRadial_ne_zero,hypLambda_ne_zero] <;> ring
  · have h := ratio_relation 4 2 (by simp [rho_X,hypRadial_ne_zero,hypLambda_ne_zero])
    convert h using 1 <;> simp [θ_X,rho_X,chartHyp] <;>
      field_simp [coordinate_ne_zero 4,coordinate_ne_zero 5,hypRadial_ne_zero,hypLambda_ne_zero] <;> ring
  · have h := ratio_relation 5 2 (by simp [rho_X,hypRadial_ne_zero,hypLambda_ne_zero])
    convert h using 1 <;> simp [θ_X,rho_X,chartHyp] <;>
      field_simp [coordinate_ne_zero 4,coordinate_ne_zero 5,hypRadial_ne_zero,hypLambda_ne_zero] <;> ring
  · have h := ratio_relation 2 3 (by simp [rho_X,hypRadial_ne_zero,hypLambda_ne_zero])
    convert h using 1 <;> simp [θ_X,rho_X,chartHyp] <;>
      field_simp [coordinate_ne_zero 4,coordinate_ne_zero 5,hypRadial_ne_zero,hypLambda_ne_zero] <;> ring
  · simpa [θ_X,rho_X,chartHyp] using polynomial θ rho (X 3)

lemma base_polynomial_relation (P : B) :
    Rel θ rho (baseRingMap P) (hypBase (algebraMap B F4 P)) := by
  have hX (i : Fin 4) : Rel θ rho (baseRingMap (X i)) (hypBase (algebraMap B F4 (X i))) := by
    rw [baseRingMap_X]
    fin_cases i <;> exact coordinate_relation _
  induction P using MvPolynomial.induction_on with
  | C c =>
    rw [baseRingMap_C]
    simpa only [θ_C,rho_C,hypConstant,RingHom.comp_apply] using polynomial θ rho (C c)
  | add P Q hP hQ => simpa only [map_add] using hP.add hQ
  | mul_X P i hP => simpa only [map_mul] using hP.mul (hX i)

lemma baseValue_relation (f : F4) : Rel θ rho (baseValue f) (hypBase f) := by
  obtain ⟨a,b,hb,rfl⟩ := IsFractionRing.div_surjective B f
  rw [map_div₀,map_div₀,baseValue_polynomial,baseValue_polynomial]
  have hb0 : b≠0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbF : algebraMap B F4 b≠0 := by simpa only [map_zero] using (IsFractionRing.injective B F4).ne hb0
  exact (base_polynomial_relation a).div θ_injective (base_polynomial_relation b)
    ((_root_.map_ne_zero _).mpr hbF)

lemma numeral_relation (n : ℕ) : Rel θ rho (n : M) (n : N) := by
  simpa only [map_natCast] using polynomial θ rho (n : Poly)

end CrossedPhysicalChart
end
end

/- Source component: PhysicalTransportCompatibility. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CrossedPhysicalChart
open CrossedCompatibleFractions

lemma hypBase_p_ne_zero : hypBase CrossedProductField.p≠0 := (_root_.map_ne_zero _).mpr CrossedProductField.p_ne_zero
lemma hypBase_q_ne_zero : hypBase CrossedProductField.q≠0 := (_root_.map_ne_zero _).mpr CrossedProductField.q_ne_zero

lemma baseVector_relation (W : Fin 4 → Field4) (i : Fin 4) :
    Rel θ rho (baseVector baseValue (coordinate 4) W i) (baseVector hypBase hypLambda W i) := by
  have hl : Rel θ rho (coordinate 4) hypLambda := coordinate_relation 4
  exact ((hl.neg.div θ_injective ((numeral_relation 3).mul (baseValue_relation CrossedProductField.p))
    (by exact mul_ne_zero (by norm_num) hypBase_p_ne_zero)).mul (baseValue_relation (W i)))

lemma lambdaVector_relation (W : Fin 4 → Field4) :
    Rel θ rho (lambdaVector baseValue (coordinate 4) W) (lambdaVector hypBase hypLambda W) := by
  have hl : Rel θ rho (coordinate 4) hypLambda := coordinate_relation 4
  have hp := baseValue_relation CrossedProductField.p
  have hq := baseValue_relation CrossedProductField.q
  have hs := baseValue_relation CrossedProductField.source
  have hP := baseValue_relation (directionalP W)
  have hQ := baseValue_relation (directionalQ W)
  apply ((((numeral_relation 3).mul hp).mul hs).add hP |>.add ((hl.pow 6).mul hQ)).div θ_injective
    ((((numeral_relation 18).mul hp).mul (hl.pow 4)).mul hq)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hypBase_p_ne_zero)
    (pow_ne_zero 4 hypLambda_ne_zero)) hypBase_q_ne_zero

lemma divergenceQuotient_relation (W : Fin 4 → Field4) :
    Rel θ rho (divergenceQuotient baseValue (coordinate 4) (coordinate 5) W)
      (divergenceQuotient hypBase hypLambda hypRadial W) := by
  have hl : Rel θ rho (coordinate 4) hypLambda := coordinate_relation 4
  have ht : Rel θ rho (coordinate 5) hypRadial := coordinate_relation 5
  have hp := baseValue_relation CrossedProductField.p
  have hq := baseValue_relation CrossedProductField.q
  have hs := baseValue_relation CrossedProductField.source
  have hP := baseValue_relation (directionalP W)
  apply ((((numeral_relation 3).mul hp).mul hs).add hP).neg.div θ_injective
    (((((numeral_relation 9).mul (hp.pow 2)).mul hq).mul (hl.pow 5)).mul (ht.pow 6))
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (pow_ne_zero 2 hypBase_p_ne_zero)) hypBase_q_ne_zero) (pow_ne_zero 5 hypLambda_ne_zero))
    (pow_ne_zero 6 hypRadial_ne_zero)

def transportedHyp (W : Fin 4 → Field4) : Fin 6 → N :=
  ![hypRadial*baseVector hypBase hypLambda W 0,hypRadial*baseVector hypBase hypLambda W 1,
    hypRadial*lambdaVector hypBase hypLambda W,0,
    hypRadial*(hypLambda*baseVector hypBase hypLambda W 2+hypCoordinate 2*lambdaVector hypBase hypLambda W),
    hypRadial*(hypLambda*baseVector hypBase hypLambda W 3+hypCoordinate 3*lambdaVector hypBase hypLambda W)]

lemma transportedVector_relation (W : Fin 4 → Field4) (i : Fin 6) :
    Rel θ rho (transportedVector W i) (transportedHyp W i) := by
  have ht : Rel θ rho (coordinate 5) hypRadial := coordinate_relation 5
  have hl : Rel θ rho (coordinate 4) hypLambda := coordinate_relation 4
  have hr : Rel θ rho (coordinate 2) (hypCoordinate 2) := coordinate_relation 2
  have hz : Rel θ rho (coordinate 3) (hypCoordinate 3) := coordinate_relation 3
  fin_cases i
  · exact ht.mul (baseVector_relation W 0)
  · exact ht.mul (baseVector_relation W 1)
  · exact ht.mul (lambdaVector_relation W)
  · exact zero θ rho
  · exact ht.mul ((hl.mul (baseVector_relation W 2)).add (hr.mul (lambdaVector_relation W)))
  · exact ht.mul ((hl.mul (baseVector_relation W 3)).add (hz.mul (lambdaVector_relation W)))

end CrossedPhysicalChart
end
end

/- Source component: CompatibleCertificateData. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CrossedCompatibleFractions
open MvPolynomial HoldoutConstruction
open scoped BigOperators
variable {C M N σ : Type*} [CommRing C] [IsDomain C] [Field M] [Field N] [Fintype σ]

/-- Clear rational normal data without introducing a hypersurface pole. -/
theorem normalized_data_of_compatible
    (θ : MvPolynomial σ C →+* M) (hθ : Function.Injective θ)
    (ρ : MvPolynomial σ C →+* N) (F A : MvPolynomial σ C)
    (hprime : Prime F) (hF : ρ F=0)
    (E : σ → Derivation ℤ M M)
    (hE : ∀ i p,E i (θ p)=θ (pderiv i p))
    (v : σ → M) (vbar : σ → N) (r : M) (rbar : N)
    (hv : ∀ i,Rel θ ρ (v i) (vbar i)) (hr : Rel θ ρ r rbar)
    (hnormal : (∑ i,v i*θ (pderiv i F))=θ A)
    (hdiv : (∑ i,E i (v i))=θ F*r) :
    ∃ D : MvPolynomial σ C,∃ W : σ → MvPolynomial σ C,∃ Q : MvPolynomial σ C,
      D≠0 ∧ IsRelPrime F D ∧ polynomialDirectional F W=A*D ∧ polynomialDivNum D W=F*Q := by
  classical
  obtain ⟨D,W,hd,hdr,hw⟩ := common_denominator θ ρ v vbar hv
  have hlegal : ¬ F∣D := by
    rintro ⟨k,hk⟩
    apply hdr
    rw [hk,map_mul,hF,zero_mul]
  have hn : polynomialDirectional F W=A*D := by
    apply hθ
    simp only [polynomialDirectional,map_sum,map_mul]
    simp_rw [hw]
    calc
      ∑ i,v i*θ D*θ (pderiv i F)=θ D*(∑ i,v i*θ (pderiv i F)) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      _=θ A*θ D := by rw [hnormal]; ring
  have hvrepr (i : σ) : v i=θ (W i)/θ D := by
    rw [hw]; field_simp
  have hder (i : σ) : E i (v i)=
      (θ (pderiv i (W i))*θ D-θ (W i)*θ (pderiv i D))/(θ D)^2 := by
    rw [hvrepr,Derivation.leibniz_div,hE,hE]
    simp only [smul_eq_mul,div_eq_mul_inv]
    ring
  have hnum : θ (polynomialDivNum D W)=(θ D)^2*(∑ i,E i (v i)) := by
    simp only [polynomialDivNum,polynomialDivergence,polynomialDirectional,map_sub,map_mul,map_sum]
    simp_rw [hder]
    conv_lhs => rw [Finset.mul_sum,← Finset.sum_sub_distrib]
    conv_rhs => rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp <;> ring
  obtain ⟨Q₀,E₀,he₀,her,hrrepr,hrbar⟩ := hr
  have hElegal : ¬F∣E₀ := by
    rintro ⟨k,hk⟩
    apply her
    rw [hk,map_mul,hF,zero_mul]
  have hcross : E₀*polynomialDivNum D W=F*(D^2*Q₀) := by
    apply hθ
    rw [map_mul,hnum,hdiv,hrrepr]
    simp only [map_mul,map_pow]
    field_simp
  have hFdvd : F∣polynomialDivNum D W := by
    have h : F∣E₀*polynomialDivNum D W := ⟨D^2*Q₀,hcross⟩
    exact (hprime.dvd_mul.mp h).resolve_left hElegal
  obtain ⟨Q,hQ⟩ := hFdvd
  refine ⟨D,W,Q,?_,hprime.irreducible.isRelPrime_iff_not_dvd.mpr hlegal,hn,hQ⟩
  intro h
  exact hdr (by rw [h,map_zero])

end CrossedCompatibleFractions
end
end

/- Source component: CrossedCertificate. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CrossedPhysicalChart
open HoldoutConstruction CrossedCompatibleFractions

/-- Legal normalized polynomial data for the exact fixed sextic and numerator. -/
theorem normalized_data : ∃ D : Poly,∃ W : Fin 6 → Poly,∃ Q : Poly,
    D≠0 ∧ IsRelPrime physicalF D ∧ polynomialDirectional physicalF W=physicalA*D ∧
      polynomialDivNum D W=physicalF*Q := by
  obtain ⟨W,hW⟩ := CrossedProductField.weighted_divergence
  exact normalized_data_of_compatible θ θ_injective rho physicalF physicalA
    physicalF_irreducible.prime rho_F physicalD physicalD_θ
    (transportedVector W) (transportedHyp W)
    (divergenceQuotient baseValue (coordinate 4) (coordinate 5) W)
    (divergenceQuotient hypBase hypLambda hypRadial W)
    (transportedVector_relation W) (divergenceQuotient_relation W)
    (transported_normal W) (transported_divergence W hW)

theorem physical_certificate : HodgeComputer.HasCertificate physicalF physicalA 1 := by
  obtain ⟨D,W,Q,hd,hlegal,hnormal,hdiv⟩ := normalized_data
  exact hasCertificate_of_normalized physicalF physicalA D W Q physicalF_homogeneous physicalA_homogeneous
    physicalF_irreducible.prime hlegal
    ((polynomialDirectional_eq_directional physicalF W).symm.trans hnormal)
    ((polynomialDivNum_eq_divergenceNumerator D W).symm.trans hdiv)
    3 physical_normal_legal

end CrossedPhysicalChart
end
end
