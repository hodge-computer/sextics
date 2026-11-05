import Proposal.PhysicalTransport
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
Homogeneous compatible fractions and legal strict certificate clearing for the
split-ternary-q2 chart. The compatibility argument adapts the accepted crossed
ternary construction of 1337isnot1337 (PR #149); homogeneous common-denominator
bookkeeping adapts the accepted holdout-q2 construction of HeadOfNaps (PR #124).
Prepared with OpenAI Codex assistance for contributor fqlx.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SplitCompatibleHomogeneous
open MvPolynomial
open scoped BigOperators
abbrev Poly := MvPolynomial (Fin 6) ℂ
variable {M N : Type*} [Field M] [Field N]

/-- Degree-zero common fraction, with a denominator legal in both evaluations. -/
def Rel (θ : Poly →+* M) (ρ : Poly →+* N) (f : M) (g : N) : Prop :=
  ∃ d : ℕ, ∃ A D : Poly, A.IsHomogeneous d ∧ D.IsHomogeneous d ∧
    θ D≠0 ∧ ρ D≠0 ∧ f=θ A/θ D ∧ g=ρ A/ρ D

lemma constant (θ : Poly →+* M) (ρ : Poly →+* N) (c : ℂ) :
    Rel θ ρ (θ (C c)) (ρ (C c)) :=
  ⟨0,C c,1,isHomogeneous_C _ c,isHomogeneous_one (Fin 6) ℂ,by simp,by simp,by simp,by simp⟩
lemma zero (θ : Poly →+* M) (ρ : Poly →+* N) : Rel θ ρ 0 0 := by
  simpa using constant θ ρ 0
lemma one (θ : Poly →+* M) (ρ : Poly →+* N) : Rel θ ρ 1 1 := by
  simpa using constant θ ρ 1
lemma numeral (θ : Poly →+* M) (ρ : Poly →+* N) (n : ℕ) : Rel θ ρ (n : M) (n : N) := by
  simpa only [map_natCast] using constant θ ρ (n : ℂ)

lemma ratio (θ : Poly →+* M) (ρ : Poly →+* N) (i j : Fin 6)
    (hθ : θ (X j)≠0) (hρ : ρ (X j)≠0) :
    Rel θ ρ (θ (X i)/θ (X j)) (ρ (X i)/ρ (X j)) :=
  ⟨1,X i,X j,isHomogeneous_X _ i,isHomogeneous_X _ j,hθ,hρ,rfl,rfl⟩

lemma Rel.add {θ : Poly →+* M} {ρ : Poly →+* N} {f h : M} {g k : N}
    (hf : Rel θ ρ f g) (hh : Rel θ ρ h k) : Rel θ ρ (f+h) (g+k) := by
  obtain ⟨d,A,D,hA,hD,hd,hr,rfl,rfl⟩ := hf
  obtain ⟨e,B,E,hB,hE,he,hs,rfl,rfl⟩ := hh
  refine ⟨d+e,A*E+B*D,D*E,(hA.mul hE).add (by simpa [Nat.add_comm] using hB.mul hD),
    hD.mul hE,by simpa using mul_ne_zero hd he,by simpa using mul_ne_zero hr hs,?_,?_⟩
  all_goals simp only [map_add,map_mul]; field_simp <;> ring
lemma Rel.neg {θ : Poly →+* M} {ρ : Poly →+* N} {f : M} {g : N}
    (hf : Rel θ ρ f g) : Rel θ ρ (-f) (-g) := by
  obtain ⟨d,A,D,hA,hD,hd,hr,rfl,rfl⟩ := hf
  exact ⟨d,-A,D,hA.neg,hD,hd,hr,by simp only [map_neg,neg_div],by simp only [map_neg,neg_div]⟩
lemma Rel.sub {θ : Poly →+* M} {ρ : Poly →+* N} {f h : M} {g k : N}
    (hf : Rel θ ρ f g) (hh : Rel θ ρ h k) : Rel θ ρ (f-h) (g-k) := by
  simpa only [sub_eq_add_neg] using hf.add hh.neg
lemma Rel.mul {θ : Poly →+* M} {ρ : Poly →+* N} {f h : M} {g k : N}
    (hf : Rel θ ρ f g) (hh : Rel θ ρ h k) : Rel θ ρ (f*h) (g*k) := by
  obtain ⟨d,A,D,hA,hD,hd,hr,rfl,rfl⟩ := hf
  obtain ⟨e,B,E,hB,hE,he,hs,rfl,rfl⟩ := hh
  refine ⟨d+e,A*B,D*E,hA.mul hB,hD.mul hE,
    by simpa using mul_ne_zero hd he,by simpa using mul_ne_zero hr hs,?_,?_⟩
  all_goals simp only [map_mul]; ring
lemma Rel.inv {θ : Poly →+* M} {ρ : Poly →+* N} {f : M} {g : N}
    (hθ : Function.Injective θ) (hf : Rel θ ρ f g) (hg : g≠0) : Rel θ ρ f⁻¹ g⁻¹ := by
  obtain ⟨d,A,D,hA,hD,hd,hr,rfl,rfl⟩ := hf
  have ha : ρ A≠0 := (div_ne_zero_iff.mp hg).1
  have ha0 : A≠0 := by intro h; exact ha (by rw [h,map_zero])
  have hθa : θ A≠0 := by simpa only [map_zero] using hθ.ne ha0
  exact ⟨d,D,A,hD,hA,hθa,ha,by rw [inv_div],by rw [inv_div]⟩
lemma Rel.div {θ : Poly →+* M} {ρ : Poly →+* N} {f h : M} {g k : N}
    (hθ : Function.Injective θ) (hf : Rel θ ρ f g) (hh : Rel θ ρ h k) (hk : k≠0) :
    Rel θ ρ (f/h) (g/k) := by
  simpa only [div_eq_mul_inv] using hf.mul (hh.inv hθ hk)
lemma Rel.pow {θ : Poly →+* M} {ρ : Poly →+* N} {f : M} {g : N}
    (hf : Rel θ ρ f g) (n : ℕ) : Rel θ ρ (f^n) (g^n) := by
  induction n with
  | zero => simpa using one θ ρ
  | succ n h => simpa only [pow_succ] using h.mul hf

lemma common_denominator {ι : Type*} [Fintype ι] (θ : Poly →+* M) (ρ : Poly →+* N)
    (f : ι → M) (g : ι → N) (h : ∀ i,Rel θ ρ (f i) (g i)) :
    ∃ d : ℕ, ∃ D : Poly, ∃ A : ι → Poly,
      D.IsHomogeneous d ∧ (∀ i,(A i).IsHomogeneous d) ∧ θ D≠0 ∧ ρ D≠0 ∧
      ∀ i,θ (A i)=f i*θ D := by
  classical
  choose d A D hA hD hd hr hf hg using h
  let e : ℕ := ∑ i,d i
  let E : Poly := ∏ i,D i
  let B : ι → Poly := fun i => A i*∏ j∈Finset.univ.erase i,D j
  have hE : θ E≠0 := by simpa [E] using Finset.prod_ne_zero_iff.mpr (fun i _ => hd i)
  have hEr : ρ E≠0 := by simpa [E] using Finset.prod_ne_zero_iff.mpr (fun i _ => hr i)
  refine ⟨e,E,B,IsHomogeneous.prod Finset.univ D d (fun i _ => hD i),?_,hE,hEr,?_⟩
  · intro i
    have hh := (hA i).mul (IsHomogeneous.prod (Finset.univ.erase i) D d (fun j _ => hD j))
    have he : e=d i+∑ j∈Finset.univ.erase i,d j :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
    simpa only [B,he] using hh
  · intro i
    have he : E=D i*∏ j∈Finset.univ.erase i,D j :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
    change θ (A i*(∏ j∈Finset.univ.erase i,D j))=f i*θ E
    rw [he,map_mul,map_mul,hf i]
    field_simp [hd i]

end SplitCompatibleHomogeneous

namespace SplitTernaryPhysical
open MvPolynomial Polynomial HoldoutConstruction
open scoped BigOperators

abbrev F4 := BaseField
def rootPolynomial : F4[X] := Polynomial.X^6+Polynomial.C (p/q)
abbrev RootField := rootPolynomial.SplittingField
abbrev HypField := RatFunc RootField

def rootInclusion : F4 →+* RootField := algebraMap F4 RootField
lemma rootPolynomial_degree : (rootPolynomial.map rootInclusion).degree≠0 := by
  change ((Polynomial.X^6+Polynomial.C (p/q)).map rootInclusion).degree≠0
  simp only [Polynomial.map_add,Polynomial.map_pow,Polynomial.map_X,Polynomial.map_C]
  rw [Polynomial.degree_X_pow_add_C (by decide : 0<6)]
  norm_num
lemma rootPolynomial_splits : (rootPolynomial.map rootInclusion).Splits := IsSplittingField.splits RootField rootPolynomial

def rootValue : RootField := Polynomial.rootOfSplits rootPolynomial_splits rootPolynomial_degree
lemma rootValue_equation : rootValue^6= -rootInclusion (p/q) := by
  have h := Polynomial.eval_rootOfSplits rootPolynomial_splits rootPolynomial_degree
  change (rootPolynomial.map rootInclusion).eval rootValue=0 at h
  change ((Polynomial.X^6+Polynomial.C (p/q)).map rootInclusion).eval rootValue=0 at h
  simpa only [Polynomial.map_add,Polynomial.map_pow,Polynomial.map_X,Polynomial.map_C,
    Polynomial.eval_add,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_C,add_eq_zero_iff_eq_neg] using h
lemma rootValue_ne_zero : rootValue≠0 := by
  intro h
  have he := rootValue_equation
  rw [h,zero_pow (by decide : (6 : ℕ)≠0)] at he
  have hn : rootInclusion (p/q)≠0 :=
    (_root_.map_ne_zero _).mpr (div_ne_zero p_ne_zero q_ne_zero)
  exact hn (neg_eq_zero.mp he.symm)

def hypBase : F4 →+* HypField := (RatFunc.C : RootField →+* HypField).comp rootInclusion
def hypCoordinate (i : Fin 4) : HypField := hypBase (algebraMap Base F4 (MvPolynomial.X i))
def hypLambda : HypField := RatFunc.C rootValue
def hypRadial : HypField := RatFunc.X
def hypConstant : ℂ →+* HypField := hypBase.comp ((algebraMap Base F4).comp MvPolynomial.C)
def chartHyp (i : Fin 5) : HypField := ![hypCoordinate 0,hypCoordinate 1,hypCoordinate 2,hypCoordinate 3,hypLambda] i

def rho : Poly →+* HypField := MvPolynomial.eval₂Hom hypConstant
  ![hypRadial*hypCoordinate 0,hypRadial*hypCoordinate 1,hypRadial,
    hypRadial*hypLambda*hypCoordinate 2,hypRadial*hypLambda*hypCoordinate 3,hypRadial*hypLambda]
lemma rho_C (c : ℂ) : rho (MvPolynomial.C c)=hypConstant c := MvPolynomial.eval₂Hom_C _ _ c
lemma rho_X (i : Fin 6) : rho (MvPolynomial.X i)=
    ![hypRadial*hypCoordinate 0,hypRadial*hypCoordinate 1,hypRadial,
      hypRadial*hypLambda*hypCoordinate 2,hypRadial*hypLambda*hypCoordinate 3,hypRadial*hypLambda] i := by
  rw [rho,MvPolynomial.eval₂Hom_X']
lemma hypRadial_ne_zero : hypRadial≠0 := by
  exact RatFunc.X_ne_zero
lemma hypLambda_ne_zero : hypLambda≠0 := (_root_.map_ne_zero _).mpr rootValue_ne_zero
lemma hypLambda_equation : hypLambda^6= -hypBase (p/q) := by
  have he := congrArg (RatFunc.C : RootField →+* HypField) rootValue_equation
  simpa only [hypLambda,hypBase,map_pow,map_neg,RingHom.comp_apply] using he
lemma hypBase_p : hypBase p=leftTernary (hypConstant (5/7 : ℂ)) (hypCoordinate 0) (hypCoordinate 1) 1 := by
  have hc : hypBase (algebraMap Base F4 (MvPolynomial.C (5/7 : ℂ)))=(5/7 : HypField) := by
    change hypConstant (5/7 : ℂ)=(5/7 : HypField)
    norm_num only [map_div₀,map_ofNat]
  simp [p,pPolynomial,leftTernary,hypCoordinate,hypConstant,map_ofNat,hc]
lemma hypBase_q : hypBase q=rightTernary (hypConstant (5/7 : ℂ)) (hypCoordinate 2) (hypCoordinate 3) 1 := by
  have hc : hypBase (algebraMap Base F4 (MvPolynomial.C (5/7 : ℂ)))=(5/7 : HypField) := by
    change hypConstant (5/7 : ℂ)=(5/7 : HypField)
    norm_num only [map_div₀,map_ofNat]
  simp [q,qPolynomial,rightTernary,hypCoordinate,hypConstant,map_ofNat,hc]
lemma rho_F : rho physicalF=0 := by
  have he : rho physicalF=hypRadial^6*(hypBase p+hypLambda^6*hypBase q) := by
    simp [physicalF,leftTernary,rightTernary,rho_X,rho_C,hypBase_p,hypBase_q,map_ofNat]
    ring
  rw [he,hypLambda_equation,map_div₀]
  have hq : hypBase q≠0 := (_root_.map_ne_zero _).mpr q_ne_zero
  field_simp
  ring

end SplitTernaryPhysical

namespace SplitTernaryPhysical
open MvPolynomial SplitCompatibleHomogeneous
open scoped BigOperators

lemma coordinate_homogeneous_relation (i : Fin 5) :
    Rel θ rho (coordinate i.castSucc) (chartHyp i) := by
  fin_cases i
  · have h := ratio θ rho 0 2 (by simp [θ_X,coordinate_ne_zero]) (by simp [rho_X,hypRadial_ne_zero])
    convert h using 1 <;> simp [θ_X,rho_X,chartHyp] <;>
      field_simp [coordinate_ne_zero 4,coordinate_ne_zero 5,hypRadial_ne_zero,hypLambda_ne_zero] <;> ring
  · have h := ratio θ rho 1 2 (by simp [θ_X,coordinate_ne_zero]) (by simp [rho_X,hypRadial_ne_zero])
    convert h using 1 <;> simp [θ_X,rho_X,chartHyp] <;>
      field_simp [coordinate_ne_zero 4,coordinate_ne_zero 5,hypRadial_ne_zero,hypLambda_ne_zero] <;> ring
  · have h := ratio θ rho 3 5 (by simp [θ_X,coordinate_ne_zero]) (by simp [rho_X,hypRadial_ne_zero,hypLambda_ne_zero])
    convert h using 1 <;> simp [θ_X,rho_X,chartHyp] <;>
      field_simp [coordinate_ne_zero 4,coordinate_ne_zero 5,hypRadial_ne_zero,hypLambda_ne_zero] <;> ring
  · have h := ratio θ rho 4 5 (by simp [θ_X,coordinate_ne_zero]) (by simp [rho_X,hypRadial_ne_zero,hypLambda_ne_zero])
    convert h using 1 <;> simp [θ_X,rho_X,chartHyp] <;>
      field_simp [coordinate_ne_zero 4,coordinate_ne_zero 5,hypRadial_ne_zero,hypLambda_ne_zero] <;> ring
  · have h := ratio θ rho 5 2 (by simp [θ_X,coordinate_ne_zero]) (by simp [rho_X,hypRadial_ne_zero])
    convert h using 1 <;> simp [θ_X,rho_X,chartHyp] <;>
      field_simp [coordinate_ne_zero 4,coordinate_ne_zero 5,hypRadial_ne_zero,hypLambda_ne_zero] <;> ring

lemma base_polynomial_homogeneous_relation (P : Base) :
    Rel θ rho (baseRingMap P) (hypBase (algebraMap Base F4 P)) := by
  have hX (i : Fin 4) : Rel θ rho (baseRingMap (X i)) (hypBase (algebraMap Base F4 (X i))) := by
    rw [baseRingMap_X]
    have hi : (i.castSucc.castSucc : Fin 6)=baseIndex i := by fin_cases i <;> rfl
    have hc : chartHyp i.castSucc=hypCoordinate i := by fin_cases i <;> rfl
    simpa only [hi,hc,hypCoordinate] using coordinate_homogeneous_relation i.castSucc
  induction P using MvPolynomial.induction_on with
  | C c =>
      rw [baseRingMap_C]
      simpa only [θ_C,rho_C,hypConstant,RingHom.comp_apply] using constant θ rho c
  | add P Q hP hQ => simpa only [map_add] using hP.add hQ
  | mul_X P i hP => simpa only [map_mul] using hP.mul (hX i)

lemma baseValue_homogeneous_relation (f : F4) : Rel θ rho (baseValue f) (hypBase f) := by
  obtain ⟨a,b,hb,rfl⟩ := IsFractionRing.div_surjective Base f
  rw [map_div₀,map_div₀,baseValue_polynomial,baseValue_polynomial]
  have hb0 : b≠0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbF : algebraMap Base F4 b≠0 := by simpa only [map_zero] using (IsFractionRing.injective Base F4).ne hb0
  exact (base_polynomial_homogeneous_relation a).div θ_injective (base_polynomial_homogeneous_relation b)
    ((_root_.map_ne_zero _).mpr hbF)

lemma hypBase_p_ne_zero : hypBase p≠0 := (_root_.map_ne_zero _).mpr p_ne_zero
lemma hypBase_q_ne_zero : hypBase q≠0 := (_root_.map_ne_zero _).mpr q_ne_zero

def hypBaseVelocity (W : Fin 4 → BaseField) (i : Fin 4) : HypField :=
  SplitTernaryHigherPole.baseCoefficient (hypBase p) (hypBase q) hypLambda*hypBase (W i)
def hypLambdaVelocity (W : Fin 4 → BaseField) : HypField :=
  SplitTernaryHigherPole.vertical (hypBase p) (hypBase q) hypLambda
    (hypBase source) (hypBase (directionalP W)) (hypBase (directionalQ W))

lemma baseVelocity_homogeneous_relation (W : Fin 4 → BaseField) (i : Fin 4) :
    Rel θ rho (baseVelocity W i) (hypBaseVelocity W i) := by
  have hl := coordinate_homogeneous_relation (4 : Fin 5)
  have hp := baseValue_homogeneous_relation p
  have hq := baseValue_homogeneous_relation q
  have hH := hp.add ((hl.pow 6).mul hq)
  exact (((hH.mul (hl.pow 5)).div θ_injective ((numeral θ rho 9).mul (hp.pow 2))
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 hypBase_p_ne_zero))).mul (baseValue_homogeneous_relation (W i)))

lemma lambdaVelocity_homogeneous_relation (W : Fin 4 → BaseField) :
    Rel θ rho (lambdaVelocity W) (hypLambdaVelocity W) := by
  have hl := coordinate_homogeneous_relation (4 : Fin 5)
  have hp := baseValue_homogeneous_relation p
  have hq := baseValue_homogeneous_relation q
  have hs := baseValue_homogeneous_relation source
  have hP := baseValue_homogeneous_relation (directionalP W)
  have hQ := baseValue_homogeneous_relation (directionalQ W)
  have hH := hp.add ((hl.pow 6).mul hq)
  have hfirst := (((hl.pow 6).neg.mul hs).div θ_injective ((numeral θ rho 12).mul hp)
    (mul_ne_zero (by norm_num) hypBase_p_ne_zero))
  have hsecond := ((((hl.pow 6).mul hs).mul hH).div θ_injective ((numeral θ rho 18).mul (hp.pow 2))
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 hypBase_p_ne_zero)))
  have hlast := (((hH.mul (hl.pow 6)).mul
    ((hP.div θ_injective hp hypBase_p_ne_zero).sub (hQ.div θ_injective hq hypBase_q_ne_zero))).div
      θ_injective ((numeral θ rho 54).mul (hp.pow 2))
        (mul_ne_zero (by norm_num) (pow_ne_zero 2 hypBase_p_ne_zero)))
  exact (hfirst.sub hsecond).add hlast

def degreeZeroVector (W : Fin 4 → BaseField) : Fin 6 → M :=
  ![baseVelocity W 0,baseVelocity W 1,0,
    coordinate 4*baseVelocity W 2+coordinate 2*lambdaVelocity W,
    coordinate 4*baseVelocity W 3+coordinate 3*lambdaVelocity W,lambdaVelocity W]
def degreeZeroHyp (W : Fin 4 → BaseField) : Fin 6 → HypField :=
  ![hypBaseVelocity W 0,hypBaseVelocity W 1,0,
    hypLambda*hypBaseVelocity W 2+hypCoordinate 2*hypLambdaVelocity W,
    hypLambda*hypBaseVelocity W 3+hypCoordinate 3*hypLambdaVelocity W,hypLambdaVelocity W]

lemma degreeZeroVector_relation (W : Fin 4 → BaseField) (i : Fin 6) :
    Rel θ rho (degreeZeroVector W i) (degreeZeroHyp W i) := by
  have hl := coordinate_homogeneous_relation (4 : Fin 5)
  have hr := coordinate_homogeneous_relation (2 : Fin 5)
  have hz := coordinate_homogeneous_relation (3 : Fin 5)
  fin_cases i
  · exact baseVelocity_homogeneous_relation W 0
  · exact baseVelocity_homogeneous_relation W 1
  · exact zero θ rho
  · exact (hl.mul (baseVelocity_homogeneous_relation W 2)).add (hr.mul (lambdaVelocity_homogeneous_relation W))
  · exact (hl.mul (baseVelocity_homogeneous_relation W 3)).add (hz.mul (lambdaVelocity_homogeneous_relation W))
  · exact lambdaVelocity_homogeneous_relation W

lemma transportedVector_degree (W : Fin 4 → BaseField) (i : Fin 6) :
    transportedVector W i=coordinate 5^7*degreeZeroVector W i := by
  fin_cases i <;> simp [transportedVector,physicalVector,degreeZeroVector] <;> ring

/-- Homogeneous data with a legal hypersurface denominator, for any W. -/
theorem homogeneous_vector_data (W : Fin 4 → BaseField) :
    ∃ d : ℕ, ∃ D : Poly, ∃ N : Fin 6 → Poly,
      D.IsHomogeneous d ∧ (∀ i,(N i).IsHomogeneous (d+7)) ∧ θ D≠0 ∧ rho D≠0 ∧
      ∀ i,θ (N i)=transportedVector W i*θ D := by
  obtain ⟨d,D,A,hD,hA,hd,hr,hrep⟩ := common_denominator θ rho
    (degreeZeroVector W) (degreeZeroHyp W) (degreeZeroVector_relation W)
  refine ⟨d,D,(fun i => X 2^7*A i),hD,?_,hd,hr,?_⟩
  · intro i
    simpa only [Nat.add_comm] using ((isHomogeneous_X ℂ (2 : Fin 6)).pow 7).mul (hA i)
  · intro i
    rw [map_mul,map_pow,hrep,transportedVector_degree]
    simp only [θ_X,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
    ring

end SplitTernaryPhysical

namespace SplitTernaryPhysical
open MvPolynomial HoldoutConstruction
open scoped BigOperators
local instance : Algebra ℤ M := Ring.toIntAlgebra _

lemma strict_polynomial_identity (W : Fin 4 → BaseField)
    (hw : (∑ i,baseD i (W i))-5*directionalP W/(3*p)-4*directionalQ W/(3*q)=source)
    (D : Poly) (N : Fin 6 → Poly) (hd : θ D≠0)
    (hrep : ∀ i,θ (N i)=transportedVector W i*θ D) :
    HodgeComputer.defect physicalF physicalA D 2 N=0 := by
  have hvrepr (i : Fin 6) : transportedVector W i=θ (N i)/θ D := by
    rw [hrep]
    field_simp
  have hder (i : Fin 6) : physicalD i (transportedVector W i)=
      (θ (pderiv i (N i))*θ D-θ (N i)*θ (pderiv i D))/(θ D)^2 := by
    rw [hvrepr,Derivation.leibniz_div,physicalD_θ,physicalD_θ]
    simp only [smul_eq_mul,div_eq_mul_inv]
    ring
  have hnum : θ (HodgeTestbed.divergenceNumerator D N)=
      (θ D)^2*(∑ i,physicalD i (transportedVector W i)) := by
    simp only [HodgeTestbed.divergenceNumerator,HodgeTestbed.divergence,
      HodgeTestbed.directional,map_sub,map_mul,map_sum]
    simp_rw [hder]
    conv_lhs => rw [Finset.mul_sum,← Finset.sum_sub_distrib]
    conv_rhs => rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp <;> ring
  have hdir : θ (HodgeTestbed.directional physicalF N)=
      θ D*(∑ i,transportedVector W i*physicalD i (θ physicalF)) := by
    simp only [HodgeTestbed.directional,map_sum,map_mul,physicalD_θ]
    simp_rw [hrep]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  apply θ_injective
  simp only [HodgeComputer.defect,map_add,map_sub,map_mul,map_pow,map_natCast,map_zero,hnum,hdir]
  have he := transported_strict_identity W hw
  linear_combination (θ D)^2*he

/-- The desired exact certificate follows once an actual weighted-divergence
primitive has been constructed. The explicit irreducibility argument is an
independent prerequisite for legality, not an existence assumption on W. -/
theorem hasCertificate_of_weighted_divergence
    (hirr : Irreducible physicalF) (W : Fin 4 → BaseField)
    (hw : (∑ i,baseD i (W i))-5*directionalP W/(3*p)-4*directionalQ W/(3*q)=source) :
    HodgeComputer.HasCertificate physicalF physicalA 2 := by
  obtain ⟨d,D,N,hD,hN,hd,hr,hrep⟩ := homogeneous_vector_data W
  have hlegal : ¬ physicalF∣D := by
    rintro ⟨k,hk⟩
    apply hr
    rw [hk,map_mul,rho_F,zero_mul]
  refine ⟨d,D,N,0,?_,hD,?_,hirr.isRelPrime_iff_not_dvd.mpr hlegal,?_⟩
  · intro h
    exact hd (by rw [h,map_zero])
  · intro i
    simpa using hN i
  · simp only [mul_zero]
    exact strict_polynomial_identity W hw D N hd hrep

end SplitTernaryPhysical

#print axioms SplitTernaryPhysical.hasCertificate_of_weighted_divergence

namespace SplitTernaryDomain
open Polynomial
abbrev Coeff := MvPolynomial (Fin 5) ℂ

def seedPolynomial : ℂ[X] := X^6+C (15/7)*X+1
lemma exists_simple_seed : ∃ a : ℂ,a^6+(15/7)*a+1=0 ∧ 6*a^5+(15/7)≠0 := by
  have hdeg : seedPolynomial.degree=6 := by unfold seedPolynomial; compute_degree!
  obtain ⟨a,ha⟩ := Complex.exists_root (by rw [hdeg]; decide)
  have he : a^6+(15/7)*a+1=0 := by
    simpa only [seedPolynomial,Polynomial.IsRoot,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_one] using ha
  refine ⟨a,he,?_⟩
  intro hd
  have hx : a=-(14/25 : ℂ) := by
    linear_combination (7/75 : ℂ)*(6*he-a*hd)
  rw [hx] at hd
  norm_num at hd

def lower : Polynomial Coeff :=
  C (3*MvPolynomial.C (5/7 : ℂ)*MvPolynomial.X 0)*X^5+
  C (MvPolynomial.C (5/7 : ℂ)*MvPolynomial.X 0^2*MvPolynomial.X 1^3+
    2*MvPolynomial.C (5/7 : ℂ)*MvPolynomial.X 1^5)*X+
  C (MvPolynomial.X 0^6+MvPolynomial.C (5/7 : ℂ)*MvPolynomial.X 0^5*MvPolynomial.X 1+
    MvPolynomial.X 1^6+SplitTernaryPhysical.rightTernary (MvPolynomial.C (5/7 : ℂ))
      (MvPolynomial.X 2) (MvPolynomial.X 3) (MvPolynomial.X 4))
def equation : Polynomial Coeff := X^6+lower
lemma equation_monic : equation.Monic := by
  apply monic_X_pow_add
  unfold lower
  compute_degree <;> norm_num

def specialization (a : ℂ) : Coeff →+* ℂ[X] :=
  MvPolynomial.eval₂Hom C ![0,0,0,1,X+C a]
def shiftedConstant (a : ℂ) : ℂ[X] := (X+C a)^6+C (15/7)*(X+C a)+1
lemma equation_specialization (a : ℂ) : equation.map (specialization a)=
    (X : (ℂ[X])[X])^6+C (shiftedConstant a) := by
  have hc : (15/7 : ℂ)=3*(5/7) := by norm_num
  simp [equation,lower,specialization,SplitTernaryPhysical.rightTernary,shiftedConstant,map_ofNat,hc]
  ring
lemma shifted_constant_zero (a : ℂ) (ha : a^6+(15/7)*a+1=0) :
    (shiftedConstant a).coeff 0=0 := by
  simpa [shiftedConstant,coeff_X_add_C_pow] using ha
lemma shifted_linear_nonzero (a : ℂ) (ha : 6*a^5+(15/7)≠0) :
    (shiftedConstant a).coeff 1≠0 := by
  have he : (shiftedConstant a).coeff 1=6*a^5+(15/7) := by
    norm_num [shiftedConstant,coeff_X_add_C_pow,Polynomial.coeff_one]
    <;> ring
  rwa [he]
lemma equation_irreducible : Irreducible equation := by
  obtain ⟨a,ha,hda⟩ := exists_simple_seed
  apply equation_monic.irreducible_of_irreducible_map (specialization a)
  rw [equation_specialization]
  exact HoldoutConstruction.irreducible_power_add_constant (shiftedConstant a)
    (shifted_constant_zero a ha) (shifted_linear_nonzero a hda) 6 (by decide)

end SplitTernaryDomain

namespace SplitTernaryPhysical
open MvPolynomial Polynomial

def normalPermutation : Equiv (Fin 6) (Fin 6) where
  toFun := ![1,2,0,3,4,5]
  invFun := ![2,0,1,3,4,5]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def normalEquiv := (MvPolynomial.renameEquiv ℂ normalPermutation).trans (MvPolynomial.finSuccEquiv ℂ 5)
lemma normal_equation : normalEquiv physicalF=SplitTernaryDomain.equation := by
  have hv : (Fin.cases (Polynomial.X : Polynomial SplitTernaryDomain.Coeff)
      (fun j => Polynomial.C (MvPolynomial.X j)))=
      ![Polynomial.X,Polynomial.C (MvPolynomial.X 0),Polynomial.C (MvPolynomial.X 1),
        Polynomial.C (MvPolynomial.X 2),Polynomial.C (MvPolynomial.X 3),Polynomial.C (MvPolynomial.X 4)] := by
    funext i; fin_cases i <;> rfl
  simp [normalEquiv,MvPolynomial.renameEquiv_apply,physicalF,leftTernary,rightTernary,normalPermutation,
    MvPolynomial.finSuccEquiv_apply,hv,SplitTernaryDomain.equation,SplitTernaryDomain.lower,map_ofNat]
  ring
lemma physicalF_irreducible : Irreducible physicalF := by
  apply (MulEquiv.irreducible_iff normalEquiv).mp
  rw [normal_equation]
  exact SplitTernaryDomain.equation_irreducible

/-- Only the explicit weighted-divergence primitive remains to be supplied. -/
theorem physical_certificate_of_weighted_divergence (W : Fin 4 → BaseField)
    (hw : (∑ i,baseD i (W i))-5*directionalP W/(3*p)-4*directionalQ W/(3*q)=source) :
    HodgeComputer.HasCertificate physicalF physicalA 2 :=
  hasCertificate_of_weighted_divergence physicalF_irreducible W hw

end SplitTernaryPhysical

#print axioms SplitTernaryPhysical.physicalF_irreducible
#print axioms SplitTernaryPhysical.physical_certificate_of_weighted_divergence
