import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic
import HodgeComputer.Constructions.TransitiveCubic.SignedExpressions
import HodgeComputer.Constructions.TransitiveCubic.PolynomialDigitCheck

/-! Diagonal-weight encoding for the reverse edge xy², with congruences
modulo 3 reducing the required digit base. The established signed-expression
and bounded-digit theorems are imported unchanged. -/

/-! A small exact encoding for covariant coefficient identities.
At fixed cubic diagonal weight, the exponents of a,b,c are determined by
those of d,e,f. Weights below 38 bound the latter exponents by 18. The grade
congruences modulo 3 allow the smaller substitution a=b=c=1, d=X, e=X^7,
f=X^49: an equal code forces the highest exponent difference to be both a
multiple of 3 and between -2 and 2, hence zero, and similarly for the next
digit. This proves injectivity on each homogeneous component.
Prepared with OpenAI Codex assistance.
-/
noncomputable section
set_option maxRecDepth 4096
namespace PolarCubicKronecker
open MvPolynomial
open scoped BigOperators
abbrev Grade := ℕ × ℕ × ℕ
abbrev Exponent := Fin 6 →₀ ℕ
def weights : Fin 6 → Grade := ![(3,0,0),(0,3,0),(0,0,3),(2,1,0),(0,2,1),(1,2,0)]
def code (m : Exponent) : ℕ := m 3+7*m 4+49*m 5

lemma weight_formula (m : Exponent) :
    Finsupp.weight weights m=
      (3*m 0+2*m 3+m 5,3*m 1+m 3+2*m 4+2*m 5,3*m 2+m 4) := by
  rw [Finsupp.weight_apply,Finsupp.sum_fintype]
  · simp only [weights,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Fin.reduceSucc,Matrix.cons_val_one,Matrix.cons_val,Finset.univ_eq_empty,Finset.sum_empty,
      Prod.smul_mk,Prod.mk_add_mk,nsmul_eq_mul]
    ext <;> simp <;> ring
  · intro; simp

lemma digit_bound (a b c d e f u v w : ℕ)
    (h0 : 3*a+2*d+f=u) (h1 : 3*b+d+2*e+2*f=v) (h2 : 3*c+e=w)
    (hw : u<38 ∧ v<38 ∧ w<38) : d<19 ∧ e<19 ∧ f<19 := by omega

private theorem last_bound (d e f : Int)
    (hd : -18 ≤ d ∧ d ≤ 18) (he : -18 ≤ e ∧ e ≤ 18)
    (h : d+7*e+49*f=0) : -2 ≤ f ∧ f ≤ 2 := by omega

private theorem middle_bound (d e : Int)
    (hd : -18 ≤ d ∧ d ≤ 18) (h : d+7*e=0) : -2 ≤ e ∧ e ≤ 2 := by omega

private theorem small_multiple_three (d q : Int)
    (hd : -2 ≤ d ∧ d ≤ 2) (h : d=3*q) : d=0 := by omega

private theorem last_multiple (a c d e f : Int)
    (h0 : 3*a+2*d+f=0) (h2 : 3*c+e=0) (hcode : d+7*e+49*f=0) :
    f=3*(a+14*c-32*f) := by omega

private theorem base7_differences (a c d e f : Int)
    (h0 : 3*a+2*d+f=0) (h2 : 3*c+e=0)
    (hcode : d+7*e+49*f=0)
    (hd : -18 ≤ d ∧ d ≤ 18) (he : -18 ≤ e ∧ e ≤ 18) :
    d=0 ∧ e=0 ∧ f=0 := by
  have hf := small_multiple_three f (a+14*c-32*f)
    (last_bound d e f hd he hcode) (last_multiple a c d e f h0 h2 hcode)
  have hmid : d+7*e=0 := by
    clear h0 h2 hd he
    omega
  have hemul : e=3*(-c) := by
    clear h0 hcode hd he hf hmid
    omega
  have he0 := small_multiple_three e (-c) (middle_bound d e hd hmid) hemul
  have hd0 : d=0 := by
    clear h0 h2 hcode hd he hemul
    omega
  exact ⟨hd0,he0,hf⟩


theorem base7_grade_injective
    (a b c d e f a' b' c' d' e' f' u v w : Nat)
    (h0 : 3*a+2*d+f=u) (h1 : 3*b+d+2*e+2*f=v) (h2 : 3*c+e=w)
    (h0' : 3*a'+2*d'+f'=u) (h1' : 3*b'+d'+2*e'+2*f'=v)
    (h2' : 3*c'+e'=w)
    (hw : u<38 ∧ v<38 ∧ w<38)
    (hcode : d+7*e+49*f=d'+7*e'+49*f') :
    a=a' ∧ b=b' ∧ c=c' ∧ d=d' ∧ e=e' ∧ f=f' := by
  have hbound : d<19 ∧ e<19 ∧ d'<19 ∧ e'<19 := by
    clear hcode
    omega
  have h00 : 3*((a:Int)-a')+2*((d:Int)-d')+((f:Int)-f')=0 := by
    clear h1 h2 h1' h2' hw hcode hbound
    omega
  have h22 : 3*((c:Int)-c')+((e:Int)-e')=0 := by
    clear h0 h1 h0' h1' hw hcode hbound h00
    omega
  have hcc : ((d:Int)-d')+7*((e:Int)-e')+49*((f:Int)-f')=0 := by
    clear h0 h1 h2 h0' h1' h2' hw hbound h00 h22
    omega
  have hd : -18 ≤ (d:Int)-d' ∧ (d:Int)-d' ≤ 18 := by
    clear h0 h1 h2 h0' h1' h2' hw hcode h00 h22 hcc
    omega
  have he : -18 ≤ (e:Int)-e' ∧ (e:Int)-e' ≤ 18 := by
    clear h0 h1 h2 h0' h1' h2' hw hcode h00 h22 hcc hd
    omega
  have hz := base7_differences ((a:Int)-a') ((c:Int)-c') ((d:Int)-d')
    ((e:Int)-e') ((f:Int)-f') h00 h22 hcc hd he
  clear hcode hw hbound h00 h22 hcc hd he
  omega


lemma code_injective_on_grade (w : Grade) (hw : w.1<38 ∧ w.2.1<38 ∧ w.2.2<38) :
    Set.InjOn code {m : Exponent | Finsupp.weight weights m=w} := by
  intro m hm n hn he
  rw [Set.mem_setOf_eq,weight_formula] at hm hn
  have hm0 := congrArg Prod.fst hm
  have hm1 := congrArg (fun z : Grade => z.2.1) hm
  have hm2 := congrArg (fun z : Grade => z.2.2) hm
  have hn0 := congrArg Prod.fst hn
  have hn1 := congrArg (fun z : Grade => z.2.1) hn
  have hn2 := congrArg (fun z : Grade => z.2.2) hn
  dsimp only at hm0 hm1 hm2 hn0 hn1 hn2
  obtain ⟨he0,he1,he2,he3,he4,he5⟩ := base7_grade_injective
    (m 0) (m 1) (m 2) (m 3) (m 4) (m 5)
    (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) w.1 w.2.1 w.2.2
    hm0 hm1 hm2 hn0 hn1 hn2 hw he
  ext i
  fin_cases i <;> assumption

variable {R : Type*} [CommSemiring R]
def encode : MvPolynomial (Fin 6) R →+* Polynomial R :=
  MvPolynomial.eval₂Hom Polynomial.C
    ![1,1,1,Polynomial.X,Polynomial.X^7,Polynomial.X^49]

lemma encode_monomial (m : Exponent) (r : R) :
    encode (MvPolynomial.monomial m r)=Polynomial.monomial (code m) r := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  simp [encode,MvPolynomial.eval₂Hom_monomial,Finsupp.prod_fintype,
    Fin.prod_univ_succ,code,pow_add,pow_mul,mul_assoc,mul_comm,mul_left_comm]

lemma encode_finsupp (p : MvPolynomial (Fin 6) R) :
    (encode p).toFinsupp.coeff=Finsupp.mapDomain code (AddMonoidAlgebra.coeff p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial m r =>
    rw [encode_monomial]
    simp [Polynomial.toFinsupp_monomial,MvPolynomial.monomial,Finsupp.mapDomain_single]
  | add p q hp hq =>
    simp only [map_add,Polynomial.toFinsupp_add,AddMonoidAlgebra.coeff_add,
      Finsupp.mapDomain_add,hp,hq]

theorem encode_injective_on_grade (w : Grade) (hw : w.1<38 ∧ w.2.1<38 ∧ w.2.2<38)
    (p q : MvPolynomial (Fin 6) R)
    (hp : p.IsWeightedHomogeneous weights w) (hq : q.IsWeightedHomogeneous weights w)
    (he : encode p=encode q) : p=q := by
  classical
  let S : Set Exponent := {m | Finsupp.weight weights m=w}
  have hsP : (p.support : Set Exponent)⊆S := fun m hm => hp (mem_support_iff.mp hm)
  have hsQ : (q.support : Set Exponent)⊆S := fun m hm => hq (mem_support_iff.mp hm)
  have heF := congrArg (fun r : Polynomial R => r.toFinsupp.coeff) he
  rw [encode_finsupp,encode_finsupp] at heF
  ext m
  by_cases hm : m∈S
  · have h := congrArg (fun f : ℕ →₀ R => f (code m)) heF
    rw [Finsupp.mapDomain_apply' S (AddMonoidAlgebra.coeff p) hsP (code_injective_on_grade w hw) hm,
      Finsupp.mapDomain_apply' S (AddMonoidAlgebra.coeff q) hsQ (code_injective_on_grade w hw) hm] at h
    exact h
  · have hp0 : coeff m p=0 := by
      by_contra h; exact hm (hp h)
    have hq0 : coeff m q=0 := by
      by_contra h; exact hm (hq h)
    rw [hp0,hq0]

end PolarCubicKronecker

/-! A proved syntactic diagonal-weight checker for signed expressions.
Successful checking certifies both nonnegative parts of the expression.
Prepared with OpenAI Codex assistance. -/
namespace PolarCubicGradeCheck
open Lean.Grind.CommRing TransitiveSignedExpressions PolarCubicKronecker MvPolynomial

def gradeAdd : Option Grade → Option Grade → Option Grade
  | some a, some b => if a=b then some a else none
  | _, _ => none
def gradeMul : Option Grade → Option Grade → Option Grade
  | some a, some b => some (a+b)
  | _, _ => none
def grade : Expr → Option Grade
  | .num _ | .natCast _ | .intCast _ => some 0
  | .var i => if h : i<6 then some (weights ⟨i,h⟩) else none
  | .neg a => grade a
  | .add a b | .sub a b => gradeAdd (grade a) (grade b)
  | .mul a b => gradeMul (grade a) (grade b)
  | .pow a n => (grade a).map (n • ·)

noncomputable def polyVariable (i : ℕ) : MvPolynomial (Fin 6) ℕ :=
  if h : i<6 then X ⟨i,h⟩ else 0

def Homogeneous (p : MvPolynomial (Fin 6) ℕ × MvPolynomial (Fin 6) ℕ)
    (w : Grade) : Prop :=
  p.1.IsWeightedHomogeneous weights w ∧ p.2.IsWeightedHomogeneous weights w

lemma homogeneous_number (n : Int) : Homogeneous (numberPair n) 0 := by
  cases n with
  | ofNat n =>
    exact ⟨by simpa [numberPair] using isWeightedHomogeneous_C weights n,
      isWeightedHomogeneous_zero ℕ weights 0⟩
  | negSucc n =>
    exact ⟨isWeightedHomogeneous_zero ℕ weights 0,
      by simpa [numberPair] using isWeightedHomogeneous_C weights (n+1)⟩

lemma homogeneous_mul {p q : MvPolynomial (Fin 6) ℕ × MvPolynomial (Fin 6) ℕ}
    {u v : Grade} (hp : Homogeneous p u) (hq : Homogeneous q v) :
    Homogeneous (pairMul p q) (u+v) :=
  ⟨(hp.1.mul hq.1).add (hp.2.mul hq.2),
    (hp.1.mul hq.2).add (hp.2.mul hq.1)⟩

lemma homogeneous_pow {p : MvPolynomial (Fin 6) ℕ × MvPolynomial (Fin 6) ℕ}
    {u : Grade} (hp : Homogeneous p u) (n : ℕ) :
    Homogeneous (pairPow p n) (n • u) := by
  induction n with
  | zero =>
    simpa only [Homogeneous,pairPow,zero_nsmul] using
      And.intro (isWeightedHomogeneous_one ℕ weights) (isWeightedHomogeneous_zero ℕ weights 0)
  | succ n ih =>
    simpa only [pairPow,succ_nsmul',add_comm] using homogeneous_mul hp ih

theorem grade_sound (e : Expr) (w : Grade) (h : grade e=some w) :
    Homogeneous (splitEval polyVariable e) w := by
  induction e generalizing w with
  | num n => cases Option.some.inj h; exact homogeneous_number n
  | intCast n => cases Option.some.inj h; exact homogeneous_number n
  | natCast n =>
    cases Option.some.inj h
    exact ⟨by simpa [splitEval] using isWeightedHomogeneous_C weights n,
      isWeightedHomogeneous_zero ℕ weights 0⟩
  | var i =>
    simp only [grade] at h
    split_ifs at h with hi
    · cases Option.some.inj h
      exact ⟨by simpa [splitEval,polyVariable,hi] using
        isWeightedHomogeneous_X (R:=ℕ) weights (⟨i,hi⟩ : Fin 6),
        isWeightedHomogeneous_zero ℕ weights _⟩
  | neg a ih => exact ⟨(ih w h).2,(ih w h).1⟩
  | add a b ha hb =>
    cases hga : grade a with
    | none => simp [grade,gradeAdd,hga] at h
    | some ga =>
      cases hgb : grade b with
      | none => simp [grade,gradeAdd,hga,hgb] at h
      | some gb =>
        simp only [grade,hga,hgb,gradeAdd] at h
        split_ifs at h with he
        · subst gb
          have hw : ga=w := Option.some.inj h
          subst w
          exact ⟨((ha ga hga).1).add ((hb ga hgb).1),
            ((ha ga hga).2).add ((hb ga hgb).2)⟩
  | sub a b ha hb =>
    cases hga : grade a with
    | none => simp [grade,gradeAdd,hga] at h
    | some ga =>
      cases hgb : grade b with
      | none => simp [grade,gradeAdd,hga,hgb] at h
      | some gb =>
        simp only [grade,hga,hgb,gradeAdd] at h
        split_ifs at h with he
        · subst gb
          have hw : ga=w := Option.some.inj h
          subst w
          exact ⟨((ha ga hga).1).add ((hb ga hgb).2),
            ((ha ga hga).2).add ((hb ga hgb).1)⟩
  | mul a b ha hb =>
    cases hga : grade a with
    | none => simp [grade,gradeMul,hga] at h
    | some ga =>
      cases hgb : grade b with
      | none => simp [grade,gradeMul,hga,hgb] at h
      | some gb =>
        simp only [grade,hga,hgb,gradeMul] at h
        have hw : ga+gb=w := Option.some.inj h
        subst w
        exact homogeneous_mul (ha ga hga) (hb gb hgb)
  | pow a n ha =>
    cases hga : grade a with
    | none => simp [grade,hga] at h
    | some ga =>
      simp only [grade,hga,Option.map_some] at h
      have hw : n • ga=w := Option.some.inj h
      subst w
      exact homogeneous_pow (ha ga hga) n

lemma gradeAdd_valid {a b : Option Grade} (h : gradeAdd a b≠none) :
    a≠none ∧ b≠none := by
  cases a <;> cases b <;> simp_all [gradeAdd]
lemma gradeMul_valid {a b : Option Grade} (h : gradeMul a b≠none) :
    a≠none ∧ b≠none := by
  cases a <;> cases b <;> simp_all [gradeMul]

theorem ringEval_congr_of_grade {K : Type*} [CommRing K]
    (e : Expr) (v v' : ℕ → K) (hv : ∀ i, i<6 → v i=v' i)
    (h : grade e≠none) : ringEval v e=ringEval v' e := by
  induction e with
  | num n => rfl
  | natCast n => rfl
  | intCast n => rfl
  | var i =>
    by_cases hi : i<6
    · exact hv i hi
    · simp [grade,hi] at h
  | neg a ha => exact congrArg Neg.neg (ha h)
  | add a b ha hb =>
    obtain ⟨h₁,h₂⟩ := gradeAdd_valid h
    exact congrArg₂ HAdd.hAdd (ha h₁) (hb h₂)
  | sub a b ha hb =>
    obtain ⟨h₁,h₂⟩ := gradeAdd_valid h
    exact congrArg₂ HSub.hSub (ha h₁) (hb h₂)
  | mul a b ha hb =>
    obtain ⟨h₁,h₂⟩ := gradeMul_valid h
    exact congrArg₂ HMul.hMul (ha h₁) (hb h₂)
  | pow a n ha =>
    have h' : grade a≠none := by
      intro hz
      simp [grade,hz] at h
    exact congrArg (fun z : K => z^n) (ha h')
end PolarCubicGradeCheck

/-! A deterministic coefficient-identity certificate. The numerical equality
is used only after proving both the diagonal weight and a coefficient bound.
All proof obligations are ordinary kernel-checkable propositions.
Prepared with OpenAI Codex assistance. -/
noncomputable section
namespace PolarCubicEncodingCheck
open Lean.Grind.CommRing TransitiveSignedExpressions PolarCubicKronecker
open PolarCubicGradeCheck MvPolynomial

def value (b : ℕ) (i : ℕ) : ℕ :=
  if i<3 then 1 else if i=3 then b else if i=4 then b^7
    else if i=5 then b^49 else 0
def evaluation (b : ℕ) : MvPolynomial (Fin 6) ℕ →+* ℕ :=
  (Polynomial.evalRingHom b).comp encode

lemma evaluation_variable (b i : ℕ) : evaluation b (polyVariable i)=value b i := by
  by_cases hi : i<6
  · interval_cases i <;> simp [evaluation,polyVariable,value,encode]
  · have hi3 : ¬i<3 := by omega
    have h3 : i≠3 := by omega
    have h4 : i≠4 := by omega
    have h5 : i≠5 := by omega
    simp [polyVariable,hi,value,hi3,h3,h4,h5]

lemma evaluation_parts (b : ℕ) (e : Expr) :
    (evaluation b (splitEval polyVariable e).1,evaluation b (splitEval polyVariable e).2)=
      splitEval (value b) e := by
  simpa only [evaluation_variable] using splitEval_map (evaluation b) polyVariable e

lemma cast_parts (b : ℕ) (e : Expr) :
    ((splitEval (value b) e).1 : ℤ)-(splitEval (value b) e).2=
      ringEval (fun i => (value b i : ℤ)) e := by
  have h' := splitEval_map (Nat.castRingHom ℤ) (value b) e
  change (((splitEval (value b) e).1 : ℤ),((splitEval (value b) e).2 : ℤ))=
    splitEval (fun i => (value b i : ℤ)) e at h'
  have hd := splitEval_difference (fun i => (value b i : ℤ)) e
  rw [← h'] at hd
  exact hd

def positiveMass (e f : Expr) : ℕ :=
  (splitEval (value 1) e).1+(splitEval (value 1) f).2
def negativeMass (e f : Expr) : ℕ :=
  (splitEval (value 1) f).1+(splitEval (value 1) e).2

theorem encoded_identity (e f : Expr) (w : Grade) (b : ℕ)
    (hw : w.1<38 ∧ w.2.1<38 ∧ w.2.2<38) (hb : 0<b)
    (he : grade e=some w) (hf : grade f=some w)
    (hp : positiveMass e f<b) (hn : negativeMass e f<b)
    (hnum : ringEval (fun i => (value b i : ℤ)) e=
      ringEval (fun i => (value b i : ℤ)) f) :
    (splitEval polyVariable e).1+(splitEval polyVariable f).2=
      (splitEval polyVariable f).1+(splitEval polyVariable e).2 := by
  let p := (splitEval polyVariable e).1+(splitEval polyVariable f).2
  let q := (splitEval polyVariable f).1+(splitEval polyVariable e).2
  have hew := grade_sound e w he
  have hfw := grade_sound f w hf
  apply encode_injective_on_grade w hw p q (hew.1.add hfw.2) (hfw.1.add hew.2)
  apply TransitivePolynomialDigits.eval_injective_bounded b hb
  · change evaluation 1 p<b
    have he1 := congrArg Prod.fst (evaluation_parts 1 e)
    have hf2 := congrArg Prod.snd (evaluation_parts 1 f)
    dsimp only at he1 hf2
    simpa only [p,map_add,he1,hf2,positiveMass] using hp
  · change evaluation 1 q<b
    have hf1 := congrArg Prod.fst (evaluation_parts 1 f)
    have he2 := congrArg Prod.snd (evaluation_parts 1 e)
    dsimp only at hf1 he2
    simpa only [q,map_add,hf1,he2,negativeMass] using hn
  · change evaluation b p=evaluation b q
    have he1 := congrArg Prod.fst (evaluation_parts b e)
    have he2 := congrArg Prod.snd (evaluation_parts b e)
    have hf1 := congrArg Prod.fst (evaluation_parts b f)
    have hf2 := congrArg Prod.snd (evaluation_parts b f)
    dsimp only at he1 he2 hf1 hf2
    simp only [p,q,map_add,he1,he2,hf1,hf2]
    rw [← cast_parts,← cast_parts] at hnum
    omega

theorem identity_of_encoding {K : Type*} [CommRing K]
    (v : Fin 6 → K) (e f : Expr) (w : Grade) (b : ℕ)
    (hw : w.1<38 ∧ w.2.1<38 ∧ w.2.2<38) (hb : 0<b)
    (he : grade e=some w) (hf : grade f=some w)
    (hp : positiveMass e f<b) (hn : negativeMass e f<b)
    (hnum : ringEval (fun i => (value b i : ℤ)) e=
      ringEval (fun i => (value b i : ℤ)) f) :
    ringEval (fun i => if h : i<6 then v ⟨i,h⟩ else 0) e=
      ringEval (fun i => if h : i<6 then v ⟨i,h⟩ else 0) f := by
  let φ : MvPolynomial (Fin 6) ℕ →+* K := eval₂Hom (Nat.castRingHom K) v
  have hvar (i : ℕ) : φ (polyVariable i)=(if h : i<6 then v ⟨i,h⟩ else 0) := by
    by_cases hi : i<6 <;> simp [φ,polyVariable,hi]
  have h := congrArg φ (encoded_identity e f w b hw hb he hf hp hn hnum)
  rw [map_add,map_add] at h
  have he' := splitEval_map φ polyVariable e
  have hf' := splitEval_map φ polyVariable f
  have heDiff := splitEval_difference (fun i => φ (polyVariable i)) e
  have hfDiff := splitEval_difference (fun i => φ (polyVariable i)) f
  rw [← he'] at heDiff
  rw [← hf'] at hfDiff
  simp only [hvar] at heDiff hfDiff
  rw [← heDiff,← hfDiff]
  linear_combination h

theorem identity_of_encoding_context {K : Type*} [CommRing K]
    (v : ℕ → K) (e f : Expr) (w : Grade) (b : ℕ)
    (hw : w.1<38 ∧ w.2.1<38 ∧ w.2.2<38) (hb : 0<b)
    (he : grade e=some w) (hf : grade f=some w)
    (hp : positiveMass e f<b) (hn : negativeMass e f<b)
    (hnum : ringEval (fun i => (value b i : ℤ)) e=
      ringEval (fun i => (value b i : ℤ)) f) : ringEval v e=ringEval v f := by
  let v' : ℕ → K := fun i => if i<6 then v i else 0
  have hv (i : ℕ) (hi : i<6) : v i=v' i := by simp [v',hi]
  have he' : grade e≠none := by rw [he]; exact Option.some_ne_none w
  have hf' : grade f≠none := by rw [hf]; exact Option.some_ne_none w
  rw [ringEval_congr_of_grade e v v' hv he',ringEval_congr_of_grade f v v' hv hf']
  exact identity_of_encoding (fun i : Fin 6 => v i) e f w b hw hb he hf hp hn hnum
end PolarCubicEncodingCheck
