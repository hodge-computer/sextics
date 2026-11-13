import Proposal.CyclicCubicKronecker
import HodgeComputer.Constructions.PolynomialEncoding.SignedExpressions

/-! A proved syntactic diagonal-weight checker for signed expressions.
Successful checking certifies both nonnegative parts of the expression.
Prepared with OpenAI Codex assistance. -/
namespace CycleCubicGradeCheck
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions CycleCubicKronecker MvPolynomial

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
end CycleCubicGradeCheck
#print axioms CycleCubicGradeCheck.grade_sound
