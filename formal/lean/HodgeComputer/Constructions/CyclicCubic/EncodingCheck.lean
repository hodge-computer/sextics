import HodgeComputer.Constructions.CyclicCubic.GradeCheck
import HodgeComputer.Constructions.CyclicCubic.PolynomialDigitCheck

/-! A deterministic coefficient-identity certificate. The numerical equality
is used only after proving both the diagonal weight and a coefficient bound.
All proof obligations are ordinary kernel-checkable propositions.
Prepared with OpenAI Codex assistance. -/
noncomputable section
namespace CycleCubicEncodingCheck
open Lean.Grind.CommRing CycleSignedExpressions CycleCubicKronecker
open CycleCubicGradeCheck MvPolynomial

def value (b : ℕ) (i : ℕ) : ℕ :=
  if i<3 then 1 else if i=3 then b else if i=4 then b^19
    else if i=5 then b^361 else 0
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
  apply CyclePolynomialDigits.eval_injective_bounded b hb
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
end CycleCubicEncodingCheck
#print axioms CycleCubicEncodingCheck.identity_of_encoding
