import Proposal.GaussianPolynomialTowers
import Proposal.ModularPolynomialBlocks
import Proposal.SegreIncidencePresentation

/-! # Evaluating modular linear functionals on sparse graded polynomials -/

set_option Elab.async false

/- Component: continuation_3/BinaryNaturalPower.lean -/
section
/-! A structurally recursive binary powering function, with a proof that it
agrees with ordinary natural powers for every fuel and exponent. -/
namespace CycleQ2BinaryNaturalPower

def power (b : ℕ) : ℕ → ℕ → ℕ
  | 0, k => b^k
  | f+1, k =>
    let a := power b f (k/2)
    if k%2=0 then a*a else b*(a*a)

theorem power_eq (b f k : ℕ) : power b f k=b^k := by
  induction f generalizing k with
  | zero => rfl
  | succ f ih =>
    simp only [power,ih]
    have hk := Nat.mod_add_div k 2
    have hb : k%2<2 := Nat.mod_lt _ (by decide)
    split_ifs with h
    · calc
        b^(k/2)*b^(k/2)=b^((k/2)*2) := by rw [pow_mul,pow_two]
        _=b^k := by congr 1; omega
    · calc
        b*(b^(k/2)*b^(k/2))=b^((k/2)*2+1) := by rw [pow_succ,pow_mul,pow_two]; ring
        _=b^k := by congr 1; omega
end CycleQ2BinaryNaturalPower
#print axioms CycleQ2BinaryNaturalPower.power_eq
end

/- Component: continuation_3/NaturalPolynomialDigits.lean -/
section
/-! Exact extraction of polynomial coefficients from a natural base evaluation.
The coefficient bound rules out carries. -/

namespace CycleQ2NaturalPolynomialDigits
open Polynomial

theorem eval_split (B : ℕ) (p : ℕ[X]) :
    p.eval B=p.coeff 0+B*p.divX.eval B := by
  have h := congrArg (Polynomial.eval B) (divX_mul_X_add p)
  simpa only [eval_add,eval_mul,eval_X,eval_C,Nat.mul_comm,Nat.add_comm] using h.symm

theorem div_eval (B : ℕ) (hB : 0<B) (p : ℕ[X]) (h0 : p.coeff 0<B) :
    p.eval B/B=p.divX.eval B := by
  rw [eval_split,Nat.add_mul_div_left _ _ hB,Nat.div_eq_of_lt h0,zero_add]

theorem coefficient (B : ℕ) (hB : 0<B) (p : ℕ[X])
    (hc : ∀ n,p.coeff n<B) (k : ℕ) :
    p.coeff k=(p.eval B/B^k)%B := by
  induction k generalizing p with
  | zero =>
    rw [Nat.pow_zero,Nat.div_one,eval_split]
    simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (hc 0)]
  | succ k ih =>
    have h := ih p.divX (fun n => by simpa only [coeff_divX] using hc (n+1))
    rw [coeff_divX,←div_eval B hB p (hc 0)] at h
    simpa only [Nat.div_div_eq_div_mul,Nat.pow_succ,Nat.mul_comm] using h

end CycleQ2NaturalPolynomialDigits

#print axioms CycleQ2NaturalPolynomialDigits.coefficient
end

/- Component: continuation_3/SparseModularFunctionalCore.lean -/
section
/-! Executable coefficient functionals. Each natural number stores8-bit
coefficient slots; its lookup defines the functional without any data invariant. -/
namespace CycleQ2SparseModularFunctional
open CycleQ2SparseGaussianPolynomial

abbrev WeightData := Fin 3 → Fin 3 → ℕ → ℕ → ℕ

def slot (n k : ℕ) : ℕ :=
  if n=0 then 0 else (n / CycleQ2BinaryNaturalPower.power 256 10 k) % 256

theorem slot_eq (n k : ℕ) : slot n k=(n / 256^k)%256 := by
  unfold slot
  rw [CycleQ2BinaryNaturalPower.power_eq]
  split_ifs with h
  · subst n; simp
  · rfl

def weight (W : WeightData) (i j : Fin 3) (e : Exponent) : ℕ :=
  slot (W i j e.2.2.2.2 e.1) (e.2.1+29*e.2.2.1)

def gmod (z : GaussianInt) : ℕ := ((z.re+33*z.im)%109).toNat

def dot (W : WeightData) (i j : Fin 3) (s : Exponent) : Sparse → ℕ
  | [] => 0
  | t::p =>
    let c := weight W i j (exponentAdd s t.1)
    if c=0 then dot W i j s p else (gmod t.2*c+dot W i j s p)%109

def shiftData (e : Exponent) (p : Sparse) : Sparse :=
  p.map (fun a => (exponentAdd e a.1,a.2))
def flattenLayersData : Layers → Sparse
  | [] => []
  | a::p => a ++ shiftData (0,1,0,0,0) (flattenLayersData p)
def flattenBlocksData : Blocks → Sparse
  | [] => []
  | a::p => flattenLayersData a ++ shiftData (1,0,0,0,0) (flattenBlocksData p)
def flattenTowersData : Towers → Sparse
  | [] => []
  | a::p => flattenBlocksData a ++ shiftData (0,0,0,0,1) (flattenTowersData p)

end CycleQ2SparseModularFunctional
end

/- Component: continuation_3/SparseGaussianGrading.lean -/
section
/-! The concrete sparse witnesses are standard homogeneous chart polynomials. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SparseGaussianPolynomial

open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations

def shift (e : Exponent) (p : Sparse) : Sparse :=
  p.map (fun a => (exponentAdd e a.1, a.2))

def flattenLayers : Layers → Sparse
  | [] => []
  | a::p => a ++ shift (0,1,0,0,0) (flattenLayers p)

def flattenBlocks : Blocks → Sparse
  | [] => []
  | a::p => flattenLayers a ++ shift (1,0,0,0,0) (flattenBlocks p)

def flattenTowers : Towers → Sparse
  | [] => []
  | a::p => flattenBlocks a ++ shift (0,0,0,0,1) (flattenTowers p)

def tupleFun (e : Exponent) : Fin 5 → ℕ := ![e.1, e.2.1, e.2.2.1, e.2.2.2.1, e.2.2.2.2]

def goodTerm (d : ℕ) (a : Term) : Bool :=
  decide (fullDegree (tupleFun a.1) = d ∧ fullCharacter (tupleFun a.1) = 0 ∧
    a.1.1 < 3 ∧ a.1.2.2.2.2 < 3)

def goodPolynomial (d : ℕ) (p : Sparse) : Bool := p.all (goodTerm d)
def goodTowers (d : ℕ) (p : Towers) : Bool := goodPolynomial d (flattenTowers p)

noncomputable section
variable {R : Type*} [CommRing R]
variable (φ : GaussianInt →+* R)

theorem termValue_shift (x : Fin 5 → R) (e : Exponent) (a : Term) :
    termValue φ x (exponentAdd e a.1, a.2) = monomial x e * termValue φ x a := by
  simp only [termValue, monomial_exponentAdd]
  ring

theorem eval_shift (x : Fin 5 → R) (e : Exponent) (p : Sparse) :
    eval φ x (shift e p) = monomial x e * eval φ x p := by
  simp only [eval, shift, List.map_map, Function.comp_def, termValue_shift,
    List.sum_map_mul_left]

theorem eval_flattenLayers (x : Fin 5 → R) (p : Layers) :
    eval φ x (flattenLayers p) = evalLayers φ x (x 1) p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [flattenLayers, eval_append, eval_shift, ih, evalLayers]
    simp [monomial]

theorem eval_flattenBlocks (x : Fin 5 → R) (p : Blocks) :
    eval φ x (flattenBlocks p) = evalBlocks φ x (x 0) (x 1) p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [flattenBlocks, eval_append, eval_shift, eval_flattenLayers, ih, evalBlocks]
    simp [monomial]

theorem eval_flattenTowers (x : Fin 5 → R) (p : Towers) :
    eval φ x (flattenTowers p) = evalTowers φ x (x 4) (x 0) (x 1) p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [flattenTowers, eval_append, eval_shift, eval_flattenBlocks, ih, evalTowers]
    simp [monomial]

def tupleExponent (e : Exponent) : Fin 5 →₀ ℕ := Finsupp.equivFunOnFinite.symm (tupleFun e)

@[simp] theorem tupleExponent_apply (e : Exponent) (i : Fin 5) :
    tupleExponent e i = tupleFun e i := rfl

theorem monomial_variables (e : Exponent) :
    monomial (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R) e =
      MvPolynomial.monomial (tupleExponent e) 1 := by
  simp only [monomial, MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, one_mul]
  apply congrArg (fun d : Fin 5 →₀ ℕ => MvPolynomial.monomial d (1 : R))
  ext i
  fin_cases i <;>
    simp [tupleExponent, tupleFun, Finsupp.single_apply, Fin.ext_iff]

theorem termValue_variables (a : Term) :
    termValue (MvPolynomial.C.comp φ) (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R) a =
      MvPolynomial.monomial (tupleExponent a.1) (φ a.2) := by
  rw [termValue, monomial_variables]
  simp only [RingHom.comp_apply, MvPolynomial.C_mul_monomial, mul_one]

theorem goodTerm_evaluation (d : ℕ) (a : Term) (h : goodTerm d a = true) :
    FullStandard (termValue (MvPolynomial.C.comp φ) (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R) a) ∧
      HG (termValue (MvPolynomial.C.comp φ) (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R) a) (d,0) := by
  have ha : fullDegree (tupleFun a.1) = d ∧ fullCharacter (tupleFun a.1) = 0 ∧
      a.1.1 < 3 ∧ a.1.2.2.2.2 < 3 := of_decide_eq_true h
  rw [termValue_variables]
  constructor
  · intro e he
    have heq : e = tupleExponent a.1 :=
      Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset he)
    subst e
    change a.1.1 < 3 ∧ a.1.2.2.2.2 < 3
    exact ha.2.2
  · apply MvPolynomial.isWeightedHomogeneous_monomial
    apply (fullGrading_eq_iff _ _).mpr
    exact ⟨ha.1, ha.2.1⟩

theorem goodPolynomial_evaluation (d : ℕ) (p : Sparse) (h : goodPolynomial d p = true) :
    FullStandard (eval (MvPolynomial.C.comp φ) (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R) p) ∧
      HG (eval (MvPolynomial.C.comp φ) (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R) p) (d,0) := by
  induction p with
  | nil =>
    constructor
    · simp [FullStandard]
    · exact (MvPolynomial.weightedHomogeneousSubmodule R fullGrading (d,0)).zero_mem
  | cons a p ih =>
    simp only [goodPolynomial, List.all_cons, Bool.and_eq_true] at h
    have ha := goodTerm_evaluation (R := R) φ d a h.1
    have hp := ih h.2
    rw [eval_cons]
    exact ⟨CycleQ2IncidenceJacobian.fullStandard_add ha.1 hp.1, ha.2.add hp.2⟩

/-- Degree, invariant character, and standardness of the literal three-level data. -/
theorem goodTowers_evaluation (d : ℕ) (p : Towers) (h : goodTowers d p = true) :
    FullStandard (evalTowers (MvPolynomial.C.comp φ)
      (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R)
      (MvPolynomial.X 4) (MvPolynomial.X 0) (MvPolynomial.X 1) p) ∧
    HG (evalTowers (MvPolynomial.C.comp φ)
      (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R)
      (MvPolynomial.X 4) (MvPolynomial.X 0) (MvPolynomial.X 1) p) (d,0) := by
  rw [← eval_flattenTowers]
  exact goodPolynomial_evaluation φ d (flattenTowers p) h

end
end CycleQ2SparseGaussianPolynomial

#print axioms CycleQ2SparseGaussianPolynomial.goodTowers_evaluation
end

/- Component: continuation_3/SparseModularFastDot.lean -/
section
/-! A compact, proved encoding for coefficient-functional evaluation.
The coefficient is reduced once when a table is encoded; subsequent shifts
only add to its one-dimensional coefficient index. -/

namespace CycleQ2SparseModularFastDot
open CycleQ2SparseModularFunctional CycleQ2SparseGaussianPolynomial

abbrev FastTerm := ℕ × ℕ × ℕ × ℕ

def encodeTerm (t : Term) : FastTerm :=
  (t.1.2.2.2.2,t.1.1,t.1.2.1+29*t.1.2.2.1,gmod t.2)

def encode (p : Sparse) : List FastTerm := p.map encodeTerm

def fastDot (W : WeightData) (i j : Fin 3) (s : ℕ) : List FastTerm → ℕ
  | [] => 0
  | t::p =>
    let c := slot (W i j t.1 t.2.1) (s+t.2.2.1)
    if c=0 then fastDot W i j s p else (t.2.2.2*c+fastDot W i j s p)%109

theorem fastDot_encode (W : WeightData) (i j : Fin 3) (u v c : ℕ) (p : Sparse) :
    fastDot W i j (u+29*v) (encode p)=dot W i j (0,u,v,c,0) p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    have h : (u+29*v)+(t.1.2.1+29*t.1.2.2.1)=
        (u+t.1.2.1)+29*(v+t.1.2.2.1) := by omega
    simp only [encode,List.map_cons,fastDot,encodeTerm,dot,weight,exponentAdd,
      zero_add,h] at ⊢
    change (if slot (W i j t.1.2.2.2.2 t.1.1)
        (u+t.1.2.1+29*(v+t.1.2.2.1))=0 then
          fastDot W i j (u+29*v) (encode p)
        else (gmod t.2 * slot (W i j t.1.2.2.2.2 t.1.1)
          (u+t.1.2.1+29*(v+t.1.2.2.1))+fastDot W i j (u+29*v) (encode p))%109)=_
    rw [ih]

abbrev WordTerm := ℕ × ℕ
abbrev FastBlock := ℕ × ℕ × List WordTerm

def dotWord (n s tail : ℕ) : List WordTerm → ℕ
  | [] => tail
  | t::p =>
    let c := slot n (s+t.1)
    if c=0 then dotWord n s tail p else (t.2*c+dotWord n s tail p)%109

def groupedDot (W : WeightData) (i j : Fin 3) (s : ℕ) : List FastBlock → ℕ
  | [] => 0
  | b::bs =>
    let n := W i j b.1 b.2.1
    if n=0 then groupedDot W i j s bs
    else dotWord n s (groupedDot W i j s bs) b.2.2

def flattenBlock (b : FastBlock) : List FastTerm :=
  b.2.2.map (fun t => (b.1,b.2.1,t.1,t.2))

def flattenGrouped (bs : List FastBlock) : List FastTerm := bs.flatMap flattenBlock

theorem dotWord_zero (s tail : ℕ) (p : List WordTerm) : dotWord 0 s tail p=tail := by
  induction p with
  | nil => rfl
  | cons t p ih => simp [dotWord,slot,ih]

theorem fastDot_block_append (W : WeightData) (i j : Fin 3) (s w z : ℕ)
    (p : List WordTerm) (q : List FastTerm) :
    fastDot W i j s (flattenBlock (w,z,p)++q)=
      dotWord (W i j w z) s (fastDot W i j s q) p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    simp only [flattenBlock,List.map_cons,List.cons_append,fastDot,dotWord] at ⊢
    change (if slot (W i j w z) (s+t.1)=0 then
      fastDot W i j s (flattenBlock (w,z,p)++q) else
      (t.2*slot (W i j w z) (s+t.1)+fastDot W i j s (flattenBlock (w,z,p)++q))%109)=_
    rw [ih]

theorem groupedDot_eq (W : WeightData) (i j : Fin 3) (s : ℕ) (bs : List FastBlock) :
    groupedDot W i j s bs=fastDot W i j s (flattenGrouped bs) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rcases b with ⟨w,z,p⟩
    simp only [groupedDot,flattenGrouped,List.flatMap_cons]
    rw [fastDot_block_append]
    change _ = dotWord (W i j w z) s (fastDot W i j s (flattenGrouped bs)) p
    rw [←ih]
    split_ifs with h
    · rw [h,dotWord_zero]
    · rfl

end CycleQ2SparseModularFastDot

#print axioms CycleQ2SparseModularFastDot.fastDot_encode
end

/- Component: continuation_3/SparseModularGrading.lean -/
section
/-! The concrete sparse witnesses are standard homogeneous chart polynomials. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SparseModularPolynomial

open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations

def shift (e : Exponent) (p : Sparse) : Sparse :=
  p.map (fun a => (exponentAdd e a.1, a.2))

def flattenLayers : Layers → Sparse
  | [] => []
  | a::p => a ++ shift (0,0,0,0,1) (flattenLayers p)

def flattenBlocks : Blocks → Sparse
  | [] => []
  | a::p => flattenLayers a ++ shift (1,0,0,0,0) (flattenBlocks p)

def tupleFun (e : Exponent) : Fin 5 → ℕ := ![e.1, e.2.1, e.2.2.1, e.2.2.2.1, e.2.2.2.2]

def goodTerm (d : ℕ) (a : Term) : Bool :=
  decide (fullDegree (tupleFun a.1) = d ∧ fullCharacter (tupleFun a.1) = 0 ∧
    a.1.1 < 3 ∧ a.1.2.2.2.2 < 3)

def goodPolynomial (d : ℕ) (p : Sparse) : Bool := p.all (goodTerm d)
def goodBlocks (d : ℕ) (p : Blocks) : Bool := goodPolynomial d (flattenBlocks p)

noncomputable section
variable {R : Type*} [CommRing R] [CharP R 109]

theorem termValue_shift (x : Fin 5 → R) (e : Exponent) (a : Term) :
    termValue x (exponentAdd e a.1, a.2) = monomial x e * termValue x a := by
  simp only [termValue, monomial_exponentAdd]
  ring

theorem eval_shift (x : Fin 5 → R) (e : Exponent) (p : Sparse) :
    eval x (shift e p) = monomial x e * eval x p := by
  simp only [eval, shift, List.map_map, Function.comp_def, termValue_shift,
    List.sum_map_mul_left]

theorem eval_flattenLayers (x : Fin 5 → R) (p : Layers) :
    eval x (flattenLayers p) = evalLayers x (x 4) p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [flattenLayers, eval_append, eval_shift, ih, evalLayers]
    simp [monomial]

theorem eval_flattenBlocks (x : Fin 5 → R) (p : Blocks) :
    eval x (flattenBlocks p) = evalBlocks x (x 0) (x 4) p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [flattenBlocks, eval_append, eval_shift, eval_flattenLayers, ih, evalBlocks]
    simp [monomial]

def tupleExponent (e : Exponent) : Fin 5 →₀ ℕ := Finsupp.equivFunOnFinite.symm (tupleFun e)

@[simp] theorem tupleExponent_apply (e : Exponent) (i : Fin 5) :
    tupleExponent e i = tupleFun e i := rfl

theorem monomial_variables (e : Exponent) :
    monomial (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R) e =
      MvPolynomial.monomial (tupleExponent e) 1 := by
  simp only [monomial, MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, one_mul]
  apply congrArg (fun d : Fin 5 →₀ ℕ => MvPolynomial.monomial d (1 : R))
  ext i
  fin_cases i <;>
    simp [tupleExponent, tupleFun, Finsupp.single_apply, Fin.ext_iff]

theorem termValue_variables (a : Term) :
    termValue (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R) a =
      MvPolynomial.monomial (tupleExponent a.1) (a.2 : R) := by
  rw [termValue, monomial_variables]
  rw [← map_natCast (MvPolynomial.C : R →+* MvPolynomial (Fin 5) R) a.2,
    MvPolynomial.C_mul_monomial, mul_one]

theorem goodTerm_evaluation (d : ℕ) (a : Term) (h : goodTerm d a = true) :
    FullStandard (termValue (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R) a) ∧
      HG (termValue (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R) a) (d,0) := by
  have ha : fullDegree (tupleFun a.1) = d ∧ fullCharacter (tupleFun a.1) = 0 ∧
      a.1.1 < 3 ∧ a.1.2.2.2.2 < 3 := of_decide_eq_true h
  rw [termValue_variables]
  constructor
  · intro e he
    have heq : e = tupleExponent a.1 :=
      Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset he)
    subst e
    change a.1.1 < 3 ∧ a.1.2.2.2.2 < 3
    exact ha.2.2
  · apply MvPolynomial.isWeightedHomogeneous_monomial
    apply (fullGrading_eq_iff _ _).mpr
    exact ⟨ha.1, ha.2.1⟩

theorem goodPolynomial_evaluation (d : ℕ) (p : Sparse) (h : goodPolynomial d p = true) :
    FullStandard (eval (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R) p) ∧
      HG (eval (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R) p) (d,0) := by
  induction p with
  | nil =>
    constructor
    · simp [FullStandard]
    · exact (MvPolynomial.weightedHomogeneousSubmodule R fullGrading (d,0)).zero_mem
  | cons a p ih =>
    simp only [goodPolynomial, List.all_cons, Bool.and_eq_true] at h
    have ha := goodTerm_evaluation (R := R) d a h.1
    have hp := ih h.2
    rw [eval_cons]
    exact ⟨CycleQ2IncidenceJacobian.fullStandard_add ha.1 hp.1, ha.2.add hp.2⟩

/-- This checks both the invariant weighted degree and the two standard-monomial
bounds of the literal chart, directly from the numerical witness coefficients. -/
theorem goodBlocks_evaluation (d : ℕ) (p : Blocks) (h : goodBlocks d p = true) :
    FullStandard (evalBlocks (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R)
      (MvPolynomial.X 0) (MvPolynomial.X 4) p) ∧
    HG (evalBlocks (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R)
      (MvPolynomial.X 0) (MvPolynomial.X 4) p) (d,0) := by
  rw [← eval_flattenBlocks]
  exact goodPolynomial_evaluation d (flattenBlocks p) h

end
end CycleQ2SparseModularPolynomial

#print axioms CycleQ2SparseModularPolynomial.goodBlocks_evaluation
end
