import HodgeComputer.Constructions.PolynomialEncoding.SignedExpressions
import HodgeComputer.Constructions.PolynomialEncoding.PolynomialDigitCheck
import HodgeComputer.Constructions.PolynomialEncoding.BivariateExpressions
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Fin

/-! Generic multi-variable Kronecker positional-encoding and factored Kronecker × grid
polynomial identity checkers:
1. Mixed-radix monomial encoding into `ℕ[X]` with `PolynomialDigits.eval_injective_bounded`,
   supporting arbitrary arity (`identity_of_kronecker`), 2/3-variable specializations, and
   sparse bivariate equality (`biv_denote_eq_of_kronecker3`).
2. Polymorphic ring-backend abstraction `PolyOps α` / `PolyOpsRel` / `letB`, certified
   coefficient `ℓ¹`-bound tracking (`PB`, `RespectsBound`, `RespectsBound2D`), and factored
   3-variable hybrid checkers (`mvPoly3_eq_zero_of_kronecker_grid` and
   `mvPoly3_eq_zero_of_kronecker2D_gridT`).

Extracted from the `symmetric-sextic-residual` construction (`benediamond`). -/

noncomputable section
namespace PolynomialEncoding.KroneckerCheck
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions
open MvPolynomial
open scoped BigOperators Polynomial

/-- Whether every variable index occurring in `e` is `< n`. -/
def varsInRange (n : ℕ) : Expr → Bool
  | .num _ | .natCast _ | .intCast _ => true
  | .var i => decide (i < n)
  | .neg a => varsInRange n a
  | .add a b | .sub a b | .mul a b => varsInRange n a && varsInRange n b
  | .pow a _ => varsInRange n a

/-- Per-variable degree upper bound of a ring expression. -/
def exprDeg (i : ℕ) : Expr → ℕ
  | .num _ | .natCast _ | .intCast _ => 0
  | .var j => if j = i then 1 else 0
  | .neg a => exprDeg i a
  | .add a b | .sub a b => max (exprDeg i a) (exprDeg i b)
  | .mul a b => exprDeg i a + exprDeg i b
  | .pow a k => k * exprDeg i a

/-- Mixed-radix stride for variable `i` given base bounds `bound : Fin n → ℕ`. -/
def stride {n : ℕ} (bound : Fin n → ℕ) (i : Fin n) : ℕ :=
  ∏ j : Fin n, if j.val < i.val then bound j else 1

/-- Mixed-radix index of a monomial exponent vector `m : Fin n →₀ ℕ`. -/
def monIdx {n : ℕ} (bound : Fin n → ℕ) (m : Fin n →₀ ℕ) : ℕ :=
  ∑ i : Fin n, m i * stride bound i

lemma stride_succ {n : ℕ} (bound : Fin (n + 1) → ℕ) (i : Fin n) :
    stride bound i.succ = bound 0 * stride (fun j => bound j.succ) i := by
  simp [stride, Fin.prod_univ_succ]

lemma stride_zero {n : ℕ} (bound : Fin (n + 1) → ℕ) : stride bound 0 = 1 := by
  simp [stride]

lemma monIdx_injective : ∀ {n : ℕ} (bound : Fin n → ℕ) (m₁ m₂ : Fin n →₀ ℕ),
    (∀ i, m₁ i < bound i) → (∀ i, m₂ i < bound i) →
    monIdx bound m₁ = monIdx bound m₂ → m₁ = m₂
  | 0, _, m₁, m₂, _, _, _ => by ext i; exact Fin.elim0 i
  | n + 1, bound, m₁, m₂, h₁, h₂, heq => by
    have hsum (m : Fin (n + 1) →₀ ℕ) :
        monIdx bound m = m 0 + bound 0 *
          monIdx (fun j : Fin n => bound j.succ) (Finsupp.equivFunOnFinite.symm (fun j => m j.succ)) := by
      simp only [monIdx, Fin.sum_univ_succ, stride_zero, mul_one, stride_succ]
      rw [Finset.mul_sum]
      congr 1; apply Finset.sum_congr rfl; intro j _
      change m j.succ * (bound 0 * stride (fun j => bound j.succ) j) =
        bound 0 * (m j.succ * stride (fun j => bound j.succ) j)
      ring
    rw [hsum m₁, hsum m₂] at heq
    have h0 : m₁ 0 = m₂ 0 := by
      have hm := congrArg (· % bound 0) heq
      rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (h₁ 0), Nat.mod_eq_of_lt (h₂ 0)] at hm
      exact hm
    have hb0 : 0 < bound 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) (h₁ 0)
    have htail_eq :
        monIdx (fun j : Fin n => bound j.succ) (Finsupp.equivFunOnFinite.symm (fun j => m₁ j.succ)) =
        monIdx (fun j : Fin n => bound j.succ) (Finsupp.equivFunOnFinite.symm (fun j => m₂ j.succ)) := by
      rw [h0] at heq
      exact Nat.eq_of_mul_eq_mul_left hb0 (Nat.add_left_cancel heq)
    have htail := monIdx_injective (fun j : Fin n => bound j.succ)
      (Finsupp.equivFunOnFinite.symm (fun j => m₁ j.succ))
      (Finsupp.equivFunOnFinite.symm (fun j => m₂ j.succ))
      (fun j => by simpa using h₁ j.succ) (fun j => by simpa using h₂ j.succ) htail_eq
    ext i
    refine Fin.cases h0 (fun j => ?_) i
    simpa using congrArg (fun f : Fin n →₀ ℕ => f j) htail

/-- Kronecker encoding homomorphism `MvPolynomial (Fin n) ℕ →+* ℕ[X]`. -/
def encode {n : ℕ} (bound : Fin n → ℕ) : MvPolynomial (Fin n) ℕ →+* ℕ[X] :=
  MvPolynomial.eval₂Hom Polynomial.C (fun i => Polynomial.X ^ stride bound i)

lemma encode_monomial {n : ℕ} (bound : Fin n → ℕ) (m : Fin n →₀ ℕ) (c : ℕ) :
    encode bound (monomial m c) = Polynomial.monomial (monIdx bound m) c := by
  rw [encode, eval₂Hom_monomial, ← Polynomial.C_mul_X_pow_eq_monomial]
  congr 1
  rw [Finsupp.prod_of_support_subset m (Finset.subset_univ _) _ (fun _ _ => pow_zero _)]
  simp only [← pow_mul, Finset.prod_pow_eq_pow_sum, monIdx]
  congr 1; apply Finset.sum_congr rfl; intro i _; ring

lemma encode_coeff_of_bounded {n : ℕ} (bound : Fin n → ℕ) (p : MvPolynomial (Fin n) ℕ)
    (hp : ∀ m ∈ p.support, ∀ i, m i < bound i) (m₀ : Fin n →₀ ℕ) (hm₀ : ∀ i, m₀ i < bound i) :
    (encode bound p).coeff (monIdx bound m₀) = p.coeff m₀ := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  change (Polynomial.lcoeff ℕ (monIdx bound m₀)) _ = _
  rw [map_sum]
  simp_rw [Polynomial.lcoeff_apply, encode_monomial, Polynomial.coeff_monomial]
  by_cases hmem : m₀ ∈ p.support
  · rw [Finset.sum_eq_single m₀]
    · simp
    · intro m hm hne
      have hidx : monIdx bound m ≠ monIdx bound m₀ := fun h =>
        hne (monIdx_injective bound m m₀ (hp m hm) hm₀ h)
      simp [hidx]
    · intro h; exact (h hmem).elim
  · rw [Finset.sum_eq_zero]
    · exact (MvPolynomial.notMem_support_iff.mp hmem).symm
    · intro m hm
      have hne : m ≠ m₀ := fun h => hmem (h ▸ hm)
      have hidx : monIdx bound m ≠ monIdx bound m₀ := fun h =>
        hne (monIdx_injective bound m m₀ (hp m hm) hm₀ h)
      simp [hidx]

theorem encode_injective_of_bounded {n : ℕ} (bound : Fin n → ℕ) (p q : MvPolynomial (Fin n) ℕ)
    (hp : ∀ m ∈ p.support, ∀ i, m i < bound i)
    (hq : ∀ m ∈ q.support, ∀ i, m i < bound i)
    (heq : encode bound p = encode bound q) : p = q := by
  ext m
  by_cases hm : ∀ i, m i < bound i
  · rw [← encode_coeff_of_bounded bound p hp m hm,
      ← encode_coeff_of_bounded bound q hq m hm, heq]
  · have h1 : m ∉ p.support := fun h => hm (hp m h)
    have h2 : m ∉ q.support := fun h => hm (hq m h)
    rw [MvPolynomial.notMem_support_iff.mp h1, MvPolynomial.notMem_support_iff.mp h2]

def polyVar (n : ℕ) (i : ℕ) : MvPolynomial (Fin n) ℕ :=
  if h : i < n then MvPolynomial.X ⟨i, h⟩ else 0

lemma deg_le_add {n : ℕ} {p q : MvPolynomial (Fin n) ℕ} {d₁ d₂ : Fin n → ℕ}
    (hp : ∀ m ∈ p.support, ∀ i, m i ≤ d₁ i)
    (hq : ∀ m ∈ q.support, ∀ i, m i ≤ d₂ i) :
    ∀ m ∈ (p + q).support, ∀ i, m i ≤ max (d₁ i) (d₂ i) := by
  intro m hm i
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact (hp m h i).trans (le_max_left _ _)
  · exact (hq m h i).trans (le_max_right _ _)

lemma deg_le_mul {n : ℕ} {p q : MvPolynomial (Fin n) ℕ} {d₁ d₂ : Fin n → ℕ}
    (hp : ∀ m ∈ p.support, ∀ i, m i ≤ d₁ i)
    (hq : ∀ m ∈ q.support, ∀ i, m i ≤ d₂ i) :
    ∀ m ∈ (p * q).support, ∀ i, m i ≤ d₁ i + d₂ i := by
  intro m hm i
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hm)
  simpa only [Finsupp.add_apply] using Nat.add_le_add (hp m₁ hm₁ i) (hq m₂ hm₂ i)

lemma deg_le_pairMul {n : ℕ} {p q : MvPolynomial (Fin n) ℕ × MvPolynomial (Fin n) ℕ}
    {d₁ d₂ : Fin n → ℕ}
    (hp : (∀ m ∈ p.1.support, ∀ i, m i ≤ d₁ i) ∧ (∀ m ∈ p.2.support, ∀ i, m i ≤ d₁ i))
    (hq : (∀ m ∈ q.1.support, ∀ i, m i ≤ d₂ i) ∧ (∀ m ∈ q.2.support, ∀ i, m i ≤ d₂ i)) :
    (∀ m ∈ (pairMul p q).1.support, ∀ i, m i ≤ d₁ i + d₂ i) ∧
    (∀ m ∈ (pairMul p q).2.support, ∀ i, m i ≤ d₁ i + d₂ i) := by
  constructor
  · simpa [pairMul] using deg_le_add (deg_le_mul hp.1 hq.1) (deg_le_mul hp.2 hq.2)
  · simpa [pairMul] using deg_le_add (deg_le_mul hp.1 hq.2) (deg_le_mul hp.2 hq.1)

lemma support_natCast_eq_zero {n : ℕ} (k : ℕ) {m : Fin n →₀ ℕ}
    (hm : m ∈ (k : MvPolynomial (Fin n) ℕ).support) : m = 0 := by
  rw [MvPolynomial.mem_support_iff, ← MvPolynomial.C_eq_natCast, MvPolynomial.coeff_C] at hm
  by_contra h
  exact hm (ite_eq_right (Ne.symm h))

lemma deg_le_pairPow {n : ℕ} {p : MvPolynomial (Fin n) ℕ × MvPolynomial (Fin n) ℕ}
    {d : Fin n → ℕ}
    (hp : (∀ m ∈ p.1.support, ∀ i, m i ≤ d i) ∧ (∀ m ∈ p.2.support, ∀ i, m i ≤ d i)) :
    ∀ k : ℕ,
      (∀ m ∈ (pairPow p k).1.support, ∀ i, m i ≤ k * d i) ∧
      (∀ m ∈ (pairPow p k).2.support, ∀ i, m i ≤ k * d i)
  | 0 => by
    constructor
    · intro m hm i
      have h0 : m = 0 := support_natCast_eq_zero 1 (by simpa [pairPow] using hm)
      subst h0; simp
    · intro m hm; simp [pairPow] at hm
  | k + 1 => by
    have ih := deg_le_pairPow hp k
    have hmul := deg_le_pairMul hp ih
    constructor
    · intro m hm i
      have := hmul.1 m hm i
      simpa [Nat.succ_mul, Nat.add_comm] using this
    · intro m hm i
      have := hmul.2 m hm i
      simpa [Nat.succ_mul, Nat.add_comm] using this

lemma splitEval_deg_le (n : ℕ) (e : Expr) :
    (∀ m ∈ (splitEval (polyVar n) e).1.support, ∀ i : Fin n, m i ≤ exprDeg i.val e) ∧
    (∀ m ∈ (splitEval (polyVar n) e).2.support, ∀ i : Fin n, m i ≤ exprDeg i.val e) := by
  induction e with
  | num k =>
    cases k with
    | ofNat a =>
      constructor
      · intro m hm i
        have h0 := support_natCast_eq_zero a (by simpa [splitEval, numberPair] using hm)
        subst h0; simp [exprDeg]
      · intro m hm; simp [splitEval, numberPair] at hm
    | negSucc a =>
      constructor
      · intro m hm; simp [splitEval, numberPair] at hm
      · intro m hm i
        have h0 := support_natCast_eq_zero (a + 1) (by simpa [splitEval, numberPair] using hm)
        subst h0; simp [exprDeg]
  | intCast k =>
    cases k with
    | ofNat a =>
      constructor
      · intro m hm i
        have h0 := support_natCast_eq_zero a (by simpa [splitEval, numberPair] using hm)
        subst h0; simp [exprDeg]
      · intro m hm; simp [splitEval, numberPair] at hm
    | negSucc a =>
      constructor
      · intro m hm; simp [splitEval, numberPair] at hm
      · intro m hm i
        have h0 := support_natCast_eq_zero (a + 1) (by simpa [splitEval, numberPair] using hm)
        subst h0; simp [exprDeg]
  | natCast k =>
    constructor
    · intro m hm i
      have h0 := support_natCast_eq_zero k (by simpa [splitEval] using hm)
      subst h0; simp [exprDeg]
    · intro m hm; simp [splitEval] at hm
  | var j =>
    constructor
    · intro m hm i
      dsimp only [splitEval, polyVar] at hm
      split_ifs at hm with hj
      · rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
        subst hm
        simp only [Finsupp.single_apply, exprDeg]
        by_cases hji : j = i.val
        · subst hji; simp
        · have hne : (⟨j, hj⟩ : Fin n) ≠ i := fun h => hji (congrArg Fin.val h)
          simp [hne, hji]
      · simp at hm
    · intro m hm; simp [splitEval] at hm
  | neg a ih => exact ⟨ih.2, ih.1⟩
  | add a b iha ihb =>
    exact ⟨deg_le_add iha.1 ihb.1, deg_le_add iha.2 ihb.2⟩
  | sub a b iha ihb =>
    exact ⟨deg_le_add iha.1 ihb.2, deg_le_add iha.2 ihb.1⟩
  | mul a b iha ihb => exact deg_le_pairMul iha ihb
  | pow a k iha => exact deg_le_pairPow iha k

def value {n : ℕ} (bound : Fin n → ℕ) (b : ℕ) (i : ℕ) : ℕ :=
  if h : i < n then b ^ stride bound ⟨i, h⟩ else 0

def evaluation {n : ℕ} (bound : Fin n → ℕ) (b : ℕ) : MvPolynomial (Fin n) ℕ →+* ℕ :=
  (Polynomial.evalRingHom b).comp (encode bound)

lemma evaluation_polyVar {n : ℕ} (bound : Fin n → ℕ) (b i : ℕ) :
    evaluation bound b (polyVar n i) = value bound b i := by
  dsimp only [evaluation, encode, polyVar, value]
  split_ifs with h <;> simp

lemma evaluation_parts {n : ℕ} (bound : Fin n → ℕ) (b : ℕ) (e : Expr) :
    (evaluation bound b (splitEval (polyVar n) e).1,
     evaluation bound b (splitEval (polyVar n) e).2) =
      splitEval (value bound b) e := by
  simpa only [evaluation_polyVar] using splitEval_map (evaluation bound b) (polyVar n) e

lemma value_one {n : ℕ} (bound : Fin n → ℕ) (i : ℕ) :
    value bound 1 i = if i < n then 1 else 0 := by
  dsimp only [value]; split_ifs <;> simp

def positiveMass (n : ℕ) (e f : Expr) : ℕ :=
  (splitEval (fun i => if i < n then 1 else 0) e).1 +
    (splitEval (fun i => if i < n then 1 else 0) f).2

def negativeMass (n : ℕ) (e f : Expr) : ℕ :=
  (splitEval (fun i => if i < n then 1 else 0) f).1 +
    (splitEval (fun i => if i < n then 1 else 0) e).2

lemma cast_parts {n : ℕ} (bound : Fin n → ℕ) (b : ℕ) (e : Expr) :
    ((splitEval (value bound b) e).1 : ℤ) - (splitEval (value bound b) e).2 =
      ringEval (fun i => (value bound b i : ℤ)) e := by
  have h' := splitEval_map (Nat.castRingHom ℤ) (value bound b) e
  change (((splitEval (value bound b) e).1 : ℤ), ((splitEval (value bound b) e).2 : ℤ)) =
    splitEval (fun i => (value bound b i : ℤ)) e at h'
  have hd := splitEval_difference (fun i => (value bound b i : ℤ)) e
  rw [← h'] at hd
  exact hd

lemma ringEval_congr_varsInRange {K : Type*} [CommRing K]
    (n : ℕ) (v₁ v₂ : ℕ → K) (hv : ∀ i < n, v₁ i = v₂ i) :
    ∀ e : Expr, varsInRange n e = true → ringEval v₁ e = ringEval v₂ e
  | .num _, _ => rfl
  | .natCast _, _ => rfl
  | .intCast _, _ => rfl
  | .var i, h => hv i (of_decide_eq_true h)
  | .neg a, h => congrArg (-·) (ringEval_congr_varsInRange n v₁ v₂ hv a h)
  | .add a b, h => by
    simp only [varsInRange, Bool.and_eq_true] at h
    simp [ringEval, ringEval_congr_varsInRange n v₁ v₂ hv a h.1,
      ringEval_congr_varsInRange n v₁ v₂ hv b h.2]
  | .sub a b, h => by
    simp only [varsInRange, Bool.and_eq_true] at h
    simp [ringEval, ringEval_congr_varsInRange n v₁ v₂ hv a h.1,
      ringEval_congr_varsInRange n v₁ v₂ hv b h.2]
  | .mul a b, h => by
    simp only [varsInRange, Bool.and_eq_true] at h
    simp [ringEval, ringEval_congr_varsInRange n v₁ v₂ hv a h.1,
      ringEval_congr_varsInRange n v₁ v₂ hv b h.2]
  | .pow a k, h => congrArg (· ^ k) (ringEval_congr_varsInRange n v₁ v₂ hv a h)

theorem encoded_identity {n : ℕ} (bound : Fin n → ℕ) (b : ℕ) (e f : Expr)
    (hb : 0 < b)
    (hde : ∀ i : Fin n, exprDeg i.val e < bound i)
    (hdf : ∀ i : Fin n, exprDeg i.val f < bound i)
    (hp : positiveMass n e f < b) (hn : negativeMass n e f < b)
    (hnum : ringEval (fun i => (value bound b i : ℤ)) e =
      ringEval (fun i => (value bound b i : ℤ)) f) :
    (splitEval (polyVar n) e).1 + (splitEval (polyVar n) f).2 =
      (splitEval (polyVar n) f).1 + (splitEval (polyVar n) e).2 := by
  let p := (splitEval (polyVar n) e).1 + (splitEval (polyVar n) f).2
  let q := (splitEval (polyVar n) f).1 + (splitEval (polyVar n) e).2
  have heD := splitEval_deg_le n e
  have hfD := splitEval_deg_le n f
  apply encode_injective_of_bounded bound p q
  · intro m hm i
    exact (deg_le_add heD.1 hfD.2 m hm i).trans_lt (max_lt (hde i) (hdf i))
  · intro m hm i
    exact (deg_le_add hfD.1 heD.2 m hm i).trans_lt (max_lt (hdf i) (hde i))
  apply PolynomialEncoding.PolynomialDigits.eval_injective_bounded b hb
  · change evaluation bound 1 p < b
    have he1 := congrArg Prod.fst (evaluation_parts bound 1 e)
    have hf2 := congrArg Prod.snd (evaluation_parts bound 1 f)
    dsimp only at he1 hf2
    have hv1 : value bound 1 = (fun i => if i < n then 1 else 0) := funext (value_one bound)
    rw [hv1] at he1 hf2
    simpa only [p, map_add, he1, hf2, positiveMass] using hp
  · change evaluation bound 1 q < b
    have hf1 := congrArg Prod.fst (evaluation_parts bound 1 f)
    have he2 := congrArg Prod.snd (evaluation_parts bound 1 e)
    dsimp only at hf1 he2
    have hv1 : value bound 1 = (fun i => if i < n then 1 else 0) := funext (value_one bound)
    rw [hv1] at hf1 he2
    simpa only [q, map_add, hf1, he2, negativeMass] using hn
  · change evaluation bound b p = evaluation bound b q
    have he1 := congrArg Prod.fst (evaluation_parts bound b e)
    have he2 := congrArg Prod.snd (evaluation_parts bound b e)
    have hf1 := congrArg Prod.fst (evaluation_parts bound b f)
    have hf2 := congrArg Prod.snd (evaluation_parts bound b f)
    dsimp only at he1 he2 hf1 hf2
    simp only [p, q, map_add, he1, he2, hf1, hf2]
    rw [← cast_parts, ← cast_parts] at hnum
    omega

theorem identity_of_kronecker {K : Type*} [CommRing K]
    {n : ℕ} (v : ℕ → K) (bound : Fin n → ℕ) (b : ℕ) (e f : Expr)
    (hb : 0 < b)
    (hve : varsInRange n e = true) (hvf : varsInRange n f = true)
    (hde : ∀ i : Fin n, exprDeg i.val e < bound i)
    (hdf : ∀ i : Fin n, exprDeg i.val f < bound i)
    (hp : positiveMass n e f < b) (hn : negativeMass n e f < b)
    (hnum : ringEval (fun i => (value bound b i : ℤ)) e =
      ringEval (fun i => (value bound b i : ℤ)) f) :
    ringEval v e = ringEval v f := by
  let v' : ℕ → K := fun i => if i < n then v i else 0
  have hv (i : ℕ) (hi : i < n) : v i = v' i := by simp [v', hi]
  rw [ringEval_congr_varsInRange n v v' hv e hve,
      ringEval_congr_varsInRange n v v' hv f hvf]
  let φ : MvPolynomial (Fin n) ℕ →+* K := eval₂Hom (Nat.castRingHom K) (fun i : Fin n => v i.val)
  have hvar (i : ℕ) : φ (polyVar n i) = v' i := by
    dsimp only [φ, polyVar, v']; split_ifs <;> simp
  have h := congrArg φ (encoded_identity bound b e f hb hde hdf hp hn hnum)
  rw [map_add, map_add] at h
  have he' := splitEval_map φ (polyVar n) e
  have hf' := splitEval_map φ (polyVar n) f
  have heDiff := splitEval_difference (fun i => φ (polyVar n i)) e
  have hfDiff := splitEval_difference (fun i => φ (polyVar n i)) f
  rw [← he'] at heDiff
  rw [← hf'] at hfDiff
  simp only [hvar] at heDiff hfDiff
  rw [← heDiff, ← hfDiff]
  linear_combination h

/-! Hybrid Kronecker + small-integer grid checker:
Kronecker-encodes the first `m` variables (`0 .. m-1`) and evaluates the last `k` variables
(`m .. m+k-1`) on `{0, ..., gridDeg j}`. Keeps Kronecker bit-widths tiny even for high-degree
5-variable polynomials while proving exact identities in any `CommRing K` via pure kernel `rfl`. -/

def allGrid : ∀ {k : ℕ}, (Fin k → ℕ) → ((Fin k → ℕ) → Bool) → Bool
  | 0, _, P => P Fin.elim0
  | _ + 1, d, P =>
    (List.range (d 0 + 1)).all fun a =>
      allGrid (fun j => d j.succ) (fun g => P (Fin.cons a g))

lemma allGrid_eq_true : ∀ {k : ℕ} (d : Fin k → ℕ) (P : (Fin k → ℕ) → Bool),
    allGrid d P = true → ∀ g : Fin k → ℕ, (∀ j, g j ≤ d j) → P g = true
  | 0, _, P, h, g, _ => by
    have hg : g = Fin.elim0 := funext fun j => Fin.elim0 j
    simpa [allGrid, hg] using h
  | _ + 1, d, P, h, g, hg => by
    rw [allGrid, List.all_eq_true] at h
    have ha : g 0 ∈ List.range (d 0 + 1) := List.mem_range.mpr (Nat.lt_succ_of_le (hg 0))
    have hrec := allGrid_eq_true (fun j => d j.succ) (fun g' => P (Fin.cons (g 0) g'))
      (h (g 0) ha) (fun j => g j.succ) (fun j => hg j.succ)
    have hcons : Fin.cons (g 0) (fun j => g j.succ) = g := by
      ext j; refine Fin.cases rfl (fun _ => rfl) j
    simpa [hcons] using hrec

def gridVal {m k : ℕ} (bound : Fin m → ℕ) (b : ℕ) (g : Fin k → ℕ) (i : ℕ) : ℕ :=
  if h1 : i < m then b ^ stride bound ⟨i, h1⟩
  else if h2 : i < m + k then g ⟨i - m, by omega⟩
  else 0

def gridMassVal {m k : ℕ} (gridDeg : Fin k → ℕ) (i : ℕ) : ℕ :=
  if h1 : i < m then 1
  else if h2 : i < m + k then gridDeg ⟨i - m, by omega⟩
  else 0

def positiveMassGrid {m k : ℕ} (gridDeg : Fin k → ℕ) (e f : Expr) : ℕ :=
  (splitEval (gridMassVal (m := m) gridDeg) e).1 +
    (splitEval (gridMassVal (m := m) gridDeg) f).2

def negativeMassGrid {m k : ℕ} (gridDeg : Fin k → ℕ) (e f : Expr) : ℕ :=
  (splitEval (gridMassVal (m := m) gridDeg) f).1 +
    (splitEval (gridMassVal (m := m) gridDeg) e).2

def checkGrid {m k : ℕ} (bound : Fin m → ℕ) (gridDeg : Fin k → ℕ) (b : ℕ) (e f : Expr) : Bool :=
  allGrid gridDeg fun g =>
    decide (ringEval (fun i => (gridVal bound b g i : ℤ)) e =
      ringEval (fun i => (gridVal bound b g i : ℤ)) f)

lemma mvpoly_eval_mono {n : ℕ} {v₁ v₂ : Fin n → ℕ} (h : ∀ i, v₁ i ≤ v₂ i)
    (p : MvPolynomial (Fin n) ℕ) : MvPolynomial.eval v₁ p ≤ MvPolynomial.eval v₂ p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add]; exact Nat.add_le_add hp hq
  | mul_X p i hp => simp only [map_mul, eval_X]; exact Nat.mul_le_mul hp (h i)

lemma mvpoly_zero_of_grid {R : Type*} [CommRing R] [IsDomain R] [CharZero R] :
    ∀ {k : ℕ} (d : Fin k → ℕ) (p : MvPolynomial (Fin k) R),
      (∀ m ∈ p.support, ∀ j, m j ≤ d j) →
      (∀ g : Fin k → ℕ, (∀ j, g j ≤ d j) → MvPolynomial.eval (fun j => (g j : R)) p = 0) →
      p = 0
  | 0, _, p, _, hzero => by
    have hp : ∀ q : MvPolynomial (Fin 0) R,
        q = MvPolynomial.C (MvPolynomial.eval (fun j : Fin 0 => ((Fin.elim0 j : ℕ) : R)) q) := by
      intro q
      induction q using MvPolynomial.induction_on with
      | C c => simp
      | add a b ha hb => rw [map_add, map_add, ← ha, ← hb]
      | mul_X _ j _ => exact Fin.elim0 j
    have h0 := hzero Fin.elim0 (fun j => Fin.elim0 j)
    rw [hp p, h0, map_zero]
  | k + 1, d, p, hdeg, hzero => by
    let P : Polynomial (MvPolynomial (Fin k) R) := MvPolynomial.finSuccEquiv R k p
    have hPdeg : P.natDegree ≤ d 0 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro n hn
      ext m
      rw [MvPolynomial.finSuccEquiv_coeff_coeff]
      simp only [AddMonoidAlgebra.coeff_zero]
      by_contra hne
      have hmem : Finsupp.cons n m ∈ p.support := MvPolynomial.mem_support_iff.mpr hne
      have hle := hdeg _ hmem 0
      simp only [Finsupp.cons_zero] at hle
      omega
    have hroot (a : ℕ) (ha : a ≤ d 0) :
        Polynomial.eval (MvPolynomial.C (a : R)) P = 0 := by
      let q := Polynomial.eval (MvPolynomial.C (a : R)) P
      apply mvpoly_zero_of_grid (fun j => d j.succ) q
      · intro m hm j
        rw [MvPolynomial.mem_support_iff] at hm
        have hq_coeff : q.coeff m =
            ∑ i ∈ Finset.range (P.natDegree + 1), (P.coeff i).coeff m * (a : R) ^ i := by
          dsimp only [q]
          rw [Polynomial.eval_eq_sum_range, MvPolynomial.coeff_sum]
          apply Finset.sum_congr rfl; intro i _
          rw [← map_pow, _root_.mul_comm, MvPolynomial.coeff_C_mul, _root_.mul_comm]
        rw [hq_coeff] at hm
        have hex : ∃ i ∈ Finset.range (P.natDegree + 1), (P.coeff i).coeff m * (a : R) ^ i ≠ 0 := by
          by_contra hall; push Not at hall; exact hm (Finset.sum_eq_zero hall)
        obtain ⟨i, _, hi⟩ := hex
        have hci : (P.coeff i).coeff m ≠ 0 := left_ne_zero_of_mul hi
        rw [MvPolynomial.finSuccEquiv_coeff_coeff] at hci
        have hle := hdeg _ (MvPolynomial.mem_support_iff.mpr hci) j.succ
        simpa only [Finsupp.cons_succ] using hle
      · intro g hg
        have heval_eq : MvPolynomial.eval (fun j => (g j : R)) (Polynomial.eval (MvPolynomial.C (a : R)) P) =
            MvPolynomial.eval (fun j => ((Fin.cons a g : Fin (k + 1) → ℕ) j : R)) p := by
          let φ₁ : MvPolynomial (Fin (k + 1)) R →+* R :=
            (MvPolynomial.eval (fun j => (g j : R))).comp
              ((Polynomial.evalRingHom (MvPolynomial.C (a : R))).comp (MvPolynomial.finSuccEquiv R k).toRingHom)
          let φ₂ : MvPolynomial (Fin (k + 1)) R →+* R :=
            MvPolynomial.eval (fun j => ((Fin.cons a g : Fin (k + 1) → ℕ) j : R))
          have hφ : φ₁ = φ₂ := by
            apply MvPolynomial.ringHom_ext
            · intro r; simp [φ₁, φ₂, MvPolynomial.finSuccEquiv_apply]
            · intro i; refine Fin.cases ?_ (fun j => ?_) i
              · simp [φ₁, φ₂, MvPolynomial.finSuccEquiv_X_zero]
              · simp [φ₁, φ₂, MvPolynomial.finSuccEquiv_X_succ]
          exact congrArg (fun f => f p) hφ
        rw [heval_eq]
        exact hzero (Fin.cons a g) (fun j => Fin.cases ha (fun j' => hg j') j)
    have hP0 : P = 0 := by
      classical
      by_contra hPne
      let S : Finset (MvPolynomial (Fin k) R) :=
        (Finset.range (d 0 + 1)).image (fun a : ℕ => MvPolynomial.C (a : R))
      have hinj : Function.Injective (fun a : ℕ => MvPolynomial.C (σ := Fin k) (a : R)) :=
        Function.Injective.comp (MvPolynomial.C_injective (Fin k) R) Nat.cast_injective
      have hScard : S.card = d 0 + 1 := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
      have hsub : S ⊆ P.roots.toFinset := by
        intro r hr
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hPne, Polynomial.IsRoot.def]
        exact hroot a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha))
      have hle1 : S.card ≤ P.roots.toFinset.card := Finset.card_le_card hsub
      have hle2 : P.roots.toFinset.card ≤ P.roots.card := Multiset.toFinset_card_le _
      have hle3 : P.roots.card ≤ P.natDegree := Polynomial.card_roots' P
      omega
    exact (MvPolynomial.finSuccEquiv R k).injective (by simpa [P] using hP0)

theorem identity_of_grid_kronecker {K : Type*} [CommRing K]
    {m k : ℕ} (v : ℕ → K) (bound : Fin m → ℕ) (gridDeg : Fin k → ℕ) (b : ℕ) (e f : Expr)
    (hb : 0 < b)
    (hve : varsInRange (m + k) e = true) (hvf : varsInRange (m + k) f = true)
    (hde_m : ∀ i : Fin m, exprDeg i.val e < bound i)
    (hdf_m : ∀ i : Fin m, exprDeg i.val f < bound i)
    (hde_k : ∀ j : Fin k, exprDeg (m + j.val) e ≤ gridDeg j)
    (hdf_k : ∀ j : Fin k, exprDeg (m + j.val) f ≤ gridDeg j)
    (hp : positiveMassGrid (m := m) gridDeg e f < b)
    (hn : negativeMassGrid (m := m) gridDeg e f < b)
    (hgrid : checkGrid bound gridDeg b e f = true) :
    ringEval v e = ringEval v f := by
  let p := (splitEval (polyVar (m + k)) e).1 + (splitEval (polyVar (m + k)) f).2
  let q := (splitEval (polyVar (m + k)) f).1 + (splitEval (polyVar (m + k)) e).2
  have heD := splitEval_deg_le (m + k) e
  have hfD := splitEval_deg_le (m + k) f
  have hp_m : ∀ mon ∈ p.support, ∀ i : Fin m, mon ⟨i.val, by omega⟩ < bound i := by
    intro mon hmon i
    exact (deg_le_add heD.1 hfD.2 mon hmon ⟨i.val, by omega⟩).trans_lt (max_lt (hde_m i) (hdf_m i))
  have hq_m : ∀ mon ∈ q.support, ∀ i : Fin m, mon ⟨i.val, by omega⟩ < bound i := by
    intro mon hmon i
    exact (deg_le_add hfD.1 heD.2 mon hmon ⟨i.val, by omega⟩).trans_lt (max_lt (hdf_m i) (hde_m i))
  have hp_k : ∀ mon ∈ p.support, ∀ j : Fin k, mon ⟨m + j.val, by omega⟩ ≤ gridDeg j := by
    intro mon hmon j
    exact (deg_le_add heD.1 hfD.2 mon hmon ⟨m + j.val, by omega⟩).trans (max_le (hde_k j) (hdf_k j))
  have hq_k : ∀ mon ∈ q.support, ∀ j : Fin k, mon ⟨m + j.val, by omega⟩ ≤ gridDeg j := by
    intro mon hmon j
    exact (deg_le_add hfD.1 heD.2 mon hmon ⟨m + j.val, by omega⟩).trans (max_le (hdf_k j) (hde_k j))
  let splitMap : MvPolynomial (Fin (m + k)) ℕ →+* MvPolynomial (Fin k) (MvPolynomial (Fin m) ℤ) :=
    MvPolynomial.eval₂Hom (MvPolynomial.C.comp (MvPolynomial.C.comp (Nat.castRingHom ℤ)))
      (fun idx => if h : idx.val < m then MvPolynomial.C (MvPolynomial.X ⟨idx.val, h⟩)
        else MvPolynomial.X ⟨idx.val - m, by omega⟩)
  -- For every grid point g ≤ gridDeg, evG p = evG q in MvPolynomial (Fin m) ℕ!
  have hsplit_eq : splitMap p = splitMap q := by
    apply sub_eq_zero.mp
    apply mvpoly_zero_of_grid gridDeg (splitMap p - splitMap q)
    · -- Degree bound in Fin k of splitMap p - splitMap q
      have hdeg_split (r : MvPolynomial (Fin (m + k)) ℕ)
          (hr : ∀ mon ∈ r.support, ∀ j : Fin k, mon ⟨m + j.val, by omega⟩ ≤ gridDeg j) :
          ∀ mon ∈ (splitMap r).support, ∀ j : Fin k, mon j ≤ gridDeg j := by
        intro mon hmon j
        rw [r.as_sum, map_sum] at hmon
        obtain ⟨d, hd, hmem⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hmon)
        dsimp only [splitMap] at hmem
        rw [eval₂Hom_monomial] at hmem
        have hprod_eq : (d.prod fun idx a =>
              (if h : idx.val < m then MvPolynomial.C (MvPolynomial.X (R := ℤ) ⟨idx.val, h⟩)
                else MvPolynomial.X ⟨idx.val - m, by omega⟩) ^ a) =
            MvPolynomial.C (∏ i : Fin m, MvPolynomial.X (R := ℤ) i ^ d ⟨i.val, by omega⟩) *
              MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun j : Fin k => d ⟨m + j.val, by omega⟩) 1 := by
          rw [Finsupp.prod_of_support_subset d (Finset.subset_univ _) _ (fun _ _ => pow_zero _)]
          rw [Fin.prod_univ_add]
          congr 1
          · rw [map_prod]
            apply Finset.prod_congr rfl; intro i _
            have hi : (Fin.castAdd k i).val < m := i.isLt
            rw [dite_eq_left hi, map_pow]; rfl
          · rw [MvPolynomial.monomial_eq, map_one, one_mul,
              Finsupp.prod_of_support_subset _ (Finset.subset_univ _) _ (fun _ _ => pow_zero _)]
            apply Finset.prod_congr rfl; intro j _
            have hj : ¬ (Fin.natAdd m j).val < m := by simp
            rw [dite_eq_right hj]; simp [Fin.natAdd]
        simp only [RingHom.comp_apply] at hmem
        rw [hprod_eq, ← mul_assoc, ← map_mul, MvPolynomial.C_mul_monomial, mul_one] at hmem
        have hmon_eq : mon = Finsupp.equivFunOnFinite.symm fun j : Fin k => d ⟨m + j.val, by omega⟩ :=
          Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hmem)
        subst hmon_eq
        simpa using hr d hd j
      intro mon hmon j
      rw [sub_eq_add_neg] at hmon
      rcases Finset.mem_union.mp (MvPolynomial.support_add hmon) with h | h
      · exact hdeg_split p hp_k mon h j
      · rw [MvPolynomial.support_neg] at h; exact hdeg_split q hq_k mon h j
    · intro g hg
      let evG : MvPolynomial (Fin (m + k)) ℕ →+* MvPolynomial (Fin m) ℕ :=
        MvPolynomial.eval₂Hom MvPolynomial.C
          (fun idx => if h : idx.val < m then MvPolynomial.X ⟨idx.val, h⟩
            else MvPolynomial.C (g ⟨idx.val - m, by omega⟩))
      have hevG_eq : evG p = evG q := by
        have hdeg_evG (r : MvPolynomial (Fin (m + k)) ℕ)
            (hr : ∀ mon ∈ r.support, ∀ i : Fin m, mon ⟨i.val, by omega⟩ < bound i) :
            ∀ mon ∈ (evG r).support, ∀ i : Fin m, mon i < bound i := by
          intro mon hmon i
          rw [r.as_sum, map_sum] at hmon
          obtain ⟨d, hd, hmem⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hmon)
          dsimp only [evG] at hmem
          rw [eval₂Hom_monomial] at hmem
          have hprod_eq : (d.prod fun idx a =>
                (if h : idx.val < m then MvPolynomial.X (R := ℕ) ⟨idx.val, h⟩
                  else MvPolynomial.C (g ⟨idx.val - m, by omega⟩)) ^ a) =
              MvPolynomial.C (∏ j : Fin k, g j ^ d ⟨m + j.val, by omega⟩) *
                MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i : Fin m => d ⟨i.val, by omega⟩) 1 := by
            rw [Finsupp.prod_of_support_subset d (Finset.subset_univ _) _ (fun _ _ => pow_zero _)]
            rw [Fin.prod_univ_add, _root_.mul_comm]
            congr 1
            · rw [map_prod]
              apply Finset.prod_congr rfl; intro j _
              have hj : ¬ (Fin.natAdd m j).val < m := by simp
              rw [dite_eq_right hj, map_pow]; simp [Fin.natAdd]
            · rw [MvPolynomial.monomial_eq, map_one, one_mul,
                Finsupp.prod_of_support_subset _ (Finset.subset_univ _) _ (fun _ _ => pow_zero _)]
              apply Finset.prod_congr rfl; intro i _
              have hi : (Fin.castAdd k i).val < m := i.isLt
              rw [dite_eq_left hi]; simp [Fin.castAdd, Fin.castLE]
          rw [hprod_eq, ← mul_assoc, ← map_mul, MvPolynomial.C_mul_monomial, mul_one] at hmem
          have hmon_eq : mon = Finsupp.equivFunOnFinite.symm fun i : Fin m => d ⟨i.val, by omega⟩ :=
            Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hmem)
          subst hmon_eq
          simpa using hr d hd i
        apply encode_injective_of_bounded bound (evG p) (evG q) (hdeg_evG p hp_m) (hdeg_evG q hq_m)
        apply PolynomialEncoding.PolynomialDigits.eval_injective_bounded b hb
        · -- Mass bound for evG p at 1, via monotonicity from gridMassVal
          have heval1 (r : MvPolynomial (Fin (m + k)) ℕ) :
              (encode bound (evG r)).eval 1 =
                MvPolynomial.eval (fun idx : Fin (m + k) => gridVal bound 1 g idx.val) r := by
            change ((Polynomial.evalRingHom 1).comp ((encode bound).comp evG)) r = _
            have hhom : (Polynomial.evalRingHom 1).comp ((encode bound).comp evG) =
                MvPolynomial.eval (fun idx : Fin (m + k) => gridVal bound 1 g idx.val) := by
              apply MvPolynomial.ringHom_ext
              · intro c; simp [evG, encode]
              · intro idx
                simp only [RingHom.comp_apply, evG, encode, eval₂Hom_X', gridVal]
                by_cases h1 : idx.val < m
                · simp [h1]
                · simp [h1]
            exact congrArg (fun f => f r) hhom
          rw [heval1]
          have hmono : MvPolynomial.eval (fun idx : Fin (m + k) => gridVal bound 1 g idx.val) p ≤
              MvPolynomial.eval (fun idx : Fin (m + k) => gridMassVal (m := m) gridDeg idx.val) p := by
            apply mvpoly_eval_mono; intro idx
            dsimp only [gridVal, gridMassVal]
            by_cases h1 : idx.val < m
            · simp [h1]
            · simp only [dite_eq_right h1, dite_eq_left idx.isLt]
              exact hg ⟨idx.val - m, by omega⟩
          have hmass : MvPolynomial.eval (fun idx : Fin (m + k) => gridMassVal (m := m) gridDeg idx.val) p =
              positiveMassGrid (m := m) gridDeg e f := by
            let evM : MvPolynomial (Fin (m + k)) ℕ →+* ℕ :=
              MvPolynomial.eval (fun idx : Fin (m + k) => gridMassVal (m := m) gridDeg idx.val)
            have hvar (i : ℕ) : evM (polyVar (m + k) i) = gridMassVal (m := m) gridDeg i := by
              dsimp only [evM, polyVar, gridMassVal]
              by_cases h2 : i < m + k
              · simp [h2]
              · have h1 : ¬ i < m := by omega
                simp [h1, h2]
            have he' := congrArg Prod.fst (splitEval_map evM (polyVar (m + k)) e)
            have hf' := congrArg Prod.snd (splitEval_map evM (polyVar (m + k)) f)
            dsimp only at he' hf'; simp only [hvar] at he' hf'
            change evM p = positiveMassGrid (m := m) gridDeg e f
            rw [show p = (splitEval (polyVar (m + k)) e).1 + (splitEval (polyVar (m + k)) f).2 from rfl,
              map_add, he', hf']; rfl
          exact hmono.trans_lt (hmass.symm ▸ hp)
        · -- Mass bound for evG q at 1
          have heval1 (r : MvPolynomial (Fin (m + k)) ℕ) :
              (encode bound (evG r)).eval 1 =
                MvPolynomial.eval (fun idx : Fin (m + k) => gridVal bound 1 g idx.val) r := by
            change ((Polynomial.evalRingHom 1).comp ((encode bound).comp evG)) r = _
            have hhom : (Polynomial.evalRingHom 1).comp ((encode bound).comp evG) =
                MvPolynomial.eval (fun idx : Fin (m + k) => gridVal bound 1 g idx.val) := by
              apply MvPolynomial.ringHom_ext
              · intro c; simp [evG, encode]
              · intro idx
                simp only [RingHom.comp_apply, evG, encode, eval₂Hom_X', gridVal]
                by_cases h1 : idx.val < m
                · simp [h1]
                · simp [h1]
            exact congrArg (fun f => f r) hhom
          rw [heval1]
          have hmono : MvPolynomial.eval (fun idx : Fin (m + k) => gridVal bound 1 g idx.val) q ≤
              MvPolynomial.eval (fun idx : Fin (m + k) => gridMassVal (m := m) gridDeg idx.val) q := by
            apply mvpoly_eval_mono; intro idx
            dsimp only [gridVal, gridMassVal]
            by_cases h1 : idx.val < m
            · simp [h1]
            · simp only [dite_eq_right h1, dite_eq_left idx.isLt]
              exact hg ⟨idx.val - m, by omega⟩
          have hmass : MvPolynomial.eval (fun idx : Fin (m + k) => gridMassVal (m := m) gridDeg idx.val) q =
              negativeMassGrid (m := m) gridDeg e f := by
            let evM : MvPolynomial (Fin (m + k)) ℕ →+* ℕ :=
              MvPolynomial.eval (fun idx : Fin (m + k) => gridMassVal (m := m) gridDeg idx.val)
            have hvar (i : ℕ) : evM (polyVar (m + k) i) = gridMassVal (m := m) gridDeg i := by
              dsimp only [evM, polyVar, gridMassVal]
              by_cases h2 : i < m + k
              · simp [h2]
              · have h1 : ¬ i < m := by omega
                simp [h1, h2]
            have hf' := congrArg Prod.fst (splitEval_map evM (polyVar (m + k)) f)
            have he' := congrArg Prod.snd (splitEval_map evM (polyVar (m + k)) e)
            dsimp only at hf' he'; simp only [hvar] at hf' he'
            change evM q = negativeMassGrid (m := m) gridDeg e f
            rw [show q = (splitEval (polyVar (m + k)) f).1 + (splitEval (polyVar (m + k)) e).2 from rfl,
              map_add, hf', he']; rfl
          exact hmono.trans_lt (hmass.symm ▸ hn)
        · -- Equality at b from hgrid!
          have hnum : ringEval (fun i => (gridVal bound b g i : ℤ)) e =
              ringEval (fun i => (gridVal bound b g i : ℤ)) f :=
            of_decide_eq_true (allGrid_eq_true gridDeg _ hgrid g hg)
          let evB : MvPolynomial (Fin (m + k)) ℕ →+* ℕ :=
            (Polynomial.evalRingHom b).comp ((encode bound).comp evG)
          have hevB_var (i : ℕ) : evB (polyVar (m + k) i) = gridVal bound b g i := by
            dsimp only [evB, polyVar, gridVal, evG, encode]
            by_cases h2 : i < m + k
            · by_cases h1 : i < m
              · simp [h1, h2]
              · simp [h1, h2]
            · have h1 : ¬ i < m := by omega
              simp [h1, h2]
          have he1 := congrArg Prod.fst (splitEval_map evB (polyVar (m + k)) e)
          have he2 := congrArg Prod.snd (splitEval_map evB (polyVar (m + k)) e)
          have hf1 := congrArg Prod.fst (splitEval_map evB (polyVar (m + k)) f)
          have hf2 := congrArg Prod.snd (splitEval_map evB (polyVar (m + k)) f)
          dsimp only at he1 he2 hf1 hf2
          have hfun : (fun i => evB (polyVar (m + k) i)) = gridVal bound b g := funext hevB_var
          rw [hfun] at he1 he2 hf1 hf2
          have hcast (expr : Expr) :
              ((splitEval (gridVal bound b g) expr).1 : ℤ) - (splitEval (gridVal bound b g) expr).2 =
                ringEval (fun i => (gridVal bound b g i : ℤ)) expr := by
            have h' := splitEval_map (Nat.castRingHom ℤ) (gridVal bound b g) expr
            change (((splitEval (gridVal bound b g) expr).1 : ℤ),
              ((splitEval (gridVal bound b g) expr).2 : ℤ)) =
              splitEval (fun i => (gridVal bound b g i : ℤ)) expr at h'
            have hd := splitEval_difference (fun i => (gridVal bound b g i : ℤ)) expr
            rw [← h'] at hd; exact hd
          change evB p = evB q
          simp only [p, q, map_add, he1, he2, hf1, hf2]
          rw [← hcast e, ← hcast f] at hnum
          omega
      -- Lift evG p = evG q to MvPolynomial (Fin m) ℤ and identify with eval g (splitMap p - splitMap q)
      have hcomm (r : MvPolynomial (Fin (m + k)) ℕ) :
          MvPolynomial.eval (fun j : Fin k => (g j : MvPolynomial (Fin m) ℤ)) (splitMap r) =
            MvPolynomial.map (Nat.castRingHom ℤ) (evG r) := by
        let φ₁ : MvPolynomial (Fin (m + k)) ℕ →+* MvPolynomial (Fin m) ℤ :=
          (MvPolynomial.eval (fun j : Fin k => (g j : MvPolynomial (Fin m) ℤ))).comp splitMap
        let φ₂ : MvPolynomial (Fin (m + k)) ℕ →+* MvPolynomial (Fin m) ℤ :=
          (MvPolynomial.map (Nat.castRingHom ℤ)).comp evG
        have hhom : φ₁ = φ₂ := by
          apply MvPolynomial.ringHom_ext
          · intro c; simp [φ₁, φ₂, splitMap, evG]
          · intro idx
            simp only [φ₁, φ₂, RingHom.comp_apply, splitMap, evG, eval₂Hom_X']
            split_ifs with h1 <;> simp
        exact congrArg (fun f => f r) hhom
      rw [map_sub, hcomm p, hcomm q, hevG_eq, sub_self]
  -- Evaluate splitMap p = splitMap q in K!
  let v' : ℕ → K := fun i => if i < m + k then v i else 0
  have hv (i : ℕ) (hi : i < m + k) : v i = v' i := by simp [v', hi]
  rw [ringEval_congr_varsInRange (m + k) v v' hv e hve,
      ringEval_congr_varsInRange (m + k) v v' hv f hvf]
  let ψ : MvPolynomial (Fin k) (MvPolynomial (Fin m) ℤ) →+* K :=
    MvPolynomial.eval₂Hom (MvPolynomial.eval₂Hom (Int.castRingHom K) (fun i : Fin m => v i.val))
      (fun j : Fin k => v (m + j.val))
  let φ : MvPolynomial (Fin (m + k)) ℕ →+* K := ψ.comp splitMap
  have hvar (i : ℕ) : φ (polyVar (m + k) i) = v' i := by
    dsimp only [φ, ψ, splitMap, polyVar, v']
    by_cases h1 : i < m + k
    · simp only [dite_eq_left h1, ite_eq_left h1, RingHom.comp_apply, eval₂Hom_X']
      by_cases h2 : i < m
      · simp [h2]
      · simp only [dite_eq_right h2, eval₂Hom_X', Nat.add_sub_cancel' (Nat.le_of_not_lt h2)]
    · simp [h1]
  have h := congrArg ψ hsplit_eq
  change φ p = φ q at h
  simp only [p, q, map_add] at h
  have he' := splitEval_map φ (polyVar (m + k)) e
  have hf' := splitEval_map φ (polyVar (m + k)) f
  have heDiff := splitEval_difference (fun i => φ (polyVar (m + k) i)) e
  have hfDiff := splitEval_difference (fun i => φ (polyVar (m + k) i)) f
  rw [← he'] at heDiff; rw [← hf'] at hfDiff
  simp only [hvar] at heDiff hfDiff
  rw [← heDiff, ← hfDiff]
  linear_combination h

/-! Fast native `ℤ` / `ℕ` kernel evaluators (zero typeclass / `Finset.prod` overhead inside
`decide +kernel`!) and specialized `m = 2` Kronecker + `k`-grid theorem `identity_of_grid2`. -/

def fastEvalZ (v : ℕ → ℤ) : Expr → ℤ
  | .num n => n
  | .natCast n => Int.ofNat n
  | .intCast n => n
  | .var i => v i
  | .neg a => Int.neg (fastEvalZ v a)
  | .add a b => Int.add (fastEvalZ v a) (fastEvalZ v b)
  | .sub a b => Int.sub (fastEvalZ v a) (fastEvalZ v b)
  | .mul a b => Int.mul (fastEvalZ v a) (fastEvalZ v b)
  | .pow a n => Int.pow (fastEvalZ v a) n

lemma fastEvalZ_eq (v : ℕ → ℤ) : ∀ e : Expr, fastEvalZ v e = ringEval v e
  | .num _ => rfl
  | .natCast _ => rfl
  | .intCast _ => rfl
  | .var _ => rfl
  | .neg a => congrArg (-·) (fastEvalZ_eq v a)
  | .add a b => congrArg₂ (· + ·) (fastEvalZ_eq v a) (fastEvalZ_eq v b)
  | .sub a b => congrArg₂ (· - ·) (fastEvalZ_eq v a) (fastEvalZ_eq v b)
  | .mul a b => congrArg₂ (· * ·) (fastEvalZ_eq v a) (fastEvalZ_eq v b)
  | .pow a n => congrArg (· ^ n) (fastEvalZ_eq v a)

def fastPairMul (p q : ℕ × ℕ) : ℕ × ℕ :=
  (Nat.add (Nat.mul p.1 q.1) (Nat.mul p.2 q.2), Nat.add (Nat.mul p.1 q.2) (Nat.mul p.2 q.1))

def fastPairPow (p : ℕ × ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | n + 1 => fastPairMul p (fastPairPow p n)

def fastSplitNat (v : ℕ → ℕ) : Expr → ℕ × ℕ
  | .num (.ofNat n) => (n, 0)
  | .num (.negSucc n) => (0, Nat.add n 1)
  | .natCast n => (n, 0)
  | .intCast (.ofNat n) => (n, 0)
  | .intCast (.negSucc n) => (0, Nat.add n 1)
  | .var i => (v i, 0)
  | .neg a => let p := fastSplitNat v a; (p.2, p.1)
  | .add a b => let p := fastSplitNat v a; let q := fastSplitNat v b; (Nat.add p.1 q.1, Nat.add p.2 q.2)
  | .sub a b => let p := fastSplitNat v a; let q := fastSplitNat v b; (Nat.add p.1 q.2, Nat.add p.2 q.1)
  | .mul a b => fastPairMul (fastSplitNat v a) (fastSplitNat v b)
  | .pow a n => fastPairPow (fastSplitNat v a) n

lemma fastPairPow_eq (p : ℕ × ℕ) : ∀ n : ℕ, fastPairPow p n = pairPow p n
  | 0 => rfl
  | n + 1 => by simp [fastPairPow, pairPow, fastPairMul, pairMul, fastPairPow_eq p n]

lemma fastSplitNat_eq (v : ℕ → ℕ) : ∀ e : Expr, fastSplitNat v e = splitEval v e
  | .num (.ofNat _) => rfl
  | .num (.negSucc _) => rfl
  | .natCast _ => rfl
  | .intCast (.ofNat _) => rfl
  | .intCast (.negSucc _) => rfl
  | .var _ => rfl
  | .neg a => by simp [fastSplitNat, splitEval, fastSplitNat_eq v a]
  | .add a b => by simp [fastSplitNat, splitEval, fastSplitNat_eq v a, fastSplitNat_eq v b]
  | .sub a b => by simp [fastSplitNat, splitEval, fastSplitNat_eq v a, fastSplitNat_eq v b]
  | .mul a b => by simp [fastSplitNat, splitEval, fastPairMul, pairMul, fastSplitNat_eq v a, fastSplitNat_eq v b]
  | .pow a n => by simp [fastSplitNat, splitEval, fastSplitNat_eq v a, fastPairPow_eq]

def fastMassVal2 {k : ℕ} (gridDeg : Fin k → ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | i + 2 => if h : i < k then gridDeg ⟨i, h⟩ else 0

def fastPosMass2 {k : ℕ} (gridDeg : Fin k → ℕ) (e f : Expr) : ℕ :=
  Nat.add (fastSplitNat (fastMassVal2 gridDeg) e).1 (fastSplitNat (fastMassVal2 gridDeg) f).2

def fastNegMass2 {k : ℕ} (gridDeg : Fin k → ℕ) (e f : Expr) : ℕ :=
  Nat.add (fastSplitNat (fastMassVal2 gridDeg) f).1 (fastSplitNat (fastMassVal2 gridDeg) e).2

def checkGrid2 {k : ℕ} (d0 : ℕ) (gridDeg : Fin k → ℕ) (b : ℕ) (e f : Expr) : Bool :=
  let b0 : ℤ := Int.ofNat b
  let b1 : ℤ := Int.ofNat (Nat.pow b d0)
  allGrid gridDeg fun g =>
    let v : ℕ → ℤ := fun
      | 0 => b0
      | 1 => b1
      | i + 2 => if h : i < k then Int.ofNat (g ⟨i, h⟩) else 0
    decide (fastEvalZ v e = fastEvalZ v f)

theorem identity_of_grid2 {K : Type*} [CommRing K]
    {k : ℕ} (v : ℕ → K) (d0 d1 : ℕ) (gridDeg : Fin k → ℕ) (b : ℕ) (e f : Expr)
    (hb : 0 < b)
    (hve : varsInRange (2 + k) e = true) (hvf : varsInRange (2 + k) f = true)
    (hd0e : exprDeg 0 e < d0) (hd1e : exprDeg 1 e < d1)
    (hd0f : exprDeg 0 f < d0) (hd1f : exprDeg 1 f < d1)
    (hde_k : ∀ j : Fin k, exprDeg (2 + j.val) e ≤ gridDeg j)
    (hdf_k : ∀ j : Fin k, exprDeg (2 + j.val) f ≤ gridDeg j)
    (hp : fastPosMass2 gridDeg e f < b)
    (hn : fastNegMass2 gridDeg e f < b)
    (hgrid : checkGrid2 d0 gridDeg b e f = true) :
    ringEval v e = ringEval v f := by
  let bound : Fin 2 → ℕ := ![d0, d1]
  have hst0 : stride bound 0 = 1 := by simp [stride]
  have hst1 : stride bound 1 = d0 := by simp [stride, bound]
  have hmv : fastMassVal2 gridDeg = gridMassVal (m := 2) gridDeg := by
    funext i
    match i with
    | 0 => rfl
    | 1 => rfl
    | i + 2 =>
      dsimp only [fastMassVal2, gridMassVal]
      have h1 : ¬ (i + 2 < 2) := by omega
      rw [dite_eq_right h1]
      by_cases h2 : i < k
      · have h3 : i + 2 < 2 + k := by omega
        simp [h2, h3]
      · have h3 : ¬ (i + 2 < 2 + k) := by omega
        simp [h2, h3]
  apply identity_of_grid_kronecker (m := 2) (k := k) v bound gridDeg b e f hb hve hvf
  · intro i; fin_cases i <;> simpa [bound]
  · intro i; fin_cases i <;> simpa [bound]
  · exact hde_k
  · exact hdf_k
  · simpa [positiveMassGrid, fastPosMass2, fastSplitNat_eq, hmv] using hp
  · simpa [negativeMassGrid, fastNegMass2, fastSplitNat_eq, hmv] using hn
  · -- Show checkGrid bound gridDeg b e f = true from checkGrid2!
    let vg (g : Fin k → ℕ) : ℕ → ℤ := fun
      | 0 => Int.ofNat b
      | 1 => Int.ofNat (Nat.pow b d0)
      | i + 2 => if h : i < k then Int.ofNat (g ⟨i, h⟩) else 0
    have hP (g : Fin k → ℕ) :
        decide (fastEvalZ (vg g) e = fastEvalZ (vg g) f) =
        decide (ringEval (fun i => (gridVal bound b g i : ℤ)) e =
          ringEval (fun i => (gridVal bound b g i : ℤ)) f) := by
      have hv_eq : vg g = (fun i => (gridVal bound b g i : ℤ)) := by
        funext i
        match i with
        | 0 => simp [vg, gridVal, hst0]
        | 1 => simp [vg, gridVal, hst1]
        | i + 2 =>
          dsimp only [vg, gridVal]
          have h1 : ¬ (i + 2 < 2) := by omega
          rw [dite_eq_right h1]
          by_cases h2 : i < k
          · have h3 : i + 2 < 2 + k := by omega
            simp [h2, h3]
          · have h3 : ¬ (i + 2 < 2 + k) := by omega
            simp [h2, h3]
      rw [fastEvalZ_eq, fastEvalZ_eq, hv_eq]
    have hall : ∀ {r : ℕ} (d : Fin r → ℕ) (P Q : (Fin r → ℕ) → Bool),
        (∀ g, P g = Q g) → allGrid d P = allGrid d Q := by
      intro r; induction r with
      | zero => intro d P Q h; exact h Fin.elim0
      | succ r ih =>
        intro d P Q h
        simp only [allGrid]
        congr 1; funext a
        exact ih _ _ _ (fun g => h (Fin.cons a g))
    rw [checkGrid, ← hall gridDeg _ _ hP]
    exact hgrid

/-! Fast 2-variable `(S, Q)` and 3-variable `(S, Q, T)` Kronecker checkers, plus sparse
`(x, y)`-bivariate `Biv` identity theorem (`biv_denote_eq_of_kronecker3`) with precomputed
base powers and zero support-alignment requirements (`merge 512 p (negBiv q)`). -/

open PolynomialEncoding.BivariateExpressions

def fastMass2 (e f : Expr) : ℕ × ℕ :=
  let pe := fastSplitNat (fun | 0 | 1 => 1 | _ => 0) e
  let pf := fastSplitNat (fun | 0 | 1 => 1 | _ => 0) f
  (Nat.add pe.1 pf.2, Nat.add pf.1 pe.2)

def checkKronecker2 (d0 d1 b : ℕ) (e f : Expr) : Bool :=
  let b0 : ℤ := Int.ofNat b
  let b1 : ℤ := Int.ofNat (Nat.pow b d0)
  let m := fastMass2 e f
  decide (0 < b) && varsInRange 2 e && varsInRange 2 f &&
  decide (exprDeg 0 e < d0) && decide (exprDeg 1 e < d1) &&
  decide (exprDeg 0 f < d0) && decide (exprDeg 1 f < d1) &&
  decide (m.1 < b) && decide (m.2 < b) &&
  decide (fastEvalZ (fun | 0 => b0 | 1 => b1 | _ => 0) e =
          fastEvalZ (fun | 0 => b0 | 1 => b1 | _ => 0) f)

theorem identity_of_kronecker2 {K : Type*} [CommRing K]
    (v : ℕ → K) (d0 d1 b : ℕ) (e f : Expr)
    (hchk : checkKronecker2 d0 d1 b e f = true) :
    ringEval v e = ringEval v f := by
  dsimp only [checkKronecker2, fastMass2] at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨⟨⟨⟨⟨hb, hve⟩, hvf⟩, hd0e⟩, hd1e⟩, hd0f⟩, hd1f⟩, hp⟩, hn⟩, hnum⟩
  let bound : Fin 2 → ℕ := ![d0, d1]
  have hst0 : stride bound 0 = 1 := by simp [stride]
  have hst1 : stride bound 1 = d0 := by simp [stride, bound]
  have hv1 : (fun | 0 | 1 => (1 : ℕ) | _ => 0) = (fun i => if i < 2 then 1 else 0) := by
    funext i; match i with | 0 | 1 => rfl | i + 2 => simp
  have hvB : (fun | 0 => Int.ofNat b | 1 => Int.ofNat (Nat.pow b d0) | _ => (0 : ℤ)) =
      (fun i => (value bound b i : ℤ)) := by
    funext i; match i with
    | 0 => simp [value, hst0]
    | 1 => simp [value, hst1]
    | i + 2 => simp [value]
  apply identity_of_kronecker (n := 2) v bound b e f hb hve hvf
  · intro i; fin_cases i <;> simpa [bound]
  · intro i; fin_cases i <;> simpa [bound]
  · simpa [positiveMass, fastSplitNat_eq, hv1] using hp
  · simpa [negativeMass, fastSplitNat_eq, hv1] using hn
  · simpa only [fastEvalZ_eq, hvB] using hnum

def fastMass3 (e f : Expr) : ℕ × ℕ :=
  let pe := fastSplitNat (fun | 0 | 1 | 2 => 1 | _ => 0) e
  let pf := fastSplitNat (fun | 0 | 1 | 2 => 1 | _ => 0) f
  (Nat.add pe.1 pf.2, Nat.add pf.1 pe.2)

def checkKronecker3With (d0 d1 d2 b : ℕ) (b0 b1 b2 : ℤ) (e f : Expr) : Bool :=
  let m := fastMass3 e f
  decide (0 < b) && varsInRange 3 e && varsInRange 3 f &&
  decide (exprDeg 0 e < d0) && decide (exprDeg 1 e < d1) && decide (exprDeg 2 e < d2) &&
  decide (exprDeg 0 f < d0) && decide (exprDeg 1 f < d1) && decide (exprDeg 2 f < d2) &&
  decide (m.1 < b) && decide (m.2 < b) &&
  decide (fastEvalZ (fun | 0 => b0 | 1 => b1 | 2 => b2 | _ => 0) e =
          fastEvalZ (fun | 0 => b0 | 1 => b1 | 2 => b2 | _ => 0) f)

def checkKronecker3 (d0 d1 d2 b : ℕ) (e f : Expr) : Bool :=
  let b0 : ℤ := Int.ofNat b
  let b1 : ℤ := Int.ofNat (Nat.pow b d0)
  let b2 : ℤ := Int.ofNat (Nat.pow b (Nat.mul d0 d1))
  checkKronecker3With d0 d1 d2 b b0 b1 b2 e f

theorem identity_of_kronecker3With {K : Type*} [CommRing K]
    (v : ℕ → K) (d0 d1 d2 b : ℕ) (e f : Expr)
    (hchk : checkKronecker3With d0 d1 d2 b (Int.ofNat b) (Int.ofNat (Nat.pow b d0))
      (Int.ofNat (Nat.pow b (Nat.mul d0 d1))) e f = true) :
    ringEval v e = ringEval v f := by
  dsimp only [checkKronecker3With, fastMass3] at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb, hve⟩, hvf⟩, hd0e⟩, hd1e⟩, hd2e⟩, hd0f⟩, hd1f⟩, hd2f⟩, hp⟩, hn⟩, hnum⟩
  let bound : Fin 3 → ℕ := ![d0, d1, d2]
  have hst0 : stride bound 0 = 1 := by simp [stride]
  have hst1 : stride bound 1 = d0 := by simp [stride, bound]
  have hst2 : stride bound 2 = d0 * d1 := by simp [stride, bound, Fin.prod_univ_three]
  have hv1 : (fun | 0 | 1 | 2 => (1 : ℕ) | _ => 0) = (fun i => if i < 3 then 1 else 0) := by
    funext i; match i with | 0 | 1 | 2 => rfl | i + 3 => simp
  let vB : ℕ → ℤ := fun
    | 0 => Int.ofNat b
    | 1 => Int.ofNat (Nat.pow b d0)
    | 2 => Int.ofNat (Nat.pow b (Nat.mul d0 d1))
    | _ => 0
  have hvB : vB = (fun i => (value bound b i : ℤ)) := by
    funext i; match i with
    | 0 => simp [vB, value, hst0]
    | 1 => simp [vB, value, hst1]
    | 2 => simp [vB, value, hst2]
    | i + 3 => simp [vB, value]
  apply identity_of_kronecker (n := 3) v bound b e f hb hve hvf
  · intro i; fin_cases i <;> simpa [bound]
  · intro i; fin_cases i <;> simpa [bound]
  · simpa [positiveMass, fastSplitNat_eq, hv1] using hp
  · simpa [negativeMass, fastSplitNat_eq, hv1] using hn
  · change fastEvalZ vB e = fastEvalZ vB f at hnum
    simpa only [fastEvalZ_eq, hvB] using hnum

theorem identity_of_kronecker3 {K : Type*} [CommRing K]
    (v : ℕ → K) (d0 d1 d2 b : ℕ) (e f : Expr)
    (hchk : checkKronecker3 d0 d1 d2 b e f = true) :
    ringEval v e = ringEval v f :=
  identity_of_kronecker3With v d0 d1 d2 b e f hchk

def negBiv : Biv → Biv
  | .nil => .nil
  | .cons a i j p => .cons (.neg a) i j (negBiv p)

lemma negBiv_denote {K : Type*} [CommRing K] (v : ℕ → K) (x y : K) (p : Biv) :
    denote v x y (negBiv p) = -denote v x y p := by
  induction p with
  | nil => simp [negBiv, denote]
  | cons a i j p ih => simp only [negBiv, denote, ringEval, ih]; ring

def checkBivZero3Aux (d0 d1 d2 b : ℕ) (b0 b1 b2 : ℤ) : Biv → Bool
  | .nil => true
  | .cons a _ _ p =>
    checkKronecker3With d0 d1 d2 b b0 b1 b2 a (.num 0) &&
    checkBivZero3Aux d0 d1 d2 b b0 b1 b2 p

def checkBivEq3 (d0 d1 d2 b : ℕ) (p q : Biv) : Bool :=
  let b0 : ℤ := Int.ofNat b
  let b1 : ℤ := Int.ofNat (Nat.pow b d0)
  let b2 : ℤ := Int.ofNat (Nat.pow b (Nat.mul d0 d1))
  checkBivZero3Aux d0 d1 d2 b b0 b1 b2 (merge 512 p (negBiv q))

lemma biv_zero_of_checkBivZero3Aux {K : Type*} [CommRing K]
    (v : ℕ → K) (x y : K) (d0 d1 d2 b : ℕ) (r : Biv)
    (h : checkBivZero3Aux d0 d1 d2 b (Int.ofNat b) (Int.ofNat (Nat.pow b d0))
      (Int.ofNat (Nat.pow b (Nat.mul d0 d1))) r = true) :
    denote v x y r = 0 := by
  induction r with
  | nil => rfl
  | cons a i j p ih =>
    simp only [checkBivZero3Aux, Bool.and_eq_true] at h
    have ha : ringEval v a = 0 := by
      simpa [ringEval] using identity_of_kronecker3With v d0 d1 d2 b a (.num 0) h.1
    simp [denote, ha, ih h.2]

theorem biv_denote_eq_of_kronecker3 {K : Type*} [CommRing K]
    (v : ℕ → K) (x y : K) (d0 d1 d2 b : ℕ) (p q : Biv)
    (hchk : checkBivEq3 d0 d1 d2 b p q = true) :
    denote v x y p = denote v x y q := by
  have hz := biv_zero_of_checkBivZero3Aux v x y d0 d1 d2 b (merge 512 p (negBiv q)) hchk
  rw [merge_denote, negBiv_denote] at hz
  linear_combination hz


/-! ### Part 2: `PolyOps`, `PB`, `PolyOpsRel`, and Factored 3-Variable Hybrid Checkers -/

/-- Polymorphic ring-operation backend allowing one polynomial algorithm to execute over
`ℤ`, bound-tracking records `PB`, `Unit` (for shape/length checks), `MvPolynomial (Fin 3) ℤ`,
or any commutative ring `R`. -/
structure PolyOps (α : Type*) where
  zero : α
  ofInt : ℤ → α
  add : α → α → α
  sub : α → α → α
  neg : α → α
  mul : α → α → α
  pow : α → ℕ → α

/-- Degree bounds `(d0, d1, d2)` and coefficient `ℓ¹`-norm bound `M` for a 3-variable polynomial. -/
structure PB where
  dS : ℕ
  dQ : ℕ
  dT : ℕ
  M : ℕ
  deriving DecidableEq

def intOps : PolyOps ℤ where
  zero := 0
  ofInt n := n
  add a b := Int.add a b
  sub a b := Int.sub a b
  neg a := Int.neg a
  mul a b := Int.mul a b
  pow a k := Int.pow a k

def pbOps : PolyOps PB where
  zero := ⟨0, 0, 0, 0⟩
  ofInt n := ⟨0, 0, 0, Int.natAbs n⟩
  add a b := ⟨Nat.max a.dS b.dS, Nat.max a.dQ b.dQ, Nat.max a.dT b.dT, Nat.add a.M b.M⟩
  sub a b := ⟨Nat.max a.dS b.dS, Nat.max a.dQ b.dQ, Nat.max a.dT b.dT, Nat.add a.M b.M⟩
  neg a := a
  mul a b := ⟨Nat.add a.dS b.dS, Nat.add a.dQ b.dQ, Nat.add a.dT b.dT, Nat.mul a.M b.M⟩
  pow a k := ⟨Nat.mul a.dS k, Nat.mul a.dQ k, Nat.mul a.dT k, Nat.pow a.M k⟩

def unitOps : PolyOps Unit where
  zero := ()
  ofInt _ := ()
  add _ _ := ()
  sub _ _ := ()
  neg _ := ()
  mul _ _ := ()
  pow _ _ := ()

abbrev P3Z := MvPolynomial (Fin 3) ℤ

def ringOps (R : Type*) [CommRing R] : PolyOps R where
  zero := 0
  ofInt n := (n : R)
  add a b := a + b
  sub a b := a - b
  neg a := -a
  mul a b := a * b
  pow a k := a ^ k

abbrev poly3Ops : PolyOps P3Z := ringOps P3Z

/-- Logical relation between two `PolyOps` backends preserving all ring operations. -/
structure PolyOpsRel {α β : Type*} (o1 : PolyOps α) (o2 : PolyOps β) (R : α → β → Prop) : Prop where
  rel_zero : R o1.zero o2.zero
  rel_ofInt : ∀ n, R (o1.ofInt n) (o2.ofInt n)
  rel_add : ∀ {a1 a2 b1 b2}, R a1 b1 → R a2 b2 → R (o1.add a1 a2) (o2.add b1 b2)
  rel_sub : ∀ {a1 a2 b1 b2}, R a1 b1 → R a2 b2 → R (o1.sub a1 a2) (o2.sub b1 b2)
  rel_neg : ∀ {a b}, R a b → R (o1.neg a) (o2.neg b)
  rel_mul : ∀ {a1 a2 b1 b2}, R a1 b1 → R a2 b2 → R (o1.mul a1 a2) (o2.mul b1 b2)
  rel_pow : ∀ {a b} k, R a b → R (o1.pow a k) (o2.pow b k)

/-- Explicit sharing combinator preserving common subexpressions across relational transfer
without triggering exponential let-unfolding in the kernel. -/
def letB {α β : Type*} (x : α) (f : α → β) : β := f x

lemma letB_rel {α₁ α₂ β₁ β₂ : Type*} {Ra : α₁ → α₂ → Prop} {Rb : β₁ → β₂ → Prop}
    {x₁ : α₁} {x₂ : α₂} {f₁ : α₁ → β₁} {f₂ : α₂ → β₂}
    (hx : Ra x₁ x₂) (hf : ∀ {a₁ a₂}, Ra a₁ a₂ → Rb (f₁ a₁) (f₂ a₂)) :
    Rb (letB x₁ f₁) (letB x₂ f₂) := hf hx

lemma letB_step {α β : Type*} {x y : α} {f : α → β} {z : β} (hxy : x = y) (hf : f y = z) :
    letB x f = z := by rw [letB, hxy, hf]

lemma letB_intro {α β : Type*} {P : β → Prop} {x : α} {f : α → β}
    (h : ∀ a, a = x → P (f a)) : P (letB x f) := h x rfl

def v3Int (s q t : ℤ) : Fin 3 → ℤ
  | 0 => s
  | 1 => q
  | 2 => t

lemma poly3ToIntRel (s q t : ℤ) :
    PolyOpsRel poly3Ops intOps (fun p z => MvPolynomial.eval (v3Int s q t) p = z) where
  rel_zero := by simp [poly3Ops, ringOps, intOps]
  rel_ofInt n := by simp [poly3Ops, ringOps, intOps]
  rel_add h1 h2 := by simp [poly3Ops, ringOps, intOps, h1, h2]
  rel_sub h1 h2 := by simp [poly3Ops, ringOps, intOps, h1, h2]; rfl
  rel_neg h := by simp [poly3Ops, ringOps, intOps, h]; rfl
  rel_mul h1 h2 := by simp [poly3Ops, ringOps, intOps, h1, h2]
  rel_pow k h := by simp [poly3Ops, ringOps, intOps, h]

lemma poly3ToRingRel {R : Type*} [CommRing R] (v : Fin 3 → R) :
    PolyOpsRel poly3Ops (ringOps R)
      (fun p x => MvPolynomial.eval₂Hom (Int.castRingHom R) v p = x) where
  rel_zero := by simp [poly3Ops, ringOps]
  rel_ofInt n := by simp [poly3Ops, ringOps]
  rel_add h1 h2 := by dsimp only [poly3Ops, ringOps]; rw [map_add, h1, h2]
  rel_sub h1 h2 := by dsimp only [poly3Ops, ringOps]; rw [map_sub, h1, h2]
  rel_neg h := by dsimp only [poly3Ops, ringOps]; rw [map_neg, h]
  rel_mul h1 h2 := by dsimp only [poly3Ops, ringOps]; rw [map_mul, h1, h2]
  rel_pow k h := by dsimp only [poly3Ops, ringOps]; rw [map_pow, h]

def evalQT (q t : ℤ) : P3Z →+* Polynomial ℤ :=
  MvPolynomial.eval₂Hom Polynomial.C (fun i => match i with
    | 0 => Polynomial.X
    | 1 => Polynomial.C q
    | 2 => Polynomial.C t)

lemma eval_evalQT (p : P3Z) (s q t : ℤ) :
    (evalQT q t p).eval s = MvPolynomial.eval (v3Int s q t) p := by
  induction p using MvPolynomial.induction_on' with
  | add p1 p2 h1 h2 => simp only [map_add, Polynomial.eval_add, h1, h2]
  | monomial m c =>
    simp only [evalQT, MvPolynomial.eval₂Hom_monomial, MvPolynomial.eval_monomial,
      Polynomial.eval_mul, Polynomial.eval_C, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Fin.prod_univ_three, Polynomial.eval_pow, Polynomial.eval_X, v3Int]

/-- Coefficient `ℓ¹`-norm of an integer polynomial. -/
def polyL1 (f : Polynomial ℤ) : ℕ :=
  ∑ i ∈ f.support, (f.coeff i).natAbs

lemma polyL1_eq_sum_range (f : Polynomial ℤ) (N : ℕ) (hN : ∀ i ∈ f.support, i < N) :
    polyL1 f = ∑ i ∈ Finset.range N, (f.coeff i).natAbs := by
  unfold polyL1
  apply Finset.sum_subset
  · intro i hi; exact Finset.mem_range.mpr (hN i hi)
  · intro i _ hi
    have h0 : f.coeff i = 0 := by simpa [Polynomial.mem_support_iff] using hi
    simp [h0]

lemma polyL1_zero : polyL1 0 = 0 := by simp [polyL1]

lemma polyL1_C (c : ℤ) : polyL1 (Polynomial.C c) = c.natAbs := by
  by_cases hc : c = 0
  · subst hc; simp [polyL1]
  · simp only [polyL1, Polynomial.support_C hc, Finset.sum_singleton, Polynomial.coeff_C_zero]

lemma polyL1_X : polyL1 Polynomial.X = 1 := by
  rw [polyL1_eq_sum_range Polynomial.X 2 (fun i hi => by
    have : i = 1 := by simpa [Polynomial.support_X] using hi
    omega)]
  simp [Finset.sum_range_succ]

lemma polyL1_neg (f : Polynomial ℤ) : polyL1 (-f) = polyL1 f := by
  simp [polyL1, Polynomial.support_neg]

lemma polyL1_add (f g : Polynomial ℤ) : polyL1 (f + g) ≤ polyL1 f + polyL1 g := by
  set N := max f.natDegree g.natDegree + 1
  have hf : ∀ i ∈ f.support, i < N := fun i hi => Nat.lt_succ_of_le ((Polynomial.le_natDegree_of_mem_supp i hi).trans (le_max_left _ _))
  have hg : ∀ i ∈ g.support, i < N := fun i hi => Nat.lt_succ_of_le ((Polynomial.le_natDegree_of_mem_supp i hi).trans (le_max_right _ _))
  have hfg : ∀ i ∈ (f + g).support, i < N := fun i hi => by
    rcases Finset.mem_union.mp (Polynomial.support_add hi) with h | h
    · exact hf i h
    · exact hg i h
  rw [polyL1_eq_sum_range (f + g) N hfg, polyL1_eq_sum_range f N hf, polyL1_eq_sum_range g N hg,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by rw [Polynomial.coeff_add]; exact Int.natAbs_add_le _ _

lemma polyL1_sum_le {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℤ) :
    polyL1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, polyL1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polyL1_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (polyL1_add _ _).trans (Nat.add_le_add_left ih _)

lemma polyL1_C_mul (c : ℤ) (g : Polynomial ℤ) :
    polyL1 (Polynomial.C c * g) = c.natAbs * polyL1 g := by
  set N := g.natDegree + 1
  have hg : ∀ i ∈ g.support, i < N := fun i hi => Nat.lt_succ_of_le (Polynomial.le_natDegree_of_mem_supp i hi)
  have hcg : ∀ i ∈ (Polynomial.C c * g).support, i < N := fun i hi => by
    have h0 : (Polynomial.C c * g).coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
    rw [Polynomial.coeff_C_mul] at h0
    exact hg i (Polynomial.mem_support_iff.mpr (right_ne_zero_of_mul h0))
  rw [polyL1_eq_sum_range (Polynomial.C c * g) N hcg, polyL1_eq_sum_range g N hg, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Polynomial.coeff_C_mul, Int.natAbs_mul]

lemma polyL1_X_pow_mul (n : ℕ) (g : Polynomial ℤ) :
    polyL1 (Polynomial.X ^ n * g) = polyL1 g := by
  set N := g.natDegree + 1
  have hg : ∀ i ∈ g.support, i < N := fun i hi => Nat.lt_succ_of_le (Polynomial.le_natDegree_of_mem_supp i hi)
  have hxg : ∀ i ∈ (Polynomial.X ^ n * g).support, i < n + N := fun i hi => by
    have hle := Polynomial.le_natDegree_of_mem_supp i hi
    have hdeg := (Polynomial.natDegree_mul_le (p := (Polynomial.X : Polynomial ℤ) ^ n) (q := g)).trans
      (Nat.add_le_add_right (Polynomial.natDegree_X_pow_le n) _)
    omega
  rw [polyL1_eq_sum_range (Polynomial.X ^ n * g) (n + N) hxg, polyL1_eq_sum_range g N hg,
    Finset.sum_range_add]
  have hlo : ∑ x ∈ Finset.range n, ((Polynomial.X ^ n * g).coeff x).natAbs = 0 := by
    apply Finset.sum_eq_zero; intro x hx
    rw [Finset.mem_range] at hx
    rw [Polynomial.coeff_X_pow_mul', ite_eq_right (by omega)]; rfl
  rw [hlo, zero_add]
  apply Finset.sum_congr rfl; intro x _
  rw [add_comm, Polynomial.coeff_X_pow_mul]

lemma polyL1_mul (f g : Polynomial ℤ) : polyL1 (f * g) ≤ polyL1 f * polyL1 g := by
  conv_lhs => rw [f.as_sum_support_C_mul_X_pow]
  rw [Finset.sum_mul]
  refine (polyL1_sum_le _ _).trans ?_
  rw [polyL1, Finset.sum_mul]
  apply Finset.sum_le_sum; intro i _
  rw [mul_assoc, polyL1_C_mul, polyL1_X_pow_mul]

lemma polyL1_pow (f : Polynomial ℤ) (k : ℕ) : polyL1 (f ^ k) ≤ (polyL1 f) ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, ← Polynomial.C_1, polyL1_C]; rfl
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (polyL1_mul _ _).trans (Nat.mul_le_mul ih le_rfl)

def RespectsBound (Qmax Tmax : ℕ) (p : P3Z) (b : PB) : Prop :=
  (∀ m ∈ p.support, m 0 ≤ b.dS ∧ m 1 ≤ b.dQ ∧ m 2 ≤ b.dT) ∧
  (∀ q t : ℤ, q.natAbs ≤ Qmax → t.natAbs ≤ Tmax → polyL1 (evalQT q t p) ≤ b.M)

lemma respectsBoundRel (Qmax Tmax : ℕ) :
    PolyOpsRel poly3Ops pbOps (RespectsBound Qmax Tmax) where
  rel_zero := ⟨fun m hm => by simp [poly3Ops, ringOps] at hm,
    fun _ _ _ _ => by simp [poly3Ops, ringOps, pbOps, polyL1_zero]⟩
  rel_ofInt n := ⟨fun m hm => by
      have hm0 : m = 0 := by
        by_contra hne
        have hC : (n : P3Z) = MvPolynomial.C n := (map_intCast (MvPolynomial.C : ℤ →+* P3Z) n).symm
        exact (MvPolynomial.mem_support_iff.mp hm)
          (by dsimp only [poly3Ops, ringOps]; rw [hC, MvPolynomial.coeff_C, ite_eq_right (Ne.symm hne)])
      subst hm0; simp [pbOps],
    fun q t _ _ => by
      have hC : (n : P3Z) = MvPolynomial.C n := (map_intCast (MvPolynomial.C : ℤ →+* P3Z) n).symm
      dsimp only [poly3Ops, ringOps, pbOps]
      rw [hC, evalQT, MvPolynomial.eval₂Hom_C, polyL1_C]⟩
  rel_add h1 h2 := ⟨fun m hm => by
      rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
      · obtain ⟨a, b, c⟩ := h1.1 m h
        exact ⟨a.trans (le_max_left _ _), b.trans (le_max_left _ _), c.trans (le_max_left _ _)⟩
      · obtain ⟨a, b, c⟩ := h2.1 m h
        exact ⟨a.trans (le_max_right _ _), b.trans (le_max_right _ _), c.trans (le_max_right _ _)⟩,
    fun q t hq ht => by
      simp only [poly3Ops, ringOps, pbOps, map_add]
      exact (polyL1_add _ _).trans (Nat.add_le_add (h1.2 q t hq ht) (h2.2 q t hq ht))⟩
  rel_sub h1 h2 := ⟨fun m hm => by
      dsimp only [poly3Ops, ringOps] at hm
      rw [sub_eq_add_neg] at hm
      rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
      · obtain ⟨a, b, c⟩ := h1.1 m h
        exact ⟨a.trans (le_max_left _ _), b.trans (le_max_left _ _), c.trans (le_max_left _ _)⟩
      · rw [MvPolynomial.support_neg] at h
        obtain ⟨a, b, c⟩ := h2.1 m h
        exact ⟨a.trans (le_max_right _ _), b.trans (le_max_right _ _), c.trans (le_max_right _ _)⟩,
    fun q t hq ht => by
      simp only [poly3Ops, ringOps, pbOps, map_sub]
      rw [sub_eq_add_neg]
      exact (polyL1_add _ _).trans (by rw [polyL1_neg]; exact Nat.add_le_add (h1.2 q t hq ht) (h2.2 q t hq ht))⟩
  rel_neg h := ⟨fun m hm => h.1 m (by simpa [poly3Ops, ringOps] using hm),
    fun q t hq ht => by simp only [poly3Ops, ringOps, pbOps, map_neg, polyL1_neg]; exact h.2 q t hq ht⟩
  rel_mul h1 h2 := ⟨fun m hm => by
      rcases Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm) with ⟨m1, hm1, m2, hm2, rfl⟩
      obtain ⟨a1, b1, c1⟩ := h1.1 m1 hm1
      obtain ⟨a2, b2, c2⟩ := h2.1 m2 hm2
      exact ⟨Nat.add_le_add a1 a2, Nat.add_le_add b1 b2, Nat.add_le_add c1 c2⟩,
    fun q t hq ht => by
      simp only [poly3Ops, ringOps, pbOps, map_mul]
      exact (polyL1_mul _ _).trans (Nat.mul_le_mul (h1.2 q t hq ht) (h2.2 q t hq ht))⟩
  rel_pow k h := by
    induction k with
    | zero =>
      refine ⟨fun m hm => by
        have : m = 0 := by simpa [poly3Ops, ringOps, MvPolynomial.support_one] using hm
        subst this; simp [pbOps],
        fun q t _ _ => by simp only [poly3Ops, ringOps, pbOps, pow_zero, map_one]; rw [← Polynomial.C_1, polyL1_C]; rfl⟩
    | succ k ih =>
      refine ⟨fun m hm => by
        rw [show poly3Ops.pow _ (k + 1) = _ ^ k * _ from pow_succ _ k] at hm
        rcases Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm) with ⟨m1, hm1, m2, hm2, rfl⟩
        obtain ⟨a1, b1, c1⟩ := ih.1 m1 hm1
        obtain ⟨a2, b2, c2⟩ := h.1 m2 hm2
        simp only [pbOps]
        exact ⟨Nat.add_le_add a1 a2, Nat.add_le_add b1 b2, Nat.add_le_add c1 c2⟩,
        fun q t hq ht => by
          simp only [poly3Ops, ringOps, pbOps, map_pow]
          exact (polyL1_pow _ _).trans (Nat.pow_le_pow_left (h.2 q t hq ht) _)⟩

lemma respectsBound_X0 (Qmax Tmax : ℕ) :
    RespectsBound Qmax Tmax (MvPolynomial.X 0) ⟨1, 0, 0, 1⟩ := by
  refine ⟨fun m hm => by
    have : m = Finsupp.single 0 1 := by simpa [MvPolynomial.support_X] using hm
    subst this; simp,
    fun q t _ _ => by simp [evalQT, polyL1_X]⟩

lemma respectsBound_X1 (Qmax Tmax : ℕ) :
    RespectsBound Qmax Tmax (MvPolynomial.X 1) ⟨0, 1, 0, Qmax⟩ := by
  refine ⟨fun m hm => by
    have : m = Finsupp.single 1 1 := by simpa [MvPolynomial.support_X] using hm
    subst this; simp,
    fun q t hq _ => by simp only [evalQT, MvPolynomial.eval₂Hom_X', polyL1_C, hq]⟩

lemma respectsBound_X2 (Qmax Tmax : ℕ) :
    RespectsBound Qmax Tmax (MvPolynomial.X 2) ⟨0, 0, 1, Tmax⟩ := by
  refine ⟨fun m hm => by
    have : m = Finsupp.single 2 1 := by simpa [MvPolynomial.support_X] using hm
    subst this; simp,
    fun q t _ ht => by simp only [evalQT, MvPolynomial.eval₂Hom_X', polyL1_C, ht]⟩

lemma natDegree_divX_le_pred {R : Type*} [Semiring R] (g : R[X]) :
    g.divX.natDegree ≤ g.natDegree - 1 := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun i hi => ?_
  rw [Polynomial.coeff_divX]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

lemma poly_eq_zero_of_eval_base (f : Polynomial ℤ) (B : ℕ)
    (hM : polyL1 f < B) (hev : f.eval (B : ℤ) = 0) : f = 0 := by
  suffices h : ∀ n (g : Polynomial ℤ), g.natDegree ≤ n → polyL1 g < B → g.eval (B : ℤ) = 0 → g = 0 from
    h f.natDegree f le_rfl hM hev
  intro n
  induction n with
  | zero =>
    intro g hdeg hMg hevg
    rw [Polynomial.eq_C_of_natDegree_le_zero hdeg] at hevg ⊢
    simp only [Polynomial.eval_C] at hevg
    simp [hevg]
  | succ n ih =>
    intro g hdeg hMg hevg
    by_cases hg0 : g = 0
    · exact hg0
    · have hc0_le : (g.coeff 0).natAbs ≤ polyL1 g := by
        by_cases h0 : g.coeff 0 = 0
        · simp [h0]
        · unfold polyL1
          exact Finset.single_le_sum (f := fun i => (g.coeff i).natAbs) (fun _ _ => Nat.zero_le _)
            (Polynomial.mem_support_iff.mpr h0)
      have hsplit : g = Polynomial.C (g.coeff 0) + Polynomial.X * g.divX := by
        rw [add_comm]; exact (Polynomial.X_mul_divX_add g).symm
      have hev' : g.coeff 0 + (B : ℤ) * g.divX.eval (B : ℤ) = 0 := by
        have h := congrArg (fun p : Polynomial ℤ => p.eval (B : ℤ)) hsplit
        simp only [hevg, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X] at h
        exact h.symm
      have hdvdZ : (B : ℤ) ∣ g.coeff 0 := ⟨-g.divX.eval (B : ℤ), by linarith⟩
      have hdvdN : B ∣ (g.coeff 0).natAbs := Int.natCast_dvd.mp hdvdZ
      have hc0_abs : (g.coeff 0).natAbs = 0 := Nat.eq_zero_of_dvd_of_lt hdvdN (lt_of_le_of_lt hc0_le hMg)
      have hc0 : g.coeff 0 = 0 := Int.natAbs_eq_zero.mp hc0_abs
      rw [hc0, zero_add] at hev'
      have hB_ne : (B : ℤ) ≠ 0 := by omega
      have hdiv_ev : g.divX.eval (B : ℤ) = 0 := (mul_eq_zero.mp hev').resolve_left hB_ne
      have hdiv_L1 : polyL1 g.divX ≤ polyL1 g := by
        rw [polyL1_eq_sum_range g.divX g.natDegree (fun i hi => by
          have hlt := Polynomial.le_natDegree_of_mem_supp i hi
          have hle := natDegree_divX_le_pred g
          have hne : g.natDegree ≠ 0 := by
            intro hz
            have hgC := Polynomial.eq_C_of_natDegree_eq_zero hz
            rw [hgC, Polynomial.divX_C] at hi
            simp at hi
          omega),
          polyL1_eq_sum_range g (g.natDegree + 1) (fun i hi => Nat.lt_succ_of_le (Polynomial.le_natDegree_of_mem_supp i hi)),
          Finset.sum_range_succ']
        simp only [Polynomial.coeff_divX]
        exact Nat.le_add_right _ _
      have hdiv_deg : g.divX.natDegree ≤ n := (natDegree_divX_le_pred g).trans (by omega)
      have hdiv0 : g.divX = 0 := ih g.divX hdiv_deg (lt_of_le_of_lt hdiv_L1 hMg) hdiv_ev
      rw [hsplit, hc0, hdiv0]; simp

/-- Soundness of 1D Kronecker (in variable `0`) × 2D grid (in variables `1, 2`) vanishing check. -/
theorem mvPoly3_eq_zero_of_kronecker_grid (p : P3Z) (b : PB) (Qmax Tmax B : ℕ)
    (Q_pts T_pts : Finset ℤ)
    (hR : RespectsBound Qmax Tmax p b)
    (hQ_deg : b.dQ < Q_pts.card) (hQ_bd : ∀ q ∈ Q_pts, q.natAbs ≤ Qmax)
    (hT_deg : b.dT < T_pts.card) (hT_bd : ∀ t ∈ T_pts, t.natAbs ≤ Tmax)
    (hB : b.M < B)
    (hev : ∀ q ∈ Q_pts, ∀ t ∈ T_pts, MvPolynomial.eval (v3Int (B : ℤ) q t) p = 0) :
    p = 0 := by
  have hevalQT_zero : ∀ q ∈ Q_pts, ∀ t ∈ T_pts, evalQT q t p = 0 := fun q hq t ht => by
    apply poly_eq_zero_of_eval_base (evalQT q t p) B
    · exact lt_of_le_of_lt (hR.2 q t (hQ_bd q hq) (hT_bd t ht)) hB
    · rw [eval_evalQT]; exact hev q hq t ht
  let polyT_of (i : ℕ) (q : ℤ) : Polynomial ℤ :=
    ∑ m ∈ p.support.filter (fun m => m 0 = i), Polynomial.C (p.coeff m * q ^ m 1) * Polynomial.X ^ m 2
  have hpolyT_eval (i : ℕ) (q t : ℤ) : (polyT_of i q).eval t = (evalQT q t p).coeff i := by
    conv_rhs => rw [p.as_sum]
    dsimp only [polyT_of]
    rw [Finset.sum_filter, show ∀ f : Polynomial ℤ, f.eval t = Polynomial.evalRingHom t f from fun _ => rfl,
      map_sum, map_sum, ← Polynomial.lcoeff_apply, map_sum]
    apply Finset.sum_congr rfl; intro m _
    simp only [Polynomial.coe_evalRingHom, Polynomial.lcoeff_apply, evalQT, MvPolynomial.eval₂Hom_monomial,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three]
    have hcoeff : (Polynomial.C (p.coeff m) * (Polynomial.X ^ m 0 * Polynomial.C q ^ m 1 * Polynomial.C t ^ m 2)).coeff i =
        if m 0 = i then p.coeff m * q ^ m 1 * t ^ m 2 else 0 := by
      rw [show Polynomial.C (p.coeff m) * (Polynomial.X ^ m 0 * Polynomial.C q ^ m 1 * Polynomial.C t ^ m 2) =
          Polynomial.C (p.coeff m * q ^ m 1 * t ^ m 2) * Polynomial.X ^ m 0 by simp only [map_mul, map_pow]; ring]
      rw [Polynomial.coeff_C_mul_X_pow]
      by_cases h : m 0 = i
      · subst h; simp
      · simp [h, Ne.symm h]
    rw [hcoeff]
    split_ifs with h0
    · simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    · simp only [Polynomial.eval_zero]
  have hpolyT_zero (i : ℕ) (q : ℤ) (hq : q ∈ Q_pts) : polyT_of i q = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (polyT_of i q) T_pts
    · intro t ht; rw [hpolyT_eval, hevalQT_zero q hq t ht, Polynomial.coeff_zero]
    · refine lt_of_le_of_lt ?_ hT_deg
      refine (Polynomial.natDegree_sum_le _ _).trans ?_
      rw [Finset.fold_max_le]
      refine ⟨Nat.zero_le _, fun m hm => ?_⟩
      have hm' := (Finset.mem_filter.mp hm).1
      exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (hR.1 m hm').2.2
  let polyQ_of (i k : ℕ) : Polynomial ℤ :=
    ∑ m ∈ p.support.filter (fun m => m 0 = i ∧ m 2 = k), Polynomial.C (p.coeff m) * Polynomial.X ^ m 1
  have hpolyQ_eval (i k : ℕ) (q : ℤ) : (polyQ_of i k).eval q = (polyT_of i q).coeff k := by
    dsimp only [polyQ_of, polyT_of]
    rw [Finset.sum_filter, Finset.sum_filter,
      show ∀ f : Polynomial ℤ, f.eval q = Polynomial.evalRingHom q f from fun _ => rfl,
      map_sum, ← Polynomial.lcoeff_apply, map_sum]
    apply Finset.sum_congr rfl; intro m _
    simp only [Polynomial.coe_evalRingHom, Polynomial.lcoeff_apply]
    by_cases h0 : m 0 = i
    · by_cases h2 : m 2 = k
      · simp only [h0, h2, and_self, ↓reduceIte, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_pow, Polynomial.eval_X, Polynomial.coeff_C_mul_X_pow]
      · simp only [h0, h2, and_false, ↓reduceIte, Polynomial.eval_zero, Polynomial.coeff_C_mul_X_pow,
          ite_eq_right (Ne.symm h2)]
    · simp only [h0, false_and, ↓reduceIte, Polynomial.eval_zero, Polynomial.coeff_zero]
  have hpolyQ_zero (i k : ℕ) : polyQ_of i k = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (polyQ_of i k) Q_pts
    · intro q hq; rw [hpolyQ_eval, hpolyT_zero i q hq, Polynomial.coeff_zero]
    · refine lt_of_le_of_lt ?_ hQ_deg
      refine (Polynomial.natDegree_sum_le _ _).trans ?_
      rw [Finset.fold_max_le]
      refine ⟨Nat.zero_le _, fun m hm => ?_⟩
      have hm' := (Finset.mem_filter.mp hm).1
      exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (hR.1 m hm').2.1
  ext m
  have hcm : (polyQ_of (m 0) (m 2)).coeff (m 1) = p.coeff m := by
    dsimp only [polyQ_of]
    rw [Finset.sum_filter, ← Polynomial.lcoeff_apply, map_sum]
    have hterm : ∀ m' : Fin 3 →₀ ℕ,
        Polynomial.lcoeff ℤ (m 1) (if m' 0 = m 0 ∧ m' 2 = m 2 then Polynomial.C (p.coeff m') * Polynomial.X ^ m' 1 else 0) =
        if m' = m then p.coeff m' else 0 := fun m' => by
      simp only [Polynomial.lcoeff_apply]
      by_cases heq : m' = m
      · subst heq; simp
      · have hne : ¬(m' 0 = m 0 ∧ m' 2 = m 2 ∧ m 1 = m' 1) := by
          rintro ⟨h0, h2, h1⟩
          apply heq; ext j; fin_cases j
          · exact h0
          · exact h1.symm
          · exact h2
        by_cases h02 : m' 0 = m 0 ∧ m' 2 = m 2
        · have h1 : m 1 ≠ m' 1 := fun h => hne ⟨h02.1, h02.2, h⟩
          simp [heq, h02, h1]
        · simp [heq, h02]
    simp_rw [hterm]
    by_cases hm : m ∈ p.support
    · rw [Finset.sum_ite_eq' p.support m p.coeff, ite_eq_left hm]
    · rw [Finset.sum_ite_eq' p.support m p.coeff, ite_eq_right hm]
      symm; simpa [MvPolynomial.mem_support_iff] using hm
  rw [← hcm, hpolyQ_zero, Polynomial.coeff_zero]
  simp

def evalT2D (D : ℕ) (t : ℤ) : P3Z →+* Polynomial ℤ :=
  MvPolynomial.eval₂Hom Polynomial.C (fun i => match i with
    | 0 => Polynomial.X
    | 1 => Polynomial.X ^ D
    | 2 => Polynomial.C t)

lemma eval_evalT2D (D : ℕ) (p : P3Z) (B : ℕ) (t : ℤ) :
    (evalT2D D t p).eval (B : ℤ) = MvPolynomial.eval (v3Int (B : ℤ) ((B ^ D : ℕ) : ℤ) t) p := by
  induction p using MvPolynomial.induction_on' with
  | add p1 p2 h1 h2 => simp only [map_add, Polynomial.eval_add, h1, h2]
  | monomial m c =>
    simp only [evalT2D, MvPolynomial.eval₂Hom_monomial, MvPolynomial.eval_monomial,
      Polynomial.eval_mul, Polynomial.eval_C, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Fin.prod_univ_three, Polynomial.eval_pow, Polynomial.eval_X, v3Int, Nat.cast_pow]

def RespectsBound2D (D Tmax : ℕ) (p : P3Z) (b : PB) : Prop :=
  (∀ m ∈ p.support, m 0 ≤ b.dS ∧ m 1 ≤ b.dQ ∧ m 2 ≤ b.dT) ∧
  (∀ t : ℤ, t.natAbs ≤ Tmax → polyL1 (evalT2D D t p) ≤ b.M)

lemma respectsBound2DRel (D Tmax : ℕ) :
    PolyOpsRel poly3Ops pbOps (RespectsBound2D D Tmax) where
  rel_zero := ⟨fun m hm => by simp [poly3Ops, ringOps] at hm,
    fun _ _ => by simp [poly3Ops, ringOps, pbOps, polyL1_zero]⟩
  rel_ofInt n := ⟨fun m hm => by
      have hm0 : m = 0 := by
        by_contra hne
        have hC : (n : P3Z) = MvPolynomial.C n := (map_intCast (MvPolynomial.C : ℤ →+* P3Z) n).symm
        exact (MvPolynomial.mem_support_iff.mp hm)
          (by dsimp only [poly3Ops, ringOps]; rw [hC, MvPolynomial.coeff_C, ite_eq_right (Ne.symm hne)])
      subst hm0; simp [pbOps],
    fun t _ => by
      have hC : (n : P3Z) = MvPolynomial.C n := (map_intCast (MvPolynomial.C : ℤ →+* P3Z) n).symm
      dsimp only [poly3Ops, ringOps, pbOps]
      rw [hC, evalT2D, MvPolynomial.eval₂Hom_C, polyL1_C]⟩
  rel_add h1 h2 := ⟨fun m hm => by
      rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
      · obtain ⟨a, b, c⟩ := h1.1 m h
        exact ⟨a.trans (le_max_left _ _), b.trans (le_max_left _ _), c.trans (le_max_left _ _)⟩
      · obtain ⟨a, b, c⟩ := h2.1 m h
        exact ⟨a.trans (le_max_right _ _), b.trans (le_max_right _ _), c.trans (le_max_right _ _)⟩,
    fun t ht => by
      simp only [poly3Ops, ringOps, pbOps, map_add]
      exact (polyL1_add _ _).trans (Nat.add_le_add (h1.2 t ht) (h2.2 t ht))⟩
  rel_sub h1 h2 := ⟨fun m hm => by
      dsimp only [poly3Ops, ringOps] at hm
      rw [sub_eq_add_neg] at hm
      rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
      · obtain ⟨a, b, c⟩ := h1.1 m h
        exact ⟨a.trans (le_max_left _ _), b.trans (le_max_left _ _), c.trans (le_max_left _ _)⟩
      · rw [MvPolynomial.support_neg] at h
        obtain ⟨a, b, c⟩ := h2.1 m h
        exact ⟨a.trans (le_max_right _ _), b.trans (le_max_right _ _), c.trans (le_max_right _ _)⟩,
    fun t ht => by
      simp only [poly3Ops, ringOps, pbOps, map_sub]
      rw [sub_eq_add_neg]
      exact (polyL1_add _ _).trans (by rw [polyL1_neg]; exact Nat.add_le_add (h1.2 t ht) (h2.2 t ht))⟩
  rel_neg h := ⟨fun m hm => h.1 m (by simpa [poly3Ops, ringOps] using hm),
    fun t ht => by simp only [poly3Ops, ringOps, pbOps, map_neg, polyL1_neg]; exact h.2 t ht⟩
  rel_mul h1 h2 := ⟨fun m hm => by
      rcases Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm) with ⟨m1, hm1, m2, hm2, rfl⟩
      obtain ⟨a1, b1, c1⟩ := h1.1 m1 hm1
      obtain ⟨a2, b2, c2⟩ := h2.1 m2 hm2
      exact ⟨Nat.add_le_add a1 a2, Nat.add_le_add b1 b2, Nat.add_le_add c1 c2⟩,
    fun t ht => by
      simp only [poly3Ops, ringOps, pbOps, map_mul]
      exact (polyL1_mul _ _).trans (Nat.mul_le_mul (h1.2 t ht) (h2.2 t ht))⟩
  rel_pow k h := by
    induction k with
    | zero =>
      refine ⟨fun m hm => by
        have : m = 0 := by simpa [poly3Ops, ringOps, MvPolynomial.support_one] using hm
        subst this; simp [pbOps],
        fun t _ => by simp only [poly3Ops, ringOps, pbOps, pow_zero, map_one]; rw [← Polynomial.C_1, polyL1_C]; rfl⟩
    | succ k ih =>
      refine ⟨fun m hm => by
        rw [show poly3Ops.pow _ (k + 1) = _ ^ k * _ from pow_succ _ k] at hm
        rcases Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm) with ⟨m1, hm1, m2, hm2, rfl⟩
        obtain ⟨a1, b1, c1⟩ := ih.1 m1 hm1
        obtain ⟨a2, b2, c2⟩ := h.1 m2 hm2
        simp only [pbOps]
        exact ⟨Nat.add_le_add a1 a2, Nat.add_le_add b1 b2, Nat.add_le_add c1 c2⟩,
        fun t ht => by
          simp only [poly3Ops, ringOps, pbOps, map_pow]
          exact (polyL1_pow _ _).trans (Nat.pow_le_pow_left (h.2 t ht) _)⟩

lemma respectsBound2D_X0 (D Tmax : ℕ) :
    RespectsBound2D D Tmax (MvPolynomial.X 0) ⟨1, 0, 0, 1⟩ := by
  refine ⟨fun m hm => by
    have : m = Finsupp.single 0 1 := by simpa [MvPolynomial.support_X] using hm
    subst this; simp,
    fun t _ => by simp [evalT2D, polyL1_X]⟩

lemma respectsBound2D_X1 (D Tmax : ℕ) :
    RespectsBound2D D Tmax (MvPolynomial.X 1) ⟨0, 1, 0, 1⟩ := by
  refine ⟨fun m hm => by
    have : m = Finsupp.single 1 1 := by simpa [MvPolynomial.support_X] using hm
    subst this; simp,
    fun t _ => by
      simp only [evalT2D, MvPolynomial.eval₂Hom_X']
      rw [← mul_one ((Polynomial.X : Polynomial ℤ) ^ D), polyL1_X_pow_mul, ← Polynomial.C_1, polyL1_C]; rfl⟩

lemma respectsBound2D_X2 (D Tmax : ℕ) :
    RespectsBound2D D Tmax (MvPolynomial.X 2) ⟨0, 0, 1, Tmax⟩ := by
  refine ⟨fun m hm => by
    have : m = Finsupp.single 2 1 := by simpa [MvPolynomial.support_X] using hm
    subst this; simp,
    fun t ht => by simp only [evalT2D, MvPolynomial.eval₂Hom_X', polyL1_C, ht]⟩

/-- Soundness of factored 2D Kronecker (variables `0, 1` at `(B, B^D)`) × 1D grid (variable `2`)
vanishing check. -/
theorem mvPoly3_eq_zero_of_kronecker2D_gridT (p : P3Z) (b : PB) (D Tmax B : ℕ)
    (T_pts : Finset ℤ)
    (hR : RespectsBound2D D Tmax p b)
    (hS_deg : b.dS < D)
    (hT_deg : b.dT < T_pts.card) (hT_bd : ∀ t ∈ T_pts, t.natAbs ≤ Tmax)
    (hB : b.M < B)
    (hev : ∀ t ∈ T_pts, MvPolynomial.eval (v3Int (B : ℤ) ((B ^ D : ℕ) : ℤ) t) p = 0) :
    p = 0 := by
  have hevalT_zero : ∀ t ∈ T_pts, evalT2D D t p = 0 := fun t ht => by
    apply poly_eq_zero_of_eval_base (evalT2D D t p) B
    · exact lt_of_le_of_lt (hR.2 t (hT_bd t ht)) hB
    · rw [eval_evalT2D]; exact hev t ht
  let polyT_of (i j : ℕ) : Polynomial ℤ :=
    ∑ m ∈ p.support.filter (fun m => m 0 = i ∧ m 1 = j), Polynomial.C (p.coeff m) * Polynomial.X ^ m 2
  have hpolyT_eval (i j : ℕ) (hi : i < D) (t : ℤ) : (polyT_of i j).eval t = (evalT2D D t p).coeff (i + D * j) := by
    conv_rhs => rw [p.as_sum]
    dsimp only [polyT_of]
    rw [Finset.sum_filter, show ∀ f : Polynomial ℤ, f.eval t = Polynomial.evalRingHom t f from fun _ => rfl,
      map_sum, map_sum, ← Polynomial.lcoeff_apply, map_sum]
    apply Finset.sum_congr rfl; intro m hm
    simp only [Polynomial.coe_evalRingHom, Polynomial.lcoeff_apply, evalT2D, MvPolynomial.eval₂Hom_monomial,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three]
    have hrew : Polynomial.C (p.coeff m) * (Polynomial.X ^ m 0 * (Polynomial.X ^ D) ^ m 1 * Polynomial.C t ^ m 2) =
        Polynomial.C (p.coeff m * t ^ m 2) * Polynomial.X ^ (m 0 + D * m 1) := by
      rw [← pow_mul, ← pow_add]; simp only [map_mul, map_pow]; ring
    rw [hrew, Polynomial.coeff_C_mul_X_pow]
    have hlt0 : m 0 < D := lt_of_le_of_lt (hR.1 m hm).1 hS_deg
    have hiff : i + D * j = m 0 + D * m 1 ↔ m 0 = i ∧ m 1 = j := by
      constructor
      · intro h
        have h1 : m 1 = j := by
          by_contra hne
          rcases Nat.lt_or_gt_of_ne hne with hlt | hgt <;> nlinarith
        subst h1
        exact ⟨by omega, rfl⟩
      · rintro ⟨rfl, rfl⟩; rfl
    by_cases h : m 0 = i ∧ m 1 = j
    · rw [ite_eq_left h, ite_eq_left (hiff.mpr h)]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    · rw [ite_eq_right h, ite_eq_right (fun heq => h (hiff.mp heq)), Polynomial.eval_zero]
  have hpolyT_zero (i j : ℕ) (hi : i < D) : polyT_of i j = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (polyT_of i j) T_pts
    · intro t ht; rw [hpolyT_eval i j hi t, hevalT_zero t ht, Polynomial.coeff_zero]
    · refine lt_of_le_of_lt ?_ hT_deg
      refine (Polynomial.natDegree_sum_le _ _).trans ?_
      rw [Finset.fold_max_le]
      refine ⟨Nat.zero_le _, fun m hm => ?_⟩
      have hm' := (Finset.mem_filter.mp hm).1
      exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (hR.1 m hm').2.2
  ext m
  by_cases hm : m ∈ p.support
  · have hlt0 : m 0 < D := lt_of_le_of_lt (hR.1 m hm).1 hS_deg
    have hcm : (polyT_of (m 0) (m 1)).coeff (m 2) = p.coeff m := by
      dsimp only [polyT_of]
      rw [Finset.sum_filter, ← Polynomial.lcoeff_apply, map_sum]
      have hterm : ∀ m' : Fin 3 →₀ ℕ,
          Polynomial.lcoeff ℤ (m 2) (if m' 0 = m 0 ∧ m' 1 = m 1 then Polynomial.C (p.coeff m') * Polynomial.X ^ m' 2 else 0) =
          if m' = m then p.coeff m' else 0 := fun m' => by
        simp only [Polynomial.lcoeff_apply]
        by_cases heq : m' = m
        · subst heq; simp
        · have hne : ¬(m' 0 = m 0 ∧ m' 1 = m 1 ∧ m 2 = m' 2) := by
            rintro ⟨h0, h1, h2⟩
            apply heq; ext j; fin_cases j
            · exact h0
            · exact h1
            · exact h2.symm
          by_cases h01 : m' 0 = m 0 ∧ m' 1 = m 1
          · have h2 : m 2 ≠ m' 2 := fun h => hne ⟨h01.1, h01.2, h⟩
            simp [heq, h01, h2]
          · simp [heq, h01]
      simp_rw [hterm]
      rw [Finset.sum_ite_eq' p.support m p.coeff, ite_eq_left hm]
    rw [← hcm, hpolyT_zero (m 0) (m 1) hlt0, Polynomial.coeff_zero]
    simp
  · simp [MvPolynomial.notMem_support_iff.mp hm]

def allRange (lo : ℤ) : ℕ → (ℤ → Bool) → Bool
  | 0, _ => true
  | k + 1, f => f lo && allRange (Int.add lo 1) k f

lemma allRange_append (lo : ℤ) (m n : ℕ) (f : ℤ → Bool) :
    allRange lo (m + n) f = (allRange lo m f && allRange (lo + (m : ℤ)) n f) := by
  induction m generalizing lo with
  | zero => simp [allRange]
  | succ k ih =>
    rw [Nat.succ_add]
    simp only [allRange, Bool.and_assoc]
    congr 1
    change allRange (lo + 1) (k + n) f = (allRange (lo + 1) k f && allRange (lo + ((k + 1 : ℕ) : ℤ)) n f)
    rw [ih (lo + 1)]
    congr 2; push_cast; ring

def rangeInt (lo : ℤ) (n : ℕ) : Finset ℤ :=
  (Finset.range n).image (fun k : ℕ => lo + (k : ℤ))

lemma rangeInt_card (lo : ℤ) (n : ℕ) : (rangeInt lo n).card = n := by
  rw [rangeInt, Finset.card_image_of_injective _ (fun a b h => by omega), Finset.card_range]

lemma allRange_spec (lo : ℤ) (n : ℕ) (f : ℤ → Bool)
    (h : allRange lo n f = true) : ∀ x ∈ rangeInt lo n, f x = true := by
  induction n generalizing lo with
  | zero => intro x hx; simp [rangeInt] at hx
  | succ k ih =>
    simp only [allRange, Bool.and_eq_true] at h
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
    rw [Finset.mem_range] at hj
    cases j with
    | zero => simpa using h.1
    | succ j' =>
      have hmem : (lo + 1) + (j' : ℤ) ∈ rangeInt (lo + 1) k :=
        Finset.mem_image.mpr ⟨j', Finset.mem_range.mpr (by omega), rfl⟩
      have hres := ih (lo + 1) h.2 _ hmem
      rwa [show (lo + 1) + (j' : ℤ) = lo + ((j' + 1 : ℕ) : ℤ) by push_cast; ring] at hres

lemma rangeInt_natAbs_le (lo : ℤ) (n M : ℕ)
    (hlo : lo.natAbs ≤ M) (hhi : (lo + (n : ℤ) - 1).natAbs ≤ M) :
    ∀ x ∈ rangeInt lo n, x.natAbs ≤ M := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
  rw [Finset.mem_range] at hk
  omega

/-- Precomputed power table `[c, c*x, ..., c*x^(n-1)]` over any `PolyOps α`. -/
def powList {α : Type*} (o : PolyOps α) (x : α) : ℕ → α → List α
  | 0, _ => []
  | n + 1, cur => cur :: powList o x n (o.mul cur x)

def getPow {α : Type*} (o : PolyOps α) (x : α) (tbl : List α) (k : ℕ) : α :=
  tbl.getD k (o.pow x k)

lemma powList_rel {α β : Type*} {o1 : PolyOps α} {o2 : PolyOps β} {R : α → β → Prop}
    (hR : PolyOpsRel o1 o2 R) {x1 : α} {x2 : β} (hx : R x1 x2) :
    ∀ n {c1 c2}, R c1 c2 → List.Forall₂ R (powList o1 x1 n c1) (powList o2 x2 n c2)
  | 0, _, _, _ => List.Forall₂.nil
  | n + 1, _, _, hc => List.Forall₂.cons hc (powList_rel hR hx n (hR.rel_mul hc hx))

lemma list_forall₂_getElem {α β : Type*} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 →
      ∀ (i : ℕ) (h1 : i < l1.length) (h2 : i < l2.length), R l1[i] l2[i]
  | _ :: _, _ :: _, .cons h _, 0, _, _ => h
  | _ :: _, _ :: _, .cons _ ht, i + 1, h1, h2 =>
      list_forall₂_getElem ht i (Nat.lt_of_succ_lt_succ h1) (Nat.lt_of_succ_lt_succ h2)

lemma list_getD_rel_gen {α β : Type*} {R : α → β → Prop} {d1 : α} {d2 : β} (hd : R d1 d2) :
    ∀ {t1 : List α} {t2 : List β}, List.Forall₂ R t1 t2 → ∀ k : ℕ, R (t1.getD k d1) (t2.getD k d2)
  | [], [], .nil, k => by simp only [List.getD_nil]; exact hd
  | _ :: _, _ :: _, .cons h _, 0 => by simp only [List.getD_cons_zero]; exact h
  | _ :: _, _ :: _, .cons _ ht, k + 1 => by simp only [List.getD_cons_succ]; exact list_getD_rel_gen hd ht k

lemma getPow_rel {α β : Type*} {o1 : PolyOps α} {o2 : PolyOps β} {R : α → β → Prop}
    (hR : PolyOpsRel o1 o2 R) {x1 : α} {x2 : β} (hx : R x1 x2)
    {t1 : List α} {t2 : List β} (ht : List.Forall₂ R t1 t2) (k : ℕ) :
    R (getPow o1 x1 t1 k) (getPow o2 x2 t2 k) :=
  list_getD_rel_gen (hR.rel_pow k hx) ht k

lemma powList_ring_getD_gen {R : Type*} [CommRing R] (x d : R) :
    ∀ n m k, (powList (ringOps R) x n (x ^ m)).getD k d = if k < n then x ^ (m + k) else d
  | 0, _, _ => by simp [powList]
  | n + 1, m, 0 => by simp [powList]
  | n + 1, m, k + 1 => by
    change (powList (ringOps R) x n (x ^ m * x)).getD k d = _
    rw [← pow_succ, powList_ring_getD_gen x d n (m + 1) k]
    by_cases hk : k < n
    · have h1 : k + 1 < n + 1 := by omega
      simp [hk, h1, show m + 1 + k = m + (k + 1) by omega]
    · have h1 : ¬(k + 1 < n + 1) := by omega
      simp [hk, h1]

lemma getPow_ring_eq {R : Type*} [CommRing R] (x : R) (n k : ℕ) :
    getPow (ringOps R) x (powList (ringOps R) x n ((ringOps R).ofInt 1)) k = x ^ k := by
  have h1 : (ringOps R).ofInt 1 = x ^ 0 := by simp [ringOps]
  rw [getPow, h1, powList_ring_getD_gen]
  simp [ringOps]

lemma getPow_poly3_eq (x : P3Z) (n k : ℕ) :
    getPow poly3Ops x (powList poly3Ops x n (poly3Ops.ofInt 1)) k = x ^ k :=
  getPow_ring_eq x n k

end PolynomialEncoding.KroneckerCheck
#print axioms PolynomialEncoding.KroneckerCheck.identity_of_kronecker
#print axioms PolynomialEncoding.KroneckerCheck.mvPoly3_eq_zero_of_kronecker2D_gridT
