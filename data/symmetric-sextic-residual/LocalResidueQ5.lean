import Proposal.LocalResidueU0
import Proposal.Q5WeightsData

/-! Local residue of `eta_L : RatFunc CoverL` across the 5 roots `RQ5` of `Q_5(U) = 0`,
and exact global residue cancellation:
1. Generic `PolyOps` / `PolBound` (`PB`) / `PolyOpsRel` centered 1D Kronecker × 2D Grid
   soundness engine, exact `Q5WeightsData` recurrences & dualities, and the Bézout proof of
   `sum_RQ5_power_eq_W_k`.
2. 12-variable 23-term identity `Q5_rem_split`, splitting `eta_AC = eta_AC_main + eta_AC_reg`,
   and regularity of `trace_AC eta_AC_reg` at every `r ∈ RQ5`.
3. Shift-invariant `numM_shift_T`, homogeneous degree-4 extraction for `p4`, exact `qX`, `qY`,
   `cA1`, `q1_poly` identities, and `trace_AC eta_AC_main = toRat R12 / (C (81 * Cv0) * toRat (Q7 * Q5))`.
4. Factored `W`-dot product + `Q`-outer cached `PolyOps` centered Grid+Kronecker kernel check
   proving `sum_RQ5_eta_L : ∑ r ∈ RQ5, CrossedRationalResidue.residue r eta_L = ιL_K5 (toK5_RQ5 / L_K ^ 2)`.
5. Exact global residue cancellation `global_residue_cancellation`:
   `toK5 P_horiz_5 = -toK5_RInf / L_K ^ 2 - toK5_RU - toK5_RQ5 / L_K ^ 2`. -/

noncomputable section
namespace SymmetricSexticResidual.LocalResidueQ5
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.SheetCalculus
  SymmetricSexticResidual.CoverAlgebra SymmetricSexticResidual.CoverResidue
  SymmetricSexticResidual.LocalResidueData SymmetricSexticResidual.LocalResidueU0
  SymmetricSexticResidual.Q5WeightsData SymmetricSexticResidual.VerticalData
  SymmetricSexticResidual.VerticalIdentity SymmetricSexticResidual.EncodingCheck
  CrossedRationalResidue Polynomial
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions PolynomialEncoding.BivariateExpressions
open scoped BigOperators

/-! ### Section 1: `PolyOps` / `PolBound` Centered Kronecker × Grid Engine and `Q5` Weight Traces -/

private structure PolyOps (α : Type*) where
  zero : α
  ofInt : ℤ → α
  add : α → α → α
  sub : α → α → α
  neg : α → α
  mul : α → α → α
  pow : α → ℕ → α

private structure PB where
  dS : ℕ
  dQ : ℕ
  dT : ℕ
  M : ℕ
  deriving DecidableEq

private def intOps : PolyOps ℤ where
  zero := 0
  ofInt n := n
  add a b := Int.add a b
  sub a b := Int.sub a b
  neg a := Int.neg a
  mul a b := Int.mul a b
  pow a k := Int.pow a k

private def pbOps : PolyOps PB where
  zero := ⟨0, 0, 0, 0⟩
  ofInt n := ⟨0, 0, 0, Int.natAbs n⟩
  add a b := ⟨Nat.max a.dS b.dS, Nat.max a.dQ b.dQ, Nat.max a.dT b.dT, Nat.add a.M b.M⟩
  sub a b := ⟨Nat.max a.dS b.dS, Nat.max a.dQ b.dQ, Nat.max a.dT b.dT, Nat.add a.M b.M⟩
  neg a := a
  mul a b := ⟨Nat.add a.dS b.dS, Nat.add a.dQ b.dQ, Nat.add a.dT b.dT, Nat.mul a.M b.M⟩
  pow a k := ⟨Nat.mul a.dS k, Nat.mul a.dQ k, Nat.mul a.dT k, Nat.pow a.M k⟩

private abbrev P3Z := MvPolynomial (Fin 3) ℤ

private def poly3Ops : PolyOps P3Z where
  zero := 0
  ofInt n := MvPolynomial.C n
  add a b := a + b
  sub a b := a - b
  neg a := -a
  mul a b := a * b
  pow a k := a ^ k

private def k5Ops : PolyOps K5 where
  zero := 0
  ofInt n := (n : K5)
  add a b := a + b
  sub a b := a - b
  neg a := -a
  mul a b := a * b
  pow a k := a ^ k

private structure PolyOpsRel {α β : Type*} (o1 : PolyOps α) (o2 : PolyOps β) (R : α → β → Prop) : Prop where
  rel_zero : R o1.zero o2.zero
  rel_ofInt : ∀ n, R (o1.ofInt n) (o2.ofInt n)
  rel_add : ∀ {a1 a2 b1 b2}, R a1 b1 → R a2 b2 → R (o1.add a1 a2) (o2.add b1 b2)
  rel_sub : ∀ {a1 a2 b1 b2}, R a1 b1 → R a2 b2 → R (o1.sub a1 a2) (o2.sub b1 b2)
  rel_neg : ∀ {a b}, R a b → R (o1.neg a) (o2.neg b)
  rel_mul : ∀ {a1 a2 b1 b2}, R a1 b1 → R a2 b2 → R (o1.mul a1 a2) (o2.mul b1 b2)
  rel_pow : ∀ {a b} k, R a b → R (o1.pow a k) (o2.pow b k)

private def letB {α β : Type*} (x : α) (f : α → β) : β := f x

private lemma letB_rel {α₁ α₂ β₁ β₂ : Type*} {Ra : α₁ → α₂ → Prop} {Rb : β₁ → β₂ → Prop}
    {x₁ : α₁} {x₂ : α₂} {f₁ : α₁ → β₁} {f₂ : α₂ → β₂}
    (hx : Ra x₁ x₂) (hf : ∀ {a₁ a₂}, Ra a₁ a₂ → Rb (f₁ a₁) (f₂ a₂)) :
    Rb (letB x₁ f₁) (letB x₂ f₂) := hf hx

private lemma letB_step {α β : Type*} {x y : α} {f : α → β} {z : β} (hxy : x = y) (hf : f y = z) :
    letB x f = z := by rw [letB, hxy, hf]

private lemma letB_intro {α β : Type*} {P : β → Prop} {x : α} {f : α → β}
    (h : ∀ a, a = x → P (f a)) : P (letB x f) := h x rfl

private def v3Int (s q t : ℤ) : Fin 3 → ℤ
  | 0 => s
  | 1 => q
  | 2 => t

private def v3K5 : Fin 3 → K5
  | 0 => S_K
  | 1 => Q_K
  | 2 => T_K

private lemma poly3ToIntRel (s q t : ℤ) :
    PolyOpsRel poly3Ops intOps (fun p z => MvPolynomial.eval (v3Int s q t) p = z) where
  rel_zero := by simp [poly3Ops, intOps]
  rel_ofInt n := by simp [poly3Ops, intOps]
  rel_add h1 h2 := by simp [poly3Ops, intOps, h1, h2]
  rel_sub h1 h2 := by simp [poly3Ops, intOps, h1, h2]; rfl
  rel_neg h := by simp [poly3Ops, intOps, h]; rfl
  rel_mul h1 h2 := by simp [poly3Ops, intOps, h1, h2]
  rel_pow k h := by simp [poly3Ops, intOps, h]

private def evalP3K5 : P3Z →+* K5 :=
  MvPolynomial.eval₂Hom (Int.castRingHom K5) v3K5

private lemma poly3ToK5Rel :
    PolyOpsRel poly3Ops k5Ops (fun p x => evalP3K5 p = x) where
  rel_zero := by simp [poly3Ops, k5Ops]
  rel_ofInt n := by simp [poly3Ops, k5Ops, evalP3K5]
  rel_add h1 h2 := by simp [poly3Ops, k5Ops, h1, h2]
  rel_sub h1 h2 := by simp [poly3Ops, k5Ops, h1, h2]
  rel_neg h := by simp [poly3Ops, k5Ops, h]
  rel_mul h1 h2 := by simp [poly3Ops, k5Ops, h1, h2]
  rel_pow k h := by simp [poly3Ops, k5Ops, h]

private def evalQT (q t : ℤ) : P3Z →+* Polynomial ℤ :=
  MvPolynomial.eval₂Hom Polynomial.C (fun i => match i with
    | 0 => Polynomial.X
    | 1 => Polynomial.C q
    | 2 => Polynomial.C t)

private lemma eval_evalQT (p : P3Z) (s q t : ℤ) :
    (evalQT q t p).eval s = MvPolynomial.eval (v3Int s q t) p := by
  induction p using MvPolynomial.induction_on' with
  | add p1 p2 h1 h2 => simp only [map_add, Polynomial.eval_add, h1, h2]
  | monomial m c =>
    simp only [evalQT, MvPolynomial.eval₂Hom_monomial, MvPolynomial.eval_monomial,
      Polynomial.eval_mul, Polynomial.eval_C, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Fin.prod_univ_three, Polynomial.eval_pow, Polynomial.eval_X, v3Int]

private def polyL1 (f : Polynomial ℤ) : ℕ :=
  ∑ i ∈ f.support, (f.coeff i).natAbs

private lemma polyL1_eq_sum_range (f : Polynomial ℤ) (N : ℕ) (hN : ∀ i ∈ f.support, i < N) :
    polyL1 f = ∑ i ∈ Finset.range N, (f.coeff i).natAbs := by
  unfold polyL1
  apply Finset.sum_subset
  · intro i hi; exact Finset.mem_range.mpr (hN i hi)
  · intro i _ hi
    have h0 : f.coeff i = 0 := by simpa [Polynomial.mem_support_iff] using hi
    simp [h0]

private lemma polyL1_zero : polyL1 0 = 0 := by simp [polyL1]

private lemma polyL1_C (c : ℤ) : polyL1 (Polynomial.C c) = c.natAbs := by
  by_cases hc : c = 0
  · subst hc; simp [polyL1]
  · simp only [polyL1, Polynomial.support_C hc, Finset.sum_singleton, Polynomial.coeff_C_zero]

private lemma polyL1_X : polyL1 Polynomial.X = 1 := by
  rw [polyL1_eq_sum_range Polynomial.X 2 (fun i hi => by
    have : i = 1 := by simpa [Polynomial.support_X] using hi
    omega)]
  simp [Finset.sum_range_succ]

private lemma polyL1_neg (f : Polynomial ℤ) : polyL1 (-f) = polyL1 f := by
  simp [polyL1, Polynomial.support_neg]

private lemma polyL1_add (f g : Polynomial ℤ) : polyL1 (f + g) ≤ polyL1 f + polyL1 g := by
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

private lemma polyL1_sum_le {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℤ) :
    polyL1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, polyL1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polyL1_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (polyL1_add _ _).trans (Nat.add_le_add_left ih _)

private lemma polyL1_C_mul (c : ℤ) (g : Polynomial ℤ) :
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

private lemma polyL1_X_pow_mul (n : ℕ) (g : Polynomial ℤ) :
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
    rw [Polynomial.coeff_X_pow_mul', if_neg (by omega)]; rfl
  rw [hlo, zero_add]
  apply Finset.sum_congr rfl; intro x _
  rw [add_comm, Polynomial.coeff_X_pow_mul]

private lemma polyL1_mul (f g : Polynomial ℤ) : polyL1 (f * g) ≤ polyL1 f * polyL1 g := by
  conv_lhs => rw [f.as_sum_support_C_mul_X_pow]
  rw [Finset.sum_mul]
  refine (polyL1_sum_le _ _).trans ?_
  rw [polyL1, Finset.sum_mul]
  apply Finset.sum_le_sum; intro i _
  rw [mul_assoc, polyL1_C_mul, polyL1_X_pow_mul]

private lemma polyL1_pow (f : Polynomial ℤ) (k : ℕ) : polyL1 (f ^ k) ≤ (polyL1 f) ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, ← Polynomial.C_1, polyL1_C]; rfl
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (polyL1_mul _ _).trans (Nat.mul_le_mul ih le_rfl)

private def RespectsBound (Qmax Tmax : ℕ) (p : P3Z) (b : PB) : Prop :=
  (∀ m ∈ p.support, m 0 ≤ b.dS ∧ m 1 ≤ b.dQ ∧ m 2 ≤ b.dT) ∧
  (∀ q t : ℤ, q.natAbs ≤ Qmax → t.natAbs ≤ Tmax → polyL1 (evalQT q t p) ≤ b.M)

private lemma respectsBoundRel (Qmax Tmax : ℕ) :
    PolyOpsRel poly3Ops pbOps (RespectsBound Qmax Tmax) where
  rel_zero := ⟨fun m hm => by simp [poly3Ops] at hm, fun _ _ _ _ => by simp [poly3Ops, pbOps, polyL1_zero]⟩
  rel_ofInt n := ⟨fun m hm => by
      have hm0 : m = 0 := by
        by_contra hne
        exact (MvPolynomial.mem_support_iff.mp hm) (by rw [poly3Ops, MvPolynomial.coeff_C, if_neg (Ne.symm hne)])
      subst hm0; simp [pbOps],
    fun q t _ _ => by simp only [poly3Ops, pbOps, evalQT, MvPolynomial.eval₂Hom_C, polyL1_C, le_rfl]⟩
  rel_add h1 h2 := ⟨fun m hm => by
      rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
      · obtain ⟨a, b, c⟩ := h1.1 m h
        exact ⟨a.trans (le_max_left _ _), b.trans (le_max_left _ _), c.trans (le_max_left _ _)⟩
      · obtain ⟨a, b, c⟩ := h2.1 m h
        exact ⟨a.trans (le_max_right _ _), b.trans (le_max_right _ _), c.trans (le_max_right _ _)⟩,
    fun q t hq ht => by
      simp only [poly3Ops, pbOps, map_add]
      exact (polyL1_add _ _).trans (Nat.add_le_add (h1.2 q t hq ht) (h2.2 q t hq ht))⟩
  rel_sub h1 h2 := ⟨fun m hm => by
      dsimp only [poly3Ops] at hm
      rw [sub_eq_add_neg] at hm
      rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
      · obtain ⟨a, b, c⟩ := h1.1 m h
        exact ⟨a.trans (le_max_left _ _), b.trans (le_max_left _ _), c.trans (le_max_left _ _)⟩
      · rw [MvPolynomial.support_neg] at h
        obtain ⟨a, b, c⟩ := h2.1 m h
        exact ⟨a.trans (le_max_right _ _), b.trans (le_max_right _ _), c.trans (le_max_right _ _)⟩,
    fun q t hq ht => by
      simp only [poly3Ops, pbOps, map_sub]
      rw [sub_eq_add_neg]
      exact (polyL1_add _ _).trans (by rw [polyL1_neg]; exact Nat.add_le_add (h1.2 q t hq ht) (h2.2 q t hq ht))⟩
  rel_neg h := ⟨fun m hm => h.1 m (by simpa [poly3Ops] using hm),
    fun q t hq ht => by simp only [poly3Ops, pbOps, map_neg, polyL1_neg]; exact h.2 q t hq ht⟩
  rel_mul h1 h2 := ⟨fun m hm => by
      rcases Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm) with ⟨m1, hm1, m2, hm2, rfl⟩
      obtain ⟨a1, b1, c1⟩ := h1.1 m1 hm1
      obtain ⟨a2, b2, c2⟩ := h2.1 m2 hm2
      exact ⟨Nat.add_le_add a1 a2, Nat.add_le_add b1 b2, Nat.add_le_add c1 c2⟩,
    fun q t hq ht => by
      simp only [poly3Ops, pbOps, map_mul]
      exact (polyL1_mul _ _).trans (Nat.mul_le_mul (h1.2 q t hq ht) (h2.2 q t hq ht))⟩
  rel_pow k h := by
    induction k with
    | zero =>
      refine ⟨fun m hm => by
        have : m = 0 := by simpa [poly3Ops, MvPolynomial.support_one] using hm
        subst this; simp [pbOps],
        fun q t _ _ => by simp only [poly3Ops, pbOps, map_pow, pow_zero, map_one, Nat.pow_zero]; rw [← Polynomial.C_1, polyL1_C]; rfl⟩
    | succ k ih =>
      refine ⟨fun m hm => by
        rw [show poly3Ops.pow _ (k + 1) = _ ^ k * _ from pow_succ _ k] at hm
        rcases Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm) with ⟨m1, hm1, m2, hm2, rfl⟩
        obtain ⟨a1, b1, c1⟩ := ih.1 m1 hm1
        obtain ⟨a2, b2, c2⟩ := h.1 m2 hm2
        simp only [pbOps, Nat.mul_succ]
        exact ⟨Nat.add_le_add a1 a2, Nat.add_le_add b1 b2, Nat.add_le_add c1 c2⟩,
        fun q t hq ht => by
          simp only [poly3Ops, pbOps, map_pow]
          exact (polyL1_pow _ _).trans (Nat.pow_le_pow_left (h.2 q t hq ht) _)⟩

private lemma respectsBound_X0 (Qmax Tmax : ℕ) :
    RespectsBound Qmax Tmax (MvPolynomial.X 0) ⟨1, 0, 0, 1⟩ := by
  refine ⟨fun m hm => by
    have : m = Finsupp.single 0 1 := by simpa [MvPolynomial.support_X] using hm
    subst this; simp,
    fun q t _ _ => by simp [evalQT, polyL1_X]⟩

private lemma respectsBound_X1 (Qmax Tmax : ℕ) :
    RespectsBound Qmax Tmax (MvPolynomial.X 1) ⟨0, 1, 0, Qmax⟩ := by
  refine ⟨fun m hm => by
    have : m = Finsupp.single 1 1 := by simpa [MvPolynomial.support_X] using hm
    subst this; simp,
    fun q t hq _ => by simp only [evalQT, MvPolynomial.eval₂Hom_X', polyL1_C, hq]⟩

private lemma respectsBound_X2 (Qmax Tmax : ℕ) :
    RespectsBound Qmax Tmax (MvPolynomial.X 2) ⟨0, 0, 1, Tmax⟩ := by
  refine ⟨fun m hm => by
    have : m = Finsupp.single 2 1 := by simpa [MvPolynomial.support_X] using hm
    subst this; simp,
    fun q t _ ht => by simp only [evalQT, MvPolynomial.eval₂Hom_X', polyL1_C, ht]⟩

private lemma natDegree_divX_le_pred {R : Type*} [Semiring R] (g : R[X]) :
    g.divX.natDegree ≤ g.natDegree - 1 := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun i hi => ?_
  rw [Polynomial.coeff_divX]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

private lemma poly_eq_zero_of_eval_base (f : Polynomial ℤ) (B : ℕ)
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

private lemma mvPoly3_eq_zero_of_kronecker_grid (p : P3Z) (b : PB) (Qmax Tmax B : ℕ)
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
  -- Slice coefficient of S^i as a polynomial in T (for fixed q):
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
  -- Slice coefficient of S^i * T^k as a polynomial in Q:
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
          if_neg (Ne.symm h2)]
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
      · subst heq; simp [Polynomial.coeff_C_mul_X_pow]
      · have hne : ¬(m' 0 = m 0 ∧ m' 2 = m 2 ∧ m 1 = m' 1) := by
          rintro ⟨h0, h2, h1⟩
          apply heq; ext j; fin_cases j
          · exact h0
          · exact h1.symm
          · exact h2
        by_cases h02 : m' 0 = m 0 ∧ m' 2 = m 2
        · have h1 : m 1 ≠ m' 1 := fun h => hne ⟨h02.1, h02.2, h⟩
          simp [heq, h02, h1, Polynomial.coeff_C_mul_X_pow]
        · simp [heq, h02]
    simp_rw [hterm]
    by_cases hm : m ∈ p.support
    · rw [Finset.sum_ite_eq' p.support m p.coeff, if_pos hm]
    · rw [Finset.sum_ite_eq' p.support m p.coeff, if_neg hm]
      symm; simpa [MvPolynomial.mem_support_iff] using hm
  rw [← hcm, hpolyQ_zero, Polynomial.coeff_zero]
  simp

private def evalT2D (D : ℕ) (t : ℤ) : P3Z →+* Polynomial ℤ :=
  MvPolynomial.eval₂Hom Polynomial.C (fun i => match i with
    | 0 => Polynomial.X
    | 1 => Polynomial.X ^ D
    | 2 => Polynomial.C t)

private lemma eval_evalT2D (D : ℕ) (p : P3Z) (B : ℕ) (t : ℤ) :
    (evalT2D D t p).eval (B : ℤ) = MvPolynomial.eval (v3Int (B : ℤ) ((B ^ D : ℕ) : ℤ) t) p := by
  induction p using MvPolynomial.induction_on' with
  | add p1 p2 h1 h2 => simp only [map_add, Polynomial.eval_add, h1, h2]
  | monomial m c =>
    simp only [evalT2D, MvPolynomial.eval₂Hom_monomial, MvPolynomial.eval_monomial,
      Polynomial.eval_mul, Polynomial.eval_C, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Fin.prod_univ_three, Polynomial.eval_pow, Polynomial.eval_X, v3Int, Nat.cast_pow]

private def RespectsBound2D (D Tmax : ℕ) (p : P3Z) (b : PB) : Prop :=
  (∀ m ∈ p.support, m 0 ≤ b.dS ∧ m 1 ≤ b.dQ ∧ m 2 ≤ b.dT) ∧
  (∀ t : ℤ, t.natAbs ≤ Tmax → polyL1 (evalT2D D t p) ≤ b.M)

private lemma respectsBound2DRel (D Tmax : ℕ) :
    PolyOpsRel poly3Ops pbOps (RespectsBound2D D Tmax) where
  rel_zero := ⟨fun m hm => by simp [poly3Ops] at hm, fun _ _ => by simp [poly3Ops, pbOps, polyL1_zero]⟩
  rel_ofInt n := ⟨fun m hm => by
      have hm0 : m = 0 := by
        by_contra hne
        exact (MvPolynomial.mem_support_iff.mp hm) (by rw [poly3Ops, MvPolynomial.coeff_C, if_neg (Ne.symm hne)])
      subst hm0; simp [pbOps],
    fun t _ => by simp only [poly3Ops, pbOps, evalT2D, MvPolynomial.eval₂Hom_C, polyL1_C, le_rfl]⟩
  rel_add h1 h2 := ⟨fun m hm => by
      rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
      · obtain ⟨a, b, c⟩ := h1.1 m h
        exact ⟨a.trans (le_max_left _ _), b.trans (le_max_left _ _), c.trans (le_max_left _ _)⟩
      · obtain ⟨a, b, c⟩ := h2.1 m h
        exact ⟨a.trans (le_max_right _ _), b.trans (le_max_right _ _), c.trans (le_max_right _ _)⟩,
    fun t ht => by
      simp only [poly3Ops, pbOps, map_add]
      exact (polyL1_add _ _).trans (Nat.add_le_add (h1.2 t ht) (h2.2 t ht))⟩
  rel_sub h1 h2 := ⟨fun m hm => by
      dsimp only [poly3Ops] at hm
      rw [sub_eq_add_neg] at hm
      rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
      · obtain ⟨a, b, c⟩ := h1.1 m h
        exact ⟨a.trans (le_max_left _ _), b.trans (le_max_left _ _), c.trans (le_max_left _ _)⟩
      · rw [MvPolynomial.support_neg] at h
        obtain ⟨a, b, c⟩ := h2.1 m h
        exact ⟨a.trans (le_max_right _ _), b.trans (le_max_right _ _), c.trans (le_max_right _ _)⟩,
    fun t ht => by
      simp only [poly3Ops, pbOps, map_sub]
      rw [sub_eq_add_neg]
      exact (polyL1_add _ _).trans (by rw [polyL1_neg]; exact Nat.add_le_add (h1.2 t ht) (h2.2 t ht))⟩
  rel_neg h := ⟨fun m hm => h.1 m (by simpa [poly3Ops] using hm),
    fun t ht => by simp only [poly3Ops, pbOps, map_neg, polyL1_neg]; exact h.2 t ht⟩
  rel_mul h1 h2 := ⟨fun m hm => by
      rcases Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm) with ⟨m1, hm1, m2, hm2, rfl⟩
      obtain ⟨a1, b1, c1⟩ := h1.1 m1 hm1
      obtain ⟨a2, b2, c2⟩ := h2.1 m2 hm2
      exact ⟨Nat.add_le_add a1 a2, Nat.add_le_add b1 b2, Nat.add_le_add c1 c2⟩,
    fun t ht => by
      simp only [poly3Ops, pbOps, map_mul]
      exact (polyL1_mul _ _).trans (Nat.mul_le_mul (h1.2 t ht) (h2.2 t ht))⟩
  rel_pow k h := by
    induction k with
    | zero =>
      refine ⟨fun m hm => by
        have : m = 0 := by simpa [poly3Ops, MvPolynomial.support_one] using hm
        subst this; simp [pbOps],
        fun t _ => by simp only [poly3Ops, pbOps, map_pow, pow_zero, map_one]; rw [← Polynomial.C_1, polyL1_C]; rfl⟩
    | succ k ih =>
      refine ⟨fun m hm => by
        rw [show poly3Ops.pow _ (k + 1) = _ ^ k * _ from pow_succ _ k] at hm
        rcases Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm) with ⟨m1, hm1, m2, hm2, rfl⟩
        obtain ⟨a1, b1, c1⟩ := ih.1 m1 hm1
        obtain ⟨a2, b2, c2⟩ := h.1 m2 hm2
        simp only [pbOps]
        exact ⟨Nat.add_le_add a1 a2, Nat.add_le_add b1 b2, Nat.add_le_add c1 c2⟩,
        fun t ht => by
          simp only [poly3Ops, pbOps, map_pow]
          exact (polyL1_pow _ _).trans (Nat.pow_le_pow_left (h.2 t ht) _)⟩

private lemma respectsBound2D_X0 (D Tmax : ℕ) :
    RespectsBound2D D Tmax (MvPolynomial.X 0) ⟨1, 0, 0, 1⟩ := by
  refine ⟨fun m hm => by
    have : m = Finsupp.single 0 1 := by simpa [MvPolynomial.support_X] using hm
    subst this; simp,
    fun t _ => by simp [evalT2D, polyL1_X]⟩

private lemma respectsBound2D_X1 (D Tmax : ℕ) :
    RespectsBound2D D Tmax (MvPolynomial.X 1) ⟨0, 1, 0, 1⟩ := by
  refine ⟨fun m hm => by
    have : m = Finsupp.single 1 1 := by simpa [MvPolynomial.support_X] using hm
    subst this; simp,
    fun t _ => by
      simp only [evalT2D, MvPolynomial.eval₂Hom_X']
      rw [← mul_one ((Polynomial.X : Polynomial ℤ) ^ D), polyL1_X_pow_mul, ← Polynomial.C_1, polyL1_C]; rfl⟩

private lemma respectsBound2D_X2 (D Tmax : ℕ) :
    RespectsBound2D D Tmax (MvPolynomial.X 2) ⟨0, 0, 1, Tmax⟩ := by
  refine ⟨fun m hm => by
    have : m = Finsupp.single 2 1 := by simpa [MvPolynomial.support_X] using hm
    subst this; simp,
    fun t ht => by simp only [evalT2D, MvPolynomial.eval₂Hom_X', polyL1_C, ht]⟩

private lemma mvPoly3_eq_zero_of_kronecker2D_gridT (p : P3Z) (b : PB) (D Tmax B : ℕ)
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
    · rw [if_pos h, if_pos (hiff.mpr h)]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    · rw [if_neg h, if_neg (fun heq => h (hiff.mp heq)), Polynomial.eval_zero]
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
        · subst heq; simp [Polynomial.coeff_C_mul_X_pow]
        · have hne : ¬(m' 0 = m 0 ∧ m' 1 = m 1 ∧ m 2 = m' 2) := by
            rintro ⟨h0, h1, h2⟩
            apply heq; ext j; fin_cases j
            · exact h0
            · exact h1
            · exact h2.symm
          by_cases h01 : m' 0 = m 0 ∧ m' 1 = m 1
          · have h2 : m 2 ≠ m' 2 := fun h => hne ⟨h01.1, h01.2, h⟩
            simp [heq, h01, h2, Polynomial.coeff_C_mul_X_pow]
          · simp [heq, h01]
      simp_rw [hterm]
      rw [Finset.sum_ite_eq' p.support m p.coeff, if_pos hm]
    rw [← hcm, hpolyT_zero (m 0) (m 1) hlt0, Polynomial.coeff_zero, MvPolynomial.coeff_zero]
    rfl
  · simp [MvPolynomial.notMem_support_iff.mp hm]

private def allRange (lo : ℤ) : ℕ → (ℤ → Bool) → Bool
  | 0, _ => true
  | k + 1, f => f lo && allRange (Int.add lo 1) k f

private lemma allRange_append (lo : ℤ) (m n : ℕ) (f : ℤ → Bool) :
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

private def rangeInt (lo : ℤ) (n : ℕ) : Finset ℤ :=
  (Finset.range n).image (fun k : ℕ => lo + (k : ℤ))

private lemma rangeInt_card (lo : ℤ) (n : ℕ) : (rangeInt lo n).card = n := by
  rw [rangeInt, Finset.card_image_of_injective _ (fun a b h => by omega), Finset.card_range]

private lemma allRange_spec (lo : ℤ) (n : ℕ) (f : ℤ → Bool)
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

private lemma rangeInt_natAbs_le (lo : ℤ) (n M : ℕ)
    (hlo : lo.natAbs ≤ M) (hhi : (lo + (n : ℤ) - 1).natAbs ≤ M) :
    ∀ x ∈ rangeInt lo n, x.natAbs ≤ M := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
  rw [Finset.mem_range] at hk
  omega

-- Power table & `Expr` evaluation over any `PolyOps α`
private def powList {α : Type*} (o : PolyOps α) (x : α) : ℕ → α → List α
  | 0, _ => []
  | n + 1, cur => cur :: powList o x n (o.mul cur x)

private def getPow {α : Type*} (o : PolyOps α) (x : α) (tbl : List α) (k : ℕ) : α :=
  tbl.getD k (o.pow x k)

private lemma powList_rel {α β : Type*} {o1 : PolyOps α} {o2 : PolyOps β} {R : α → β → Prop}
    (hR : PolyOpsRel o1 o2 R) {x1 : α} {x2 : β} (hx : R x1 x2) :
    ∀ n {c1 c2}, R c1 c2 → List.Forall₂ R (powList o1 x1 n c1) (powList o2 x2 n c2)
  | 0, _, _, _ => List.Forall₂.nil
  | n + 1, _, _, hc => List.Forall₂.cons hc (powList_rel hR hx n (hR.rel_mul hc hx))

private lemma list_forall₂_getElem {α β : Type*} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 →
      ∀ (i : ℕ) (h1 : i < l1.length) (h2 : i < l2.length), R l1[i] l2[i]
  | _ :: _, _ :: _, .cons h _, 0, _, _ => h
  | _ :: _, _ :: _, .cons _ ht, i + 1, h1, h2 =>
      list_forall₂_getElem ht i (Nat.lt_of_succ_lt_succ h1) (Nat.lt_of_succ_lt_succ h2)

private lemma list_getD_rel_gen {α β : Type*} {R : α → β → Prop} {d1 : α} {d2 : β} (hd : R d1 d2) :
    ∀ {t1 : List α} {t2 : List β}, List.Forall₂ R t1 t2 → ∀ k : ℕ, R (t1.getD k d1) (t2.getD k d2)
  | [], [], .nil, k => by simp only [List.getD_nil]; exact hd
  | _ :: _, _ :: _, .cons h _, 0 => by simp only [List.getD_cons_zero]; exact h
  | _ :: _, _ :: _, .cons _ ht, k + 1 => by simp only [List.getD_cons_succ]; exact list_getD_rel_gen hd ht k

private lemma getPow_rel {α β : Type*} {o1 : PolyOps α} {o2 : PolyOps β} {R : α → β → Prop}
    (hR : PolyOpsRel o1 o2 R) {x1 : α} {x2 : β} (hx : R x1 x2)
    {t1 : List α} {t2 : List β} (ht : List.Forall₂ R t1 t2) (k : ℕ) :
    R (getPow o1 x1 t1 k) (getPow o2 x2 t2 k) :=
  list_getD_rel_gen (hR.rel_pow k hx) ht k

private lemma powList_poly3_getD_gen (x d : P3Z) :
    ∀ n m k, (powList poly3Ops x n (x ^ m)).getD k d = if k < n then x ^ (m + k) else d
  | 0, _, _ => by simp [powList]
  | n + 1, m, 0 => by simp [powList]
  | n + 1, m, k + 1 => by
    change (powList poly3Ops x n (x ^ m * x)).getD k d = _
    rw [← pow_succ, powList_poly3_getD_gen x d n (m + 1) k]
    by_cases hk : k < n
    · have h1 : k + 1 < n + 1 := by omega
      simp [hk, h1, show m + 1 + k = m + (k + 1) by omega]
    · have h1 : ¬(k + 1 < n + 1) := by omega
      simp [hk, h1]

private lemma getPow_poly3_eq (x : P3Z) (n k : ℕ) :
    getPow poly3Ops x (powList poly3Ops x n (poly3Ops.ofInt 1)) k = x ^ k := by
  have h1 : poly3Ops.ofInt 1 = x ^ 0 := by simp [poly3Ops]
  rw [getPow, h1, powList_poly3_getD_gen]
  simp [poly3Ops]

private def evalExpr2 {α : Type*} (o : PolyOps α) (S Q : α) (pS pQ : List α) : Expr → α
  | .num c => o.ofInt c
  | .natCast n => o.ofInt (n : ℤ)
  | .intCast z => o.ofInt z
  | .var 0 => S
  | .var 1 => Q
  | .var _ => o.zero
  | .neg a => o.neg (evalExpr2 o S Q pS pQ a)
  | .add a b => o.add (evalExpr2 o S Q pS pQ a) (evalExpr2 o S Q pS pQ b)
  | .sub a b => o.sub (evalExpr2 o S Q pS pQ a) (evalExpr2 o S Q pS pQ b)
  | .mul a b => o.mul (evalExpr2 o S Q pS pQ a) (evalExpr2 o S Q pS pQ b)
  | .pow (.var 0) k => getPow o S pS k
  | .pow (.var 1) k => getPow o Q pQ k
  | .pow a k => o.pow (evalExpr2 o S Q pS pQ a) k

private lemma evalExpr2_rel {α β : Type*} {o1 : PolyOps α} {o2 : PolyOps β} {R : α → β → Prop}
    (hR : PolyOpsRel o1 o2 R) {S1 Q1 : α} {S2 Q2 : β} (hS : R S1 S2) (hQ : R Q1 Q2)
    {pS1 pQ1 : List α} {pS2 pQ2 : List β}
    (hpS : List.Forall₂ R pS1 pS2) (hpQ : List.Forall₂ R pQ1 pQ2) :
    ∀ e : Expr, R (evalExpr2 o1 S1 Q1 pS1 pQ1 e) (evalExpr2 o2 S2 Q2 pS2 pQ2 e)
  | .num c => hR.rel_ofInt c
  | .natCast n => hR.rel_ofInt n
  | .intCast z => hR.rel_ofInt z
  | .var 0 => hS
  | .var 1 => hQ
  | .var (k + 2) => hR.rel_zero
  | .neg a => hR.rel_neg (evalExpr2_rel hR hS hQ hpS hpQ a)
  | .add a b => hR.rel_add (evalExpr2_rel hR hS hQ hpS hpQ a) (evalExpr2_rel hR hS hQ hpS hpQ b)
  | .sub a b => hR.rel_sub (evalExpr2_rel hR hS hQ hpS hpQ a) (evalExpr2_rel hR hS hQ hpS hpQ b)
  | .mul a b => hR.rel_mul (evalExpr2_rel hR hS hQ hpS hpQ a) (evalExpr2_rel hR hS hQ hpS hpQ b)
  | .pow (.var 0) k => getPow_rel hR hS hpS k
  | .pow (.var 1) k => getPow_rel hR hQ hpQ k
  | .pow (.var (j + 2)) k => hR.rel_pow k hR.rel_zero
  | .pow (.num c) k => hR.rel_pow k (hR.rel_ofInt c)
  | .pow (.natCast n) k => hR.rel_pow k (hR.rel_ofInt n)
  | .pow (.intCast z) k => hR.rel_pow k (hR.rel_ofInt z)
  | .pow (.neg a) k => hR.rel_pow k (hR.rel_neg (evalExpr2_rel hR hS hQ hpS hpQ a))
  | .pow (.add a b) k => hR.rel_pow k (hR.rel_add (evalExpr2_rel hR hS hQ hpS hpQ a) (evalExpr2_rel hR hS hQ hpS hpQ b))
  | .pow (.sub a b) k => hR.rel_pow k (hR.rel_sub (evalExpr2_rel hR hS hQ hpS hpQ a) (evalExpr2_rel hR hS hQ hpS hpQ b))
  | .pow (.mul a b) k => hR.rel_pow k (hR.rel_mul (evalExpr2_rel hR hS hQ hpS hpQ a) (evalExpr2_rel hR hS hQ hpS hpQ b))
  | .pow (.pow a j) k => hR.rel_pow k (evalExpr2_rel hR hS hQ hpS hpQ (.pow a j))

private def v3P3_SQ : ℕ → P3Z
  | 0 => MvPolynomial.X 0
  | 1 => MvPolynomial.X 1
  | _ => 0

private lemma evalExpr2_poly3_eq (nS nQ : ℕ) :
    ∀ e : Expr,
      evalExpr2 poly3Ops (MvPolynomial.X 0) (MvPolynomial.X 1)
        (powList poly3Ops (MvPolynomial.X 0) nS (poly3Ops.ofInt 1))
        (powList poly3Ops (MvPolynomial.X 1) nQ (poly3Ops.ofInt 1)) e =
      ringEval v3P3_SQ e
  | .num c => by simp [evalExpr2, poly3Ops, ringEval]
  | .natCast n => by simp [evalExpr2, poly3Ops, ringEval]
  | .intCast z => by simp [evalExpr2, poly3Ops, ringEval]
  | .var 0 => rfl
  | .var 1 => rfl
  | .var (_ + 2) => rfl
  | .neg a => by rw [evalExpr2, ringEval, evalExpr2_poly3_eq nS nQ a]; rfl
  | .add a b => by rw [evalExpr2, ringEval, evalExpr2_poly3_eq nS nQ a, evalExpr2_poly3_eq nS nQ b]; rfl
  | .sub a b => by rw [evalExpr2, ringEval, evalExpr2_poly3_eq nS nQ a, evalExpr2_poly3_eq nS nQ b]; rfl
  | .mul a b => by rw [evalExpr2, ringEval, evalExpr2_poly3_eq nS nQ a, evalExpr2_poly3_eq nS nQ b]; rfl
  | .pow (.var 0) k => by simp [evalExpr2, getPow_poly3_eq, ringEval, v3P3_SQ]
  | .pow (.var 1) k => by simp [evalExpr2, getPow_poly3_eq, ringEval, v3P3_SQ]
  | .pow (.var (_ + 2)) k => by simp [evalExpr2, poly3Ops, ringEval, v3P3_SQ]
  | .pow (.num c) k => by simp [evalExpr2, poly3Ops, ringEval]
  | .pow (.natCast n) k => by simp [evalExpr2, poly3Ops, ringEval]
  | .pow (.intCast z) k => by simp [evalExpr2, poly3Ops, ringEval]
  | .pow (.neg a) k => by simp only [evalExpr2, ringEval]; rw [evalExpr2_poly3_eq nS nQ a]; rfl
  | .pow (.add a b) k => by simp only [evalExpr2, ringEval]; rw [evalExpr2_poly3_eq nS nQ a, evalExpr2_poly3_eq nS nQ b]; rfl
  | .pow (.sub a b) k => by simp only [evalExpr2, ringEval]; rw [evalExpr2_poly3_eq nS nQ a, evalExpr2_poly3_eq nS nQ b]; rfl
  | .pow (.mul a b) k => by simp only [evalExpr2, ringEval]; rw [evalExpr2_poly3_eq nS nQ a, evalExpr2_poly3_eq nS nQ b]; rfl
  | .pow (.pow a j) k => by
      have ih := evalExpr2_poly3_eq nS nQ (.pow a j)
      change poly3Ops.pow (evalExpr2 _ _ _ _ _ (.pow a j)) k = (ringEval v3P3_SQ (.pow a j)) ^ k
      rw [ih]; rfl

private def vK5_SQ : ℕ → K5
  | 0 => S_K
  | 1 => Q_K
  | _ => 0

private def evalSQ_K5 (e : Expr) : K5 := ringEval vK5_SQ e

private lemma evalP3K5_ringEval_SQ (e : Expr) :
    evalP3K5 (ringEval v3P3_SQ e) = evalSQ_K5 e := by
  induction e with
  | num c => simp [evalP3K5, evalSQ_K5, ringEval]
  | natCast n => simp [evalP3K5, evalSQ_K5, ringEval]
  | intCast z => simp [evalP3K5, evalSQ_K5, ringEval]
  | var j =>
    match j with
    | 0 => simp [evalP3K5, evalSQ_K5, ringEval, v3P3_SQ, v3K5, vK5_SQ]
    | 1 => simp [evalP3K5, evalSQ_K5, ringEval, v3P3_SQ, v3K5, vK5_SQ]
    | _ + 2 => simp [evalP3K5, evalSQ_K5, ringEval, v3P3_SQ, vK5_SQ]
  | neg a ha => simp [evalSQ_K5, ringEval] at ha ⊢; rw [ha]
  | add a b ha hb => simp [evalSQ_K5, ringEval] at ha hb ⊢; rw [ha, hb]
  | sub a b ha hb => simp [evalSQ_K5, ringEval] at ha hb ⊢; rw [ha, hb]
  | mul a b ha hb => simp [evalSQ_K5, ringEval] at ha hb ⊢; rw [ha, hb]
  | pow a k ha => simp [evalSQ_K5, ringEval] at ha ⊢; rw [ha]

-- Nonvanishing of `fac_0 .. fac_6` and `D_all_expr` in `K5` via `evLoc` mod 1009!
private def vLoc_SQ : ℕ → LocK5
  | 0 => S_loc
  | 1 => Q_loc
  | _ => 0

private def v1009_SQ : ℕ → ZMod 1009
  | 0 => 2
  | 1 => 3
  | _ => 0

private lemma evalSQ_K5_ne_zero_of_mod1009 (e : Expr) (h : ringEval v1009_SQ e ≠ 0) :
    evalSQ_K5 e ≠ 0 := by
  have hsub : ∀ e' : Expr, LocK5.subtype (ringEval vLoc_SQ e') = evalSQ_K5 e' := by
    intro e'
    induction e' with
    | num c => simp [evalSQ_K5, ringEval]
    | natCast n => simp [evalSQ_K5, ringEval]
    | intCast z => simp [evalSQ_K5, ringEval]
    | var j =>
      match j with
      | 0 => rfl
      | 1 => rfl
      | _ + 2 => simp [evalSQ_K5, ringEval, vLoc_SQ, vK5_SQ]
    | neg a ha => simp [evalSQ_K5, ringEval] at ha ⊢; rw [ha]
    | add a b ha hb => simp [evalSQ_K5, ringEval] at ha hb ⊢; rw [ha, hb]
    | sub a b ha hb => simp [evalSQ_K5, ringEval] at ha hb ⊢; rw [ha, hb]
    | mul a b ha hb => simp [evalSQ_K5, ringEval] at ha hb ⊢; rw [ha, hb]
    | pow a k ha => simp [evalSQ_K5, ringEval] at ha ⊢; rw [ha]
  have hev : ∀ e' : Expr, evLoc (ringEval vLoc_SQ e') = ringEval v1009_SQ e' := by
    intro e'
    induction e' with
    | num c => simp [ringEval]
    | natCast n => simp [ringEval]
    | intCast z => simp [ringEval]
    | var j =>
      match j with
      | 0 => exact evLoc_S
      | 1 => exact evLoc_Q
      | _ + 2 => simp [ringEval, vLoc_SQ, v1009_SQ]
    | neg a ha => simp [ringEval] at ha ⊢; rw [ha]
    | add a b ha hb => simp [ringEval] at ha hb ⊢; rw [ha, hb]
    | sub a b ha hb => simp [ringEval] at ha hb ⊢; rw [ha, hb]
    | mul a b ha hb => simp [ringEval] at ha hb ⊢; rw [ha, hb]
    | pow a k ha => simp [ringEval] at ha ⊢; rw [ha]
  rw [← hsub e]
  exact LocK5.ne_zero_of_evLoc (by rw [hev e]; exact h)

private lemma fac_0_ne : evalSQ_K5 fac_0 ≠ 0 := evalSQ_K5_ne_zero_of_mod1009 fac_0 (by decide)
private lemma fac_1_ne : evalSQ_K5 fac_1 ≠ 0 := evalSQ_K5_ne_zero_of_mod1009 fac_1 (by decide)
private lemma fac_2_ne : evalSQ_K5 fac_2 ≠ 0 := evalSQ_K5_ne_zero_of_mod1009 fac_2 (by decide)
private lemma fac_3_ne : evalSQ_K5 fac_3 ≠ 0 := evalSQ_K5_ne_zero_of_mod1009 fac_3 (by decide)
private lemma fac_4_ne : evalSQ_K5 fac_4 ≠ 0 := evalSQ_K5_ne_zero_of_mod1009 fac_4 (by decide)
private lemma fac_5_ne : evalSQ_K5 fac_5 ≠ 0 := evalSQ_K5_ne_zero_of_mod1009 fac_5 (by decide)
private lemma fac_6_ne : evalSQ_K5 fac_6 ≠ 0 := evalSQ_K5_ne_zero_of_mod1009 fac_6 (by decide)

private lemma D_all_K5_ne : evalSQ_K5 D_all_expr ≠ 0 := by
  simp only [D_all_expr, evalSQ_K5, ringEval]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero fac_0_ne fac_1_ne) (pow_ne_zero 7 fac_2_ne)) (pow_ne_zero 13 fac_3_ne))
    (pow_ne_zero 2 fac_4_ne)) (pow_ne_zero 4 fac_5_ne)) fac_6_ne

private lemma fac_4_eq_neg_L : evalSQ_K5 fac_4 = -L_K := by
  simp only [fac_4, evalSQ_K5, ringEval, vK5_SQ, L_K, Int.cast_neg, Int.cast_ofNat]; ring

-- Exact identification of `k5Params.Q5_z` and `k5Params.Q7_z` with `Q5WeightsData.Q5_c`, `Q7_c`!
private lemma Q5_poly_eval_eq {R : Type*} [Field R] [CharZero R] (S Q U : R) :
    let ca := (-625 / 81 * S ^ 2 + 500 / 27 * S * Q - 25 / 3 * Q ^ 2) +
              (143 / 81 * S ^ 2 - 184 / 27 * S * Q + 52 / 9 * Q ^ 2) * U +
              (-4 / 81 * S ^ 2 + 8 / 27 * S * Q - 4 / 9 * Q ^ 2) * U ^ 2
    let cb := (250 / 27 * S ^ 2 - 50 / 3 * S * Q) +
              (-92 / 27 * S ^ 2 + 104 / 9 * S * Q - 22 / 3 * Q ^ 2 + 10 / 7 * Q + 10 / 7) * U +
              (4 / 27 * S ^ 2 - 8 / 9 * S * Q + 4 / 3 * Q ^ 2) * U ^ 2
    let q20 := (-625 / 81 * S + 250 / 27 * Q) + (143 / 81 * S - 92 / 27 * Q) * U + (-4 / 81 * S + 4 / 27 * Q) * U ^ 2
    let q11 := (500 / 27 * S - 50 / 3 * Q) + (-184 / 27 * S + 104 / 9 * Q) * U + (8 / 27 * S - 8 / 9 * Q) * U ^ 2
    let q02 := (-25 / 3 * S) + (52 / 9 * S - 22 / 3 * Q + 5 / 7) * U + (-4 / 9 * S + 4 / 3 * Q) * U ^ 2
    let v : ℕ → R := fun | 0 => S | 1 => Q | _ => 0
    2893401 * (q20 * cb ^ 2 - q11 * ca * cb + q02 * ca ^ 2) =
      ringEval v Q5_c0 + ringEval v Q5_c1 * U + ringEval v Q5_c2 * U ^ 2 +
      ringEval v Q5_c3 * U ^ 3 + ringEval v Q5_c4 * U ^ 4 + ringEval v Q5_c5 * U ^ 5 := by
  simp only [Q5_c0, Q5_c1, Q5_c2, Q5_c3, Q5_c4, Q5_c5, ringEval, Int.cast_neg, Int.cast_ofNat]
  ring

private lemma Q7_poly_eval_eq {R : Type*} [Field R] [CharZero R] (S Q U : R) :
    let ca := (-625 / 81 * S ^ 2 + 500 / 27 * S * Q - 25 / 3 * Q ^ 2) +
              (143 / 81 * S ^ 2 - 184 / 27 * S * Q + 52 / 9 * Q ^ 2) * U +
              (-4 / 81 * S ^ 2 + 8 / 27 * S * Q - 4 / 9 * Q ^ 2) * U ^ 2
    let cb := (250 / 27 * S ^ 2 - 50 / 3 * S * Q) +
              (-92 / 27 * S ^ 2 + 104 / 9 * S * Q - 22 / 3 * Q ^ 2 + 10 / 7 * Q + 10 / 7) * U +
              (4 / 27 * S ^ 2 - 8 / 9 * S * Q + 4 / 3 * Q ^ 2) * U ^ 2
    let c30 := (-625 / 243 : R) + 143 / 243 * U - 4 / 243 * U ^ 2
    let c21 := (250 / 27 : R) - 92 / 27 * U + 4 / 27 * U ^ 2
    let c12 := (-25 / 3 : R) + 52 / 9 * U - 4 / 9 * U ^ 2
    let c03 := (-22 / 9 : R) * U + 4 / 9 * U ^ 2
    let v : ℕ → R := fun | 0 => S | 1 => Q | _ => 0
    1640558367 * (c30 * cb ^ 3 - c21 * ca * cb ^ 2 + c12 * ca ^ 2 * cb - c03 * ca ^ 3) =
      2 * (ringEval v Q7_c0 + ringEval v Q7_c1 * U + ringEval v Q7_c2 * U ^ 2 +
        ringEval v Q7_c3 * U ^ 3 + ringEval v Q7_c4 * U ^ 4 + ringEval v Q7_c5 * U ^ 5 +
        ringEval v Q7_c6 * U ^ 6 + ringEval v Q7_c7 * U ^ 7) := by
  simp only [Q7_c0, Q7_c1, Q7_c2, Q7_c3, Q7_c4, Q7_c5, Q7_c6, Q7_c7, ringEval, Int.cast_neg, Int.cast_ofNat]
  ring

private def Q5_pol_K5 : K5[X] :=
  ∑ j : Fin 6, Polynomial.C (evalSQ_K5 (Q5_c j)) * Polynomial.X ^ j.val

private def Q7_pol_K5 : K5[X] :=
  ∑ j : Fin 8, Polynomial.C (evalSQ_K5 (Q7_c j)) * Polynomial.X ^ j.val

private lemma Q5_K5_eq_scaled :
    Polynomial.C (2893401 : K5) * k5Params.Q5_z = Q5_pol_K5 := by
  have hinf : Infinite K5 := Infinite.of_injective (Nat.cast : ℕ → K5) Nat.cast_injective
  apply Polynomial.funext; intro u
  have hring := Q5_poly_eval_eq S_K Q_K u
  have hv : ∀ e : Expr, (∀ k ≥ 2, e ≠ .var k) → True := fun _ _ => trivial
  have hQ5_ev : (Polynomial.C (2893401 : K5) * k5Params.Q5_z).eval u =
      2893401 * (
        ((-625 / 81 * S_K + 250 / 27 * Q_K) + (143 / 81 * S_K - 92 / 27 * Q_K) * u + (-4 / 81 * S_K + 4 / 27 * Q_K) * u ^ 2) *
          ((250 / 27 * S_K ^ 2 - 50 / 3 * S_K * Q_K) +
            (-92 / 27 * S_K ^ 2 + 104 / 9 * S_K * Q_K - 22 / 3 * Q_K ^ 2 + 10 / 7 * Q_K + 10 / 7) * u +
            (4 / 27 * S_K ^ 2 - 8 / 9 * S_K * Q_K + 4 / 3 * Q_K ^ 2) * u ^ 2) ^ 2 -
        ((500 / 27 * S_K - 50 / 3 * Q_K) + (-184 / 27 * S_K + 104 / 9 * Q_K) * u + (8 / 27 * S_K - 8 / 9 * Q_K) * u ^ 2) *
          ((-625 / 81 * S_K ^ 2 + 500 / 27 * S_K * Q_K - 25 / 3 * Q_K ^ 2) +
            (143 / 81 * S_K ^ 2 - 184 / 27 * S_K * Q_K + 52 / 9 * Q_K ^ 2) * u +
            (-4 / 81 * S_K ^ 2 + 8 / 27 * S_K * Q_K - 4 / 9 * Q_K ^ 2) * u ^ 2) *
          ((250 / 27 * S_K ^ 2 - 50 / 3 * S_K * Q_K) +
            (-92 / 27 * S_K ^ 2 + 104 / 9 * S_K * Q_K - 22 / 3 * Q_K ^ 2 + 10 / 7 * Q_K + 10 / 7) * u +
            (4 / 27 * S_K ^ 2 - 8 / 9 * S_K * Q_K + 4 / 3 * Q_K ^ 2) * u ^ 2) +
        ((-25 / 3 * S_K) + (52 / 9 * S_K - 22 / 3 * Q_K + 5 / 7) * u + (-4 / 9 * S_K + 4 / 3 * Q_K) * u ^ 2) *
          ((-625 / 81 * S_K ^ 2 + 500 / 27 * S_K * Q_K - 25 / 3 * Q_K ^ 2) +
            (143 / 81 * S_K ^ 2 - 184 / 27 * S_K * Q_K + 52 / 9 * Q_K ^ 2) * u +
            (-4 / 81 * S_K ^ 2 + 8 / 27 * S_K * Q_K - 4 / 9 * Q_K ^ 2) * u ^ 2) ^ 2) := by
    simp only [CoverParams.Q5_z, CoverParams.q20, CoverParams.q11, CoverParams.q02,
      CoverParams.ca_h, CoverParams.cb_h, CoverParams.quadU,
      CoverParams.inv9, CoverParams.inv27, CoverParams.inv81,
      k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q,
      Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat]
    ring
  rw [hQ5_ev, hring]
  have hsum : Q5_pol_K5.eval u =
      evalSQ_K5 Q5_c0 + evalSQ_K5 Q5_c1 * u + evalSQ_K5 Q5_c2 * u ^ 2 +
      evalSQ_K5 Q5_c3 * u ^ 3 + evalSQ_K5 Q5_c4 * u ^ 4 + evalSQ_K5 Q5_c5 * u ^ 5 := by
    simp only [Q5_pol_K5, Fin.sum_univ_six, Q5_c, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    change evalSQ_K5 Q5_c0 * u ^ 0 + evalSQ_K5 Q5_c1 * u ^ 1 + evalSQ_K5 Q5_c2 * u ^ 2 +
      evalSQ_K5 Q5_c3 * u ^ 3 + evalSQ_K5 Q5_c4 * u ^ 4 + evalSQ_K5 Q5_c5 * u ^ 5 = _
    ring
  rw [hsum]; rfl

private lemma Q7_K5_eq_scaled :
    Polynomial.C (1640558367 : K5) * k5Params.Q7_z = Polynomial.C (2 : K5) * Q7_pol_K5 := by
  have hinf : Infinite K5 := Infinite.of_injective (Nat.cast : ℕ → K5) Nat.cast_injective
  apply Polynomial.funext; intro u
  have hring := Q7_poly_eval_eq S_K Q_K u
  have hQ7_ev : (Polynomial.C (1640558367 : K5) * k5Params.Q7_z).eval u =
      1640558367 * (
        ((-625 / 243 : K5) + 143 / 243 * u - 4 / 243 * u ^ 2) *
          ((250 / 27 * S_K ^ 2 - 50 / 3 * S_K * Q_K) +
            (-92 / 27 * S_K ^ 2 + 104 / 9 * S_K * Q_K - 22 / 3 * Q_K ^ 2 + 10 / 7 * Q_K + 10 / 7) * u +
            (4 / 27 * S_K ^ 2 - 8 / 9 * S_K * Q_K + 4 / 3 * Q_K ^ 2) * u ^ 2) ^ 3 -
        ((250 / 27 : K5) - 92 / 27 * u + 4 / 27 * u ^ 2) *
          ((-625 / 81 * S_K ^ 2 + 500 / 27 * S_K * Q_K - 25 / 3 * Q_K ^ 2) +
            (143 / 81 * S_K ^ 2 - 184 / 27 * S_K * Q_K + 52 / 9 * Q_K ^ 2) * u +
            (-4 / 81 * S_K ^ 2 + 8 / 27 * S_K * Q_K - 4 / 9 * Q_K ^ 2) * u ^ 2) *
          ((250 / 27 * S_K ^ 2 - 50 / 3 * S_K * Q_K) +
            (-92 / 27 * S_K ^ 2 + 104 / 9 * S_K * Q_K - 22 / 3 * Q_K ^ 2 + 10 / 7 * Q_K + 10 / 7) * u +
            (4 / 27 * S_K ^ 2 - 8 / 9 * S_K * Q_K + 4 / 3 * Q_K ^ 2) * u ^ 2) ^ 2 +
        ((-25 / 3 : K5) + 52 / 9 * u - 4 / 9 * u ^ 2) *
          ((-625 / 81 * S_K ^ 2 + 500 / 27 * S_K * Q_K - 25 / 3 * Q_K ^ 2) +
            (143 / 81 * S_K ^ 2 - 184 / 27 * S_K * Q_K + 52 / 9 * Q_K ^ 2) * u +
            (-4 / 81 * S_K ^ 2 + 8 / 27 * S_K * Q_K - 4 / 9 * Q_K ^ 2) * u ^ 2) ^ 2 *
          ((250 / 27 * S_K ^ 2 - 50 / 3 * S_K * Q_K) +
            (-92 / 27 * S_K ^ 2 + 104 / 9 * S_K * Q_K - 22 / 3 * Q_K ^ 2 + 10 / 7 * Q_K + 10 / 7) * u +
            (4 / 27 * S_K ^ 2 - 8 / 9 * S_K * Q_K + 4 / 3 * Q_K ^ 2) * u ^ 2) -
        ((-22 / 9 : K5) * u + 4 / 9 * u ^ 2) *
          ((-625 / 81 * S_K ^ 2 + 500 / 27 * S_K * Q_K - 25 / 3 * Q_K ^ 2) +
            (143 / 81 * S_K ^ 2 - 184 / 27 * S_K * Q_K + 52 / 9 * Q_K ^ 2) * u +
            (-4 / 81 * S_K ^ 2 + 8 / 27 * S_K * Q_K - 4 / 9 * Q_K ^ 2) * u ^ 2) ^ 3) := by
    simp only [CoverParams.Q7_z, CoverParams.c30, CoverParams.c21, CoverParams.c12, CoverParams.c03,
      CoverParams.ca_h, CoverParams.cb_h, CoverParams.quadU,
      CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, CoverParams.inv243,
      k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q,
      Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_zero]
    ring
  rw [hQ7_ev, hring]
  have hsum : (Polynomial.C (2 : K5) * Q7_pol_K5).eval u =
      2 * (evalSQ_K5 Q7_c0 + evalSQ_K5 Q7_c1 * u + evalSQ_K5 Q7_c2 * u ^ 2 +
        evalSQ_K5 Q7_c3 * u ^ 3 + evalSQ_K5 Q7_c4 * u ^ 4 + evalSQ_K5 Q7_c5 * u ^ 5 +
        evalSQ_K5 Q7_c6 * u ^ 6 + evalSQ_K5 Q7_c7 * u ^ 7) := by
    simp only [Q7_pol_K5, Fin.sum_univ_eight, Q7_c, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    change 2 * (evalSQ_K5 Q7_c0 * u ^ 0 + evalSQ_K5 Q7_c1 * u ^ 1 + evalSQ_K5 Q7_c2 * u ^ 2 +
      evalSQ_K5 Q7_c3 * u ^ 3 + evalSQ_K5 Q7_c4 * u ^ 4 + evalSQ_K5 Q7_c5 * u ^ 5 +
      evalSQ_K5 Q7_c6 * u ^ 6 + evalSQ_K5 Q7_c7 * u ^ 7) = _
    ring
  rw [hsum]; rfl

private lemma Q5_c5_eq_fac :
    evalSQ_K5 (Q5_c 5) = (lc5_const : K5) * evalSQ_K5 lc5_fac_expr := by
  simp only [Q5_c, Q5_c5, lc5_const, lc5_fac_expr, fac_3, fac_4, evalSQ_K5, ringEval, vK5_SQ,
    Int.cast_neg, Int.cast_ofNat]
  ring

private lemma D_all_eq_lc5_mul :
    evalSQ_K5 D_all_expr = evalSQ_K5 lc5_fac_expr * evalSQ_K5 D_all_div_lc5_expr := by
  simp only [D_all_expr, lc5_fac_expr, D_all_div_lc5_expr, evalSQ_K5, ringEval]
  ring

-- Fast `PolyOps` evaluator for the 13 `Q5`/`Q7` recurrence & duality polynomials!
private def W_num_expr (k : Fin 13) : Expr :=
  .mul (.num (N_k_mul k)) (.mul (D_quot_expr k) (N_k_expr k))

private def q5Dot {α : Type*} (o : PolyOps α) (q50 q51 q52 q53 q54 q55 a0 a1 a2 a3 a4 a5 : α) : α :=
  o.add (o.add (o.add (o.mul q50 a0) (o.mul q51 a1)) (o.add (o.mul q52 a2) (o.mul q53 a3)))
        (o.add (o.mul q54 a4) (o.mul q55 a5))

private lemma q5Dot_rel {α β : Type*} {o1 : PolyOps α} {o2 : PolyOps β} {R : α → β → Prop}
    (hR : PolyOpsRel o1 o2 R) {q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 : α}
    {q0' q1' q2' q3' q4' q5' a0' a1' a2' a3' a4' a5' : β}
    (hq0 : R q0 q0') (hq1 : R q1 q1') (hq2 : R q2 q2') (hq3 : R q3 q3') (hq4 : R q4 q4') (hq5 : R q5 q5')
    (ha0 : R a0 a0') (ha1 : R a1 a1') (ha2 : R a2 a2') (ha3 : R a3 a3') (ha4 : R a4 a4') (ha5 : R a5 a5') :
    R (q5Dot o1 q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5) (q5Dot o2 q0' q1' q2' q3' q4' q5' a0' a1' a2' a3' a4' a5') :=
  hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_mul hq0 ha0) (hR.rel_mul hq1 ha1))
    (hR.rel_add (hR.rel_mul hq2 ha2) (hR.rel_mul hq3 ha3)))
    (hR.rel_add (hR.rel_mul hq4 ha4) (hR.rel_mul hq5 ha5))

private def q7Dot {α : Type*} (o : PolyOps α) (q70 q71 q72 q73 q74 q75 q76 q77 a0 a1 a2 a3 a4 a5 a6 a7 : α) : α :=
  o.add (o.add (o.add (o.mul q70 a0) (o.mul q71 a1)) (o.add (o.mul q72 a2) (o.mul q73 a3)))
        (o.add (o.add (o.mul q74 a4) (o.mul q75 a5)) (o.add (o.mul q76 a6) (o.mul q77 a7)))

private lemma q7Dot_rel {α β : Type*} {o1 : PolyOps α} {o2 : PolyOps β} {R : α → β → Prop}
    (hR : PolyOpsRel o1 o2 R) {q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 : α}
    {q0' q1' q2' q3' q4' q5' q6' q7' a0' a1' a2' a3' a4' a5' a6' a7' : β}
    (hq0 : R q0 q0') (hq1 : R q1 q1') (hq2 : R q2 q2') (hq3 : R q3 q3')
    (hq4 : R q4 q4') (hq5 : R q5 q5') (hq6 : R q6 q6') (hq7 : R q7 q7')
    (ha0 : R a0 a0') (ha1 : R a1 a1') (ha2 : R a2 a2') (ha3 : R a3 a3')
    (ha4 : R a4 a4') (ha5 : R a5 a5') (ha6 : R a6 a6') (ha7 : R a7 a7') :
    R (q7Dot o1 q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7)
      (q7Dot o2 q0' q1' q2' q3' q4' q5' q6' q7' a0' a1' a2' a3' a4' a5' a6' a7') :=
  hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_mul hq0 ha0) (hR.rel_mul hq1 ha1))
    (hR.rel_add (hR.rel_mul hq2 ha2) (hR.rel_mul hq3 ha3)))
    (hR.rel_add (hR.rel_add (hR.rel_mul hq4 ha4) (hR.rel_mul hq5 ha5))
      (hR.rel_add (hR.rel_mul hq6 ha6) (hR.rel_mul hq7 ha7)))

private def q5q7RecList {α : Type*} (o : PolyOps α) (S Q : α) : List α :=
  letB (powList o S 30 (o.ofInt 1)) fun pS =>
  letB (powList o Q 37 (o.ofInt 1)) fun pQ =>
  letB (o.add (o.mul (o.ofInt (-5)) S) (o.mul (o.ofInt 9) Q)) fun f2 =>
  letB (o.add (o.neg S) (o.mul (o.ofInt 3) Q)) fun f3 =>
  letB (o.add (o.add (o.ofInt (-45)) (o.mul (o.ofInt (-77)) S)) (o.mul (o.ofInt 210) Q)) fun f4 =>
  letB (evalExpr2 o S Q pS pQ fac_5) fun f5 =>
  letB (evalExpr2 o S Q pS pQ fac_6) fun f6 =>
  letB (o.mul f2 f2) fun f2_2 =>
  letB (o.mul f2_2 f2_2) fun f2_4 =>
  letB (o.mul f2_4 f2_2) fun f2_6 =>
  letB (o.mul f2_6 f2) fun f2_7 =>
  letB (o.mul (o.mul f3 f3) f3) fun f3_3 =>
  letB (o.mul f3_3 f3_3) fun f3_6 =>
  letB (o.mul f3_6 f3_3) fun f3_9 =>
  letB (o.mul f3_9 f3_3) fun f3_12 =>
  letB (o.mul f3_12 f3) fun f3_13 =>
  letB (o.mul f4 f4) fun f4_2 =>
  letB (o.mul f3_13 f4_2) fun d0 =>
  letB (o.mul (o.mul (o.mul S f2_2) f3_13) f4_2) fun d1 =>
  letB (o.mul (o.mul (o.mul S f2_4) f3_13) f4_2) fun d2 =>
  letB (o.mul (o.mul (o.mul S f2_6) f3_13) f4_2) fun d3 =>
  letB (o.mul (o.mul (o.mul S f2_7) f3_13) f4_2) fun d4 =>
  letB (o.mul (o.mul (o.mul S f2_7) f3_12) f4_2) fun d8 =>
  letB (o.mul (o.mul (o.mul S f2_7) f3_9) f4_2) fun d9 =>
  letB (o.mul (o.mul (o.mul S f2_7) f3_6) f4_2) fun d10 =>
  letB (o.mul (o.mul (o.mul S f2_7) f3_3) f4) fun d11 =>
  letB (o.mul S f2_7) fun d12 =>
  letB (o.mul (o.ofInt (N_k_mul 0)) (o.mul d0 (evalExpr2 o S Q pS pQ (N_k_expr 0)))) fun W0 =>
  letB (o.mul (o.ofInt (N_k_mul 1)) (o.mul d1 (evalExpr2 o S Q pS pQ (N_k_expr 1)))) fun W1 =>
  letB (o.mul (o.ofInt (N_k_mul 2)) (o.mul d2 (evalExpr2 o S Q pS pQ (N_k_expr 2)))) fun W2 =>
  letB (o.mul (o.ofInt (N_k_mul 3)) (o.mul d3 (evalExpr2 o S Q pS pQ (N_k_expr 3)))) fun W3 =>
  letB (o.mul (o.ofInt (N_k_mul 4)) (o.mul d4 (evalExpr2 o S Q pS pQ (N_k_expr 4)))) fun W4 =>
  letB (o.mul (o.ofInt (N_k_mul 5)) (o.mul d4 (evalExpr2 o S Q pS pQ (N_k_expr 5)))) fun W5 =>
  letB (o.mul (o.ofInt (N_k_mul 6)) (o.mul d4 (evalExpr2 o S Q pS pQ (N_k_expr 6)))) fun W6 =>
  letB (o.mul (o.ofInt (N_k_mul 7)) (o.mul d4 (evalExpr2 o S Q pS pQ (N_k_expr 7)))) fun W7 =>
  letB (o.mul (o.ofInt (N_k_mul 8)) (o.mul d8 (evalExpr2 o S Q pS pQ (N_k_expr 8)))) fun W8 =>
  letB (o.mul (o.ofInt (N_k_mul 9)) (o.mul d9 (evalExpr2 o S Q pS pQ (N_k_expr 9)))) fun W9 =>
  letB (o.mul (o.ofInt (N_k_mul 10)) (o.mul d10 (evalExpr2 o S Q pS pQ (N_k_expr 10)))) fun W10 =>
  letB (o.mul (o.ofInt (N_k_mul 11)) (o.mul d11 (evalExpr2 o S Q pS pQ (N_k_expr 11)))) fun W11 =>
  letB (o.mul (o.ofInt (N_k_mul 12)) (o.mul d12 (evalExpr2 o S Q pS pQ (N_k_expr 12)))) fun W12 =>
  letB (evalExpr2 o S Q pS pQ Q5_c0) fun q50 =>
  letB (evalExpr2 o S Q pS pQ Q5_c1) fun q51 =>
  letB (evalExpr2 o S Q pS pQ Q5_c2) fun q52 =>
  letB (evalExpr2 o S Q pS pQ Q5_c3) fun q53 =>
  letB (evalExpr2 o S Q pS pQ Q5_c4) fun q54 =>
  letB (evalExpr2 o S Q pS pQ Q5_c5) fun q55 =>
  letB (evalExpr2 o S Q pS pQ Q7_c0) fun q70 =>
  letB (evalExpr2 o S Q pS pQ Q7_c1) fun q71 =>
  letB (evalExpr2 o S Q pS pQ Q7_c2) fun q72 =>
  letB (evalExpr2 o S Q pS pQ Q7_c3) fun q73 =>
  letB (evalExpr2 o S Q pS pQ Q7_c4) fun q74 =>
  letB (evalExpr2 o S Q pS pQ Q7_c5) fun q75 =>
  letB (evalExpr2 o S Q pS pQ Q7_c6) fun q76 =>
  letB (evalExpr2 o S Q pS pQ Q7_c7) fun q77 =>
  letB (o.mul (o.mul (o.mul (o.mul (o.mul (o.mul Q S) f2_7) f3_9) f4) (o.pow f5 4)) f6) fun dlc5 =>
  [ q5Dot o q50 q51 q52 q53 q54 q55 W0 W1 W2 W3 W4 W5,
    q5Dot o q50 q51 q52 q53 q54 q55 W1 W2 W3 W4 W5 W6,
    q5Dot o q50 q51 q52 q53 q54 q55 W2 W3 W4 W5 W6 W7,
    q5Dot o q50 q51 q52 q53 q54 q55 W3 W4 W5 W6 W7 W8,
    q5Dot o q50 q51 q52 q53 q54 q55 W4 W5 W6 W7 W8 W9,
    q5Dot o q50 q51 q52 q53 q54 q55 W5 W6 W7 W8 W9 W10,
    q5Dot o q50 q51 q52 q53 q54 q55 W6 W7 W8 W9 W10 W11,
    q5Dot o q50 q51 q52 q53 q54 q55 W7 W8 W9 W10 W11 W12,
    q7Dot o q70 q71 q72 q73 q74 q75 q76 q77 W0 W1 W2 W3 W4 W5 W6 W7,
    q7Dot o q70 q71 q72 q73 q74 q75 q76 q77 W1 W2 W3 W4 W5 W6 W7 W8,
    q7Dot o q70 q71 q72 q73 q74 q75 q76 q77 W2 W3 W4 W5 W6 W7 W8 W9,
    q7Dot o q70 q71 q72 q73 q74 q75 q76 q77 W3 W4 W5 W6 W7 W8 W9 W10,
    o.sub (o.mul (o.ofInt lc5_const) (q7Dot o q70 q71 q72 q73 q74 q75 q76 q77 W4 W5 W6 W7 W8 W9 W10 W11))
          (o.mul (o.ofInt D_int_all) dlc5) ]

private lemma q5q7RecList_rel {α β : Type*} {o1 : PolyOps α} {o2 : PolyOps β} {R : α → β → Prop}
    (hR : PolyOpsRel o1 o2 R) {S1 Q1 : α} {S2 Q2 : β} (hS : R S1 S2) (hQ : R Q1 Q2) :
    List.Forall₂ R (q5q7RecList o1 S1 Q1) (q5q7RecList o2 S2 Q2) := by
  unfold q5q7RecList
  refine letB_rel (powList_rel hR hS 30 (hR.rel_ofInt 1)) fun hpS => ?_
  refine letB_rel (powList_rel hR hQ 37 (hR.rel_ofInt 1)) fun hpQ => ?_
  refine letB_rel (hR.rel_add (hR.rel_mul (hR.rel_ofInt (-5)) hS) (hR.rel_mul (hR.rel_ofInt 9) hQ)) fun hf2 => ?_
  refine letB_rel (hR.rel_add (hR.rel_neg hS) (hR.rel_mul (hR.rel_ofInt 3) hQ)) fun hf3 => ?_
  refine letB_rel (hR.rel_add (hR.rel_add (hR.rel_ofInt (-45)) (hR.rel_mul (hR.rel_ofInt (-77)) hS)) (hR.rel_mul (hR.rel_ofInt 210) hQ)) fun hf4 => ?_
  refine letB_rel (evalExpr2_rel hR hS hQ hpS hpQ fac_5) fun hf5 => ?_
  refine letB_rel (evalExpr2_rel hR hS hQ hpS hpQ fac_6) fun hf6 => ?_
  refine letB_rel (hR.rel_mul hf2 hf2) fun hf2_2 => ?_
  refine letB_rel (hR.rel_mul hf2_2 hf2_2) fun hf2_4 => ?_
  refine letB_rel (hR.rel_mul hf2_4 hf2_2) fun hf2_6 => ?_
  refine letB_rel (hR.rel_mul hf2_6 hf2) fun hf2_7 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_mul hf3 hf3) hf3) fun hf3_3 => ?_
  refine letB_rel (hR.rel_mul hf3_3 hf3_3) fun hf3_6 => ?_
  refine letB_rel (hR.rel_mul hf3_6 hf3_3) fun hf3_9 => ?_
  refine letB_rel (hR.rel_mul hf3_9 hf3_3) fun hf3_12 => ?_
  refine letB_rel (hR.rel_mul hf3_12 hf3) fun hf3_13 => ?_
  refine letB_rel (hR.rel_mul hf4 hf4) fun hf4_2 => ?_
  refine letB_rel (hR.rel_mul hf3_13 hf4_2) fun hd0 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul hS hf2_2) hf3_13) hf4_2) fun hd1 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul hS hf2_4) hf3_13) hf4_2) fun hd2 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul hS hf2_6) hf3_13) hf4_2) fun hd3 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul hS hf2_7) hf3_13) hf4_2) fun hd4 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul hS hf2_7) hf3_12) hf4_2) fun hd8 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul hS hf2_7) hf3_9) hf4_2) fun hd9 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul hS hf2_7) hf3_6) hf4_2) fun hd10 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul hS hf2_7) hf3_3) hf4) fun hd11 => ?_
  refine letB_rel (hR.rel_mul hS hf2_7) fun hd12 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd0 (evalExpr2_rel hR hS hQ hpS hpQ _))) fun hW0 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd1 (evalExpr2_rel hR hS hQ hpS hpQ _))) fun hW1 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd2 (evalExpr2_rel hR hS hQ hpS hpQ _))) fun hW2 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd3 (evalExpr2_rel hR hS hQ hpS hpQ _))) fun hW3 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd4 (evalExpr2_rel hR hS hQ hpS hpQ _))) fun hW4 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd4 (evalExpr2_rel hR hS hQ hpS hpQ _))) fun hW5 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd4 (evalExpr2_rel hR hS hQ hpS hpQ _))) fun hW6 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd4 (evalExpr2_rel hR hS hQ hpS hpQ _))) fun hW7 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd8 (evalExpr2_rel hR hS hQ hpS hpQ _))) fun hW8 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd9 (evalExpr2_rel hR hS hQ hpS hpQ _))) fun hW9 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd10 (evalExpr2_rel hR hS hQ hpS hpQ _))) fun hW10 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd11 (evalExpr2_rel hR hS hQ hpS hpQ _))) fun hW11 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd12 (evalExpr2_rel hR hS hQ hpS hpQ _))) fun hW12 => ?_
  refine letB_rel (evalExpr2_rel hR hS hQ hpS hpQ Q5_c0) fun hq50 => ?_
  refine letB_rel (evalExpr2_rel hR hS hQ hpS hpQ Q5_c1) fun hq51 => ?_
  refine letB_rel (evalExpr2_rel hR hS hQ hpS hpQ Q5_c2) fun hq52 => ?_
  refine letB_rel (evalExpr2_rel hR hS hQ hpS hpQ Q5_c3) fun hq53 => ?_
  refine letB_rel (evalExpr2_rel hR hS hQ hpS hpQ Q5_c4) fun hq54 => ?_
  refine letB_rel (evalExpr2_rel hR hS hQ hpS hpQ Q5_c5) fun hq55 => ?_
  refine letB_rel (evalExpr2_rel hR hS hQ hpS hpQ Q7_c0) fun hq70 => ?_
  refine letB_rel (evalExpr2_rel hR hS hQ hpS hpQ Q7_c1) fun hq71 => ?_
  refine letB_rel (evalExpr2_rel hR hS hQ hpS hpQ Q7_c2) fun hq72 => ?_
  refine letB_rel (evalExpr2_rel hR hS hQ hpS hpQ Q7_c3) fun hq73 => ?_
  refine letB_rel (evalExpr2_rel hR hS hQ hpS hpQ Q7_c4) fun hq74 => ?_
  refine letB_rel (evalExpr2_rel hR hS hQ hpS hpQ Q7_c5) fun hq75 => ?_
  refine letB_rel (evalExpr2_rel hR hS hQ hpS hpQ Q7_c6) fun hq76 => ?_
  refine letB_rel (evalExpr2_rel hR hS hQ hpS hpQ Q7_c7) fun hq77 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul (hR.rel_mul (hR.rel_mul (hR.rel_mul hQ hS) hf2_7) hf3_9) hf4)
    (hR.rel_pow 4 hf5)) hf6) fun hdlc5 => ?_
  exact List.Forall₂.cons (q5Dot_rel hR hq50 hq51 hq52 hq53 hq54 hq55 hW0 hW1 hW2 hW3 hW4 hW5)
    (List.Forall₂.cons (q5Dot_rel hR hq50 hq51 hq52 hq53 hq54 hq55 hW1 hW2 hW3 hW4 hW5 hW6)
    (List.Forall₂.cons (q5Dot_rel hR hq50 hq51 hq52 hq53 hq54 hq55 hW2 hW3 hW4 hW5 hW6 hW7)
    (List.Forall₂.cons (q5Dot_rel hR hq50 hq51 hq52 hq53 hq54 hq55 hW3 hW4 hW5 hW6 hW7 hW8)
    (List.Forall₂.cons (q5Dot_rel hR hq50 hq51 hq52 hq53 hq54 hq55 hW4 hW5 hW6 hW7 hW8 hW9)
    (List.Forall₂.cons (q5Dot_rel hR hq50 hq51 hq52 hq53 hq54 hq55 hW5 hW6 hW7 hW8 hW9 hW10)
    (List.Forall₂.cons (q5Dot_rel hR hq50 hq51 hq52 hq53 hq54 hq55 hW6 hW7 hW8 hW9 hW10 hW11)
    (List.Forall₂.cons (q5Dot_rel hR hq50 hq51 hq52 hq53 hq54 hq55 hW7 hW8 hW9 hW10 hW11 hW12)
    (List.Forall₂.cons (q7Dot_rel hR hq70 hq71 hq72 hq73 hq74 hq75 hq76 hq77 hW0 hW1 hW2 hW3 hW4 hW5 hW6 hW7)
    (List.Forall₂.cons (q7Dot_rel hR hq70 hq71 hq72 hq73 hq74 hq75 hq76 hq77 hW1 hW2 hW3 hW4 hW5 hW6 hW7 hW8)
    (List.Forall₂.cons (q7Dot_rel hR hq70 hq71 hq72 hq73 hq74 hq75 hq76 hq77 hW2 hW3 hW4 hW5 hW6 hW7 hW8 hW9)
    (List.Forall₂.cons (q7Dot_rel hR hq70 hq71 hq72 hq73 hq74 hq75 hq76 hq77 hW3 hW4 hW5 hW6 hW7 hW8 hW9 hW10)
    (List.Forall₂.cons (hR.rel_sub (hR.rel_mul (hR.rel_ofInt _)
        (q7Dot_rel hR hq70 hq71 hq72 hq73 hq74 hq75 hq76 hq77 hW4 hW5 hW6 hW7 hW8 hW9 hW10 hW11))
      (hR.rel_mul (hR.rel_ofInt _) hdlc5)) List.Forall₂.nil))))))))))))

private def q5q7Lim : ℕ := Nat.pow 2 455
private def q5q7B : ℤ := Int.ofNat q5q7Lim

private def checkQ5Q7Bounds : Bool :=
  (q5q7RecList pbOps ⟨1, 0, 0, 1⟩ ⟨0, 1, 0, 25⟩).all fun b =>
    Nat.blt b.dQ 50 && Nat.beq b.dT 0 && Nat.blt b.M q5q7Lim

private def checkQ5Q7Chunk (lo : ℤ) (n : ℕ) : Bool :=
  allRange lo n fun q =>
    (q5q7RecList intOps q5q7B q).all (fun z => z == 0)

private lemma checkQ5Q7Chunk_append (lo : ℤ) (m n : ℕ) :
    checkQ5Q7Chunk lo (m + n) = (checkQ5Q7Chunk lo m && checkQ5Q7Chunk (lo + (m : ℤ)) n) :=
  allRange_append lo m n _

private lemma q5q7_bounds_ok : checkQ5Q7Bounds = true := by decide +kernel
private lemma q5q7_chunk_0 : checkQ5Q7Chunk (-24) 10 = true := by decide +kernel
private lemma q5q7_chunk_1 : checkQ5Q7Chunk (-14) 10 = true := by decide +kernel
private lemma q5q7_chunk_2 : checkQ5Q7Chunk (-4) 10 = true := by decide +kernel
private lemma q5q7_chunk_3 : checkQ5Q7Chunk 6 10 = true := by decide +kernel
private lemma q5q7_chunk_4 : checkQ5Q7Chunk 16 10 = true := by decide +kernel

private lemma q5q7_values_ok : checkQ5Q7Chunk (-24) 50 = true := by
  rw [show (50 : ℕ) = 10 + 40 from rfl, checkQ5Q7Chunk_append, q5q7_chunk_0, Bool.true_and]
  rw [show ((-24 : ℤ) + (10 : ℕ)) = -14 from rfl, show (40 : ℕ) = 10 + 30 from rfl, checkQ5Q7Chunk_append, q5q7_chunk_1, Bool.true_and]
  rw [show ((-14 : ℤ) + (10 : ℕ)) = -4 from rfl, show (30 : ℕ) = 10 + 20 from rfl, checkQ5Q7Chunk_append, q5q7_chunk_2, Bool.true_and]
  rw [show ((-4 : ℤ) + (10 : ℕ)) = 6 from rfl, show (20 : ℕ) = 10 + 10 from rfl, checkQ5Q7Chunk_append, q5q7_chunk_3, Bool.true_and]
  exact q5q7_chunk_4

private lemma q5q7RecList_poly3_zero :
    ∀ p ∈ q5q7RecList poly3Ops (MvPolynomial.X 0) (MvPolynomial.X 1), p = 0 := by
  have hb_ok : checkQ5Q7Bounds = true := q5q7_bounds_ok
  have hv_ok : checkQ5Q7Chunk (-24) 50 = true := q5q7_values_ok
  unfold checkQ5Q7Bounds at hb_ok
  unfold checkQ5Q7Chunk at hv_ok
  have hrelB := q5q7RecList_rel (respectsBoundRel 25 0) (respectsBound_X0 25 0) (respectsBound_X1 25 0)
  have hrelV : ∀ q ∈ rangeInt (-24) 50,
      List.Forall₂ (fun p z => MvPolynomial.eval (v3Int (2 ^ 455 : ℕ) q 0) p = z)
        (q5q7RecList poly3Ops (MvPolynomial.X 0) (MvPolynomial.X 1))
        (q5q7RecList intOps q5q7B q) := fun q _ =>
    q5q7RecList_rel (poly3ToIntRel (2 ^ 455 : ℕ) q 0) (by simp [v3Int, q5q7B, q5q7Lim]) (by simp [v3Int])
  have hallB : ∀ b ∈ q5q7RecList pbOps ⟨1, 0, 0, 1⟩ ⟨0, 1, 0, 25⟩, b.dQ < 50 ∧ b.dT = 0 ∧ b.M < 2 ^ 455 := by
    intro b hb
    have h := List.all_eq_true.mp hb_ok b hb
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  have hallV : ∀ q ∈ rangeInt (-24) 50, ∀ z ∈ q5q7RecList intOps q5q7B q, z = 0 := by
    intro q hq z hz
    have h1 := allRange_spec (-24) 50 _ hv_ok q hq
    exact beq_iff_eq.mp (List.all_eq_true.mp h1 z hz)
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  have hlenB := hrelB.length_eq
  have hb_rel : RespectsBound 25 0
      ((q5q7RecList poly3Ops (MvPolynomial.X 0) (MvPolynomial.X 1))[i])
      ((q5q7RecList pbOps ⟨1, 0, 0, 1⟩ ⟨0, 1, 0, 25⟩)[i]'(hlenB ▸ hi)) :=
    list_forall₂_getElem hrelB i hi (hlenB ▸ hi)
  obtain ⟨hdQ, hdT, hM⟩ := hallB _ (List.getElem_mem _)
  apply mvPoly3_eq_zero_of_kronecker_grid _ _ 25 0 (2 ^ 455) (rangeInt (-24) 50) {0}
    hb_rel (by rw [rangeInt_card]; exact hdQ)
    (rangeInt_natAbs_le (-24) 50 25 (by decide) (by decide))
    (by simp [hdT]) (fun t ht => by simp at ht; subst ht; simp) hM
  intro q hq t ht
  simp only [Finset.mem_singleton] at ht; subst ht
  have hrv := hrelV q hq
  have hlenV := hrv.length_eq
  have heq := list_forall₂_getElem hrv i hi (hlenV ▸ hi)
  rw [heq]
  exact hallV q hq _ (List.getElem_mem _)

private lemma dq_pow_chain_eq (f0 f1 f2 f3 f4 f5 f6 : K5) :
    let f2_2 := f2 * f2; let f2_4 := f2_2 * f2_2; let f2_6 := f2_4 * f2_2; let f2_7 := f2_6 * f2
    let f3_3 := f3 * f3 * f3; let f3_6 := f3_3 * f3_3; let f3_9 := f3_6 * f3_3
    let f3_12 := f3_9 * f3_3; let f3_13 := f3_12 * f3
    let f4_2 := f4 * f4
    (f3_13 * f4_2 = f3 ^ 13 * f4 ^ 2) ∧
    (f1 * f2_2 * f3_13 * f4_2 = f1 * f2 ^ 2 * f3 ^ 13 * f4 ^ 2) ∧
    (f1 * f2_4 * f3_13 * f4_2 = f1 * f2 ^ 4 * f3 ^ 13 * f4 ^ 2) ∧
    (f1 * f2_6 * f3_13 * f4_2 = f1 * f2 ^ 6 * f3 ^ 13 * f4 ^ 2) ∧
    (f1 * f2_7 * f3_13 * f4_2 = f1 * f2 ^ 7 * f3 ^ 13 * f4 ^ 2) ∧
    (f1 * f2_7 * f3_12 * f4_2 = f1 * f2 ^ 7 * f3 ^ 12 * f4 ^ 2) ∧
    (f1 * f2_7 * f3_9 * f4_2 = f1 * f2 ^ 7 * f3 ^ 9 * f4 ^ 2) ∧
    (f1 * f2_7 * f3_6 * f4_2 = f1 * f2 ^ 7 * f3 ^ 6 * f4 ^ 2) ∧
    (f1 * f2_7 * f3_3 * f4 = f1 * f2 ^ 7 * f3 ^ 3 * f4) ∧
    (f1 * f2_7 = f1 * f2 ^ 7) ∧
    (f0 * f1 * f2_7 * f3_9 * f4 * f5 ^ 4 * f6 = f0 * f1 * f2 ^ 7 * f3 ^ 9 * f4 * f5 ^ 4 * f6) ∧
    (f0 * f1 * f2_7 * f3_13 * f5 ^ 4 * f6 * f4 ^ 2 = f0 * f1 * f2 ^ 7 * f3 ^ 13 * f4 ^ 2 * f5 ^ 4 * f6) := by
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, by ring, by ring, by ring, by ring, by ring, by ring⟩

private lemma fac_K5_eqs :
    Q_K = evalSQ_K5 fac_0 ∧ S_K = evalSQ_K5 fac_1 ∧
    (-5 : K5) * S_K + 9 * Q_K = evalSQ_K5 fac_2 ∧
    -S_K + 3 * Q_K = evalSQ_K5 fac_3 ∧
    -45 + (-77 : K5) * S_K + 210 * Q_K = evalSQ_K5 fac_4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [fac_0, fac_1, fac_2, fac_3, fac_4, evalSQ_K5, ringEval, vK5_SQ, Int.cast_neg, Int.cast_ofNat]; try ring)

private lemma Q5_Q7_recurrences_K5 :
    (∀ k : Fin 8, ∑ j : Fin 6, evalSQ_K5 (Q5_c j) * evalSQ_K5 (W_num_expr ⟨k.val + j.val, by omega⟩) = 0) ∧
    (∀ m : Fin 4, ∑ j : Fin 8, evalSQ_K5 (Q7_c j) * evalSQ_K5 (W_num_expr ⟨m.val + j.val, by omega⟩) = 0) ∧
    ((lc5_const : K5) * ∑ j : Fin 8, evalSQ_K5 (Q7_c j) * evalSQ_K5 (W_num_expr ⟨4 + j.val, by omega⟩) =
      (D_int_all : K5) * evalSQ_K5 D_all_div_lc5_expr) := by
  have hrelK : List.Forall₂ (fun p x => evalP3K5 p = x)
      (q5q7RecList poly3Ops (MvPolynomial.X 0) (MvPolynomial.X 1))
      (q5q7RecList k5Ops S_K Q_K) :=
    q5q7RecList_rel poly3ToK5Rel (by simp [evalP3K5, v3K5]) (by simp [evalP3K5, v3K5])
  have hallK : ∀ x ∈ q5q7RecList k5Ops S_K Q_K, x = 0 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hlen := hrelK.length_eq
    have heq := list_forall₂_getElem hrelK i (hlen.symm ▸ hi) hi
    rw [← heq, q5q7RecList_poly3_zero _ (List.getElem_mem _), map_zero]
  have hev_eq (e : Expr) :
      evalExpr2 k5Ops S_K Q_K (powList k5Ops S_K 30 (k5Ops.ofInt 1)) (powList k5Ops Q_K 37 (k5Ops.ofInt 1)) e =
      evalSQ_K5 e := by
    have hX0 : evalP3K5 (MvPolynomial.X 0) = S_K := by simp [evalP3K5, v3K5]
    have hX1 : evalP3K5 (MvPolynomial.X 1) = Q_K := by simp [evalP3K5, v3K5]
    have h := evalExpr2_rel poly3ToK5Rel hX0 hX1
      (powList_rel poly3ToK5Rel hX0 30 (poly3ToK5Rel.rel_ofInt 1))
      (powList_rel poly3ToK5Rel hX1 37 (poly3ToK5Rel.rel_ofInt 1)) e
    rw [evalExpr2_poly3_eq, evalP3K5_ringEval_SQ] at h
    exact h.symm
  -- Rewrite `q5q7RecList k5Ops S_K Q_K` using `letB_step` (O(N), zero DAG expansion)!
  have hlist_eq : q5q7RecList k5Ops S_K Q_K =
      let w : Fin 13 → K5 := fun k => evalSQ_K5 (W_num_expr k)
      let q5 : Fin 6 → K5 := fun j => evalSQ_K5 (Q5_c j)
      let q7 : Fin 8 → K5 := fun j => evalSQ_K5 (Q7_c j)
      let r5 := fun a0 a1 a2 a3 a4 a5 =>
        (q5 0 * a0 + q5 1 * a1 + (q5 2 * a2 + q5 3 * a3)) + (q5 4 * a4 + q5 5 * a5)
      let r7 := fun a0 a1 a2 a3 a4 a5 a6 a7 =>
        (q7 0 * a0 + q7 1 * a1 + (q7 2 * a2 + q7 3 * a3)) +
          ((q7 4 * a4 + q7 5 * a5) + (q7 6 * a6 + q7 7 * a7))
      [ r5 (w 0) (w 1) (w 2) (w 3) (w 4) (w 5),
        r5 (w 1) (w 2) (w 3) (w 4) (w 5) (w 6),
        r5 (w 2) (w 3) (w 4) (w 5) (w 6) (w 7),
        r5 (w 3) (w 4) (w 5) (w 6) (w 7) (w 8),
        r5 (w 4) (w 5) (w 6) (w 7) (w 8) (w 9),
        r5 (w 5) (w 6) (w 7) (w 8) (w 9) (w 10),
        r5 (w 6) (w 7) (w 8) (w 9) (w 10) (w 11),
        r5 (w 7) (w 8) (w 9) (w 10) (w 11) (w 12),
        r7 (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7),
        r7 (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7) (w 8),
        r7 (w 2) (w 3) (w 4) (w 5) (w 6) (w 7) (w 8) (w 9),
        r7 (w 3) (w 4) (w 5) (w 6) (w 7) (w 8) (w 9) (w 10),
        (lc5_const : K5) * r7 (w 4) (w 5) (w 6) (w 7) (w 8) (w 9) (w 10) (w 11) -
          (D_int_all : K5) * evalSQ_K5 D_all_div_lc5_expr ] := by
    have hf := fac_K5_eqs
    have hW (k : Fin 13) : evalSQ_K5 (W_num_expr k) =
        (N_k_mul k : K5) * (evalSQ_K5 (D_quot_expr k) * evalSQ_K5 (N_k_expr k)) := rfl
    have hD0 : evalSQ_K5 (D_quot_expr 0) = evalSQ_K5 fac_3 ^ 13 * evalSQ_K5 fac_4 ^ 2 := rfl
    have hD1 : evalSQ_K5 (D_quot_expr 1) = evalSQ_K5 fac_1 * evalSQ_K5 fac_2 ^ 2 * evalSQ_K5 fac_3 ^ 13 * evalSQ_K5 fac_4 ^ 2 := rfl
    have hD2 : evalSQ_K5 (D_quot_expr 2) = evalSQ_K5 fac_1 * evalSQ_K5 fac_2 ^ 4 * evalSQ_K5 fac_3 ^ 13 * evalSQ_K5 fac_4 ^ 2 := rfl
    have hD3 : evalSQ_K5 (D_quot_expr 3) = evalSQ_K5 fac_1 * evalSQ_K5 fac_2 ^ 6 * evalSQ_K5 fac_3 ^ 13 * evalSQ_K5 fac_4 ^ 2 := rfl
    have hD4 : evalSQ_K5 (D_quot_expr 4) = evalSQ_K5 fac_1 * evalSQ_K5 fac_2 ^ 7 * evalSQ_K5 fac_3 ^ 13 * evalSQ_K5 fac_4 ^ 2 := rfl
    have hD5 : evalSQ_K5 (D_quot_expr 5) = evalSQ_K5 (D_quot_expr 4) := rfl
    have hD6 : evalSQ_K5 (D_quot_expr 6) = evalSQ_K5 (D_quot_expr 4) := rfl
    have hD7 : evalSQ_K5 (D_quot_expr 7) = evalSQ_K5 (D_quot_expr 4) := rfl
    have hD8 : evalSQ_K5 (D_quot_expr 8) = evalSQ_K5 fac_1 * evalSQ_K5 fac_2 ^ 7 * evalSQ_K5 fac_3 ^ 12 * evalSQ_K5 fac_4 ^ 2 := rfl
    have hD9 : evalSQ_K5 (D_quot_expr 9) = evalSQ_K5 fac_1 * evalSQ_K5 fac_2 ^ 7 * evalSQ_K5 fac_3 ^ 9 * evalSQ_K5 fac_4 ^ 2 := rfl
    have hD10 : evalSQ_K5 (D_quot_expr 10) = evalSQ_K5 fac_1 * evalSQ_K5 fac_2 ^ 7 * evalSQ_K5 fac_3 ^ 6 * evalSQ_K5 fac_4 ^ 2 := rfl
    have hD11 : evalSQ_K5 (D_quot_expr 11) = evalSQ_K5 fac_1 * evalSQ_K5 fac_2 ^ 7 * evalSQ_K5 fac_3 ^ 3 * evalSQ_K5 fac_4 := rfl
    have hD12 : evalSQ_K5 (D_quot_expr 12) = evalSQ_K5 fac_1 * evalSQ_K5 fac_2 ^ 7 := rfl
    have hDlc5 : evalSQ_K5 D_all_div_lc5_expr =
        evalSQ_K5 fac_0 * evalSQ_K5 fac_1 * evalSQ_K5 fac_2 ^ 7 * evalSQ_K5 fac_3 ^ 9 *
        evalSQ_K5 fac_4 * evalSQ_K5 fac_5 ^ 4 * evalSQ_K5 fac_6 := rfl
    unfold q5q7RecList
    rw [letB, letB]
    refine letB_step (y := evalSQ_K5 fac_2) (by simpa [k5Ops] using hf.2.2.1) ?_
    refine letB_step (y := evalSQ_K5 fac_3) (by simpa [k5Ops] using hf.2.2.2.1) ?_
    refine letB_step (y := evalSQ_K5 fac_4) (by simpa [k5Ops] using hf.2.2.2.2) ?_
    refine letB_step (hev_eq fac_5) ?_
    refine letB_step (hev_eq fac_6) ?_
    refine letB_step (y := evalSQ_K5 fac_2 ^ 2) (by dsimp [k5Ops]; ring) ?_
    refine letB_step (y := evalSQ_K5 fac_2 ^ 4) (by dsimp [k5Ops]; ring) ?_
    refine letB_step (y := evalSQ_K5 fac_2 ^ 6) (by dsimp [k5Ops]; ring) ?_
    refine letB_step (y := evalSQ_K5 fac_2 ^ 7) (by dsimp [k5Ops]; ring) ?_
    refine letB_step (y := evalSQ_K5 fac_3 ^ 3) (by dsimp [k5Ops]; ring) ?_
    refine letB_step (y := evalSQ_K5 fac_3 ^ 6) (by dsimp [k5Ops]; ring) ?_
    refine letB_step (y := evalSQ_K5 fac_3 ^ 9) (by dsimp [k5Ops]; ring) ?_
    refine letB_step (y := evalSQ_K5 fac_3 ^ 12) (by dsimp [k5Ops]; ring) ?_
    refine letB_step (y := evalSQ_K5 fac_3 ^ 13) (by dsimp [k5Ops]; ring) ?_
    refine letB_step (y := evalSQ_K5 fac_4 ^ 2) (by dsimp [k5Ops]; ring) ?_
    refine letB_step (y := evalSQ_K5 (D_quot_expr 0)) (by dsimp [k5Ops]; rw [hD0]) ?_
    refine letB_step (y := evalSQ_K5 (D_quot_expr 1)) (by dsimp [k5Ops]; rw [hD1, ← hf.2.1]) ?_
    refine letB_step (y := evalSQ_K5 (D_quot_expr 2)) (by dsimp [k5Ops]; rw [hD2, ← hf.2.1]) ?_
    refine letB_step (y := evalSQ_K5 (D_quot_expr 3)) (by dsimp [k5Ops]; rw [hD3, ← hf.2.1]) ?_
    refine letB_step (y := evalSQ_K5 (D_quot_expr 4)) (by dsimp [k5Ops]; rw [hD4, ← hf.2.1]) ?_
    refine letB_step (y := evalSQ_K5 (D_quot_expr 8)) (by dsimp [k5Ops]; rw [hD8, ← hf.2.1]) ?_
    refine letB_step (y := evalSQ_K5 (D_quot_expr 9)) (by dsimp [k5Ops]; rw [hD9, ← hf.2.1]) ?_
    refine letB_step (y := evalSQ_K5 (D_quot_expr 10)) (by dsimp [k5Ops]; rw [hD10, ← hf.2.1]) ?_
    refine letB_step (y := evalSQ_K5 (D_quot_expr 11)) (by dsimp [k5Ops]; rw [hD11, ← hf.2.1]) ?_
    refine letB_step (y := evalSQ_K5 (D_quot_expr 12)) (by dsimp [k5Ops]; rw [hD12, ← hf.2.1]) ?_
    refine letB_step (y := evalSQ_K5 (W_num_expr 0)) (by rw [hev_eq, hW]; rfl) ?_
    refine letB_step (y := evalSQ_K5 (W_num_expr 1)) (by rw [hev_eq, hW]; rfl) ?_
    refine letB_step (y := evalSQ_K5 (W_num_expr 2)) (by rw [hev_eq, hW]; rfl) ?_
    refine letB_step (y := evalSQ_K5 (W_num_expr 3)) (by rw [hev_eq, hW]; rfl) ?_
    refine letB_step (y := evalSQ_K5 (W_num_expr 4)) (by rw [hev_eq, hW]; rfl) ?_
    refine letB_step (y := evalSQ_K5 (W_num_expr 5)) (by rw [hev_eq, hW, hD5]; rfl) ?_
    refine letB_step (y := evalSQ_K5 (W_num_expr 6)) (by rw [hev_eq, hW, hD6]; rfl) ?_
    refine letB_step (y := evalSQ_K5 (W_num_expr 7)) (by rw [hev_eq, hW, hD7]; rfl) ?_
    refine letB_step (y := evalSQ_K5 (W_num_expr 8)) (by rw [hev_eq, hW]; rfl) ?_
    refine letB_step (y := evalSQ_K5 (W_num_expr 9)) (by rw [hev_eq, hW]; rfl) ?_
    refine letB_step (y := evalSQ_K5 (W_num_expr 10)) (by rw [hev_eq, hW]; rfl) ?_
    refine letB_step (y := evalSQ_K5 (W_num_expr 11)) (by rw [hev_eq, hW]; rfl) ?_
    refine letB_step (y := evalSQ_K5 (W_num_expr 12)) (by rw [hev_eq, hW]; rfl) ?_
    refine letB_step (hev_eq Q5_c0) ?_
    refine letB_step (hev_eq Q5_c1) ?_
    refine letB_step (hev_eq Q5_c2) ?_
    refine letB_step (hev_eq Q5_c3) ?_
    refine letB_step (hev_eq Q5_c4) ?_
    refine letB_step (hev_eq Q5_c5) ?_
    refine letB_step (hev_eq Q7_c0) ?_
    refine letB_step (hev_eq Q7_c1) ?_
    refine letB_step (hev_eq Q7_c2) ?_
    refine letB_step (hev_eq Q7_c3) ?_
    refine letB_step (hev_eq Q7_c4) ?_
    refine letB_step (hev_eq Q7_c5) ?_
    refine letB_step (hev_eq Q7_c6) ?_
    refine letB_step (hev_eq Q7_c7) ?_
    refine letB_step (y := evalSQ_K5 D_all_div_lc5_expr) (by dsimp [k5Ops]; rw [hDlc5, ← hf.1, ← hf.2.1]) ?_
    simp only [q5Dot, q7Dot, k5Ops]; rfl
  rw [hlist_eq] at hallK
  refine ⟨?_, ?_, ?_⟩
  · intro k
    have hk : ∀ i : Fin 8,
        ((evalSQ_K5 (Q5_c 0) * evalSQ_K5 (W_num_expr ⟨i.val + 0, by omega⟩) +
          evalSQ_K5 (Q5_c 1) * evalSQ_K5 (W_num_expr ⟨i.val + 1, by omega⟩) +
         (evalSQ_K5 (Q5_c 2) * evalSQ_K5 (W_num_expr ⟨i.val + 2, by omega⟩) +
          evalSQ_K5 (Q5_c 3) * evalSQ_K5 (W_num_expr ⟨i.val + 3, by omega⟩))) +
         (evalSQ_K5 (Q5_c 4) * evalSQ_K5 (W_num_expr ⟨i.val + 4, by omega⟩) +
          evalSQ_K5 (Q5_c 5) * evalSQ_K5 (W_num_expr ⟨i.val + 5, by omega⟩))) = 0 := fun i => by
      fin_cases i <;> exact hallK _ (by simp)
    have h0 := hk k
    rw [Fin.sum_univ_six]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two,
      show (3 : Fin 6).val = 3 from rfl, show (4 : Fin 6).val = 4 from rfl, show (5 : Fin 6).val = 5 from rfl]
    linear_combination h0
  · intro m
    have hm : ∀ i : Fin 4,
        ((evalSQ_K5 (Q7_c 0) * evalSQ_K5 (W_num_expr ⟨i.val + 0, by omega⟩) +
          evalSQ_K5 (Q7_c 1) * evalSQ_K5 (W_num_expr ⟨i.val + 1, by omega⟩) +
         (evalSQ_K5 (Q7_c 2) * evalSQ_K5 (W_num_expr ⟨i.val + 2, by omega⟩) +
          evalSQ_K5 (Q7_c 3) * evalSQ_K5 (W_num_expr ⟨i.val + 3, by omega⟩))) +
        ((evalSQ_K5 (Q7_c 4) * evalSQ_K5 (W_num_expr ⟨i.val + 4, by omega⟩) +
          evalSQ_K5 (Q7_c 5) * evalSQ_K5 (W_num_expr ⟨i.val + 5, by omega⟩)) +
         (evalSQ_K5 (Q7_c 6) * evalSQ_K5 (W_num_expr ⟨i.val + 6, by omega⟩) +
          evalSQ_K5 (Q7_c 7) * evalSQ_K5 (W_num_expr ⟨i.val + 7, by omega⟩)))) = 0 := fun i => by
      fin_cases i <;> exact hallK _ (by simp)
    have h0 := hm m
    rw [Fin.sum_univ_eight]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two,
      show (3 : Fin 8).val = 3 from rfl, show (4 : Fin 8).val = 4 from rfl, show (5 : Fin 8).val = 5 from rfl,
      show (6 : Fin 8).val = 6 from rfl, show (7 : Fin 8).val = 7 from rfl]
    linear_combination h0
  · have h12 : (lc5_const : K5) *
        ((evalSQ_K5 (Q7_c 0) * evalSQ_K5 (W_num_expr 4) +
          evalSQ_K5 (Q7_c 1) * evalSQ_K5 (W_num_expr 5) +
         (evalSQ_K5 (Q7_c 2) * evalSQ_K5 (W_num_expr 6) +
          evalSQ_K5 (Q7_c 3) * evalSQ_K5 (W_num_expr 7))) +
        ((evalSQ_K5 (Q7_c 4) * evalSQ_K5 (W_num_expr 8) +
          evalSQ_K5 (Q7_c 5) * evalSQ_K5 (W_num_expr 9)) +
         (evalSQ_K5 (Q7_c 6) * evalSQ_K5 (W_num_expr 10) +
          evalSQ_K5 (Q7_c 7) * evalSQ_K5 (W_num_expr 11)))) -
        (D_int_all : K5) * evalSQ_K5 D_all_div_lc5_expr = 0 := hallK _ (by simp)
    rw [Fin.sum_univ_eight]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two,
      show (3 : Fin 8).val = 3 from rfl, show (4 : Fin 8).val = 4 from rfl, show (5 : Fin 8).val = 5 from rfl,
      show (6 : Fin 8).val = 6 from rfl, show (7 : Fin 8).val = 7 from rfl,
      show ∀ h : 4 + 0 < 13, (⟨4 + 0, h⟩ : Fin 13) = 4 from fun _ => rfl,
      show ∀ h : 4 + 1 < 13, (⟨4 + 1, h⟩ : Fin 13) = 5 from fun _ => rfl,
      show ∀ h : 4 + 2 < 13, (⟨4 + 2, h⟩ : Fin 13) = 6 from fun _ => rfl,
      show ∀ h : 4 + 3 < 13, (⟨4 + 3, h⟩ : Fin 13) = 7 from fun _ => rfl,
      show ∀ h : 4 + 4 < 13, (⟨4 + 4, h⟩ : Fin 13) = 8 from fun _ => rfl,
      show ∀ h : 4 + 5 < 13, (⟨4 + 5, h⟩ : Fin 13) = 9 from fun _ => rfl,
      show ∀ h : 4 + 6 < 13, (⟨4 + 6, h⟩ : Fin 13) = 10 from fun _ => rfl,
      show ∀ h : 4 + 7 < 13, (⟨4 + 7, h⟩ : Fin 13) = 11 from fun _ => rfl]
    linear_combination h12

-- Rational Q5 weight `W_K5 k = W_num_K5 k / (D_int_all * D_all_K5)` (for integer polynomials `Q5_pol`, `Q7_pol`)
private def W_K5 (k : Fin 13) : K5 :=
  evalSQ_K5 (W_num_expr k) / ((D_int_all : K5) * evalSQ_K5 D_all_expr)

-- Scaled Q5 weight for `k5Params.Q5_z`, `k5Params.Q7_z`
private def W_K5_scaled (k : Fin 13) : K5 :=
  ((sc5_den * sc7_den : ℤ) : K5) / ((sc5_num * sc7_num : ℤ) : K5) * W_K5 k

private lemma infinityCoefficient_apply (g : RatFunc CoverL) :
    CrossedRationalResidue.infinityCoefficient g =
      CrossedRationalResidue.residue (0 : CoverL) ((RatFunc.X ^ 2)⁻¹ * reciprocal g) := rfl

-- Euler residue trace on `X^m / Q5_pol` (`m = 0..4`) via `CrossedRationalResidue.residue_sum_eq_infinity`!
private lemma sum_RQ5_euler_power (m : Fin 5) :
    ∑ r ∈ RQ5, r ^ m.val / (Q5_pol_K5.map ιL_K5).derivative.eval r =
      if m.val = 4 then ιL_K5 (evalSQ_K5 (Q5_c 5))⁻¹ else 0 := by
  set Q5L : CoverL[X] := Q5_pol_K5.map ιL_K5
  have h2893401 : (2893401 : K5) ≠ 0 := by exact_mod_cast (by decide : (2893401 : ℕ) ≠ 0)
  have hQ5L_eq : Q5L = Polynomial.C (ιL_K5 2893401) * k5Params.Q5_z.map ιL_K5 := by
    dsimp only [Q5L]
    rw [← Q5_K5_eq_scaled, Polynomial.map_mul, Polynomial.map_C]
  have hQ5L_ne : Q5L ≠ 0 := by
    rw [hQ5L_eq]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr (map_ne_zero_iff _ ιL_K5.injective |>.mpr h2893401))
      (Polynomial.map_ne_zero Q5_K5_ne_zero)
  have hQ5L_deg : Q5L.natDegree = 5 := by
    rw [hQ5L_eq, Polynomial.natDegree_C_mul (map_ne_zero_iff _ ιL_K5.injective |>.mpr h2893401),
      Polynomial.natDegree_map_eq_of_injective ιL_K5.injective, Q5_K5_natDegree]
  have hQ5L_c5 : Q5L.coeff 5 = ιL_K5 (evalSQ_K5 (Q5_c 5)) := by
    simp only [Q5L, Q5_pol_K5, Polynomial.coeff_map, ← Polynomial.lcoeff_apply, map_sum]
    simp only [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul_X_pow, Fin.sum_univ_six]
    simp
  have hQ5L_c5_ne : Q5L.coeff 5 ≠ 0 := by
    rw [← hQ5L_deg]; exact Polynomial.leadingCoeff_ne_zero.mpr hQ5L_ne
  let f : RatFunc CoverL :=
    algebraMap CoverL[X] (RatFunc CoverL) (Polynomial.X ^ m.val) /
    algebraMap CoverL[X] (RatFunc CoverL) Q5L
  have hf_splits : f.denom.Splits := by
    have hdvd : f.denom ∣ Q5L := (RatFunc.denom_dvd hQ5L_ne).mpr ⟨Polynomial.X ^ m.val, rfl⟩
    have hsp : Q5L.Splits := by
      rw [hQ5L_eq]
      exact (Polynomial.Splits.C _).mul Q5_splits_CoverL
    exact hsp.of_dvd hQ5L_ne hdvd
  have houtside : ∀ a ∉ RQ5, CrossedRationalResidue.residue a f = 0 := by
    intro a ha
    have ha_ne : Q5L.eval a ≠ 0 := by
      rw [hQ5L_eq, Polynomial.eval_mul, Polynomial.eval_C]
      refine mul_ne_zero (map_ne_zero_iff _ ιL_K5.injective |>.mpr h2893401) ?_
      intro h0; exact ha (mem_RQ5_iff.mpr h0)
    have hreg : RegularAt a f := ⟨Polynomial.X ^ m.val, Q5L, ha_ne, rfl⟩
    exact hreg.residue_eq_zero
  have hsum_eq := CrossedRationalResidue.residue_sum_eq_infinity f hf_splits RQ5 houtside
  have hres_r : ∀ r ∈ RQ5, CrossedRationalResidue.residue r f = r ^ m.val / Q5L.derivative.eval r := by
    intro r hr
    have hr0 : Q5L.eval r = 0 := by
      rw [hQ5L_eq, Polynomial.eval_mul, Polynomial.eval_C, mem_RQ5_iff.mp hr, mul_zero]
    have hrd : Q5L.derivative.eval r ≠ 0 := by
      rw [hQ5L_eq, Polynomial.derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C]
      refine mul_ne_zero (map_ne_zero_iff _ ιL_K5.injective |>.mpr h2893401) ?_
      have hcop := eval_ne_zero_of_isCoprime isCoprime_Q5_Q5_deriv (mem_RQ5_iff.mp hr)
      rwa [← Polynomial.derivative_map] at hcop
    rw [simplePole_residue (Polynomial.X ^ m.val) Q5L r hr0 hrd]
    simp [Polynomial.eval_pow, Polynomial.eval_X]
  rw [Finset.sum_congr rfl hres_r] at hsum_eq
  rw [hsum_eq]
  -- Compute `infinityCoefficient f = residue 0 ((X^2)⁻¹ * reciprocal f)` via reversed polynomial `Q_rev`!
  let Q_rev : CoverL[X] := ∑ j : Fin 6, Polynomial.C (Q5L.coeff (5 - j.val)) * Polynomial.X ^ j.val
  have hQrev_0 : Q_rev.eval 0 = Q5L.coeff 5 := by
    simp [Q_rev, Fin.sum_univ_six]
  have hQrev_0_ne : Q_rev.eval 0 ≠ 0 := by rw [hQrev_0]; exact hQ5L_c5_ne
  have hrec_Q5L : reciprocal (algebraMap CoverL[X] (RatFunc CoverL) Q5L) =
      algebraMap CoverL[X] (RatFunc CoverL) Q_rev / RatFunc.X ^ 5 := by
    rw [reciprocal_polynomial]
    have hQ5L_as : Q5L = ∑ j : Fin 6, Polynomial.C (Q5L.coeff j.val) * Polynomial.X ^ j.val := by
      rw [Fin.sum_univ_eq_sum_range (fun j => Polynomial.C (Q5L.coeff j) * Polynomial.X ^ j)]
      exact Polynomial.as_sum_range_C_mul_X_pow' Q5L (by omega)
    conv_lhs => rw [hQ5L_as]
    simp only [map_sum, map_mul, map_pow, aeval_C, aeval_X,
      show ∀ c : CoverL, algebraMap CoverL (RatFunc CoverL) c = RatFunc.C c from fun _ => rfl,
      RatFunc.algebraMap_C, RatFunc.algebraMap_X, Q_rev]
    rw [Finset.sum_div, Fin.sum_univ_six, Fin.sum_univ_six]
    have hX := CrossedRationalResidue.X_ne_zero (K := CoverL)
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, show (3 : Fin 6).val = 3 from rfl,
      show (4 : Fin 6).val = 4 from rfl, show (5 : Fin 6).val = 5 from rfl,
      Nat.sub_zero, Nat.reduceSub, pow_zero, pow_one, inv_pow, mul_one]
    field_simp [hX]
    ring
  have hrec_Xm : reciprocal (algebraMap CoverL[X] (RatFunc CoverL) (Polynomial.X ^ m.val)) =
      (RatFunc.X ^ m.val)⁻¹ := by
    rw [map_pow, RatFunc.algebraMap_X, map_pow, reciprocal_X, inv_pow]
  have hQrev_ne : algebraMap CoverL[X] (RatFunc CoverL) Q_rev ≠ 0 :=
    polynomialMap_ne_zero (fun h0 => hQrev_0_ne (by simp [h0]))
  have hX := CrossedRationalResidue.X_ne_zero (K := CoverL)
  rw [infinityCoefficient_apply]
  simp only [f, map_div₀, hrec_Xm, hrec_Q5L]
  split_ifs with hm4
  · have hsimp : (RatFunc.X ^ 2)⁻¹ * ((RatFunc.X ^ m.val)⁻¹ /
        (algebraMap CoverL[X] (RatFunc CoverL) Q_rev / RatFunc.X ^ 5)) =
        (algebraMap CoverL[X] (RatFunc CoverL) (1 : CoverL[X]) /
          algebraMap CoverL[X] (RatFunc CoverL) Q_rev) / uniformizer (0 : CoverL) := by
      rw [hm4, uniformizer_zero, map_one]
      field_simp [hX, hQrev_ne]
    rw [hsimp, residue_div_uniformizer, valueAt_div_polynomials 0 1 Q_rev hQrev_0_ne,
      Polynomial.eval_one, hQrev_0, hQ5L_c5, one_div, map_inv₀]
  · have hm3 : m.val ≤ 3 := by omega
    have hsimp : (RatFunc.X ^ 2)⁻¹ * ((RatFunc.X ^ m.val)⁻¹ /
        (algebraMap CoverL[X] (RatFunc CoverL) Q_rev / RatFunc.X ^ 5)) =
        algebraMap CoverL[X] (RatFunc CoverL) (Polynomial.X ^ (3 - m.val)) /
        algebraMap CoverL[X] (RatFunc CoverL) Q_rev := by
      rw [map_pow, RatFunc.algebraMap_X]
      have hpow : (RatFunc.X : RatFunc CoverL) ^ (3 - m.val) * (RatFunc.X ^ 2 * RatFunc.X ^ m.val) = RatFunc.X ^ 5 := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      rw [← hpow]
      field_simp [hX, hQrev_ne]
    rw [hsimp]
    have hreg : RegularAt (0 : CoverL)
        (algebraMap CoverL[X] (RatFunc CoverL) (Polynomial.X ^ (3 - m.val)) /
          algebraMap CoverL[X] (RatFunc CoverL) Q_rev) := ⟨Polynomial.X ^ (3 - m.val), Q_rev, hQrev_0_ne, rfl⟩
    exact hreg.residue_eq_zero

private def seqRec5 {K : Type*} [Field K] (c : Fin 6 → K) (init : Fin 5 → K) : ℕ → K
  | 0 => init 0
  | 1 => init 1
  | 2 => init 2
  | 3 => init 3
  | 4 => init 4
  | n + 5 => -(∑ j : Fin 5, c j.castSucc * seqRec5 c init (n + j.val)) / c (Fin.last 5)
termination_by n => n

-- 15-line Bézout proof identifying every `RQ5` power sum `k = 0..12` with `W_K5_scaled k`!
private lemma sum_RQ5_power_eq_W_k (k : Fin 13) :
    ∑ r ∈ RQ5, r ^ k.val / ((k5Params.Q7_z.map ιL_K5).eval r * (k5Params.Q5_z.map ιL_K5).derivative.eval r) =
      ιL_K5 (W_K5_scaled k) := by
  have h2893401 : (2893401 : K5) ≠ 0 := by exact_mod_cast (by decide : (2893401 : ℕ) ≠ 0)
  have h1640 : (1640558367 : K5) ≠ 0 := by exact_mod_cast (by decide : (1640558367 : ℕ) ≠ 0)
  have h2 : (2 : K5) ≠ 0 := by exact_mod_cast (by decide : (2 : ℕ) ≠ 0)
  have hDint : (D_int_all : K5) ≠ 0 :=
    Int.cast_ne_zero.mpr (by unfold D_int_all; decide)
  have hlc5_ne : evalSQ_K5 (Q5_c 5) ≠ 0 := by
    rw [Q5_c5_eq_fac]
    have h112 : (lc5_const : K5) ≠ 0 := by
      unfold lc5_const; push_cast
      exact neg_ne_zero.mpr (by exact_mod_cast (by decide : (112 : ℕ) ≠ 0))
    have hfac : evalSQ_K5 lc5_fac_expr ≠ 0 := by
      simp only [lc5_fac_expr, evalSQ_K5, ringEval]
      exact mul_ne_zero (pow_ne_zero 4 fac_3_ne) fac_4_ne
    exact mul_ne_zero h112 hfac
  set Q5L : CoverL[X] := Q5_pol_K5.map ιL_K5
  set Q7L : CoverL[X] := Q7_pol_K5.map ιL_K5
  have hQ5L_eq : Q5L = Polynomial.C (ιL_K5 2893401) * k5Params.Q5_z.map ιL_K5 := by
    dsimp only [Q5L]
    rw [← Q5_K5_eq_scaled, Polynomial.map_mul, Polynomial.map_C]
  have hQ7L_eq : Polynomial.C (ιL_K5 2) * Q7L = Polynomial.C (ιL_K5 1640558367) * k5Params.Q7_z.map ιL_K5 := by
    dsimp only [Q7L]
    rw [← Polynomial.map_C, ← Polynomial.map_mul, ← Q7_K5_eq_scaled, Polynomial.map_mul, Polynomial.map_C]
  -- First prove for `Q5L`, `Q7L`: `T_pol k = ιL_K5 (W_K5 k)`!
  let T_pol (n : ℕ) : CoverL := ∑ r ∈ RQ5, r ^ n / (Q7L.eval r * Q5L.derivative.eval r)
  have hQ7_ne_r : ∀ r ∈ RQ5, Q7L.eval r ≠ 0 := by
    intro r hr
    have h7 := eval_ne_zero_of_isCoprime isCoprime_Q5_Q7 (mem_RQ5_iff.mp hr)
    intro h0
    have hev := congrArg (fun p : CoverL[X] => p.eval r) hQ7L_eq
    simp only [Polynomial.eval_mul, Polynomial.eval_C, h0, mul_zero] at hev
    exact mul_ne_zero (map_ne_zero_iff _ ιL_K5.injective |>.mpr h1640) h7 hev.symm
  have hdQ5_ne_r : ∀ r ∈ RQ5, Q5L.derivative.eval r ≠ 0 := by
    intro r hr
    rw [hQ5L_eq, Polynomial.derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C]
    refine mul_ne_zero (map_ne_zero_iff _ ιL_K5.injective |>.mpr h2893401) ?_
    have h := eval_ne_zero_of_isCoprime isCoprime_Q5_Q5_deriv (mem_RQ5_iff.mp hr)
    rwa [← Polynomial.derivative_map] at h
  have hT_rec5 : ∀ n : ℕ, ∑ j : Fin 6, ιL_K5 (evalSQ_K5 (Q5_c j)) * T_pol (n + j.val) = 0 := by
    intro n
    simp only [T_pol, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero; intro r hr
    have h1 : ∑ j : Fin 6, ιL_K5 (evalSQ_K5 (Q5_c j)) * (r ^ (n + j.val) / (Q7L.eval r * Q5L.derivative.eval r)) =
        (r ^ n * Q5L.eval r) / (Q7L.eval r * Q5L.derivative.eval r) := by
      have hev5 : Q5L.eval r = ∑ j : Fin 6, ιL_K5 (evalSQ_K5 (Q5_c j)) * r ^ j.val := by
        simp only [Q5L, Q5_pol_K5, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
          Polynomial.map_pow, Polynomial.map_X,
          show ∀ p : CoverL[X], p.eval r = Polynomial.evalRingHom r p from fun _ => rfl, map_sum]
        simp only [Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      rw [hev5, Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl; intro j _
      rw [pow_add]; ring
    rw [h1, hQ5L_eq, Polynomial.eval_mul, Polynomial.eval_C, mem_RQ5_iff.mp hr]
    simp
  have hT_dual7 : ∀ m : Fin 5,
      ∑ j : Fin 8, ιL_K5 (evalSQ_K5 (Q7_c j)) * T_pol (m.val + j.val) =
        if m.val = 4 then ιL_K5 (evalSQ_K5 (Q5_c 5))⁻¹ else 0 := by
    intro m
    rw [← sum_RQ5_euler_power m]
    simp only [T_pol, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro r hr
    have h1 : ∑ j : Fin 8, ιL_K5 (evalSQ_K5 (Q7_c j)) * (r ^ (m.val + j.val) / (Q7L.eval r * Q5L.derivative.eval r)) =
        (r ^ m.val * Q7L.eval r) / (Q7L.eval r * Q5L.derivative.eval r) := by
      have hev7 : Q7L.eval r = ∑ j : Fin 8, ιL_K5 (evalSQ_K5 (Q7_c j)) * r ^ j.val := by
        simp only [Q7L, Q7_pol_K5, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
          Polynomial.map_pow, Polynomial.map_X,
          show ∀ p : CoverL[X], p.eval r = Polynomial.evalRingHom r p from fun _ => rfl, map_sum]
        simp only [Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      rw [hev7, Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl; intro j _
      rw [pow_add]; ring
    rw [h1]
    have hq7 := hQ7_ne_r r hr
    rw [_root_.mul_comm (r ^ m.val) (Q7L.eval r), mul_div_mul_left _ _ hq7]
  -- Now compare `T_pol` with `W_K5` using `Q5_Q7_recurrences_K5`!
  obtain ⟨hW5, hW7_03, hW7_4⟩ := Q5_Q7_recurrences_K5
  have hW_rec5 (n : Fin 8) :
      ∑ j : Fin 6, ιL_K5 (evalSQ_K5 (Q5_c j)) * ιL_K5 (W_K5 ⟨n.val + j.val, by omega⟩) = 0 := by
    have h := congrArg ιL_K5 (hW5 n)
    simp only [map_sum, map_mul, map_zero] at h
    simp_rw [W_K5, map_div₀, ← mul_div_assoc]
    rw [← Finset.sum_div, h, zero_div]
  have hW_dual7 (m : Fin 5) :
      ∑ j : Fin 8, ιL_K5 (evalSQ_K5 (Q7_c j)) * ιL_K5 (W_K5 ⟨m.val + j.val, by omega⟩) =
        if m.val = 4 then ιL_K5 (evalSQ_K5 (Q5_c 5))⁻¹ else 0 := by
    split_ifs with hm4
    · have h4 : m = 4 := Fin.ext hm4
      clear hm4; subst h4
      have hden_ne : (D_int_all : K5) * evalSQ_K5 D_all_expr ≠ 0 := mul_ne_zero hDint D_all_K5_ne
      have hK : ∑ j : Fin 8, evalSQ_K5 (Q7_c j) * W_K5 ⟨(4 : Fin 5).val + j.val, by omega⟩ = (evalSQ_K5 (Q5_c 5))⁻¹ := by
        simp only [show (4 : Fin 5).val = 4 from rfl]
        simp_rw [W_K5, ← mul_div_assoc]
        rw [← Finset.sum_div, div_eq_iff hden_ne]
        apply mul_left_cancel₀ hlc5_ne
        rw [← mul_assoc, mul_inv_cancel₀ hlc5_ne, one_mul, Q5_c5_eq_fac, D_all_eq_lc5_mul]
        have hW7_4' := hW7_4
        generalize ∑ j : Fin 8, evalSQ_K5 (Q7_c j) * evalSQ_K5 (W_num_expr ⟨4 + j.val, by omega⟩) = S7 at hW7_4' ⊢
        generalize evalSQ_K5 lc5_fac_expr = flc
        generalize evalSQ_K5 D_all_div_lc5_expr = fdl at hW7_4' ⊢
        generalize (D_int_all : K5) = dA at hW7_4' ⊢
        generalize (lc5_const : K5) = c5 at hW7_4' ⊢
        linear_combination flc * hW7_4'
      have hL := congrArg ιL_K5 hK
      simpa only [map_sum, map_mul, map_inv₀] using hL
    · have hm4' : m.val < 4 := by omega
      have h := congrArg ιL_K5 (hW7_03 ⟨m.val, hm4'⟩)
      simp only [map_sum, map_mul, map_zero] at h
      simp_rw [W_K5, map_div₀, ← mul_div_assoc]
      rw [← Finset.sum_div, h, zero_div]
  -- Define `Δ_ext : ℕ → CoverL` extending `T_pol n - ιL_K5 (W_K5 n)` recursively via `Q5`!
  let Δ_ext : ℕ → CoverL :=
    seqRec5 (fun j => ιL_K5 (evalSQ_K5 (Q5_c j))) (fun j => T_pol j.val - ιL_K5 (W_K5 ⟨j.val, by omega⟩))
  have hΔ_rec (n : ℕ) : ∑ j : Fin 6, ιL_K5 (evalSQ_K5 (Q5_c j)) * Δ_ext (n + j.val) = 0 := by
    have hlcL : ιL_K5 (evalSQ_K5 (Q5_c (Fin.last 5))) ≠ 0 := (map_ne_zero_iff _ ιL_K5.injective).mpr hlc5_ne
    have h5 : Δ_ext (n + 5) =
        -(∑ j : Fin 5, ιL_K5 (evalSQ_K5 (Q5_c j.castSucc)) * Δ_ext (n + j.val)) /
          ιL_K5 (evalSQ_K5 (Q5_c (Fin.last 5))) := by
      dsimp only [Δ_ext]; rw [seqRec5]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last, h5, mul_div_cancel₀ _ hlcL]
    ring
  have hΔ_eq (n : Fin 13) : Δ_ext n.val = T_pol n.val - ιL_K5 (W_K5 n) := by
    obtain ⟨m, hm⟩ := n
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      by_cases hlt : m < 5
      · interval_cases m <;> (dsimp only [Δ_ext]; rw [seqRec5]; rfl)
      · have hlcL : ιL_K5 (evalSQ_K5 (Q5_c (Fin.last 5))) ≠ 0 := (map_ne_zero_iff _ ιL_K5.injective).mpr hlc5_ne
        have hm5 : m - 5 < 8 := by omega
        have hr1 := hΔ_rec (m - 5)
        have hr2 := hT_rec5 (m - 5)
        have hr3 := hW_rec5 ⟨m - 5, hm5⟩
        rw [Fin.sum_univ_castSucc] at hr1 hr2 hr3
        simp only [Fin.coe_castSucc, Fin.val_last, show m - 5 + 5 = m by omega] at hr1 hr2 hr3
        have hsum_eq : ∑ j : Fin 5, ιL_K5 (evalSQ_K5 (Q5_c j.castSucc)) * Δ_ext (m - 5 + j.val) =
            ∑ j : Fin 5, ιL_K5 (evalSQ_K5 (Q5_c j.castSucc)) *
              (T_pol (m - 5 + j.val) - ιL_K5 (W_K5 ⟨m - 5 + j.val, by omega⟩)) := by
          apply Finset.sum_congr rfl; intro j _
          rw [ih (m - 5 + j.val) (by omega) (by omega)]
        apply mul_left_cancel₀ hlcL
        have hdiff : ∑ j : Fin 5, ιL_K5 (evalSQ_K5 (Q5_c j.castSucc)) *
              (T_pol (m - 5 + j.val) - ιL_K5 (W_K5 ⟨m - 5 + j.val, by omega⟩)) =
            (∑ j : Fin 5, ιL_K5 (evalSQ_K5 (Q5_c j.castSucc)) * T_pol (m - 5 + j.val)) -
            (∑ j : Fin 5, ιL_K5 (evalSQ_K5 (Q5_c j.castSucc)) * ιL_K5 (W_K5 ⟨m - 5 + j.val, by omega⟩)) := by
          rw [← Finset.sum_sub_distrib]; congr 1; ext j; ring
        rw [hsum_eq, hdiff] at hr1
        linear_combination hr1 - hr2 + hr3
  -- Linear functional `Λ(P) = ∑ P.coeff n * Δ_ext n`: vanishes on `Q5L * A` and `Q7L * B`!
  let Λ : CoverL[X] → CoverL := fun P => P.sum (fun n c => c * Δ_ext n)
  have hΛ_add (P Q : CoverL[X]) : Λ (P + Q) = Λ P + Λ Q :=
    Polynomial.sum_add_index _ _ _ (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)
  have hΛ_C_mul_X (c : CoverL) (n : ℕ) : Λ (Polynomial.C c * Polynomial.X ^ n) = c * Δ_ext n := by
    rw [Polynomial.C_mul_X_pow_eq_monomial]
    exact Polynomial.sum_monomial_index _ _ (zero_mul _)
  have hΛ_Q5 (A : CoverL[X]) : Λ (Q5L * A) = 0 := by
    induction A using Polynomial.induction_on' with
    | add p q hp hq => rw [mul_add, hΛ_add, hp, hq, add_zero]
    | monomial n c =>
      have h1 : Q5L * Polynomial.monomial n c =
          ∑ j : Fin 6, Polynomial.C (c * ιL_K5 (evalSQ_K5 (Q5_c j))) * Polynomial.X ^ (n + j.val) := by
        rw [← Polynomial.C_mul_X_pow_eq_monomial]
        simp only [Q5L, Q5_pol_K5, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
          Polynomial.map_pow, Polynomial.map_X, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro j _
        rw [pow_add, map_mul]; ring
      rw [h1]
      have hΛ_sum : ∀ (s : Finset (Fin 6)) (f : Fin 6 → CoverL[X]), Λ (∑ j ∈ s, f j) = ∑ j ∈ s, Λ (f j) := by
        intro s f; classical induction s using Finset.induction_on with
        | empty => simp [Λ]
        | insert a s ha ih => rw [Finset.sum_insert ha, hΛ_add, ih, Finset.sum_insert ha]
      rw [hΛ_sum]
      simp_rw [hΛ_C_mul_X, mul_assoc, ← Finset.mul_sum, hΔ_rec, mul_zero]
  have hΛ_Q7_mon (m : Fin 5) (c : CoverL) : Λ (Q7L * Polynomial.monomial m.val c) = 0 := by
    have h1 : Q7L * Polynomial.monomial m.val c =
        ∑ j : Fin 8, Polynomial.C (c * ιL_K5 (evalSQ_K5 (Q7_c j))) * Polynomial.X ^ (m.val + j.val) := by
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp only [Q7L, Q7_pol_K5, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_pow, Polynomial.map_X, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro j _
      rw [pow_add, map_mul]; ring
    rw [h1]
    have hΛ_sum : ∀ (s : Finset (Fin 8)) (f : Fin 8 → CoverL[X]), Λ (∑ j ∈ s, f j) = ∑ j ∈ s, Λ (f j) := by
      intro s f; classical induction s using Finset.induction_on with
      | empty => simp [Λ]
      | insert a s ha ih => rw [Finset.sum_insert ha, hΛ_add, ih, Finset.sum_insert ha]
    rw [hΛ_sum]
    simp_rw [hΛ_C_mul_X, mul_assoc, ← Finset.mul_sum]
    have hsum0 : ∑ j : Fin 8, ιL_K5 (evalSQ_K5 (Q7_c j)) * Δ_ext (m.val + j.val) = 0 := by
      have heq : ∀ j : Fin 8, Δ_ext (m.val + j.val) = T_pol (m.val + j.val) - ιL_K5 (W_K5 ⟨m.val + j.val, by omega⟩) :=
        fun j => hΔ_eq ⟨m.val + j.val, by omega⟩
      simp_rw [heq, mul_sub, Finset.sum_sub_distrib, hT_dual7 m, hW_dual7 m, sub_self]
    rw [hsum0, mul_zero]
  have hΛ_Q7 (B : CoverL[X]) : Λ (Q7L * B) = 0 := by
    have hQ5L_ne : Q5L ≠ 0 := by
      rw [hQ5L_eq]
      exact mul_ne_zero (Polynomial.C_ne_zero.mpr ((map_ne_zero_iff _ ιL_K5.injective).mpr h2893401))
        (Polynomial.map_ne_zero Q5_K5_ne_zero)
    have hQ5L_deg : Q5L.natDegree = 5 := by
      rw [hQ5L_eq, Polynomial.natDegree_C_mul ((map_ne_zero_iff _ ιL_K5.injective).mpr h2893401),
        Polynomial.natDegree_map_eq_of_injective ιL_K5.injective, Q5_K5_natDegree]
    have hdiv := Polynomial.modByMonic_add_div B (p := Polynomial.C (Q5L.leadingCoeff⁻¹) * Q5L)
    set Q5M := Polynomial.C (Q5L.leadingCoeff⁻¹) * Q5L
    have hM_monic : Q5M.Monic := by
      rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
        inv_mul_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr hQ5L_ne)]
    have hM_deg : Q5M.natDegree = 5 := by
      rw [Polynomial.natDegree_C_mul (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hQ5L_ne)), hQ5L_deg]
    set rem := B %ₘ Q5M
    set quo := B /ₘ Q5M
    have hB_eq : B = rem + Q5L * (Polynomial.C (Q5L.leadingCoeff⁻¹) * quo) := by
      have h := Polynomial.modByMonic_add_div B Q5M
      rw [← h]; dsimp only [rem, quo, Q5M]; ring
    rw [hB_eq, mul_add, hΛ_add, show Q7L * (Q5L * (Polynomial.C Q5L.leadingCoeff⁻¹ * quo)) =
        Q5L * (Q7L * (Polynomial.C Q5L.leadingCoeff⁻¹ * quo)) by ring, hΛ_Q5, add_zero]
    have hrem_deg : rem.natDegree < 5 := by
      by_cases hr0 : rem = 0
      · simp [hr0]
      · have hlt := Polynomial.degree_modByMonic_lt B hM_monic
        rw [Polynomial.degree_eq_natDegree hr0, Polynomial.degree_eq_natDegree hM_monic.ne_zero, hM_deg] at hlt
        exact WithBot.coe_lt_coe.mp hlt
    have hrem_sum : rem = ∑ m : Fin 5, Polynomial.monomial m.val (rem.coeff m.val) := by
      rw [Fin.sum_univ_eq_sum_range (fun m => Polynomial.monomial m (rem.coeff m))]
      exact Polynomial.as_sum_range' rem 5 hrem_deg
    rw [hrem_sum, Finset.mul_sum]
    have hΛ_sum5 : ∀ (s : Finset (Fin 5)) (f : Fin 5 → CoverL[X]), Λ (∑ m ∈ s, f m) = ∑ m ∈ s, Λ (f m) := by
      intro s f; classical induction s using Finset.induction_on with
      | empty => simp [Λ]
      | insert a s ha ih => rw [Finset.sum_insert ha, hΛ_add, ih, Finset.sum_insert ha]
    rw [hΛ_sum5]
    exact Finset.sum_eq_zero fun m _ => hΛ_Q7_mon m _
  -- Bézout combination from `CoverAlgebra.isCoprime_Q5_Q7`!
  obtain ⟨u, v, huv⟩ := isCoprime_Q5_Q7
  have hbez : (u.map ιL_K5 * Polynomial.C (ιL_K5 2893401)⁻¹) * Q5L +
      (v.map ιL_K5 * Polynomial.C (ιL_K5 1640558367)⁻¹ * Polynomial.C (ιL_K5 2)) * Q7L = 1 := by
    have huvL := congrArg (Polynomial.map ιL_K5) huv
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one] at huvL
    have h5i : Polynomial.C (ιL_K5 2893401)⁻¹ * Q5L = k5Params.Q5_z.map ιL_K5 := by
      rw [hQ5L_eq, ← mul_assoc, ← Polynomial.C_mul,
        inv_mul_cancel₀ ((map_ne_zero_iff _ ιL_K5.injective).mpr h2893401), Polynomial.C_1, one_mul]
    have h7i : Polynomial.C (ιL_K5 1640558367)⁻¹ * Polynomial.C (ιL_K5 2) * Q7L = k5Params.Q7_z.map ιL_K5 := by
      rw [mul_assoc, hQ7L_eq, ← mul_assoc, ← Polynomial.C_mul,
        inv_mul_cancel₀ ((map_ne_zero_iff _ ιL_K5.injective).mpr h1640), Polynomial.C_1, one_mul]
    linear_combination huvL + u.map ιL_K5 * h5i + v.map ιL_K5 * h7i
  have hΔ_zero : Δ_ext k.val = 0 := by
    have h1 : Polynomial.C (1 : CoverL) * Polynomial.X ^ k.val =
        Q5L * (Polynomial.X ^ k.val * (u.map ιL_K5 * Polynomial.C (ιL_K5 2893401)⁻¹)) +
        Q7L * (Polynomial.X ^ k.val * (v.map ιL_K5 * Polynomial.C (ιL_K5 1640558367)⁻¹ * Polynomial.C (ιL_K5 2))) := by
      rw [Polynomial.C_1, one_mul]
      linear_combination -Polynomial.X ^ k.val * hbez
    have hΛ1 := congrArg Λ h1
    rw [hΛ_C_mul_X, one_mul, hΛ_add, hΛ_Q5, hΛ_Q7, add_zero] at hΛ1
    exact hΛ1
  have hTk_eq : T_pol k.val = ιL_K5 (W_K5 k) := sub_eq_zero.mp (hΔ_eq k ▸ hΔ_zero)
  -- Rescale from `(Q5L, Q7L)` back to `(k5Params.Q5_z, k5Params.Q7_z)`!
  have hscale : ∑ r ∈ RQ5, r ^ k.val / ((k5Params.Q7_z.map ιL_K5).eval r * (k5Params.Q5_z.map ιL_K5).derivative.eval r) =
      ιL_K5 (((sc5_den * sc7_den : ℤ) : K5) / ((sc5_num * sc7_num : ℤ) : K5)) * T_pol k.val := by
    simp only [T_pol, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro r hr
    have hQ5d : Q5L.derivative.eval r = ιL_K5 2893401 * (k5Params.Q5_z.map ιL_K5).derivative.eval r := by
      rw [hQ5L_eq, Polynomial.derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C]
    have hQ7e : ιL_K5 2 * Q7L.eval r = ιL_K5 1640558367 * (k5Params.Q7_z.map ιL_K5).eval r := by
      have h := congrArg (fun p : CoverL[X] => p.eval r) hQ7L_eq
      simpa only [Polynomial.eval_mul, Polynomial.eval_C] using h
    have hq5d_ne : (k5Params.Q5_z.map ιL_K5).derivative.eval r ≠ 0 := by
      have h := hdQ5_ne_r r hr; rw [hQ5d] at h; exact right_ne_zero_of_mul h
    have hq7e_ne : (k5Params.Q7_z.map ιL_K5).eval r ≠ 0 :=
      eval_ne_zero_of_isCoprime isCoprime_Q5_Q7 (mem_RQ5_iff.mp hr)
    have hq7L_ne := hQ7_ne_r r hr
    have h2L : (ιL_K5 2 : CoverL) ≠ 0 := (map_ne_zero_iff _ ιL_K5.injective).mpr h2
    have h5L : (ιL_K5 2893401 : CoverL) ≠ 0 := (map_ne_zero_iff _ ιL_K5.injective).mpr h2893401
    have h7L : (ιL_K5 1640558367 : CoverL) ≠ 0 := (map_ne_zero_iff _ ιL_K5.injective).mpr h1640
    have hsc : ιL_K5 (((sc5_den * sc7_den : ℤ) : K5) / ((sc5_num * sc7_num : ℤ) : K5)) =
        ιL_K5 2893401 * ιL_K5 1640558367 / ιL_K5 2 := by
      simp only [sc5_num, sc5_den, sc7_num, sc7_den, map_div₀, map_mul, map_ofNat, map_one,
        Int.cast_mul, Int.cast_ofNat, Int.cast_one, one_mul]
    rw [hsc, hQ5d]
    have hq7_div : Q7L.eval r = ιL_K5 1640558367 * (k5Params.Q7_z.map ιL_K5).eval r / ιL_K5 2 := by
      rw [eq_div_iff h2L, _root_.mul_comm, hQ7e]
    rw [hq7_div]
    field_simp [hq5d_ne, hq7e_ne, h2L, h5L, h7L]
  rw [hscale, hTk_eq, ← map_mul, W_K5_scaled]

/-! ### Section 2: 12-Variable `Q23` Split and Regularity of `eta_AC_reg` on `RQ5` -/

private def Q23_of {R : Type*} [CommRing R] (q2 q1 q0 e3 e2 e1 e0 p4 p3 p2 p1 p0 : R) : R :=
  - q0 ^ 2 * e2 ^ 2 * p4
  + q0 ^ 2 * e3 * e1 * p4
  + q0 ^ 2 * e3 * e2 * p3
  - q0 ^ 2 * e3 ^ 2 * p2
  + q1 * q0 * e2 * e1 * p4
  - q1 * q0 * e3 * e0 * p4
  - q1 * q0 * e3 * e1 * p3
  + q1 * q0 * e3 ^ 2 * p1
  - q1 ^ 2 * e2 * e0 * p4
  + q1 ^ 2 * e3 * e0 * p3
  - q1 ^ 2 * e3 ^ 2 * p0
  - q2 * q0 * e1 ^ 2 * p4
  + 2 * q2 * q0 * e2 * e0 * p4
  - q2 * q0 * e3 * e0 * p3
  + q2 * q0 * e3 * e1 * p2
  - q2 * q0 * e3 * e2 * p1
  + q2 * q0 * e3 ^ 2 * p0
  + q2 * q1 * e1 * e0 * p4
  - q2 * q1 * e3 * e0 * p2
  + q2 * q1 * e3 * e2 * p0
  - q2 ^ 2 * e0 ^ 2 * p4
  + q2 ^ 2 * e3 * e0 * p1
  - q2 ^ 2 * e3 * e1 * p0

private lemma Q5_rem_split {R : Type*} [CommRing R] (q2 q1 q0 e3 e2 e1 e0 p4 p3 p2 p1 p0 : R) :
    e3 * (remDeg4_P1 q2 q1 q0 p4 p3 p2 p1 * remDeg3_d0 q2 q1 q0 e3 e2 e0 -
          remDeg4_P0 q2 q1 q0 p4 p3 p2 p0 * remDeg3_d1 q2 q1 q0 e3 e2 e1) =
    q2 ^ 2 * p4 * syl5 q2 q1 q0 e3 e2 e1 e0 +
    q2 ^ 3 * Q23_of q2 q1 q0 e3 e2 e1 e0 p4 p3 p2 p1 p0 := by
  simp only [remDeg4_P1, remDeg4_P0, remDeg3_d1, remDeg3_d0, syl5, Q23_of]
  ring

private def p4_AC : A_C := (interp4 P18_z_AC).1

private def Q23_AC : A_C :=
  let p := interp4 P18_z_AC
  Q23_of (pairC k5Params.d2_2) (pairC k5Params.d2_1) (pairC k5Params.d2_0)
    (pairC k5Params.d3_3) (pairC k5Params.d3_2) (pairC k5Params.d3_1) (pairC k5Params.d3_0)
    p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2

private def eta_AC_main : A_C :=
  -(p4_AC * U_C ^ 3 * W_C * polyC k5Params.cb_h ^ 4) /
    (81 * ιC_K5 k5Params.Av0 * (2 * W_C + polyC k5Params.bW) *
      polyC k5Params.Q7_z * polyC k5Params.Q5_z)

private def eta_AC_reg : A_C :=
  -(Q23_AC * U_C ^ 3 * W_C * polyC k5Params.cb_h ^ 4) /
    (81 * ιC_K5 k5Params.Av0 * (2 * W_C + polyC k5Params.bW) *
      polyC k5Params.Q7_z * pairC k5Params.res_z)

private lemma Q7_K5_ne_zero : k5Params.Q7_z ≠ 0 := by
  intro h0
  obtain ⟨u, v, huv⟩ := isCoprime_Q5_Q7
  rw [h0, mul_zero, add_zero] at huv
  have hdeg := congrArg Polynomial.natDegree huv
  rw [Polynomial.natDegree_one] at hdeg
  have hu : u ≠ 0 := fun hu0 => by simp [hu0] at huv
  rw [Polynomial.natDegree_mul hu Q5_K5_ne_zero, Q5_K5_natDegree] at hdeg
  omega

private lemma eta_AC_eq_main_add_reg : eta_AC = eta_AC_main + eta_AC_reg := by
  have hQ5_ne : polyC k5Params.Q5_z ≠ 0 := polyC_ne_zero Q5_K5_ne_zero
  have hQ7_ne : polyC k5Params.Q7_z ≠ 0 := polyC_ne_zero Q7_K5_ne_zero
  have hres_ne : pairC k5Params.res_z ≠ 0 := pairC_ne_zero_of_pnm nm_z_K5_ne_zero
  have h81_ne : (81 : A_C) ≠ 0 := by exact_mod_cast (by decide : (81 : ℕ) ≠ 0)
  have hAv0_ne : ιC_K5 k5Params.Av0 ≠ 0 := (map_ne_zero_iff _ ιC_K5.injective).mpr Av0_K5_ne_zero
  have h2W_ne : 2 * W_C + polyC k5Params.bW ≠ 0 := by
    intro h0
    have hsq : (2 * W_C + polyC k5Params.bW) ^ 2 = polyC k5Params.disc_E0 := by
      simp only [polyC, CoverParams.disc_E0, map_sub, map_pow, map_mul, map_ofNat]
      linear_combination 4 * W_C_relation
    rw [h0, zero_pow (by omega)] at hsq
    have hd_ne : k5Params.disc_E0 ≠ 0 := by
      intro hd0
      obtain ⟨u, v, huv⟩ := isCoprime_Q5_disc_E0
      rw [hd0, mul_zero, add_zero] at huv
      have hu : u ≠ 0 := fun hu0 => by simp [hu0] at huv
      have hdeg := congrArg Polynomial.natDegree huv
      rw [Polynomial.natDegree_one, Polynomial.natDegree_mul hu Q5_K5_ne_zero, Q5_K5_natDegree] at hdeg
      omega
    exact polyC_ne_zero hd_ne hsq.symm
  have hd22 : pairC k5Params.d2_2 = polyC k5Params.Q5_z := by
    simp [pairC, polyC, CoverParams.d2_2, PairAlg.map_ofScalar, evalAC_ofScalar]
  have hd33 : pairC k5Params.d3_3 = polyC k5Params.Q7_z := by
    simp [pairC, polyC, CoverParams.d3_3, PairAlg.map_ofScalar, evalAC_ofScalar]
  have hd1 : pairC k5Params.d1_z =
      remDeg3_d1 (pairC k5Params.d2_2) (pairC k5Params.d2_1) (pairC k5Params.d2_0)
        (pairC k5Params.d3_3) (pairC k5Params.d3_2) (pairC k5Params.d3_1) := by
    simp only [CoverParams.d1_z, CoverParams.pmul, remDeg3_d1, pairC,
      PairAlg.map_sub, PairAlg.map_mul, evalAC_sub, evalAC_mul]
  have hd0 : pairC k5Params.d0_z =
      remDeg3_d0 (pairC k5Params.d2_2) (pairC k5Params.d2_1) (pairC k5Params.d2_0)
        (pairC k5Params.d3_3) (pairC k5Params.d3_2) (pairC k5Params.d3_0) := by
    simp only [CoverParams.d0_z, CoverParams.pmul, remDeg3_d0, pairC,
      PairAlg.map_sub, PairAlg.map_mul, evalAC_sub, evalAC_mul]
  have hres : pairC k5Params.res_z =
      syl5 (pairC k5Params.d2_2) (pairC k5Params.d2_1) (pairC k5Params.d2_0)
        (pairC k5Params.d3_3) (pairC k5Params.d3_2) (pairC k5Params.d3_1) (pairC k5Params.d3_0) := by
    simp only [CoverParams.res_z, syl5Pair, syl5, pairC, PairAlg.map_add, PairAlg.map_sub,
      PairAlg.map_mul, PairAlg.map_smul, evalAC_add, evalAC_sub, evalAC_mul, evalAC_smul,
      map_ofNat]
    ring
  have hsplit := Q5_rem_split (pairC k5Params.d2_2) (pairC k5Params.d2_1) (pairC k5Params.d2_0)
    (pairC k5Params.d3_3) (pairC k5Params.d3_2) (pairC k5Params.d3_1) (pairC k5Params.d3_0)
    (interp4 P18_z_AC).1 (interp4 P18_z_AC).2.1 (interp4 P18_z_AC).2.2.1
    (interp4 P18_z_AC).2.2.2.1 (interp4 P18_z_AC).2.2.2.2
  rw [← hd1, ← hd0, ← hres, hd22, hd33] at hsplit
  simp only [eta_AC, eta_AC_num, eta_AC_main, eta_AC_reg, p4_AC, Q23_AC, hd22, hd33]
  have hcore :
      -(remDeg4_P1 (polyC k5Params.Q5_z) (pairC k5Params.d2_1) (pairC k5Params.d2_0)
          (interp4 P18_z_AC).1 (interp4 P18_z_AC).2.1 (interp4 P18_z_AC).2.2.1 (interp4 P18_z_AC).2.2.2.1 * pairC k5Params.d0_z -
        remDeg4_P0 (polyC k5Params.Q5_z) (pairC k5Params.d2_1) (pairC k5Params.d2_0)
          (interp4 P18_z_AC).1 (interp4 P18_z_AC).2.1 (interp4 P18_z_AC).2.2.1 (interp4 P18_z_AC).2.2.2.2 * pairC k5Params.d1_z) /
        (polyC k5Params.Q5_z ^ 3 * pairC k5Params.res_z) =
      -(interp4 P18_z_AC).1 / (polyC k5Params.Q7_z * polyC k5Params.Q5_z) +
      -Q23_of (polyC k5Params.Q5_z) (pairC k5Params.d2_1) (pairC k5Params.d2_0)
        (polyC k5Params.Q7_z) (pairC k5Params.d3_2) (pairC k5Params.d3_1) (pairC k5Params.d3_0)
        (interp4 P18_z_AC).1 (interp4 P18_z_AC).2.1 (interp4 P18_z_AC).2.2.1
        (interp4 P18_z_AC).2.2.2.1 (interp4 P18_z_AC).2.2.2.2 /
        (polyC k5Params.Q7_z * pairC k5Params.res_z) := by
    field_simp [hQ5_ne, hQ7_ne, hres_ne]
    linear_combination -hsplit
  have hfac := congrArg (fun t => t * (U_C ^ 3 * W_C * polyC k5Params.cb_h ^ 4 /
      (81 * ιC_K5 k5Params.Av0 * (2 * W_C + polyC k5Params.bW)))) hcore
  have hC_ne : 81 * ιC_K5 k5Params.Av0 * (2 * W_C + polyC k5Params.bW) ≠ 0 :=
    mul_ne_zero (mul_ne_zero h81_ne hAv0_ne) h2W_ne
  calc _ = _ * (U_C ^ 3 * W_C * polyC k5Params.cb_h ^ 4 /
        (81 * ιC_K5 k5Params.Av0 * (2 * W_C + polyC k5Params.bW))) := by
          field_simp [hC_ne, hQ5_ne, hres_ne]
    _ = _ := hfac
    _ = _ := by field_simp [hC_ne, hQ5_ne, hQ7_ne, hres_ne]

private lemma mapRatFunc_toRat (P : K5[X]) :
    mapRatFunc ιL_K5 (toRat P) = algebraMap CoverL[X] (RatFunc CoverL) (P.map ιL_K5) :=
  mapRatFunc_algebraMap ιL_K5 P

-- Regularity of `trace_AC eta_AC_reg` at every `r ∈ RQ5`!
private structure RegQ5 (r : CoverL) (x : A_C) : Prop where
  c0 : RegularAt r (mapRatFunc ιL_K5 (coordsAC x).c0)
  c1 : RegularAt r (mapRatFunc ιL_K5 (coordsAC x).c1)

private lemma regQ5_evalAC {r : CoverL} {p : PairAlg (RatFunc K5)}
    (h0 : RegularAt r (mapRatFunc ιL_K5 p.c0)) (h1 : RegularAt r (mapRatFunc ιL_K5 p.c1)) :
    RegQ5 r (evalAC p) :=
  ⟨by rwa [coordsAC_evalAC], by rwa [coordsAC_evalAC]⟩

private lemma regQ5_zero (r : CoverL) : RegQ5 r 0 := by
  rw [show (0 : A_C) = evalAC ⟨0, 0⟩ by simp [evalAC]]
  exact regQ5_evalAC (by simp [regAt_zero]) (by simp [regAt_zero])

private lemma regQ5_one (r : CoverL) : RegQ5 r 1 := by
  rw [show (1 : A_C) = evalAC ⟨1, 0⟩ by simp [evalAC]]
  exact regQ5_evalAC (by simp [regAt_one]) (by simp [regAt_zero])

private lemma regQ5_ofNat (r : CoverL) (n : ℕ) [n.AtLeastTwo] : RegQ5 r (no_index (OfNat.ofNat n)) := by
  have h1 : (OfNat.ofNat n : A_C) = evalAC ⟨(n : RatFunc K5), 0⟩ := by
    simp [evalAC, show (OfNat.ofNat n : A_C) = (n : A_C) from rfl]
  rw [h1]
  exact regQ5_evalAC (by rw [map_natCast]; exact ⟨Polynomial.C (n : CoverL), 1, by simp, by simp⟩) (by simp [regAt_zero])

private lemma regQ5_ιC_K5 (r : CoverL) (c : K5) : RegQ5 r (ιC_K5 c) := by
  rw [show ιC_K5 c = evalAC ⟨RatFunc.C c, 0⟩ by simp [evalAC, ιC_K5]]
  exact regQ5_evalAC (by simp [mapRatFunc_C, regAt_C]) (by simp [regAt_zero])

private lemma regQ5_polyC (r : CoverL) (P : K5[X]) : RegQ5 r (polyC P) := by
  rw [show polyC P = evalAC ⟨toRat P, 0⟩ by simp [evalAC, polyC]]
  exact regQ5_evalAC (by rw [mapRatFunc_toRat]; exact ⟨P.map ιL_K5, 1, by simp, by simp⟩) (by simp [regAt_zero])

private lemma regQ5_pairC (r : CoverL) (p : PairAlg K5[X]) : RegQ5 r (pairC p) := by
  rw [pairC]
  exact regQ5_evalAC
    (by simp only [PairAlg.map, mapRatFunc_toRat]; exact ⟨p.c0.map ιL_K5, 1, by simp, by simp⟩)
    (by simp only [PairAlg.map, mapRatFunc_toRat]; exact ⟨p.c1.map ιL_K5, 1, by simp, by simp⟩)

private lemma regQ5_U_C (r : CoverL) : RegQ5 r U_C := by
  simpa [polyC, U_C, toRat] using regQ5_polyC r Polynomial.X

private lemma regQ5_W_C (r : CoverL) : RegQ5 r W_C := by
  rw [← evalAC_W]
  exact regQ5_evalAC (by simp [PairAlg.W, regAt_zero]) (by simp [PairAlg.W, regAt_one])

private lemma regQ5_add {r : CoverL} {x y : A_C} (hx : RegQ5 r x) (hy : RegQ5 r y) : RegQ5 r (x + y) := by
  rw [← evalAC_coordsAC x, ← evalAC_coordsAC y, ← evalAC_add]
  exact regQ5_evalAC
    (by simp only [PairAlg.add, map_add]; exact hx.1.add hy.1)
    (by simp only [PairAlg.add, map_add]; exact hx.2.add hy.2)

private lemma regQ5_neg {r : CoverL} {x : A_C} (hx : RegQ5 r x) : RegQ5 r (-x) := by
  rw [← evalAC_coordsAC x, ← evalAC_neg]
  exact regQ5_evalAC (by simp only [PairAlg.neg, map_neg]; exact regAt_neg_local hx.1)
    (by simp only [PairAlg.neg, map_neg]; exact regAt_neg_local hx.2)

private lemma regQ5_sub {r : CoverL} {x y : A_C} (hx : RegQ5 r x) (hy : RegQ5 r y) : RegQ5 r (x - y) := by
  rw [sub_eq_add_neg]; exact regQ5_add hx (regQ5_neg hy)

private lemma regQ5_mul {r : CoverL} {x y : A_C} (hx : RegQ5 r x) (hy : RegQ5 r y) : RegQ5 r (x * y) := by
  rw [← evalAC_coordsAC x, ← evalAC_coordsAC y, ← evalAC_mul]
  have hb : RegularAt r (mapRatFunc ιL_K5 (toRat k5Params.bW)) := by
    rw [mapRatFunc_toRat]; exact ⟨k5Params.bW.map ιL_K5, 1, by simp, by simp⟩
  have hc : RegularAt r (mapRatFunc ιL_K5 (toRat k5Params.cW)) := by
    rw [mapRatFunc_toRat]; exact ⟨k5Params.cW.map ιL_K5, 1, by simp, by simp⟩
  exact regQ5_evalAC
    (by simp only [PairAlg.mul, map_sub, map_mul]; exact regAt_sub_local (regAt_mul_local hx.1 hy.1) (regAt_mul_local (regAt_mul_local hx.2 hy.2) hc))
    (by simp only [PairAlg.mul, map_add, map_sub, map_mul]; exact regAt_sub_local (regAt_add_local (regAt_mul_local hx.1 hy.2) (regAt_mul_local hx.2 hy.1)) (regAt_mul_local (regAt_mul_local hx.2 hy.2) hb))
where
  regAt_add_local {f g : RatFunc CoverL} (hf : RegularAt r f) (hg : RegularAt r g) : RegularAt r (f + g) := hf.add hg

private lemma regQ5_pow {r : CoverL} {x : A_C} (hx : RegQ5 r x) (n : ℕ) : RegQ5 r (x ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact regQ5_one r
  | succ k ih => rw [pow_succ]; exact regQ5_mul ih hx

private lemma regQ5_div_polyC {r : CoverL} {x : A_C} {P : K5[X]} (hx : RegQ5 r x)
    (hP : (P.map ιL_K5).eval r ≠ 0) : RegQ5 r (x / polyC P) := by
  have h1 : x / polyC P = evalAC (PairAlg.smul (toRat P)⁻¹ (coordsAC x)) := by
    rw [evalAC_smul, evalAC_coordsAC, map_inv₀, div_eq_inv_mul]; rfl
  rw [h1]
  have hinv : RegularAt r (mapRatFunc ιL_K5 (toRat P)⁻¹) := by
    rw [map_inv₀, mapRatFunc_toRat]
    exact ⟨1, P.map ιL_K5, hP, by simp⟩
  exact regQ5_evalAC
    (by simp only [PairAlg.smul, map_mul]; exact regAt_mul_local hinv hx.1)
    (by simp only [PairAlg.smul, map_mul]; exact regAt_mul_local hinv hx.2)

private lemma regQ5_div_pairC {r : CoverL} {x : A_C} {y : PairAlg K5[X]} (hx : RegQ5 r x)
    (hnm : ((k5Params.pnm y).map ιL_K5).eval r ≠ 0) : RegQ5 r (x / pairC y) := by
  have hy_conj : pairC y * pairC (PairAlg.conj k5Params.bW y) = polyC (k5Params.pnm y) := by
    simp only [pairC, polyC, ← evalAC_mul, ← evalAC_ofScalar]
    congr 1; ext <;> (simp only [PairAlg.mul, PairAlg.conj, PairAlg.ofScalar, PairAlg.map,
      CoverParams.pnm, PairAlg.nm, map_add, map_sub, map_neg, map_mul, map_pow]; ring)
  have hnm_ne : k5Params.pnm y ≠ 0 := fun h0 => hnm (by simp [h0])
  have hconj_ne : pairC (PairAlg.conj k5Params.bW y) ≠ 0 := fun h0 =>
    polyC_ne_zero hnm_ne (by rw [← hy_conj, h0, mul_zero])
  have heq : x / pairC y = (x * pairC (PairAlg.conj k5Params.bW y)) / polyC (k5Params.pnm y) := by
    rw [← hy_conj, mul_div_mul_right _ _ hconj_ne]
  rw [heq]
  exact regQ5_div_polyC (regQ5_mul hx (regQ5_pairC r _)) hnm

private lemma regQ5_div_nat {r : CoverL} {x : A_C} (hx : RegQ5 r x) (n : ℕ) [hn : n.AtLeastTwo] :
    RegQ5 r (x / no_index (OfNat.ofNat n)) := by
  have heq : (OfNat.ofNat n : A_C) = polyC (Polynomial.C (n : K5)) := by
    simp [polyC, toRat, show (OfNat.ofNat n : A_C) = (n : A_C) from rfl]
  rw [heq]
  apply regQ5_div_polyC hx
  simp only [Polynomial.map_C, Polynomial.eval_C, Polynomial.map_natCast, Polynomial.eval_natCast, map_natCast]
  exact (Nat.cast_ne_zero (R := CoverL)).mpr (NeZero.ne n)

private lemma regularAt_trace_eta_AC_reg (r : CoverL) (hr : r ∈ RQ5) :
    RegularAt r (mapRatFunc ιL_K5 (Algebra.trace (RatFunc K5) A_C eta_AC_reg)) := by
  have hQ5_0 := mem_RQ5_iff.mp hr
  have hr0 : r ≠ 0 := fun h0 => zero_notMem_RQ5 (h0 ▸ hr)
  have hr1 : r ≠ 1 := by
    have h := eval_ne_zero_of_isCoprime isCoprime_Q5_X_sub_1 hQ5_0
    simpa [sub_eq_zero] using h
  have hcb_ne : (k5Params.cb_h.map ιL_K5).eval r ≠ 0 := eval_ne_zero_of_isCoprime isCoprime_Q5_cb_h hQ5_0
  have hQ7_ne : (k5Params.Q7_z.map ιL_K5).eval r ≠ 0 := eval_ne_zero_of_isCoprime isCoprime_Q5_Q7 hQ5_0
  have hnmWU_ne : (k5Params.nm_WU.map ιL_K5).eval r ≠ 0 := eval_ne_zero_of_isCoprime isCoprime_Q5_nm_WU hQ5_0
  have hP34_ne : (P34_K5.map ιL_K5).eval r ≠ 0 := fun h => Finset.disjoint_left.mp disjoint_R34_RQ5 (mem_R34_iff.mpr h) hr
  have hnm_z_ne : (k5Params.nm_z.map ιL_K5).eval r ≠ 0 := by
    rw [nm_z_K5_factor]
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    have hcbm_ne : (cb_h_m_K5.map ιL_K5).eval r ≠ 0 := by
      have h := congrArg (fun p : K5[X] => (p.map ιL_K5).eval r) cb_h_K5_eq_mul_monic
      simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul, Polynomial.eval_C] at h
      rw [h] at hcb_ne; exact right_ne_zero_of_mul hcb_ne
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero
      ((map_ne_zero_iff _ ιL_K5.injective).mpr lc34_K5_ne_zero)
      (pow_ne_zero 15 hr0)) (pow_ne_zero 12 hcbm_ne)) hP34_ne
  have hcW_ne : (k5Params.cW.map ιL_K5).eval r ≠ 0 := cW_eval_ne_zero hr0
  -- Show `W_C`, `V_C`, `u_of U_C`, `v_of V_C` are invertible in `RegQ5 r`!
  have hU_reg : RegQ5 r U_C := regQ5_U_C r
  have hW_reg : RegQ5 r W_C := regQ5_W_C r
  have hV_reg : RegQ5 r V_C := by
    rw [V_C, show U_C = polyC Polynomial.X by simp [U_C, polyC, toRat]]
    exact regQ5_div_polyC hW_reg (by simpa using hr0)
  have hdiv_W {x : A_C} (hx : RegQ5 r x) : RegQ5 r (x / W_C) := by
    rw [show W_C = pairC PairAlg.W by rw [← evalAC_W, pairC]; congr 1; ext <;> simp [PairAlg.W, PairAlg.map]]
    exact regQ5_div_pairC hx (by simpa [CoverParams.pnm, PairAlg.nm, PairAlg.W] using hcW_ne)
  have hdiv_U {x : A_C} (hx : RegQ5 r x) : RegQ5 r (x / U_C) := by
    rw [show U_C = polyC Polynomial.X by simp [U_C, polyC, toRat]]
    exact regQ5_div_polyC hx (by simpa using hr0)
  have hdiv_V {x : A_C} (hx : RegQ5 r x) : RegQ5 r (x / V_C) := by
    rw [V_C, div_div_eq_mul_div]; exact hdiv_W (regQ5_mul hx hU_reg)
  have hdiv_u {x : A_C} (hx : RegQ5 r x) : RegQ5 r (x / u_of U_C) := by
    have hu : u_of U_C = polyC (Polynomial.X - 1) / 9 := by
      simp [u_of, U_C, polyC, toRat]
    rw [hu, div_div_eq_mul_div]
    exact regQ5_div_polyC (regQ5_mul hx (regQ5_ofNat r 9)) (by simpa [sub_eq_zero] using hr1)
  have hdiv_v {x : A_C} (hx : RegQ5 r x) : RegQ5 r (x / v_of V_C) := by
    have hv : v_of V_C = pairC (PairAlg.sub PairAlg.W (PairAlg.ofScalar Polynomial.X)) / (9 * U_C) := by
      simp only [v_of, V_C, pairC, PairAlg.map_sub, PairAlg.map_W, PairAlg.map_ofScalar,
        evalAC_sub, evalAC_W, evalAC_ofScalar, U_C, toRat, RatFunc.algebraMap_X]
      have hU := U_C_ne_zero; rw [U_C] at hU; field_simp [hU]
    rw [hv, div_div_eq_mul_div]
    exact regQ5_div_pairC (regQ5_mul hx (regQ5_mul (regQ5_ofNat r 9) hU_reg)) (by
      have hpair : PairAlg.sub PairAlg.W (PairAlg.ofScalar (Polynomial.X : K5[X])) = ⟨-Polynomial.X, 1⟩ := by
        ext <;> simp [PairAlg.sub, PairAlg.W, PairAlg.ofScalar]
      rw [hpair]; exact hnmWU_ne)
  -- Prove `RegQ5 r (P18_z_AC z)` for any `z` with `RegQ5 r z`!
  have hP18_gen (a b : A_C) (ha : RegQ5 r a) (hb : RegQ5 r b) :
      RegQ5 r (P18_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) a b U_C V_C) := by
    have hS := regQ5_ιC_K5 r S_K; have hQ := regQ5_ιC_K5 r Q_K; have hT := regQ5_ιC_K5 r T_K
    have hx := regQ5_ιC_K5 r x_K; have hy := regQ5_ιC_K5 r y_K
    have hξS := regQ5_sub hS (regQ5_mul ha hT)
    have hξQ := regQ5_sub hQ (regQ5_mul hb hT)
    have hdHS (s q : A_C) (hs : RegQ5 r s) (hq : RegQ5 r q) : RegQ5 r (dH_dS s q U_C V_C) := by
      dsimp only [dH_dS]
      repeat' (with_reducible first | apply regQ5_div_nat | apply regQ5_add | apply regQ5_sub | apply regQ5_neg | apply regQ5_mul | apply regQ5_pow | exact hs | exact hq | exact hU_reg | exact hV_reg | exact regQ5_zero r | exact regQ5_one r | exact regQ5_ofNat r _)
    have hdHQ (s q v0 : A_C) (hs : RegQ5 r s) (hq : RegQ5 r q) (hv0 : RegQ5 r v0) : RegQ5 r (dH_dQ s q v0 U_C V_C) := by
      dsimp only [dH_dQ]
      repeat' (with_reducible first | apply regQ5_div_nat | apply regQ5_add | apply regQ5_sub | apply regQ5_neg | apply regQ5_mul | apply regQ5_pow | exact hs | exact hq | exact hv0 | exact hU_reg | exact hV_reg | exact regQ5_zero r | exact regQ5_one r | exact regQ5_ofNat r _)
    have hnumM (mi : Fin 10) : RegQ5 r (numM mi a b (ιC_K5 S_K - a * ιC_K5 T_K) (ιC_K5 Q_K - b * ιC_K5 T_K) U_C V_C) := by
      have ha2 : RegQ5 r (q1_a2 a b U_C V_C) := hdHS _ _ ha hb
      have ha0 : RegQ5 r (q1_a0 _ _ U_C V_C) := hdHS _ _ hξS hξQ
      have ha1 : RegQ5 r (q1_a1 _ _ _ _ U_C V_C) := regQ5_sub (regQ5_sub (hdHS _ _ (regQ5_add ha hξS) (regQ5_add hb hξQ)) ha2) ha0
      have hb2 : RegQ5 r (q2_b2 a b U_C V_C) := hdHQ _ _ 0 ha hb (regQ5_zero r)
      have hb0 : RegQ5 r (q2_b0 _ _ U_C V_C) := hdHQ _ _ 1 hξS hξQ (regQ5_one r)
      have hb1 : RegQ5 r (q2_b1 _ _ _ _ U_C V_C) :=
        regQ5_add (regQ5_sub (regQ5_sub (hdHQ _ _ 0 (regQ5_add ha hξS) (regQ5_add hb hξQ) (regQ5_zero r)) hb2)
          (hdHQ _ _ 0 hξS hξQ (regQ5_zero r)))
          (regQ5_mul (regQ5_mul (regQ5_mul (regQ5_div_nat (regQ5_ofNat r 10) 7) hb) hU_reg) hV_reg)
      have hd20 := regQ5_sub (regQ5_mul ha2 hb0) (regQ5_mul ha0 hb2)
      have hd21 := regQ5_sub (regQ5_mul ha2 hb1) (regQ5_mul ha1 hb2)
      have hd10 := regQ5_sub (regQ5_mul ha1 hb0) (regQ5_mul ha0 hb1)
      fin_cases mi <;> dsimp only [numM, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
        repeat' (with_reducible first | exact hd10 | exact hd20 | exact hd21 | exact hξS | exact hξQ | apply regQ5_div_nat | apply regQ5_add | apply regQ5_sub | apply regQ5_neg | apply regQ5_mul | apply regQ5_pow | exact ha | exact hb | exact ha2 | exact ha1 | exact ha0 | exact hb2 | exact hb1 | exact hb0 | exact hS | exact hQ | exact hT | exact regQ5_zero r | exact regQ5_one r | exact regQ5_ofNat r _)
    have hM0 : RegQ5 r (A_0U a b (ιC_K5 S_K - a * ιC_K5 T_K) (ιC_K5 Q_K - b * ιC_K5 T_K) U_C V_C / U_C +
        A_0V a b (ιC_K5 S_K - a * ιC_K5 T_K) (ιC_K5 Q_K - b * ιC_K5 T_K) U_C V_C / V_C) := by
      refine regQ5_add (hdiv_U ?_) (hdiv_V ?_)
      · dsimp only [A_0U]
        repeat' (with_reducible first | apply regQ5_div_nat | apply regQ5_add | apply regQ5_sub | apply regQ5_neg | apply regQ5_mul | exact hnumM _ | exact regQ5_ofNat r _)
      · dsimp only [A_0V]
        repeat' (with_reducible first | apply regQ5_div_nat | apply regQ5_add | apply regQ5_sub | apply regQ5_neg | apply regQ5_mul | exact hnumM _ | exact regQ5_ofNat r _)
    have hAY : RegQ5 r (A_Y a b (ιC_K5 S_K - a * ιC_K5 T_K) (ιC_K5 Q_K - b * ιC_K5 T_K) U_C V_C) := by
      dsimp only [A_Y]
      repeat' (with_reducible first | apply regQ5_div_nat | apply regQ5_add | apply regQ5_sub | apply regQ5_neg | apply regQ5_mul | exact hU_reg | exact hV_reg | exact hnumM _ | exact regQ5_ofNat r _)
    have hAX : RegQ5 r (A_X a b (ιC_K5 S_K - a * ιC_K5 T_K) (ιC_K5 Q_K - b * ιC_K5 T_K) U_C V_C) := by
      dsimp only [A_X]
      repeat' (with_reducible first | apply regQ5_div_nat | apply regQ5_add | apply regQ5_sub | apply regQ5_neg | apply regQ5_mul | exact hU_reg | exact hnumM _ | exact regQ5_ofNat r _)
    have hu_r : RegQ5 r (u_of U_C) := regQ5_div_nat (regQ5_sub hU_reg (regQ5_one r)) 9
    have hv_r : RegQ5 r (v_of V_C) := regQ5_div_nat (regQ5_sub hV_reg (regQ5_one r)) 9
    have hH0 : RegQ5 r (H0_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K)) := by
      dsimp only [H0_of]
      repeat' (with_reducible first | apply regQ5_div_nat | apply regQ5_add | apply regQ5_sub | apply regQ5_neg | apply regQ5_mul | apply regQ5_pow | exact hS | exact hQ | exact hT | exact regQ5_ofNat r _)
    have hdH0 (k : Fin 3) : RegQ5 r (dH0_fn k (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K)) := by
      fin_cases k <;> dsimp only [dH0_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
        repeat' (with_reducible first | apply regQ5_div_nat | apply regQ5_add | apply regQ5_sub | apply regQ5_neg | apply regQ5_mul | apply regQ5_pow | exact hS | exact hQ | exact hT | exact regQ5_ofNat r _)
    have hdF5 (k : Fin 5) : RegQ5 r (dF5_fn k (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K)) := by
      fin_cases k <;> dsimp only [dF5_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
        repeat' (with_reducible first | apply regQ5_add | apply regQ5_mul | apply regQ5_pow | exact hS | exact hT | exact hx | exact hy | exact hdH0 _ | exact regQ5_ofNat r _)
    have hu3 : RegQ5 r (u3_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 x_K)) := by
      dsimp only [u3_of]; exact regQ5_add (regQ5_sub hx hS) (regQ5_mul (regQ5_ofNat r 2) hQ)
    have hv3 : RegQ5 r (v3_of (ιC_K5 T_K) (ιC_K5 y_K)) := by
      dsimp only [v3_of]; exact regQ5_add (regQ5_sub hy hT) (regQ5_ofNat r 2)
    have hDX2 : RegQ5 r (DX2_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 x_K)) := by
      dsimp only [DX2_of]
      repeat' (with_reducible first | apply regQ5_add | apply regQ5_sub | apply regQ5_mul | apply regQ5_pow | exact hS | exact hQ | exact hu3 | exact regQ5_ofNat r _)
    have hDY2 : RegQ5 r (DY2_of (ιC_K5 T_K) (ιC_K5 y_K)) := by
      dsimp only [DY2_of]
      repeat' (with_reducible first | apply regQ5_add | apply regQ5_sub | apply regQ5_mul | apply regQ5_pow | exact hT | exact hv3 | exact regQ5_ofNat r _)
    have hdDX2 (k : Fin 5) : RegQ5 r (dDX2_fn k (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 x_K)) := by
      fin_cases k <;> dsimp only [dDX2_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
        repeat' (with_reducible first | apply regQ5_add | apply regQ5_sub | apply regQ5_neg | apply regQ5_mul | apply regQ5_pow | exact hS | exact hQ | exact hu3 | exact regQ5_zero r | exact regQ5_ofNat r _)
    have hdDY2 (k : Fin 5) : RegQ5 r (dDY2_fn k (ιC_K5 T_K) (ιC_K5 y_K)) := by
      fin_cases k <;> dsimp only [dDY2_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
        repeat' (with_reducible first | apply regQ5_add | apply regQ5_sub | apply regQ5_neg | apply regQ5_mul | apply regQ5_pow | exact hT | exact hv3 | exact regQ5_zero r | exact regQ5_one r | exact regQ5_ofNat r _)
    have hLX : RegQ5 r (LX_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 x_K) U_C) := by
      dsimp only [LX_of]
      repeat' (with_reducible first | apply regQ5_div_nat | apply regQ5_add | apply regQ5_sub | apply regQ5_mul | exact hu_r | exact hS | exact hQ | exact hu3 | exact hU_reg | exact regQ5_ofNat r _)
    have hLY : RegQ5 r (LY_of (ιC_K5 T_K) (ιC_K5 y_K) V_C) := by
      dsimp only [LY_of]
      repeat' (with_reducible first | apply regQ5_div_nat | apply regQ5_add | apply regQ5_sub | apply regQ5_mul | exact hv_r | exact hT | exact hv3 | exact hV_reg | exact regQ5_ofNat r _)
    have hdLX (k : Fin 5) : RegQ5 r (dLX_fn k U_C) := by
      fin_cases k <;> dsimp only [dLX_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
        repeat' (with_reducible first | apply regQ5_div_nat | apply regQ5_add | apply regQ5_sub | apply regQ5_neg | apply regQ5_mul | exact hu_r | exact hU_reg | exact regQ5_zero r | exact regQ5_ofNat r _)
    have hdLY (k : Fin 5) : RegQ5 r (dLY_fn k V_C) := by
      fin_cases k <;> dsimp only [dLY_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
        repeat' (with_reducible first | apply regQ5_div_nat | apply regQ5_add | apply regQ5_sub | apply regQ5_neg | apply regQ5_mul | exact hv_r | exact hV_reg | exact regQ5_zero r | exact regQ5_ofNat r _)
    have hbr (k : Fin 5) : RegQ5 r (br_fn k (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) U_C V_C) := by
      dsimp only [br_fn]
      refine regQ5_add ?_ (regQ5_mul (regQ5_mul (regQ5_mul (regQ5_ofNat r 2) hS) hT)
        (regQ5_sub (regQ5_mul hLX (hdLY k)) (regQ5_mul hLY (hdLX k))))
      fin_cases k
      · exact regQ5_mul (regQ5_mul (regQ5_neg hT) hLX) hLY
      · exact regQ5_zero r
      · exact regQ5_mul (regQ5_mul hS hLX) hLY
      · exact regQ5_zero r
      · exact regQ5_zero r
    have hom (i j : Fin 5) : RegQ5 r (om_fn i j (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) U_C V_C) := by
      dsimp only [om_fn]
      have homX (k : Fin 5) : RegQ5 r (match k with
          | 0 => -25 * ιC_K5 S_K * U_C + 15 * ιC_K5 Q_K * U_C + 9 * ιC_K5 x_K * U_C + 25 * ιC_K5 S_K - 15 * ιC_K5 Q_K
          | 1 => 30 * (U_C - 1) * ιC_K5 S_K
          | 3 => 18 * U_C * ιC_K5 S_K
          | _ => 0) := by
        split <;> repeat' (with_reducible first | apply regQ5_add | apply regQ5_sub | apply regQ5_neg | apply regQ5_mul | exact hS | exact hQ | exact hx | exact hU_reg | exact regQ5_zero r | exact regQ5_one r | exact regQ5_ofNat r _)
      have homY (k : Fin 5) : RegQ5 r (match k with
          | 2 => -25 * ιC_K5 T_K * V_C + 9 * ιC_K5 y_K * V_C + 25 * ιC_K5 T_K + 15 * V_C - 15
          | 4 => 18 * V_C * ιC_K5 T_K
          | _ => 0) := by
        split <;> repeat' (with_reducible first | apply regQ5_add | apply regQ5_sub | apply regQ5_neg | apply regQ5_mul | exact hT | exact hy | exact hV_reg | exact regQ5_zero r | exact regQ5_ofNat r _)
      exact regQ5_mul (regQ5_div_nat (regQ5_one r) 81)
        (regQ5_sub (regQ5_mul (homX i) (homY j)) (regQ5_mul (homX j) (homY i)))
    have hFc (f2 : Fin 5 → Fin 5 → A_C) (hf2 : ∀ p q, RegQ5 r (f2 p q)) (i : Fin 3) :
        RegQ5 r (F_contract (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) f2 i) := by
      fin_cases i <;> dsimp only [F_contract, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
        exact regQ5_add (regQ5_add (regQ5_mul (hdF5 4) (hf2 _ 3)) (regQ5_mul (hdF5 3) (hf2 4 _)))
          (regQ5_mul (hdF5 _) (hf2 3 4))
    have hdot (v : Fin 3 → A_C) (hv : ∀ i, RegQ5 r (v i)) : RegQ5 r (dot_ab v a b) :=
      regQ5_add (regQ5_add (regQ5_mul (hv 0) ha) (regQ5_mul (hv 1) hb)) (hv 2)
    have hqY : RegQ5 r (dot_ab (QY_num (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) U_C V_C) a b / v_of V_C) :=
      hdiv_v (hdot _ fun i => regQ5_mul hDY2 (regQ5_sub
        (regQ5_mul hDX2 (hFc _ (fun p q => regQ5_mul (regQ5_mul hS hT) (hom p q)) i))
        (hFc _ (fun p q => regQ5_mul (regQ5_mul hS hT)
          (regQ5_sub (regQ5_mul (hdDX2 p) (hbr q)) (regQ5_mul (hdDX2 q) (hbr p)))) i)))
    have hqX : RegQ5 r (dot_ab (QX_num (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) U_C V_C) a b / u_of U_C) :=
      hdiv_u (hdot _ fun i => regQ5_mul hDX2 (regQ5_add
        (regQ5_mul (regQ5_neg hDY2) (hFc _ (fun p q => regQ5_mul (regQ5_mul hS hT) (hom p q)) i))
        (hFc _ (fun p q => regQ5_mul (regQ5_mul hS hT)
          (regQ5_sub (regQ5_mul (hdDY2 p) (hbr q)) (regQ5_mul (hdDY2 q) (hbr p)))) i)))
    have hA1 : RegQ5 r (A1_of (ιC_K5 S_K) (ιC_K5 Q_K) U_C V_C) := by
      dsimp only [A1_of]
      repeat' (with_reducible first | apply regQ5_div_nat | apply regQ5_sub | apply regQ5_mul | apply regQ5_pow | exact hS | exact hQ | exact hU_reg | exact hV_reg | exact regQ5_one r | exact regQ5_ofNat r _)
    have hB1 : RegQ5 r (B1_of (ιC_K5 T_K) U_C V_C) := by
      dsimp only [B1_of]
      repeat' (with_reducible first | apply regQ5_div_nat | apply regQ5_sub | apply regQ5_mul | apply regQ5_pow | exact hT | exact hU_reg | exact hV_reg | exact regQ5_one r | exact regQ5_ofNat r _)
    have hdA1 (k : Fin 3) : RegQ5 r (dA1_fn k (ιC_K5 S_K) (ιC_K5 Q_K) U_C V_C) := by
      fin_cases k <;> dsimp only [dA1_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
        repeat' (with_reducible first | apply regQ5_div_nat | apply regQ5_add | apply regQ5_sub | apply regQ5_neg | apply regQ5_mul | apply regQ5_pow | exact hS | exact hQ | exact hU_reg | exact hV_reg | exact regQ5_zero r | exact regQ5_one r | exact regQ5_ofNat r _)
    have hcA1 : RegQ5 r (cA1_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) a b U_C V_C) := by
      dsimp only [cA1_of]
      repeat' (with_reducible first | apply regQ5_add | apply regQ5_sub | apply regQ5_mul | exact hH0 | exact hA1 | exact ha | exact hb | exact hdA1 _ | exact hdH0 _)
    have hEB : RegQ5 r (EB_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) U_C V_C) := by
      dsimp only [EB_of, W2_of]
      repeat' (with_reducible first | apply regQ5_sub | apply regQ5_mul | exact hS | exact hT | exact hDX2 | exact hDY2 | exact hdF5 _ | exact hbr _ | exact regQ5_ofNat r _)
    dsimp only [P18_of]
    exact regQ5_add
      (regQ5_mul hM0 (regQ5_add (regQ5_add (regQ5_mul (regQ5_mul hH0 hA1) hqY) (regQ5_mul (regQ5_mul hH0 hB1) hqX))
        (regQ5_mul (hdiv_v hcA1) hEB)))
      (regQ5_mul (regQ5_add (regQ5_mul hAY hqY) (regQ5_mul hAX hqX)) (regQ5_pow hH0 2))
  have hP18_reg (z : A_C) (hz : RegQ5 r z) : RegQ5 r (P18_z_AC z) := by
    have ha : RegQ5 r (z / W_C) := hdiv_W hz
    have hb : RegQ5 r (-(polyC k5Params.ca_h * z + pairC k5Params.c0W) / (W_C * polyC k5Params.cb_h)) := by
      rw [← div_div]
      exact regQ5_div_polyC (hdiv_W (regQ5_neg (regQ5_add (regQ5_mul (regQ5_polyC r _) hz) (regQ5_pairC r _)))) hcb_ne
    exact hP18_gen _ _ ha hb
  -- All 5 interpolated coefficients of `P18_z_AC` are `RegQ5 r`!
  have hp0 := hP18_reg 0 (regQ5_zero r)
  have hp1 := hP18_reg 1 (regQ5_one r)
  have hpm1 := hP18_reg (-1) (regQ5_neg (regQ5_one r))
  have hp2 := hP18_reg 2 (regQ5_ofNat r 2)
  have hpm2 := hP18_reg (-2) (regQ5_neg (regQ5_ofNat r 2))
  have hq4 : RegQ5 r (interp4 P18_z_AC).1 := by
    dsimp only [interp4]
    exact regQ5_div_nat (regQ5_add (regQ5_add (regQ5_mul (regQ5_neg (regQ5_ofNat r 4)) (regQ5_add hp1 hpm1))
      (regQ5_add hp2 hpm2)) (regQ5_mul (regQ5_ofNat r 6) hp0)) 24
  have hq3 : RegQ5 r (interp4 P18_z_AC).2.1 := by
    dsimp only [interp4]
    exact regQ5_div_nat (regQ5_add (regQ5_mul (regQ5_neg (regQ5_ofNat r 2)) (regQ5_sub hp1 hpm1))
      (regQ5_sub hp2 hpm2)) 12
  have hq2 : RegQ5 r (interp4 P18_z_AC).2.2.1 := by
    dsimp only [interp4]
    exact regQ5_div_nat (regQ5_sub (regQ5_sub (regQ5_mul (regQ5_ofNat r 16) (regQ5_add hp1 hpm1))
      (regQ5_add hp2 hpm2)) (regQ5_mul (regQ5_ofNat r 30) hp0)) 24
  have hq1 : RegQ5 r (interp4 P18_z_AC).2.2.2.1 := by
    dsimp only [interp4]
    exact regQ5_div_nat (regQ5_sub (regQ5_mul (regQ5_ofNat r 8) (regQ5_sub hp1 hpm1))
      (regQ5_sub hp2 hpm2)) 12
  have hq0 : RegQ5 r (interp4 P18_z_AC).2.2.2.2 := hp0
  have hQ23 : RegQ5 r Q23_AC := by
    dsimp only [Q23_AC, Q23_of]
    repeat' (with_reducible first | apply regQ5_add | apply regQ5_sub | apply regQ5_neg | apply regQ5_mul | apply regQ5_pow | exact regQ5_pairC r _ | exact hq4 | exact hq3 | exact hq2 | exact hq1 | exact hq0 | exact regQ5_ofNat r _)
  have hnum : RegQ5 r (-(Q23_AC * U_C ^ 3 * W_C * polyC k5Params.cb_h ^ 4) /
      (81 * ιC_K5 k5Params.Av0 * polyC k5Params.Q7_z * pairC k5Params.res_z)) := by
    have htop := regQ5_neg (regQ5_mul (regQ5_mul (regQ5_mul hQ23 (regQ5_pow hU_reg 3)) hW_reg) (regQ5_pow (regQ5_polyC r k5Params.cb_h) 4))
    have h81Av0 : 81 * ιC_K5 k5Params.Av0 = polyC (Polynomial.C (81 * k5Params.Av0)) := by
      simp [polyC, ιC_K5, toRat, RatFunc.algebraMap_C, map_ofNat]
    rw [h81Av0, ← div_div, ← div_div]
    apply regQ5_div_pairC _ hnm_z_ne
    apply regQ5_div_polyC _ hQ7_ne
    apply regQ5_div_polyC htop
    rw [Polynomial.map_C, Polynomial.eval_C, map_mul, map_ofNat]
    have h81 : (81 : CoverL) ≠ 0 := by
      have h : ((81 : ℕ) : CoverL) ≠ 0 := (Nat.cast_ne_zero (R := CoverL)).mpr (by decide)
      rwa [Nat.cast_ofNat] at h
    exact mul_ne_zero h81 ((map_ne_zero_iff _ ιL_K5.injective).mpr Av0_K5_ne_zero)
  -- Apply `trace_AC_euler` with `y = PairAlg.one`!
  set x_reg := -(Q23_AC * U_C ^ 3 * W_C * polyC k5Params.cb_h ^ 4) /
    (81 * ιC_K5 k5Params.Av0 * polyC k5Params.Q7_z * pairC k5Params.res_z)
  have heta_eq : eta_AC_reg = evalAC (coordsAC x_reg) /
      (evalAC (PairAlg.ofScalar (1 : RatFunc K5)) * (2 * W_C + ιC_rat (toRat k5Params.bW))) := by
    rw [evalAC_coordsAC, evalAC_ofScalar, map_one, one_mul]
    have hmul : ∀ a b c d e : A_C, a / (b * c * d * e) = (a / (b * d * e)) / c := fun a b c d e => by
      rw [div_div]; congr 1; ring
    exact hmul (-(Q23_AC * U_C ^ 3 * W_C * polyC k5Params.cb_h ^ 4))
      (81 * ιC_K5 k5Params.Av0) (2 * W_C + polyC k5Params.bW)
      (polyC k5Params.Q7_z) (pairC k5Params.res_z)
  rw [heta_eq, trace_AC_euler (coordsAC x_reg) (PairAlg.ofScalar 1) (by simp [PairAlg.nm, PairAlg.ofScalar])]
  simp only [PairAlg.nm, PairAlg.ofScalar, one_pow, zero_pow (by omega : 2 ≠ 0),
    zero_mul, mul_zero, add_zero, sub_zero, mul_one, div_one]
  exact hnum.2

private lemma residue_eta_L_eq_main (r : CoverL) (hr : r ∈ RQ5) :
    CrossedRationalResidue.residue r eta_L =
      CrossedRationalResidue.residue r (mapRatFunc ιL_K5 (Algebra.trace (RatFunc K5) A_C eta_AC_main)) := by
  simp only [CoverResidue.eta_L, CoverResidue.eta, eta_AC_eq_main_add_reg, map_add]
  rw [(regularAt_trace_eta_AC_reg r hr).residue_eq_zero, add_zero]


/-! ### Section 3: Generic `UPoly` / `BivL` / `UBivL` Algebra, Shift-Invariant `p4_AC`, and Trace Reduction -/

private abbrev UPoly (α : Type*) := List α
private abbrev BivL (α : Type*) := List (List α)
private abbrev UBivL (α : Type*) := List (BivL α)

private def uAdd {α : Type*} (o : PolyOps α) : UPoly α → UPoly α → UPoly α
  | [], b => b
  | a, [] => a
  | a :: as, b :: bs => o.add a b :: uAdd o as bs

private def uNeg {α : Type*} (o : PolyOps α) (a : UPoly α) : UPoly α :=
  a.map o.neg

private def uSub {α : Type*} (o : PolyOps α) : UPoly α → UPoly α → UPoly α
  | [], b => uNeg o b
  | a, [] => a
  | a :: as, b :: bs => o.sub a b :: uSub o as bs

private def uSc {α : Type*} (o : PolyOps α) (c : α) (a : UPoly α) : UPoly α :=
  a.map (o.mul c)

private def uShift {α : Type*} (o : PolyOps α) (a : UPoly α) : UPoly α :=
  o.zero :: a

private def uTail {α : Type*} : UPoly α → UPoly α
  | [] => []
  | _ :: tl => tl

private def uMul {α : Type*} (o : PolyOps α) : UPoly α → UPoly α → UPoly α
  | [], _ => []
  | a :: as, b => uAdd o (uSc o a b) (uShift o (uMul o as b))

private def uMonomial {α : Type*} (o : PolyOps α) : ℕ → α → UPoly α
  | 0, c => [c]
  | k + 1, c => o.zero :: uMonomial o k c

private def uEval {α : Type*} (o : PolyOps α) : UPoly α → α → α
  | [], _ => o.zero
  | a :: as, t => o.add a (o.mul t (uEval o as t))

private def bivAdd {α : Type*} (o : PolyOps α) : BivL α → BivL α → BivL α
  | [], b => b
  | a, [] => a
  | r1 :: rs1, r2 :: rs2 => uAdd o r1 r2 :: bivAdd o rs1 rs2

private def bivNeg {α : Type*} (o : PolyOps α) (b : BivL α) : BivL α :=
  b.map (uNeg o)

private def bivSub {α : Type*} (o : PolyOps α) : BivL α → BivL α → BivL α
  | [], b => bivNeg o b
  | a, [] => a
  | r1 :: rs1, r2 :: rs2 => uSub o r1 r2 :: bivSub o rs1 rs2

private def bivSc {α : Type*} (o : PolyOps α) (c : α) (b : BivL α) : BivL α :=
  b.map (uSc o c)

private def bivConst {α : Type*} (c : α) : BivL α := [[c]]

private def bivMul {α : Type*} (o : PolyOps α) : BivL α → BivL α → BivL α
  | [], _ => []
  | r :: rs, b => bivAdd o (b.map (uMul o r)) ([] :: bivMul o rs b)

private def bivRedOnce {α : Type*} (o : PolyOps α) (s21 t21 nh0 : α) : BivL α → BivL α
  | [] => []
  | [r0] => [uSc o s21 r0]
  | [r0, r1] => [uSc o s21 r0, uSc o s21 r1]
  | r0 :: r1 :: rest =>
      bivAdd o [uSc o s21 r0, uSc o s21 r1]
        (rest.map fun ri => uAdd o (uSc o nh0 ri) (uShift o (uShift o (uSc o t21 ri))))

private def ubAdd {α : Type*} (o : PolyOps α) : UBivL α → UBivL α → UBivL α
  | [], b => b
  | a, [] => a
  | b1 :: bs1, b2 :: bs2 => bivAdd o b1 b2 :: ubAdd o bs1 bs2

private def ubNeg {α : Type*} (o : PolyOps α) (a : UBivL α) : UBivL α :=
  a.map (bivNeg o)

private def ubSub {α : Type*} (o : PolyOps α) : UBivL α → UBivL α → UBivL α
  | [], b => ubNeg o b
  | a, [] => a
  | b1 :: bs1, b2 :: bs2 => bivSub o b1 b2 :: ubSub o bs1 bs2

private def ubSc {α : Type*} (o : PolyOps α) (c : α) (a : UBivL α) : UBivL α :=
  a.map (bivSc o c)

private def ubBmul {α : Type*} (o : PolyOps α) (b0 : BivL α) (a : UBivL α) : UBivL α :=
  a.map (bivMul o b0)

private def ubShift {α : Type*} (a : UBivL α) : UBivL α := [] :: a

private def ubMulU {α : Type*} (o : PolyOps α) : UPoly α → UBivL α → UBivL α
  | [], _ => []
  | c :: cs, ub => ubAdd o (ubSc o c ub) (ubShift (ubMulU o cs ub))

private def ubSynDiv1Rem {α : Type*} (o : PolyOps α) : UBivL α → BivL α × UBivL α
  | [] => ([], [])
  | [b] => (b, [])
  | b :: b' :: rest =>
      let (r, q) := ubSynDiv1Rem o (b' :: rest)
      (bivAdd o b r, r :: q)

private def dotWAux {α : Type*} (o : PolyOps α) (W : List α) (shift j : ℕ) : ℕ → UPoly α → α
  | _, [] => o.zero
  | i, a :: as =>
      let idx := i + j + shift
      let term := if 1 ≤ idx ∧ idx ≤ 13 then o.mul a (W.getD (idx - 1) o.zero) else o.zero
      o.add term (dotWAux o W shift j (i + 1) as)

private def dotW {α : Type*} (o : PolyOps α) (A W : UPoly α) (shift : ℕ) : UPoly α :=
  [dotWAux o W shift 0 0 A, dotWAux o W shift 1 0 A, dotWAux o W shift 2 0 A,
   dotWAux o W shift 3 0 A, dotWAux o W shift 4 0 A]

private def combineBivDot {α : Type*} (o : PolyOps α) : UBivL α → UPoly α → BivL α
  | [], _ => []
  | _, [] => []
  | b :: bs, c :: cs => bivAdd o (bivSc o c b) (combineBivDot o bs cs)

private inductive SPoly (α : Type*)
  | sc : α → SPoly α
  | poly : UPoly α → SPoly α

private def sToU {α : Type*} : SPoly α → UPoly α
  | .sc a => [a]
  | .poly p => p

private def sNeg {α : Type*} (o : PolyOps α) : SPoly α → SPoly α
  | .sc a => .sc (o.neg a)
  | .poly p => .poly (uNeg o p)

private def sAdd {α : Type*} (o : PolyOps α) : SPoly α → SPoly α → SPoly α
  | .sc a, .sc b => .sc (o.add a b)
  | .sc a, .poly [] => .sc a
  | .sc a, .poly (b :: bs) => .poly (o.add a b :: bs)
  | .poly p, .poly q => .poly (uAdd o p q)
  | .poly [], .sc b => .sc b
  | .poly (a :: as), .sc b => .poly (o.add a b :: as)

private def sSub {α : Type*} (o : PolyOps α) : SPoly α → SPoly α → SPoly α
  | .sc a, .sc b => .sc (o.sub a b)
  | a, b => .poly (uSub o (sToU a) (sToU b))

private def sMul {α : Type*} (o : PolyOps α) : SPoly α → SPoly α → SPoly α
  | .sc a, .sc b => .sc (o.mul a b)
  | .sc a, .poly p => .poly (uSc o a p)
  | .poly p, .sc b => .poly (uSc o b p)
  | .poly p, .poly q => .poly (uMul o p q)

private def sShiftK {α : Type*} (o : PolyOps α) : ℕ → SPoly α → SPoly α
  | 0, x => x
  | k, .sc a => .poly (uMonomial o k a)
  | k + 1, .poly p => sShiftK o k (.poly (uShift o p))

private def uPow {α : Type*} (o : PolyOps α) (p : UPoly α) : ℕ → UPoly α
  | 0 => [o.ofInt 1]
  | n + 1 => uMul o (uPow o p n) p

private def evalExpr3SPoly {α : Type*} (o : PolyOps α) (S Q : α) (pS pQ : List α) : Expr → SPoly α
  | .num c => .sc (o.ofInt c)
  | .natCast n => .sc (o.ofInt (n : ℤ))
  | .intCast z => .sc (o.ofInt z)
  | .var 0 => .sc S
  | .var 1 => .sc Q
  | .var 2 => .poly [o.zero, o.ofInt 1]
  | .var _ => .sc o.zero
  | .neg a => sNeg o (evalExpr3SPoly o S Q pS pQ a)
  | .add a b => sAdd o (evalExpr3SPoly o S Q pS pQ a) (evalExpr3SPoly o S Q pS pQ b)
  | .sub a b => sSub o (evalExpr3SPoly o S Q pS pQ a) (evalExpr3SPoly o S Q pS pQ b)
  | .mul a b =>
      match b with
      | .var 2 => sShiftK o 1 (evalExpr3SPoly o S Q pS pQ a)
      | .pow (.var 2) k => sShiftK o k (evalExpr3SPoly o S Q pS pQ a)
      | _ => sMul o (evalExpr3SPoly o S Q pS pQ a) (evalExpr3SPoly o S Q pS pQ b)
  | .pow a k =>
      match a with
      | .var 0 => .sc (getPow o S pS k)
      | .var 1 => .sc (getPow o Q pQ k)
      | .var 2 => .poly (uMonomial o k (o.ofInt 1))
      | _ => .poly (uPow o (sToU (evalExpr3SPoly o S Q pS pQ a)) k)

private def evalExpr3PolyT {α : Type*} (o : PolyOps α) (S Q : α) (pS pQ : List α) (e : Expr) : UPoly α :=
  sToU (evalExpr3SPoly o S Q pS pQ e)

-- `PolyOpsRel` preservation lemmas for `UPoly`, `BivL`, `UBivL`, `dotW`, `combineBivDot`, `evalExpr3PolyT`
section PolyOpsRelLifts
variable {α β : Type*} {o1 : PolyOps α} {o2 : PolyOps β} {R : α → β → Prop}

private abbrev URel (R : α → β → Prop) := List.Forall₂ R
private abbrev BRel (R : α → β → Prop) := List.Forall₂ (List.Forall₂ R)
private abbrev UBRel (R : α → β → Prop) := List.Forall₂ (List.Forall₂ (List.Forall₂ R))

private lemma uAdd_rel (hR : PolyOpsRel o1 o2 R) :
    ∀ {a1 a2 b1 b2}, URel R a1 b1 → URel R a2 b2 → URel R (uAdd o1 a1 a2) (uAdd o2 b1 b2)
  | [], _, [], _, .nil, h2 => h2
  | _ :: _, [], _ :: _, [], h1, .nil => h1
  | _ :: _, _ :: _, _ :: _, _ :: _, .cons ha has, .cons hb hbs =>
      .cons (hR.rel_add ha hb) (uAdd_rel hR has hbs)

private lemma uNeg_rel (hR : PolyOpsRel o1 o2 R) {a b} (h : URel R a b) :
    URel R (uNeg o1 a) (uNeg o2 b) := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (hR.rel_neg hab) ih

private lemma uSub_rel (hR : PolyOpsRel o1 o2 R) :
    ∀ {a1 a2 b1 b2}, URel R a1 b1 → URel R a2 b2 → URel R (uSub o1 a1 a2) (uSub o2 b1 b2)
  | [], _, [], _, .nil, h2 => uNeg_rel hR h2
  | _ :: _, [], _ :: _, [], h1, .nil => h1
  | _ :: _, _ :: _, _ :: _, _ :: _, .cons ha has, .cons hb hbs =>
      .cons (hR.rel_sub ha hb) (uSub_rel hR has hbs)

private lemma uSc_rel (hR : PolyOpsRel o1 o2 R) {c1 c2} (hc : R c1 c2) {a b} (h : URel R a b) :
    URel R (uSc o1 c1 a) (uSc o2 c2 b) := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (hR.rel_mul hc hab) ih

private lemma uShift_rel (hR : PolyOpsRel o1 o2 R) {a b} (h : URel R a b) :
    URel R (uShift o1 a) (uShift o2 b) :=
  .cons hR.rel_zero h

private lemma uTail_rel : ∀ {a b}, URel R a b → URel R (uTail a) (uTail b)
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons _ h => h

private lemma uMul_rel (hR : PolyOpsRel o1 o2 R) :
    ∀ {a1 a2 b1 b2}, URel R a1 b1 → URel R a2 b2 → URel R (uMul o1 a1 a2) (uMul o2 b1 b2)
  | [], _, [], _, .nil, _ => .nil
  | _ :: _, _, _ :: _, _, .cons ha has, h2 =>
      uAdd_rel hR (uSc_rel hR ha h2) (uShift_rel hR (uMul_rel hR has h2))

private lemma uMonomial_rel (hR : PolyOpsRel o1 o2 R) :
    ∀ k {c1 c2}, R c1 c2 → URel R (uMonomial o1 k c1) (uMonomial o2 k c2)
  | 0, _, _, hc => .cons hc .nil
  | k + 1, _, _, hc => .cons hR.rel_zero (uMonomial_rel hR k hc)

private lemma uEval_rel (hR : PolyOpsRel o1 o2 R) {t1 t2} (ht : R t1 t2) :
    ∀ {a b}, URel R a b → R (uEval o1 a t1) (uEval o2 b t2)
  | [], [], .nil => hR.rel_zero
  | _ :: _, _ :: _, .cons ha has => hR.rel_add ha (hR.rel_mul ht (uEval_rel hR ht has))

private lemma bivAdd_rel (hR : PolyOpsRel o1 o2 R) :
    ∀ {a1 a2 b1 b2}, BRel R a1 b1 → BRel R a2 b2 → BRel R (bivAdd o1 a1 a2) (bivAdd o2 b1 b2)
  | [], _, [], _, .nil, h2 => h2
  | _ :: _, [], _ :: _, [], h1, .nil => h1
  | _ :: _, _ :: _, _ :: _, _ :: _, .cons ha has, .cons hb hbs =>
      .cons (uAdd_rel hR ha hb) (bivAdd_rel hR has hbs)

private lemma bivNeg_rel (hR : PolyOpsRel o1 o2 R) {a b} (h : BRel R a b) :
    BRel R (bivNeg o1 a) (bivNeg o2 b) := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (uNeg_rel hR hab) ih

private lemma bivSub_rel (hR : PolyOpsRel o1 o2 R) :
    ∀ {a1 a2 b1 b2}, BRel R a1 b1 → BRel R a2 b2 → BRel R (bivSub o1 a1 a2) (bivSub o2 b1 b2)
  | [], _, [], _, .nil, h2 => bivNeg_rel hR h2
  | _ :: _, [], _ :: _, [], h1, .nil => h1
  | _ :: _, _ :: _, _ :: _, _ :: _, .cons ha has, .cons hb hbs =>
      .cons (uSub_rel hR ha hb) (bivSub_rel hR has hbs)

private lemma bivSc_rel (hR : PolyOpsRel o1 o2 R) {c1 c2} (hc : R c1 c2) {a b} (h : BRel R a b) :
    BRel R (bivSc o1 c1 a) (bivSc o2 c2 b) := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (uSc_rel hR hc hab) ih

private lemma bivConst_rel {c1 c2} (hc : R c1 c2) : BRel R (bivConst c1) (bivConst c2) :=
  .cons (.cons hc .nil) .nil

private lemma bivMul_rel (hR : PolyOpsRel o1 o2 R) :
    ∀ {a1 a2 b1 b2}, BRel R a1 b1 → BRel R a2 b2 → BRel R (bivMul o1 a1 a2) (bivMul o2 b1 b2)
  | [], _, [], _, .nil, _ => .nil
  | _ :: _, _, _ :: _, _, .cons ha has, h2 => by
      refine bivAdd_rel hR ?_ (.cons .nil (bivMul_rel hR has h2))
      clear has
      induction h2 with
      | nil => exact .nil
      | cons hb _ ih => exact .cons (uMul_rel hR ha hb) ih

private lemma bivRedOnce_rel (hR : PolyOpsRel o1 o2 R)
    {s1 s2 t1 t2 n1 n2} (hs : R s1 s2) (ht : R t1 t2) (hn : R n1 n2) :
    ∀ {a b}, BRel R a b → BRel R (bivRedOnce o1 s1 t1 n1 a) (bivRedOnce o2 s2 t2 n2 b)
  | [], [], .nil => .nil
  | [_], [_], .cons h0 .nil => .cons (uSc_rel hR hs h0) .nil
  | [_, _], [_, _], .cons h0 (.cons h1 .nil) => .cons (uSc_rel hR hs h0) (.cons (uSc_rel hR hs h1) .nil)
  | _ :: _ :: _ :: _, _ :: _ :: _ :: _, .cons h0 (.cons h1 (.cons h2 hrest)) => by
      refine bivAdd_rel hR (.cons (uSc_rel hR hs h0) (.cons (uSc_rel hR hs h1) .nil)) ?_
      have hmap : ∀ {x y}, BRel R x y →
          BRel R (x.map fun ri => uAdd o1 (uSc o1 n1 ri) (uShift o1 (uShift o1 (uSc o1 t1 ri))))
                 (y.map fun ri => uAdd o2 (uSc o2 n2 ri) (uShift o2 (uShift o2 (uSc o2 t2 ri)))) := by
        intro x y hxy; induction hxy with
        | nil => exact .nil
        | cons hxy' _ ih =>
            exact .cons (uAdd_rel hR (uSc_rel hR hn hxy') (uShift_rel hR (uShift_rel hR (uSc_rel hR ht hxy')))) ih
      exact hmap (.cons h2 hrest)

private lemma ubAdd_rel (hR : PolyOpsRel o1 o2 R) :
    ∀ {a1 a2 b1 b2}, UBRel R a1 b1 → UBRel R a2 b2 → UBRel R (ubAdd o1 a1 a2) (ubAdd o2 b1 b2)
  | [], _, [], _, .nil, h2 => h2
  | _ :: _, [], _ :: _, [], h1, .nil => h1
  | _ :: _, _ :: _, _ :: _, _ :: _, .cons ha has, .cons hb hbs =>
      .cons (bivAdd_rel hR ha hb) (ubAdd_rel hR has hbs)

private lemma ubNeg_rel (hR : PolyOpsRel o1 o2 R) {a b} (h : UBRel R a b) :
    UBRel R (ubNeg o1 a) (ubNeg o2 b) := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (bivNeg_rel hR hab) ih

private lemma ubSub_rel (hR : PolyOpsRel o1 o2 R) :
    ∀ {a1 a2 b1 b2}, UBRel R a1 b1 → UBRel R a2 b2 → UBRel R (ubSub o1 a1 a2) (ubSub o2 b1 b2)
  | [], _, [], _, .nil, h2 => ubNeg_rel hR h2
  | _ :: _, [], _ :: _, [], h1, .nil => h1
  | _ :: _, _ :: _, _ :: _, _ :: _, .cons ha has, .cons hb hbs =>
      .cons (bivSub_rel hR ha hb) (ubSub_rel hR has hbs)

private lemma ubSc_rel (hR : PolyOpsRel o1 o2 R) {c1 c2} (hc : R c1 c2) {a b} (h : UBRel R a b) :
    UBRel R (ubSc o1 c1 a) (ubSc o2 c2 b) := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (bivSc_rel hR hc hab) ih

private lemma ubBmul_rel (hR : PolyOpsRel o1 o2 R) {b1 b2} (hb : BRel R b1 b2) {a1 a2} (ha : UBRel R a1 a2) :
    UBRel R (ubBmul o1 b1 a1) (ubBmul o2 b2 a2) := by
  induction ha with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (bivMul_rel hR hb hab) ih

private lemma ubShift_rel {a b} (h : UBRel R a b) : UBRel R (ubShift a) (ubShift b) :=
  .cons .nil h

private lemma ubMulU_rel (hR : PolyOpsRel o1 o2 R) :
    ∀ {u1 u2 b1 b2}, URel R u1 u2 → UBRel R b1 b2 → UBRel R (ubMulU o1 u1 b1) (ubMulU o2 u2 b2)
  | [], [], _, _, .nil, _ => .nil
  | _ :: _, _ :: _, _, _, .cons hc hcs, hb =>
      ubAdd_rel hR (ubSc_rel hR hc hb) (ubShift_rel (ubMulU_rel hR hcs hb))

private lemma ubSynDiv1Rem_rel (hR : PolyOpsRel o1 o2 R) :
    ∀ {a b}, UBRel R a b →
      BRel R (ubSynDiv1Rem o1 a).1 (ubSynDiv1Rem o2 b).1 ∧
      UBRel R (ubSynDiv1Rem o1 a).2 (ubSynDiv1Rem o2 b).2
  | [], [], .nil => ⟨.nil, .nil⟩
  | [_], [_], .cons h .nil => ⟨h, .nil⟩
  | _ :: _ :: _, _ :: _ :: _, .cons h1 (.cons h2 hrest) =>
      let ih := ubSynDiv1Rem_rel hR (.cons h2 hrest)
      ⟨bivAdd_rel hR h1 ih.1, .cons ih.1 ih.2⟩

private lemma list_getD_rel (hR : PolyOpsRel o1 o2 R) {l1 l2} (hl : URel R l1 l2) (k : ℕ) :
    R (l1.getD k o1.zero) (l2.getD k o2.zero) := by
  induction hl generalizing k with
  | nil => exact hR.rel_zero
  | cons hab _ ih =>
      cases k with
      | zero => exact hab
      | succ k' => exact ih k'

private lemma dotWAux_rel (hR : PolyOpsRel o1 o2 R) {W1 W2} (hW : URel R W1 W2) (shift j : ℕ) :
    ∀ i {A1 A2}, URel R A1 A2 → R (dotWAux o1 W1 shift j i A1) (dotWAux o2 W2 shift j i A2)
  | _, [], [], .nil => hR.rel_zero
  | i, _ :: _, _ :: _, .cons ha has => by
      dsimp only [dotWAux]
      apply hR.rel_add
      · split_ifs
        · exact hR.rel_mul ha (list_getD_rel hR hW _)
        · exact hR.rel_zero
      · exact dotWAux_rel hR hW shift j (i + 1) has

private lemma dotW_rel (hR : PolyOpsRel o1 o2 R) {A1 A2 W1 W2} (hA : URel R A1 A2) (hW : URel R W1 W2) (shift : ℕ) :
    URel R (dotW o1 A1 W1 shift) (dotW o2 A2 W2 shift) :=
  .cons (dotWAux_rel hR hW shift 0 0 hA) (.cons (dotWAux_rel hR hW shift 1 0 hA)
    (.cons (dotWAux_rel hR hW shift 2 0 hA) (.cons (dotWAux_rel hR hW shift 3 0 hA)
      (.cons (dotWAux_rel hR hW shift 4 0 hA) .nil))))

private lemma combineBivDot_rel (hR : PolyOpsRel o1 o2 R) :
    ∀ {B1 B2 t1 t2}, UBRel R B1 B2 → URel R t1 t2 → BRel R (combineBivDot o1 B1 t1) (combineBivDot o2 B2 t2)
  | [], [], _, _, .nil, _ => .nil
  | _ :: _, _ :: _, [], [], _, .nil => .nil
  | _ :: _, _ :: _, _ :: _, _ :: _, .cons hb hbs, .cons hc hcs =>
      bivAdd_rel hR (bivSc_rel hR hc hb) (combineBivDot_rel hR hbs hcs)

private inductive SRel (R : α → β → Prop) : SPoly α → SPoly β → Prop
  | sc {a b} : R a b → SRel R (.sc a) (.sc b)
  | poly {a b} : URel R a b → SRel R (.poly a) (.poly b)

private lemma sToU_rel {a b} (h : SRel R a b) : URel R (sToU a) (sToU b) := by
  cases h with
  | sc hab => exact .cons hab .nil
  | poly hab => exact hab

private lemma sNeg_rel (hR : PolyOpsRel o1 o2 R) {a b} (h : SRel R a b) : SRel R (sNeg o1 a) (sNeg o2 b) := by
  cases h with
  | sc hab => exact .sc (hR.rel_neg hab)
  | poly hab => exact .poly (uNeg_rel hR hab)

private lemma sAdd_rel (hR : PolyOpsRel o1 o2 R) {a1 a2 b1 b2} (h1 : SRel R a1 b1) (h2 : SRel R a2 b2) :
    SRel R (sAdd o1 a1 a2) (sAdd o2 b1 b2) := by
  cases h1 with
  | sc ha =>
      cases h2 with
      | sc hb => exact .sc (hR.rel_add ha hb)
      | poly hb =>
          cases hb with
          | nil => exact .sc ha
          | cons hb0 hbs => exact .poly (.cons (hR.rel_add ha hb0) hbs)
  | poly ha =>
      cases h2 with
      | sc hb =>
          cases ha with
          | nil => exact .sc hb
          | cons ha0 has => exact .poly (.cons (hR.rel_add ha0 hb) has)
      | poly hb => exact .poly (uAdd_rel hR ha hb)

private lemma sSub_rel (hR : PolyOpsRel o1 o2 R) {a1 a2 b1 b2} (h1 : SRel R a1 b1) (h2 : SRel R a2 b2) :
    SRel R (sSub o1 a1 a2) (sSub o2 b1 b2) := by
  cases h1 with
  | sc ha =>
      cases h2 with
      | sc hb => exact .sc (hR.rel_sub ha hb)
      | poly hb => exact .poly (uSub_rel hR (.cons ha .nil) hb)
  | poly ha =>
      cases h2 with
      | sc hb => exact .poly (uSub_rel hR ha (.cons hb .nil))
      | poly hb => exact .poly (uSub_rel hR ha hb)

private lemma sMul_rel (hR : PolyOpsRel o1 o2 R) {a1 a2 b1 b2} (h1 : SRel R a1 b1) (h2 : SRel R a2 b2) :
    SRel R (sMul o1 a1 a2) (sMul o2 b1 b2) := by
  cases h1 with
  | sc ha =>
      cases h2 with
      | sc hb => exact .sc (hR.rel_mul ha hb)
      | poly hb => exact .poly (uSc_rel hR ha hb)
  | poly ha =>
      cases h2 with
      | sc hb => exact .poly (uSc_rel hR hb ha)
      | poly hb => exact .poly (uMul_rel hR ha hb)

private lemma sShiftK_rel (hR : PolyOpsRel o1 o2 R) :
    ∀ k {a b}, SRel R a b → SRel R (sShiftK o1 k a) (sShiftK o2 k b)
  | 0, _, _, h => h
  | k + 1, _, _, .sc hab => .poly (uMonomial_rel hR (k + 1) hab)
  | k + 1, _, _, .poly hab => sShiftK_rel hR k (.poly (uShift_rel hR hab))

private lemma uPow_rel (hR : PolyOpsRel o1 o2 R) {p1 p2} (hp : URel R p1 p2) :
    ∀ k, URel R (uPow o1 p1 k) (uPow o2 p2 k)
  | 0 => .cons (hR.rel_ofInt 1) .nil
  | k + 1 => uMul_rel hR (uPow_rel hR hp k) hp

private lemma evalExpr3SPoly_rel (hR : PolyOpsRel o1 o2 R) {S1 Q1 : α} {S2 Q2 : β}
    (hS : R S1 S2) (hQ : R Q1 Q2) {pS1 pQ1 : List α} {pS2 pQ2 : List β}
    (hpS : URel R pS1 pS2) (hpQ : URel R pQ1 pQ2) :
    ∀ e : Expr, SRel R (evalExpr3SPoly o1 S1 Q1 pS1 pQ1 e) (evalExpr3SPoly o2 S2 Q2 pS2 pQ2 e)
  | .num c => .sc (hR.rel_ofInt c)
  | .natCast n => .sc (hR.rel_ofInt n)
  | .intCast z => .sc (hR.rel_ofInt z)
  | .var 0 => .sc hS
  | .var 1 => .sc hQ
  | .var 2 => .poly (.cons hR.rel_zero (.cons (hR.rel_ofInt 1) .nil))
  | .var (_ + 3) => .sc hR.rel_zero
  | .neg a => sNeg_rel hR (evalExpr3SPoly_rel hR hS hQ hpS hpQ a)
  | .add a b => sAdd_rel hR (evalExpr3SPoly_rel hR hS hQ hpS hpQ a) (evalExpr3SPoly_rel hR hS hQ hpS hpQ b)
  | .sub a b => sSub_rel hR (evalExpr3SPoly_rel hR hS hQ hpS hpQ a) (evalExpr3SPoly_rel hR hS hQ hpS hpQ b)
  | .mul a b => by
      have ha := evalExpr3SPoly_rel hR hS hQ hpS hpQ a
      have hb := evalExpr3SPoly_rel hR hS hQ hpS hpQ b
      dsimp only [evalExpr3SPoly]
      split
      · exact sShiftK_rel hR 1 ha
      · exact sShiftK_rel hR _ ha
      · exact sMul_rel hR ha hb
  | .pow a k => by
      have ha := evalExpr3SPoly_rel hR hS hQ hpS hpQ a
      dsimp only [evalExpr3SPoly]
      split
      · exact .sc (getPow_rel hR hS hpS k)
      · exact .sc (getPow_rel hR hQ hpQ k)
      · exact .poly (uMonomial_rel hR k (hR.rel_ofInt 1))
      · exact .poly (uPow_rel hR (sToU_rel ha) k)

private lemma evalExpr3PolyT_rel (hR : PolyOpsRel o1 o2 R) {S1 Q1 : α} {S2 Q2 : β}
    (hS : R S1 S2) (hQ : R Q1 Q2) {pS1 pQ1 : List α} {pS2 pQ2 : List β}
    (hpS : URel R pS1 pS2) (hpQ : URel R pQ1 pQ2) (e : Expr) :
    URel R (evalExpr3PolyT o1 S1 Q1 pS1 pQ1 e) (evalExpr3PolyT o2 S2 Q2 pS2 pQ2 e) :=
  sToU_rel (evalExpr3SPoly_rel hR hS hQ hpS hpQ e)

end PolyOpsRelLifts

-- Evaluation of `UPoly K5`, `BivL K5`, `UBivL K5` into `K5[X]` and `K5`!
private def evalUPolyK5 : UPoly K5 → K5[X]
  | [] => 0
  | a :: as => Polynomial.C a + Polynomial.X * evalUPolyK5 as

private def evalYListK5 : UPoly K5 → K5
  | [] => 0
  | a :: as => a + y_K * evalYListK5 as

private def evalBivLK5 : BivL K5 → K5
  | [] => 0
  | r :: rs => evalYListK5 r + x_K * evalBivLK5 rs

private def evalUBivLK5 : UBivL K5 → K5[X]
  | [] => 0
  | b :: bs => Polynomial.C (evalBivLK5 b) + Polynomial.X * evalUBivLK5 bs

private lemma list_getD_of_le {α : Type*} (a : List α) (d : α) {k : ℕ} (hk : a.length ≤ k) :
    a.getD k d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]; rfl

private lemma evalUPolyK5_uAdd : ∀ a b, evalUPolyK5 (uAdd k5Ops a b) = evalUPolyK5 a + evalUPolyK5 b
  | [], b => by simp [uAdd, evalUPolyK5]
  | a :: as, [] => by simp [uAdd, evalUPolyK5]
  | a :: as, b :: bs => by
      simp only [uAdd, evalUPolyK5, evalUPolyK5_uAdd as bs]; dsimp only [k5Ops]; simp only [map_add]; ring

private lemma evalUPolyK5_uNeg (a : UPoly K5) : evalUPolyK5 (uNeg k5Ops a) = -evalUPolyK5 a := by
  induction a with
  | nil => simp [uNeg, evalUPolyK5]
  | cons a as ih =>
      simp only [uNeg, List.map_cons, evalUPolyK5] at ih ⊢; rw [ih]; dsimp only [k5Ops]; simp only [map_neg]; ring

private lemma evalUPolyK5_uSub : ∀ a b, evalUPolyK5 (uSub k5Ops a b) = evalUPolyK5 a - evalUPolyK5 b
  | [], b => by simp [uSub, evalUPolyK5, evalUPolyK5_uNeg]
  | a :: as, [] => by simp [uSub, evalUPolyK5]
  | a :: as, b :: bs => by
      simp only [uSub, evalUPolyK5, evalUPolyK5_uSub as bs]; dsimp only [k5Ops]; simp only [map_sub]; ring

private lemma evalUPolyK5_uSc (c : K5) (a : UPoly K5) :
    evalUPolyK5 (uSc k5Ops c a) = Polynomial.C c * evalUPolyK5 a := by
  induction a with
  | nil => simp [uSc, evalUPolyK5]
  | cons a as ih =>
      simp only [uSc, List.map_cons, evalUPolyK5] at ih ⊢; rw [ih]; dsimp only [k5Ops]; simp only [map_mul]; ring

private lemma evalUPolyK5_uShift (a : UPoly K5) : evalUPolyK5 (uShift k5Ops a) = Polynomial.X * evalUPolyK5 a := by
  simp [uShift, evalUPolyK5, k5Ops]

private lemma evalUPolyK5_uMul : ∀ a b, evalUPolyK5 (uMul k5Ops a b) = evalUPolyK5 a * evalUPolyK5 b
  | [], b => by simp [uMul, evalUPolyK5]
  | a :: as, b => by
      simp only [uMul, evalUPolyK5, evalUPolyK5_uAdd, evalUPolyK5_uSc, evalUPolyK5_uShift,
        evalUPolyK5_uMul as b]; ring

private lemma evalUPolyK5_uTail : ∀ a, evalUPolyK5 a = Polynomial.C (a.headD 0) + Polynomial.X * evalUPolyK5 (uTail a)
  | [] => by simp [evalUPolyK5, uTail]
  | _ :: _ => by simp [evalUPolyK5, uTail]

private lemma evalUPolyK5_coeff (a : UPoly K5) : ∀ k, (evalUPolyK5 a).coeff k = a.getD k 0 := by
  induction a with
  | nil => intro k; simp [evalUPolyK5]
  | cons x xs ih =>
      intro k; cases k with
      | zero => simp [evalUPolyK5]
      | succ k' => simp [evalUPolyK5, Polynomial.coeff_X_mul, ih k']

private lemma evalUPolyK5_natDegree_le (a : UPoly K5) (k : ℕ) (hk : a.length ≤ k) :
    (evalUPolyK5 a).coeff k = 0 := by
  rw [evalUPolyK5_coeff, list_getD_of_le a 0 hk]

private lemma evalYListK5_uAdd : ∀ a b, evalYListK5 (uAdd k5Ops a b) = evalYListK5 a + evalYListK5 b
  | [], b => by simp [uAdd, evalYListK5]
  | a :: as, [] => by simp [uAdd, evalYListK5]
  | a :: as, b :: bs => by simp only [uAdd, evalYListK5, evalYListK5_uAdd as bs]; dsimp only [k5Ops]; ring

private lemma evalYListK5_uNeg (a : UPoly K5) : evalYListK5 (uNeg k5Ops a) = -evalYListK5 a := by
  induction a with
  | nil => simp [uNeg, evalYListK5]
  | cons a as ih => simp only [uNeg, List.map_cons, evalYListK5] at ih ⊢; rw [ih]; dsimp only [k5Ops]; ring

private lemma evalYListK5_uSub : ∀ a b, evalYListK5 (uSub k5Ops a b) = evalYListK5 a - evalYListK5 b
  | [], b => by simp [uSub, evalYListK5, evalYListK5_uNeg]
  | a :: as, [] => by simp [uSub, evalYListK5]
  | a :: as, b :: bs => by simp only [uSub, evalYListK5, evalYListK5_uSub as bs]; dsimp only [k5Ops]; ring

private lemma evalYListK5_uSc (c : K5) (a : UPoly K5) : evalYListK5 (uSc k5Ops c a) = c * evalYListK5 a := by
  induction a with
  | nil => simp [uSc, evalYListK5]
  | cons a as ih => simp only [uSc, List.map_cons, evalYListK5] at ih ⊢; rw [ih]; dsimp only [k5Ops]; ring

private lemma evalYListK5_uShift (a : UPoly K5) : evalYListK5 (uShift k5Ops a) = y_K * evalYListK5 a := by
  simp [uShift, evalYListK5, k5Ops]

private lemma evalYListK5_uMul : ∀ a b, evalYListK5 (uMul k5Ops a b) = evalYListK5 a * evalYListK5 b
  | [], b => by simp [uMul, evalYListK5]
  | a :: as, b => by
      simp only [uMul, evalYListK5, evalYListK5_uAdd, evalYListK5_uSc, evalYListK5_uShift,
        evalYListK5_uMul as b]; ring

private lemma evalBivLK5_bivAdd : ∀ a b, evalBivLK5 (bivAdd k5Ops a b) = evalBivLK5 a + evalBivLK5 b
  | [], b => by simp [bivAdd, evalBivLK5]
  | a :: as, [] => by simp [bivAdd, evalBivLK5]
  | a :: as, b :: bs => by
      simp only [bivAdd, evalBivLK5, evalYListK5_uAdd, evalBivLK5_bivAdd as bs]; ring

private lemma evalBivLK5_bivNeg (a : BivL K5) : evalBivLK5 (bivNeg k5Ops a) = -evalBivLK5 a := by
  induction a with
  | nil => simp [bivNeg, evalBivLK5]
  | cons a as ih => simp only [bivNeg, List.map_cons, evalBivLK5, evalYListK5_uNeg] at ih ⊢; rw [ih]; ring

private lemma evalBivLK5_bivSub : ∀ a b, evalBivLK5 (bivSub k5Ops a b) = evalBivLK5 a - evalBivLK5 b
  | [], b => by simp [bivSub, evalBivLK5, evalBivLK5_bivNeg]
  | a :: as, [] => by simp [bivSub, evalBivLK5]
  | a :: as, b :: bs => by
      simp only [bivSub, evalBivLK5, evalYListK5_uSub, evalBivLK5_bivSub as bs]; ring

private lemma evalBivLK5_bivSc (c : K5) (a : BivL K5) : evalBivLK5 (bivSc k5Ops c a) = c * evalBivLK5 a := by
  induction a with
  | nil => simp [bivSc, evalBivLK5]
  | cons a as ih => simp only [bivSc, List.map_cons, evalBivLK5, evalYListK5_uSc] at ih ⊢; rw [ih]; ring

private lemma evalBivLK5_bivMul : ∀ a b, evalBivLK5 (bivMul k5Ops a b) = evalBivLK5 a * evalBivLK5 b
  | [], b => by simp [bivMul, evalBivLK5]
  | r :: rs, b => by
      have hmap : ∀ (l : BivL K5), evalBivLK5 (l.map (uMul k5Ops r)) = evalYListK5 r * evalBivLK5 l := by
        intro l; induction l with
        | nil => simp [evalBivLK5]
        | cons x xs ih => simp only [List.map_cons, evalBivLK5, evalYListK5_uMul, ih]; ring
      simp only [bivMul, evalBivLK5, evalBivLK5_bivAdd, hmap, evalBivLK5_bivMul rs b, evalYListK5]; ring

private lemma F5_of_K5_zero : F5_of S_K Q_K T_K x_K y_K = 0 := by
  have h := F5_of_L (L := K5)
  simpa only [F5_of, H0_of, SL, QL, TL, xL, yL, ιL, Algebra.algebraMap_self, RingHom.id_apply] using h

private lemma evalBivLK5_bivRedOnce (b : BivL K5) :
    evalBivLK5 (bivRedOnce k5Ops (21 * S_K) (-(21 * T_K)) (-(7 * H0_of S_K Q_K T_K)) b) =
      (21 * S_K) * evalBivLK5 b := by
  have hx2 : 21 * S_K * x_K ^ 2 = -(21 * T_K) * y_K ^ 2 + -(7 * H0_of S_K Q_K T_K) := by
    have hF := F5_of_K5_zero; unfold F5_of at hF; linear_combination 7 * hF
  have hrest : ∀ l : BivL K5,
      evalBivLK5 (l.map fun ri => uAdd k5Ops (uSc k5Ops (-(7 * H0_of S_K Q_K T_K)) ri)
        (uShift k5Ops (uShift k5Ops (uSc k5Ops (-(21 * T_K)) ri)))) =
      (21 * S_K) * (x_K ^ 2 * evalBivLK5 l) := by
    intro l; induction l with
    | nil => simp [evalBivLK5]
    | cons r rs ih =>
        simp only [List.map_cons, evalBivLK5, evalYListK5_uAdd, evalYListK5_uSc, evalYListK5_uShift, ih]
        linear_combination -evalYListK5 r * hx2
  match b with
  | [] => simp [bivRedOnce, evalBivLK5]
  | [r0] => simp [bivRedOnce, evalBivLK5, evalYListK5_uSc]
  | [r0, r1] => simp only [bivRedOnce, evalBivLK5, evalYListK5_uSc]; ring
  | r0 :: r1 :: r2 :: rest =>
      simp only [bivRedOnce, evalBivLK5_bivAdd, evalBivLK5, evalYListK5_uSc, hrest (r2 :: rest)]
      ring

private lemma evalUBivLK5_ubAdd : ∀ a b, evalUBivLK5 (ubAdd k5Ops a b) = evalUBivLK5 a + evalUBivLK5 b
  | [], b => by simp [ubAdd, evalUBivLK5]
  | a :: as, [] => by simp [ubAdd, evalUBivLK5]
  | a :: as, b :: bs => by
      simp only [ubAdd, evalUBivLK5, evalBivLK5_bivAdd, map_add, evalUBivLK5_ubAdd as bs]; ring

private lemma evalUBivLK5_ubNeg (a : UBivL K5) : evalUBivLK5 (ubNeg k5Ops a) = -evalUBivLK5 a := by
  induction a with
  | nil => simp [ubNeg, evalUBivLK5]
  | cons a as ih =>
      simp only [ubNeg, List.map_cons, evalUBivLK5, evalBivLK5_bivNeg, map_neg] at ih ⊢; rw [ih]; ring

private lemma evalUBivLK5_ubSub : ∀ a b, evalUBivLK5 (ubSub k5Ops a b) = evalUBivLK5 a - evalUBivLK5 b
  | [], b => by simp [ubSub, evalUBivLK5, evalUBivLK5_ubNeg]
  | a :: as, [] => by simp [ubSub, evalUBivLK5]
  | a :: as, b :: bs => by
      simp only [ubSub, evalUBivLK5, evalBivLK5_bivSub, map_sub, evalUBivLK5_ubSub as bs]; ring

private lemma evalUBivLK5_ubSc (c : K5) (a : UBivL K5) :
    evalUBivLK5 (ubSc k5Ops c a) = Polynomial.C c * evalUBivLK5 a := by
  induction a with
  | nil => simp [ubSc, evalUBivLK5]
  | cons a as ih =>
      simp only [ubSc, List.map_cons, evalUBivLK5, evalBivLK5_bivSc, map_mul] at ih ⊢; rw [ih]; ring

private lemma evalUBivLK5_ubBmul (b0 : BivL K5) (a : UBivL K5) :
    evalUBivLK5 (ubBmul k5Ops b0 a) = Polynomial.C (evalBivLK5 b0) * evalUBivLK5 a := by
  induction a with
  | nil => simp [ubBmul, evalUBivLK5]
  | cons a as ih =>
      simp only [ubBmul, List.map_cons, evalUBivLK5, evalBivLK5_bivMul, map_mul] at ih ⊢; rw [ih]; ring

private lemma evalUBivLK5_ubShift (a : UBivL K5) : evalUBivLK5 (ubShift a) = Polynomial.X * evalUBivLK5 a := by
  simp [ubShift, evalUBivLK5, evalBivLK5]

private lemma evalUBivLK5_ubMulU : ∀ u b, evalUBivLK5 (ubMulU k5Ops u b) = evalUPolyK5 u * evalUBivLK5 b
  | [], b => by simp [ubMulU, evalUPolyK5, evalUBivLK5]
  | c :: cs, b => by
      simp only [ubMulU, evalUPolyK5, evalUBivLK5_ubAdd, evalUBivLK5_ubSc, evalUBivLK5_ubShift,
        evalUBivLK5_ubMulU cs b]; ring

private lemma evalUBivLK5_ubSynDiv1Rem :
    ∀ a, evalUBivLK5 a = Polynomial.C (evalBivLK5 (ubSynDiv1Rem k5Ops a).1) +
      (Polynomial.X - 1) * evalUBivLK5 (ubSynDiv1Rem k5Ops a).2
  | [] => by simp [ubSynDiv1Rem, evalUBivLK5, evalBivLK5]
  | [b] => by simp [ubSynDiv1Rem, evalUBivLK5]
  | b :: b' :: rest => by
      have ih := evalUBivLK5_ubSynDiv1Rem (b' :: rest)
      simp only [ubSynDiv1Rem, evalUBivLK5, evalBivLK5_bivAdd, map_add] at ih ⊢
      linear_combination Polynomial.X * ih

private lemma evalUBivLK5_coeff (a : UBivL K5) : ∀ k, (evalUBivLK5 a).coeff k = evalBivLK5 (a.getD k []) := by
  induction a with
  | nil => intro k; simp [evalUBivLK5, evalBivLK5]
  | cons b bs ih =>
      intro k; cases k with
      | zero => simp [evalUBivLK5]
      | succ k' => simp [evalUBivLK5, Polynomial.coeff_X_mul, ih k']

-- Bilinear `dotW` + `combineBivDot` identity:
private lemma evalBivLK5_combineBivDot_dotW (A : UPoly K5) (B : UBivL K5) (W : UPoly K5) (shift : ℕ)
    (hBlen : B.length ≤ 5) (hdeg : A.length + B.length + shift ≤ 15) :
    evalBivLK5 (combineBivDot k5Ops B (dotW k5Ops A W shift)) =
      ∑ k : Fin 13, ((Polynomial.X ^ shift * evalUPolyK5 A * evalUBivLK5 B).coeff (k.val + 1)) * W.getD k.val 0 := by
  have hdot : ∀ (j i : ℕ) (L : UPoly K5),
      dotWAux k5Ops W shift j i L =
        ∑ m ∈ Finset.range L.length,
          if 1 ≤ i + m + j + shift ∧ i + m + j + shift ≤ 13 then
            L.getD m 0 * W.getD (i + m + j + shift - 1) 0
          else 0 := by
    intro j i L; induction L generalizing i with
    | nil => simp [dotWAux, k5Ops]
    | cons x xs ih =>
        simp only [dotWAux, List.length_cons, Finset.sum_range_succ', ih (i + 1)]
        dsimp only [k5Ops]
        rw [add_comm]
        congr 1
        apply Finset.sum_congr rfl; intro m _
        have heq : i + 1 + m + j + shift = i + (m + 1) + j + shift := by omega
        simp [heq]
  have hcomb : ∀ (L : UBivL K5) (ts : UPoly K5), L.length ≤ ts.length →
      evalBivLK5 (combineBivDot k5Ops L ts) =
        ∑ j ∈ Finset.range L.length, ts.getD j 0 * evalBivLK5 (L.getD j []) := by
    intro L; induction L with
    | nil => intro _ _; simp [combineBivDot, evalBivLK5]
    | cons b bs ih =>
        intro ts hle; cases ts with
        | nil => simp at hle
        | cons t ts' =>
            simp only [combineBivDot, evalBivLK5_bivAdd, evalBivLK5_bivSc, List.length_cons,
              Finset.sum_range_succ', ih ts' (by simpa using hle)]
            rw [add_comm]; simp
  rw [hcomb B (dotW k5Ops A W shift) (by simpa [dotW] using hBlen)]
  have hgetD_dot : ∀ j < B.length,
      (dotW k5Ops A W shift).getD j 0 =
        ∑ i ∈ Finset.range A.length,
          if 1 ≤ i + j + shift ∧ i + j + shift ≤ 13 then
            A.getD i 0 * W.getD (i + j + shift - 1) 0
          else 0 := by
    intro j hj
    have hj5 : j < 5 := lt_of_lt_of_le hj hBlen
    interval_cases j <;> simp only [dotW, List.getD_cons_zero, List.getD_cons_succ, hdot, zero_add]
  rw [Finset.sum_congr rfl fun j hj => by rw [hgetD_dot j (Finset.mem_range.mp hj), Finset.sum_mul]]
  rw [← Finset.sum_product']
  -- Match every `(j, i)` pair to `k = i + j + shift - 1` when `1 ≤ i + j + shift ≤ 13`:
  have hcoeff (k : Fin 13) :
      (Polynomial.X ^ shift * evalUPolyK5 A * evalUBivLK5 B).coeff (k.val + 1) =
        ∑ p ∈ Finset.range B.length ×ˢ Finset.range A.length,
          if p.2 + p.1 + shift = k.val + 1 then A.getD p.2 0 * evalBivLK5 (B.getD p.1 []) else 0 := by
    rw [mul_assoc, Polynomial.coeff_X_pow_mul']
    split_ifs with hsh
    · rw [Polynomial.coeff_mul]
      have hcongr : ∀ x : ℕ × ℕ, (evalUPolyK5 A).coeff x.1 * (evalUBivLK5 B).coeff x.2 =
          if x.1 < A.length ∧ x.2 < B.length then A.getD x.1 0 * evalBivLK5 (B.getD x.2 []) else 0 := by
        intro x; rw [evalUPolyK5_coeff, evalUBivLK5_coeff]
        split_ifs with h
        · rfl
        · push_neg at h
          by_cases h1 : x.1 < A.length
          · rw [list_getD_of_le B [] (h h1), evalBivLK5, mul_zero]
          · rw [list_getD_of_le A 0 (by omega), zero_mul]
      simp_rw [hcongr]
      rw [← Finset.sum_filter]
      symm; rw [← Finset.sum_filter]
      refine Finset.sum_nbij (fun p => (p.2, p.1)) ?_ ?_ ?_ ?_
      · intro p hp
        simp [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_antidiagonal] at hp ⊢
        exact ⟨by omega, hp.1.2, hp.1.1⟩
      · intro p1 _ p2 _ h; ext <;> [exact congrArg Prod.snd h; exact congrArg Prod.fst h]
      · intro x hx
        simp [Finset.mem_filter, Finset.mem_antidiagonal] at hx
        refine ⟨(x.2, x.1), ?_, rfl⟩
        simp [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        exact ⟨⟨hx.2.2, hx.2.1⟩, by omega⟩
      · intro _ _; rfl
    · symm; apply Finset.sum_eq_zero; intro p _
      have : p.2 + p.1 + shift ≠ k.val + 1 := by omega
      simp [this]
  simp_rw [hcoeff, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro p hp
  simp only [Finset.mem_product, Finset.mem_range] at hp
  have hle13 : p.2 + p.1 + shift ≤ 13 := by omega
  by_cases h0 : p.2 + p.1 + shift = 0
  · simp only [h0, show ¬(1 ≤ 0 ∧ 0 ≤ 13) by omega, ↓reduceIte, zero_mul]
    symm; apply Finset.sum_eq_zero; intro k _
    simp [show (0 : ℕ) ≠ k.val + 1 by omega]
  · have hge1 : 1 ≤ p.2 + p.1 + shift := by omega
    have hk_lt : p.2 + p.1 + shift - 1 < 13 := by omega
    let k0 : Fin 13 := ⟨p.2 + p.1 + shift - 1, hk_lt⟩
    rw [if_pos ⟨hge1, hle13⟩, Finset.sum_eq_single k0]
    · simp only [k0, show p.2 + p.1 + shift - 1 + 1 = p.2 + p.1 + shift by omega, ↓reduceIte]; ring
    · intro k _ hne
      have hne' : p.2 + p.1 + shift ≠ k.val + 1 := fun h => hne (Fin.ext (by dsimp [k0]; omega))
      simp [hne']
    · intro h; exact absurd (Finset.mem_univ k0) h

-- 3-variable `Expr` evaluation to `P3Z` for `evalExpr3PolyT`
private def v3P3_SQT : ℕ → P3Z
  | 0 => MvPolynomial.X 0
  | 1 => MvPolynomial.X 1
  | 2 => MvPolynomial.X 2
  | _ => 0

private lemma uEval_uAdd_P3Z (t : P3Z) : ∀ a b, uEval poly3Ops (uAdd poly3Ops a b) t = uEval poly3Ops a t + uEval poly3Ops b t
  | [], b => by simp [uAdd, uEval, poly3Ops]
  | a :: as, [] => by simp [uAdd, uEval, poly3Ops]
  | a :: as, b :: bs => by simp only [uAdd, uEval, uEval_uAdd_P3Z t as bs]; dsimp only [poly3Ops]; ring

private lemma uEval_uNeg_P3Z (t : P3Z) (a : UPoly P3Z) : uEval poly3Ops (uNeg poly3Ops a) t = -uEval poly3Ops a t := by
  induction a with
  | nil => simp [uNeg, uEval, poly3Ops]
  | cons a as ih => simp only [uNeg, List.map_cons, uEval] at ih ⊢; rw [ih]; dsimp only [poly3Ops]; ring

private lemma uEval_uSub_P3Z (t : P3Z) : ∀ a b, uEval poly3Ops (uSub poly3Ops a b) t = uEval poly3Ops a t - uEval poly3Ops b t
  | [], b => by simp only [uSub, uEval_uNeg_P3Z, uEval]; dsimp only [poly3Ops]; ring
  | a :: as, [] => by simp [uSub, uEval, poly3Ops]
  | a :: as, b :: bs => by simp only [uSub, uEval, uEval_uSub_P3Z t as bs]; dsimp only [poly3Ops]; ring

private lemma uEval_uSc_P3Z (t c : P3Z) (a : UPoly P3Z) : uEval poly3Ops (uSc poly3Ops c a) t = c * uEval poly3Ops a t := by
  induction a with
  | nil => simp [uSc, uEval, poly3Ops]
  | cons a as ih => simp only [uSc, List.map_cons, uEval] at ih ⊢; rw [ih]; dsimp only [poly3Ops]; ring

private lemma uEval_uShift_P3Z (t : P3Z) (a : UPoly P3Z) :
    uEval poly3Ops (uShift poly3Ops a) t = t * uEval poly3Ops a t := by
  simp [uShift, uEval, poly3Ops]

private lemma uEval_uMul_P3Z (t : P3Z) : ∀ a b, uEval poly3Ops (uMul poly3Ops a b) t = uEval poly3Ops a t * uEval poly3Ops b t
  | [], b => by simp [uMul, uEval, poly3Ops]
  | a :: as, b => by
      simp only [uMul, uEval, uEval_uAdd_P3Z, uEval_uSc_P3Z, uEval_uShift_P3Z, uEval_uMul_P3Z t as b]
      dsimp only [poly3Ops]; ring

private lemma uEval_uMonomial_P3Z (t c : P3Z) : ∀ k, uEval poly3Ops (uMonomial poly3Ops k c) t = c * t ^ k
  | 0 => by simp [uMonomial, uEval, poly3Ops]
  | k + 1 => by simp only [uMonomial, uEval, uEval_uMonomial_P3Z t c k, pow_succ]; dsimp only [poly3Ops]; ring

private lemma uEval_uPow_P3Z (t : P3Z) (p : UPoly P3Z) :
    ∀ k, uEval poly3Ops (uPow poly3Ops p k) t = (uEval poly3Ops p t) ^ k
  | 0 => by simp [uPow, uEval, poly3Ops]
  | k + 1 => by simp only [uPow, uEval_uMul_P3Z, uEval_uPow_P3Z t p k, pow_succ]

private lemma uEval_sNeg_P3Z (t : P3Z) : ∀ a, uEval poly3Ops (sToU (sNeg poly3Ops a)) t = -uEval poly3Ops (sToU a) t
  | .sc a => by simp only [sNeg, sToU, uEval]; dsimp only [poly3Ops]; ring
  | .poly p => by simp only [sNeg, sToU, uEval_uNeg_P3Z]

private lemma uEval_sAdd_P3Z (t : P3Z) : ∀ a b,
    uEval poly3Ops (sToU (sAdd poly3Ops a b)) t = uEval poly3Ops (sToU a) t + uEval poly3Ops (sToU b) t
  | .sc a, .sc b => by simp only [sAdd, sToU, uEval]; dsimp only [poly3Ops]; ring
  | .sc a, .poly [] => by simp only [sAdd, sToU, uEval]; dsimp only [poly3Ops]; ring
  | .sc a, .poly (b :: bs) => by simp only [sAdd, sToU, uEval]; dsimp only [poly3Ops]; ring
  | .poly [], .sc b => by simp only [sAdd, sToU, uEval]; dsimp only [poly3Ops]; ring
  | .poly (a :: as), .sc b => by simp only [sAdd, sToU, uEval]; dsimp only [poly3Ops]; ring
  | .poly p, .poly q => by simp only [sAdd, sToU, uEval_uAdd_P3Z]

private lemma uEval_sSub_P3Z (t : P3Z) : ∀ a b,
    uEval poly3Ops (sToU (sSub poly3Ops a b)) t = uEval poly3Ops (sToU a) t - uEval poly3Ops (sToU b) t
  | .sc a, .sc b => by simp only [sSub, sToU, uEval]; dsimp only [poly3Ops]; ring
  | .sc a, .poly p => by simp only [sSub, sToU, uEval_uSub_P3Z]
  | .poly p, .sc b => by simp only [sSub, sToU, uEval_uSub_P3Z]
  | .poly p, .poly q => by simp only [sSub, sToU, uEval_uSub_P3Z]

private lemma uEval_sMul_P3Z (t : P3Z) : ∀ a b,
    uEval poly3Ops (sToU (sMul poly3Ops a b)) t = uEval poly3Ops (sToU a) t * uEval poly3Ops (sToU b) t
  | .sc a, .sc b => by simp only [sMul, sToU, uEval]; dsimp only [poly3Ops]; ring
  | .sc a, .poly p => by simp only [sMul, sToU, uEval_uSc_P3Z, uEval]; dsimp only [poly3Ops]; ring
  | .poly p, .sc b => by simp only [sMul, sToU, uEval_uSc_P3Z, uEval]; dsimp only [poly3Ops]; ring
  | .poly p, .poly q => by simp only [sMul, sToU, uEval_uMul_P3Z]

private lemma uEval_sShiftK_P3Z (t : P3Z) : ∀ k a,
    uEval poly3Ops (sToU (sShiftK poly3Ops k a)) t = uEval poly3Ops (sToU a) t * t ^ k
  | 0, a => by simp only [sShiftK, pow_zero, mul_one]
  | k + 1, .sc a => by
      simp only [sShiftK, sToU, uEval_uMonomial_P3Z, uEval]; dsimp only [poly3Ops]; rw [pow_succ]; ring
  | k + 1, .poly p => by
      change uEval poly3Ops (sToU (sShiftK poly3Ops k (.poly (uShift poly3Ops p)))) t = _
      rw [uEval_sShiftK_P3Z t k (.poly (uShift poly3Ops p)), sToU, sToU, uEval_uShift_P3Z, pow_succ]
      ring

private lemma uEval_evalExpr3SPoly_P3Z (nS nQ : ℕ) :
    ∀ e : Expr,
      uEval poly3Ops (sToU (evalExpr3SPoly poly3Ops (MvPolynomial.X 0) (MvPolynomial.X 1)
        (powList poly3Ops (MvPolynomial.X 0) nS (poly3Ops.ofInt 1))
        (powList poly3Ops (MvPolynomial.X 1) nQ (poly3Ops.ofInt 1)) e)) (MvPolynomial.X 2) =
      ringEval v3P3_SQT e
  | .num c => by simp [evalExpr3SPoly, sToU, uEval, poly3Ops, ringEval]
  | .natCast n => by simp [evalExpr3SPoly, sToU, uEval, poly3Ops, ringEval]
  | .intCast z => by simp [evalExpr3SPoly, sToU, uEval, poly3Ops, ringEval]
  | .var 0 => by simp [evalExpr3SPoly, sToU, uEval, poly3Ops, ringEval, v3P3_SQT]
  | .var 1 => by simp [evalExpr3SPoly, sToU, uEval, poly3Ops, ringEval, v3P3_SQT]
  | .var 2 => by simp [evalExpr3SPoly, sToU, uEval, poly3Ops, ringEval, v3P3_SQT]
  | .var (_ + 3) => by simp [evalExpr3SPoly, sToU, uEval, poly3Ops, ringEval, v3P3_SQT]
  | .neg a => by simp [evalExpr3SPoly, uEval_sNeg_P3Z, ringEval, uEval_evalExpr3SPoly_P3Z nS nQ a]
  | .add a b => by simp [evalExpr3SPoly, uEval_sAdd_P3Z, ringEval, uEval_evalExpr3SPoly_P3Z nS nQ a, uEval_evalExpr3SPoly_P3Z nS nQ b]
  | .sub a b => by simp [evalExpr3SPoly, uEval_sSub_P3Z, ringEval, uEval_evalExpr3SPoly_P3Z nS nQ a, uEval_evalExpr3SPoly_P3Z nS nQ b]
  | .mul a b => by
      have ha := uEval_evalExpr3SPoly_P3Z nS nQ a
      have hb := uEval_evalExpr3SPoly_P3Z nS nQ b
      dsimp only [evalExpr3SPoly, ringEval]
      split
      · simp [uEval_sShiftK_P3Z, ha, ringEval, v3P3_SQT]
      · simp [uEval_sShiftK_P3Z, ha, ringEval, v3P3_SQT]
      · simp [uEval_sMul_P3Z, ha, hb]
  | .pow a k => by
      have ha := uEval_evalExpr3SPoly_P3Z nS nQ a
      dsimp only [evalExpr3SPoly, ringEval]
      split
      · simp only [sToU, uEval, getPow_poly3_eq, ringEval, v3P3_SQT]; dsimp only [poly3Ops]; ring
      · simp only [sToU, uEval, getPow_poly3_eq, ringEval, v3P3_SQT]; dsimp only [poly3Ops]; ring
      · simp only [sToU, uEval_uMonomial_P3Z, ringEval, v3P3_SQT]; dsimp only [poly3Ops]; simp
      · rw [sToU, uEval_uPow_P3Z, ha]

private lemma uEval_evalExpr3PolyT_P3Z (nS nQ : ℕ) (e : Expr) :
    uEval poly3Ops (evalExpr3PolyT poly3Ops (MvPolynomial.X 0) (MvPolynomial.X 1)
      (powList poly3Ops (MvPolynomial.X 0) nS (poly3Ops.ofInt 1))
      (powList poly3Ops (MvPolynomial.X 1) nQ (poly3Ops.ofInt 1)) e) (MvPolynomial.X 2) =
    ringEval v3P3_SQT e :=
  uEval_evalExpr3SPoly_P3Z nS nQ e

private lemma evalP3K5_ringEval_SQT (e : Expr) :
    evalP3K5 (ringEval v3P3_SQT e) = ringEval vK5 e := by
  induction e with
  | num c => simp [evalP3K5, ringEval]
  | natCast n => simp [evalP3K5, ringEval]
  | intCast z => simp [evalP3K5, ringEval]
  | var j =>
      match j with
      | 0 => simp [evalP3K5, ringEval, v3P3_SQT, v3K5, vK5]
      | 1 => simp [evalP3K5, ringEval, v3P3_SQT, v3K5, vK5]
      | 2 => simp [evalP3K5, ringEval, v3P3_SQT, v3K5, vK5]
      | _ + 3 => simp [evalP3K5, ringEval, v3P3_SQT, vK5]
  | neg a ha => simp [ringEval] at ha ⊢; rw [ha]
  | add a b ha hb => simp [ringEval] at ha hb ⊢; rw [ha, hb]
  | sub a b ha hb => simp [ringEval] at ha hb ⊢; rw [ha, hb]
  | mul a b ha hb => simp [ringEval] at ha hb ⊢; rw [ha, hb]
  | pow a k ha => simp [ringEval] at ha ⊢; rw [ha]

-- Shift-invariant `numM_lead3` and degree-3 expansion of `numM` along `(a1 * z, b1 * z + b0)`
section NumMLead3
variable {R : Type*} [Field R] [CharZero R]

private def numM_lead3 (mi : Fin 10) (S Q T a1 b1 U V : R) : R :=
  let a2 := q1_a2 a1 b1 U V; let a1' := q1_a1 a1 b1 S Q U V; let a0' := q1_a0 S Q U V
  let b2 := q2_b2 a1 b1 U V; let b1' := q2_b1 a1 b1 S Q U V; let b0' := q2_b0 S Q U V
  let d21 := a2 * b1' - a1' * b2
  let d20 := a2 * b0' - a0' * b2
  let d10 := a1' * b0' - a0' * b1'
  (1 / 16) * match mi with
    | 0 => a1 ^ 2 * d10 - 2 * a1 * S * d20 + S ^ 2 * d21
    | 1 => a1 * b1 * d10 - (a1 * Q + b1 * S) * d20 + S * Q * d21
    | 2 => b1 ^ 2 * d10 - 2 * b1 * Q * d20 + Q ^ 2 * d21
    | 3 => T * (S * d21 - a1 * d20)
    | 4 => S * d21 - a1 * d20
    | 5 => T * (Q * d21 - b1 * d20)
    | 6 => Q * d21 - b1 * d20
    | 7 => T ^ 2 * d21
    | 8 => T * d21
    | 9 => d21

private lemma numM_isPoly3_core (mi : Fin 10) (S Q T a1 b1 b0 A2 A2_1 A2_0 A1 A1_0 A0 B2 B2_1 B2_0 B1 B1_0 B0 : R) :
    let d21' : R → R := fun z => (A2 * z ^ 2 + A2_1 * z + A2_0) * (B1 * z + B1_0) - (A1 * z + A1_0) * (B2 * z ^ 2 + B2_1 * z + B2_0)
    let d20' : R → R := fun z => (A2 * z ^ 2 + A2_1 * z + A2_0) * B0 - A0 * (B2 * z ^ 2 + B2_1 * z + B2_0)
    let d10' : R → R := fun z => (A1 * z + A1_0) * B0 - A0 * (B1 * z + B1_0)
    let D21 : R → R := d21'
    let D20 : R → R := fun z => d20' z - T * d21' z
    let D10 : R → R := fun z => d10' z - 2 * T * d20' z + T ^ 2 * d21' z
    let d21_0 := A2 * B1 - A1 * B2
    let d20_0 := A2 * B0 - A0 * B2
    let d10_0 := A1 * B0 - A0 * B1
    ∃ c2 c1 c0 : R, ∀ z : R,
      (1 / 16 : R) * (match mi with
        | 0 => (a1 * z) ^ 2 * D10 z - 2 * (a1 * z) * (S - a1 * z * T) * D20 z + (S - a1 * z * T) ^ 2 * D21 z
        | 1 => (a1 * z) * (b1 * z + b0) * D10 z - ((a1 * z) * (Q - (b1 * z + b0) * T) + (b1 * z + b0) * (S - a1 * z * T)) * D20 z +
                 (S - a1 * z * T) * (Q - (b1 * z + b0) * T) * D21 z
        | 2 => (b1 * z + b0) ^ 2 * D10 z - 2 * (b1 * z + b0) * (Q - (b1 * z + b0) * T) * D20 z + (Q - (b1 * z + b0) * T) ^ 2 * D21 z
        | 3 => (a1 * z) * D10 z - (S - a1 * z * T) * D20 z
        | 4 => -(a1 * z) * D20 z + (S - a1 * z * T) * D21 z
        | 5 => (b1 * z + b0) * D10 z - (Q - (b1 * z + b0) * T) * D20 z
        | 6 => -(b1 * z + b0) * D20 z + (Q - (b1 * z + b0) * T) * D21 z
        | 7 => D10 z
        | 8 => -D20 z
        | 9 => D21 z) =
      ((1 / 16 : R) * match mi with
        | 0 => a1 ^ 2 * d10_0 - 2 * a1 * S * d20_0 + S ^ 2 * d21_0
        | 1 => a1 * b1 * d10_0 - (a1 * Q + b1 * S) * d20_0 + S * Q * d21_0
        | 2 => b1 ^ 2 * d10_0 - 2 * b1 * Q * d20_0 + Q ^ 2 * d21_0
        | 3 => T * (S * d21_0 - a1 * d20_0)
        | 4 => S * d21_0 - a1 * d20_0
        | 5 => T * (Q * d21_0 - b1 * d20_0)
        | 6 => Q * d21_0 - b1 * d20_0
        | 7 => T ^ 2 * d21_0
        | 8 => T * d21_0
        | 9 => d21_0) * z ^ 3 + c2 * z ^ 2 + c1 * z + c0 := by
  intro d21' d20' d10' D21 D20 D10 d21_0 d20_0 d10_0
  have hlin (p2 p1 p0 q1 q0 r0 : R) :
      ∃ c2 c1 c0 : R, ∀ z : R,
        (1 / 16 : R) * ((p2 * z ^ 2 + p1 * z + p0) * d10' z - (q1 * z + q0) * d20' z + r0 * d21' z) =
        (1 / 16 : R) * (p2 * d10_0 - q1 * d20_0 + r0 * d21_0) * z ^ 3 + c2 * z ^ 2 + c1 * z + c0 := by
    refine ⟨(1 / 16) * (p2 * (A1_0 * B0 - A0 * B1_0) + p1 * d10_0 - q1 * (A2_1 * B0 - A0 * B2_1) -
              q0 * d20_0 + r0 * (A2 * B1_0 + A2_1 * B1 - A1 * B2_1 - A1_0 * B2)),
            (1 / 16) * (p1 * (A1_0 * B0 - A0 * B1_0) + p0 * d10_0 - q1 * (A2_0 * B0 - A0 * B2_0) -
              q0 * (A2_1 * B0 - A0 * B2_1) + r0 * (A2_1 * B1_0 + A2_0 * B1 - A1 * B2_0 - A1_0 * B2_1)),
            (1 / 16) * (p0 * (A1_0 * B0 - A0 * B1_0) - q0 * (A2_0 * B0 - A0 * B2_0) + r0 * (A2_0 * B1_0 - A1_0 * B2_0)),
            fun z => by dsimp only [d21', d20', d10', d21_0, d20_0, d10_0]; ring⟩
  fin_cases mi
  · obtain ⟨c2, c1, c0, h⟩ := hlin (a1 ^ 2) 0 0 (2 * a1 * S) 0 (S ^ 2)
    refine ⟨c2, c1, c0, fun z => ?_⟩; have hz := h z; dsimp only [D21, D20, D10] at hz ⊢
    generalize d21' z = u1 at hz ⊢; generalize d20' z = u2 at hz ⊢; generalize d10' z = u3 at hz ⊢
    generalize d21_0 = v1 at hz ⊢; generalize d20_0 = v2 at hz ⊢; generalize d10_0 = v3 at hz ⊢; linear_combination hz
  · obtain ⟨c2, c1, c0, h⟩ := hlin (a1 * b1) (a1 * b0) 0 (a1 * Q + b1 * S) (b0 * S) (S * Q)
    refine ⟨c2, c1, c0, fun z => ?_⟩; have hz := h z; dsimp only [D21, D20, D10] at hz ⊢
    generalize d21' z = u1 at hz ⊢; generalize d20' z = u2 at hz ⊢; generalize d10' z = u3 at hz ⊢
    generalize d21_0 = v1 at hz ⊢; generalize d20_0 = v2 at hz ⊢; generalize d10_0 = v3 at hz ⊢; linear_combination hz
  · obtain ⟨c2, c1, c0, h⟩ := hlin (b1 ^ 2) (2 * b1 * b0) (b0 ^ 2) (2 * b1 * Q) (2 * b0 * Q) (Q ^ 2)
    refine ⟨c2, c1, c0, fun z => ?_⟩; have hz := h z; dsimp only [D21, D20, D10] at hz ⊢
    generalize d21' z = u1 at hz ⊢; generalize d20' z = u2 at hz ⊢; generalize d10' z = u3 at hz ⊢
    generalize d21_0 = v1 at hz ⊢; generalize d20_0 = v2 at hz ⊢; generalize d10_0 = v3 at hz ⊢; linear_combination hz
  · obtain ⟨c2, c1, c0, h⟩ := hlin 0 a1 0 (a1 * T) S (S * T)
    refine ⟨c2, c1, c0, fun z => ?_⟩; have hz := h z; dsimp only [D21, D20, D10] at hz ⊢
    generalize d21' z = u1 at hz ⊢; generalize d20' z = u2 at hz ⊢; generalize d10' z = u3 at hz ⊢
    generalize d21_0 = v1 at hz ⊢; generalize d20_0 = v2 at hz ⊢; generalize d10_0 = v3 at hz ⊢; linear_combination hz
  · obtain ⟨c2, c1, c0, h⟩ := hlin 0 0 0 a1 0 S
    refine ⟨c2, c1, c0, fun z => ?_⟩; have hz := h z; dsimp only [D21, D20, D10] at hz ⊢
    generalize d21' z = u1 at hz ⊢; generalize d20' z = u2 at hz ⊢; generalize d10' z = u3 at hz ⊢
    generalize d21_0 = v1 at hz ⊢; generalize d20_0 = v2 at hz ⊢; generalize d10_0 = v3 at hz ⊢; linear_combination hz
  · obtain ⟨c2, c1, c0, h⟩ := hlin 0 b1 b0 (b1 * T) (b0 * T + Q) (Q * T)
    refine ⟨c2, c1, c0, fun z => ?_⟩; have hz := h z; dsimp only [D21, D20, D10] at hz ⊢
    generalize d21' z = u1 at hz ⊢; generalize d20' z = u2 at hz ⊢; generalize d10' z = u3 at hz ⊢
    generalize d21_0 = v1 at hz ⊢; generalize d20_0 = v2 at hz ⊢; generalize d10_0 = v3 at hz ⊢; linear_combination hz
  · obtain ⟨c2, c1, c0, h⟩ := hlin 0 0 0 b1 b0 Q
    refine ⟨c2, c1, c0, fun z => ?_⟩; have hz := h z; dsimp only [D21, D20, D10] at hz ⊢
    generalize d21' z = u1 at hz ⊢; generalize d20' z = u2 at hz ⊢; generalize d10' z = u3 at hz ⊢
    generalize d21_0 = v1 at hz ⊢; generalize d20_0 = v2 at hz ⊢; generalize d10_0 = v3 at hz ⊢; linear_combination hz
  · obtain ⟨c2, c1, c0, h⟩ := hlin 0 0 1 0 (2 * T) (T ^ 2)
    refine ⟨c2, c1, c0, fun z => ?_⟩; have hz := h z; dsimp only [D21, D20, D10] at hz ⊢
    generalize d21' z = u1 at hz ⊢; generalize d20' z = u2 at hz ⊢; generalize d10' z = u3 at hz ⊢
    generalize d21_0 = v1 at hz ⊢; generalize d20_0 = v2 at hz ⊢; generalize d10_0 = v3 at hz ⊢; linear_combination hz
  · obtain ⟨c2, c1, c0, h⟩ := hlin 0 0 0 0 1 T
    refine ⟨c2, c1, c0, fun z => ?_⟩; have hz := h z; dsimp only [D21, D20, D10] at hz ⊢
    generalize d21' z = u1 at hz ⊢; generalize d20' z = u2 at hz ⊢; generalize d10' z = u3 at hz ⊢
    generalize d21_0 = v1 at hz ⊢; generalize d20_0 = v2 at hz ⊢; generalize d10_0 = v3 at hz ⊢; linear_combination hz
  · obtain ⟨c2, c1, c0, h⟩ := hlin 0 0 0 0 0 1
    refine ⟨c2, c1, c0, fun z => ?_⟩; have hz := h z; dsimp only [D21, D20, D10] at hz ⊢
    generalize d21' z = u1 at hz ⊢; generalize d20' z = u2 at hz ⊢; generalize d10' z = u3 at hz ⊢
    generalize d21_0 = v1 at hz ⊢; generalize d20_0 = v2 at hz ⊢; generalize d10_0 = v3 at hz ⊢; linear_combination hz

private lemma numM_isPoly3 (mi : Fin 10) (S Q T a1 b1 b0 U V : R) :
    ∃ c2 c1 c0 : R, ∀ z : R,
      numM mi (a1 * z) (b1 * z + b0) (S - (a1 * z) * T) (Q - (b1 * z + b0) * T) U V =
        numM_lead3 mi S Q T a1 b1 U V * z ^ 3 + c2 * z ^ 2 + c1 * z + c0 := by
  set A2 := q1_a2 a1 b1 U V with hA2; set A2_1 := q1_a1 a1 b1 0 b0 U V; set A2_0 := q1_a0 0 b0 U V
  set A1 := q1_a1 a1 b1 S Q U V with hA1; set A1_0 := q1_a1 0 b0 S Q U V; set A0 := q1_a0 S Q U V with hA0
  set B2 := q2_b2 a1 b1 U V with hB2
  set B2_1 := dH_dQ a1 (b1 + b0) 0 U V - dH_dQ a1 b1 0 U V - dH_dQ 0 b0 0 U V
  set B2_0 := q2_b2 0 b0 U V
  set B1 := q2_b1 a1 b1 S Q U V with hB1; set B1_0 := q2_b1 0 b0 S Q U V; set B0 := q2_b0 S Q U V with hB0
  have ha2 (z : R) : q1_a2 (a1 * z) (b1 * z + b0) U V = A2 * z ^ 2 + A2_1 * z + A2_0 := by
    simp only [A2, A2_1, A2_0, q1_a2, q1_a1, q1_a0, dH_dS]; ring
  have ha1 (z : R) : q1_a1 (a1 * z) (b1 * z + b0) (S - a1 * z * T) (Q - (b1 * z + b0) * T) U V =
      (A1 * z + A1_0) - 2 * T * (A2 * z ^ 2 + A2_1 * z + A2_0) := by
    simp only [A2, A2_1, A2_0, A1, A1_0, q1_a2, q1_a1, q1_a0, dH_dS]; ring
  have ha0 (z : R) : q1_a0 (S - a1 * z * T) (Q - (b1 * z + b0) * T) U V =
      A0 - T * (A1 * z + A1_0) + T ^ 2 * (A2 * z ^ 2 + A2_1 * z + A2_0) := by
    simp only [A2, A2_1, A2_0, A1, A1_0, A0, q1_a2, q1_a1, q1_a0, dH_dS]; ring
  have hb2 (z : R) : q2_b2 (a1 * z) (b1 * z + b0) U V = B2 * z ^ 2 + B2_1 * z + B2_0 := by
    simp only [B2, B2_1, B2_0, q2_b2, dH_dQ]; ring
  have hb1 (z : R) : q2_b1 (a1 * z) (b1 * z + b0) (S - a1 * z * T) (Q - (b1 * z + b0) * T) U V =
      (B1 * z + B1_0) - 2 * T * (B2 * z ^ 2 + B2_1 * z + B2_0) := by
    simp only [B2, B2_1, B2_0, B1, B1_0, q2_b2, q2_b1, dH_dQ]; ring
  have hb0 (z : R) : q2_b0 (S - a1 * z * T) (Q - (b1 * z + b0) * T) U V =
      B0 - T * (B1 * z + B1_0) + T ^ 2 * (B2 * z ^ 2 + B2_1 * z + B2_0) := by
    simp only [B2, B2_1, B2_0, B1, B1_0, B0, q2_b2, q2_b1, q2_b0, dH_dQ]; ring
  have hshift (z : R) :
      let a2 := q1_a2 (a1 * z) (b1 * z + b0) U V
      let a1_ := q1_a1 (a1 * z) (b1 * z + b0) (S - a1 * z * T) (Q - (b1 * z + b0) * T) U V
      let a0_ := q1_a0 (S - a1 * z * T) (Q - (b1 * z + b0) * T) U V
      let b2 := q2_b2 (a1 * z) (b1 * z + b0) U V
      let b1_ := q2_b1 (a1 * z) (b1 * z + b0) (S - a1 * z * T) (Q - (b1 * z + b0) * T) U V
      let b0_ := q2_b0 (S - a1 * z * T) (Q - (b1 * z + b0) * T) U V
      (a2 * b1_ - a1_ * b2 = (A2 * z ^ 2 + A2_1 * z + A2_0) * (B1 * z + B1_0) - (A1 * z + A1_0) * (B2 * z ^ 2 + B2_1 * z + B2_0)) ∧
      (a2 * b0_ - a0_ * b2 = ((A2 * z ^ 2 + A2_1 * z + A2_0) * B0 - A0 * (B2 * z ^ 2 + B2_1 * z + B2_0)) -
        T * ((A2 * z ^ 2 + A2_1 * z + A2_0) * (B1 * z + B1_0) - (A1 * z + A1_0) * (B2 * z ^ 2 + B2_1 * z + B2_0))) ∧
      (a1_ * b0_ - a0_ * b1_ = ((A1 * z + A1_0) * B0 - A0 * (B1 * z + B1_0)) -
        2 * T * ((A2 * z ^ 2 + A2_1 * z + A2_0) * B0 - A0 * (B2 * z ^ 2 + B2_1 * z + B2_0)) +
        T ^ 2 * ((A2 * z ^ 2 + A2_1 * z + A2_0) * (B1 * z + B1_0) - (A1 * z + A1_0) * (B2 * z ^ 2 + B2_1 * z + B2_0))) := by
    simp only [ha2, ha1, ha0, hb2, hb1, hb0]
    generalize (A2 * z ^ 2 + A2_1 * z + A2_0) = pA2; generalize (A1 * z + A1_0) = pA1; generalize A0 = pA0
    generalize (B2 * z ^ 2 + B2_1 * z + B2_0) = pB2; generalize (B1 * z + B1_0) = pB1; generalize B0 = pB0
    exact ⟨by ring, by ring, by ring⟩
  obtain ⟨c2, c1, c0, h⟩ := numM_isPoly3_core mi S Q T a1 b1 b0 A2 A2_1 A2_0 A1 A1_0 A0 B2 B2_1 B2_0 B1 B1_0 B0
  refine ⟨c2, c1, c0, fun z => ?_⟩
  have hz := h z
  have hs := hshift z
  fin_cases mi <;> (
    simp only [numM, numM_lead3, hs.1, hs.2.1, hs.2.2, ← hA2, ← hA1, ← hA0, ← hB2, ← hB1, ← hB0,
      zero_mul, one_mul, sub_zero, add_zero, zero_sub, zero_add, neg_mul] at hz ⊢
    exact hz)

private lemma numM_lead3_scale (mi : Fin 10) (S Q T a1 b1 U V lam : R) :
    numM_lead3 mi S Q T (lam * a1) (lam * b1) U V =
      lam ^ 3 * V ^ 2 * numM_lead3 mi S Q T a1 b1 U 1 := by
  have ha2 : q1_a2 (lam * a1) (lam * b1) U V = lam ^ 2 * V * q1_a2 a1 b1 U 1 := by
    simp only [q1_a2, dH_dS]; ring
  have ha1 : q1_a1 (lam * a1) (lam * b1) S Q U V = lam * V * q1_a1 a1 b1 S Q U 1 := by
    simp only [q1_a1, dH_dS]; ring
  have ha0 : q1_a0 S Q U V = V * q1_a0 S Q U 1 := by
    simp only [q1_a0, dH_dS]; ring
  have hb2 : q2_b2 (lam * a1) (lam * b1) U V = lam ^ 2 * V * q2_b2 a1 b1 U 1 := by
    simp only [q2_b2, dH_dQ]; ring
  have hb1 : q2_b1 (lam * a1) (lam * b1) S Q U V = lam * V * q2_b1 a1 b1 S Q U 1 := by
    simp only [q2_b1, dH_dQ]; ring
  have hb0 : q2_b0 S Q U V = V * q2_b0 S Q U 1 := by
    simp only [q2_b0, dH_dQ]; ring
  simp only [numM_lead3, ha2, ha1, ha0, hb2, hb1, hb0]
  generalize q1_a2 a1 b1 U 1 = x2; generalize q1_a1 a1 b1 S Q U 1 = x1; generalize q1_a0 S Q U 1 = x0
  generalize q2_b2 a1 b1 U 1 = y2; generalize q2_b1 a1 b1 S Q U 1 = y1; generalize q2_b0 S Q U 1 = y0
  fin_cases mi <;> ring

end NumMLead3

-- Exact integer scaling constants for the `PolyOps` cached `Q5` residue engine
private def L_all_A : ℤ := 235267436250
private def M_A_int : ℤ := L_all_A * 16 * 45927 * 567 ^ 4
private def M_mid_int : ℤ := 2250423
private def M_R_int : ℤ := M_A_int * 1701 * M_mid_int
private def C_RHS_int : ℤ := -5438812994401448072650932000000000000000

private structure ACache (α : Type*) where
  ca_p : UPoly α
  cb_p : UPoly α
  A0U_t0 : UPoly α
  A0U_t1 : UPoly α
  A0V_t0 : UPoly α
  A0V_t1 : UPoly α
  A0V_t2 : UPoly α
  AY2_t0 : UPoly α
  AY2_t1 : UPoly α
  AY3_t0 : UPoly α
  AY3_t1 : UPoly α
  AX2_t0 : UPoly α
  AX2_t1 : UPoly α
  AX2_t2 : UPoly α
  Bv_SQ : UPoly α

private def evalACache {α : Type*} (o : PolyOps α) (S Q : α) : ACache α :=
  letB (o.mul S S) fun S2 =>
  letB (o.mul S Q) fun SQ =>
  letB (o.mul Q Q) fun Q2 =>
  letB (o.mul S2 S) fun S3 =>
  letB (o.mul Q2 Q) fun Q3 =>
  letB (o.sub S (o.mul (o.ofInt 3) Q)) fun Sm3Q =>
  letB (o.mul Sm3Q Sm3Q) fun Sm3Q2 =>
  letB (o.sub (o.mul (o.ofInt 5) S) (o.mul (o.ofInt 9) Q)) fun A5 =>
  letB (o.mul (o.ofInt (-175)) (o.mul A5 (o.sub (o.mul (o.ofInt 5) S) (o.mul (o.ofInt 3) Q)))) fun ca0 =>
  letB (o.mul (o.ofInt 7) (o.add (o.sub (o.mul (o.ofInt 143) S2) (o.mul (o.ofInt 552) SQ)) (o.mul (o.ofInt 468) Q2))) fun ca1 =>
  letB (o.mul (o.ofInt (-28)) Sm3Q2) fun ca2 =>
  letB [ca0, ca1, ca2] fun ca_p =>
  letB (o.mul (o.ofInt 1050) (o.mul S A5)) fun cb0 =>
  letB (o.add (o.add (o.mul (o.ofInt 21) (o.sub (o.add (o.mul (o.ofInt (-92)) S2) (o.mul (o.ofInt 312) SQ))
      (o.mul (o.ofInt 198) Q2))) (o.mul (o.ofInt 810) Q)) (o.ofInt 810)) fun cb1 =>
  letB (o.mul (o.ofInt 84) Sm3Q2) fun cb2 =>
  letB [cb0, cb1, cb2] fun cb_p =>
  letB (uNeg o ca_p) fun b_p =>
  letB [o.sub cb0 (o.mul (o.ofInt 3) (o.neg ca0)), o.sub cb1 (o.mul (o.ofInt 3) (o.neg ca1))] fun am3b_p =>
  letB (uSub o (uSc o (o.ofInt 5) cb_p) (uSc o (o.ofInt 9) b_p)) fun a5m9b =>
  letB (uSub o (uSc o (o.ofInt 15) cb_p) (uSc o (o.ofInt 9) b_p)) fun a15m9b =>
  letB (uMul o cb_p cb_p) fun aa =>
  letB (uMul o cb_p b_p) fun ab =>
  letB (uMul o b_p b_p) fun bb =>
  letB (uMul o am3b_p am3b_p) fun am3b2 =>
  letB (uAdd o (uAdd o (uSc o (o.ofInt (-25)) (uMul o a5m9b a15m9b))
      (uShift o (uAdd o (uSub o (uSc o (o.ofInt 429) aa) (uSc o (o.ofInt 1656) ab)) (uSc o (o.ofInt 1404) bb))))
      (uShift o (uShift o (uSc o (o.ofInt (-12)) am3b2)))) fun A2 =>
  letB (uAdd o (uAdd o (uSc o (o.ofInt 50) (uMul o cb_p a5m9b))
      (uShift o (uSub o (uAdd o (uSc o (o.ofInt (-92)) aa) (uSc o (o.ofInt 312) ab)) (uSc o (o.ofInt 198) bb))))
      (uShift o (uShift o (uSc o (o.ofInt 4) am3b2)))) fun B2 =>
  letB (o.sub (o.mul (o.ofInt 15) S) (o.mul (o.ofInt 9) Q)) fun S15m9Q =>
  letB (uAdd o (uSc o S b_p) (uSc o Q cb_p)) fun sbqa =>
  letB (uAdd o (uAdd o (uSc o (o.ofInt (-25)) (uAdd o (uSc o S15m9Q a5m9b) (uSc o A5 a15m9b)))
      (uShift o (uAdd o (uSub o (uSc o (o.mul (o.ofInt 858) S) cb_p) (uSc o (o.ofInt 1656) sbqa))
        (uSc o (o.mul (o.ofInt 2808) Q) b_p))))
      (uShift o (uShift o (uSc o (o.mul (o.ofInt (-24)) Sm3Q) am3b_p)))) fun A1 =>
  letB (uAdd o (uAdd o (uSc o (o.ofInt 350) (uSub o (uSc o (o.sub (o.mul (o.ofInt 10) S) (o.mul (o.ofInt 9) Q)) cb_p)
      (uSc o (o.mul (o.ofInt 9) S) b_p)))
      (uShift o (uAdd o (uSc o (o.ofInt 7) (uSub o (uAdd o (uSc o (o.mul (o.ofInt (-184)) S) cb_p)
        (uSc o (o.ofInt 312) sbqa)) (uSc o (o.mul (o.ofInt 396) Q) b_p))) (uSc o (o.ofInt 270) b_p))))
      (uShift o (uShift o (uSc o (o.mul (o.ofInt 56) Sm3Q) am3b_p)))) fun B1 =>
  letB (uSc o (o.ofInt 567) (uSub o (uMul o A2 B1) (uSc o (o.ofInt 7) (uMul o A1 B2)))) fun D21 =>
  letB (uSub o (uSc o (o.ofInt 189) (uMul o A2 cb_p)) (uSc o (o.ofInt 1701) (uMul o ca_p B2))) fun D20 =>
  letB (uSub o (uSc o (o.ofInt 189) (uMul o A1 cb_p)) (uSc o (o.ofInt 243) (uMul o ca_p B1))) fun D10 =>
  letB (uAdd o (uSub o (uMul o aa D10) (uSc o (o.mul (o.ofInt 2) S) (uMul o cb_p D20))) (uSc o S2 D21)) fun m0 =>
  letB (uAdd o (uSub o (uMul o ab D10) (uMul o sbqa D20)) (uSc o SQ D21)) fun m1 =>
  letB (uAdd o (uSub o (uMul o bb D10) (uSc o (o.mul (o.ofInt 2) Q) (uMul o b_p D20))) (uSc o Q2 D21)) fun m2 =>
  letB (uSub o (uSc o S D21) (uMul o cb_p D20)) fun m4 =>
  letB (uSub o (uSc o Q D21) (uMul o b_p D20)) fun m6 =>
  letB (uSub o (uSc o (o.ofInt 5) m0) (uSc o (o.ofInt 9) m1)) fun l01 =>
  letB (uSub o (uSc o (o.ofInt 5) m1) (uSc o (o.ofInt 9) m2)) fun l12 =>
  letB (uSub o (uSc o (o.ofInt 5) m4) (uSc o (o.ofInt 9) m6)) fun l46 =>
  letB (uSc o (o.ofInt (-100 * 968178750)) l46) fun AY2_base =>
  letB (o.mul (o.ofInt (-175)) (o.mul S (o.mul A5 A5))) fun Bv0_1701 =>
  letB (o.sub (o.add (o.sub (o.mul (o.ofInt 143) S3) (o.mul (o.ofInt 828) (o.mul S2 Q)))
      (o.mul (o.ofInt 1404) (o.mul S Q2))) (o.mul (o.ofInt 594) Q3)) fun Bv1_243_S =>
  letB (o.add (o.add (o.mul (o.ofInt 7) Bv1_243_S) (o.mul (o.ofInt 1215) Q2)) (o.mul (o.ofInt 2430) Q)) fun Bv1_SQ_1701 =>
  letB (o.mul (o.ofInt (-28)) (o.mul Sm3Q2 Sm3Q)) fun Bv2_1701 =>
  ⟨ca_p, cb_p,
   uAdd o (uAdd o (uSc o (o.ofInt (-19708 * 187110)) l01) (uSc o (o.ofInt (1472 * 187110)) l12))
     (uSc o (o.ofInt (188 * 116181450)) l46),
   uSc o (o.ofInt (-16 * 322726250)) l46,
   uAdd o (uAdd o (uSc o (o.ofInt (-892 * (-9) * 64545250)) m4)
     (uSc o (o.ofInt (40 * (-9) * 2904536250)) m6)) (uSc o (o.ofInt (392 * (-9) * 19646550)) D21),
   uAdd o (uAdd o (uAdd o (uSc o (o.ofInt (-892 * 5 * 64545250)) m4)
     (uSc o (o.ofInt (40 * 5 * 2904536250)) m6)) (uSc o (o.ofInt (-112 * (-9) * 98232750)) D21))
     (uSc o (o.ofInt (392 * 5 * 19646550)) D21),
   uSc o (o.ofInt (-112 * 5 * 98232750)) D21,
   uSc o (o.ofInt (-9)) AY2_base,
   uSc o (o.ofInt 5) AY2_base,
   uAdd o (uSub o (uAdd o (uSc o (o.ofInt (-907876 * 6930)) l01) (uSc o (o.ofInt (2258324 * 6930)) l12))
     (uSc o (o.ofInt (64 * 348544350)) l46))
     (uShift o (uAdd o (uSc o (o.ofInt (-123236 * 126)) (uSub o (uAdd o (uSc o (o.ofInt 77) m0) (uSc o (o.ofInt 2790) m6)) (uSc o (o.ofInt 5904) D21)))
       (uSc o (o.ofInt (492944 * 9)) (uSub o (uAdd o (uSc o (o.ofInt 770) m1) (uSc o (o.ofInt 9270) m6)) (uSc o (o.ofInt 21159) D21))))),
   uAdd o (uSc o (o.ofInt (8 * 968178750)) l46)
     (uShift o (uAdd o (uSc o (o.ofInt (-123236 * 126)) (uSc o (o.ofInt 2156) D21))
       (uSc o (o.ofInt (492944 * 9)) (uSc o (o.ofInt 7546) D21)))),
   uShift o (uAdd o (uSc o (o.ofInt (-8 * (-9) * 580907250)) m4) (uSc o (o.ofInt (6916 * (-9) * 6548850)) D21)),
   uShift o (uAdd o (uAdd o (uSc o (o.ofInt (-8 * 5 * 580907250)) m4)
     (uSc o (o.ofInt (-476 * (-9) * 32744250)) D21)) (uSc o (o.ofInt (6916 * 5 * 6548850)) D21)),
   uShift o (uSc o (o.ofInt (-476 * 5 * 32744250)) D21),
   [Bv0_1701, Bv1_SQ_1701, Bv2_1701]⟩

private structure GeomSQ (α : Type*) where
  H0_7_SQ : α
  S2 : α
  DX2 : BivL α
  dDX2_dS : BivL α
  dDX2_dQ : BivL α
  dDX2_dx : BivL α
  dF5_0 : BivL α
  dF5_1 : BivL α
  dF5_3 : BivL α
  LX_27 : UBivL α
  dLX_0 : UBivL α
  dLX_1 : UBivL α
  dLX_3 : UBivL α
  PX_0 : UBivL α
  PX_1 : UBivL α
  PX_3 : UBivL α
  A1_1_27 : UPoly α
  qC_63 : UPoly α
  qEx_63 : UPoly α

private def evalGeomSQ {α : Type*} (o : PolyOps α) (S Q : α) : GeomSQ α :=
  letB (o.mul S S) fun S2 =>
  letB (o.mul S Q) fun SQ =>
  letB (o.mul Q Q) fun Q2 =>
  letB (o.mul S2 S) fun S3 =>
  letB (o.mul S2 S2) fun S4 =>
  letB (o.mul Q2 Q) fun Q3 =>
  letB (o.mul Q2 Q2) fun Q4 =>
  letB (o.sub S (o.mul (o.ofInt 3) Q)) fun Sm3Q =>
  letB (o.sub (o.mul (o.ofInt 5) S) (o.mul (o.ofInt 9) Q)) fun A5 =>
  letB (o.sub (o.sub (o.add (o.mul (o.ofInt (-2)) S3) (o.mul (o.ofInt 6) (o.mul S2 Q)))
      (o.mul (o.ofInt 3) (o.mul S Q2))) (o.mul (o.ofInt 2) Q3)) fun pS =>
  letB (o.add (o.add (o.mul (o.ofInt 7) pS) (o.mul (o.ofInt 5) Q2)) (o.mul (o.ofInt 10) Q)) fun H0_7_SQ =>
  letB ([[o.add (o.neg S) (o.mul (o.ofInt 2) Q)], [o.ofInt 1]] : BivL α) fun u3 =>
  letB (bivMul o u3 u3) fun u3_2 =>
  letB (bivConst (o.sub (o.mul (o.ofInt 25) S) (o.mul (o.ofInt 45) Q))) fun LX0 =>
  letB ([[o.sub (o.mul (o.ofInt 45) Q) (o.mul (o.ofInt 25) S)], [o.ofInt 27]] : BivL α) fun LX1 =>
  letB ([LX0, LX1] : UBivL α) fun LX_27 =>
  letB ([bivConst (o.ofInt 25), bivConst (o.ofInt (-25))] : UBivL α) fun dLX_0 =>
  letB ([bivConst (o.ofInt (-45)), bivConst (o.ofInt 45)] : UBivL α) fun dLX_1 =>
  letB ([[], bivConst (o.ofInt 27)] : UBivL α) fun dLX_3 =>
  letB (o.mul (o.ofInt 2) S) fun S2x =>
  ⟨H0_7_SQ, S2,
   bivAdd o (bivConst (o.sub (o.mul S Q2) (o.mul (o.ofInt 4) Q3)))
     (bivAdd o (bivSc o (o.sub (o.mul (o.ofInt 18) SQ) (o.mul (o.ofInt 4) S2)) u3)
       (bivSc o (o.mul (o.ofInt (-27)) S) u3_2)),
   bivAdd o (bivConst (o.sub (o.add Q2 (o.mul (o.ofInt 4) S2)) (o.mul (o.ofInt 18) SQ)))
     (bivAdd o (bivSc o (o.add (o.mul (o.ofInt 46) S) (o.mul (o.ofInt 18) Q)) u3)
       (bivSc o (o.ofInt (-27)) u3_2)),
   bivAdd o (bivConst (o.sub (o.add (o.mul (o.ofInt (-8)) S2) (o.mul (o.ofInt 38) SQ)) (o.mul (o.ofInt 12) Q2)))
     (bivSc o (o.mul (o.ofInt (-90)) S) u3),
   bivAdd o (bivConst (o.add (o.mul (o.ofInt (-4)) S2) (o.mul (o.ofInt 18) SQ)))
     (bivSc o (o.mul (o.ofInt (-54)) S) u3),
   [[o.mul (o.ofInt 7) (o.sub (o.add (o.mul (o.ofInt (-6)) S2) (o.mul (o.ofInt 12) SQ)) (o.mul (o.ofInt 3) Q2))], [], [o.ofInt 21]],
   [[o.add (o.add (o.mul (o.ofInt 7) (o.sub (o.sub (o.mul (o.ofInt 6) S2) (o.mul (o.ofInt 6) SQ)) (o.mul (o.ofInt 6) Q2)))
     (o.mul (o.ofInt 10) Q)) (o.ofInt 10)]],
   [[], [o.mul (o.ofInt 42) S]],
   LX_27, dLX_0, dLX_1, dLX_3,
   ubAdd o (ubSc o S2x dLX_0) LX_27, ubSc o S2x dLX_1, ubSc o S2x dLX_3,
   [o.mul (o.ofInt 25) (o.mul S (o.mul A5 A5)), o.mul (o.ofInt (-4)) (o.mul (o.mul Sm3Q Sm3Q) Sm3Q)],
   [o.add (o.add (o.add (o.add (o.add (o.add (o.add (o.add (o.add (o.add
      (o.mul (o.ofInt (-5250)) S4) (o.mul (o.ofInt 30450) (o.mul S3 Q)))
      (o.mul (o.ofInt (-64050)) (o.mul S2 Q2))) (o.mul (o.ofInt 63000) (o.mul S Q3)))
      (o.mul (o.ofInt (-28350)) Q4)) (o.mul (o.ofInt 6250) (o.mul S2 Q)))
      (o.mul (o.ofInt (-15000)) (o.mul S Q2))) (o.mul (o.ofInt 6750) Q3))
      (o.mul (o.ofInt 6250) S2)) (o.mul (o.ofInt (-15000)) SQ)) (o.mul (o.ofInt 6750) Q2),
    o.add (o.add (o.add (o.add (o.add (o.add (o.add (o.add (o.add (o.add
      (o.mul (o.ofInt 336) S4) (o.mul (o.ofInt (-2856)) (o.mul S3 Q)))
      (o.mul (o.ofInt 8484) (o.mul S2 Q2))) (o.mul (o.ofInt (-10080)) (o.mul S Q3)))
      (o.mul (o.ofInt 3780) Q4)) (o.mul (o.ofInt (-40)) (o.mul S2 Q)))
      (o.mul (o.ofInt 240) (o.mul S Q2))) (o.mul (o.ofInt (-360)) Q3))
      (o.mul (o.ofInt (-40)) S2)) (o.mul (o.ofInt 240) SQ)) (o.mul (o.ofInt (-360)) Q2)],
   [o.add (o.add (o.add (o.add (o.add (o.add (o.add
      (o.mul (o.ofInt 6090) S3) (o.mul (o.ofInt (-25620)) (o.mul S2 Q)))
      (o.mul (o.ofInt 34650) (o.mul S Q2))) (o.mul (o.ofInt (-20790)) Q3))
      (o.mul (o.ofInt (-6750)) SQ)) (o.mul (o.ofInt 4050) Q2))
      (o.mul (o.ofInt (-6750)) S)) (o.mul (o.ofInt 4050) Q),
    o.add (o.add (o.add
      (o.mul (o.ofInt (-420)) S3) (o.mul (o.ofInt 2940) (o.mul S2 Q)))
      (o.mul (o.ofInt (-6300)) (o.mul S Q2))) (o.mul (o.ofInt 3780) Q3)]⟩

private structure SQCache (α : Type*) where
  W : UPoly α
  D_div_L2 : α
  ac : ACache α
  gsq : GeomSQ α
  d_A0U_t0 : UPoly α
  d_A0U_t1 : UPoly α
  d_A0V_t0 : UPoly α
  d_A0V_t1 : UPoly α
  d_A0V_t2 : UPoly α
  d_A0V_U_t0 : UPoly α
  d_A0V_U_t1 : UPoly α
  d_A0V_U_t2 : UPoly α
  d_A0VBv_t0 : UPoly α
  d_A0VBv_t1 : UPoly α
  d_A0VBv_t2 : UPoly α
  d_AY2_t0 : UPoly α
  d_AY2_t1 : UPoly α
  d_AY3_t0 : UPoly α
  d_AY3_t1 : UPoly α
  d_AX2_t0 : UPoly α
  d_AX2_t1 : UPoly α
  d_AX2_t2 : UPoly α
  RQ5_T : List (List (UPoly α))

private def evalSQCache {α : Type*} (o : PolyOps α) (S Q : α) : SQCache α :=
  letB (powList o S 30 (o.ofInt 1)) fun pS =>
  letB (powList o Q 37 (o.ofInt 1)) fun pQ =>
  letB (o.add (o.mul (o.ofInt (-5)) S) (o.mul (o.ofInt 9) Q)) fun f2 =>
  letB (o.add (o.neg S) (o.mul (o.ofInt 3) Q)) fun f3 =>
  letB (o.add (o.add (o.ofInt (-45)) (o.mul (o.ofInt (-77)) S)) (o.mul (o.ofInt 210) Q)) fun f4 =>
  letB (o.mul f2 f2) fun f2_2 =>
  letB (o.mul f2_2 f2_2) fun f2_4 =>
  letB (o.mul f2_4 f2_2) fun f2_6 =>
  letB (o.mul f2_6 f2) fun f2_7 =>
  letB (o.mul (o.mul f3 f3) f3) fun f3_3 =>
  letB (o.mul f3_3 f3_3) fun f3_6 =>
  letB (o.mul f3_6 f3_3) fun f3_9 =>
  letB (o.mul f3_9 f3_3) fun f3_12 =>
  letB (o.mul f3_12 f3) fun f3_13 =>
  letB (o.mul f4 f4) fun f4_2 =>
  letB (o.mul f3_13 f4_2) fun d0 =>
  letB (o.mul (o.mul (o.mul S f2_2) f3_13) f4_2) fun d1 =>
  letB (o.mul (o.mul (o.mul S f2_4) f3_13) f4_2) fun d2 =>
  letB (o.mul (o.mul (o.mul S f2_6) f3_13) f4_2) fun d3 =>
  letB (o.mul (o.mul (o.mul S f2_7) f3_13) f4_2) fun d4 =>
  letB (o.mul (o.mul (o.mul S f2_7) f3_12) f4_2) fun d8 =>
  letB (o.mul (o.mul (o.mul S f2_7) f3_9) f4_2) fun d9 =>
  letB (o.mul (o.mul (o.mul S f2_7) f3_6) f4_2) fun d10 =>
  letB (o.mul (o.mul (o.mul S f2_7) f3_3) f4) fun d11 =>
  letB (o.mul S f2_7) fun d12 =>
  letB ([o.mul (o.ofInt (N_k_mul 0)) (o.mul d0 (evalExpr2 o S Q pS pQ (N_k_expr 0))),
         o.mul (o.ofInt (N_k_mul 1)) (o.mul d1 (evalExpr2 o S Q pS pQ (N_k_expr 1))),
         o.mul (o.ofInt (N_k_mul 2)) (o.mul d2 (evalExpr2 o S Q pS pQ (N_k_expr 2))),
         o.mul (o.ofInt (N_k_mul 3)) (o.mul d3 (evalExpr2 o S Q pS pQ (N_k_expr 3))),
         o.mul (o.ofInt (N_k_mul 4)) (o.mul d4 (evalExpr2 o S Q pS pQ (N_k_expr 4))),
         o.mul (o.ofInt (N_k_mul 5)) (o.mul d4 (evalExpr2 o S Q pS pQ (N_k_expr 5))),
         o.mul (o.ofInt (N_k_mul 6)) (o.mul d4 (evalExpr2 o S Q pS pQ (N_k_expr 6))),
         o.mul (o.ofInt (N_k_mul 7)) (o.mul d4 (evalExpr2 o S Q pS pQ (N_k_expr 7))),
         o.mul (o.ofInt (N_k_mul 8)) (o.mul d8 (evalExpr2 o S Q pS pQ (N_k_expr 8))),
         o.mul (o.ofInt (N_k_mul 9)) (o.mul d9 (evalExpr2 o S Q pS pQ (N_k_expr 9))),
         o.mul (o.ofInt (N_k_mul 10)) (o.mul d10 (evalExpr2 o S Q pS pQ (N_k_expr 10))),
         o.mul (o.ofInt (N_k_mul 11)) (o.mul d11 (evalExpr2 o S Q pS pQ (N_k_expr 11))),
         o.mul (o.ofInt (N_k_mul 12)) (o.mul d12 (evalExpr2 o S Q pS pQ (N_k_expr 12)))] : UPoly α) fun W =>
  letB (o.mul (o.mul (o.mul (o.mul (o.mul Q S) f2_7) f3_13) (o.pow (evalExpr2 o S Q pS pQ fac_5) 4))
      (evalExpr2 o S Q pS pQ fac_6)) fun D_div_L2 =>
  letB (evalACache o S Q) fun ac =>
  letB (evalGeomSQ o S Q) fun gsq =>
  ⟨W, D_div_L2, ac, gsq,
   dotW o (uTail ac.A0U_t0) W 1, dotW o (uTail ac.A0U_t1) W 1,
   dotW o ac.A0V_t0 W 0, dotW o ac.A0V_t1 W 0, dotW o ac.A0V_t2 W 0,
   dotW o ac.A0V_t0 W 1, dotW o ac.A0V_t1 W 1, dotW o ac.A0V_t2 W 1,
   dotW o (uMul o ac.A0V_t0 ac.Bv_SQ) W 0, dotW o (uMul o ac.A0V_t1 ac.Bv_SQ) W 0, dotW o (uMul o ac.A0V_t2 ac.Bv_SQ) W 0,
   dotW o ac.AY2_t0 W 0, dotW o ac.AY2_t1 W 0,
   dotW o ac.AY3_t0 W 1, dotW o ac.AY3_t1 W 1,
   dotW o ac.AX2_t0 W 0, dotW o ac.AX2_t1 W 0, dotW o ac.AX2_t2 W 0,
   [[evalExpr3PolyT o S Q pS pQ RQ5_biv_x0y0, evalExpr3PolyT o S Q pS pQ RQ5_biv_x0y1,
     evalExpr3PolyT o S Q pS pQ RQ5_biv_x0y2, evalExpr3PolyT o S Q pS pQ RQ5_biv_x0y3,
     evalExpr3PolyT o S Q pS pQ RQ5_biv_x0y4, evalExpr3PolyT o S Q pS pQ RQ5_biv_x0y5],
    [evalExpr3PolyT o S Q pS pQ RQ5_biv_x1y0, evalExpr3PolyT o S Q pS pQ RQ5_biv_x1y1,
     evalExpr3PolyT o S Q pS pQ RQ5_biv_x1y2, evalExpr3PolyT o S Q pS pQ RQ5_biv_x1y3,
     evalExpr3PolyT o S Q pS pQ RQ5_biv_x1y4]]⟩

private structure GeomT (α : Type*) where
  H0_7 : α
  H0_7_2 : α
  Av0_243 : α
  Cv0_int : α
  Cv0_243 : α
  Bv1_T_1701 : α
  DY2 : BivL α
  rem_qX0 : BivL α
  rem_qX1 : BivL α
  qX_0_sc : UBivL α
  qX_1_sc : UBivL α
  qY_0_321489 : UBivL α
  DY2_qE_63 : UBivL α
  q1_0_div_sc : UBivL α
  q1_1_sc : UBivL α
  q1_2_div_sc : UBivL α

private def evalGeomT {α : Type*} (o : PolyOps α) (S : α) (ca_p cb_p : UPoly α) (gsq : GeomSQ α) (T : α) : GeomT α :=
  letB (o.mul T T) fun T2 =>
  letB (o.mul T2 T) fun T3 =>
  letB (o.sub (o.sub (o.add (o.mul (o.ofInt (-2)) T3) (o.mul (o.ofInt 6) T2)) (o.mul (o.ofInt 3) T)) (o.ofInt 2)) fun pT =>
  letB (o.add gsq.H0_7_SQ (o.mul (o.ofInt 7) pT)) fun H0_7 =>
  letB (o.mul H0_7 H0_7) fun H0_7_2 =>
  letB (o.sub T (o.ofInt 3)) fun Tm3 =>
  letB (o.mul (o.ofInt (-4)) (o.mul (o.mul Tm3 Tm3) Tm3)) fun Av0_243 =>
  letB (o.sub (o.mul (o.ofInt 5) T) (o.ofInt 9)) fun T59 =>
  letB (o.mul T (o.mul T59 T59)) fun Cv0_int =>
  letB (o.mul (o.ofInt (-25)) Cv0_int) fun Cv0_243 =>
  letB (o.mul (o.ofInt 7) (o.sub (o.add (o.sub (o.mul (o.ofInt 143) T3) (o.mul (o.ofInt 828) T2))
      (o.mul (o.ofInt 1404) T)) (o.ofInt 594))) fun Bv1_T_1701 =>
  letB ([[o.add (o.neg T) (o.ofInt 2), o.ofInt 1]] : BivL α) fun v3 =>
  letB (bivMul o v3 v3) fun v3_2 =>
  letB (bivAdd o (bivConst (o.sub T (o.ofInt 4)))
      (bivAdd o (bivSc o (o.sub (o.mul (o.ofInt 18) T) (o.mul (o.ofInt 4) T2)) v3)
        (bivSc o (o.mul (o.ofInt (-27)) T) v3_2))) fun DY2 =>
  letB (bivAdd o (bivConst (o.add (o.mul (o.ofInt (-4)) T2) (o.mul (o.ofInt 18) T)))
      (bivSc o (o.mul (o.ofInt (-54)) T) v3)) fun dDY2_dy =>
  letB (o.mul S T) fun ST =>
  letB (o.mul (o.ofInt 2) ST) fun ST2 =>
  letB (bivSc o ST (bivMul o gsq.DX2 DY2)) fun W2 =>
  letB ([[o.zero, o.mul (o.ofInt 42) T]] : BivL α) fun dF5_4 =>
  letB (bivConst (o.sub (o.mul (o.ofInt 25) T) (o.ofInt 45))) fun LY0 =>
  letB ([[o.sub (o.ofInt 45) (o.mul (o.ofInt 25) T), o.ofInt 27]] : BivL α) fun LY1 =>
  letB (bivConst (o.mul (o.ofInt 54) T)) fun PY_4_1 =>
  letB (ubSub o (ubSc o (o.neg ST2) (ubBmul o LY0 gsq.dLX_0)) (ubSc o T (ubBmul o LY0 gsq.LX_27))) fun br0_0 =>
  letB (ubSub o (ubSc o (o.neg ST2) (ubBmul o LY1 gsq.dLX_0)) (ubSc o T (ubBmul o LY1 gsq.LX_27))) fun br1_0 =>
  letB (ubSc o (o.neg ST2) (ubBmul o LY0 gsq.dLX_1)) fun br0_1 =>
  letB (ubSc o (o.neg ST2) (ubBmul o LY1 gsq.dLX_1)) fun br1_1 =>
  letB (ubSc o (o.neg ST2) (ubBmul o LY0 gsq.dLX_3)) fun br0_3 =>
  letB (ubSc o (o.neg ST2) (ubBmul o LY1 gsq.dLX_3)) fun br1_3 =>
  letB (ubSc o (o.mul (o.ofInt 27) ST2) gsq.LX_27) fun br1_4 =>
  letB (ubSc o ST (ubAdd o (ubBmul o gsq.dF5_3 (ubNeg o (ubBmul o PY_4_1 gsq.PX_0)))
      (ubBmul o gsq.dF5_0 (ubBmul o PY_4_1 gsq.PX_3)))) fun omF1_0 =>
  letB (ubSc o ST (ubAdd o (ubBmul o gsq.dF5_3 (ubNeg o (ubBmul o PY_4_1 gsq.PX_1)))
      (ubBmul o gsq.dF5_1 (ubBmul o PY_4_1 gsq.PX_3)))) fun omF1_1 =>
  letB (ubSc o ST (ubSub o (ubBmul o gsq.dF5_3 (ubBmul o dDY2_dy br0_0)) (ubBmul o gsq.dF5_0 (ubBmul o dDY2_dy br0_3)))) fun dYF0_0 =>
  letB (ubSc o ST (ubSub o (ubBmul o gsq.dF5_3 (ubBmul o dDY2_dy br0_1)) (ubBmul o gsq.dF5_1 (ubBmul o dDY2_dy br0_3)))) fun dYF0_1 =>
  letB (ubSc o ST (ubSub o (ubBmul o gsq.dF5_3 (ubBmul o dDY2_dy br1_0)) (ubBmul o gsq.dF5_0 (ubBmul o dDY2_dy br1_3)))) fun dYF1_0 =>
  letB (ubSc o ST (ubSub o (ubBmul o gsq.dF5_3 (ubBmul o dDY2_dy br1_1)) (ubBmul o gsq.dF5_1 (ubBmul o dDY2_dy br1_3)))) fun dYF1_1 =>
  letB (ubSc o ST (ubBmul o dF5_4 (ubSub o (ubBmul o gsq.dDX2_dS br0_3) (ubBmul o gsq.dDX2_dx br0_0)))) fun dXF0_0 =>
  letB (ubSc o ST (ubBmul o dF5_4 (ubSub o (ubBmul o gsq.dDX2_dQ br0_3) (ubBmul o gsq.dDX2_dx br0_1)))) fun dXF0_1 =>
  letB (ubBmul o gsq.DX2 dYF0_0) fun QX0_0 =>
  letB (ubBmul o gsq.DX2 dYF0_1) fun QX0_1 =>
  letB (ubBmul o gsq.DX2 (ubSub o dYF1_0 (ubBmul o DY2 omF1_0))) fun QX1_0 =>
  letB (ubBmul o gsq.DX2 (ubSub o dYF1_1 (ubBmul o DY2 omF1_1))) fun QX1_1 =>
  letB (ubNeg o (ubBmul o DY2 dXF0_0)) fun QY0_0 =>
  letB (ubNeg o (ubBmul o DY2 dXF0_1)) fun QY0_1 =>
  letB (ubSc o (o.ofInt 2) (ubBmul o W2 (ubBmul o dF5_4 br0_3))) fun EB0_5103 =>
  letB (ubSc o (o.ofInt 2) (ubBmul o W2 (ubSub o (ubBmul o dF5_4 br1_3) (ubBmul o gsq.dF5_3 br1_4)))) fun EB1_5103 =>
  letB (ubSynDiv1Rem o (ubSub o (ubMulU o cb_p QX0_0) (ubMulU o ca_p QX0_1))) fun div0 =>
  letB (ubSynDiv1Rem o (ubSub o (ubMulU o cb_p QX1_0) (ubMulU o ca_p QX1_1))) fun div1 =>
  letB (ubSub o (ubMulU o cb_p QY0_0) (ubMulU o ca_p QY0_1)) fun QY_dot_0_sc =>
  letB (o.mul (o.ofInt 4) (o.mul gsq.S2 T2)) fun c4S2T2 =>
  letB ([[[o.mul c4S2T2 (gsq.qC_63.getD 0 o.zero)], [o.mul c4S2T2 (gsq.qEx_63.getD 0 o.zero)]],
         [[o.mul c4S2T2 (gsq.qC_63.getD 1 o.zero)], [o.mul c4S2T2 (gsq.qEx_63.getD 1 o.zero)]]] : UBivL α) fun qE_63 =>
  letB (ubBmul o DY2 qE_63) fun DY2_qE_63 =>
  letB (ubAdd o (ubNeg o QY_dot_0_sc) (ubSc o (o.mul (o.ofInt 189) Cv0_243) (ubShift DY2_qE_63))) fun qY_0_321489 =>
  ⟨H0_7, H0_7_2, Av0_243, Cv0_int, Cv0_243, Bv1_T_1701, DY2,
   div0.1, div1.1, div0.2, div1.2, qY_0_321489, DY2_qE_63,
   ubAdd o (ubSc o (o.mul (o.ofInt (-9)) H0_7) div0.2) (ubSc o (o.ofInt 63) (ubMulU o gsq.qC_63 EB0_5103)),
   ubAdd o (ubSc o (o.mul (o.ofInt 9) H0_7) (ubMulU o gsq.A1_1_27 qY_0_321489))
     (ubShift (ubAdd o
       (ubSc o (o.mul (o.ofInt 9) H0_7) (ubSub o (ubSc o Av0_243 div0.2) (ubSc o Cv0_243 div1.2)))
       (ubSc o (o.ofInt 63) (ubMulU o gsq.qC_63 (ubSub o (ubSc o Cv0_243 EB1_5103) (ubSc o Av0_243 EB0_5103)))))),
   ubSub o
     (ubAdd o (ubSc o (o.mul (o.ofInt (-1701)) H0_7) (ubMulU o gsq.A1_1_27 DY2_qE_63))
       (ubSc o (o.mul (o.ofInt 9) H0_7) div1.2))
     (ubSc o (o.ofInt 63) (ubMulU o gsq.qC_63 EB1_5103))⟩

private def evalBTot {α : Type*} (o : PolyOps α) (cache : SQCache α) (gt : GeomT α) (T : α) : BivL α :=
  letB (o.mul T T) fun T2 =>
  letB (uAdd o cache.d_A0U_t0 (uSc o T cache.d_A0U_t1)) fun d_A0U =>
  letB (uAdd o (uAdd o cache.d_A0V_t0 (uSc o T cache.d_A0V_t1)) (uSc o T2 cache.d_A0V_t2)) fun d_A0V =>
  letB (uAdd o (uAdd o cache.d_A0V_U_t0 (uSc o T cache.d_A0V_U_t1)) (uSc o T2 cache.d_A0V_U_t2)) fun d_A0V_U =>
  letB (uAdd o (uAdd o (uAdd o cache.d_A0VBv_t0 (uSc o T cache.d_A0VBv_t1)) (uSc o T2 cache.d_A0VBv_t2))
      (uSc o gt.Bv1_T_1701 d_A0V_U)) fun d_A0VBv =>
  letB (uAdd o cache.d_AY2_t0 (uSc o T cache.d_AY2_t1)) fun d_AY2 =>
  letB (uAdd o cache.d_AY3_t0 (uSc o T cache.d_AY3_t1)) fun d_AY3 =>
  letB (uAdd o (uAdd o cache.d_AX2_t0 (uSc o T cache.d_AX2_t1)) (uSc o T2 cache.d_AX2_t2)) fun d_AX2 =>
  bivAdd o (bivAdd o (bivAdd o
      (combineBivDot o (ubSub o gt.q1_0_div_sc gt.q1_2_div_sc) (uSc o (o.mul (o.ofInt 7) gt.Cv0_243) d_A0U))
      (combineBivDot o gt.DY2_qE_63 (uSc o (o.mul (o.ofInt 45927) (o.mul gt.Cv0_243 gt.H0_7_2)) d_AY3)))
      (combineBivDot o gt.q1_1_sc (uSc o (o.ofInt 7) d_A0V)))
    (bivAdd o (bivSc o (o.mul (o.ofInt 243) gt.H0_7_2)
      (bivAdd o (combineBivDot o gt.qY_0_321489 d_AY2) (combineBivDot o gt.qX_0_sc d_AX2)))
      (bivNeg o (combineBivDot o gt.q1_0_div_sc d_A0VBv)))

private def evalTStep {α : Type*} (o : PolyOps α) (S : α) (cache : SQCache α) (T : α) : BivL α :=
  letB (evalGeomT o S cache.ac.ca_p cache.ac.cb_p cache.gsq T) fun gt =>
  letB (evalBTot o cache gt T) fun B_tot =>
  letB (o.mul (o.ofInt 21) S) fun s21 =>
  letB (o.neg (o.mul (o.ofInt 21) T)) fun t21 =>
  letB (o.neg gt.H0_7) fun nh0 =>
  letB (bivRedOnce o s21 t21 nh0 (bivRedOnce o s21 t21 nh0 B_tot)) fun lhs =>
  letB (o.mul (o.ofInt C_RHS_int) (o.mul (o.mul s21 s21) (o.mul gt.Cv0_int cache.D_div_L2))) fun rhs_sc =>
  letB (cache.RQ5_T.map (fun row => row.map (fun p => uEval o p T))) fun rhs_raw =>
  bivSub o lhs (bivSc o rhs_sc rhs_raw)

-- `PolyOpsRel` preservation for `evalACache`, `evalGeomSQ`, `evalSQCache`, `evalGeomT`, `evalBTot`, `evalTStep`
section CacheRel
variable {α β : Type*} {o1 : PolyOps α} {o2 : PolyOps β} {R : α → β → Prop}

private structure ACacheRel (R : α → β → Prop) (a : ACache α) (b : ACache β) : Prop where
  ca_p : URel R a.ca_p b.ca_p
  cb_p : URel R a.cb_p b.cb_p
  A0U_t0 : URel R a.A0U_t0 b.A0U_t0
  A0U_t1 : URel R a.A0U_t1 b.A0U_t1
  A0V_t0 : URel R a.A0V_t0 b.A0V_t0
  A0V_t1 : URel R a.A0V_t1 b.A0V_t1
  A0V_t2 : URel R a.A0V_t2 b.A0V_t2
  AY2_t0 : URel R a.AY2_t0 b.AY2_t0
  AY2_t1 : URel R a.AY2_t1 b.AY2_t1
  AY3_t0 : URel R a.AY3_t0 b.AY3_t0
  AY3_t1 : URel R a.AY3_t1 b.AY3_t1
  AX2_t0 : URel R a.AX2_t0 b.AX2_t0
  AX2_t1 : URel R a.AX2_t1 b.AX2_t1
  AX2_t2 : URel R a.AX2_t2 b.AX2_t2
  Bv_SQ : URel R a.Bv_SQ b.Bv_SQ

private structure GeomSQRel (R : α → β → Prop) (a : GeomSQ α) (b : GeomSQ β) : Prop where
  H0_7_SQ : R a.H0_7_SQ b.H0_7_SQ
  S2 : R a.S2 b.S2
  DX2 : BRel R a.DX2 b.DX2
  dDX2_dS : BRel R a.dDX2_dS b.dDX2_dS
  dDX2_dQ : BRel R a.dDX2_dQ b.dDX2_dQ
  dDX2_dx : BRel R a.dDX2_dx b.dDX2_dx
  dF5_0 : BRel R a.dF5_0 b.dF5_0
  dF5_1 : BRel R a.dF5_1 b.dF5_1
  dF5_3 : BRel R a.dF5_3 b.dF5_3
  LX_27 : UBRel R a.LX_27 b.LX_27
  dLX_0 : UBRel R a.dLX_0 b.dLX_0
  dLX_1 : UBRel R a.dLX_1 b.dLX_1
  dLX_3 : UBRel R a.dLX_3 b.dLX_3
  PX_0 : UBRel R a.PX_0 b.PX_0
  PX_1 : UBRel R a.PX_1 b.PX_1
  PX_3 : UBRel R a.PX_3 b.PX_3
  A1_1_27 : URel R a.A1_1_27 b.A1_1_27
  qC_63 : URel R a.qC_63 b.qC_63
  qEx_63 : URel R a.qEx_63 b.qEx_63

private structure SQCacheRel (R : α → β → Prop) (a : SQCache α) (b : SQCache β) : Prop where
  W : URel R a.W b.W
  D_div_L2 : R a.D_div_L2 b.D_div_L2
  ac : ACacheRel R a.ac b.ac
  gsq : GeomSQRel R a.gsq b.gsq
  d_A0U_t0 : URel R a.d_A0U_t0 b.d_A0U_t0
  d_A0U_t1 : URel R a.d_A0U_t1 b.d_A0U_t1
  d_A0V_t0 : URel R a.d_A0V_t0 b.d_A0V_t0
  d_A0V_t1 : URel R a.d_A0V_t1 b.d_A0V_t1
  d_A0V_t2 : URel R a.d_A0V_t2 b.d_A0V_t2
  d_A0V_U_t0 : URel R a.d_A0V_U_t0 b.d_A0V_U_t0
  d_A0V_U_t1 : URel R a.d_A0V_U_t1 b.d_A0V_U_t1
  d_A0V_U_t2 : URel R a.d_A0V_U_t2 b.d_A0V_U_t2
  d_A0VBv_t0 : URel R a.d_A0VBv_t0 b.d_A0VBv_t0
  d_A0VBv_t1 : URel R a.d_A0VBv_t1 b.d_A0VBv_t1
  d_A0VBv_t2 : URel R a.d_A0VBv_t2 b.d_A0VBv_t2
  d_AY2_t0 : URel R a.d_AY2_t0 b.d_AY2_t0
  d_AY2_t1 : URel R a.d_AY2_t1 b.d_AY2_t1
  d_AY3_t0 : URel R a.d_AY3_t0 b.d_AY3_t0
  d_AY3_t1 : URel R a.d_AY3_t1 b.d_AY3_t1
  d_AX2_t0 : URel R a.d_AX2_t0 b.d_AX2_t0
  d_AX2_t1 : URel R a.d_AX2_t1 b.d_AX2_t1
  d_AX2_t2 : URel R a.d_AX2_t2 b.d_AX2_t2
  RQ5_T : List.Forall₂ (List.Forall₂ (URel R)) a.RQ5_T b.RQ5_T

private structure GeomTRel (R : α → β → Prop) (a : GeomT α) (b : GeomT β) : Prop where
  H0_7 : R a.H0_7 b.H0_7
  H0_7_2 : R a.H0_7_2 b.H0_7_2
  Av0_243 : R a.Av0_243 b.Av0_243
  Cv0_int : R a.Cv0_int b.Cv0_int
  Cv0_243 : R a.Cv0_243 b.Cv0_243
  Bv1_T_1701 : R a.Bv1_T_1701 b.Bv1_T_1701
  DY2 : BRel R a.DY2 b.DY2
  rem_qX0 : BRel R a.rem_qX0 b.rem_qX0
  rem_qX1 : BRel R a.rem_qX1 b.rem_qX1
  qX_0_sc : UBRel R a.qX_0_sc b.qX_0_sc
  qX_1_sc : UBRel R a.qX_1_sc b.qX_1_sc
  qY_0_321489 : UBRel R a.qY_0_321489 b.qY_0_321489
  DY2_qE_63 : UBRel R a.DY2_qE_63 b.DY2_qE_63
  q1_0_div_sc : UBRel R a.q1_0_div_sc b.q1_0_div_sc
  q1_1_sc : UBRel R a.q1_1_sc b.q1_1_sc
  q1_2_div_sc : UBRel R a.q1_2_div_sc b.q1_2_div_sc

private lemma evalACache_rel (hR : PolyOpsRel o1 o2 R) {S1 Q1 : α} {S2 Q2 : β}
    (hS : R S1 S2) (hQ : R Q1 Q2) : ACacheRel R (evalACache o1 S1 Q1) (evalACache o2 S2 Q2) := by
  unfold evalACache
  refine letB_rel (hR.rel_mul hS hS) fun hS2 =>
    letB_rel (hR.rel_mul hS hQ) fun hSQ =>
    letB_rel (hR.rel_mul hQ hQ) fun hQ2 =>
    letB_rel (hR.rel_mul hS2 hS) fun hS3 =>
    letB_rel (hR.rel_mul hQ2 hQ) fun hQ3 =>
    letB_rel (hR.rel_sub hS (hR.rel_mul (hR.rel_ofInt 3) hQ)) fun hSm3Q =>
    letB_rel (hR.rel_mul hSm3Q hSm3Q) fun hSm3Q2 =>
    letB_rel (hR.rel_sub (hR.rel_mul (hR.rel_ofInt 5) hS) (hR.rel_mul (hR.rel_ofInt 9) hQ)) fun hA5 =>
    letB_rel (hR.rel_mul (hR.rel_ofInt (-175)) (hR.rel_mul hA5 (hR.rel_sub (hR.rel_mul (hR.rel_ofInt 5) hS) (hR.rel_mul (hR.rel_ofInt 3) hQ)))) fun hca0 =>
    letB_rel (hR.rel_mul (hR.rel_ofInt 7) (hR.rel_add (hR.rel_sub (hR.rel_mul (hR.rel_ofInt 143) hS2) (hR.rel_mul (hR.rel_ofInt 552) hSQ)) (hR.rel_mul (hR.rel_ofInt 468) hQ2))) fun hca1 =>
    letB_rel (hR.rel_mul (hR.rel_ofInt (-28)) hSm3Q2) fun hca2 =>
    letB_rel (.cons hca0 (.cons hca1 (.cons hca2 .nil)) : URel R _ _) fun hca =>
    letB_rel (hR.rel_mul (hR.rel_ofInt 1050) (hR.rel_mul hS hA5)) fun hcb0 =>
    letB_rel (hR.rel_add (hR.rel_add (hR.rel_mul (hR.rel_ofInt 21) (hR.rel_sub (hR.rel_add (hR.rel_mul (hR.rel_ofInt (-92)) hS2) (hR.rel_mul (hR.rel_ofInt 312) hSQ)) (hR.rel_mul (hR.rel_ofInt 198) hQ2))) (hR.rel_mul (hR.rel_ofInt 810) hQ)) (hR.rel_ofInt 810)) fun hcb1 =>
    letB_rel (hR.rel_mul (hR.rel_ofInt 84) hSm3Q2) fun hcb2 =>
    letB_rel (.cons hcb0 (.cons hcb1 (.cons hcb2 .nil)) : URel R _ _) fun hcb =>
    letB_rel (uNeg_rel hR hca) fun hb =>
    letB_rel (.cons (hR.rel_sub hcb0 (hR.rel_mul (hR.rel_ofInt 3) (hR.rel_neg hca0)))
        (.cons (hR.rel_sub hcb1 (hR.rel_mul (hR.rel_ofInt 3) (hR.rel_neg hca1))) .nil) : URel R _ _) fun ham3b =>
    letB_rel (uSub_rel hR (uSc_rel hR (hR.rel_ofInt 5) hcb) (uSc_rel hR (hR.rel_ofInt 9) hb)) fun ha5m9b =>
    letB_rel (uSub_rel hR (uSc_rel hR (hR.rel_ofInt 15) hcb) (uSc_rel hR (hR.rel_ofInt 9) hb)) fun ha15m9b =>
    letB_rel (uMul_rel hR hcb hcb) fun haa =>
    letB_rel (uMul_rel hR hcb hb) fun hab =>
    letB_rel (uMul_rel hR hb hb) fun hbb =>
    letB_rel (uMul_rel hR ham3b ham3b) fun ham3b2 =>
    letB_rel (uAdd_rel hR (uAdd_rel hR (uSc_rel hR (hR.rel_ofInt (-25)) (uMul_rel hR ha5m9b ha15m9b))
        (uShift_rel hR (uAdd_rel hR (uSub_rel hR (uSc_rel hR (hR.rel_ofInt 429) haa) (uSc_rel hR (hR.rel_ofInt 1656) hab)) (uSc_rel hR (hR.rel_ofInt 1404) hbb))))
        (uShift_rel hR (uShift_rel hR (uSc_rel hR (hR.rel_ofInt (-12)) ham3b2)))) fun hA2 =>
    letB_rel (uAdd_rel hR (uAdd_rel hR (uSc_rel hR (hR.rel_ofInt 50) (uMul_rel hR hcb ha5m9b))
        (uShift_rel hR (uSub_rel hR (uAdd_rel hR (uSc_rel hR (hR.rel_ofInt (-92)) haa) (uSc_rel hR (hR.rel_ofInt 312) hab)) (uSc_rel hR (hR.rel_ofInt 198) hbb))))
        (uShift_rel hR (uShift_rel hR (uSc_rel hR (hR.rel_ofInt 4) ham3b2)))) fun hB2 =>
    letB_rel (hR.rel_sub (hR.rel_mul (hR.rel_ofInt 15) hS) (hR.rel_mul (hR.rel_ofInt 9) hQ)) fun hS15m9Q =>
    letB_rel (uAdd_rel hR (uSc_rel hR hS hb) (uSc_rel hR hQ hcb)) fun hsbqa =>
    letB_rel (uAdd_rel hR (uAdd_rel hR (uSc_rel hR (hR.rel_ofInt (-25)) (uAdd_rel hR (uSc_rel hR hS15m9Q ha5m9b) (uSc_rel hR hA5 ha15m9b)))
        (uShift_rel hR (uAdd_rel hR (uSub_rel hR (uSc_rel hR (hR.rel_mul (hR.rel_ofInt 858) hS) hcb) (uSc_rel hR (hR.rel_ofInt 1656) hsbqa))
          (uSc_rel hR (hR.rel_mul (hR.rel_ofInt 2808) hQ) hb))))
        (uShift_rel hR (uShift_rel hR (uSc_rel hR (hR.rel_mul (hR.rel_ofInt (-24)) hSm3Q) ham3b)))) fun hA1 =>
    letB_rel (uAdd_rel hR (uAdd_rel hR (uSc_rel hR (hR.rel_ofInt 350) (uSub_rel hR (uSc_rel hR (hR.rel_sub (hR.rel_mul (hR.rel_ofInt 10) hS) (hR.rel_mul (hR.rel_ofInt 9) hQ)) hcb)
        (uSc_rel hR (hR.rel_mul (hR.rel_ofInt 9) hS) hb)))
        (uShift_rel hR (uAdd_rel hR (uSc_rel hR (hR.rel_ofInt 7) (uSub_rel hR (uAdd_rel hR (uSc_rel hR (hR.rel_mul (hR.rel_ofInt (-184)) hS) hcb)
          (uSc_rel hR (hR.rel_ofInt 312) hsbqa)) (uSc_rel hR (hR.rel_mul (hR.rel_ofInt 396) hQ) hb))) (uSc_rel hR (hR.rel_ofInt 270) hb))))
        (uShift_rel hR (uShift_rel hR (uSc_rel hR (hR.rel_mul (hR.rel_ofInt 56) hSm3Q) ham3b)))) fun hB1 =>
    letB_rel (uSc_rel hR (hR.rel_ofInt 567) (uSub_rel hR (uMul_rel hR hA2 hB1) (uSc_rel hR (hR.rel_ofInt 7) (uMul_rel hR hA1 hB2)))) fun hD21 =>
    letB_rel (uSub_rel hR (uSc_rel hR (hR.rel_ofInt 189) (uMul_rel hR hA2 hcb)) (uSc_rel hR (hR.rel_ofInt 1701) (uMul_rel hR hca hB2))) fun hD20 =>
    letB_rel (uSub_rel hR (uSc_rel hR (hR.rel_ofInt 189) (uMul_rel hR hA1 hcb)) (uSc_rel hR (hR.rel_ofInt 243) (uMul_rel hR hca hB1))) fun hD10 =>
    letB_rel (uAdd_rel hR (uSub_rel hR (uMul_rel hR haa hD10) (uSc_rel hR (hR.rel_mul (hR.rel_ofInt 2) hS) (uMul_rel hR hcb hD20))) (uSc_rel hR hS2 hD21)) fun hm0 =>
    letB_rel (uAdd_rel hR (uSub_rel hR (uMul_rel hR hab hD10) (uMul_rel hR hsbqa hD20)) (uSc_rel hR hSQ hD21)) fun hm1 =>
    letB_rel (uAdd_rel hR (uSub_rel hR (uMul_rel hR hbb hD10) (uSc_rel hR (hR.rel_mul (hR.rel_ofInt 2) hQ) (uMul_rel hR hb hD20))) (uSc_rel hR hQ2 hD21)) fun hm2 =>
    letB_rel (uSub_rel hR (uSc_rel hR hS hD21) (uMul_rel hR hcb hD20)) fun hm4 =>
    letB_rel (uSub_rel hR (uSc_rel hR hQ hD21) (uMul_rel hR hb hD20)) fun hm6 =>
    letB_rel (uSub_rel hR (uSc_rel hR (hR.rel_ofInt 5) hm0) (uSc_rel hR (hR.rel_ofInt 9) hm1)) fun hl01 =>
    letB_rel (uSub_rel hR (uSc_rel hR (hR.rel_ofInt 5) hm1) (uSc_rel hR (hR.rel_ofInt 9) hm2)) fun hl12 =>
    letB_rel (uSub_rel hR (uSc_rel hR (hR.rel_ofInt 5) hm4) (uSc_rel hR (hR.rel_ofInt 9) hm6)) fun hl46 =>
    letB_rel (uSc_rel hR (hR.rel_ofInt (-100 * 968178750)) hl46) fun hAY2b =>
    letB_rel (hR.rel_mul (hR.rel_ofInt (-175)) (hR.rel_mul hS (hR.rel_mul hA5 hA5))) fun hBv0 =>
    letB_rel (hR.rel_sub (hR.rel_add (hR.rel_sub (hR.rel_mul (hR.rel_ofInt 143) hS3) (hR.rel_mul (hR.rel_ofInt 828) (hR.rel_mul hS2 hQ)))
        (hR.rel_mul (hR.rel_ofInt 1404) (hR.rel_mul hS hQ2))) (hR.rel_mul (hR.rel_ofInt 594) hQ3)) fun hBv1S =>
    letB_rel (hR.rel_add (hR.rel_add (hR.rel_mul (hR.rel_ofInt 7) hBv1S) (hR.rel_mul (hR.rel_ofInt 1215) hQ2)) (hR.rel_mul (hR.rel_ofInt 2430) hQ)) fun hBv1 =>
    letB_rel (hR.rel_mul (hR.rel_ofInt (-28)) (hR.rel_mul hSm3Q2 hSm3Q)) fun hBv2 =>
    ⟨hca, hcb,
      uAdd_rel hR (uAdd_rel hR (uSc_rel hR (hR.rel_ofInt _) hl01) (uSc_rel hR (hR.rel_ofInt _) hl12)) (uSc_rel hR (hR.rel_ofInt _) hl46),
      uSc_rel hR (hR.rel_ofInt _) hl46,
      uAdd_rel hR (uAdd_rel hR (uSc_rel hR (hR.rel_ofInt _) hm4) (uSc_rel hR (hR.rel_ofInt _) hm6)) (uSc_rel hR (hR.rel_ofInt _) hD21),
      uAdd_rel hR (uAdd_rel hR (uAdd_rel hR (uSc_rel hR (hR.rel_ofInt _) hm4) (uSc_rel hR (hR.rel_ofInt _) hm6)) (uSc_rel hR (hR.rel_ofInt _) hD21)) (uSc_rel hR (hR.rel_ofInt _) hD21),
      uSc_rel hR (hR.rel_ofInt _) hD21,
      uSc_rel hR (hR.rel_ofInt _) hAY2b, uSc_rel hR (hR.rel_ofInt _) hAY2b,
      uAdd_rel hR (uSub_rel hR (uAdd_rel hR (uSc_rel hR (hR.rel_ofInt _) hl01) (uSc_rel hR (hR.rel_ofInt _) hl12)) (uSc_rel hR (hR.rel_ofInt _) hl46))
        (uShift_rel hR (uAdd_rel hR (uSc_rel hR (hR.rel_ofInt _) (uSub_rel hR (uAdd_rel hR (uSc_rel hR (hR.rel_ofInt _) hm0) (uSc_rel hR (hR.rel_ofInt _) hm6)) (uSc_rel hR (hR.rel_ofInt _) hD21)))
          (uSc_rel hR (hR.rel_ofInt _) (uSub_rel hR (uAdd_rel hR (uSc_rel hR (hR.rel_ofInt _) hm1) (uSc_rel hR (hR.rel_ofInt _) hm6)) (uSc_rel hR (hR.rel_ofInt _) hD21))))),
      uAdd_rel hR (uSc_rel hR (hR.rel_ofInt _) hl46)
        (uShift_rel hR (uAdd_rel hR (uSc_rel hR (hR.rel_ofInt _) (uSc_rel hR (hR.rel_ofInt _) hD21)) (uSc_rel hR (hR.rel_ofInt _) (uSc_rel hR (hR.rel_ofInt _) hD21)))),
      uShift_rel hR (uAdd_rel hR (uSc_rel hR (hR.rel_ofInt _) hm4) (uSc_rel hR (hR.rel_ofInt _) hD21)),
      uShift_rel hR (uAdd_rel hR (uAdd_rel hR (uSc_rel hR (hR.rel_ofInt _) hm4) (uSc_rel hR (hR.rel_ofInt _) hD21)) (uSc_rel hR (hR.rel_ofInt _) hD21)),
      uShift_rel hR (uSc_rel hR (hR.rel_ofInt _) hD21),
      .cons hBv0 (.cons hBv1 (.cons hBv2 .nil))⟩

private lemma evalGeomSQ_rel (hR : PolyOpsRel o1 o2 R) {S1 Q1 : α} {S2 Q2 : β}
    (hS : R S1 S2) (hQ : R Q1 Q2) : GeomSQRel R (evalGeomSQ o1 S1 Q1) (evalGeomSQ o2 S2 Q2) := by
  unfold evalGeomSQ
  refine letB_rel (hR.rel_mul hS hS) fun hS2 =>
    letB_rel (hR.rel_mul hS hQ) fun hSQ =>
    letB_rel (hR.rel_mul hQ hQ) fun hQ2 =>
    letB_rel (hR.rel_mul hS2 hS) fun hS3 =>
    letB_rel (hR.rel_mul hS2 hS2) fun hS4 =>
    letB_rel (hR.rel_mul hQ2 hQ) fun hQ3 =>
    letB_rel (hR.rel_mul hQ2 hQ2) fun hQ4 =>
    letB_rel (hR.rel_sub hS (hR.rel_mul (hR.rel_ofInt 3) hQ)) fun hSm3Q =>
    letB_rel (hR.rel_sub (hR.rel_mul (hR.rel_ofInt 5) hS) (hR.rel_mul (hR.rel_ofInt 9) hQ)) fun hA5 =>
    letB_rel (hR.rel_sub (hR.rel_sub (hR.rel_add (hR.rel_mul (hR.rel_ofInt (-2)) hS3) (hR.rel_mul (hR.rel_ofInt 6) (hR.rel_mul hS2 hQ)))
        (hR.rel_mul (hR.rel_ofInt 3) (hR.rel_mul hS hQ2))) (hR.rel_mul (hR.rel_ofInt 2) hQ3)) fun hpS =>
    letB_rel (hR.rel_add (hR.rel_add (hR.rel_mul (hR.rel_ofInt 7) hpS) (hR.rel_mul (hR.rel_ofInt 5) hQ2)) (hR.rel_mul (hR.rel_ofInt 10) hQ)) fun hH0 =>
    letB_rel (.cons (.cons (hR.rel_add (hR.rel_neg hS) (hR.rel_mul (hR.rel_ofInt 2) hQ)) .nil) (.cons (.cons (hR.rel_ofInt 1) .nil) .nil) : BRel R _ _) fun hu3 =>
    letB_rel (bivMul_rel hR hu3 hu3) fun hu3_2 =>
    letB_rel (bivConst_rel (hR.rel_sub (hR.rel_mul (hR.rel_ofInt 25) hS) (hR.rel_mul (hR.rel_ofInt 45) hQ))) fun hLX0 =>
    letB_rel (.cons (.cons (hR.rel_sub (hR.rel_mul (hR.rel_ofInt 45) hQ) (hR.rel_mul (hR.rel_ofInt 25) hS)) .nil) (.cons (.cons (hR.rel_ofInt 27) .nil) .nil) : BRel R _ _) fun hLX1 =>
    letB_rel (.cons hLX0 (.cons hLX1 .nil) : UBRel R _ _) fun hLX =>
    letB_rel (.cons (bivConst_rel (hR.rel_ofInt 25)) (.cons (bivConst_rel (hR.rel_ofInt (-25))) .nil) : UBRel R _ _) fun hdLX0 =>
    letB_rel (.cons (bivConst_rel (hR.rel_ofInt (-45))) (.cons (bivConst_rel (hR.rel_ofInt 45)) .nil) : UBRel R _ _) fun hdLX1 =>
    letB_rel (.cons .nil (.cons (bivConst_rel (hR.rel_ofInt 27)) .nil) : UBRel R _ _) fun hdLX3 =>
    letB_rel (hR.rel_mul (hR.rel_ofInt 2) hS) fun hS2x =>
    ⟨hH0, hS2,
      bivAdd_rel hR (bivConst_rel (hR.rel_sub (hR.rel_mul hS hQ2) (hR.rel_mul (hR.rel_ofInt 4) hQ3)))
        (bivAdd_rel hR (bivSc_rel hR (hR.rel_sub (hR.rel_mul (hR.rel_ofInt 18) hSQ) (hR.rel_mul (hR.rel_ofInt 4) hS2)) hu3)
          (bivSc_rel hR (hR.rel_mul (hR.rel_ofInt (-27)) hS) hu3_2)),
      bivAdd_rel hR (bivConst_rel (hR.rel_sub (hR.rel_add hQ2 (hR.rel_mul (hR.rel_ofInt 4) hS2)) (hR.rel_mul (hR.rel_ofInt 18) hSQ)))
        (bivAdd_rel hR (bivSc_rel hR (hR.rel_add (hR.rel_mul (hR.rel_ofInt 46) hS) (hR.rel_mul (hR.rel_ofInt 18) hQ)) hu3)
          (bivSc_rel hR (hR.rel_ofInt (-27)) hu3_2)),
      bivAdd_rel hR (bivConst_rel (hR.rel_sub (hR.rel_add (hR.rel_mul (hR.rel_ofInt (-8)) hS2) (hR.rel_mul (hR.rel_ofInt 38) hSQ)) (hR.rel_mul (hR.rel_ofInt 12) hQ2)))
        (bivSc_rel hR (hR.rel_mul (hR.rel_ofInt (-90)) hS) hu3),
      bivAdd_rel hR (bivConst_rel (hR.rel_add (hR.rel_mul (hR.rel_ofInt (-4)) hS2) (hR.rel_mul (hR.rel_ofInt 18) hSQ)))
        (bivSc_rel hR (hR.rel_mul (hR.rel_ofInt (-54)) hS) hu3),
      .cons (.cons (hR.rel_mul (hR.rel_ofInt 7) (hR.rel_sub (hR.rel_add (hR.rel_mul (hR.rel_ofInt (-6)) hS2) (hR.rel_mul (hR.rel_ofInt 12) hSQ)) (hR.rel_mul (hR.rel_ofInt 3) hQ2))) .nil)
        (.cons .nil (.cons (.cons (hR.rel_ofInt 21) .nil) .nil)),
      .cons (.cons (hR.rel_add (hR.rel_add (hR.rel_mul (hR.rel_ofInt 7) (hR.rel_sub (hR.rel_sub (hR.rel_mul (hR.rel_ofInt 6) hS2) (hR.rel_mul (hR.rel_ofInt 6) hSQ)) (hR.rel_mul (hR.rel_ofInt 6) hQ2))) (hR.rel_mul (hR.rel_ofInt 10) hQ)) (hR.rel_ofInt 10)) .nil) .nil,
      .cons .nil (.cons (.cons (hR.rel_mul (hR.rel_ofInt 42) hS) .nil) .nil),
      hLX, hdLX0, hdLX1, hdLX3,
      ubAdd_rel hR (ubSc_rel hR hS2x hdLX0) hLX, ubSc_rel hR hS2x hdLX1, ubSc_rel hR hS2x hdLX3,
      .cons (hR.rel_mul (hR.rel_ofInt 25) (hR.rel_mul hS (hR.rel_mul hA5 hA5))) (.cons (hR.rel_mul (hR.rel_ofInt (-4)) (hR.rel_mul (hR.rel_mul hSm3Q hSm3Q) hSm3Q)) .nil),
      .cons (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add
          (hR.rel_mul (hR.rel_ofInt _) hS4) (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hS3 hQ)))
          (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hS2 hQ2))) (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hS hQ3)))
          (hR.rel_mul (hR.rel_ofInt _) hQ4)) (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hS2 hQ)))
          (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hS hQ2))) (hR.rel_mul (hR.rel_ofInt _) hQ3))
          (hR.rel_mul (hR.rel_ofInt _) hS2)) (hR.rel_mul (hR.rel_ofInt _) hSQ)) (hR.rel_mul (hR.rel_ofInt _) hQ2))
        (.cons (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add
          (hR.rel_mul (hR.rel_ofInt _) hS4) (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hS3 hQ)))
          (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hS2 hQ2))) (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hS hQ3)))
          (hR.rel_mul (hR.rel_ofInt _) hQ4)) (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hS2 hQ)))
          (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hS hQ2))) (hR.rel_mul (hR.rel_ofInt _) hQ3))
          (hR.rel_mul (hR.rel_ofInt _) hS2)) (hR.rel_mul (hR.rel_ofInt _) hSQ)) (hR.rel_mul (hR.rel_ofInt _) hQ2)) .nil),
      .cons (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add
          (hR.rel_mul (hR.rel_ofInt _) hS3) (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hS2 hQ)))
          (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hS hQ2))) (hR.rel_mul (hR.rel_ofInt _) hQ3))
          (hR.rel_mul (hR.rel_ofInt _) hSQ)) (hR.rel_mul (hR.rel_ofInt _) hQ2))
          (hR.rel_mul (hR.rel_ofInt _) hS)) (hR.rel_mul (hR.rel_ofInt _) hQ))
        (.cons (hR.rel_add (hR.rel_add (hR.rel_add
          (hR.rel_mul (hR.rel_ofInt _) hS3) (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hS2 hQ)))
          (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hS hQ2))) (hR.rel_mul (hR.rel_ofInt _) hQ3)) .nil)⟩

private lemma evalSQCache_rel (hR : PolyOpsRel o1 o2 R) {S1 Q1 : α} {S2 Q2 : β}
    (hS : R S1 S2) (hQ : R Q1 Q2) : SQCacheRel R (evalSQCache o1 S1 Q1) (evalSQCache o2 S2 Q2) := by
  unfold evalSQCache
  refine letB_rel (powList_rel hR hS 30 (hR.rel_ofInt 1)) fun hpS =>
    letB_rel (powList_rel hR hQ 37 (hR.rel_ofInt 1)) fun hpQ =>
    letB_rel (hR.rel_add (hR.rel_mul (hR.rel_ofInt (-5)) hS) (hR.rel_mul (hR.rel_ofInt 9) hQ)) fun hf2 =>
    letB_rel (hR.rel_add (hR.rel_neg hS) (hR.rel_mul (hR.rel_ofInt 3) hQ)) fun hf3 =>
    letB_rel (hR.rel_add (hR.rel_add (hR.rel_ofInt (-45)) (hR.rel_mul (hR.rel_ofInt (-77)) hS)) (hR.rel_mul (hR.rel_ofInt 210) hQ)) fun hf4 =>
    letB_rel (hR.rel_mul hf2 hf2) fun hf2_2 =>
    letB_rel (hR.rel_mul hf2_2 hf2_2) fun hf2_4 =>
    letB_rel (hR.rel_mul hf2_4 hf2_2) fun hf2_6 =>
    letB_rel (hR.rel_mul hf2_6 hf2) fun hf2_7 =>
    letB_rel (hR.rel_mul (hR.rel_mul hf3 hf3) hf3) fun hf3_3 =>
    letB_rel (hR.rel_mul hf3_3 hf3_3) fun hf3_6 =>
    letB_rel (hR.rel_mul hf3_6 hf3_3) fun hf3_9 =>
    letB_rel (hR.rel_mul hf3_9 hf3_3) fun hf3_12 =>
    letB_rel (hR.rel_mul hf3_12 hf3) fun hf3_13 =>
    letB_rel (hR.rel_mul hf4 hf4) fun hf4_2 =>
    letB_rel (hR.rel_mul hf3_13 hf4_2) fun hd0 =>
    letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul hS hf2_2) hf3_13) hf4_2) fun hd1 =>
    letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul hS hf2_4) hf3_13) hf4_2) fun hd2 =>
    letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul hS hf2_6) hf3_13) hf4_2) fun hd3 =>
    letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul hS hf2_7) hf3_13) hf4_2) fun hd4 =>
    letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul hS hf2_7) hf3_12) hf4_2) fun hd8 =>
    letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul hS hf2_7) hf3_9) hf4_2) fun hd9 =>
    letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul hS hf2_7) hf3_6) hf4_2) fun hd10 =>
    letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul hS hf2_7) hf3_3) hf4) fun hd11 =>
    letB_rel (hR.rel_mul hS hf2_7) fun hd12 =>
    letB_rel (.cons (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd0 (evalExpr2_rel hR hS hQ hpS hpQ _)))
      (.cons (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd1 (evalExpr2_rel hR hS hQ hpS hpQ _)))
      (.cons (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd2 (evalExpr2_rel hR hS hQ hpS hpQ _)))
      (.cons (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd3 (evalExpr2_rel hR hS hQ hpS hpQ _)))
      (.cons (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd4 (evalExpr2_rel hR hS hQ hpS hpQ _)))
      (.cons (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd4 (evalExpr2_rel hR hS hQ hpS hpQ _)))
      (.cons (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd4 (evalExpr2_rel hR hS hQ hpS hpQ _)))
      (.cons (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd4 (evalExpr2_rel hR hS hQ hpS hpQ _)))
      (.cons (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd8 (evalExpr2_rel hR hS hQ hpS hpQ _)))
      (.cons (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd9 (evalExpr2_rel hR hS hQ hpS hpQ _)))
      (.cons (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd10 (evalExpr2_rel hR hS hQ hpS hpQ _)))
      (.cons (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd11 (evalExpr2_rel hR hS hQ hpS hpQ _)))
      (.cons (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd12 (evalExpr2_rel hR hS hQ hpS hpQ _))) .nil)))))))))))) : URel R _ _) fun hW =>
    letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul (hR.rel_mul (hR.rel_mul hQ hS) hf2_7) hf3_13) (hR.rel_pow 4 (evalExpr2_rel hR hS hQ hpS hpQ fac_5))) (evalExpr2_rel hR hS hQ hpS hpQ fac_6)) fun hD =>
    letB_rel (evalACache_rel hR hS hQ) fun hac =>
    letB_rel (evalGeomSQ_rel hR hS hQ) fun hgsq =>
    ⟨hW, hD, hac, hgsq,
      dotW_rel hR (uTail_rel hac.A0U_t0) hW 1, dotW_rel hR (uTail_rel hac.A0U_t1) hW 1,
      dotW_rel hR hac.A0V_t0 hW 0, dotW_rel hR hac.A0V_t1 hW 0, dotW_rel hR hac.A0V_t2 hW 0,
      dotW_rel hR hac.A0V_t0 hW 1, dotW_rel hR hac.A0V_t1 hW 1, dotW_rel hR hac.A0V_t2 hW 1,
      dotW_rel hR (uMul_rel hR hac.A0V_t0 hac.Bv_SQ) hW 0, dotW_rel hR (uMul_rel hR hac.A0V_t1 hac.Bv_SQ) hW 0,
      dotW_rel hR (uMul_rel hR hac.A0V_t2 hac.Bv_SQ) hW 0,
      dotW_rel hR hac.AY2_t0 hW 0, dotW_rel hR hac.AY2_t1 hW 0,
      dotW_rel hR hac.AY3_t0 hW 1, dotW_rel hR hac.AY3_t1 hW 1,
      dotW_rel hR hac.AX2_t0 hW 0, dotW_rel hR hac.AX2_t1 hW 0, dotW_rel hR hac.AX2_t2 hW 0,
      .cons (.cons (evalExpr3PolyT_rel hR hS hQ hpS hpQ _) (.cons (evalExpr3PolyT_rel hR hS hQ hpS hpQ _) (.cons (evalExpr3PolyT_rel hR hS hQ hpS hpQ _) (.cons (evalExpr3PolyT_rel hR hS hQ hpS hpQ _) (.cons (evalExpr3PolyT_rel hR hS hQ hpS hpQ _) (.cons (evalExpr3PolyT_rel hR hS hQ hpS hpQ _) .nil))))))
        (.cons (.cons (evalExpr3PolyT_rel hR hS hQ hpS hpQ _) (.cons (evalExpr3PolyT_rel hR hS hQ hpS hpQ _) (.cons (evalExpr3PolyT_rel hR hS hQ hpS hpQ _) (.cons (evalExpr3PolyT_rel hR hS hQ hpS hpQ _) (.cons (evalExpr3PolyT_rel hR hS hQ hpS hpQ _) .nil))))) .nil)⟩

private lemma evalGeomT_rel (hR : PolyOpsRel o1 o2 R) {S1 T1 : α} {S2 T2 : β}
    {ca1 ca2 cb1 cb2} {g1 : GeomSQ α} {g2 : GeomSQ β}
    (hS : R S1 S2) (hca : URel R ca1 ca2) (hcb : URel R cb1 cb2) (hg : GeomSQRel R g1 g2) (hT : R T1 T2) :
    GeomTRel R (evalGeomT o1 S1 ca1 cb1 g1 T1) (evalGeomT o2 S2 ca2 cb2 g2 T2) := by
  unfold evalGeomT
  refine letB_rel (hR.rel_mul hT hT) fun hT2 =>
    letB_rel (hR.rel_mul hT2 hT) fun hT3 =>
    letB_rel (hR.rel_sub (hR.rel_sub (hR.rel_add (hR.rel_mul (hR.rel_ofInt (-2)) hT3) (hR.rel_mul (hR.rel_ofInt 6) hT2)) (hR.rel_mul (hR.rel_ofInt 3) hT)) (hR.rel_ofInt 2)) fun hpT =>
    letB_rel (hR.rel_add hg.H0_7_SQ (hR.rel_mul (hR.rel_ofInt 7) hpT)) fun hH0 =>
    letB_rel (hR.rel_mul hH0 hH0) fun hH02 =>
    letB_rel (hR.rel_sub hT (hR.rel_ofInt 3)) fun hTm3 =>
    letB_rel (hR.rel_mul (hR.rel_ofInt (-4)) (hR.rel_mul (hR.rel_mul hTm3 hTm3) hTm3)) fun hAv0 =>
    letB_rel (hR.rel_sub (hR.rel_mul (hR.rel_ofInt 5) hT) (hR.rel_ofInt 9)) fun hT59 =>
    letB_rel (hR.rel_mul hT (hR.rel_mul hT59 hT59)) fun hCv0i =>
    letB_rel (hR.rel_mul (hR.rel_ofInt (-25)) hCv0i) fun hCv0 =>
    letB_rel (hR.rel_mul (hR.rel_ofInt 7) (hR.rel_sub (hR.rel_add (hR.rel_sub (hR.rel_mul (hR.rel_ofInt 143) hT3) (hR.rel_mul (hR.rel_ofInt 828) hT2)) (hR.rel_mul (hR.rel_ofInt 1404) hT)) (hR.rel_ofInt 594))) fun hBv1T =>
    letB_rel (.cons (.cons (hR.rel_add (hR.rel_neg hT) (hR.rel_ofInt 2)) (.cons (hR.rel_ofInt 1) .nil)) .nil : BRel R _ _) fun hv3 =>
    letB_rel (bivMul_rel hR hv3 hv3) fun hv3_2 =>
    letB_rel (bivAdd_rel hR (bivConst_rel (hR.rel_sub hT (hR.rel_ofInt 4)))
        (bivAdd_rel hR (bivSc_rel hR (hR.rel_sub (hR.rel_mul (hR.rel_ofInt 18) hT) (hR.rel_mul (hR.rel_ofInt 4) hT2)) hv3)
          (bivSc_rel hR (hR.rel_mul (hR.rel_ofInt (-27)) hT) hv3_2))) fun hDY2 =>
    letB_rel (bivAdd_rel hR (bivConst_rel (hR.rel_add (hR.rel_mul (hR.rel_ofInt (-4)) hT2) (hR.rel_mul (hR.rel_ofInt 18) hT)))
        (bivSc_rel hR (hR.rel_mul (hR.rel_ofInt (-54)) hT) hv3)) fun hdDY2 =>
    letB_rel (hR.rel_mul hS hT) fun hST =>
    letB_rel (hR.rel_mul (hR.rel_ofInt 2) hST) fun hST2 =>
    letB_rel (bivSc_rel hR hST (bivMul_rel hR hg.DX2 hDY2)) fun hW2 =>
    letB_rel (.cons (.cons hR.rel_zero (.cons (hR.rel_mul (hR.rel_ofInt 42) hT) .nil)) .nil : BRel R _ _) fun hdF54 =>
    letB_rel (bivConst_rel (hR.rel_sub (hR.rel_mul (hR.rel_ofInt 25) hT) (hR.rel_ofInt 45))) fun hLY0 =>
    letB_rel (.cons (.cons (hR.rel_sub (hR.rel_ofInt 45) (hR.rel_mul (hR.rel_ofInt 25) hT)) (.cons (hR.rel_ofInt 27) .nil)) .nil : BRel R _ _) fun hLY1 =>
    letB_rel (bivConst_rel (hR.rel_mul (hR.rel_ofInt 54) hT)) fun hPY41 =>
    letB_rel (ubSub_rel hR (ubSc_rel hR (hR.rel_neg hST2) (ubBmul_rel hR hLY0 hg.dLX_0)) (ubSc_rel hR hT (ubBmul_rel hR hLY0 hg.LX_27))) fun hbr00 =>
    letB_rel (ubSub_rel hR (ubSc_rel hR (hR.rel_neg hST2) (ubBmul_rel hR hLY1 hg.dLX_0)) (ubSc_rel hR hT (ubBmul_rel hR hLY1 hg.LX_27))) fun hbr10 =>
    letB_rel (ubSc_rel hR (hR.rel_neg hST2) (ubBmul_rel hR hLY0 hg.dLX_1)) fun hbr01 =>
    letB_rel (ubSc_rel hR (hR.rel_neg hST2) (ubBmul_rel hR hLY1 hg.dLX_1)) fun hbr11 =>
    letB_rel (ubSc_rel hR (hR.rel_neg hST2) (ubBmul_rel hR hLY0 hg.dLX_3)) fun hbr03 =>
    letB_rel (ubSc_rel hR (hR.rel_neg hST2) (ubBmul_rel hR hLY1 hg.dLX_3)) fun hbr13 =>
    letB_rel (ubSc_rel hR (hR.rel_mul (hR.rel_ofInt 27) hST2) hg.LX_27) fun hbr14 =>
    letB_rel (ubSc_rel hR hST (ubAdd_rel hR (ubBmul_rel hR hg.dF5_3 (ubNeg_rel hR (ubBmul_rel hR hPY41 hg.PX_0))) (ubBmul_rel hR hg.dF5_0 (ubBmul_rel hR hPY41 hg.PX_3)))) fun hom0 =>
    letB_rel (ubSc_rel hR hST (ubAdd_rel hR (ubBmul_rel hR hg.dF5_3 (ubNeg_rel hR (ubBmul_rel hR hPY41 hg.PX_1))) (ubBmul_rel hR hg.dF5_1 (ubBmul_rel hR hPY41 hg.PX_3)))) fun hom1 =>
    letB_rel (ubSc_rel hR hST (ubSub_rel hR (ubBmul_rel hR hg.dF5_3 (ubBmul_rel hR hdDY2 hbr00)) (ubBmul_rel hR hg.dF5_0 (ubBmul_rel hR hdDY2 hbr03)))) fun hdYF00 =>
    letB_rel (ubSc_rel hR hST (ubSub_rel hR (ubBmul_rel hR hg.dF5_3 (ubBmul_rel hR hdDY2 hbr01)) (ubBmul_rel hR hg.dF5_1 (ubBmul_rel hR hdDY2 hbr03)))) fun hdYF01 =>
    letB_rel (ubSc_rel hR hST (ubSub_rel hR (ubBmul_rel hR hg.dF5_3 (ubBmul_rel hR hdDY2 hbr10)) (ubBmul_rel hR hg.dF5_0 (ubBmul_rel hR hdDY2 hbr13)))) fun hdYF10 =>
    letB_rel (ubSc_rel hR hST (ubSub_rel hR (ubBmul_rel hR hg.dF5_3 (ubBmul_rel hR hdDY2 hbr11)) (ubBmul_rel hR hg.dF5_1 (ubBmul_rel hR hdDY2 hbr13)))) fun hdYF11 =>
    letB_rel (ubSc_rel hR hST (ubBmul_rel hR hdF54 (ubSub_rel hR (ubBmul_rel hR hg.dDX2_dS hbr03) (ubBmul_rel hR hg.dDX2_dx hbr00)))) fun hdXF00 =>
    letB_rel (ubSc_rel hR hST (ubBmul_rel hR hdF54 (ubSub_rel hR (ubBmul_rel hR hg.dDX2_dQ hbr03) (ubBmul_rel hR hg.dDX2_dx hbr01)))) fun hdXF01 =>
    letB_rel (ubBmul_rel hR hg.DX2 hdYF00) fun hQX00 =>
    letB_rel (ubBmul_rel hR hg.DX2 hdYF01) fun hQX01 =>
    letB_rel (ubBmul_rel hR hg.DX2 (ubSub_rel hR hdYF10 (ubBmul_rel hR hDY2 hom0))) fun hQX10 =>
    letB_rel (ubBmul_rel hR hg.DX2 (ubSub_rel hR hdYF11 (ubBmul_rel hR hDY2 hom1))) fun hQX11 =>
    letB_rel (ubNeg_rel hR (ubBmul_rel hR hDY2 hdXF00)) fun hQY00 =>
    letB_rel (ubNeg_rel hR (ubBmul_rel hR hDY2 hdXF01)) fun hQY01 =>
    letB_rel (ubSc_rel hR (hR.rel_ofInt 2) (ubBmul_rel hR hW2 (ubBmul_rel hR hdF54 hbr03))) fun hEB0 =>
    letB_rel (ubSc_rel hR (hR.rel_ofInt 2) (ubBmul_rel hR hW2 (ubSub_rel hR (ubBmul_rel hR hdF54 hbr13) (ubBmul_rel hR hg.dF5_3 hbr14)))) fun hEB1 =>
    letB_rel (Ra := fun p q => BRel R p.1 q.1 ∧ UBRel R p.2 q.2)
      (ubSynDiv1Rem_rel hR (ubSub_rel hR (ubMulU_rel hR hcb hQX00) (ubMulU_rel hR hca hQX01))) fun hdiv0 =>
    letB_rel (Ra := fun p q => BRel R p.1 q.1 ∧ UBRel R p.2 q.2)
      (ubSynDiv1Rem_rel hR (ubSub_rel hR (ubMulU_rel hR hcb hQX10) (ubMulU_rel hR hca hQX11))) fun hdiv1 =>
    letB_rel (ubSub_rel hR (ubMulU_rel hR hcb hQY00) (ubMulU_rel hR hca hQY01)) fun hQYd0 =>
    letB_rel (hR.rel_mul (hR.rel_ofInt 4) (hR.rel_mul hg.S2 hT2)) fun hc4 =>
    letB_rel (.cons (.cons (.cons (hR.rel_mul hc4 (list_getD_rel hR hg.qC_63 0)) .nil) (.cons (.cons (hR.rel_mul hc4 (list_getD_rel hR hg.qEx_63 0)) .nil) .nil))
        (.cons (.cons (.cons (hR.rel_mul hc4 (list_getD_rel hR hg.qC_63 1)) .nil) (.cons (.cons (hR.rel_mul hc4 (list_getD_rel hR hg.qEx_63 1)) .nil) .nil)) .nil) : UBRel R _ _) fun hqE =>
    letB_rel (ubBmul_rel hR hDY2 hqE) fun hDYqE =>
    letB_rel (ubAdd_rel hR (ubNeg_rel hR hQYd0) (ubSc_rel hR (hR.rel_mul (hR.rel_ofInt 189) hCv0) (ubShift_rel hDYqE))) fun hqY0 =>
    ⟨hH0, hH02, hAv0, hCv0i, hCv0, hBv1T, hDY2, hdiv0.1, hdiv1.1, hdiv0.2, hdiv1.2, hqY0, hDYqE,
      ubAdd_rel hR (ubSc_rel hR (hR.rel_mul (hR.rel_ofInt (-9)) hH0) hdiv0.2) (ubSc_rel hR (hR.rel_ofInt 63) (ubMulU_rel hR hg.qC_63 hEB0)),
      ubAdd_rel hR (ubSc_rel hR (hR.rel_mul (hR.rel_ofInt 9) hH0) (ubMulU_rel hR hg.A1_1_27 hqY0))
        (ubShift_rel (ubAdd_rel hR
          (ubSc_rel hR (hR.rel_mul (hR.rel_ofInt 9) hH0) (ubSub_rel hR (ubSc_rel hR hAv0 hdiv0.2) (ubSc_rel hR hCv0 hdiv1.2)))
          (ubSc_rel hR (hR.rel_ofInt 63) (ubMulU_rel hR hg.qC_63 (ubSub_rel hR (ubSc_rel hR hCv0 hEB1) (ubSc_rel hR hAv0 hEB0)))))),
      ubSub_rel hR (ubAdd_rel hR (ubSc_rel hR (hR.rel_mul (hR.rel_ofInt (-1701)) hH0) (ubMulU_rel hR hg.A1_1_27 hDYqE))
        (ubSc_rel hR (hR.rel_mul (hR.rel_ofInt 9) hH0) hdiv1.2)) (ubSc_rel hR (hR.rel_ofInt 63) (ubMulU_rel hR hg.qC_63 hEB1))⟩

private lemma evalBTot_rel (hR : PolyOpsRel o1 o2 R) {c1 : SQCache α} {c2 : SQCache β}
    {g1 : GeomT α} {g2 : GeomT β} {T1 : α} {T2 : β}
    (hc : SQCacheRel R c1 c2) (hg : GeomTRel R g1 g2) (hT : R T1 T2) :
    BRel R (evalBTot o1 c1 g1 T1) (evalBTot o2 c2 g2 T2) := by
  unfold evalBTot
  refine letB_rel (hR.rel_mul hT hT) fun hT2 =>
    letB_rel (uAdd_rel hR hc.d_A0U_t0 (uSc_rel hR hT hc.d_A0U_t1)) fun hdU =>
    letB_rel (uAdd_rel hR (uAdd_rel hR hc.d_A0V_t0 (uSc_rel hR hT hc.d_A0V_t1)) (uSc_rel hR hT2 hc.d_A0V_t2)) fun hdV =>
    letB_rel (uAdd_rel hR (uAdd_rel hR hc.d_A0V_U_t0 (uSc_rel hR hT hc.d_A0V_U_t1)) (uSc_rel hR hT2 hc.d_A0V_U_t2)) fun hdVU =>
    letB_rel (uAdd_rel hR (uAdd_rel hR (uAdd_rel hR hc.d_A0VBv_t0 (uSc_rel hR hT hc.d_A0VBv_t1)) (uSc_rel hR hT2 hc.d_A0VBv_t2)) (uSc_rel hR hg.Bv1_T_1701 hdVU)) fun hdVB =>
    letB_rel (uAdd_rel hR hc.d_AY2_t0 (uSc_rel hR hT hc.d_AY2_t1)) fun hdY2 =>
    letB_rel (uAdd_rel hR hc.d_AY3_t0 (uSc_rel hR hT hc.d_AY3_t1)) fun hdY3 =>
    letB_rel (uAdd_rel hR (uAdd_rel hR hc.d_AX2_t0 (uSc_rel hR hT hc.d_AX2_t1)) (uSc_rel hR hT2 hc.d_AX2_t2)) fun hdX2 =>
    bivAdd_rel hR (bivAdd_rel hR (bivAdd_rel hR
        (combineBivDot_rel hR (ubSub_rel hR hg.q1_0_div_sc hg.q1_2_div_sc) (uSc_rel hR (hR.rel_mul (hR.rel_ofInt 7) hg.Cv0_243) hdU))
        (combineBivDot_rel hR hg.DY2_qE_63 (uSc_rel hR (hR.rel_mul (hR.rel_ofInt 45927) (hR.rel_mul hg.Cv0_243 hg.H0_7_2)) hdY3)))
        (combineBivDot_rel hR hg.q1_1_sc (uSc_rel hR (hR.rel_ofInt 7) hdV)))
      (bivAdd_rel hR (bivSc_rel hR (hR.rel_mul (hR.rel_ofInt 243) hg.H0_7_2)
        (bivAdd_rel hR (combineBivDot_rel hR hg.qY_0_321489 hdY2) (combineBivDot_rel hR hg.qX_0_sc hdX2)))
        (bivNeg_rel hR (combineBivDot_rel hR hg.q1_0_div_sc hdVB)))

private lemma evalTStep_rel (hR : PolyOpsRel o1 o2 R) {S1 T1 : α} {S2 T2 : β}
    {c1 : SQCache α} {c2 : SQCache β}
    (hS : R S1 S2) (hc : SQCacheRel R c1 c2) (hT : R T1 T2) :
    BRel R (evalTStep o1 S1 c1 T1) (evalTStep o2 S2 c2 T2) := by
  unfold evalTStep
  refine letB_rel (evalGeomT_rel hR hS hc.ac.ca_p hc.ac.cb_p hc.gsq hT) fun hgt =>
    letB_rel (evalBTot_rel hR hc hgt hT) fun hB =>
    letB_rel (hR.rel_mul (hR.rel_ofInt 21) hS) fun hs21 =>
    letB_rel (hR.rel_neg (hR.rel_mul (hR.rel_ofInt 21) hT)) fun ht21 =>
    letB_rel (hR.rel_neg hgt.H0_7) fun hnh0 =>
    letB_rel (bivRedOnce_rel hR hs21 ht21 hnh0 (bivRedOnce_rel hR hs21 ht21 hnh0 hB)) fun hlhs =>
    letB_rel (hR.rel_mul (hR.rel_ofInt C_RHS_int) (hR.rel_mul (hR.rel_mul hs21 hs21) (hR.rel_mul hgt.Cv0_int hc.D_div_L2))) fun hrsc =>
    letB_rel ?_ fun hrraw =>
    bivSub_rel hR hlhs (bivSc_rel hR hrsc hrraw)
  have hmap : ∀ {l1 l2}, List.Forall₂ (List.Forall₂ (URel R)) l1 l2 →
      BRel R (l1.map fun row => row.map fun p => uEval o1 p T1)
        (l2.map fun row => row.map fun p => uEval o2 p T2) := by
    intro l1 l2 hl
    induction hl with
    | nil => exact .nil
    | cons hrow _ ih =>
        refine .cons ?_ ih
        induction hrow with
        | nil => exact .nil
        | cons hp _ ihp => exact .cons (uEval_rel hR hT hp) ihp
  exact hmap hc.RQ5_T

end CacheRel

-- Exact `k5Ops` / `A_C` bridge: matching `evalACache`, `evalGeomT`, and `evalBTot` to `SheetCalculus` and `p4_AC`!

private def cacheK : SQCache K5 := evalSQCache k5Ops S_K Q_K
private def gtK : GeomT K5 := evalGeomT k5Ops S_K cacheK.ac.ca_p cacheK.ac.cb_p cacheK.gsq T_K

private lemma polyC_C (c : K5) : polyC (Polynomial.C c) = ιC_K5 c := by
  simp [polyC, ιC_K5, toRat]

private lemma polyC_X : polyC (Polynomial.X : K5[X]) = U_C := by
  simp [polyC, U_C, toRat]

private lemma polyC_add (p q : K5[X]) : polyC (p + q) = polyC p + polyC q := by
  simp [polyC]

private lemma polyC_sub (p q : K5[X]) : polyC (p - q) = polyC p - polyC q := by
  simp [polyC]

private lemma polyC_neg (p : K5[X]) : polyC (-p) = -polyC p := by
  simp [polyC]

private lemma polyC_mul (p q : K5[X]) : polyC (p * q) = polyC p * polyC q := by
  simp [polyC]

private lemma polyC_pow (p : K5[X]) (n : ℕ) : polyC (p ^ n) = polyC p ^ n := by
  simp [polyC]

-- Pure-ring identities for `dHS_243`, `dHQ0_27`, `dHS_bi_243`, `dHQ1_bi_189`
section PureRingBridge
variable {R : Type*} [Field R] [CharZero R]

private lemma dHS_243_ring (a b U : R) :
    -25 * ((5 * a - 9 * b) * (15 * a - 9 * b)) +
    U * (429 * (a * a) - 1656 * (a * b) + 1404 * (b * b)) +
    U * (U * (-12 * ((a - 3 * b) * (a - 3 * b)))) = 243 * q1_a2 a b U 1 := by
  simp only [q1_a2, dH_dS]; ring

private lemma dHQ0_27_ring (a b U : R) :
    50 * (a * (5 * a - 9 * b)) +
    U * (-92 * (a * a) + 312 * (a * b) - 198 * (b * b)) +
    U * (U * (4 * ((a - 3 * b) * (a - 3 * b)))) = 27 * q2_b2 a b U 1 := by
  simp only [q2_b2, dH_dQ]; ring

private lemma dHS_bi_243_ring (S Q a b U : R) :
    -25 * ((15 * S - 9 * Q) * (5 * a - 9 * b) + (5 * S - 9 * Q) * (15 * a - 9 * b)) +
    U * (858 * S * a - 1656 * (S * b + Q * a) + 2808 * Q * b) +
    U * (U * (-24 * (S - 3 * Q) * (a - 3 * b))) = 243 * q1_a1 a b S Q U 1 := by
  simp only [q1_a1, dH_dS]; ring

private lemma dHQ1_bi_189_ring (S Q a b U : R) :
    350 * ((10 * S - 9 * Q) * a - 9 * S * b) +
    U * (7 * (-184 * S * a + 312 * (S * b + Q * a) - 396 * Q * b) + 270 * b) +
    U * (U * (56 * (S - 3 * Q) * (a - 3 * b))) = 189 * q2_b1 a b S Q U 1 := by
  simp only [q2_b1, dH_dQ]; ring

private lemma B1_of_eq_Av0_Cv0 (T U V : R) :
    B1_of T U V = 9 * U * ((-(4 / 243 : R) * (T - 3) ^ 3) * V - (-(25 / 243 : R) * T * (5 * T - 9) ^ 2)) := by
  simp only [B1_of]; ring

private lemma E0_V_split (S Q T U V : R) :
    H_cub S Q T 1 U V =
      V * (U * H0_of S Q T + u_of U * A1_of S Q U 1) +
      (V - 1) * U * ((-(4 / 243 : R) * (T - 3) ^ 3) * V - (-(25 / 243 : R) * T * (5 * T - 9) ^ 2)) := by
  have h1 := H_cub_eq_H0_A1_B1 S Q T U V
  have hA : A1_of S Q U V = V * A1_of S Q U 1 := by simp only [A1_of]; ring
  rw [h1, hA, B1_of_eq_Av0_Cv0, v_of]
  ring

private lemma cA1_dot_V1_ring (S Q T U : R) :
    let ca := q1_a0 S Q U 1; let cb := q2_b0 S Q U 1
    let qC0 : R := -5250 * S ^ 4 + 30450 * S ^ 3 * Q - 64050 * S ^ 2 * Q ^ 2 + 63000 * S * Q ^ 3 - 28350 * Q ^ 4 +
      6250 * S ^ 2 * Q - 15000 * S * Q ^ 2 + 6750 * Q ^ 3 + 6250 * S ^ 2 - 15000 * S * Q + 6750 * Q ^ 2
    let qC1 : R := 336 * S ^ 4 - 2856 * S ^ 3 * Q + 8484 * S ^ 2 * Q ^ 2 - 10080 * S * Q ^ 3 + 3780 * Q ^ 4 -
      40 * S ^ 2 * Q + 240 * S * Q ^ 2 - 360 * Q ^ 3 - 40 * S ^ 2 + 240 * S * Q - 360 * Q ^ 2
    let qC := (qC0 + qC1 * U) / 63
    (H0_of S Q T * dA1_fn 0 S Q U 1 - A1_of S Q U 1 * dH0_fn 0 S Q T) * cb -
    (H0_of S Q T * dA1_fn 1 S Q U 1 - A1_of S Q U 1 * dH0_fn 1 S Q T) * ca =
      qC * (U * H0_of S Q T + u_of U * A1_of S Q U 1) := by
  intro ca cb qC0 qC1 qC
  -- Factor linearly in `H0 := H0_of S Q T`!
  set H0 := H0_of S Q T
  have h1 : dA1_fn 0 S Q U 1 * cb - dA1_fn 1 S Q U 1 * ca = qC * U := by
    simp only [dA1_fn, cb, ca, q2_b0, q1_a0, dH_dQ, dH_dS, qC, qC0, qC1]; ring
  have h2 : -(dH0_fn 0 S Q T * cb - dH0_fn 1 S Q T * ca) = qC * u_of U := by
    simp only [dH0_fn, cb, ca, q2_b0, q1_a0, dH_dQ, dH_dS, qC, qC0, qC1, u_of]; ring
  linear_combination H0 * h1 + A1_of S Q U 1 * h2

private lemma QY_dot_V1_ring (S Q T x y U : R) :
    let ca := q1_a0 S Q U 1; let cb := q2_b0 S Q U 1
    let qC0 : R := -5250 * S ^ 4 + 30450 * S ^ 3 * Q - 64050 * S ^ 2 * Q ^ 2 + 63000 * S * Q ^ 3 - 28350 * Q ^ 4 +
      6250 * S ^ 2 * Q - 15000 * S * Q ^ 2 + 6750 * Q ^ 3 + 6250 * S ^ 2 - 15000 * S * Q + 6750 * Q ^ 2
    let qC1 : R := 336 * S ^ 4 - 2856 * S ^ 3 * Q + 8484 * S ^ 2 * Q ^ 2 - 10080 * S * Q ^ 3 + 3780 * Q ^ 4 -
      40 * S ^ 2 * Q + 240 * S * Q ^ 2 - 360 * Q ^ 3 - 40 * S ^ 2 + 240 * S * Q - 360 * Q ^ 2
    let qEx0 : R := 6090 * S ^ 3 - 25620 * S ^ 2 * Q + 34650 * S * Q ^ 2 - 20790 * Q ^ 3 -
      6750 * S * Q + 4050 * Q ^ 2 - 6750 * S + 4050 * Q
    let qEx1 : R := -420 * S ^ 3 + 2940 * S ^ 2 * Q - 6300 * S * Q ^ 2 + 3780 * Q ^ 3
    let qE := 4 * S ^ 2 * T ^ 2 * ((qC0 + qC1 * U) + x * (qEx0 + qEx1 * U)) / 63
    QY_num S Q T x y U 1 0 * cb - QY_num S Q T x y U 1 1 * ca =
      DY2_of T y * qE * (u_of U * A1_of S Q U 1 - 3 * U * (S * x ^ 2 + T * y ^ 2)) := by
  intro ca cb qC0 qC1 qEx0 qEx1 qE
  have hLY1 : LY_of T y 1 = y := by simp only [LY_of, v3_of, v_of]; ring
  have hdLY1 : ∀ k : Fin 5, dLY_fn k (1 : R) = match k with | 4 => 1 | _ => 0 := by
    intro k; fin_cases k <;> simp [dLY_fn, v_of] <;> ring
  -- Split `(DX2 * Omega_F - dDX2_F)` dotted with `(cb, -ca)` by `y ^ 2` and `y ^ 0`!
  have hy2 : -S * T * (6 * T) *
      ((dDX2_fn 0 S Q x * (-2 * S * T * dLX_fn 3 U) - dDX2_fn 3 S Q x * (-T * LX_of S Q x U - 2 * S * T * dLX_fn 0 U)) * cb -
       (dDX2_fn 1 S Q x * (-2 * S * T * dLX_fn 3 U) - dDX2_fn 3 S Q x * (-2 * S * T * dLX_fn 1 U)) * ca) =
      qE * (-3 * U * T) := by
    simp only [dDX2_fn, dLX_fn, LX_of, u3_of, u_of, cb, ca, q2_b0, q1_a0, dH_dQ, dH_dS, qE, qC0, qC1, qEx0, qEx1]
    ring
  have hy0 :
      DX2_of S Q x * (S * T * ((6 * S * x) * (-(2 / 9 : R) * T * (-25 * S * U + 15 * Q * U + 9 * x * U + 25 * S - 15 * Q)) +
        (3 * x ^ 2 + dH0_fn 0 S Q T) * (4 * S * T * U)) * cb -
        S * T * ((6 * S * x) * (-(2 / 9 : R) * T * (30 * (U - 1) * S)) + dH0_fn 1 S Q T * (4 * S * T * U)) * ca) -
      S * T * (((6 * S * x) * (-dDX2_fn 0 S Q x * (2 * S * T * LX_of S Q x U)) +
          (3 * x ^ 2 + dH0_fn 0 S Q T) * (dDX2_fn 3 S Q x * (2 * S * T * LX_of S Q x U))) * cb -
        ((6 * S * x) * (-dDX2_fn 1 S Q x * (2 * S * T * LX_of S Q x U)) +
          dH0_fn 1 S Q T * (dDX2_fn 3 S Q x * (2 * S * T * LX_of S Q x U))) * ca) =
      qE * (u_of U * A1_of S Q U 1 - 3 * U * S * x ^ 2) := by
    simp only [DX2_of, dDX2_fn, dH0_fn, LX_of, u3_of, u_of, A1_of, cb, ca, q2_b0, q1_a0, dH_dQ, dH_dS,
      qE, qC0, qC1, qEx0, qEx1]
    ring
  have hinner :
      (DX2_of S Q x * Omega_F S Q T x y U 1 0 - dDX2_F S Q T x y U 1 0) * cb -
      (DX2_of S Q x * Omega_F S Q T x y U 1 1 - dDX2_F S Q T x y U 1 1) * ca =
      qE * (u_of U * A1_of S Q U 1 - 3 * U * (S * x ^ 2 + T * y ^ 2)) := by
    have hd4 : dDX2_fn 4 S Q x = 0 := rfl
    have hdX4 : dLX_fn 4 U = 0 := rfl
    simp only [Omega_F, dDX2_F, F_contract, om_fn, br_fn, dF5_fn, hLY1, hdLY1, hd4, hdX4,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, mul_zero, zero_mul, add_zero, zero_add, sub_zero]
    linear_combination y ^ 2 * hy2 + hy0
  simp only [QY_num]
  linear_combination DY2_of T y * hinner

private lemma QX_dot_U1_ring (S Q T x y V : R) :
    let ca := q1_a0 S Q 1 1; let cb := q2_b0 S Q 1 1
    QX_num S Q T x y 1 V 0 * cb - QX_num S Q T x y 1 V 1 * ca = 0 := by
  intro ca cb
  have hca : ca = dH0_fn 0 S Q T := by simp only [ca, q1_a0, dH_dS, dH0_fn]; ring
  have hcb : cb = dH0_fn 1 S Q T := by simp only [cb, q2_b0, dH_dQ, dH0_fn]; ring
  have hLX1 : LX_of S Q x 1 = x := by simp only [LX_of, u3_of, u_of]; ring
  have hdLX1 : ∀ k : Fin 5, dLX_fn k (1 : R) = match k with | 3 => 1 | _ => 0 := by
    intro k; fin_cases k <;> simp [dLX_fn, u_of] <;> ring
  rw [hca, hcb]
  simp only [QX_num, Omega_F, dDY2_F, F_contract, om_fn, br_fn, dF5_fn, dDY2_fn, dLY_fn, hLX1, hdLX1,
    Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  ring

private lemma QY_QX_U0V0_ring (S Q T x y : R) :
    let ca := q1_a0 S Q 0 1; let cb := q2_b0 S Q 0 1
    (QY_num S Q T x y 0 0 0 * cb - QY_num S Q T x y 0 0 1 * ca = 0) ∧
    (QX_num S Q T x y 0 0 0 * cb - QX_num S Q T x y 0 0 1 * ca = 0) ∧
    (EB_of S Q T x y 0 0 = 0) := by
  intro ca cb
  have hbr0 : br_fn 0 S Q T x y 0 0 * cb - br_fn 1 S Q T x y 0 0 * ca = 0 := by
    simp only [br_fn, LX_of, LY_of, dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of, ca, cb, q1_a0, q2_b0, dH_dS, dH_dQ]
    ring
  have hbr3 : br_fn 3 S Q T x y 0 0 = 0 := by simp [br_fn, dLX_fn, dLY_fn]
  have hbr4 : br_fn 4 S Q T x y 0 0 = 0 := by simp [br_fn, dLX_fn, dLY_fn]
  have hom0 : Omega_F S Q T x y 0 0 0 = 0 := by simp [Omega_F, F_contract, om_fn]
  have hom1 : Omega_F S Q T x y 0 0 1 = 0 := by simp [Omega_F, F_contract, om_fn]
  refine ⟨?_, ?_, ?_⟩
  · have hd4 : dDX2_fn 4 S Q x = 0 := rfl
    simp only [QY_num, hom0, hom1, dDX2_F, F_contract, hbr3, hbr4, hd4, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    linear_combination DY2_of T y * S * T * dF5_fn 4 S Q T x y * dDX2_fn 3 S Q x * hbr0
  · have hd3 : dDY2_fn 3 T y = 0 := rfl
    simp only [QX_num, hom0, hom1, dDY2_F, F_contract, hbr3, hbr4, hd3, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    linear_combination DX2_of S Q x * S * T * dF5_fn 3 S Q T x y * dDY2_fn 4 T y * hbr0
  · simp [EB_of, hbr3, hbr4]

end PureRingBridge

-- Fast O(N) `letB_intro` structural decomposition of `cacheK` (`evalSQCache k5Ops S_K Q_K`)
private lemma cacheK_props :
    cacheK.ac = evalACache k5Ops S_K Q_K ∧
    cacheK.gsq = evalGeomSQ k5Ops S_K Q_K ∧
    cacheK.W =
      [evalSQ_K5 (W_num_expr 0), evalSQ_K5 (W_num_expr 1), evalSQ_K5 (W_num_expr 2),
       evalSQ_K5 (W_num_expr 3), evalSQ_K5 (W_num_expr 4), evalSQ_K5 (W_num_expr 5),
       evalSQ_K5 (W_num_expr 6), evalSQ_K5 (W_num_expr 7), evalSQ_K5 (W_num_expr 8),
       evalSQ_K5 (W_num_expr 9), evalSQ_K5 (W_num_expr 10), evalSQ_K5 (W_num_expr 11),
       evalSQ_K5 (W_num_expr 12)] ∧
    evalSQ_K5 D_all_expr = cacheK.D_div_L2 * L_K ^ 2 ∧
    evalBivLK5 (cacheK.RQ5_T.map fun row => row.map fun p => uEval k5Ops p T_K) = evalBivK5 RQ5_biv ∧
    (cacheK.d_A0U_t0 = dotW k5Ops (uTail cacheK.ac.A0U_t0) cacheK.W 1 ∧
     cacheK.d_A0U_t1 = dotW k5Ops (uTail cacheK.ac.A0U_t1) cacheK.W 1 ∧
     cacheK.d_A0V_t0 = dotW k5Ops cacheK.ac.A0V_t0 cacheK.W 0 ∧
     cacheK.d_A0V_t1 = dotW k5Ops cacheK.ac.A0V_t1 cacheK.W 0 ∧
     cacheK.d_A0V_t2 = dotW k5Ops cacheK.ac.A0V_t2 cacheK.W 0 ∧
     cacheK.d_A0V_U_t0 = dotW k5Ops cacheK.ac.A0V_t0 cacheK.W 1 ∧
     cacheK.d_A0V_U_t1 = dotW k5Ops cacheK.ac.A0V_t1 cacheK.W 1 ∧
     cacheK.d_A0V_U_t2 = dotW k5Ops cacheK.ac.A0V_t2 cacheK.W 1 ∧
     cacheK.d_A0VBv_t0 = dotW k5Ops (uMul k5Ops cacheK.ac.A0V_t0 cacheK.ac.Bv_SQ) cacheK.W 0 ∧
     cacheK.d_A0VBv_t1 = dotW k5Ops (uMul k5Ops cacheK.ac.A0V_t1 cacheK.ac.Bv_SQ) cacheK.W 0 ∧
     cacheK.d_A0VBv_t2 = dotW k5Ops (uMul k5Ops cacheK.ac.A0V_t2 cacheK.ac.Bv_SQ) cacheK.W 0 ∧
     cacheK.d_AY2_t0 = dotW k5Ops cacheK.ac.AY2_t0 cacheK.W 0 ∧
     cacheK.d_AY2_t1 = dotW k5Ops cacheK.ac.AY2_t1 cacheK.W 0 ∧
     cacheK.d_AY3_t0 = dotW k5Ops cacheK.ac.AY3_t0 cacheK.W 1 ∧
     cacheK.d_AY3_t1 = dotW k5Ops cacheK.ac.AY3_t1 cacheK.W 1 ∧
     cacheK.d_AX2_t0 = dotW k5Ops cacheK.ac.AX2_t0 cacheK.W 0 ∧
     cacheK.d_AX2_t1 = dotW k5Ops cacheK.ac.AX2_t1 cacheK.W 0 ∧
     cacheK.d_AX2_t2 = dotW k5Ops cacheK.ac.AX2_t2 cacheK.W 0) := by
  let P : SQCache K5 → Prop := fun c =>
    c.ac = evalACache k5Ops S_K Q_K ∧
    c.gsq = evalGeomSQ k5Ops S_K Q_K ∧
    c.W =
      [evalSQ_K5 (W_num_expr 0), evalSQ_K5 (W_num_expr 1), evalSQ_K5 (W_num_expr 2),
       evalSQ_K5 (W_num_expr 3), evalSQ_K5 (W_num_expr 4), evalSQ_K5 (W_num_expr 5),
       evalSQ_K5 (W_num_expr 6), evalSQ_K5 (W_num_expr 7), evalSQ_K5 (W_num_expr 8),
       evalSQ_K5 (W_num_expr 9), evalSQ_K5 (W_num_expr 10), evalSQ_K5 (W_num_expr 11),
       evalSQ_K5 (W_num_expr 12)] ∧
    evalSQ_K5 D_all_expr = c.D_div_L2 * L_K ^ 2 ∧
    evalBivLK5 (c.RQ5_T.map fun row => row.map fun p => uEval k5Ops p T_K) = evalBivK5 RQ5_biv ∧
    (c.d_A0U_t0 = dotW k5Ops (uTail c.ac.A0U_t0) c.W 1 ∧
     c.d_A0U_t1 = dotW k5Ops (uTail c.ac.A0U_t1) c.W 1 ∧
     c.d_A0V_t0 = dotW k5Ops c.ac.A0V_t0 c.W 0 ∧
     c.d_A0V_t1 = dotW k5Ops c.ac.A0V_t1 c.W 0 ∧
     c.d_A0V_t2 = dotW k5Ops c.ac.A0V_t2 c.W 0 ∧
     c.d_A0V_U_t0 = dotW k5Ops c.ac.A0V_t0 c.W 1 ∧
     c.d_A0V_U_t1 = dotW k5Ops c.ac.A0V_t1 c.W 1 ∧
     c.d_A0V_U_t2 = dotW k5Ops c.ac.A0V_t2 c.W 1 ∧
     c.d_A0VBv_t0 = dotW k5Ops (uMul k5Ops c.ac.A0V_t0 c.ac.Bv_SQ) c.W 0 ∧
     c.d_A0VBv_t1 = dotW k5Ops (uMul k5Ops c.ac.A0V_t1 c.ac.Bv_SQ) c.W 0 ∧
     c.d_A0VBv_t2 = dotW k5Ops (uMul k5Ops c.ac.A0V_t2 c.ac.Bv_SQ) c.W 0 ∧
     c.d_AY2_t0 = dotW k5Ops c.ac.AY2_t0 c.W 0 ∧
     c.d_AY2_t1 = dotW k5Ops c.ac.AY2_t1 c.W 0 ∧
     c.d_AY3_t0 = dotW k5Ops c.ac.AY3_t0 c.W 1 ∧
     c.d_AY3_t1 = dotW k5Ops c.ac.AY3_t1 c.W 1 ∧
     c.d_AX2_t0 = dotW k5Ops c.ac.AX2_t0 c.W 0 ∧
     c.d_AX2_t1 = dotW k5Ops c.ac.AX2_t1 c.W 0 ∧
     c.d_AX2_t2 = dotW k5Ops c.ac.AX2_t2 c.W 0)
  suffices h : P (evalSQCache k5Ops S_K Q_K) from h
  unfold evalSQCache
  refine letB_intro fun pS hpS => letB_intro fun pQ hpQ =>
    letB_intro fun f2 hf2 => letB_intro fun f3 hf3 => letB_intro fun f4 hf4 =>
    letB_intro fun f2_2 hf2_2 => letB_intro fun f2_4 hf2_4 => letB_intro fun f2_6 hf2_6 => letB_intro fun f2_7 hf2_7 =>
    letB_intro fun f3_3 hf3_3 => letB_intro fun f3_6 hf3_6 => letB_intro fun f3_9 hf3_9 =>
    letB_intro fun f3_12 hf3_12 => letB_intro fun f3_13 hf3_13 => letB_intro fun f4_2 hf4_2 =>
    letB_intro fun d0 hd0 => letB_intro fun d1 hd1 => letB_intro fun d2 hd2 => letB_intro fun d3 hd3 =>
    letB_intro fun d4 hd4 => letB_intro fun d8 hd8 => letB_intro fun d9 hd9 => letB_intro fun d10 hd10 =>
    letB_intro fun d11 hd11 => letB_intro fun d12 hd12 => letB_intro fun W hW =>
    letB_intro fun D_div_L2 hDdiv => letB_intro fun ac hac => letB_intro fun gsq hgsq => ?_
  dsimp only [P]
  have hX0 : evalP3K5 (MvPolynomial.X 0) = S_K := by simp [evalP3K5, v3K5]
  have hX1 : evalP3K5 (MvPolynomial.X 1) = Q_K := by simp [evalP3K5, v3K5]
  have hX2 : evalP3K5 (MvPolynomial.X 2) = T_K := by simp [evalP3K5, v3K5]
  have hev2 (e : Expr) : evalExpr2 k5Ops S_K Q_K pS pQ e = evalSQ_K5 e := by
    rw [hpS, hpQ]
    have h := evalExpr2_rel poly3ToK5Rel hX0 hX1
      (powList_rel poly3ToK5Rel hX0 30 (poly3ToK5Rel.rel_ofInt 1))
      (powList_rel poly3ToK5Rel hX1 37 (poly3ToK5Rel.rel_ofInt 1)) e
    rw [evalExpr2_poly3_eq, evalP3K5_ringEval_SQ] at h; exact h.symm
  have hevT (e : Expr) : uEval k5Ops (evalExpr3PolyT k5Ops S_K Q_K pS pQ e) T_K = ringEval vK5 e := by
    rw [hpS, hpQ]
    have h := uEval_rel poly3ToK5Rel hX2
      (evalExpr3PolyT_rel poly3ToK5Rel hX0 hX1
        (powList_rel poly3ToK5Rel hX0 30 (poly3ToK5Rel.rel_ofInt 1))
        (powList_rel poly3ToK5Rel hX1 37 (poly3ToK5Rel.rel_ofInt 1)) e)
    rw [uEval_evalExpr3PolyT_P3Z, evalP3K5_ringEval_SQT] at h; exact h.symm
  have hf := fac_K5_eqs
  have hf2' : f2 = evalSQ_K5 fac_2 := by rw [hf2]; dsimp only [k5Ops]; rw [← hf.2.2.1]; push_cast; ring
  have hf3' : f3 = evalSQ_K5 fac_3 := by rw [hf3]; dsimp only [k5Ops]; rw [← hf.2.2.2.1]; push_cast; ring
  have hf4' : f4 = evalSQ_K5 fac_4 := by rw [hf4]; dsimp only [k5Ops]; rw [← hf.2.2.2.2]; push_cast; ring
  have hf2_2' : f2_2 = evalSQ_K5 fac_2 ^ 2 := by rw [hf2_2, hf2']; dsimp only [k5Ops]; ring
  have hf2_4' : f2_4 = evalSQ_K5 fac_2 ^ 4 := by rw [hf2_4, hf2_2']; dsimp only [k5Ops]; ring
  have hf2_6' : f2_6 = evalSQ_K5 fac_2 ^ 6 := by rw [hf2_6, hf2_4', hf2_2']; dsimp only [k5Ops]; ring
  have hf2_7' : f2_7 = evalSQ_K5 fac_2 ^ 7 := by rw [hf2_7, hf2_6', hf2']; dsimp only [k5Ops]; ring
  have hf3_3' : f3_3 = evalSQ_K5 fac_3 ^ 3 := by rw [hf3_3, hf3']; dsimp only [k5Ops]; ring
  have hf3_6' : f3_6 = evalSQ_K5 fac_3 ^ 6 := by rw [hf3_6, hf3_3']; dsimp only [k5Ops]; ring
  have hf3_9' : f3_9 = evalSQ_K5 fac_3 ^ 9 := by rw [hf3_9, hf3_6', hf3_3']; dsimp only [k5Ops]; ring
  have hf3_12' : f3_12 = evalSQ_K5 fac_3 ^ 12 := by rw [hf3_12, hf3_9', hf3_3']; dsimp only [k5Ops]; ring
  have hf3_13' : f3_13 = evalSQ_K5 fac_3 ^ 13 := by rw [hf3_13, hf3_12', hf3']; dsimp only [k5Ops]; ring
  have hf4_2' : f4_2 = evalSQ_K5 fac_4 ^ 2 := by rw [hf4_2, hf4']; dsimp only [k5Ops]; ring
  have hS1 : S_K = evalSQ_K5 fac_1 := hf.2.1
  have hQ0 : Q_K = evalSQ_K5 fac_0 := hf.1
  have hd0' : d0 = evalSQ_K5 (D_quot_expr 0) := by rw [hd0, hf3_13', hf4_2']; rfl
  have hd1' : d1 = evalSQ_K5 (D_quot_expr 1) := by rw [hd1, hf2_2', hf3_13', hf4_2', hS1]; rfl
  have hd2' : d2 = evalSQ_K5 (D_quot_expr 2) := by rw [hd2, hf2_4', hf3_13', hf4_2', hS1]; rfl
  have hd3' : d3 = evalSQ_K5 (D_quot_expr 3) := by rw [hd3, hf2_6', hf3_13', hf4_2', hS1]; rfl
  have hd4' : d4 = evalSQ_K5 (D_quot_expr 4) := by rw [hd4, hf2_7', hf3_13', hf4_2', hS1]; rfl
  have hd8' : d8 = evalSQ_K5 (D_quot_expr 8) := by rw [hd8, hf2_7', hf3_12', hf4_2', hS1]; rfl
  have hd9' : d9 = evalSQ_K5 (D_quot_expr 9) := by rw [hd9, hf2_7', hf3_9', hf4_2', hS1]; rfl
  have hd10' : d10 = evalSQ_K5 (D_quot_expr 10) := by rw [hd10, hf2_7', hf3_6', hf4_2', hS1]; rfl
  have hd11' : d11 = evalSQ_K5 (D_quot_expr 11) := by rw [hd11, hf2_7', hf3_3', hf4', hS1]; rfl
  have hd12' : d12 = evalSQ_K5 (D_quot_expr 12) := by rw [hd12, hf2_7', hS1]; rfl
  refine ⟨hac, hgsq, ?_, ?_, ?_, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  · rw [hW]; simp only [hev2, hd0', hd1', hd2', hd3', hd4', hd8', hd9', hd10', hd11', hd12']; rfl
  · have hL2 : L_K ^ 2 = evalSQ_K5 fac_4 ^ 2 := by rw [fac_4_eq_neg_L, neg_sq]
    have hDall : evalSQ_K5 D_all_expr =
        evalSQ_K5 fac_0 * evalSQ_K5 fac_1 * evalSQ_K5 fac_2 ^ 7 * evalSQ_K5 fac_3 ^ 13 *
        evalSQ_K5 fac_4 ^ 2 * evalSQ_K5 fac_5 ^ 4 * evalSQ_K5 fac_6 := rfl
    rw [hDall, hL2, hDdiv, hev2, hev2, hf2_7', hf3_13', hS1, hQ0]; dsimp only [k5Ops]; ring
  · simp only [List.map_cons, List.map_nil, hevT, evalBivLK5, evalYListK5, evalBivK5, RQ5_biv, denote]; ring

private lemma polyC_zero : polyC 0 = 0 := by simp only [polyC, toRat, map_zero]
private lemma polyC_one : polyC 1 = 1 := by simp only [polyC, toRat, map_one]
private lemma polyC_ofNat (n : ℕ) [n.AtLeastTwo] : polyC (no_index (OfNat.ofNat n)) = OfNat.ofNat n := by
  simp only [polyC, toRat, map_ofNat]

private lemma polyC_ca_cb_eq_q10_q20 :
    polyC k5Params.ca_h = q1_a0 (ιC_K5 S_K) (ιC_K5 Q_K) U_C 1 ∧
    polyC k5Params.cb_h = q2_b0 (ιC_K5 S_K) (ιC_K5 Q_K) U_C 1 := by
  constructor <;> (
    simp only [CoverParams.ca_h, CoverParams.cb_h, CoverParams.quadU,
      CoverParams.inv9, CoverParams.inv27, CoverParams.inv81,
      k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q,
      polyC_add, polyC_sub, polyC_neg, polyC_mul, polyC_pow, polyC_C, polyC_X, polyC_ofNat, polyC_zero, polyC_one,
      map_add, map_sub, map_mul, map_div₀, map_inv₀, map_neg, map_pow, map_one, map_zero, map_ofNat,
      q1_a0, q2_b0, dH_dS, dH_dQ]; ring)

private def A0U_U_p : K5[X] :=
  evalUPolyK5 (uTail cacheK.ac.A0U_t0) + Polynomial.C T_K * evalUPolyK5 (uTail cacheK.ac.A0U_t1)

private def A0V_p : K5[X] :=
  evalUPolyK5 cacheK.ac.A0V_t0 + Polynomial.C T_K * evalUPolyK5 cacheK.ac.A0V_t1 +
    Polynomial.C (T_K ^ 2) * evalUPolyK5 cacheK.ac.A0V_t2

private def AY2_p : K5[X] :=
  evalUPolyK5 cacheK.ac.AY2_t0 + Polynomial.C T_K * evalUPolyK5 cacheK.ac.AY2_t1

private def AY3_p : K5[X] :=
  evalUPolyK5 cacheK.ac.AY3_t0 + Polynomial.C T_K * evalUPolyK5 cacheK.ac.AY3_t1

private def AX2_p : K5[X] :=
  evalUPolyK5 cacheK.ac.AX2_t0 + Polynomial.C T_K * evalUPolyK5 cacheK.ac.AX2_t1 +
    Polynomial.C (T_K ^ 2) * evalUPolyK5 cacheK.ac.AX2_t2

private def Bv_1701_p : K5[X] :=
  evalUPolyK5 cacheK.ac.Bv_SQ + Polynomial.C gtK.Bv1_T_1701 * Polynomial.X

-- Fast O(N) `letB_intro` bridge for `cacheK.ac` (`evalACache k5Ops S_K Q_K`)!
private lemma evalACache_K5_props :
    let m := fun mi : Fin 10 => numM_lead3 mi (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K)
      (polyC k5Params.cb_h) (-polyC k5Params.ca_h) U_C 1
    let Cscale : A_C := 16 * 45927 * 567 ^ 4
    let T := ιC_K5 T_K
    (evalUPolyK5 cacheK.ac.ca_p = Polynomial.C 567 * k5Params.ca_h) ∧
    (evalUPolyK5 cacheK.ac.cb_p = Polynomial.C 567 * k5Params.cb_h) ∧
    ((evalUPolyK5 cacheK.ac.ca_p).eval 0 = -175 * ((5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K))) ∧
    ((evalUPolyK5 cacheK.ac.cb_p).eval 0 = 1050 * (S_K * (5 * S_K - 9 * Q_K))) ∧
    (cacheK.ac.A0U_t0.headD 0 = 0 ∧ cacheK.ac.A0U_t1.headD 0 = 0) ∧
    ((evalUPolyK5 cacheK.ac.AY2_t0).eval 0 = 0 ∧ (evalUPolyK5 cacheK.ac.AY2_t1).eval 0 = 0) ∧
    ((evalUPolyK5 cacheK.ac.AX2_t0).eval 0 = 0 ∧ (evalUPolyK5 cacheK.ac.AX2_t1).eval 0 = 0 ∧
      (evalUPolyK5 cacheK.ac.AX2_t2).eval 0 = 0) ∧
    (polyC (evalUPolyK5 cacheK.ac.Bv_SQ) =
      ιC_K5 (-175 * (S_K * (5 * S_K - 9 * Q_K) ^ 2)) +
      U_C * ιC_K5 (7 * (143 * S_K ^ 3 - 828 * S_K ^ 2 * Q_K + 1404 * S_K * Q_K ^ 2 - 594 * Q_K ^ 3) +
        1215 * Q_K ^ 2 + 2430 * Q_K) +
      U_C ^ 2 * ιC_K5 (-28 * (S_K - 3 * Q_K) ^ 3)) ∧
    (polyC (evalUPolyK5 cacheK.ac.A0U_t0 + Polynomial.C T_K * evalUPolyK5 cacheK.ac.A0U_t1) =
        ((-19708 * 187110 : ℤ) : A_C) * (5 * (Cscale * m 0) - 9 * (Cscale * m 1)) +
        ((1472 * 187110 : ℤ) : A_C) * (5 * (Cscale * m 1) - 9 * (Cscale * m 2)) +
        ((188 * 116181450 : ℤ) : A_C) * (5 * (Cscale * m 4) - 9 * (Cscale * m 6)) +
        T * (((-16 * 322726250 : ℤ) : A_C) * (5 * (Cscale * m 4) - 9 * (Cscale * m 6))) ∧
     polyC (evalUPolyK5 cacheK.ac.A0V_t0 + Polynomial.C T_K * evalUPolyK5 cacheK.ac.A0V_t1 +
          Polynomial.C (T_K ^ 2) * evalUPolyK5 cacheK.ac.A0V_t2) =
        (((-892 * (-9) * 64545250 : ℤ) : A_C) * (Cscale * m 4) + ((40 * (-9) * 2904536250 : ℤ) : A_C) * (Cscale * m 6) +
          ((392 * (-9) * 19646550 : ℤ) : A_C) * (Cscale * m 9)) +
        T * (((-892 * 5 * 64545250 : ℤ) : A_C) * (Cscale * m 4) + ((40 * 5 * 2904536250 : ℤ) : A_C) * (Cscale * m 6) +
          ((-112 * (-9) * 98232750 : ℤ) : A_C) * (Cscale * m 9) + ((392 * 5 * 19646550 : ℤ) : A_C) * (Cscale * m 9)) +
        T ^ 2 * (((-112 * 5 * 98232750 : ℤ) : A_C) * (Cscale * m 9)) ∧
     polyC (evalUPolyK5 cacheK.ac.AY2_t0 + Polynomial.C T_K * evalUPolyK5 cacheK.ac.AY2_t1) =
        ((-9 : ℤ) : A_C) * (((-100 * 968178750 : ℤ) : A_C) * (5 * (Cscale * m 4) - 9 * (Cscale * m 6))) +
        T * ((5 : ℤ) : A_C) * (((-100 * 968178750 : ℤ) : A_C) * (5 * (Cscale * m 4) - 9 * (Cscale * m 6))) ∧
     polyC (evalUPolyK5 cacheK.ac.AY3_t0 + Polynomial.C T_K * evalUPolyK5 cacheK.ac.AY3_t1) =
        (((-907876 * 6930 : ℤ) : A_C) * (5 * (Cscale * m 0) - 9 * (Cscale * m 1)) +
          ((2258324 * 6930 : ℤ) : A_C) * (5 * (Cscale * m 1) - 9 * (Cscale * m 2)) -
          ((64 * 348544350 : ℤ) : A_C) * (5 * (Cscale * m 4) - 9 * (Cscale * m 6)) +
          U_C * (((-123236 * 126 : ℤ) : A_C) * (77 * (Cscale * m 0) + 2790 * (Cscale * m 6) - 5904 * (Cscale * m 9)) +
            ((492944 * 9 : ℤ) : A_C) * (770 * (Cscale * m 1) + 9270 * (Cscale * m 6) - 21159 * (Cscale * m 9)))) +
        T * (((8 * 968178750 : ℤ) : A_C) * (5 * (Cscale * m 4) - 9 * (Cscale * m 6)) +
          U_C * (((-123236 * 126 : ℤ) : A_C) * (2156 * (Cscale * m 9)) +
            ((492944 * 9 : ℤ) : A_C) * (7546 * (Cscale * m 9)))) ∧
     polyC (evalUPolyK5 cacheK.ac.AX2_t0 + Polynomial.C T_K * evalUPolyK5 cacheK.ac.AX2_t1 +
          Polynomial.C (T_K ^ 2) * evalUPolyK5 cacheK.ac.AX2_t2) =
        U_C * (((-8 * (-9) * 580907250 : ℤ) : A_C) * (Cscale * m 4) + ((6916 * (-9) * 6548850 : ℤ) : A_C) * (Cscale * m 9)) +
        T * (U_C * (((-8 * 5 * 580907250 : ℤ) : A_C) * (Cscale * m 4) +
          ((-476 * (-9) * 32744250 : ℤ) : A_C) * (Cscale * m 9) + ((6916 * 5 * 6548850 : ℤ) : A_C) * (Cscale * m 9))) +
        T ^ 2 * (U_C * (((-476 * 5 * 32744250 : ℤ) : A_C) * (Cscale * m 9)))) := by
  intro m Cscale T
  rw [cacheK_props.1]
  let P : ACache K5 → Prop := fun ac =>
    (evalUPolyK5 ac.ca_p = Polynomial.C 567 * k5Params.ca_h) ∧
    (evalUPolyK5 ac.cb_p = Polynomial.C 567 * k5Params.cb_h) ∧
    ((evalUPolyK5 ac.ca_p).eval 0 = -175 * ((5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K))) ∧
    ((evalUPolyK5 ac.cb_p).eval 0 = 1050 * (S_K * (5 * S_K - 9 * Q_K))) ∧
    (ac.A0U_t0.headD 0 = 0 ∧ ac.A0U_t1.headD 0 = 0) ∧
    ((evalUPolyK5 ac.AY2_t0).eval 0 = 0 ∧ (evalUPolyK5 ac.AY2_t1).eval 0 = 0) ∧
    ((evalUPolyK5 ac.AX2_t0).eval 0 = 0 ∧ (evalUPolyK5 ac.AX2_t1).eval 0 = 0 ∧
      (evalUPolyK5 ac.AX2_t2).eval 0 = 0) ∧
    (polyC (evalUPolyK5 ac.Bv_SQ) =
      ιC_K5 (-175 * (S_K * (5 * S_K - 9 * Q_K) ^ 2)) +
      U_C * ιC_K5 (7 * (143 * S_K ^ 3 - 828 * S_K ^ 2 * Q_K + 1404 * S_K * Q_K ^ 2 - 594 * Q_K ^ 3) +
        1215 * Q_K ^ 2 + 2430 * Q_K) +
      U_C ^ 2 * ιC_K5 (-28 * (S_K - 3 * Q_K) ^ 3)) ∧
    (polyC (evalUPolyK5 ac.A0U_t0 + Polynomial.C T_K * evalUPolyK5 ac.A0U_t1) =
        ((-19708 * 187110 : ℤ) : A_C) * (5 * (Cscale * m 0) - 9 * (Cscale * m 1)) +
        ((1472 * 187110 : ℤ) : A_C) * (5 * (Cscale * m 1) - 9 * (Cscale * m 2)) +
        ((188 * 116181450 : ℤ) : A_C) * (5 * (Cscale * m 4) - 9 * (Cscale * m 6)) +
        T * (((-16 * 322726250 : ℤ) : A_C) * (5 * (Cscale * m 4) - 9 * (Cscale * m 6))) ∧
     polyC (evalUPolyK5 ac.A0V_t0 + Polynomial.C T_K * evalUPolyK5 ac.A0V_t1 +
          Polynomial.C (T_K ^ 2) * evalUPolyK5 ac.A0V_t2) =
        (((-892 * (-9) * 64545250 : ℤ) : A_C) * (Cscale * m 4) + ((40 * (-9) * 2904536250 : ℤ) : A_C) * (Cscale * m 6) +
          ((392 * (-9) * 19646550 : ℤ) : A_C) * (Cscale * m 9)) +
        T * (((-892 * 5 * 64545250 : ℤ) : A_C) * (Cscale * m 4) + ((40 * 5 * 2904536250 : ℤ) : A_C) * (Cscale * m 6) +
          ((-112 * (-9) * 98232750 : ℤ) : A_C) * (Cscale * m 9) + ((392 * 5 * 19646550 : ℤ) : A_C) * (Cscale * m 9)) +
        T ^ 2 * (((-112 * 5 * 98232750 : ℤ) : A_C) * (Cscale * m 9)) ∧
     polyC (evalUPolyK5 ac.AY2_t0 + Polynomial.C T_K * evalUPolyK5 ac.AY2_t1) =
        ((-9 : ℤ) : A_C) * (((-100 * 968178750 : ℤ) : A_C) * (5 * (Cscale * m 4) - 9 * (Cscale * m 6))) +
        T * ((5 : ℤ) : A_C) * (((-100 * 968178750 : ℤ) : A_C) * (5 * (Cscale * m 4) - 9 * (Cscale * m 6))) ∧
     polyC (evalUPolyK5 ac.AY3_t0 + Polynomial.C T_K * evalUPolyK5 ac.AY3_t1) =
        (((-907876 * 6930 : ℤ) : A_C) * (5 * (Cscale * m 0) - 9 * (Cscale * m 1)) +
          ((2258324 * 6930 : ℤ) : A_C) * (5 * (Cscale * m 1) - 9 * (Cscale * m 2)) -
          ((64 * 348544350 : ℤ) : A_C) * (5 * (Cscale * m 4) - 9 * (Cscale * m 6)) +
          U_C * (((-123236 * 126 : ℤ) : A_C) * (77 * (Cscale * m 0) + 2790 * (Cscale * m 6) - 5904 * (Cscale * m 9)) +
            ((492944 * 9 : ℤ) : A_C) * (770 * (Cscale * m 1) + 9270 * (Cscale * m 6) - 21159 * (Cscale * m 9)))) +
        T * (((8 * 968178750 : ℤ) : A_C) * (5 * (Cscale * m 4) - 9 * (Cscale * m 6)) +
          U_C * (((-123236 * 126 : ℤ) : A_C) * (2156 * (Cscale * m 9)) +
            ((492944 * 9 : ℤ) : A_C) * (7546 * (Cscale * m 9)))) ∧
     polyC (evalUPolyK5 ac.AX2_t0 + Polynomial.C T_K * evalUPolyK5 ac.AX2_t1 +
          Polynomial.C (T_K ^ 2) * evalUPolyK5 ac.AX2_t2) =
        U_C * (((-8 * (-9) * 580907250 : ℤ) : A_C) * (Cscale * m 4) + ((6916 * (-9) * 6548850 : ℤ) : A_C) * (Cscale * m 9)) +
        T * (U_C * (((-8 * 5 * 580907250 : ℤ) : A_C) * (Cscale * m 4) +
          ((-476 * (-9) * 32744250 : ℤ) : A_C) * (Cscale * m 9) + ((6916 * 5 * 6548850 : ℤ) : A_C) * (Cscale * m 9))) +
        T ^ 2 * (U_C * (((-476 * 5 * 32744250 : ℤ) : A_C) * (Cscale * m 9))))
  suffices h : P (evalACache k5Ops S_K Q_K) from h
  unfold evalACache
  refine letB_intro fun S2 hS2 => letB_intro fun SQ hSQ => letB_intro fun Q2 hQ2 =>
    letB_intro fun S3 hS3 => letB_intro fun Q3 hQ3 => letB_intro fun Sm3Q hSm3Q =>
    letB_intro fun Sm3Q2 hSm3Q2 => letB_intro fun A5 hA5 =>
    letB_intro fun ca0 hca0 => letB_intro fun ca1 hca1 => letB_intro fun ca2 hca2 => letB_intro fun ca_p hca_p =>
    letB_intro fun cb0 hcb0 => letB_intro fun cb1 hcb1 => letB_intro fun cb2 hcb2 => letB_intro fun cb_p hcb_p =>
    letB_intro fun b_p hb_p => letB_intro fun am3b_p ham3b_p =>
    letB_intro fun a5m9b ha5m9b => letB_intro fun a15m9b ha15m9b =>
    letB_intro fun aa haa => letB_intro fun ab hab => letB_intro fun bb hbb => letB_intro fun am3b2 ham3b2 =>
    letB_intro fun A2 hA2 => letB_intro fun B2 hB2 => letB_intro fun S15m9Q hS15m9Q => letB_intro fun sbqa hsbqa =>
    letB_intro fun A1 hA1 => letB_intro fun B1 hB1 =>
    letB_intro fun D21 hD21 => letB_intro fun D20 hD20 => letB_intro fun D10 hD10 =>
    letB_intro fun m0 hm0 => letB_intro fun m1 hm1 => letB_intro fun m2 hm2 => letB_intro fun m4 hm4 => letB_intro fun m6 hm6 =>
    letB_intro fun l01 hl01 => letB_intro fun l12 hl12 => letB_intro fun l46 hl46 => letB_intro fun AY2_base hAY2_base =>
    letB_intro fun Bv0_1701 hBv0 => letB_intro fun Bv1_243_S hBv1S =>
    letB_intro fun Bv1_SQ_1701 hBv1SQ => letB_intro fun Bv2_1701 hBv2 => ?_
  dsimp only [P]
  have hS2' : S2 = S_K * S_K := hS2
  have hSQ' : SQ = S_K * Q_K := hSQ
  have hQ2' : Q2 = Q_K * Q_K := hQ2
  have hS3' : S3 = S_K ^ 3 := by rw [hS3, hS2']; dsimp only [k5Ops]; ring
  have hQ3' : Q3 = Q_K ^ 3 := by rw [hQ3, hQ2']; dsimp only [k5Ops]; ring
  have hSm3Q' : Sm3Q = S_K - 3 * Q_K := by rw [hSm3Q]; dsimp only [k5Ops]; push_cast; ring
  have hSm3Q2' : Sm3Q2 = (S_K - 3 * Q_K) ^ 2 := by rw [hSm3Q2, hSm3Q']; dsimp only [k5Ops]; ring
  have hA5' : A5 = 5 * S_K - 9 * Q_K := by rw [hA5]; dsimp only [k5Ops]; push_cast; ring
  have hS15m9Q' : S15m9Q = 15 * S_K - 9 * Q_K := by rw [hS15m9Q]; dsimp only [k5Ops]; push_cast; ring
  have hca0' : ca0 = -175 * ((5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)) := by
    rw [hca0, hA5']; dsimp only [k5Ops]; push_cast; ring
  have hca1' : ca1 = 7 * (143 * S_K ^ 2 - 552 * (S_K * Q_K) + 468 * Q_K ^ 2) := by
    rw [hca1, hS2', hSQ', hQ2']; dsimp only [k5Ops]; push_cast; ring
  have hca2' : ca2 = -28 * (S_K - 3 * Q_K) ^ 2 := by rw [hca2, hSm3Q2']; dsimp only [k5Ops]; push_cast; ring
  have hcb0' : cb0 = 1050 * (S_K * (5 * S_K - 9 * Q_K)) := by rw [hcb0, hA5']; dsimp only [k5Ops]; push_cast; ring
  have hcb1' : cb1 = 21 * (-92 * S_K ^ 2 + 312 * (S_K * Q_K) - 198 * Q_K ^ 2) + 810 * Q_K + 810 := by
    rw [hcb1, hS2', hSQ', hQ2']; dsimp only [k5Ops]; push_cast; ring
  have hcb2' : cb2 = 84 * (S_K - 3 * Q_K) ^ 2 := by rw [hcb2, hSm3Q2']; dsimp only [k5Ops]; push_cast; ring
  have hca_K : evalUPolyK5 ca_p = Polynomial.C 567 * k5Params.ca_h := by
    have hinf : Infinite K5 := Infinite.of_injective (Nat.cast : ℕ → K5) Nat.cast_injective
    apply Polynomial.funext; intro u
    rw [hca_p]; simp only [evalUPolyK5, hca0', hca1', hca2', CoverParams.ca_h, CoverParams.quadU,
      CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_zero]; ring
  have hcb_K : evalUPolyK5 cb_p = Polynomial.C 567 * k5Params.cb_h := by
    have hinf : Infinite K5 := Infinite.of_injective (Nat.cast : ℕ → K5) Nat.cast_injective
    apply Polynomial.funext; intro u
    rw [hcb_p]; simp only [evalUPolyK5, hcb0', hcb1', hcb2', CoverParams.cb_h, CoverParams.quadU,
      CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_zero]; ring
  have hca_e0 : (evalUPolyK5 ca_p).eval 0 = ca0 := by rw [hca_p]; simp [evalUPolyK5]
  have hcb_e0 : (evalUPolyK5 cb_p).eval 0 = cb0 := by rw [hcb_p]; simp [evalUPolyK5]
  -- Evaluate `l01, l12, l46` at `U = 0` in O(N) steps!
  have he0_b : (evalUPolyK5 b_p).eval 0 = -ca0 := by rw [hb_p, evalUPolyK5_uNeg, Polynomial.eval_neg, hca_e0]
  have he0_a5 : (evalUPolyK5 a5m9b).eval 0 = 5 * cb0 - 9 * (-ca0) := by
    rw [ha5m9b, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uSc]; simp [k5Ops, hcb_e0, he0_b]
  have he0_a15 : (evalUPolyK5 a15m9b).eval 0 = 15 * cb0 - 9 * (-ca0) := by
    rw [ha15m9b, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uSc]; simp [k5Ops, hcb_e0, he0_b]
  have he0_aa : (evalUPolyK5 aa).eval 0 = cb0 * cb0 := by rw [haa, evalUPolyK5_uMul]; simp [hcb_e0]
  have he0_ab : (evalUPolyK5 ab).eval 0 = cb0 * (-ca0) := by rw [hab, evalUPolyK5_uMul]; simp [hcb_e0, he0_b]
  have he0_bb : (evalUPolyK5 bb).eval 0 = (-ca0) * (-ca0) := by rw [hbb, evalUPolyK5_uMul]; simp [he0_b]
  have he0_sbqa : (evalUPolyK5 sbqa).eval 0 = S_K * (-ca0) + Q_K * cb0 := by
    rw [hsbqa, evalUPolyK5_uAdd, evalUPolyK5_uSc, evalUPolyK5_uSc]; simp [hcb_e0, he0_b]
  set A2_0 : K5 := -25 * ((5 * cb0 - 9 * (-ca0)) * (15 * cb0 - 9 * (-ca0)))
  set B2_0 : K5 := 50 * (cb0 * (5 * cb0 - 9 * (-ca0)))
  set A1_0 : K5 := -25 * ((15 * S_K - 9 * Q_K) * (5 * cb0 - 9 * (-ca0)) + A5 * (15 * cb0 - 9 * (-ca0)))
  set B1_0 : K5 := 350 * ((10 * S_K - 9 * Q_K) * cb0 - 9 * S_K * (-ca0))
  set D21_0 : K5 := 567 * (A2_0 * B1_0 - 7 * (A1_0 * B2_0))
  set D20_0 : K5 := 189 * (A2_0 * cb0) - 1701 * (ca0 * B2_0)
  set D10_0 : K5 := 189 * (A1_0 * cb0) - 243 * (ca0 * B1_0)
  have he0_A2 : (evalUPolyK5 A2).eval 0 = A2_0 := by
    rw [hA2]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSc, evalUPolyK5_uMul, evalUPolyK5_uShift,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, mul_zero, add_zero,
      he0_a5, he0_a15, Int.cast_neg, Int.cast_ofNat]; dsimp only [k5Ops]; simp only [Int.cast_neg, Int.cast_ofNat, map_intCast, map_neg, map_mul, map_add, map_sub, map_ofNat, mul_zero, zero_mul, add_zero, zero_add]; rfl
  have he0_B2 : (evalUPolyK5 B2).eval 0 = B2_0 := by
    rw [hB2]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSc, evalUPolyK5_uMul, evalUPolyK5_uShift,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, mul_zero, add_zero,
      hcb_e0, he0_a5, Int.cast_ofNat]; dsimp only [k5Ops]; simp only [Int.cast_neg, Int.cast_ofNat, map_intCast, map_neg, map_mul, map_add, map_sub, map_ofNat, mul_zero, zero_mul, add_zero, zero_add]; rfl
  have he0_A1 : (evalUPolyK5 A1).eval 0 = A1_0 := by
    rw [hA1]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSc, evalUPolyK5_uShift,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, mul_zero, add_zero,
      he0_a5, he0_a15, hS15m9Q', Int.cast_neg, Int.cast_ofNat]; dsimp only [k5Ops]; simp only [Int.cast_neg, Int.cast_ofNat, map_intCast, map_neg, map_mul, map_add, map_sub, map_ofNat, mul_zero, zero_mul, add_zero, zero_add]; rfl
  have he0_B1 : (evalUPolyK5 B1).eval 0 = B1_0 := by
    rw [hB1]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uShift,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      mul_zero, add_zero, hcb_e0, he0_b, Int.cast_ofNat]; dsimp only [k5Ops]; simp only [Int.cast_neg, Int.cast_ofNat, map_intCast, map_neg, map_mul, map_add, map_sub, map_ofNat, mul_zero, zero_mul, add_zero, zero_add]; rfl
  have he0_D21 : (evalUPolyK5 D21).eval 0 = D21_0 := by
    rw [hD21]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, he0_A2, he0_B1, he0_A1, he0_B2, Int.cast_ofNat]; dsimp only [k5Ops]; simp only [Int.cast_neg, Int.cast_ofNat, map_intCast, map_neg, map_mul, map_add, map_sub, map_ofNat, mul_zero, zero_mul, add_zero, zero_add]; rfl
  have he0_D20 : (evalUPolyK5 D20).eval 0 = D20_0 := by
    rw [hD20]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, he0_A2, hcb_e0, hca_e0, he0_B2, Int.cast_ofNat]; dsimp only [k5Ops]; simp only [Int.cast_neg, Int.cast_ofNat, map_intCast, map_neg, map_mul, map_add, map_sub, map_ofNat, mul_zero, zero_mul, add_zero, zero_add]; rfl
  have he0_D10 : (evalUPolyK5 D10).eval 0 = D10_0 := by
    rw [hD10]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, he0_A1, hcb_e0, hca_e0, he0_B1, Int.cast_ofNat]; dsimp only [k5Ops]; simp only [Int.cast_neg, Int.cast_ofNat, map_intCast, map_neg, map_mul, map_add, map_sub, map_ofNat, mul_zero, zero_mul, add_zero, zero_add]; rfl
  have he0_m0 : (evalUPolyK5 m0).eval 0 = cb0 * cb0 * D10_0 - 2 * S_K * (cb0 * D20_0) + S_K * S_K * D21_0 := by
    rw [hm0]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      he0_aa, he0_D10, hcb_e0, he0_D20, hS2', he0_D21, Int.cast_ofNat]; dsimp only [k5Ops]; simp only [Int.cast_neg, Int.cast_ofNat, map_intCast, map_neg, map_mul, map_add, map_sub, map_ofNat, mul_zero, zero_mul, add_zero, zero_add]
  have he0_m1 : (evalUPolyK5 m1).eval 0 = cb0 * (-ca0) * D10_0 - (S_K * (-ca0) + Q_K * cb0) * D20_0 + S_K * Q_K * D21_0 := by
    rw [hm1]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      he0_ab, he0_D10, he0_sbqa, he0_D20, hSQ', he0_D21]
  have he0_m2 : (evalUPolyK5 m2).eval 0 = (-ca0) * (-ca0) * D10_0 - 2 * Q_K * ((-ca0) * D20_0) + Q_K * Q_K * D21_0 := by
    rw [hm2]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      he0_bb, he0_D10, he0_b, he0_D20, hQ2', he0_D21, Int.cast_ofNat]; dsimp only [k5Ops]; simp only [Int.cast_neg, Int.cast_ofNat, map_intCast, map_neg, map_mul, map_add, map_sub, map_ofNat, mul_zero, zero_mul, add_zero, zero_add]
  have he0_m4 : (evalUPolyK5 m4).eval 0 = S_K * D21_0 - cb0 * D20_0 := by
    rw [hm4]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hcb_e0, he0_D21, he0_D20]
  have he0_m6 : (evalUPolyK5 m6).eval 0 = Q_K * D21_0 - (-ca0) * D20_0 := by
    rw [hm6]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, he0_b, he0_D21, he0_D20]
  have h5a9b : 5 * cb0 - 9 * (-ca0) = -525 * A5 ^ 2 := by rw [hcb0', hca0', hA5']; ring
  have hD20_0 : D20_0 = -525 * A5 * D10_0 := by
    dsimp only [D20_0, D10_0, A2_0, B2_0, A1_0, B1_0]; rw [hcb0', hca0', hA5']; ring
  have hD21_0 : D21_0 = -525 * A5 * D20_0 := by
    dsimp only [D21_0, D20_0, A2_0, B2_0, A1_0, B1_0]; rw [hcb0', hca0', hA5']; ring
  have he0_l46 : (evalUPolyK5 l46).eval 0 = 0 := by
    rw [hl46]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, he0_m4, he0_m6]; dsimp only [k5Ops]; push_cast
    linear_combination A5 * hD21_0 - D20_0 * h5a9b + D21_0 * hA5'.symm
  have he0_l01 : (evalUPolyK5 l01).eval 0 = 0 := by
    rw [hl01]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, he0_m0, he0_m1]; dsimp only [k5Ops]; push_cast
    linear_combination (cb0 * D10_0 - S_K * D20_0) * h5a9b - cb0 * A5 * hD20_0 +
      S_K * A5 * hD21_0 + (S_K * D21_0 - cb0 * D20_0) * hA5'.symm
  have he0_l12 : (evalUPolyK5 l12).eval 0 = 0 := by
    rw [hl12]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, he0_m1, he0_m2]; dsimp only [k5Ops]; push_cast
    linear_combination ((-ca0) * D10_0 - Q_K * D20_0) * h5a9b - (-ca0) * A5 * hD20_0 +
      Q_K * A5 * hD21_0 + (Q_K * D21_0 - (-ca0) * D20_0) * hA5'.symm
  have hhead : ∀ (p : UPoly K5), p.headD 0 = (evalUPolyK5 p).eval 0 := fun p => by cases p <;> simp [evalUPolyK5]
  -- Evaluate every node in `A_C` in O(N) steps!
  set S := ιC_K5 S_K; set Q := ιC_K5 Q_K
  set ca := polyC k5Params.ca_h; set cb := polyC k5Params.cb_h
  set a := (567 : A_C) * cb; set b := -((567 : A_C) * ca)
  have hp_ca : polyC (evalUPolyK5 ca_p) = 567 * ca := by rw [hca_K, polyC_mul, polyC_C]; simp [ca, map_ofNat]
  have hp_cb : polyC (evalUPolyK5 cb_p) = a := by rw [hcb_K, polyC_mul, polyC_C]; simp [a, cb, map_ofNat]
  have hp_b : polyC (evalUPolyK5 b_p) = b := by rw [hb_p, evalUPolyK5_uNeg, polyC_neg, hp_ca]
  have hp_am3b : polyC (evalUPolyK5 am3b_p) = a - 3 * b := by
    have hca_ex : polyC (evalUPolyK5 ca_p) = ιC_K5 ca0 + U_C * (ιC_K5 ca1 + U_C * ιC_K5 ca2) := by
      rw [hca_p]; simp only [evalUPolyK5, polyC_add, polyC_mul, polyC_C, polyC_X, map_zero, mul_zero, add_zero]
    have hcb_ex : polyC (evalUPolyK5 cb_p) = ιC_K5 cb0 + U_C * (ιC_K5 cb1 + U_C * ιC_K5 cb2) := by
      rw [hcb_p]; simp only [evalUPolyK5, polyC_add, polyC_mul, polyC_C, polyC_X, map_zero, mul_zero, add_zero]
    have h2 : cb2 - 3 * (-ca2) = 0 := by rw [hcb2', hca2']; ring
    have h2C : ιC_K5 cb2 + 3 * ιC_K5 ca2 = 0 := by
      have := congrArg ιC_K5 h2; simp only [map_sub, map_mul, map_neg, map_ofNat, map_zero] at this
      linear_combination this
    rw [ham3b_p]; simp only [evalUPolyK5, k5Ops, polyC_add, polyC_sub, polyC_neg, polyC_mul, polyC_C, polyC_X, polyC_ofNat,
      map_sub, map_mul, map_neg, map_ofNat, map_intCast, map_zero, mul_zero, add_zero, Int.cast_ofNat]
    rw [← hp_cb, ← hp_b, hb_p, evalUPolyK5_uNeg, polyC_neg, hca_ex, hcb_ex]
    linear_combination -U_C ^ 2 * h2C
  have hp_a5 : polyC (evalUPolyK5 a5m9b) = 5 * a - 9 * b := by
    rw [ha5m9b, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uSc]
    simp only [polyC_sub, polyC_mul, polyC_C, hp_cb, hp_b]; dsimp only [k5Ops]; simp only [map_intCast, Int.cast_ofNat, map_ofNat]
  have hp_a15 : polyC (evalUPolyK5 a15m9b) = 15 * a - 9 * b := by
    rw [ha15m9b, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uSc]
    simp only [polyC_sub, polyC_mul, polyC_C, hp_cb, hp_b]; dsimp only [k5Ops]; simp only [map_intCast, Int.cast_ofNat, map_ofNat]
  have hp_aa : polyC (evalUPolyK5 aa) = a * a := by rw [haa, evalUPolyK5_uMul, polyC_mul, hp_cb]
  have hp_ab : polyC (evalUPolyK5 ab) = a * b := by rw [hab, evalUPolyK5_uMul, polyC_mul, hp_cb, hp_b]
  have hp_bb : polyC (evalUPolyK5 bb) = b * b := by rw [hbb, evalUPolyK5_uMul, polyC_mul, hp_b]
  have hp_am3b2 : polyC (evalUPolyK5 am3b2) = (a - 3 * b) * (a - 3 * b) := by
    rw [ham3b2, evalUPolyK5_uMul, polyC_mul, hp_am3b]
  have hp_sbqa : polyC (evalUPolyK5 sbqa) = S * b + Q * a := by
    rw [hsbqa, evalUPolyK5_uAdd, evalUPolyK5_uSc, evalUPolyK5_uSc]; simp [polyC_add, polyC_mul, polyC_C, hp_cb, hp_b, S, Q]
  set A2_v : A_C := 243 * q1_a2 a b U_C 1
  set B2_v : A_C := 27 * q2_b2 a b U_C 1
  set A1_v : A_C := 243 * q1_a1 a b S Q U_C 1
  set B1_v : A_C := 189 * q2_b1 a b S Q U_C 1
  set D21_v : A_C := 567 * (A2_v * B1_v - 7 * (A1_v * B2_v))
  set D20_v : A_C := 189 * (A2_v * a) - 1701 * (567 * ca * B2_v)
  set D10_v : A_C := 189 * (A1_v * a) - 243 * (567 * ca * B1_v)
  have hp_A2 : polyC (evalUPolyK5 A2) = A2_v := by
    rw [hA2]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uShift, evalUPolyK5_uMul, polyC_add, polyC_sub, polyC_mul, polyC_C, polyC_X, map_intCast, Int.cast_neg, Int.cast_ofNat,
      hp_a5, hp_a15, hp_aa, hp_ab, hp_bb, hp_am3b2]; dsimp only [k5Ops]; simp only [Int.cast_neg, Int.cast_ofNat, map_intCast, map_neg, map_mul, map_add, map_sub, map_ofNat, mul_zero, zero_mul, add_zero, zero_add]
    exact dHS_243_ring a b U_C
  have hp_B2 : polyC (evalUPolyK5 B2) = B2_v := by
    rw [hB2]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uShift, evalUPolyK5_uMul, polyC_add, polyC_sub, polyC_mul, polyC_C, polyC_X, map_intCast, Int.cast_neg, Int.cast_ofNat,
      hp_cb, hp_a5, hp_aa, hp_ab, hp_bb, hp_am3b2]; dsimp only [k5Ops]; simp only [Int.cast_neg, Int.cast_ofNat, map_intCast, map_neg, map_mul, map_add, map_sub, map_ofNat, mul_zero, zero_mul, add_zero, zero_add]
    exact dHQ0_27_ring a b U_C
  have hp_A1 : polyC (evalUPolyK5 A1) = A1_v := by
    rw [hA1]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uShift, polyC_add, polyC_sub, polyC_mul, polyC_C, polyC_X, polyC_ofNat, hS15m9Q', hA5', hSm3Q',
      map_sub, map_mul, map_neg, map_ofNat, map_intCast, Int.cast_neg, Int.cast_ofNat,
      hp_a5, hp_a15, hp_cb, hp_sbqa, hp_b, hp_am3b]; dsimp only [k5Ops]; simp only [Int.cast_neg, Int.cast_ofNat, map_intCast, map_neg, map_mul, map_add, map_sub, map_ofNat, mul_zero, zero_mul, add_zero, zero_add]
    change _ = 243 * q1_a1 a b S Q U_C 1
    rw [← dHS_bi_243_ring S Q a b U_C]
  have hp_B1 : polyC (evalUPolyK5 B1) = B1_v := by
    rw [hB1]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uShift, polyC_add, polyC_sub, polyC_mul, polyC_C, polyC_X, polyC_ofNat, hSm3Q',
      map_sub, map_mul, map_neg, map_ofNat, map_intCast, Int.cast_neg, Int.cast_ofNat,
      hp_cb, hp_b, hp_sbqa, hp_am3b]; dsimp only [k5Ops]; simp only [Int.cast_neg, Int.cast_ofNat, map_intCast, map_neg, map_mul, map_add, map_sub, map_ofNat, mul_zero, zero_mul, add_zero, zero_add]
    change _ = 189 * q2_b1 a b S Q U_C 1
    rw [← dHQ1_bi_189_ring S Q a b U_C]
  have hp_D21 : polyC (evalUPolyK5 D21) = D21_v := by
    rw [hD21]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      polyC_sub, polyC_mul, polyC_C, map_intCast, Int.cast_ofNat, hp_A2, hp_B1, hp_A1, hp_B2]; dsimp only [k5Ops]; simp only [Int.cast_neg, Int.cast_ofNat, map_intCast, map_neg, map_mul, map_add, map_sub, map_ofNat, mul_zero, zero_mul, add_zero, zero_add]; rfl
  have hp_D20 : polyC (evalUPolyK5 D20) = D20_v := by
    rw [hD20]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      polyC_sub, polyC_mul, polyC_C, map_intCast, Int.cast_ofNat, hp_A2, hp_cb, hp_ca, hp_B2]; dsimp only [k5Ops]; simp only [Int.cast_neg, Int.cast_ofNat, map_intCast, map_neg, map_mul, map_add, map_sub, map_ofNat, mul_zero, zero_mul, add_zero, zero_add]; rfl
  have hp_D10 : polyC (evalUPolyK5 D10) = D10_v := by
    rw [hD10]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      polyC_sub, polyC_mul, polyC_C, map_intCast, Int.cast_ofNat, hp_A1, hp_cb, hp_ca, hp_B1]; dsimp only [k5Ops]; simp only [Int.cast_neg, Int.cast_ofNat, map_intCast, map_neg, map_mul, map_add, map_sub, map_ofNat, mul_zero, zero_mul, add_zero, zero_add]; rfl
  have ha2_eq : q1_a2 a b U_C 1 = (567 : A_C) ^ 2 * q1_a2 cb (-ca) U_C 1 := by simp only [a, b, q1_a2, dH_dS]; ring
  have hb2_eq : q2_b2 a b U_C 1 = (567 : A_C) ^ 2 * q2_b2 cb (-ca) U_C 1 := by simp only [a, b, q2_b2, dH_dQ]; ring
  have ha1_eq : q1_a1 a b S Q U_C 1 = (567 : A_C) * q1_a1 cb (-ca) S Q U_C 1 := by simp only [a, b, q1_a1, dH_dS]; ring
  have hb1_eq : q2_b1 a b S Q U_C 1 = (567 : A_C) * q2_b1 cb (-ca) S Q U_C 1 := by simp only [a, b, q2_b1, dH_dQ]; ring
  have hca_q : ca = q1_a0 S Q U_C 1 := polyC_ca_cb_eq_q10_q20.1
  have hcb_q : cb = q2_b0 S Q U_C 1 := polyC_ca_cb_eq_q10_q20.2
  have hD21_m : D21_v = Cscale * m 9 := by
    simp only [D21_v, A2_v, B2_v, A1_v, B1_v, ha2_eq, hb2_eq, ha1_eq, hb1_eq, Cscale, m, numM_lead3]; ring
  have hD20_m : D20_v = 45927 * 567 ^ 3 * (q1_a2 cb (-ca) U_C 1 * q2_b0 S Q U_C 1 - q1_a0 S Q U_C 1 * q2_b2 cb (-ca) U_C 1) := by
    dsimp only [D20_v, A2_v, B2_v]; rw [ha2_eq, hb2_eq]; simp only [a, hca_q, hcb_q]; ring
  have hD10_m : D10_v = 45927 * 567 ^ 2 * (q1_a1 cb (-ca) S Q U_C 1 * q2_b0 S Q U_C 1 - q1_a0 S Q U_C 1 * q2_b1 cb (-ca) S Q U_C 1) := by
    dsimp only [D10_v, A1_v, B1_v]; rw [ha1_eq, hb1_eq]; simp only [a, hca_q, hcb_q]; ring
  have hp_m0 : polyC (evalUPolyK5 m0) = Cscale * m 0 := by
    rw [hm0]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      polyC_add, polyC_sub, polyC_mul, polyC_C, hS2', map_mul, map_intCast, Int.cast_ofNat,
      hp_aa, hp_D10, hp_cb, hp_D20, hp_D21, hD21_m, hD20_m, hD10_m, Cscale, m, numM_lead3, a, b, S]; dsimp only [k5Ops]; simp only [Int.cast_neg, Int.cast_ofNat, map_intCast, map_neg, map_mul, map_add, map_sub, map_ofNat, mul_zero, zero_mul, add_zero, zero_add]; ring
  have hp_m1 : polyC (evalUPolyK5 m1) = Cscale * m 1 := by
    rw [hm1]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      polyC_add, polyC_sub, polyC_mul, polyC_C, hSQ', map_mul,
      hp_ab, hp_D10, hp_sbqa, hp_D20, hp_D21, hD21_m, hD20_m, hD10_m, Cscale, m, numM_lead3, a, b, S, Q]; ring
  have hp_m2 : polyC (evalUPolyK5 m2) = Cscale * m 2 := by
    rw [hm2]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      polyC_add, polyC_sub, polyC_mul, polyC_C, hQ2', map_mul, map_intCast, Int.cast_ofNat,
      hp_bb, hp_D10, hp_b, hp_D20, hp_D21, hD21_m, hD20_m, hD10_m, Cscale, m, numM_lead3, a, b, Q]; dsimp only [k5Ops]; simp only [Int.cast_neg, Int.cast_ofNat, map_intCast, map_neg, map_mul, map_add, map_sub, map_ofNat, mul_zero, zero_mul, add_zero, zero_add]; ring
  have hp_m4 : polyC (evalUPolyK5 m4) = Cscale * m 4 := by
    rw [hm4]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      polyC_sub, polyC_mul, polyC_C, hp_D21, hp_cb, hp_D20, hD21_m, hD20_m, Cscale, m, numM_lead3, a, S]; ring
  have hp_m6 : polyC (evalUPolyK5 m6) = Cscale * m 6 := by
    rw [hm6]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      polyC_sub, polyC_mul, polyC_C, hp_D21, hp_b, hp_D20, hD21_m, hD20_m, Cscale, m, numM_lead3, b, Q]; ring
  have hp_l01 : polyC (evalUPolyK5 l01) = 5 * (Cscale * m 0) - 9 * (Cscale * m 1) := by
    rw [hl01, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uSc]
    simp only [polyC_sub, polyC_mul, polyC_C, hp_m0, hp_m1]; dsimp only [k5Ops]; simp only [map_intCast, Int.cast_ofNat, map_ofNat]
  have hp_l12 : polyC (evalUPolyK5 l12) = 5 * (Cscale * m 1) - 9 * (Cscale * m 2) := by
    rw [hl12, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uSc]
    simp only [polyC_sub, polyC_mul, polyC_C, hp_m1, hp_m2]; dsimp only [k5Ops]; simp only [map_intCast, Int.cast_ofNat, map_ofNat]
  have hp_l46 : polyC (evalUPolyK5 l46) = 5 * (Cscale * m 4) - 9 * (Cscale * m 6) := by
    rw [hl46, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uSc]
    simp only [polyC_sub, polyC_mul, polyC_C, hp_m4, hp_m6]; dsimp only [k5Ops]; simp only [map_intCast, Int.cast_ofNat, map_ofNat]
  have hp_AY2b : polyC (evalUPolyK5 AY2_base) = ((-100 * 968178750 : ℤ) : A_C) * (5 * (Cscale * m 4) - 9 * (Cscale * m 6)) := by
    rw [hAY2_base, evalUPolyK5_uSc, polyC_mul, polyC_C, hp_l46]; dsimp only [k5Ops]; simp only [map_intCast]
  refine ⟨hca_K, hcb_K, by rw [hca_e0, hca0'], by rw [hcb_e0, hcb0'], ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hhead]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSc, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, he0_l01, he0_l12, he0_l46, mul_zero, add_zero]
  · rw [hhead]; simp only [evalUPolyK5_uSc, Polynomial.eval_mul, Polynomial.eval_C, he0_l46, mul_zero]
  · simp only [evalUPolyK5_uSc, hAY2_base, Polynomial.eval_mul, Polynomial.eval_C, he0_l46, mul_zero]
  · simp only [evalUPolyK5_uSc, hAY2_base, Polynomial.eval_mul, Polynomial.eval_C, he0_l46, mul_zero]
  · simp [evalUPolyK5_uShift]
  · simp [evalUPolyK5_uShift]
  · simp [evalUPolyK5_uShift]
  · simp only [evalUPolyK5, polyC_add, polyC_mul, polyC_C, polyC_X, map_zero, mul_zero, add_zero]
    have h0 : Bv0_1701 = -175 * (S_K * (5 * S_K - 9 * Q_K) ^ 2) := by rw [hBv0, hA5']; dsimp only [k5Ops]; push_cast; ring
    have h1 : Bv1_SQ_1701 = 7 * (143 * S_K ^ 3 - 828 * S_K ^ 2 * Q_K + 1404 * S_K * Q_K ^ 2 - 594 * Q_K ^ 3) +
        1215 * Q_K ^ 2 + 2430 * Q_K := by
      rw [hBv1SQ, hBv1S, hS3', hS2', hQ2', hQ3']; dsimp only [k5Ops]; push_cast; ring
    have h2 : Bv2_1701 = -28 * (S_K - 3 * Q_K) ^ 3 := by rw [hBv2, hSm3Q2', hSm3Q']; dsimp only [k5Ops]; push_cast; ring
    rw [h0, h1, h2]; ring
  · simp only [evalUPolyK5_uAdd, evalUPolyK5_uSc, polyC_add, polyC_mul, polyC_C,
      hp_l01, hp_l12, hp_l46]; dsimp only [k5Ops, T]; simp only [map_intCast]
  · simp only [evalUPolyK5_uAdd, evalUPolyK5_uSc, polyC_add, polyC_mul, polyC_pow, polyC_C,
      map_pow, hp_m4, hp_m6, hp_D21, hD21_m]; dsimp only [k5Ops, T]; simp only [map_intCast]
  · simp only [evalUPolyK5_uSc, polyC_add, polyC_mul, polyC_C, hp_AY2b]; dsimp only [k5Ops, T]; simp only [map_intCast]
    generalize (((-100 * 968178750 : ℤ) : A_C) * (5 * (Cscale * m 4) - 9 * (Cscale * m 6))) = Z
    generalize ιC_K5 T_K = t; ring
  · simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uShift,
      polyC_add, polyC_sub, polyC_mul, polyC_C, polyC_X,
      hp_l01, hp_l12, hp_l46, hp_m0, hp_m1, hp_m6, hp_D21, hD21_m]; dsimp only [k5Ops, T]; simp only [map_intCast, Int.cast_ofNat, map_ofNat]
  · simp only [evalUPolyK5_uAdd, evalUPolyK5_uSc, evalUPolyK5_uShift,
      polyC_add, polyC_mul, polyC_pow, polyC_C, polyC_X, map_pow, hp_m4, hp_D21, hD21_m]; dsimp only [k5Ops, T]; simp only [map_intCast]

private lemma evalUPolyK5_ca_cb :
    evalUPolyK5 cacheK.ac.ca_p = Polynomial.C 567 * k5Params.ca_h ∧
    evalUPolyK5 cacheK.ac.cb_p = Polynomial.C 567 * k5Params.cb_h :=
  ⟨evalACache_K5_props.1, evalACache_K5_props.2.1⟩

private lemma A0U_head_zero :
    cacheK.ac.A0U_t0.headD 0 = 0 ∧ cacheK.ac.A0U_t1.headD 0 = 0 :=
  evalACache_K5_props.2.2.2.2.1

private lemma evalACache_AC_bridge :
    let m := fun mi : Fin 10 => numM_lead3 mi (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K)
      (polyC k5Params.cb_h) (-polyC k5Params.ca_h) U_C 1
    let MA : A_C := (M_A_int : A_C)
    (U_C * polyC A0U_U_p = MA * (-(19708 / 1257375 : A_C) * (5 * m 0 - 9 * m 1) +
        (1472 / 1257375 : A_C) * (5 * m 1 - 9 * m 2) - (16 / 729 : A_C) * (5 * m 3 - 9 * m 5) +
        (188 / 2025 : A_C) * (5 * m 4 - 9 * m 6))) ∧
    (polyC A0V_p = MA * (-(892 / 3645 : A_C) * (5 * m 3 - 9 * m 4) + (40 / 81 : A_C) * (5 * m 5 - 9 * m 6) -
        (112 / 2395 : A_C) * (5 * m 7 - 9 * m 8) + (392 / 11975 : A_C) * (5 * m 8 - 9 * m 9))) ∧
    (polyC AY2_p = MA * (-(100 / 243 : A_C) * (25 * m 3 - 45 * m 4 - 45 * m 5 + 81 * m 6))) ∧
    (polyC AY3_p = MA * (-(907876 / 33949125 : A_C) * (5 * m 0 - 9 * m 1) +
        (2258324 / 33949125 : A_C) * (5 * m 1 - 9 * m 2) + (8 / 243 : A_C) * (5 * m 3 - 9 * m 5) -
        (64 / 675 : A_C) * (5 * m 4 - 9 * m 6) +
        U_C * (-(123236 / 24249375 : A_C) * (m 0 + (2790 / 77 : A_C) * m 6 + 28 * m 8 - (5904 / 77 : A_C) * m 9) +
          (492944 / 33949125 : A_C) * (m 1 + (927 / 77 : A_C) * m 6 + (49 / 5 : A_C) * m 8 - (21159 / 770 : A_C) * m 9)))) ∧
    (polyC AX2_p = MA * (U_C * (-(8 / 405 : A_C) * (5 * m 3 - 9 * m 4) -
        (476 / 7185 : A_C) * (5 * m 7 - 9 * m 8) + (6916 / 35925 : A_C) * (5 * m 8 - 9 * m 9)))) := by
  intro m MA
  have hA0U_eq : Polynomial.X * A0U_U_p = evalUPolyK5 cacheK.ac.A0U_t0 + Polynomial.C T_K * evalUPolyK5 cacheK.ac.A0U_t1 := by
    have h0 := evalUPolyK5_uTail cacheK.ac.A0U_t0
    have h1 := evalUPolyK5_uTail cacheK.ac.A0U_t1
    rw [A0U_head_zero.1, map_zero, zero_add] at h0
    rw [A0U_head_zero.2, map_zero, zero_add] at h1
    simp only [A0U_U_p, h0, h1]; ring
  rw [show U_C * polyC A0U_U_p = polyC (evalUPolyK5 cacheK.ac.A0U_t0 + Polynomial.C T_K * evalUPolyK5 cacheK.ac.A0U_t1) by
    rw [← polyC_X, ← polyC_mul, hA0U_eq]]
  set T := ιC_K5 T_K
  set Cscale : A_C := 16 * 45927 * 567 ^ 4
  have hrat_L (p q r : ℤ) (hq : q ≠ 0) (hmul : p * L_all_A = r * q) :
      ((p : A_C) / (q : A_C)) * (L_all_A : A_C) = (r : A_C) := by
    have hqA : (q : A_C) ≠ 0 := Int.cast_ne_zero.mpr hq
    have hZ : (p : A_C) * (L_all_A : A_C) = (r : A_C) * (q : A_C) := by exact_mod_cast hmul
    rw [div_mul_eq_mul_div, hZ, mul_div_cancel_right₀ _ hqA]
  have hMA_split : MA = (L_all_A : A_C) * Cscale := by
    simp only [MA, M_A_int, Cscale, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]; ring
  have hm3 : m 3 = T * m 4 := by simp [m, numM_lead3, T]; ring
  have hm5 : m 5 = T * m 6 := by simp [m, numM_lead3, T]; ring
  have hm8 : m 8 = T * m 9 := by simp [m, numM_lead3, T]; ring
  have hm7 : m 7 = T ^ 2 * m 9 := by simp [m, numM_lead3, T]; ring
  have hA_eval := evalACache_K5_props.2.2.2.2.2.2.2.2
  dsimp only [A0V_p, AY2_p, AY3_p, AX2_p]
  rw [hA_eval.1, hA_eval.2.1, hA_eval.2.2.1, hA_eval.2.2.2.1, hA_eval.2.2.2.2,
    hMA_split, hm3, hm5, hm8, hm7]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h1 := hrat_L (-19708) 1257375 (-19708 * 187110) (by decide) (by unfold L_all_A; decide)
    have h2 := hrat_L 1472 1257375 (1472 * 187110) (by decide) (by unfold L_all_A; decide)
    have h3 := hrat_L (-16) 729 (-16 * 322726250) (by decide) (by unfold L_all_A; decide)
    have h4 := hrat_L 188 2025 (188 * 116181450) (by decide) (by unfold L_all_A; decide)
    rw [← h1, ← h2, ← h3, ← h4]
    simp only [Int.cast_neg, Int.cast_ofNat, neg_div]
    generalize (L_all_A : A_C) = Lc
    generalize (19708 / 1257375 : A_C) = c1; generalize (1472 / 1257375 : A_C) = c2
    generalize (16 / 729 : A_C) = c3; generalize (188 / 2025 : A_C) = c4
    ring
  · have h1 := hrat_L (-892) 3645 (-892 * 64545250) (by decide) (by unfold L_all_A; decide)
    have h2 := hrat_L 40 81 (40 * 2904536250) (by decide) (by unfold L_all_A; decide)
    have h3 := hrat_L (-112) 2395 (-112 * 98232750) (by decide) (by unfold L_all_A; decide)
    have h4 := hrat_L 392 11975 (392 * 19646550) (by decide) (by unfold L_all_A; decide)
    have hsc : ∀ (a b c : ℤ), ((a * b * c : ℤ) : A_C) = (b : A_C) * ((a * c : ℤ) : A_C) := fun a b c => by
      push_cast; ring
    rw [hsc (-892) (-9) 64545250, hsc 40 (-9) 2904536250, hsc 392 (-9) 19646550,
        hsc (-892) 5 64545250, hsc 40 5 2904536250, hsc (-112) (-9) 98232750,
        hsc 392 5 19646550, hsc (-112) 5 98232750, ← h1, ← h2, ← h3, ← h4]
    simp only [Int.cast_neg, Int.cast_ofNat, neg_div]
    generalize (L_all_A : A_C) = Lc
    generalize (892 / 3645 : A_C) = c1; generalize (40 / 81 : A_C) = c2
    generalize (112 / 2395 : A_C) = c3; generalize (392 / 11975 : A_C) = c4
    ring
  · have h1 := hrat_L (-100) 243 (-100 * 968178750) (by decide) (by unfold L_all_A; decide)
    rw [← h1]
    simp only [Int.cast_neg, Int.cast_ofNat, neg_div]
    generalize (L_all_A : A_C) = Lc; generalize (100 / 243 : A_C) = c1
    ring
  · have h1 := hrat_L (-907876) 33949125 (-907876 * 6930) (by decide) (by unfold L_all_A; decide)
    have h2 := hrat_L 2258324 33949125 (2258324 * 6930) (by decide) (by unfold L_all_A; decide)
    have h3 := hrat_L 8 243 (8 * 968178750) (by decide) (by unfold L_all_A; decide)
    have h4 := hrat_L (-64) 675 (-64 * 348544350) (by decide) (by unfold L_all_A; decide)
    have h5 := hrat_L (-123236) (24249375 * 77) (-123236 * 126) (by decide) (by unfold L_all_A; decide)
    have h6 := hrat_L 492944 (33949125 * 770) (492944 * 9) (by decide) (by unfold L_all_A; decide)
    have h4' : ((64 * 348544350 : ℤ) : A_C) = -((-64 * 348544350 : ℤ) : A_C) := by
      have : ((64 * 348544350 : ℤ) : A_C) = ((-(-64 * 348544350) : ℤ) : A_C) := by congr 1
      rw [this, Int.cast_neg]
    rw [h4', ← h1, ← h2, ← h3, ← h4, ← h5, ← h6]
    rw [show (((-123236 : ℤ) : A_C) / (((24249375 * 77 : ℤ) : A_C))) = -(123236 / 24249375 : A_C) / 77 by
      simp only [Int.cast_mul, Int.cast_neg, Int.cast_ofNat, neg_div, div_mul_eq_div_div]]
    rw [show (((492944 : ℤ) : A_C) / (((33949125 * 770 : ℤ) : A_C))) = (492944 / 33949125 : A_C) / 770 by
      simp only [Int.cast_mul, Int.cast_ofNat, div_mul_eq_div_div]]
    simp only [Int.cast_neg, Int.cast_ofNat, neg_div]
    generalize (L_all_A : A_C) = Lc
    generalize (907876 / 33949125 : A_C) = c1; generalize (2258324 / 33949125 : A_C) = c2
    generalize (8 / 243 : A_C) = c3; generalize (64 / 675 : A_C) = c4
    generalize (123236 / 24249375 : A_C) = c5; generalize (492944 / 33949125 : A_C) = c6
    ring
  · have h1 := hrat_L (-8) 405 (-8 * 580907250) (by decide) (by unfold L_all_A; decide)
    have h2 := hrat_L (-476) 7185 (-476 * 32744250) (by decide) (by unfold L_all_A; decide)
    have h3 := hrat_L 6916 35925 (6916 * 6548850) (by decide) (by unfold L_all_A; decide)
    have hsc : ∀ (a b c : ℤ), ((a * b * c : ℤ) : A_C) = (b : A_C) * ((a * c : ℤ) : A_C) := fun a b c => by
      push_cast; ring
    rw [hsc (-8) (-9) 580907250, hsc 6916 (-9) 6548850, hsc (-8) 5 580907250,
        hsc (-476) (-9) 32744250, hsc 6916 5 6548850, hsc (-476) 5 32744250, ← h1, ← h2, ← h3]
    simp only [Int.cast_neg, Int.cast_ofNat, neg_div]
    generalize (L_all_A : A_C) = Lc
    generalize (8 / 405 : A_C) = c1; generalize (476 / 7185 : A_C) = c2; generalize (6916 / 35925 : A_C) = c3
    ring

-- Fast O(N) `letB_intro` bridge for `cacheK.gsq` (`evalGeomSQ k5Ops S_K Q_K`)!
private lemma evalGeomSQ_K5_props :
    let S := ιC_K5 S_K; let Q := ιC_K5 Q_K; let T := ιC_K5 T_K; let x := ιC_K5 x_K; let y := ιC_K5 y_K
    let qC0_K : K5 := -5250 * S_K ^ 4 + 30450 * S_K ^ 3 * Q_K - 64050 * S_K ^ 2 * Q_K ^ 2 + 63000 * S_K * Q_K ^ 3 -
      28350 * Q_K ^ 4 + 6250 * S_K ^ 2 * Q_K - 15000 * S_K * Q_K ^ 2 + 6750 * Q_K ^ 3 +
      6250 * S_K ^ 2 - 15000 * S_K * Q_K + 6750 * Q_K ^ 2
    let qC1_K : K5 := 336 * S_K ^ 4 - 2856 * S_K ^ 3 * Q_K + 8484 * S_K ^ 2 * Q_K ^ 2 - 10080 * S_K * Q_K ^ 3 +
      3780 * Q_K ^ 4 - 40 * S_K ^ 2 * Q_K + 240 * S_K * Q_K ^ 2 - 360 * Q_K ^ 3 -
      40 * S_K ^ 2 + 240 * S_K * Q_K - 360 * Q_K ^ 2
    let qEx0_K : K5 := 6090 * S_K ^ 3 - 25620 * S_K ^ 2 * Q_K + 34650 * S_K * Q_K ^ 2 - 20790 * Q_K ^ 3 -
      6750 * S_K * Q_K + 4050 * Q_K ^ 2 - 6750 * S_K + 4050 * Q_K
    let qEx1_K : K5 := -420 * S_K ^ 3 + 2940 * S_K ^ 2 * Q_K - 6300 * S_K * Q_K ^ 2 + 3780 * Q_K ^ 3
    (cacheK.gsq.H0_7_SQ = 7 * (-2 * S_K ^ 3 + 6 * S_K ^ 2 * Q_K - 3 * S_K * Q_K ^ 2 - 2 * Q_K ^ 3) + 5 * Q_K ^ 2 + 10 * Q_K) ∧
    (cacheK.gsq.S2 = S_K * S_K) ∧
    (ιC_K5 (evalBivLK5 cacheK.gsq.DX2) = DX2_of S Q x) ∧
    (ιC_K5 (evalBivLK5 cacheK.gsq.dDX2_dS) = dDX2_fn 0 S Q x ∧
     ιC_K5 (evalBivLK5 cacheK.gsq.dDX2_dQ) = dDX2_fn 1 S Q x ∧
     ιC_K5 (evalBivLK5 cacheK.gsq.dDX2_dx) = dDX2_fn 3 S Q x) ∧
    (ιC_K5 (evalBivLK5 cacheK.gsq.dF5_0) = 7 * dF5_fn 0 S Q T x y ∧
     ιC_K5 (evalBivLK5 cacheK.gsq.dF5_1) = 7 * dF5_fn 1 S Q T x y ∧
     ιC_K5 (evalBivLK5 cacheK.gsq.dF5_3) = 7 * dF5_fn 3 S Q T x y ∧
     evalBivLK5 cacheK.gsq.dF5_0 = 7 * (3 * x_K ^ 2 + q1_a0 S_K Q_K 1 1) ∧
     evalBivLK5 cacheK.gsq.dF5_1 = 7 * q2_b0 S_K Q_K 1 1 ∧
     evalBivLK5 cacheK.gsq.dF5_3 = 42 * S_K * x_K) ∧
    (polyC (evalUBivLK5 cacheK.gsq.LX_27) = 27 * LX_of S Q x U_C ∧
     (evalUBivLK5 cacheK.gsq.LX_27).eval 0 = 25 * S_K - 45 * Q_K ∧
     (evalUBivLK5 cacheK.gsq.LX_27).eval 1 = 27 * x_K) ∧
    (polyC (evalUBivLK5 cacheK.gsq.dLX_0) = 27 * dLX_fn 0 U_C ∧
     (evalUBivLK5 cacheK.gsq.dLX_0).eval 0 = 25 ∧ (evalUBivLK5 cacheK.gsq.dLX_0).eval 1 = 0) ∧
    (polyC (evalUBivLK5 cacheK.gsq.dLX_1) = 27 * dLX_fn 1 U_C ∧
     (evalUBivLK5 cacheK.gsq.dLX_1).eval 0 = -45 ∧ (evalUBivLK5 cacheK.gsq.dLX_1).eval 1 = 0) ∧
    (polyC (evalUBivLK5 cacheK.gsq.dLX_3) = 27 * dLX_fn 3 U_C ∧
     (evalUBivLK5 cacheK.gsq.dLX_3).eval 0 = 0 ∧ (evalUBivLK5 cacheK.gsq.dLX_3).eval 1 = 27) ∧
    (polyC (evalUBivLK5 cacheK.gsq.PX_0) = (27 / 9 : A_C) * (-25 * S * U_C + 15 * Q * U_C + 9 * x * U_C + 25 * S - 15 * Q) ∧
     (evalUBivLK5 cacheK.gsq.PX_0).eval 1 = 27 * x_K ∧
     polyC (evalUBivLK5 cacheK.gsq.PX_1) = (27 / 9 : A_C) * (30 * (U_C - 1) * S) ∧
     (evalUBivLK5 cacheK.gsq.PX_1).eval 1 = 0 ∧
     polyC (evalUBivLK5 cacheK.gsq.PX_3) = (27 / 9 : A_C) * (18 * U_C * S) ∧
     (evalUBivLK5 cacheK.gsq.PX_3).eval 1 = 54 * S_K) ∧
    (polyC (evalUPolyK5 cacheK.gsq.A1_1_27) = 27 * A1_of S Q U_C 1) ∧
    (polyC (evalUPolyK5 cacheK.gsq.qC_63) = ιC_K5 qC0_K + ιC_K5 qC1_K * U_C ∧
     cacheK.gsq.qC_63.getD 0 0 = qC0_K ∧ cacheK.gsq.qC_63.getD 1 0 = qC1_K ∧
     cacheK.gsq.qEx_63.getD 0 0 = qEx0_K ∧ cacheK.gsq.qEx_63.getD 1 0 = qEx1_K) := by
  intro S Q T x y qC0_K qC1_K qEx0_K qEx1_K
  rw [cacheK_props.2.1]
  let P : GeomSQ K5 → Prop := fun g =>
    (g.H0_7_SQ = 7 * (-2 * S_K ^ 3 + 6 * S_K ^ 2 * Q_K - 3 * S_K * Q_K ^ 2 - 2 * Q_K ^ 3) + 5 * Q_K ^ 2 + 10 * Q_K) ∧
    (g.S2 = S_K * S_K) ∧
    (ιC_K5 (evalBivLK5 g.DX2) = DX2_of S Q x) ∧
    (ιC_K5 (evalBivLK5 g.dDX2_dS) = dDX2_fn 0 S Q x ∧
     ιC_K5 (evalBivLK5 g.dDX2_dQ) = dDX2_fn 1 S Q x ∧
     ιC_K5 (evalBivLK5 g.dDX2_dx) = dDX2_fn 3 S Q x) ∧
    (ιC_K5 (evalBivLK5 g.dF5_0) = 7 * dF5_fn 0 S Q T x y ∧
     ιC_K5 (evalBivLK5 g.dF5_1) = 7 * dF5_fn 1 S Q T x y ∧
     ιC_K5 (evalBivLK5 g.dF5_3) = 7 * dF5_fn 3 S Q T x y ∧
     evalBivLK5 g.dF5_0 = 7 * (3 * x_K ^ 2 + q1_a0 S_K Q_K 1 1) ∧
     evalBivLK5 g.dF5_1 = 7 * q2_b0 S_K Q_K 1 1 ∧
     evalBivLK5 g.dF5_3 = 42 * S_K * x_K) ∧
    (polyC (evalUBivLK5 g.LX_27) = 27 * LX_of S Q x U_C ∧
     (evalUBivLK5 g.LX_27).eval 0 = 25 * S_K - 45 * Q_K ∧
     (evalUBivLK5 g.LX_27).eval 1 = 27 * x_K) ∧
    (polyC (evalUBivLK5 g.dLX_0) = 27 * dLX_fn 0 U_C ∧
     (evalUBivLK5 g.dLX_0).eval 0 = 25 ∧ (evalUBivLK5 g.dLX_0).eval 1 = 0) ∧
    (polyC (evalUBivLK5 g.dLX_1) = 27 * dLX_fn 1 U_C ∧
     (evalUBivLK5 g.dLX_1).eval 0 = -45 ∧ (evalUBivLK5 g.dLX_1).eval 1 = 0) ∧
    (polyC (evalUBivLK5 g.dLX_3) = 27 * dLX_fn 3 U_C ∧
     (evalUBivLK5 g.dLX_3).eval 0 = 0 ∧ (evalUBivLK5 g.dLX_3).eval 1 = 27) ∧
    (polyC (evalUBivLK5 g.PX_0) = (27 / 9 : A_C) * (-25 * S * U_C + 15 * Q * U_C + 9 * x * U_C + 25 * S - 15 * Q) ∧
     (evalUBivLK5 g.PX_0).eval 1 = 27 * x_K ∧
     polyC (evalUBivLK5 g.PX_1) = (27 / 9 : A_C) * (30 * (U_C - 1) * S) ∧
     (evalUBivLK5 g.PX_1).eval 1 = 0 ∧
     polyC (evalUBivLK5 g.PX_3) = (27 / 9 : A_C) * (18 * U_C * S) ∧
     (evalUBivLK5 g.PX_3).eval 1 = 54 * S_K) ∧
    (polyC (evalUPolyK5 g.A1_1_27) = 27 * A1_of S Q U_C 1) ∧
    (polyC (evalUPolyK5 g.qC_63) = ιC_K5 qC0_K + ιC_K5 qC1_K * U_C ∧
     g.qC_63.getD 0 0 = qC0_K ∧ g.qC_63.getD 1 0 = qC1_K ∧
     g.qEx_63.getD 0 0 = qEx0_K ∧ g.qEx_63.getD 1 0 = qEx1_K)
  suffices h : P (evalGeomSQ k5Ops S_K Q_K) from h
  unfold evalGeomSQ
  refine letB_intro fun S2 hS2 => letB_intro fun SQ hSQ => letB_intro fun Q2 hQ2 =>
    letB_intro fun S3 hS3 => letB_intro fun S4 hS4 => letB_intro fun Q3 hQ3 => letB_intro fun Q4 hQ4 =>
    letB_intro fun Sm3Q hSm3Q => letB_intro fun A5 hA5 => letB_intro fun pS hpS => letB_intro fun H0_7_SQ hH0SQ =>
    letB_intro fun u3 hu3 => letB_intro fun u3_2 hu3_2 =>
    letB_intro fun LX0 hLX0 => letB_intro fun LX1 hLX1 => letB_intro fun LX_27 hLX27 =>
    letB_intro fun dLX_0 hdLX0 => letB_intro fun dLX_1 hdLX1 => letB_intro fun dLX_3 hdLX3 =>
    letB_intro fun S2x hS2x => ?_
  dsimp only [P]
  have hS2' : S2 = S_K * S_K := hS2
  have hSQ' : SQ = S_K * Q_K := hSQ
  have hQ2' : Q2 = Q_K * Q_K := hQ2
  have hS3' : S3 = S_K ^ 3 := by rw [hS3, hS2']; dsimp only [k5Ops]; ring
  have hS4' : S4 = S_K ^ 4 := by rw [hS4, hS2']; dsimp only [k5Ops]; ring
  have hQ3' : Q3 = Q_K ^ 3 := by rw [hQ3, hQ2']; dsimp only [k5Ops]; ring
  have hQ4' : Q4 = Q_K ^ 4 := by rw [hQ4, hQ2']; dsimp only [k5Ops]; ring
  have hSm3Q' : Sm3Q = S_K - 3 * Q_K := by rw [hSm3Q]; dsimp only [k5Ops]; push_cast; ring
  have hA5' : A5 = 5 * S_K - 9 * Q_K := by rw [hA5]; dsimp only [k5Ops]; push_cast; ring
  have hS2x' : S2x = 2 * S_K := by rw [hS2x]; dsimp only [k5Ops]; push_cast; ring
  have hu3_eq : evalBivLK5 u3 = x_K - S_K + 2 * Q_K := by
    rw [hu3]; simp only [evalBivLK5, evalYListK5, k5Ops, Int.cast_ofNat]; ring
  have hu3_2_eq : evalBivLK5 u3_2 = (x_K - S_K + 2 * Q_K) ^ 2 := by
    rw [hu3_2, evalBivLK5_bivMul, hu3_eq]; ring
  have hLX0_eq : evalBivLK5 LX0 = 25 * S_K - 45 * Q_K := by
    rw [hLX0]; simp only [bivConst, evalBivLK5, evalYListK5, k5Ops, Int.cast_ofNat]; ring
  have hLX1_eq : evalBivLK5 LX1 = 45 * Q_K - 25 * S_K + 27 * x_K := by
    rw [hLX1]; simp only [evalBivLK5, evalYListK5, k5Ops, Int.cast_ofNat]; ring
  have hLX_ac : polyC (evalUBivLK5 LX_27) = 27 * LX_of S Q x U_C := by
    rw [hLX27]; simp only [evalUBivLK5, hLX0_eq, hLX1_eq, polyC_add, polyC_sub, polyC_mul, polyC_C, polyC_X, polyC_ofNat,
      LX_of, u3_of, u_of, S, Q, x, map_add, map_sub, map_mul, map_ofNat, map_zero, mul_zero, add_zero]; ring
  have hLX_e0 : (evalUBivLK5 LX_27).eval 0 = 25 * S_K - 45 * Q_K := by
    rw [hLX27]; simp [evalUBivLK5, hLX0_eq]
  have hLX_e1 : (evalUBivLK5 LX_27).eval 1 = 27 * x_K := by
    rw [hLX27]; simp [evalUBivLK5, hLX0_eq, hLX1_eq]; ring
  have hd0_ac : polyC (evalUBivLK5 dLX_0) = 27 * dLX_fn 0 U_C := by
    rw [hdLX0]; simp only [evalUBivLK5, bivConst, evalBivLK5, evalYListK5, k5Ops,
      polyC_add, polyC_sub, polyC_neg, polyC_mul, polyC_C, polyC_X, polyC_ofNat, polyC_zero,
      dLX_fn, u_of, Int.cast_neg, Int.cast_ofNat,
      map_add, map_sub, map_neg, map_ofNat, map_zero, mul_zero, add_zero]; ring
  have hd0_e0 : (evalUBivLK5 dLX_0).eval 0 = 25 := by
    rw [hdLX0]; simp [evalUBivLK5, bivConst, evalBivLK5, evalYListK5, k5Ops]
  have hd0_e1 : (evalUBivLK5 dLX_0).eval 1 = 0 := by
    rw [hdLX0]; simp [evalUBivLK5, bivConst, evalBivLK5, evalYListK5, k5Ops]
  have hd1_ac : polyC (evalUBivLK5 dLX_1) = 27 * dLX_fn 1 U_C := by
    rw [hdLX1]; simp only [evalUBivLK5, bivConst, evalBivLK5, evalYListK5, k5Ops,
      polyC_add, polyC_sub, polyC_neg, polyC_mul, polyC_C, polyC_X, polyC_ofNat, polyC_zero,
      dLX_fn, u_of, Int.cast_neg, Int.cast_ofNat,
      map_add, map_sub, map_neg, map_ofNat, map_zero, mul_zero, add_zero]; ring
  have hd1_e0 : (evalUBivLK5 dLX_1).eval 0 = -45 := by
    rw [hdLX1]; simp [evalUBivLK5, bivConst, evalBivLK5, evalYListK5, k5Ops]
  have hd1_e1 : (evalUBivLK5 dLX_1).eval 1 = 0 := by
    rw [hdLX1]; simp [evalUBivLK5, bivConst, evalBivLK5, evalYListK5, k5Ops]
  have hd3_ac : polyC (evalUBivLK5 dLX_3) = 27 * dLX_fn 3 U_C := by
    rw [hdLX3]; simp only [evalUBivLK5, bivConst, evalBivLK5, evalYListK5, k5Ops,
      polyC_add, polyC_sub, polyC_neg, polyC_mul, polyC_C, polyC_X, polyC_ofNat, polyC_zero,
      dLX_fn, u_of, Int.cast_ofNat,
      map_add, map_sub, map_ofNat, map_zero, mul_zero, add_zero]; ring
  have hd3_e0 : (evalUBivLK5 dLX_3).eval 0 = 0 := by
    rw [hdLX3]; simp [evalUBivLK5, evalBivLK5]
  have hd3_e1 : (evalUBivLK5 dLX_3).eval 1 = 27 := by
    rw [hdLX3]; simp [evalUBivLK5, bivConst, evalBivLK5, evalYListK5, k5Ops]
  have hqC0_eq :
      ((((((((((-5250 : K5) * S4 + 30450 * (S3 * Q_K)) + -64050 * (S2 * Q2)) + 63000 * (S_K * Q3)) +
        -28350 * Q4) + 6250 * (S2 * Q_K)) + -15000 * (S_K * Q2)) + 6750 * Q3) + 6250 * S2) +
        -15000 * SQ) + 6750 * Q2 = qC0_K := by
    rw [hS4', hS3', hS2', hSQ', hQ2', hQ3', hQ4']; dsimp only [qC0_K]; ring
  have hqC1_eq :
      ((((((((((336 : K5) * S4 + -2856 * (S3 * Q_K)) + 8484 * (S2 * Q2)) + -10080 * (S_K * Q3)) +
        3780 * Q4) + -40 * (S2 * Q_K)) + 240 * (S_K * Q2)) + -360 * Q3) + -40 * S2) +
        240 * SQ) + -360 * Q2 = qC1_K := by
    rw [hS4', hS3', hS2', hSQ', hQ2', hQ3', hQ4']; dsimp only [qC1_K]; ring
  have hqEx0_eq :
      (((((((6090 : K5) * S3 + -25620 * (S2 * Q_K)) + 34650 * (S_K * Q2)) + -20790 * Q3) +
        -6750 * SQ) + 4050 * Q2) + -6750 * S_K) + 4050 * Q_K = qEx0_K := by
    rw [hS3', hS2', hSQ', hQ2', hQ3']; dsimp only [qEx0_K]; ring
  have hqEx1_eq : (((-420 : K5) * S3 + 2940 * (S2 * Q_K)) + -6300 * (S_K * Q2)) + 3780 * Q3 = qEx1_K := by
    rw [hS3', hS2', hQ2', hQ3']; dsimp only [qEx1_K]; ring
  refine ⟨?_, hS2', ?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨hLX_ac, hLX_e0, hLX_e1⟩,
    ⟨hd0_ac, hd0_e0, hd0_e1⟩, ⟨hd1_ac, hd1_e0, hd1_e1⟩, ⟨hd3_ac, hd3_e0, hd3_e1⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hH0SQ, hpS, hS3', hS2', hQ2', hQ3']; dsimp only [k5Ops]; push_cast; ring
  · simp only [evalBivLK5_bivAdd, evalBivLK5_bivSc, bivConst, evalBivLK5, evalYListK5, hu3_eq, hu3_2_eq,
      hS2', hSQ', hQ2', hQ3', DX2_of, u3_of, S, Q, x, map_add, map_sub, map_mul, map_neg, map_pow,
      map_ofNat, map_zero, Int.cast_neg, Int.cast_ofNat]; dsimp only [k5Ops]; simp only [Int.cast_neg, Int.cast_ofNat, map_intCast, map_neg, map_mul, map_add, map_sub, map_pow, map_ofNat, map_zero, mul_zero, zero_mul, add_zero, zero_add]; ring
  · simp only [evalBivLK5_bivAdd, evalBivLK5_bivSc, bivConst, evalBivLK5, evalYListK5, hu3_eq, hu3_2_eq,
      hS2', hSQ', hQ2', dDX2_fn, u3_of, S, Q, x, map_add, map_sub, map_mul, map_neg, map_pow,
      map_ofNat, map_zero, Int.cast_neg, Int.cast_ofNat]; dsimp only [k5Ops]; simp only [Int.cast_neg, Int.cast_ofNat, map_intCast, map_neg, map_mul, map_add, map_sub, map_ofNat, map_zero, mul_zero, zero_mul, add_zero, zero_add]; ring
  · simp only [evalBivLK5_bivAdd, evalBivLK5_bivSc, bivConst, evalBivLK5, evalYListK5, hu3_eq,
      hS2', hSQ', hQ2', dDX2_fn, u3_of, S, Q, x, map_add, map_sub, map_mul, map_neg, map_pow,
      map_ofNat, map_zero, Int.cast_neg, Int.cast_ofNat]; dsimp only [k5Ops]; simp only [Int.cast_neg, Int.cast_ofNat, map_intCast, map_neg, map_mul, map_add, map_sub, map_ofNat, map_zero, mul_zero, zero_mul, add_zero, zero_add]; ring
  · simp only [evalBivLK5_bivAdd, evalBivLK5_bivSc, bivConst, evalBivLK5, evalYListK5, hu3_eq,
      hS2', hSQ', dDX2_fn, u3_of, S, Q, x, map_add, map_sub, map_mul, map_neg, map_pow,
      map_ofNat, map_zero, Int.cast_neg, Int.cast_ofNat]; dsimp only [k5Ops]; simp only [Int.cast_neg, Int.cast_ofNat, map_intCast, map_neg, map_mul, map_add, map_sub, map_ofNat, map_zero, mul_zero, zero_mul, add_zero, zero_add]; ring
  · simp only [evalBivLK5, evalYListK5, hS2', hSQ', hQ2', k5Ops, dF5_fn, dH0_fn, S, Q, T, x, y,
      map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_zero, Int.cast_neg, Int.cast_ofNat]; ring
  · simp only [evalBivLK5, evalYListK5, hS2', hSQ', hQ2', k5Ops, dF5_fn, dH0_fn, S, Q, T, x, y,
      map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_zero, Int.cast_neg, Int.cast_ofNat]; ring
  · simp only [evalBivLK5, evalYListK5, k5Ops, dF5_fn, S, Q, T, x, y,
      map_add, map_mul, map_ofNat, map_zero, Int.cast_ofNat]; ring
  · simp only [evalBivLK5, evalYListK5, hS2', hSQ', hQ2', k5Ops, q1_a0, dH_dS, Int.cast_neg, Int.cast_ofNat]; ring
  · simp only [evalBivLK5, evalYListK5, hS2', hSQ', hQ2', k5Ops, q2_b0, dH_dQ, Int.cast_neg, Int.cast_ofNat]; ring
  · simp only [evalBivLK5, evalYListK5, k5Ops, Int.cast_ofNat]; ring
  · simp only [evalUBivLK5_ubAdd, evalUBivLK5_ubSc, polyC_add, polyC_mul, polyC_C, polyC_ofNat, hS2x', hd0_ac, hLX_ac,
      dLX_fn, LX_of, u3_of, u_of, S, Q, x, map_mul, map_ofNat]; ring
  · simp only [evalUBivLK5_ubAdd, evalUBivLK5_ubSc, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      hd0_e1, hLX_e1, mul_zero, zero_add]
  · simp only [evalUBivLK5_ubSc, polyC_mul, polyC_C, polyC_ofNat, hS2x', hd1_ac, dLX_fn, u_of, S, map_mul, map_ofNat]; ring
  · simp only [evalUBivLK5_ubSc, Polynomial.eval_mul, Polynomial.eval_C, hd1_e1, mul_zero]
  · simp only [evalUBivLK5_ubSc, polyC_mul, polyC_C, polyC_ofNat, hS2x', hd3_ac, dLX_fn, u_of, S, map_mul, map_ofNat]; ring
  · simp only [evalUBivLK5_ubSc, Polynomial.eval_mul, Polynomial.eval_C, hS2x', hd3_e1]; ring
  · simp only [evalUPolyK5, hA5', hSm3Q', k5Ops, polyC_add, polyC_sub, polyC_neg, polyC_mul, polyC_pow, polyC_C, polyC_X, polyC_ofNat, polyC_zero, A1_of, S, Q,
      map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_zero, mul_zero, add_zero,
      Int.cast_neg, Int.cast_ofNat]; ring
  · simp only [evalUPolyK5, k5Ops, Int.cast_neg, Int.cast_ofNat, hqC0_eq, hqC1_eq,
      polyC_add, polyC_mul, polyC_C, polyC_X, map_zero, mul_zero, add_zero]; ring
  · simp only [List.getD_cons_zero, k5Ops, Int.cast_neg, Int.cast_ofNat, hqC0_eq]
  · simp only [List.getD_cons_succ, List.getD_cons_zero, k5Ops, Int.cast_neg, Int.cast_ofNat, hqC1_eq]
  · simp only [List.getD_cons_zero, k5Ops, Int.cast_neg, Int.cast_ofNat, hqEx0_eq]
  · simp only [List.getD_cons_succ, List.getD_cons_zero, k5Ops, Int.cast_neg, Int.cast_ofNat, hqEx1_eq]

-- Fast O(N) `letB_intro` bridge for `gtK` (`evalGeomT k5Ops S_K cacheK.ac.ca_p cacheK.ac.cb_p cacheK.gsq T_K`)!
private lemma evalGeomT_K5_props :
    let S := ιC_K5 S_K; let Q := ιC_K5 Q_K; let T := ιC_K5 T_K
    let x := ιC_K5 x_K; let y := ιC_K5 y_K
    let ca := polyC k5Params.ca_h; let cb := polyC k5Params.cb_h
    let QX_dot := QX_num S Q T x y U_C V_C 0 * cb - QX_num S Q T x y U_C V_C 1 * ca
    let QY_dot := QY_num S Q T x y U_C V_C 0 * cb - QY_num S Q T x y U_C V_C 1 * ca
    let cA1_dot := (H0_of S Q T * dA1_fn 0 S Q U_C V_C - A1_of S Q U_C V_C * dH0_fn 0 S Q T) * cb -
      (H0_of S Q T * dA1_fn 1 S Q U_C V_C - A1_of S Q U_C V_C * dH0_fn 1 S Q T) * ca
    let q1_dot := H0_of S Q T * A1_of S Q U_C V_C * (QY_dot / v_of V_C) +
      H0_of S Q T * B1_of T U_C V_C * (QX_dot / u_of U_C) +
      (cA1_dot / v_of V_C) * EB_of S Q T x y U_C V_C
    (gtK.H0_7 = 7 * H0_of S_K Q_K T_K) ∧
    (gtK.H0_7_2 = gtK.H0_7 ^ 2) ∧
    (gtK.Av0_243 = 243 * k5Params.Av0) ∧
    (gtK.Cv0_243 = 243 * k5Params.Cv0) ∧
    (gtK.Cv0_243 = -25 * gtK.Cv0_int) ∧
    (polyC Bv_1701_p = 1701 * (ιC_K5 k5Params.Av0 * polyC k5Params.bW)) ∧
    (polyC (evalUBivLK5 gtK.qX_0_sc) + V_C * polyC (evalUBivLK5 gtK.qX_1_sc) = 321489 * (QX_dot / u_of U_C)) ∧
    (polyC (evalUBivLK5 gtK.qY_0_321489) - 9 * (321489 / 63 : A_C) * polyC (evalUBivLK5 gtK.DY2_qE_63) * U_C * ιC_K5 k5Params.Av0 * V_C =
      321489 * (QY_dot / v_of V_C)) ∧
    ((M_mid_int : A_C) * q1_dot =
      ιC_K5 k5Params.Cv0 * U_C * polyC (evalUBivLK5 gtK.q1_0_div_sc) +
      (1 / 243 : A_C) * polyC (evalUBivLK5 gtK.q1_1_sc) * V_C +
      ιC_K5 k5Params.Av0 * U_C * polyC (evalUBivLK5 gtK.q1_2_div_sc) * V_C ^ 2) ∧
    ((evalUBivLK5 gtK.qX_0_sc).eval 0 = 0 ∧
     (evalUBivLK5 gtK.qY_0_321489).eval 0 = 0 ∧
     (evalUBivLK5 gtK.q1_0_div_sc).eval 0 = 0 ∧
     (evalUBivLK5 gtK.q1_1_sc).eval 0 = 0) := by
  intro S Q T x y ca cb QX_dot QY_dot cA1_dot q1_dot
  let P : GeomT K5 → Prop := fun gt =>
    (gt.H0_7 = 7 * H0_of S_K Q_K T_K) ∧
    (gt.H0_7_2 = gt.H0_7 ^ 2) ∧
    (gt.Av0_243 = 243 * k5Params.Av0) ∧
    (gt.Cv0_243 = 243 * k5Params.Cv0) ∧
    (gt.Cv0_243 = -25 * gt.Cv0_int) ∧
    (polyC (evalUPolyK5 cacheK.ac.Bv_SQ + Polynomial.C gt.Bv1_T_1701 * Polynomial.X) =
      1701 * (ιC_K5 k5Params.Av0 * polyC k5Params.bW)) ∧
    (polyC (evalUBivLK5 gt.qX_0_sc) + V_C * polyC (evalUBivLK5 gt.qX_1_sc) = 321489 * (QX_dot / u_of U_C)) ∧
    (polyC (evalUBivLK5 gt.qY_0_321489) - 9 * (321489 / 63 : A_C) * polyC (evalUBivLK5 gt.DY2_qE_63) * U_C * ιC_K5 k5Params.Av0 * V_C =
      321489 * (QY_dot / v_of V_C)) ∧
    ((M_mid_int : A_C) * q1_dot =
      ιC_K5 k5Params.Cv0 * U_C * polyC (evalUBivLK5 gt.q1_0_div_sc) +
      (1 / 243 : A_C) * polyC (evalUBivLK5 gt.q1_1_sc) * V_C +
      ιC_K5 k5Params.Av0 * U_C * polyC (evalUBivLK5 gt.q1_2_div_sc) * V_C ^ 2) ∧
    ((evalUBivLK5 gt.qX_0_sc).eval 0 = 0 ∧
     (evalUBivLK5 gt.qY_0_321489).eval 0 = 0 ∧
     (evalUBivLK5 gt.q1_0_div_sc).eval 0 = 0 ∧
     (evalUBivLK5 gt.q1_1_sc).eval 0 = 0)
  suffices h : P (evalGeomT k5Ops S_K cacheK.ac.ca_p cacheK.ac.cb_p cacheK.gsq T_K) from h
  unfold evalGeomT
  refine letB_intro fun T2 hT2 => letB_intro fun T3 hT3 => letB_intro fun pT hpT =>
    letB_intro fun H0_7 hH0_7 => letB_intro fun H0_7_2 hH0_7_2 =>
    letB_intro fun Tm3 hTm3 => letB_intro fun Av0_243 hAv0_243 =>
    letB_intro fun T59 hT59 => letB_intro fun Cv0_int hCv0_int => letB_intro fun Cv0_243 hCv0_243 =>
    letB_intro fun Bv1_T_1701 hBv1_T => letB_intro fun v3 hv3 => letB_intro fun v3_2 hv3_2 =>
    letB_intro fun DY2 hDY2_d => letB_intro fun dDY2_dy hdDY2_d =>
    letB_intro fun ST hST => letB_intro fun ST2 hST2 => letB_intro fun W2 hW2 =>
    letB_intro fun dF5_4 hdF5_4 => letB_intro fun LY0 hLY0 => letB_intro fun LY1 hLY1 =>
    letB_intro fun PY_4_1 hPY41 =>
    letB_intro fun br0_0 hbr0_0 => letB_intro fun br1_0 hbr1_0 =>
    letB_intro fun br0_1 hbr0_1 => letB_intro fun br1_1 hbr1_1 =>
    letB_intro fun br0_3 hbr0_3 => letB_intro fun br1_3 hbr1_3 => letB_intro fun br1_4 hbr1_4 =>
    letB_intro fun omF1_0 homF1_0 => letB_intro fun omF1_1 homF1_1 =>
    letB_intro fun dYF0_0 hdYF0_0 => letB_intro fun dYF0_1 hdYF0_1 =>
    letB_intro fun dYF1_0 hdYF1_0 => letB_intro fun dYF1_1 hdYF1_1 =>
    letB_intro fun dXF0_0 hdXF0_0 => letB_intro fun dXF0_1 hdXF0_1 =>
    letB_intro fun QX0_0 hQX0_0 => letB_intro fun QX0_1 hQX0_1 =>
    letB_intro fun QX1_0 hQX1_0 => letB_intro fun QX1_1 hQX1_1 =>
    letB_intro fun QY0_0 hQY0_0 => letB_intro fun QY0_1 hQY0_1 =>
    letB_intro fun EB0_5103 hEB0 => letB_intro fun EB1_5103 hEB1 =>
    letB_intro fun div0 hdiv0 => letB_intro fun div1 hdiv1 =>
    letB_intro fun QY_dot_0_sc hQYd0 => letB_intro fun c4S2T2 hc4S2T2 =>
    letB_intro fun qE_63 hqE_63 => letB_intro fun DY2_qE_63 hDYqE =>
    letB_intro fun qY_0_321489 hqY0 => ?_
  dsimp only [P]
  have hacP := evalACache_K5_props
  have hgsqP := evalGeomSQ_K5_props
  have hca_p : polyC (evalUPolyK5 cacheK.ac.ca_p) = 567 * ca := by rw [hacP.1, polyC_mul, polyC_C]; simp [ca, map_ofNat]
  have hcb_p : polyC (evalUPolyK5 cacheK.ac.cb_p) = 567 * cb := by rw [hacP.2.1, polyC_mul, polyC_C]; simp [cb, map_ofNat]
  have hca_e0 := hacP.2.2.1
  have hcb_e0 := hacP.2.2.2.1
  have hca_e1 : (evalUPolyK5 cacheK.ac.ca_p).eval 1 = 567 * q1_a0 S_K Q_K 1 1 := by
    rw [hacP.1, Polynomial.eval_mul, Polynomial.eval_C]
    simp only [CoverParams.ca_h, CoverParams.quadU, CoverParams.inv9, CoverParams.inv27,
      CoverParams.inv81, k5Params_inv3, k5Params_S, k5Params_Q,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
      q1_a0, dH_dS]; ring
  have hcb_e1 : (evalUPolyK5 cacheK.ac.cb_p).eval 1 = 567 * q2_b0 S_K Q_K 1 1 := by
    rw [hacP.2.1, Polynomial.eval_mul, Polynomial.eval_C]
    simp only [CoverParams.cb_h, CoverParams.quadU, CoverParams.inv9, CoverParams.inv27,
      CoverParams.inv81, k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
      q2_b0, dH_dQ]; ring
  -- Scalar identities
  have hT2' : T2 = T_K * T_K := hT2
  have hT3' : T3 = T_K ^ 3 := by rw [hT3, hT2']; dsimp only [k5Ops]; ring
  have hH0 : H0_7 = 7 * H0_of S_K Q_K T_K := by
    rw [hH0_7, hpT, hgsqP.1, hT3', hT2']; dsimp only [k5Ops, H0_of]; push_cast; ring
  have hH0_2 : H0_7_2 = H0_7 ^ 2 := by rw [hH0_7_2]; dsimp only [k5Ops]; ring
  have hAv0 : Av0_243 = 243 * k5Params.Av0 := by
    rw [hAv0_243, hTm3]; simp only [k5Ops, CoverParams.Av0, CoverParams.inv243, k5Params_inv3, k5Params_T,
      Int.cast_neg, Int.cast_ofNat]; ring
  have hCv0 : Cv0_243 = 243 * k5Params.Cv0 := by
    rw [hCv0_243, hCv0_int, hT59]; simp only [k5Ops, CoverParams.Cv0, CoverParams.inv243, k5Params_inv3, k5Params_T,
      Int.cast_neg, Int.cast_ofNat]; ring
  have hCv0i : Cv0_243 = -25 * Cv0_int := by rw [hCv0_243]; dsimp only [k5Ops]; push_cast; ring
  have hBv1701 : polyC (evalUPolyK5 cacheK.ac.Bv_SQ + Polynomial.C Bv1_T_1701 * Polynomial.X) =
      1701 * (ιC_K5 k5Params.Av0 * polyC k5Params.bW) := by
    have hbW : ιC_K5 k5Params.Av0 * polyC k5Params.bW = polyC k5Params.Bv := by
      rw [CoverParams.bW, polyC_mul, polyC_C, ← mul_assoc, ← map_mul,
        k5Params_Av0_mul_inv, map_one, one_mul]
    rw [hbW, polyC_add, polyC_mul, polyC_C, polyC_X, hacP.2.2.2.2.2.2.2.1, hBv1_T, hT3', hT2']
    simp only [k5Ops, CoverParams.Bv, CoverParams.Bv0, CoverParams.Bv1, CoverParams.Bv2, CoverParams.quadU,
      CoverParams.inv9, CoverParams.inv27, CoverParams.inv243, k5Params_inv3, k5Params_inv7,
      k5Params_S, k5Params_Q, k5Params_T, polyC_add, polyC_sub, polyC_neg, polyC_mul, polyC_pow, polyC_C, polyC_X, polyC_ofNat, polyC_zero, polyC_one,
      map_add, map_sub, map_mul, map_div₀, map_inv₀, map_neg, map_pow, map_ofNat, map_one, map_zero, Int.cast_neg, Int.cast_ofNat]; ring
  -- BivL & basic `A_C` evaluations
  have hv3_eq : evalBivLK5 v3 = y_K - T_K + 2 := by rw [hv3]; simp only [evalBivLK5, evalYListK5, k5Ops, Int.cast_ofNat]; ring
  have hv3_2_eq : evalBivLK5 v3_2 = (y_K - T_K + 2) ^ 2 := by rw [hv3_2, evalBivLK5_bivMul, hv3_eq]; ring
  have hDY2 : ιC_K5 (evalBivLK5 DY2) = DY2_of T y := by
    rw [hDY2_d]; simp only [evalBivLK5_bivAdd, evalBivLK5_bivSc, bivConst, evalBivLK5, evalYListK5,
      hv3_eq, hv3_2_eq, hT2', DY2_of, v3_of, T, y, map_add, map_sub, map_mul, map_neg, map_pow,
      map_ofNat, map_zero, Int.cast_neg, Int.cast_ofNat]; dsimp only [k5Ops]; simp only [Int.cast_neg, Int.cast_ofNat, map_intCast, map_neg, map_mul, map_add, map_sub, map_ofNat, map_zero, mul_zero, zero_mul, add_zero, zero_add]; ring
  have hdDY2 : ιC_K5 (evalBivLK5 dDY2_dy) = dDY2_fn 4 T y := by
    rw [hdDY2_d]; simp only [evalBivLK5_bivAdd, evalBivLK5_bivSc, bivConst, evalBivLK5, evalYListK5,
      hv3_eq, hT2', dDY2_fn, v3_of, T, y, map_add, map_sub, map_mul, map_neg, map_ofNat, map_zero,
      Int.cast_neg, Int.cast_ofNat]; dsimp only [k5Ops]; simp only [Int.cast_neg, Int.cast_ofNat, map_intCast, map_neg, map_mul, map_add, map_sub, map_ofNat, map_zero, mul_zero, zero_mul, add_zero, zero_add]; ring
  have hST' : ST = S_K * T_K := hST
  have hST2' : ST2 = 2 * (S_K * T_K) := by rw [hST2, hST']; dsimp only [k5Ops]; push_cast; ring
  have hW2_eq : ιC_K5 (evalBivLK5 W2) = S * T * DX2_of S Q x * DY2_of T y := by
    rw [hW2, evalBivLK5_bivSc, evalBivLK5_bivMul, hST', map_mul, map_mul, map_mul, hgsqP.2.2.1, hDY2]; ring
  have hdF5_4_eq : ιC_K5 (evalBivLK5 dF5_4) = 7 * dF5_fn 4 S Q T x y := by
    rw [hdF5_4]; simp only [evalBivLK5, evalYListK5, k5Ops, dF5_fn, T, y, map_add, map_mul, map_ofNat, map_zero, Int.cast_ofNat]; ring
  have hLY0_K : evalBivLK5 LY0 = 25 * T_K - 45 := by
    rw [hLY0]; simp only [bivConst, evalBivLK5, evalYListK5, k5Ops, Int.cast_ofNat]; ring
  have hLY1_K : evalBivLK5 LY1 = 45 - 25 * T_K + 27 * y_K := by
    rw [hLY1]; simp only [evalBivLK5, evalYListK5, k5Ops, Int.cast_ofNat]; ring
  have hLY0_AC : ιC_K5 (evalBivLK5 LY0) = 27 * LY_of T y 0 := by
    rw [hLY0_K]; simp only [LY_of, v3_of, v_of, T, map_sub, map_mul, map_ofNat]; ring
  have hLY_eq : ιC_K5 (evalBivLK5 LY0) + V_C * ιC_K5 (evalBivLK5 LY1) = 27 * LY_of T y V_C := by
    rw [hLY0_K, hLY1_K]; simp only [LY_of, v3_of, v_of, T, y, map_add, map_sub, map_mul, map_ofNat]; ring
  have hPY_K : evalBivLK5 PY_4_1 = 54 * T_K := by
    rw [hPY41]; simp only [bivConst, evalBivLK5, evalYListK5, k5Ops, Int.cast_ofNat]; ring
  -- Evaluate `br0_0..br1_4`, `omF1_*`, `dYF*`, `QX*` at `U = 0`, `U = 1`, and in `A_C`!
  have hbr0_3_e0 : (evalUBivLK5 br0_3).eval 0 = 0 := by
    rw [hbr0_3, evalUBivLK5_ubSc, evalUBivLK5_ubBmul]; simp [hgsqP.2.2.2.2.2.2.2.2.1.2.1]
  have hbr0_0_e0 : (evalUBivLK5 br0_0).eval 0 = -(2 * (S_K * T_K)) * ((25 * T_K - 45) * 25) - T_K * ((25 * T_K - 45) * (25 * S_K - 45 * Q_K)) := by
    rw [hbr0_0]; simp only [evalUBivLK5_ubSub, evalUBivLK5_ubSc, evalUBivLK5_ubBmul,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hST2', hLY0_K,
      hgsqP.2.2.2.2.2.2.1.2.1, hgsqP.2.2.2.2.2.1.2.1]; dsimp only [k5Ops]
  have hbr0_1_e0 : (evalUBivLK5 br0_1).eval 0 = -(2 * (S_K * T_K)) * ((25 * T_K - 45) * (-45)) := by
    rw [hbr0_1]; simp only [evalUBivLK5_ubSc, evalUBivLK5_ubBmul,
      Polynomial.eval_mul, Polynomial.eval_C, hST2', hLY0_K, hgsqP.2.2.2.2.2.2.2.1.2.1]; dsimp only [k5Ops]
  have hbr0_cancel : (evalUBivLK5 br0_0).eval 0 * (evalUPolyK5 cacheK.ac.cb_p).eval 0 -
      (evalUBivLK5 br0_1).eval 0 * (evalUPolyK5 cacheK.ac.ca_p).eval 0 = 0 := by
    rw [hbr0_0_e0, hbr0_1_e0, hcb_e0, hca_e0]; ring
  have hbr_e1 :
      (evalUBivLK5 br0_0).eval 1 = -T_K * (evalBivLK5 LY0 * (27 * x_K)) ∧
      (evalUBivLK5 br0_1).eval 1 = 0 ∧
      (evalUBivLK5 br0_3).eval 1 = -(2 * (S_K * T_K)) * (evalBivLK5 LY0 * 27) ∧
      (evalUBivLK5 br1_0).eval 1 = -T_K * (evalBivLK5 LY1 * (27 * x_K)) ∧
      (evalUBivLK5 br1_1).eval 1 = 0 ∧
      (evalUBivLK5 br1_3).eval 1 = -(2 * (S_K * T_K)) * (evalBivLK5 LY1 * 27) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hbr0_0]; simp [evalUBivLK5_ubSub, evalUBivLK5_ubSc, evalUBivLK5_ubBmul, hgsqP.2.2.2.2.2.2.1.2.2, hgsqP.2.2.2.2.2.1.2.2]
    · rw [hbr0_1]; simp [evalUBivLK5_ubSc, evalUBivLK5_ubBmul, hgsqP.2.2.2.2.2.2.2.1.2.2]
    · rw [hbr0_3]; simp [evalUBivLK5_ubSc, evalUBivLK5_ubBmul, hST2', hgsqP.2.2.2.2.2.2.2.2.1.2.2]; dsimp only [k5Ops]; ring
    · rw [hbr1_0]; simp [evalUBivLK5_ubSub, evalUBivLK5_ubSc, evalUBivLK5_ubBmul, hgsqP.2.2.2.2.2.2.1.2.2, hgsqP.2.2.2.2.2.1.2.2]
    · rw [hbr1_1]; simp [evalUBivLK5_ubSc, evalUBivLK5_ubBmul, hgsqP.2.2.2.2.2.2.2.1.2.2]
    · rw [hbr1_3]; simp [evalUBivLK5_ubSc, evalUBivLK5_ubBmul, hST2', hgsqP.2.2.2.2.2.2.2.2.1.2.2]; dsimp only [k5Ops]; ring
  have hdQX0_e1 : (evalUBivLK5 (ubSub k5Ops (ubMulU k5Ops cacheK.ac.cb_p QX0_0) (ubMulU k5Ops cacheK.ac.ca_p QX0_1))).eval 1 = 0 := by
    rw [hQX0_0, hQX0_1, hdYF0_0, hdYF0_1]
    simp only [evalUBivLK5_ubSub, evalUBivLK5_ubSc, evalUBivLK5_ubBmul, evalUBivLK5_ubMulU,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      hcb_e1, hca_e1, hbr_e1.1, hbr_e1.2.1, hbr_e1.2.2.1,
      hgsqP.2.2.2.2.1.2.2.2.1, hgsqP.2.2.2.2.1.2.2.2.2.1, hgsqP.2.2.2.2.1.2.2.2.2.2]; ring
  have hdQX1_e1 : (evalUBivLK5 (ubSub k5Ops (ubMulU k5Ops cacheK.ac.cb_p QX1_0) (ubMulU k5Ops cacheK.ac.ca_p QX1_1))).eval 1 = 0 := by
    rw [hQX1_0, hQX1_1, hdYF1_0, hdYF1_1, homF1_0, homF1_1]
    simp only [evalUBivLK5_ubAdd, evalUBivLK5_ubSub, evalUBivLK5_ubNeg, evalUBivLK5_ubSc, evalUBivLK5_ubBmul, evalUBivLK5_ubMulU,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul, Polynomial.eval_C,
      hcb_e1, hca_e1, hbr_e1.2.2.2.1, hbr_e1.2.2.2.2.1, hbr_e1.2.2.2.2.2, hPY_K,
      hgsqP.2.2.2.2.1.2.2.2.1, hgsqP.2.2.2.2.1.2.2.2.2.1, hgsqP.2.2.2.2.1.2.2.2.2.2,
      hgsqP.2.2.2.2.2.2.2.2.2.1.2.1, hgsqP.2.2.2.2.2.2.2.2.2.1.2.2.2.1, hgsqP.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2]; ring
  have hrem0 : evalBivLK5 div0.1 = 0 := by
    rw [hdiv0]
    have h := congrArg (fun p : K5[X] => p.eval 1)
      (evalUBivLK5_ubSynDiv1Rem (ubSub k5Ops (ubMulU k5Ops cacheK.ac.cb_p QX0_0) (ubMulU k5Ops cacheK.ac.ca_p QX0_1)))
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_one, sub_self, zero_mul, add_zero, hdQX0_e1] at h
    exact h.symm
  have hrem1 : evalBivLK5 div1.1 = 0 := by
    rw [hdiv1]
    have h := congrArg (fun p : K5[X] => p.eval 1)
      (evalUBivLK5_ubSynDiv1Rem (ubSub k5Ops (ubMulU k5Ops cacheK.ac.cb_p QX1_0) (ubMulU k5Ops cacheK.ac.ca_p QX1_1)))
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_one, sub_self, zero_mul, add_zero, hdQX1_e1] at h
    exact h.symm
  -- `A_C` evaluation of `QX`, `QY`, `EB`, `q1`!
  have hdQX_AC :
      polyC (evalUBivLK5 (ubSub k5Ops (ubMulU k5Ops cacheK.ac.cb_p QX0_0) (ubMulU k5Ops cacheK.ac.ca_p QX0_1))) +
      V_C * polyC (evalUBivLK5 (ubSub k5Ops (ubMulU k5Ops cacheK.ac.cb_p QX1_0) (ubMulU k5Ops cacheK.ac.ca_p QX1_1))) =
      2893401 * QX_dot := by
    rw [hQX0_0, hQX0_1, hQX1_0, hQX1_1, hdYF0_0, hdYF0_1, hdYF1_0, hdYF1_1, homF1_0, homF1_1,
      hbr0_0, hbr0_1, hbr0_3, hbr1_0, hbr1_1, hbr1_3]
    simp only [evalUBivLK5_ubAdd, evalUBivLK5_ubSub, evalUBivLK5_ubNeg, evalUBivLK5_ubSc, evalUBivLK5_ubBmul, evalUBivLK5_ubMulU, polyC_add, polyC_sub, polyC_neg, polyC_mul, polyC_C, polyC_ofNat, hST', hST2', hPY_K,
      map_mul, map_neg, map_ofNat, hca_p, hcb_p, hgsqP.2.2.1, hDY2, hdDY2,
      hgsqP.2.2.2.2.1.1, hgsqP.2.2.2.2.1.2.1, hgsqP.2.2.2.2.1.2.2.1,
      hgsqP.2.2.2.2.2.1.1, hgsqP.2.2.2.2.2.2.1.1, hgsqP.2.2.2.2.2.2.2.1.1, hgsqP.2.2.2.2.2.2.2.2.1.1,
      hgsqP.2.2.2.2.2.2.2.2.2.1.1, hgsqP.2.2.2.2.2.2.2.2.2.1.2.2.1, hgsqP.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1]; dsimp only [k5Ops]; simp only [Int.cast_neg, Int.cast_ofNat, map_intCast, map_neg, map_mul, map_add, map_sub, map_ofNat, mul_zero, zero_mul, add_zero, zero_add]
    have hd0 : dDY2_fn 0 T y = 0 := rfl
    have hd1 : dDY2_fn 1 T y = 0 := rfl
    have hd3 : dDY2_fn 3 T y = 0 := rfl
    simp only [QX_dot, QX_num, Omega_F, dDY2_F, F_contract, om_fn, br_fn, hd0, hd1, hd3, dLY_fn,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    dsimp only [S, Q, T, x, y] at hLY_eq ⊢
    linear_combination -107163 * DX2_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 x_K) * ιC_K5 S_K * ιC_K5 T_K ^ 2 * dDY2_fn 4 (ιC_K5 T_K) (ιC_K5 y_K) *
      (dF5_fn 3 (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) * ((2 * ιC_K5 S_K * dLX_fn 0 U_C + LX_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 x_K) U_C) * cb - 2 * ιC_K5 S_K * dLX_fn 1 U_C * ca) -
       2 * ιC_K5 S_K * dLX_fn 3 U_C * (dF5_fn 0 (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) * cb - dF5_fn 1 (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) * ca)) * hLY_eq
  have hqX_AC : polyC (evalUBivLK5 div0.2) + V_C * polyC (evalUBivLK5 div1.2) = 321489 * (QX_dot / u_of U_C) := by
    have h0 := congrArg polyC (evalUBivLK5_ubSynDiv1Rem (ubSub k5Ops (ubMulU k5Ops cacheK.ac.cb_p QX0_0) (ubMulU k5Ops cacheK.ac.ca_p QX0_1)))
    have h1 := congrArg polyC (evalUBivLK5_ubSynDiv1Rem (ubSub k5Ops (ubMulU k5Ops cacheK.ac.cb_p QX1_0) (ubMulU k5Ops cacheK.ac.ca_p QX1_1)))
    rw [← hdiv0, hrem0, map_zero, zero_add, polyC_mul, polyC_sub, polyC_X, polyC_one] at h0
    rw [← hdiv1, hrem1, map_zero, zero_add, polyC_mul, polyC_sub, polyC_X, polyC_one] at h1
    have hu_ne : U_C - 1 ≠ 0 := fun h => u_of_U_C_ne_zero (by simp [u_of, h])
    apply mul_left_cancel₀ hu_ne
    calc (U_C - 1) * (polyC (evalUBivLK5 div0.2) + V_C * polyC (evalUBivLK5 div1.2)) =
          polyC (evalUBivLK5 (ubSub k5Ops (ubMulU k5Ops cacheK.ac.cb_p QX0_0) (ubMulU k5Ops cacheK.ac.ca_p QX0_1))) +
          V_C * polyC (evalUBivLK5 (ubSub k5Ops (ubMulU k5Ops cacheK.ac.cb_p QX1_0) (ubMulU k5Ops cacheK.ac.ca_p QX1_1))) := by
            rw [h0, h1]; ring
      _ = 2893401 * QX_dot := hdQX_AC
      _ = (U_C - 1) * (321489 * (QX_dot / u_of U_C)) := by
          have hu := u_of_U_C_ne_zero; rw [u_of] at hu ⊢; field_simp [hu]; ring
  have hQYd0_AC : polyC (evalUBivLK5 QY_dot_0_sc) =
      2893401 * (QY_num S Q T x y U_C 0 0 * cb - QY_num S Q T x y U_C 0 1 * ca) := by
    rw [hQYd0, hQY0_0, hQY0_1, hdXF0_0, hdXF0_1, hbr0_0, hbr0_1, hbr0_3]
    simp only [evalUBivLK5_ubSub, evalUBivLK5_ubNeg, evalUBivLK5_ubSc, evalUBivLK5_ubBmul, evalUBivLK5_ubMulU, polyC_sub, polyC_neg, polyC_mul, polyC_C, hST', hST2',
      map_mul, map_neg, map_ofNat, hca_p, hcb_p, hDY2, hdF5_4_eq, hLY0_AC,
      hgsqP.2.2.2.1.1, hgsqP.2.2.2.1.2.1, hgsqP.2.2.2.1.2.2,
      hgsqP.2.2.2.2.2.1.1, hgsqP.2.2.2.2.2.2.1.1, hgsqP.2.2.2.2.2.2.2.1.1, hgsqP.2.2.2.2.2.2.2.2.1.1]; dsimp only [k5Ops]; simp only [Int.cast_neg, Int.cast_ofNat, map_intCast, map_neg, map_mul, map_add, map_sub, map_ofNat, mul_zero, zero_mul, add_zero, zero_add]
    have hd4 : dDX2_fn 4 S Q x = 0 := rfl
    have hdX4 : dLX_fn 4 U_C = 0 := rfl
    simp only [QY_num, Omega_F, dDX2_F, F_contract, om_fn, br_fn, hd4, hdX4, dLY_fn,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    dsimp only [S, Q, T, x, y]; ring
  have hDYqE_eq : polyC (evalUBivLK5 DY2_qE_63) =
      63 * DY2_of T y * (4 * S ^ 2 * T ^ 2 *
        (((-5250 * S ^ 4 + 30450 * S ^ 3 * Q - 64050 * S ^ 2 * Q ^ 2 + 63000 * S * Q ^ 3 - 28350 * Q ^ 4 +
            6250 * S ^ 2 * Q - 15000 * S * Q ^ 2 + 6750 * Q ^ 3 + 6250 * S ^ 2 - 15000 * S * Q + 6750 * Q ^ 2) +
          (336 * S ^ 4 - 2856 * S ^ 3 * Q + 8484 * S ^ 2 * Q ^ 2 - 10080 * S * Q ^ 3 + 3780 * Q ^ 4 -
            40 * S ^ 2 * Q + 240 * S * Q ^ 2 - 360 * Q ^ 3 - 40 * S ^ 2 + 240 * S * Q - 360 * Q ^ 2) * U_C) +
         x * ((6090 * S ^ 3 - 25620 * S ^ 2 * Q + 34650 * S * Q ^ 2 - 20790 * Q ^ 3 -
            6750 * S * Q + 4050 * Q ^ 2 - 6750 * S + 4050 * Q) +
          (-420 * S ^ 3 + 2940 * S ^ 2 * Q - 6300 * S * Q ^ 2 + 3780 * Q ^ 3) * U_C)) / 63) := by
    rw [hDYqE, evalUBivLK5_ubBmul, polyC_mul, polyC_C, hDY2, hqE_63, hc4S2T2, hgsqP.2.1, hT2']
    simp only [evalUBivLK5, evalBivLK5, evalYListK5, k5Ops, Int.cast_ofNat,
      hgsqP.2.2.2.2.2.2.2.2.2.2.2.2.1, hgsqP.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hgsqP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hgsqP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
      polyC_add, polyC_sub, polyC_neg, polyC_mul, polyC_pow, polyC_C, polyC_X, polyC_ofNat, S, Q, T, x, y,
      map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_zero, mul_zero, add_zero]; ring
  have hAv_A : ιC_K5 k5Params.Av0 = -(4 / 243 : A_C) * (T - 3) ^ 3 := by
    simp only [CoverParams.Av0, CoverParams.inv243, k5Params_inv3, k5Params_T, T,
      map_mul, map_sub, map_neg, map_div₀, map_inv₀, map_pow, map_one, map_ofNat]; ring
  have hCv_A : ιC_K5 k5Params.Cv0 = -(25 / 243 : A_C) * T * (5 * T - 9) ^ 2 := by
    simp only [CoverParams.Cv0, CoverParams.inv243, k5Params_inv3, k5Params_T, T,
      map_mul, map_sub, map_neg, map_div₀, map_inv₀, map_pow, map_one, map_ofNat]; ring
  have hqY_AC : polyC (evalUBivLK5 qY_0_321489) -
      9 * (321489 / 63 : A_C) * polyC (evalUBivLK5 DY2_qE_63) * U_C * ιC_K5 k5Params.Av0 * V_C =
      321489 * (QY_dot / v_of V_C) := by
    have hQY0_eq : polyC (evalUBivLK5 qY_0_321489) =
        -2893401 * (QY_num S Q T x y U_C 0 0 * cb - QY_num S Q T x y U_C 0 1 * ca) +
        189 * ιC_K5 Cv0_243 * U_C * polyC (evalUBivLK5 DY2_qE_63) := by
      rw [hqY0, evalUBivLK5_ubAdd, evalUBivLK5_ubNeg, evalUBivLK5_ubSc, evalUBivLK5_ubShift,
        polyC_add, polyC_neg, polyC_mul, polyC_mul, polyC_C, polyC_X, hQYd0_AC]
      simp only [k5Ops, map_mul, map_intCast, map_ofNat, Int.cast_ofNat]; ring
    have hQY_lin : QY_dot = V_C * (QY_num S Q T x y U_C 1 0 * cb - QY_num S Q T x y U_C 1 1 * ca) -
        (V_C - 1) * (QY_num S Q T x y U_C 0 0 * cb - QY_num S Q T x y U_C 0 1 * ca) := by
      have h1 : ∀ i : Fin 3, QY_num S Q T x y U_C V_C i =
          V_C * QY_num S Q T x y U_C 1 i - (V_C - 1) * QY_num S Q T x y U_C 0 i := fun i => by
        fin_cases i <;> (simp only [QY_num, Omega_F, dDX2_F, F_contract, om_fn, br_fn, LY_of, dLY_fn, v3_of, v_of]; ring)
      simp only [QY_dot, h1 0, h1 1]; ring
    have hV1 := QY_dot_V1_ring S Q T x y U_C
    rw [← polyC_ca_cb_eq_q10_q20.1, ← polyC_ca_cb_eq_q10_q20.2] at hV1
    have hV_factor : V_C * (u_of U_C * A1_of S Q U_C 1 - 3 * U_C * (S * x ^ 2 + T * y ^ 2)) =
        -(V_C - 1) * U_C * (ιC_K5 k5Params.Av0 * V_C - ιC_K5 k5Params.Cv0) := by
      have hsp := E0_V_split S Q T U_C V_C
      have hHcub0 : H_cub S Q T 1 U_C V_C = 0 := by simpa [E_fn, S, Q, T] using E0_AC_zero 0 0
      rw [hHcub0, ← hAv_A, ← hCv_A] at hsp
      have hF5_0 : F5_of S Q T x y = 0 := F5_of_AC
      unfold F5_of at hF5_0
      linear_combination -hsp - U_C * V_C * hF5_0
    rw [hQY0_eq, hCv0, map_mul, map_ofNat, ← mul_div_assoc (321489 : A_C), eq_div_iff v_of_V_C_ne_zero, hQY_lin, hV1]
    have hcomb : V_C * (DY2_of T y *
        (4 * S ^ 2 * T ^ 2 *
          (((-5250 * S ^ 4 + 30450 * S ^ 3 * Q - 64050 * S ^ 2 * Q ^ 2 + 63000 * S * Q ^ 3 - 28350 * Q ^ 4 +
              6250 * S ^ 2 * Q - 15000 * S * Q ^ 2 + 6750 * Q ^ 3 + 6250 * S ^ 2 - 15000 * S * Q + 6750 * Q ^ 2) +
            (336 * S ^ 4 - 2856 * S ^ 3 * Q + 8484 * S ^ 2 * Q ^ 2 - 10080 * S * Q ^ 3 + 3780 * Q ^ 4 -
              40 * S ^ 2 * Q + 240 * S * Q ^ 2 - 360 * Q ^ 3 - 40 * S ^ 2 + 240 * S * Q - 360 * Q ^ 2) * U_C) +
           x * ((6090 * S ^ 3 - 25620 * S ^ 2 * Q + 34650 * S * Q ^ 2 - 20790 * Q ^ 3 -
              6750 * S * Q + 4050 * Q ^ 2 - 6750 * S + 4050 * Q) +
            (-420 * S ^ 3 + 2940 * S ^ 2 * Q - 6300 * S * Q ^ 2 + 3780 * Q ^ 3) * U_C)) / 63) *
        (u_of U_C * A1_of S Q U_C 1 - 3 * U_C * (S * x ^ 2 + T * y ^ 2))) =
        (polyC (evalUBivLK5 DY2_qE_63) / 63) * (-(V_C - 1) * U_C * (ιC_K5 k5Params.Av0 * V_C - ιC_K5 k5Params.Cv0)) := by
      rw [hDYqE_eq, ← hV_factor]; ring
    rw [hcomb, v_of]; ring
  have hEB_AC : polyC (evalUBivLK5 EB0_5103) + V_C * polyC (evalUBivLK5 EB1_5103) = 5103 * EB_of S Q T x y U_C V_C := by
    rw [hEB0, hEB1, hbr0_3, hbr1_3, hbr1_4]
    simp only [evalUBivLK5_ubSub, evalUBivLK5_ubSc, evalUBivLK5_ubBmul,
      polyC_sub, polyC_mul, polyC_C, hST2', map_mul, map_neg, map_intCast, Int.cast_ofNat,
      hW2_eq, hdF5_4_eq, hgsqP.2.2.2.2.1.2.2.1, hgsqP.2.2.2.2.2.2.2.2.1.1, hgsqP.2.2.2.2.2.1.1]; dsimp only [k5Ops]; simp only [Int.cast_neg, Int.cast_ofNat, map_intCast, map_neg, map_mul, map_add, map_sub, map_ofNat, mul_zero, zero_mul, add_zero, zero_add]
    have hdX4 : dLX_fn 4 U_C = 0 := rfl
    simp only [EB_of, W2_of, br_fn, hdX4, dLY_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    dsimp only [S, Q, T, x, y] at hLY_eq ⊢
    linear_combination -378 * (ιC_K5 S_K * ιC_K5 T_K * DX2_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 x_K) * DY2_of (ιC_K5 T_K) (ιC_K5 y_K)) *
      dF5_fn 4 (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) *
      (2 * ιC_K5 S_K * ιC_K5 T_K * dLX_fn 3 U_C) * hLY_eq
  have hq1_AC : (M_mid_int : A_C) * q1_dot =
      ιC_K5 k5Params.Cv0 * U_C * polyC (evalUBivLK5 (ubAdd k5Ops (ubSc k5Ops (k5Ops.mul (k5Ops.ofInt (-9)) H0_7) div0.2)
        (ubSc k5Ops (k5Ops.ofInt 63) (ubMulU k5Ops cacheK.gsq.qC_63 EB0_5103)))) +
      (1 / 243 : A_C) * polyC (evalUBivLK5 (ubAdd k5Ops (ubSc k5Ops (k5Ops.mul (k5Ops.ofInt 9) H0_7) (ubMulU k5Ops cacheK.gsq.A1_1_27 qY_0_321489))
        (ubShift (ubAdd k5Ops (ubSc k5Ops (k5Ops.mul (k5Ops.ofInt 9) H0_7) (ubSub k5Ops (ubSc k5Ops Av0_243 div0.2) (ubSc k5Ops Cv0_243 div1.2)))
          (ubSc k5Ops (k5Ops.ofInt 63) (ubMulU k5Ops cacheK.gsq.qC_63 (ubSub k5Ops (ubSc k5Ops Cv0_243 EB1_5103) (ubSc k5Ops Av0_243 EB0_5103)))))))) * V_C +
      ιC_K5 k5Params.Av0 * U_C * polyC (evalUBivLK5 (ubSub k5Ops (ubAdd k5Ops (ubSc k5Ops (k5Ops.mul (k5Ops.ofInt (-1701)) H0_7)
        (ubMulU k5Ops cacheK.gsq.A1_1_27 DY2_qE_63)) (ubSc k5Ops (k5Ops.mul (k5Ops.ofInt 9) H0_7) div1.2))
        (ubSc k5Ops (k5Ops.ofInt 63) (ubMulU k5Ops cacheK.gsq.qC_63 EB1_5103)))) * V_C ^ 2 := by
    have hcA1_AC : cA1_dot / v_of V_C =
        (9 / 63 : A_C) * polyC (evalUPolyK5 cacheK.gsq.qC_63) * U_C * (ιC_K5 k5Params.Cv0 - ιC_K5 k5Params.Av0 * V_C) := by
      have hV1 := cA1_dot_V1_ring S Q T U_C
      rw [← polyC_ca_cb_eq_q10_q20.1, ← polyC_ca_cb_eq_q10_q20.2] at hV1
      have hqC_eq : polyC (evalUPolyK5 cacheK.gsq.qC_63) =
          (-5250 * S ^ 4 + 30450 * S ^ 3 * Q - 64050 * S ^ 2 * Q ^ 2 + 63000 * S * Q ^ 3 - 28350 * Q ^ 4 +
            6250 * S ^ 2 * Q - 15000 * S * Q ^ 2 + 6750 * Q ^ 3 + 6250 * S ^ 2 - 15000 * S * Q + 6750 * Q ^ 2) +
          (336 * S ^ 4 - 2856 * S ^ 3 * Q + 8484 * S ^ 2 * Q ^ 2 - 10080 * S * Q ^ 3 + 3780 * Q ^ 4 -
            40 * S ^ 2 * Q + 240 * S * Q ^ 2 - 360 * Q ^ 3 - 40 * S ^ 2 + 240 * S * Q - 360 * Q ^ 2) * U_C := by
        rw [hgsqP.2.2.2.2.2.2.2.2.2.2.2.1]; simp only [S, Q, map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat]
      have hcA1_V : cA1_dot = V_C * ((H0_of S Q T * dA1_fn 0 S Q U_C 1 - A1_of S Q U_C 1 * dH0_fn 0 S Q T) * cb -
          (H0_of S Q T * dA1_fn 1 S Q U_C 1 - A1_of S Q U_C 1 * dH0_fn 1 S Q T) * ca) := by
        simp only [cA1_dot, A1_of, dA1_fn]; ring
      have hsp := E0_V_split S Q T U_C V_C
      have hHcub0 : H_cub S Q T 1 U_C V_C = 0 := by simpa [E_fn, S, Q, T] using E0_AC_zero 0 0
      rw [hHcub0, ← hAv_A, ← hCv_A] at hsp
      rw [div_eq_iff v_of_V_C_ne_zero, hcA1_V, hV1, ← hqC_eq, v_of]
      linear_combination -(polyC (evalUPolyK5 cacheK.gsq.qC_63) / 63) * hsp
    have hB1_AC : B1_of T U_C V_C = 9 * U_C * (ιC_K5 k5Params.Av0 * V_C - ιC_K5 k5Params.Cv0) := by
      rw [B1_of_eq_Av0_Cv0, ← hAv_A, ← hCv_A]
    have hA1_V : A1_of S Q U_C V_C = V_C * A1_of S Q U_C 1 := by simp only [A1_of]; ring
    have hH0_AC : ιC_K5 H0_7 = 7 * H0_of S Q T := by
      rw [hH0]; simp only [H0_of, S, Q, T, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]
    have hAv0_AC : ιC_K5 Av0_243 = 243 * ιC_K5 k5Params.Av0 := by rw [hAv0]; simp [map_ofNat]
    have hCv0_AC : ιC_K5 Cv0_243 = 243 * ιC_K5 k5Params.Cv0 := by rw [hCv0]; simp [map_ofNat]
    simp only [evalUBivLK5_ubAdd, evalUBivLK5_ubSub, evalUBivLK5_ubSc, evalUBivLK5_ubShift, evalUBivLK5_ubMulU, polyC_add, polyC_sub, polyC_mul, polyC_C, polyC_X, map_mul, map_intCast, Int.cast_neg, Int.cast_ofNat,
      hgsqP.2.2.2.2.2.2.2.2.2.2.1]; dsimp only [k5Ops]; simp only [Int.cast_neg, Int.cast_ofNat, map_intCast, map_neg, map_mul, map_add, map_sub, map_ofNat, mul_zero, zero_mul, add_zero, zero_add, hH0_AC, hAv0_AC, hCv0_AC]
    dsimp only [q1_dot]
    rw [hA1_V, hB1_AC, hcA1_AC, show M_mid_int = 2250423 from rfl]
    push_cast
    linear_combination (7 * H0_of S Q T * A1_of S Q U_C 1 * V_C) * (-hqY_AC) +
      (7 * H0_of S Q T * (9 * U_C * (ιC_K5 k5Params.Av0 * V_C - ιC_K5 k5Params.Cv0))) * (-hqX_AC) +
      (63 * polyC (evalUPolyK5 cacheK.gsq.qC_63) * U_C * (ιC_K5 k5Params.Cv0 - ιC_K5 k5Params.Av0 * V_C)) * (-hEB_AC)
  -- `U = 0` vanishing for `R13_int_p_eval_zero`!
  have hqX0_e0 : (evalUBivLK5 div0.2).eval 0 = 0 := by
    have h0 := congrArg (fun p : K5[X] => p.eval 0)
      (evalUBivLK5_ubSynDiv1Rem (ubSub k5Ops (ubMulU k5Ops cacheK.ac.cb_p QX0_0) (ubMulU k5Ops cacheK.ac.ca_p QX0_1)))
    rw [← hdiv0, hrem0, map_zero, zero_add] at h0
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one, zero_sub, neg_mul, one_mul] at h0
    have hd0 : (evalUBivLK5 (ubSub k5Ops (ubMulU k5Ops cacheK.ac.cb_p QX0_0) (ubMulU k5Ops cacheK.ac.ca_p QX0_1))).eval 0 = 0 := by
      rw [hQX0_0, hQX0_1, hdYF0_0, hdYF0_1]
      simp only [evalUBivLK5_ubSub, evalUBivLK5_ubSc, evalUBivLK5_ubBmul, evalUBivLK5_ubMulU,
        Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hbr0_3_e0, mul_zero, sub_zero]
      linear_combination evalBivLK5 cacheK.gsq.DX2 * ST * evalBivLK5 cacheK.gsq.dF5_3 * evalBivLK5 dDY2_dy * hbr0_cancel
    rw [hd0] at h0; exact neg_eq_zero.mp h0.symm
  have hqY0_e0 : (evalUBivLK5 qY_0_321489).eval 0 = 0 := by
    rw [hqY0, hQYd0, hQY0_0, hQY0_1, hdXF0_0, hdXF0_1]
    simp only [evalUBivLK5_ubAdd, evalUBivLK5_ubSub, evalUBivLK5_ubNeg, evalUBivLK5_ubSc,
      evalUBivLK5_ubBmul, evalUBivLK5_ubMulU, evalUBivLK5_ubShift,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, hbr0_3_e0, mul_zero, zero_mul, zero_sub, add_zero]
    linear_combination -evalBivLK5 DY2 * ST * evalBivLK5 dF5_4 * evalBivLK5 cacheK.gsq.dDX2_dx * hbr0_cancel
  have hEB0_e0 : (evalUBivLK5 EB0_5103).eval 0 = 0 := by
    rw [hEB0]; simp [evalUBivLK5_ubSc, evalUBivLK5_ubBmul, hbr0_3_e0]
  refine ⟨hH0, hH0_2, hAv0, hCv0, hCv0i, hBv1701, hqX_AC, hqY_AC, hq1_AC, ⟨hqX0_e0, hqY0_e0, ?_, ?_⟩⟩
  · simp [evalUBivLK5_ubAdd, evalUBivLK5_ubSc, evalUBivLK5_ubMulU, hqX0_e0, hEB0_e0]
  · simp [evalUBivLK5_ubAdd, evalUBivLK5_ubSc, evalUBivLK5_ubShift, evalUBivLK5_ubMulU, hqY0_e0]

private lemma evalGeomT_AC_bridge :
    let S := ιC_K5 S_K; let Q := ιC_K5 Q_K; let T := ιC_K5 T_K
    let x := ιC_K5 x_K; let y := ιC_K5 y_K
    let ca := polyC k5Params.ca_h; let cb := polyC k5Params.cb_h
    let QX_dot := QX_num S Q T x y U_C V_C 0 * cb - QX_num S Q T x y U_C V_C 1 * ca
    let QY_dot := QY_num S Q T x y U_C V_C 0 * cb - QY_num S Q T x y U_C V_C 1 * ca
    let cA1_dot := (H0_of S Q T * dA1_fn 0 S Q U_C V_C - A1_of S Q U_C V_C * dH0_fn 0 S Q T) * cb -
      (H0_of S Q T * dA1_fn 1 S Q U_C V_C - A1_of S Q U_C V_C * dH0_fn 1 S Q T) * ca
    let q1_dot := H0_of S Q T * A1_of S Q U_C V_C * (QY_dot / v_of V_C) +
      H0_of S Q T * B1_of T U_C V_C * (QX_dot / u_of U_C) +
      (cA1_dot / v_of V_C) * EB_of S Q T x y U_C V_C
    (gtK.H0_7 = 7 * H0_of S_K Q_K T_K) ∧
    (gtK.Av0_243 = 243 * k5Params.Av0) ∧
    (gtK.Cv0_243 = 243 * k5Params.Cv0) ∧
    (gtK.Cv0_243 = -25 * gtK.Cv0_int) ∧
    (polyC Bv_1701_p = 1701 * (ιC_K5 k5Params.Av0 * polyC k5Params.bW)) ∧
    (polyC (evalUBivLK5 gtK.qX_0_sc) + V_C * polyC (evalUBivLK5 gtK.qX_1_sc) = 321489 * (QX_dot / u_of U_C)) ∧
    (polyC (evalUBivLK5 gtK.qY_0_321489) - 9 * (321489 / 63 : A_C) * polyC (evalUBivLK5 gtK.DY2_qE_63) * U_C * ιC_K5 k5Params.Av0 * V_C =
      321489 * (QY_dot / v_of V_C)) ∧
    ((M_mid_int : A_C) * q1_dot =
      ιC_K5 k5Params.Cv0 * U_C * polyC (evalUBivLK5 gtK.q1_0_div_sc) +
      (1 / 243 : A_C) * polyC (evalUBivLK5 gtK.q1_1_sc) * V_C +
      ιC_K5 k5Params.Av0 * U_C * polyC (evalUBivLK5 gtK.q1_2_div_sc) * V_C ^ 2) :=
  let h := evalGeomT_K5_props
  ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1⟩

-- Define `R13_int_p : K5[X]` and `R12_int_p := R13_int_p.divX`!
private def R13_int_p : K5[X] :=
  Polynomial.C (7 * gtK.Cv0_243) * (Polynomial.X * A0U_U_p * (evalUBivLK5 gtK.q1_0_div_sc - evalUBivLK5 gtK.q1_2_div_sc)) +
  Polynomial.C (45927 * gtK.Cv0_243 * gtK.H0_7_2) * (Polynomial.X * AY3_p * evalUBivLK5 gtK.DY2_qE_63) +
  Polynomial.C 7 * (A0V_p * evalUBivLK5 gtK.q1_1_sc) +
  Polynomial.C (243 * gtK.H0_7_2) * (AY2_p * evalUBivLK5 gtK.qY_0_321489 + AX2_p * evalUBivLK5 gtK.qX_0_sc) -
  A0V_p * Bv_1701_p * evalUBivLK5 gtK.q1_0_div_sc

private def R12_int_p : K5[X] := R13_int_p.divX

private lemma R13_int_p_eval_zero : R13_int_p.eval 0 = 0 := by
  have hac0 := evalACache_K5_props.2.2.2.2.2
  have hAY2_0 : AY2_p.eval 0 = 0 := by
    simp [AY2_p, hac0.1.1, hac0.1.2]
  have hAX2_0 : AX2_p.eval 0 = 0 := by
    simp [AX2_p, hac0.2.1.1, hac0.2.1.2.1, hac0.2.1.2.2]
  have hq0 := evalGeomT_K5_props.2.2.2.2.2.2.2.2.2
  simp only [R13_int_p, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, hAY2_0, hAX2_0, hq0.1, hq0.2.1, hq0.2.2.1, hq0.2.2.2]
  ring

private lemma R13_int_p_eq_X_mul_R12 : R13_int_p = Polynomial.X * R12_int_p := by
  have h := Polynomial.X_mul_divX_add R13_int_p
  have hc0 : R13_int_p.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]; exact R13_int_p_eval_zero
  rw [hc0, map_zero, add_zero] at h
  exact h.symm

-- Step 1 of `trace_AC_eta_AC_main_eq`: extract `p4_AC = (interp4 P18_z_AC).1` via `numM_isPoly3`, `numM_lead3_scale`, `interp4_eq`!
private lemma p4_AC_eq :
    let S := ιC_K5 S_K; let Q := ιC_K5 Q_K; let T := ιC_K5 T_K
    let x := ιC_K5 x_K; let y := ιC_K5 y_K
    let ca := polyC k5Params.ca_h; let cb := polyC k5Params.cb_h
    let m := fun mi : Fin 10 => numM_lead3 mi S Q T cb (-ca) U_C 1
    let QX_dot := QX_num S Q T x y U_C V_C 0 * cb - QX_num S Q T x y U_C V_C 1 * ca
    let QY_dot := QY_num S Q T x y U_C V_C 0 * cb - QY_num S Q T x y U_C V_C 1 * ca
    let cA1_dot := (H0_of S Q T * dA1_fn 0 S Q U_C V_C - A1_of S Q U_C V_C * dH0_fn 0 S Q T) * cb -
      (H0_of S Q T * dA1_fn 1 S Q U_C V_C - A1_of S Q U_C V_C * dH0_fn 1 S Q T) * ca
    let q1_dot := H0_of S Q T * A1_of S Q U_C V_C * (QY_dot / v_of V_C) +
      H0_of S Q T * B1_of T U_C V_C * (QX_dot / u_of U_C) +
      (cA1_dot / v_of V_C) * EB_of S Q T x y U_C V_C
    let A0U_l : A_C := -(19708 / 1257375 : A_C) * (5 * m 0 - 9 * m 1) + (1472 / 1257375 : A_C) * (5 * m 1 - 9 * m 2) -
        (16 / 729 : A_C) * (5 * m 3 - 9 * m 5) + (188 / 2025 : A_C) * (5 * m 4 - 9 * m 6)
    let A0V_l : A_C := -(892 / 3645 : A_C) * (5 * m 3 - 9 * m 4) + (40 / 81 : A_C) * (5 * m 5 - 9 * m 6) -
        (112 / 2395 : A_C) * (5 * m 7 - 9 * m 8) + (392 / 11975 : A_C) * (5 * m 8 - 9 * m 9)
    let AY_l : A_C := -(100 / 243 : A_C) * (25 * m 3 - 45 * m 4 - 45 * m 5 + 81 * m 6) +
        V_C * (-(907876 / 33949125 : A_C) * (5 * m 0 - 9 * m 1) + (2258324 / 33949125 : A_C) * (5 * m 1 - 9 * m 2) +
          (8 / 243 : A_C) * (5 * m 3 - 9 * m 5) - (64 / 675 : A_C) * (5 * m 4 - 9 * m 6)) +
        U_C * V_C * (-(123236 / 24249375 : A_C) * (m 0 + (2790 / 77 : A_C) * m 6 + 28 * m 8 - (5904 / 77 : A_C) * m 9) +
          (492944 / 33949125 : A_C) * (m 1 + (927 / 77 : A_C) * m 6 + (49 / 5 : A_C) * m 8 - (21159 / 770 : A_C) * m 9))
    let AX_l : A_C := U_C * (-(8 / 405 : A_C) * (5 * m 3 - 9 * m 4) - (476 / 7185 : A_C) * (5 * m 7 - 9 * m 8) +
        (6916 / 35925 : A_C) * (5 * m 8 - 9 * m 9))
    p4_AC = (V_C ^ 2 / (W_C * cb) ^ 4) *
      ((A0U_l / U_C + A0V_l / V_C) * q1_dot + (AY_l * (QY_dot / v_of V_C) + AX_l * (QX_dot / u_of U_C)) * H0_of S Q T ^ 2) := by
  intro S Q T x y ca cb m QX_dot QY_dot cA1_dot q1_dot A0U_l A0V_l AY_l AX_l
  have hW_ne := W_C_ne_zero; have hU_ne := U_C_ne_zero; have hV_ne := V_C_ne_zero
  have hu_ne := u_of_U_C_ne_zero; have hv_ne := v_of_V_C_ne_zero
  have hcb_ne : cb ≠ 0 := polyC_ne_zero cb_h_K5_ne_zero
  set a1 : A_C := 1 / W_C
  set b1 : A_C := -ca / (W_C * cb)
  set b0 : A_C := -pairC k5Params.c0W / (W_C * cb)
  have hab_z (z : A_C) :
      z / W_C = a1 * z ∧ -(ca * z + pairC k5Params.c0W) / (W_C * cb) = b1 * z + b0 := by
    dsimp only [a1, b1, b0]; constructor
    · field_simp [hW_ne]
    · field_simp [hW_ne, hcb_ne]; ring
  have hnum_poly (mi : Fin 10) : ∃ c2 c1 c0 : A_C, ∀ z : A_C,
      numM mi (a1 * z) (b1 * z + b0) (S - (a1 * z) * T) (Q - (b1 * z + b0) * T) U_C V_C =
        (V_C ^ 2 / (W_C * cb) ^ 3 * m mi) * z ^ 3 + c2 * z ^ 2 + c1 * z + c0 := by
    obtain ⟨c2, c1, c0, h⟩ := numM_isPoly3 mi S Q T a1 b1 b0 U_C V_C
    have hsc : numM_lead3 mi S Q T a1 b1 U_C V_C = V_C ^ 2 / (W_C * cb) ^ 3 * m mi := by
      have h1 : a1 = (1 / (W_C * cb)) * cb := by dsimp only [a1]; field_simp [hW_ne, hcb_ne]
      have h2 : b1 = (1 / (W_C * cb)) * (-ca) := by dsimp only [b1]; field_simp [hW_ne, hcb_ne]
      rw [h1, h2, numM_lead3_scale]; dsimp only [m]; field_simp [hW_ne, hcb_ne]
    exact ⟨c2, c1, c0, fun z => by rw [h z, hsc]⟩
  choose c2 c1 c0 hnm using hnum_poly
  let fA0U (v : Fin 10 → A_C) : A_C :=
    -(19708 / 1257375 : A_C) * (5 * v 0 - 9 * v 1) + (1472 / 1257375 : A_C) * (5 * v 1 - 9 * v 2) -
    (16 / 729 : A_C) * (5 * v 3 - 9 * v 5) + (188 / 2025 : A_C) * (5 * v 4 - 9 * v 6)
  let fA0V (v : Fin 10 → A_C) : A_C :=
    -(892 / 3645 : A_C) * (5 * v 3 - 9 * v 4) + (40 / 81 : A_C) * (5 * v 5 - 9 * v 6) -
    (112 / 2395 : A_C) * (5 * v 7 - 9 * v 8) + (392 / 11975 : A_C) * (5 * v 8 - 9 * v 9)
  let fAY (v : Fin 10 → A_C) : A_C :=
    -(100 / 243 : A_C) * (25 * v 3 - 45 * v 4 - 45 * v 5 + 81 * v 6) +
    V_C * (-(907876 / 33949125 : A_C) * (5 * v 0 - 9 * v 1) + (2258324 / 33949125 : A_C) * (5 * v 1 - 9 * v 2) +
      (8 / 243 : A_C) * (5 * v 3 - 9 * v 5) - (64 / 675 : A_C) * (5 * v 4 - 9 * v 6)) +
    U_C * V_C * (-(123236 / 24249375 : A_C) * (v 0 + (2790 / 77 : A_C) * v 6 + 28 * v 8 - (5904 / 77 : A_C) * v 9) +
      (492944 / 33949125 : A_C) * (v 1 + (927 / 77 : A_C) * v 6 + (49 / 5 : A_C) * v 8 - (21159 / 770 : A_C) * v 9))
  let fAX (v : Fin 10 → A_C) : A_C :=
    U_C * (-(8 / 405 : A_C) * (5 * v 3 - 9 * v 4) - (476 / 7185 : A_C) * (5 * v 7 - 9 * v 8) +
      (6916 / 35925 : A_C) * (5 * v 8 - 9 * v 9))
  have hM0 : ∃ d2 d1 d0 : A_C, ∀ z : A_C,
      A_0U (a1 * z) (b1 * z + b0) (S - a1 * z * T) (Q - (b1 * z + b0) * T) U_C V_C / U_C +
      A_0V (a1 * z) (b1 * z + b0) (S - a1 * z * T) (Q - (b1 * z + b0) * T) U_C V_C / V_C =
      (V_C ^ 2 / (W_C * cb) ^ 3 * (A0U_l / U_C + A0V_l / V_C)) * z ^ 3 + d2 * z ^ 2 + d1 * z + d0 := by
    refine ⟨fA0U c2 / U_C + fA0V c2 / V_C, fA0U c1 / U_C + fA0V c1 / V_C, fA0U c0 / U_C + fA0V c0 / V_C, fun z => ?_⟩
    simp only [A_0U, A_0V, hnm, A0U_l, A0V_l, fA0U, fA0V]; ring
  have hMY : ∃ d2 d1 d0 : A_C, ∀ z : A_C,
      A_Y (a1 * z) (b1 * z + b0) (S - a1 * z * T) (Q - (b1 * z + b0) * T) U_C V_C =
      (V_C ^ 2 / (W_C * cb) ^ 3 * AY_l) * z ^ 3 + d2 * z ^ 2 + d1 * z + d0 := by
    refine ⟨fAY c2, fAY c1, fAY c0, fun z => ?_⟩
    simp only [A_Y, hnm, AY_l, fAY]; ring
  have hMX : ∃ d2 d1 d0 : A_C, ∀ z : A_C,
      A_X (a1 * z) (b1 * z + b0) (S - a1 * z * T) (Q - (b1 * z + b0) * T) U_C V_C =
      (V_C ^ 2 / (W_C * cb) ^ 3 * AX_l) * z ^ 3 + d2 * z ^ 2 + d1 * z + d0 := by
    refine ⟨fAX c2, fAX c1, fAX c0, fun z => ?_⟩
    simp only [A_X, hnm, AX_l, fAX]; ring
  obtain ⟨m2, m1, m0, hM0⟩ := hM0
  obtain ⟨y2, y1, y0, hMY⟩ := hMY
  obtain ⟨x2, x1, x0, hMX⟩ := hMX
  have hqY_z (z : A_C) : dot_ab (QY_num S Q T x y U_C V_C) (a1 * z) (b1 * z + b0) / v_of V_C =
      (QY_dot / (W_C * cb * v_of V_C)) * z + (QY_num S Q T x y U_C V_C 1 * b0 + QY_num S Q T x y U_C V_C 2) / v_of V_C := by
    simp only [dot_ab, QY_dot, a1, b1]; field_simp [hW_ne, hcb_ne, hv_ne]; ring
  have hqX_z (z : A_C) : dot_ab (QX_num S Q T x y U_C V_C) (a1 * z) (b1 * z + b0) / u_of U_C =
      (QX_dot / (W_C * cb * u_of U_C)) * z + (QX_num S Q T x y U_C V_C 1 * b0 + QX_num S Q T x y U_C V_C 2) / u_of U_C := by
    simp only [dot_ab, QX_dot, a1, b1]; field_simp [hW_ne, hcb_ne, hu_ne]; ring
  have hcA1_z (z : A_C) : cA1_of S Q T (a1 * z) (b1 * z + b0) U_C V_C / v_of V_C =
      (cA1_dot / (W_C * cb * v_of V_C)) * z +
      ((H0_of S Q T * dA1_fn 1 S Q U_C V_C - A1_of S Q U_C V_C * dH0_fn 1 S Q T) * b0 +
        (H0_of S Q T * dA1_fn 2 S Q U_C V_C - A1_of S Q U_C V_C * dH0_fn 2 S Q T)) / v_of V_C := by
    simp only [cA1_of, cA1_dot, a1, b1]; field_simp [hW_ne, hcb_ne, hv_ne]; ring
  set qY_0z := (QY_num S Q T x y U_C V_C 1 * b0 + QY_num S Q T x y U_C V_C 2) / v_of V_C
  set qX_0z := (QX_num S Q T x y U_C V_C 1 * b0 + QX_num S Q T x y U_C V_C 2) / u_of U_C
  set q1_0z := H0_of S Q T * A1_of S Q U_C V_C * qY_0z + H0_of S Q T * B1_of T U_C V_C * qX_0z +
    ((H0_of S Q T * dA1_fn 1 S Q U_C V_C - A1_of S Q U_C V_C * dH0_fn 1 S Q T) * b0 +
      (H0_of S Q T * dA1_fn 2 S Q U_C V_C - A1_of S Q U_C V_C * dH0_fn 2 S Q T)) / v_of V_C * EB_of S Q T x y U_C V_C
  have hP18_poly : ∀ z : A_C, P18_z_AC z =
      ((V_C ^ 2 / (W_C * cb) ^ 4) * ((A0U_l / U_C + A0V_l / V_C) * q1_dot +
        (AY_l * (QY_dot / v_of V_C) + AX_l * (QX_dot / u_of U_C)) * H0_of S Q T ^ 2)) * z ^ 4 +
      ((V_C ^ 2 / (W_C * cb) ^ 3 * (A0U_l / U_C + A0V_l / V_C)) * q1_0z + m2 * (q1_dot / (W_C * cb)) +
        ((V_C ^ 2 / (W_C * cb) ^ 3 * AY_l) * qY_0z + y2 * (QY_dot / (W_C * cb * v_of V_C)) +
         (V_C ^ 2 / (W_C * cb) ^ 3 * AX_l) * qX_0z + x2 * (QX_dot / (W_C * cb * u_of U_C))) * H0_of S Q T ^ 2) * z ^ 3 +
      (m2 * q1_0z + m1 * (q1_dot / (W_C * cb)) +
        (y2 * qY_0z + y1 * (QY_dot / (W_C * cb * v_of V_C)) + x2 * qX_0z + x1 * (QX_dot / (W_C * cb * u_of U_C))) * H0_of S Q T ^ 2) * z ^ 2 +
      (m1 * q1_0z + m0 * (q1_dot / (W_C * cb)) +
        (y1 * qY_0z + y0 * (QY_dot / (W_C * cb * v_of V_C)) + x1 * qX_0z + x0 * (QX_dot / (W_C * cb * u_of U_C))) * H0_of S Q T ^ 2) * z +
      (m0 * q1_0z + (y0 * qY_0z + x0 * qX_0z) * H0_of S Q T ^ 2) := fun z => by
    dsimp only [P18_z_AC, P18_of]
    rw [(hab_z z).1, (hab_z z).2, hM0 z, hMY z, hMX z, hqY_z z, hqX_z z, hcA1_z z]
    dsimp only [q1_dot, q1_0z]
    field_simp [hW_ne, hcb_ne, hU_ne, hV_ne, hu_ne, hv_ne]; ring
  have hint := interp4_eq hP18_poly
  simp only [p4_AC, hint]

-- Exact `trace_AC` formula for `eta_AC_main` via `p4_AC_eq`, 1-line `E0` reduction, and `trace_AC_euler`!
private lemma trace_AC_eta_AC_main_eq :
    Algebra.trace (RatFunc K5) A_C eta_AC_main =
      toRat R12_int_p / (RatFunc.C (81 * k5Params.Cv0 * (M_R_int : K5)) * toRat (k5Params.Q7_z * k5Params.Q5_z)) := by
  set S := ιC_K5 S_K; set Q := ιC_K5 Q_K; set T := ιC_K5 T_K
  set x := ιC_K5 x_K; set y := ιC_K5 y_K
  set ca := polyC k5Params.ca_h; set cb := polyC k5Params.cb_h
  have hU_ne := U_C_ne_zero; have hV_ne := V_C_ne_zero
  have hcb_ne : cb ≠ 0 := polyC_ne_zero cb_h_K5_ne_zero
  have hCv0_ne : ιC_K5 k5Params.Cv0 ≠ 0 := (map_ne_zero_iff _ ιC_K5.injective).mpr k5Params_Cv0_ne
  have hMR_ne : (M_R_int : A_C) ≠ 0 := by
    have hZ : M_R_int ≠ 0 := by unfold M_R_int M_A_int L_all_A M_mid_int; decide
    exact Int.cast_ne_zero.mpr hZ
  set m := fun mi : Fin 10 => numM_lead3 mi S Q T cb (-ca) U_C 1
  set QX_dot := QX_num S Q T x y U_C V_C 0 * cb - QX_num S Q T x y U_C V_C 1 * ca
  set QY_dot := QY_num S Q T x y U_C V_C 0 * cb - QY_num S Q T x y U_C V_C 1 * ca
  set cA1_dot := (H0_of S Q T * dA1_fn 0 S Q U_C V_C - A1_of S Q U_C V_C * dH0_fn 0 S Q T) * cb -
    (H0_of S Q T * dA1_fn 1 S Q U_C V_C - A1_of S Q U_C V_C * dH0_fn 1 S Q T) * ca
  set q1_dot := H0_of S Q T * A1_of S Q U_C V_C * (QY_dot / v_of V_C) +
    H0_of S Q T * B1_of T U_C V_C * (QX_dot / u_of U_C) +
    (cA1_dot / v_of V_C) * EB_of S Q T x y U_C V_C
  set A0U_l : A_C := -(19708 / 1257375 : A_C) * (5 * m 0 - 9 * m 1) + (1472 / 1257375 : A_C) * (5 * m 1 - 9 * m 2) -
      (16 / 729 : A_C) * (5 * m 3 - 9 * m 5) + (188 / 2025 : A_C) * (5 * m 4 - 9 * m 6)
  set A0V_l : A_C := -(892 / 3645 : A_C) * (5 * m 3 - 9 * m 4) + (40 / 81 : A_C) * (5 * m 5 - 9 * m 6) -
      (112 / 2395 : A_C) * (5 * m 7 - 9 * m 8) + (392 / 11975 : A_C) * (5 * m 8 - 9 * m 9)
  set AY_l : A_C := -(100 / 243 : A_C) * (25 * m 3 - 45 * m 4 - 45 * m 5 + 81 * m 6) +
      V_C * (-(907876 / 33949125 : A_C) * (5 * m 0 - 9 * m 1) + (2258324 / 33949125 : A_C) * (5 * m 1 - 9 * m 2) +
        (8 / 243 : A_C) * (5 * m 3 - 9 * m 5) - (64 / 675 : A_C) * (5 * m 4 - 9 * m 6)) +
      U_C * V_C * (-(123236 / 24249375 : A_C) * (m 0 + (2790 / 77 : A_C) * m 6 + 28 * m 8 - (5904 / 77 : A_C) * m 9) +
        (492944 / 33949125 : A_C) * (m 1 + (927 / 77 : A_C) * m 6 + (49 / 5 : A_C) * m 8 - (21159 / 770 : A_C) * m 9))
  set AX_l : A_C := U_C * (-(8 / 405 : A_C) * (5 * m 3 - 9 * m 4) - (476 / 7185 : A_C) * (5 * m 7 - 9 * m 8) +
      (6916 / 35925 : A_C) * (5 * m 8 - 9 * m 9))
  have hp4_eq : p4_AC = (V_C ^ 2 / (W_C * cb) ^ 4) *
      ((A0U_l / U_C + A0V_l / V_C) * q1_dot + (AY_l * (QY_dot / v_of V_C) + AX_l * (QX_dot / u_of U_C)) * H0_of S Q T ^ 2) :=
    p4_AC_eq
  -- Step 2: 1-line `E0` trace reduction `-(p4_AC * U_C^3 * W_C * cb^4) = -Const + (Av0 / Cv0) * (R12 / M_R) * (bW + W_C)`!
  obtain ⟨hA0U, hA0V, hAY2, hAY3, hAX2⟩ := evalACache_AC_bridge
  obtain ⟨hH0, hAv0, hCv0, _, hBv1701, hqX, hqY, hq1⟩ := evalGeomT_AC_bridge
  have hM0_sub : (M_A_int : A_C) * (A0U_l / U_C) = polyC A0U_U_p := by
    rw [← mul_div_assoc, ← hA0U, mul_div_cancel_left₀ _ hU_ne]
  have hA0V_sub : (M_A_int : A_C) * A0V_l = polyC A0V_p := hA0V.symm
  have hAX_sub : (M_A_int : A_C) * AX_l = polyC AX2_p := hAX2.symm
  have hAY_sub : (M_A_int : A_C) * AY_l = polyC AY2_p + V_C * polyC AY3_p := by
    dsimp only [AY_l]
    linear_combination -hAY2 - V_C * hAY3
  have hE0_W : ιC_K5 k5Params.Av0 * U_C * V_C ^ 2 + (ιC_K5 k5Params.Av0 * polyC k5Params.bW) * V_C + ιC_K5 k5Params.Cv0 * U_C = 0 := by
    have hW : W_C ^ 2 + polyC k5Params.bW * W_C + polyC k5Params.cW = 0 := W_C_relation
    have hcW : polyC k5Params.cW = ιC_K5 k5Params.Cv0 * ιC_K5 k5Params.Av0_inv * U_C ^ 2 := by
      simp [CoverParams.cW, polyC_mul, polyC_pow, polyC_C, polyC_X]
    have hAv_inv : ιC_K5 k5Params.Av0 * ιC_K5 k5Params.Av0_inv = 1 := by
      rw [← map_mul, k5Params_Av0_mul_inv, map_one]
    rw [hcW] at hW
    have hV : W_C = U_C * V_C := by simp only [V_C, mul_div_cancel₀ _ hU_ne]
    rw [hV] at hW
    have hmul := congrArg (fun t => ιC_K5 k5Params.Av0 * t) hW
    simp only [mul_zero] at hmul
    have h1 : ιC_K5 k5Params.Av0 * ((U_C * V_C) ^ 2 + polyC k5Params.bW * (U_C * V_C) +
        ιC_K5 k5Params.Cv0 * ιC_K5 k5Params.Av0_inv * U_C ^ 2) =
        U_C * (ιC_K5 k5Params.Av0 * U_C * V_C ^ 2 + (ιC_K5 k5Params.Av0 * polyC k5Params.bW) * V_C + ιC_K5 k5Params.Cv0 * U_C) := by
      linear_combination (ιC_K5 k5Params.Cv0 * U_C ^ 2) * hAv_inv
    rw [h1] at hmul
    exact (mul_eq_zero.mp hmul).resolve_left hU_ne
  -- Compute `(M_R_int : A_C) * (V_C ^ 2 * (p4_AC * U_C ^ 3 * W_C * cb ^ 4)) = Const * V_C ^ 2 + polyC R13_int_p * V_C`!
  set q1_div_sc : A_C := -polyC A0V_p * polyC (evalUBivLK5 gtK.q1_0_div_sc)
  set pV4_div_sc : A_C := polyC A0U_U_p * polyC (evalUBivLK5 gtK.q1_2_div_sc) -
      (9 * 729 : A_C) * polyC AY3_p * polyC (evalUBivLK5 gtK.DY2_qE_63) * (ιC_K5 gtK.H0_7) ^ 2
  have hMR_def : (M_R_int : A_C) = (M_A_int : A_C) * 1701 * (M_mid_int : A_C) := by
    simp only [M_R_int, Int.cast_mul, Int.cast_ofNat]
  have hM_mid_def : (M_mid_int : A_C) = 7 * 321489 := by
    have hZ : M_mid_int = 7 * 321489 := by unfold M_mid_int; decide
    exact_mod_cast hZ
  have hH0_2_eq : ιC_K5 gtK.H0_7_2 = (7 * H0_of S Q T) ^ 2 := by
    have h2 : gtK.H0_7_2 = gtK.H0_7 ^ 2 := evalGeomT_K5_props.2.1
    rw [h2, map_pow, hH0]; simp only [H0_of, S, Q, T, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]
  have hH0_AC : ιC_K5 gtK.H0_7 = 7 * H0_of S Q T := by
    rw [hH0]; simp only [H0_of, S, Q, T, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]
  have hCv0_AC : ιC_K5 gtK.Cv0_243 = 243 * ιC_K5 k5Params.Cv0 := by rw [hCv0]; simp [map_ofNat]
  set Const_sc : A_C :=
    1701 * ((1 / 243 : A_C) * polyC A0U_U_p * polyC (evalUBivLK5 gtK.q1_1_sc) +
      polyC A0V_p * ιC_K5 k5Params.Av0 * U_C * polyC (evalUBivLK5 gtK.q1_2_div_sc)) +
    (243 : A_C) * ιC_K5 gtK.H0_7_2 * (polyC AY3_p * polyC (evalUBivLK5 gtK.qY_0_321489) -
      (9 * 5103 : A_C) * polyC AY2_p * polyC (evalUBivLK5 gtK.DY2_qE_63) * U_C * ιC_K5 k5Params.Av0 +
      polyC AX2_p * polyC (evalUBivLK5 gtK.qX_1_sc)) -
    ((polyC Bv_1701_p) * pV4_div_sc - 1701 * ιC_K5 k5Params.Av0 * U_C * q1_div_sc)
  have hN_red : (M_R_int : A_C) * (V_C ^ 2 * (p4_AC * U_C ^ 3 * W_C * cb ^ 4)) =
      Const_sc * V_C ^ 2 + polyC R13_int_p * V_C := by
    have hV_mul : V_C ^ 2 * (p4_AC * U_C ^ 3 * W_C * cb ^ 4) =
        V_C * ((A0U_l / U_C + A0V_l / V_C) * q1_dot +
          (AY_l * (QY_dot / v_of V_C) + AX_l * (QX_dot / u_of U_C)) * H0_of S Q T ^ 2) := by
      rw [hp4_eq]
      have hW_UV : W_C = U_C * V_C := by simp only [V_C, mul_div_cancel₀ _ hU_ne]
      rw [hW_UV]
      have halg : ∀ (u v c x : A_C), u ≠ 0 → v ≠ 0 → c ≠ 0 →
          v ^ 2 * (v ^ 2 / (u * v * c) ^ 4 * x * u ^ 3 * (u * v) * c ^ 4) = v * x := by
        intro u v c x hu hv hc; field_simp [hu, hv, hc]
      exact halg U_C V_C cb _ hU_ne hV_ne hcb_ne
    rw [hV_mul, hMR_def]
    have hLHS_expand : (M_A_int : A_C) * 1701 * (M_mid_int : A_C) *
        (V_C * ((A0U_l / U_C + A0V_l / V_C) * q1_dot +
          (AY_l * (QY_dot / v_of V_C) + AX_l * (QX_dot / u_of U_C)) * H0_of S Q T ^ 2)) =
        1701 * (polyC A0U_U_p * V_C + polyC A0V_p) * ((M_mid_int : A_C) * q1_dot) +
        (243 : A_C) * ιC_K5 gtK.H0_7_2 * V_C *
          ((polyC AY2_p + V_C * polyC AY3_p) * (321489 * (QY_dot / v_of V_C)) +
           polyC AX2_p * (321489 * (QX_dot / u_of U_C))) := by
      have halg : ∀ (ma mm v a0u a0v ay ax q1 qy qx h0 : A_C), v ≠ 0 →
          mm = 7 * 321489 →
          ma * 1701 * mm * (v * ((a0u + a0v / v) * q1 + (ay * qy + ax * qx) * h0 ^ 2)) =
          1701 * ((ma * a0u) * v + ma * a0v) * (mm * q1) +
          243 * (7 * h0) ^ 2 * v * ((ma * ay) * (321489 * qy) + (ma * ax) * (321489 * qx)) := by
        intro ma mm v a0u a0v ay ax q1 qy qx h0 hv hmm
        rw [hmm]; field_simp [hv]; ring
      rw [hH0_2_eq, ← hM0_sub, ← hA0V_sub, ← hAY_sub, ← hAX_sub]
      exact halg (M_A_int : A_C) (M_mid_int : A_C) V_C (A0U_l / U_C) A0V_l AY_l AX_l
        q1_dot (QY_dot / v_of V_C) (QX_dot / u_of U_C) (H0_of S Q T) hV_ne hM_mid_def
    rw [hLHS_expand, hq1, ← hqY, ← hqX]
    simp only [R13_int_p, Const_sc, q1_div_sc, pV4_div_sc, polyC_add, polyC_sub, polyC_mul, polyC_C, polyC_X, polyC_ofNat,
      map_mul, map_ofNat, hCv0_AC, hH0_2_eq, hH0_AC, hBv1701]
    have hE := hE0_W
    generalize polyC A0U_U_p = a0u
    generalize polyC A0V_p = a0v
    generalize polyC AY2_p = ay2
    generalize polyC AY3_p = ay3
    generalize polyC AX2_p = ax2
    generalize polyC (evalUBivLK5 gtK.q1_0_div_sc) = q10
    generalize polyC (evalUBivLK5 gtK.q1_1_sc) = q11
    generalize polyC (evalUBivLK5 gtK.q1_2_div_sc) = q12
    generalize polyC (evalUBivLK5 gtK.DY2_qE_63) = dyq
    generalize polyC (evalUBivLK5 gtK.qY_0_321489) = qy0
    generalize polyC (evalUBivLK5 gtK.qX_0_sc) = qx0
    generalize polyC (evalUBivLK5 gtK.qX_1_sc) = qx1
    generalize H0_of S Q T = h0
    generalize polyC k5Params.bW = bw at hE ⊢
    generalize ιC_K5 k5Params.Av0 = av at hE ⊢
    generalize ιC_K5 k5Params.Cv0 = cv at hE ⊢
    generalize U_C = u at hE ⊢
    generalize V_C = v at hE ⊢
    linear_combination (1701 * (a0u * q12 - (9 * 729 : A_C) * ay3 * dyq * (7 * h0) ^ 2) * v + 1701 * a0v * q10) * hE
  -- Divide by `V_C^2` and rewrite `-1 / V_C = (Av0 / Cv0 / U_C) * (bW + W_C)`!
  have hinvV : -(1 / V_C) = (ιC_K5 k5Params.Av0 / ιC_K5 k5Params.Cv0 / U_C) * (polyC k5Params.bW + W_C) := by
    have h1 : V_C * (ιC_K5 k5Params.Av0 * (polyC k5Params.bW + W_C)) = -(ιC_K5 k5Params.Cv0 * U_C) := by
      have hW_UV : W_C = U_C * V_C := by simp only [V_C, mul_div_cancel₀ _ hU_ne]
      rw [hW_UV]; linear_combination hE0_W
    field_simp [hV_ne, hCv0_ne, hU_ne]
    linear_combination -h1
  -- Express `-(p4_AC * U_C^3 * W_C * cb^4)` in `evalAC` form and apply `trace_AC_euler`!
  set q1_div_rat : RatFunc K5 := -toRat A0V_p * toRat (evalUBivLK5 gtK.q1_0_div_sc)
  set pV4_div_rat : RatFunc K5 := toRat A0U_U_p * toRat (evalUBivLK5 gtK.q1_2_div_sc) -
      (9 * 729 : RatFunc K5) * toRat AY3_p * toRat (evalUBivLK5 gtK.DY2_qE_63) * (RatFunc.C gtK.H0_7) ^ 2
  set Const_rat : RatFunc K5 :=
    1701 * ((1 / 243 : RatFunc K5) * toRat A0U_U_p * toRat (evalUBivLK5 gtK.q1_1_sc) +
      toRat A0V_p * RatFunc.C k5Params.Av0 * RatFunc.X * toRat (evalUBivLK5 gtK.q1_2_div_sc)) +
    (243 : RatFunc K5) * RatFunc.C gtK.H0_7_2 * (toRat AY3_p * toRat (evalUBivLK5 gtK.qY_0_321489) -
      (9 * 5103 : RatFunc K5) * toRat AY2_p * toRat (evalUBivLK5 gtK.DY2_qE_63) * RatFunc.X * RatFunc.C k5Params.Av0 +
      toRat AX2_p * toRat (evalUBivLK5 gtK.qX_1_sc)) -
    ((toRat Bv_1701_p) * pV4_div_rat - 1701 * RatFunc.C k5Params.Av0 * RatFunc.X * q1_div_rat)
  have hN_evalAC :
      -(p4_AC * U_C ^ 3 * W_C * cb ^ 4) =
        evalAC ⟨-toRat (Polynomial.C (M_R_int : K5)⁻¹) * Const_rat +
            RatFunc.C (k5Params.Av0 / (k5Params.Cv0 * (M_R_int : K5))) * toRat R12_int_p * toRat k5Params.bW,
          RatFunc.C (k5Params.Av0 / (k5Params.Cv0 * (M_R_int : K5))) * toRat R12_int_p⟩ := by
    have hιC_K5 : ∀ c : K5, ιC_K5 c = ιC_rat (RatFunc.C c) := fun _ => rfl
    have hConst_in_base : Const_sc = ιC_rat Const_rat := by
      simp only [Const_sc, Const_rat, pV4_div_sc, pV4_div_rat, q1_div_sc, q1_div_rat,
        polyC, hιC_K5, U_C, map_add, map_sub, map_neg, map_mul, map_div₀, map_pow, map_one, map_ofNat]
    have hR13_C : polyC R13_int_p = U_C * polyC R12_int_p := by
      rw [R13_int_p_eq_X_mul_R12, polyC_mul, polyC_X]
    have hN_eq : -(p4_AC * U_C ^ 3 * W_C * cb ^ 4) =
        -(M_R_int : A_C)⁻¹ * Const_sc +
        (ιC_K5 k5Params.Av0 / (ιC_K5 k5Params.Cv0 * (M_R_int : A_C))) * polyC R12_int_p * (polyC k5Params.bW + W_C) := by
      have hstep : ∀ (P4 C0 R12 MR Av Cv U V bW W : A_C),
          MR ≠ 0 → V ≠ 0 → U ≠ 0 → Cv ≠ 0 →
          MR * (V ^ 2 * P4) = C0 * V ^ 2 + U * R12 * V →
          -(1 / V) = (Av / Cv / U) * (bW + W) →
          -P4 = -MR⁻¹ * C0 + (Av / (Cv * MR)) * R12 * (bW + W) := by
        intro P4 C0 R12 MR Av Cv U V bW W hMR hV hU hCv hred hinv
        have hdiv := congrArg (fun t => -t / (MR * V ^ 2)) hred
        have hl : -(MR * (V ^ 2 * P4)) / (MR * V ^ 2) = -P4 := by field_simp [hMR, hV]
        rw [hl] at hdiv
        rw [hdiv]
        calc -(C0 * V ^ 2 + U * R12 * V) / (MR * V ^ 2) =
              -MR⁻¹ * C0 + (-(1 / V)) * (U * R12 / MR) := by field_simp [hMR, hV]; ring
          _ = -MR⁻¹ * C0 + (Av / (Cv * MR)) * R12 * (bW + W) := by rw [hinv]; field_simp [hU, hCv, hMR]
      exact hstep _ _ _ _ _ _ _ _ _ _ hMR_ne hV_ne hU_ne hCv0_ne (by rw [← hR13_C]; exact hN_red) hinvV
    rw [hN_eq, hConst_in_base]
    have hMR_C : (M_R_int : A_C) = ιC_rat (RatFunc.C (M_R_int : K5)) := by
      simp only [map_intCast]
    have hMR_inv : (M_R_int : A_C)⁻¹ = ιC_rat (toRat (Polynomial.C (M_R_int : K5)⁻¹)) := by
      rw [hMR_C, ← map_inv₀ ιC_rat, ← map_inv₀ RatFunc.C, toRat, RatFunc.algebraMap_C]
    have hAv_C : ιC_K5 k5Params.Av0 / (ιC_K5 k5Params.Cv0 * (M_R_int : A_C)) =
        ιC_rat (RatFunc.C (k5Params.Av0 / (k5Params.Cv0 * (M_R_int : K5)))) := by
      rw [hMR_C, hιC_K5, hιC_K5]; simp only [map_div₀, map_mul]
    rw [hMR_inv, hAv_C]
    simp only [evalAC, polyC, map_add, map_neg, map_mul]
    generalize ιC_rat (toRat (Polynomial.C (M_R_int : K5)⁻¹)) = a
    generalize ιC_rat Const_rat = c0
    generalize ιC_rat (RatFunc.C (k5Params.Av0 / (k5Params.Cv0 * (M_R_int : K5)))) = k
    generalize ιC_rat (toRat R12_int_p) = r12
    generalize ιC_rat (toRat k5Params.bW) = bw
    ring
  -- Plug `hN_evalAC` into `eta_AC_main` and apply `trace_AC_euler` with `y = PairAlg.ofScalar 1`!
  set den_rat : RatFunc K5 :=
    RatFunc.C (81 * k5Params.Av0) * toRat k5Params.Q7_z * toRat k5Params.Q5_z
  set num_pair : PairAlg (RatFunc K5) :=
    ⟨-toRat (Polynomial.C (M_R_int : K5)⁻¹) * Const_rat +
       RatFunc.C (k5Params.Av0 / (k5Params.Cv0 * (M_R_int : K5))) * toRat R12_int_p * toRat k5Params.bW,
     RatFunc.C (k5Params.Av0 / (k5Params.Cv0 * (M_R_int : K5))) * toRat R12_int_p⟩
  have heta_main : eta_AC_main =
      evalAC (PairAlg.smul den_rat⁻¹ num_pair) /
        (evalAC (PairAlg.ofScalar (1 : RatFunc K5)) * (2 * W_C + ιC_rat (toRat k5Params.bW))) := by
    rw [evalAC_smul, evalAC_ofScalar, map_one, one_mul, ← hN_evalAC]
    have hιC_K5 : ∀ c : K5, ιC_K5 c = ιC_rat (RatFunc.C c) := fun _ => rfl
    have h81Av0 : (81 : A_C) * ιC_K5 k5Params.Av0 = ιC_rat (RatFunc.C (81 * k5Params.Av0)) := by
      rw [hιC_K5]; simp only [map_mul, map_ofNat]
    have hden_eq : ιC_rat den_rat⁻¹ =
        (81 * ιC_K5 k5Params.Av0 * polyC k5Params.Q7_z * polyC k5Params.Q5_z)⁻¹ := by
      dsimp only [den_rat, polyC]
      rw [map_inv₀, map_mul, map_mul, ← h81Av0]
    rw [hden_eq]
    have hdiv_alg : ∀ (N a b c d : A_C), N / (a * b * c * d) = (a * c * d)⁻¹ * N / b := fun N a b c d => by
      simp only [div_eq_mul_inv, mul_inv]; ring
    dsimp only [eta_AC_main]
    change -(p4_AC * U_C ^ 3 * W_C * cb ^ 4) /
        (81 * ιC_K5 k5Params.Av0 * (2 * W_C + polyC k5Params.bW) * polyC k5Params.Q7_z * polyC k5Params.Q5_z) =
      (81 * ιC_K5 k5Params.Av0 * polyC k5Params.Q7_z * polyC k5Params.Q5_z)⁻¹ *
        -(p4_AC * U_C ^ 3 * W_C * cb ^ 4) / (2 * W_C + polyC k5Params.bW)
    exact hdiv_alg (-(p4_AC * U_C ^ 3 * W_C * cb ^ 4))
      (81 * ιC_K5 k5Params.Av0) (2 * W_C + polyC k5Params.bW) (polyC k5Params.Q7_z) (polyC k5Params.Q5_z)
  rw [heta_main, trace_AC_euler (PairAlg.smul den_rat⁻¹ num_pair) (PairAlg.ofScalar 1) (by simp [PairAlg.nm, PairAlg.ofScalar])]
  simp only [PairAlg.nm, PairAlg.ofScalar, PairAlg.smul, num_pair, den_rat,
    pow_two, mul_zero, zero_mul, add_zero, sub_zero, mul_one, div_one, map_mul, map_div₀, map_ofNat]
  have hAv_R : (RatFunc.C k5Params.Av0 : RatFunc K5) ≠ 0 := by
    simpa [map_eq_zero] using Av0_K5_ne_zero
  have hCv_R : (RatFunc.C k5Params.Cv0 : RatFunc K5) ≠ 0 := by
    simpa [map_eq_zero] using k5Params_Cv0_ne
  have hMR_R : (RatFunc.C (M_R_int : K5) : RatFunc K5) ≠ 0 := by
    have hZ : M_R_int ≠ 0 := by unfold M_R_int M_A_int L_all_A M_mid_int; decide
    have hK : (M_R_int : K5) ≠ 0 := Int.cast_ne_zero.mpr hZ
    simpa [map_eq_zero] using hK
  have hQ7_R : toRat k5Params.Q7_z ≠ 0 := by
    simpa [toRat, map_eq_zero] using Q7_K5_ne_zero
  have hQ5_R : toRat k5Params.Q5_z ≠ 0 := by
    simpa [toRat, map_eq_zero] using Q5_K5_ne_zero
  have hrat_alg : ∀ (a c m q7 q5 r12 : RatFunc K5), a ≠ 0 → c ≠ 0 → m ≠ 0 → q7 ≠ 0 → q5 ≠ 0 →
      (81 * a * q7 * q5)⁻¹ * (a / (c * m) * r12) = r12 / (81 * c * m * (q7 * q5)) := by
    intro a c m q7 q5 r12 ha hc hm hq7 hq5; field_simp [ha, hc, hm, hq7, hq5]
  exact hrat_alg _ _ _ _ _ _ hAv_R hCv_R hMR_R hQ7_R hQ5_R

-- Lengths of `ACache` and `GeomT` lists (for `evalBivLK5_combineBivDot_dotW`!)
private lemma uAdd_len {α : Type*} (o : PolyOps α) : ∀ a b, (uAdd o a b).length = max a.length b.length
  | [], b => by simp [uAdd]
  | a :: as, [] => by simp [uAdd]
  | _ :: as, _ :: bs => by simp [uAdd, uAdd_len o as bs, Nat.succ_max_succ]

private lemma uSub_len {α : Type*} (o : PolyOps α) : ∀ a b, (uSub o a b).length = max a.length b.length
  | [], b => by simp [uSub, uNeg]
  | a :: as, [] => by simp [uSub]
  | _ :: as, _ :: bs => by simp [uSub, uSub_len o as bs, Nat.succ_max_succ]

private lemma uMul_len_le {α : Type*} (o : PolyOps α) :
    ∀ a b, b ≠ [] → (uMul o a b).length ≤ a.length + b.length - 1
  | [], _, _ => by simp [uMul]
  | [x], b, hb => by
      simp only [uMul, uAdd_len, uSc, uShift, List.length_map, List.length_cons, List.length_nil]
      have : 1 ≤ b.length := List.length_pos_of_ne_nil hb
      omega
  | x :: y :: xs, b, hb => by
      have ih := uMul_len_le o (y :: xs) b hb
      simp only [uMul, uAdd_len, uSc, uShift, List.length_map, List.length_cons] at ih ⊢
      omega

private lemma ubAdd_len {α : Type*} (o : PolyOps α) : ∀ a b, (ubAdd o a b).length = max a.length b.length
  | [], b => by simp [ubAdd]
  | a :: as, [] => by simp [ubAdd]
  | _ :: as, _ :: bs => by simp [ubAdd, ubAdd_len o as bs, Nat.succ_max_succ]

private lemma ubSub_len {α : Type*} (o : PolyOps α) : ∀ a b, (ubSub o a b).length = max a.length b.length
  | [], b => by simp [ubSub, ubNeg]
  | a :: as, [] => by simp [ubSub]
  | _ :: as, _ :: bs => by simp [ubSub, ubSub_len o as bs, Nat.succ_max_succ]

private lemma ubMulU_len_le {α : Type*} (o : PolyOps α) :
    ∀ u b, b ≠ [] → (ubMulU o u b).length ≤ u.length + b.length - 1
  | [], _, _ => by simp [ubMulU]
  | [c], b, hb => by
      simp only [ubMulU, ubAdd_len, ubSc, ubShift, List.length_map, List.length_cons, List.length_nil]
      have : 1 ≤ b.length := List.length_pos_of_ne_nil hb
      omega
  | c :: c' :: cs, b, hb => by
      have ih := ubMulU_len_le o (c' :: cs) b hb
      simp only [ubMulU, ubAdd_len, ubSc, ubShift, List.length_map, List.length_cons] at ih ⊢
      omega

private lemma ubSynDiv1Rem_len {α : Type*} (o : PolyOps α) :
    ∀ a, (ubSynDiv1Rem o a).2.length = a.length - 1
  | [] => rfl
  | [_] => rfl
  | _ :: b' :: rest => by
      have ih := ubSynDiv1Rem_len o (b' :: rest)
      simp only [ubSynDiv1Rem, List.length_cons] at ih ⊢
      omega

private lemma evalBivLK5_combineBivDot_uAdd (B : UBivL K5) :
    ∀ (t1 t2 : UPoly K5),
      evalBivLK5 (combineBivDot k5Ops B (uAdd k5Ops t1 t2)) =
      evalBivLK5 (combineBivDot k5Ops B t1) + evalBivLK5 (combineBivDot k5Ops B t2) := by
  induction B with
  | nil => intro _ _; simp [combineBivDot, evalBivLK5]
  | cons b bs ih =>
      intro t1 t2
      cases t1 with
      | nil => simp [uAdd, combineBivDot, evalBivLK5]
      | cons x xs => cases t2 with
        | nil => simp [uAdd, combineBivDot, evalBivLK5]
        | cons y ys =>
            simp only [uAdd, combineBivDot, evalBivLK5_bivAdd, evalBivLK5_bivSc, ih xs ys]
            dsimp only [k5Ops]; ring

private lemma evalBivLK5_combineBivDot_uSc (c : K5) (B : UBivL K5) :
    ∀ t : UPoly K5, evalBivLK5 (combineBivDot k5Ops B (uSc k5Ops c t)) =
      c * evalBivLK5 (combineBivDot k5Ops B t) := by
  induction B with
  | nil => intro _; simp [combineBivDot, evalBivLK5]
  | cons b bs ih =>
      intro t; cases t with
      | nil => simp [uSc, combineBivDot, evalBivLK5]
      | cons x xs =>
          rw [show uSc k5Ops c (x :: xs) = k5Ops.mul c x :: uSc k5Ops c xs from rfl]
          simp only [combineBivDot, evalBivLK5_bivAdd, evalBivLK5_bivSc, ih xs]
          dsimp only [k5Ops]; ring

private lemma uSc_len {α : Type*} (o : PolyOps α) (c : α) (a : UPoly α) : (uSc o c a).length = a.length :=
  List.length_map _

private lemma dotW_len {α : Type*} (o : PolyOps α) (A W : UPoly α) (sh : ℕ) : (dotW o A W sh).length = 5 := rfl

private def uOps : PolyOps Unit :=
  ⟨(), fun _ => (), fun _ _ => (), fun _ _ => (), fun _ => (), fun _ _ => (), fun _ _ => ()⟩

private def acUnit : ACache Unit := evalACache uOps () ()
private def gsqUnit : GeomSQ Unit := evalGeomSQ uOps () ()
private def gtUnit : GeomT Unit := evalGeomT uOps () acUnit.ca_p acUnit.cb_p gsqUnit ()

private lemma acUnit_lens :
    (uTail acUnit.A0U_t0).length ≤ 9 ∧ (uTail acUnit.A0U_t1).length ≤ 9 ∧
    acUnit.A0V_t0.length ≤ 10 ∧ acUnit.A0V_t1.length ≤ 10 ∧ acUnit.A0V_t2.length ≤ 10 ∧
    (uMul uOps acUnit.A0V_t0 acUnit.Bv_SQ).length ≤ 12 ∧
    (uMul uOps acUnit.A0V_t1 acUnit.Bv_SQ).length ≤ 12 ∧
    (uMul uOps acUnit.A0V_t2 acUnit.Bv_SQ).length ≤ 12 ∧
    acUnit.AY2_t0.length ≤ 10 ∧ acUnit.AY2_t1.length ≤ 10 ∧
    acUnit.AY3_t0.length ≤ 11 ∧ acUnit.AY3_t1.length ≤ 11 ∧
    acUnit.AX2_t0.length ≤ 11 ∧ acUnit.AX2_t1.length ≤ 11 ∧ acUnit.AX2_t2.length ≤ 11 ∧
    acUnit.Bv_SQ.length ≤ 3 := by decide +kernel

private lemma gtUnit_lens :
    (ubSub uOps gtUnit.q1_0_div_sc gtUnit.q1_2_div_sc).length ≤ 3 ∧
    gtUnit.DY2_qE_63.length ≤ 2 ∧ gtUnit.q1_1_sc.length ≤ 5 ∧
    gtUnit.qY_0_321489.length ≤ 4 ∧ gtUnit.qX_0_sc.length ≤ 3 ∧ gtUnit.q1_0_div_sc.length ≤ 3 ∧
    gtUnit.q1_2_div_sc.length ≤ 3 := by decide +kernel

private lemma cacheK_ac_lens :
    (uTail cacheK.ac.A0U_t0).length ≤ 9 ∧ (uTail cacheK.ac.A0U_t1).length ≤ 9 ∧
    cacheK.ac.A0V_t0.length ≤ 10 ∧ cacheK.ac.A0V_t1.length ≤ 10 ∧ cacheK.ac.A0V_t2.length ≤ 10 ∧
    (uMul k5Ops cacheK.ac.A0V_t0 cacheK.ac.Bv_SQ).length ≤ 12 ∧
    (uMul k5Ops cacheK.ac.A0V_t1 cacheK.ac.Bv_SQ).length ≤ 12 ∧
    (uMul k5Ops cacheK.ac.A0V_t2 cacheK.ac.Bv_SQ).length ≤ 12 ∧
    cacheK.ac.AY2_t0.length ≤ 10 ∧ cacheK.ac.AY2_t1.length ≤ 10 ∧
    cacheK.ac.AY3_t0.length ≤ 11 ∧ cacheK.ac.AY3_t1.length ≤ 11 ∧
    cacheK.ac.AX2_t0.length ≤ 11 ∧ cacheK.ac.AX2_t1.length ≤ 11 ∧ cacheK.ac.AX2_t2.length ≤ 11 ∧
    cacheK.ac.Bv_SQ.length ≤ 3 := by
  have htriv : PolyOpsRel k5Ops uOps (fun _ _ => True) :=
    ⟨trivial, fun _ => trivial, fun _ _ => trivial, fun _ _ => trivial, fun _ => trivial, fun _ _ => trivial, fun _ _ => trivial⟩
  have hrel := evalACache_rel htriv (S1 := S_K) (Q1 := Q_K) (S2 := ()) (Q2 := ()) trivial trivial
  have hu : ∀ {l1 : UPoly K5} {l2 : UPoly Unit}, URel (fun _ _ => True) l1 l2 → l1.length = l2.length :=
    fun h => h.length_eq
  rw [cacheK_props.1, hu (uTail_rel hrel.A0U_t0), hu (uTail_rel hrel.A0U_t1),
    hu hrel.A0V_t0, hu hrel.A0V_t1, hu hrel.A0V_t2,
    hu (uMul_rel htriv hrel.A0V_t0 hrel.Bv_SQ), hu (uMul_rel htriv hrel.A0V_t1 hrel.Bv_SQ),
    hu (uMul_rel htriv hrel.A0V_t2 hrel.Bv_SQ), hu hrel.AY2_t0, hu hrel.AY2_t1,
    hu hrel.AY3_t0, hu hrel.AY3_t1, hu hrel.AX2_t0, hu hrel.AX2_t1, hu hrel.AX2_t2, hu hrel.Bv_SQ]
  exact acUnit_lens

private lemma gtK_lens :
    (ubSub k5Ops gtK.q1_0_div_sc gtK.q1_2_div_sc).length ≤ 3 ∧
    gtK.DY2_qE_63.length ≤ 2 ∧ gtK.q1_1_sc.length ≤ 5 ∧
    gtK.qY_0_321489.length ≤ 4 ∧ gtK.qX_0_sc.length ≤ 3 ∧ gtK.q1_0_div_sc.length ≤ 3 ∧
    gtK.q1_2_div_sc.length ≤ 3 := by
  have htriv : PolyOpsRel k5Ops uOps (fun _ _ => True) :=
    ⟨trivial, fun _ => trivial, fun _ _ => trivial, fun _ _ => trivial, fun _ => trivial, fun _ _ => trivial, fun _ _ => trivial⟩
  have hac := evalACache_rel htriv (S1 := S_K) (Q1 := Q_K) (S2 := ()) (Q2 := ()) trivial trivial
  have hgsq := evalGeomSQ_rel htriv (S1 := S_K) (Q1 := Q_K) (S2 := ()) (Q2 := ()) trivial trivial
  have hrel := evalGeomT_rel htriv (S1 := S_K) (T1 := T_K) (S2 := ()) (T2 := ()) trivial hac.ca_p hac.cb_p hgsq trivial
  have hub : ∀ {l1 : UBivL K5} {l2 : UBivL Unit}, UBRel (fun _ _ => True) l1 l2 → l1.length = l2.length :=
    fun h => h.length_eq
  unfold gtK
  rw [cacheK_props.1, cacheK_props.2.1, hub (ubSub_rel htriv hrel.q1_0_div_sc hrel.q1_2_div_sc),
    hub hrel.DY2_qE_63, hub hrel.q1_1_sc, hub hrel.qY_0_321489, hub hrel.qX_0_sc,
    hub hrel.q1_0_div_sc, hub hrel.q1_2_div_sc]
  exact gtUnit_lens

-- Prove `evalBivLK5 (evalBTot k5Ops cacheK gtK T_K) = ∑ k : Fin 13, R12_int_p.coeff k.val * evalSQ_K5 (W_num_expr k)`!
private lemma evalBivLK5_BTot_eq_dot_W :
    evalBivLK5 (evalBTot k5Ops cacheK gtK T_K) =
      ∑ k : Fin 13, R12_int_p.coeff k.val * evalSQ_K5 (W_num_expr k) := by
  have hW_list := cacheK_props.2.2.1
  have hW_get (k : Fin 13) : cacheK.W.getD k.val 0 = evalSQ_K5 (W_num_expr k) := by
    rw [hW_list]; fin_cases k <;> rfl
  have hlen_ac := cacheK_ac_lens
  have hlen_gt := gtK_lens
  -- Expand `evalBTot` via `letB_intro` (zero DAG expansion!)
  let P_btot : BivL K5 → Prop := fun b => evalBivLK5 b = ∑ k : Fin 13, R12_int_p.coeff k.val * evalSQ_K5 (W_num_expr k)
  suffices h : P_btot (evalBTot k5Ops cacheK gtK T_K) from h
  unfold evalBTot
  refine letB_intro fun T2 hT2 => letB_intro fun d_A0U hdU => letB_intro fun d_A0V hdV =>
    letB_intro fun d_A0V_U hdVU => letB_intro fun d_A0VBv hdVB => letB_intro fun d_AY2 hdY2 =>
    letB_intro fun d_AY3 hdY3 => letB_intro fun d_AX2 hdX2 => ?_
  dsimp only [P_btot]
  have hd := cacheK_props.2.2.2.2.2
  rw [hdU, hdV, hdVB, hdVU, hdY2, hdY3, hdX2, hT2,
    hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.1,
    hd.2.2.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.2.2.2.2.1,
    hd.2.2.2.2.2.2.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2]
  simp only [evalBivLK5_bivAdd, evalBivLK5_bivNeg, evalBivLK5_bivSc,
    evalBivLK5_combineBivDot_uSc, evalBivLK5_combineBivDot_uAdd]
  rw [evalBivLK5_combineBivDot_dotW _ _ _ 1 (by omega) (by omega),
      evalBivLK5_combineBivDot_dotW _ _ _ 1 (by omega) (by omega),
      evalBivLK5_combineBivDot_dotW _ _ _ 1 (by omega) (by omega),
      evalBivLK5_combineBivDot_dotW _ _ _ 1 (by omega) (by omega),
      evalBivLK5_combineBivDot_dotW _ _ _ 0 (by omega) (by omega),
      evalBivLK5_combineBivDot_dotW _ _ _ 0 (by omega) (by omega),
      evalBivLK5_combineBivDot_dotW _ _ _ 0 (by omega) (by omega),
      evalBivLK5_combineBivDot_dotW _ _ _ 0 (by omega) (by omega),
      evalBivLK5_combineBivDot_dotW _ _ _ 0 (by omega) (by omega),
      evalBivLK5_combineBivDot_dotW _ _ _ 0 (by omega) (by omega),
      evalBivLK5_combineBivDot_dotW _ _ _ 0 (by omega) (by omega),
      evalBivLK5_combineBivDot_dotW _ _ _ 0 (by omega) (by omega),
      evalBivLK5_combineBivDot_dotW _ _ _ 0 (by omega) (by omega),
      evalBivLK5_combineBivDot_dotW _ _ _ 0 (by omega) (by omega),
      evalBivLK5_combineBivDot_dotW _ _ _ 0 (by omega) (by omega),
      evalBivLK5_combineBivDot_dotW _ _ _ 1 (by omega) (by omega),
      evalBivLK5_combineBivDot_dotW _ _ _ 1 (by omega) (by omega),
      evalBivLK5_combineBivDot_dotW _ _ _ 1 (by omega) (by omega)]
  have hmul : ∀ a b : K5, k5Ops.mul a b = a * b := fun _ _ => rfl
  have hof : ∀ n : ℤ, k5Ops.ofInt n = (n : K5) := fun _ => rfl
  simp only [hmul, hof, Int.cast_ofNat]
  simp_rw [hW_get]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro k _
  have hR12c : R12_int_p.coeff k.val = R13_int_p.coeff (k.val + 1) := by
    simp [R12_int_p, Polynomial.coeff_divX]
  rw [hR12c]
  have hcoeff_eq : R13_int_p.coeff (k.val + 1) =
      7 * gtK.Cv0_243 * ((Polynomial.X ^ 1 * evalUPolyK5 (uTail cacheK.ac.A0U_t0) * evalUBivLK5 (ubSub k5Ops gtK.q1_0_div_sc gtK.q1_2_div_sc)).coeff (k.val + 1) +
        T_K * (Polynomial.X ^ 1 * evalUPolyK5 (uTail cacheK.ac.A0U_t1) * evalUBivLK5 (ubSub k5Ops gtK.q1_0_div_sc gtK.q1_2_div_sc)).coeff (k.val + 1)) +
      45927 * (gtK.Cv0_243 * gtK.H0_7_2) * ((Polynomial.X ^ 1 * evalUPolyK5 cacheK.ac.AY3_t0 * evalUBivLK5 gtK.DY2_qE_63).coeff (k.val + 1) +
        T_K * (Polynomial.X ^ 1 * evalUPolyK5 cacheK.ac.AY3_t1 * evalUBivLK5 gtK.DY2_qE_63).coeff (k.val + 1)) +
      7 * ((Polynomial.X ^ 0 * evalUPolyK5 cacheK.ac.A0V_t0 * evalUBivLK5 gtK.q1_1_sc).coeff (k.val + 1) +
        T_K * (Polynomial.X ^ 0 * evalUPolyK5 cacheK.ac.A0V_t1 * evalUBivLK5 gtK.q1_1_sc).coeff (k.val + 1) +
        T_K * T_K * (Polynomial.X ^ 0 * evalUPolyK5 cacheK.ac.A0V_t2 * evalUBivLK5 gtK.q1_1_sc).coeff (k.val + 1)) +
      243 * gtK.H0_7_2 * (((Polynomial.X ^ 0 * evalUPolyK5 cacheK.ac.AY2_t0 * evalUBivLK5 gtK.qY_0_321489).coeff (k.val + 1) +
        T_K * (Polynomial.X ^ 0 * evalUPolyK5 cacheK.ac.AY2_t1 * evalUBivLK5 gtK.qY_0_321489).coeff (k.val + 1)) +
        ((Polynomial.X ^ 0 * evalUPolyK5 cacheK.ac.AX2_t0 * evalUBivLK5 gtK.qX_0_sc).coeff (k.val + 1) +
        T_K * (Polynomial.X ^ 0 * evalUPolyK5 cacheK.ac.AX2_t1 * evalUBivLK5 gtK.qX_0_sc).coeff (k.val + 1) +
        T_K * T_K * (Polynomial.X ^ 0 * evalUPolyK5 cacheK.ac.AX2_t2 * evalUBivLK5 gtK.qX_0_sc).coeff (k.val + 1))) -
      ((Polynomial.X ^ 0 * evalUPolyK5 (uMul k5Ops cacheK.ac.A0V_t0 cacheK.ac.Bv_SQ) * evalUBivLK5 gtK.q1_0_div_sc).coeff (k.val + 1) +
        T_K * (Polynomial.X ^ 0 * evalUPolyK5 (uMul k5Ops cacheK.ac.A0V_t1 cacheK.ac.Bv_SQ) * evalUBivLK5 gtK.q1_0_div_sc).coeff (k.val + 1) +
        T_K * T_K * (Polynomial.X ^ 0 * evalUPolyK5 (uMul k5Ops cacheK.ac.A0V_t2 cacheK.ac.Bv_SQ) * evalUBivLK5 gtK.q1_0_div_sc).coeff (k.val + 1) +
        gtK.Bv1_T_1701 * ((Polynomial.X ^ 1 * evalUPolyK5 cacheK.ac.A0V_t0 * evalUBivLK5 gtK.q1_0_div_sc).coeff (k.val + 1) +
          T_K * (Polynomial.X ^ 1 * evalUPolyK5 cacheK.ac.A0V_t1 * evalUBivLK5 gtK.q1_0_div_sc).coeff (k.val + 1) +
          T_K * T_K * (Polynomial.X ^ 1 * evalUPolyK5 cacheK.ac.A0V_t2 * evalUBivLK5 gtK.q1_0_div_sc).coeff (k.val + 1))) := by
    have hpoly : R13_int_p =
        Polynomial.C (7 * gtK.Cv0_243) * (Polynomial.X ^ 1 * evalUPolyK5 (uTail cacheK.ac.A0U_t0) * evalUBivLK5 (ubSub k5Ops gtK.q1_0_div_sc gtK.q1_2_div_sc) +
          Polynomial.C T_K * (Polynomial.X ^ 1 * evalUPolyK5 (uTail cacheK.ac.A0U_t1) * evalUBivLK5 (ubSub k5Ops gtK.q1_0_div_sc gtK.q1_2_div_sc))) +
        Polynomial.C (45927 * (gtK.Cv0_243 * gtK.H0_7_2)) * (Polynomial.X ^ 1 * evalUPolyK5 cacheK.ac.AY3_t0 * evalUBivLK5 gtK.DY2_qE_63 +
          Polynomial.C T_K * (Polynomial.X ^ 1 * evalUPolyK5 cacheK.ac.AY3_t1 * evalUBivLK5 gtK.DY2_qE_63)) +
        Polynomial.C 7 * (Polynomial.X ^ 0 * evalUPolyK5 cacheK.ac.A0V_t0 * evalUBivLK5 gtK.q1_1_sc +
          Polynomial.C T_K * (Polynomial.X ^ 0 * evalUPolyK5 cacheK.ac.A0V_t1 * evalUBivLK5 gtK.q1_1_sc) +
          Polynomial.C (T_K * T_K) * (Polynomial.X ^ 0 * evalUPolyK5 cacheK.ac.A0V_t2 * evalUBivLK5 gtK.q1_1_sc)) +
        Polynomial.C (243 * gtK.H0_7_2) * ((Polynomial.X ^ 0 * evalUPolyK5 cacheK.ac.AY2_t0 * evalUBivLK5 gtK.qY_0_321489 +
          Polynomial.C T_K * (Polynomial.X ^ 0 * evalUPolyK5 cacheK.ac.AY2_t1 * evalUBivLK5 gtK.qY_0_321489)) +
          (Polynomial.X ^ 0 * evalUPolyK5 cacheK.ac.AX2_t0 * evalUBivLK5 gtK.qX_0_sc +
          Polynomial.C T_K * (Polynomial.X ^ 0 * evalUPolyK5 cacheK.ac.AX2_t1 * evalUBivLK5 gtK.qX_0_sc) +
          Polynomial.C (T_K * T_K) * (Polynomial.X ^ 0 * evalUPolyK5 cacheK.ac.AX2_t2 * evalUBivLK5 gtK.qX_0_sc))) -
        (Polynomial.X ^ 0 * evalUPolyK5 (uMul k5Ops cacheK.ac.A0V_t0 cacheK.ac.Bv_SQ) * evalUBivLK5 gtK.q1_0_div_sc +
          Polynomial.C T_K * (Polynomial.X ^ 0 * evalUPolyK5 (uMul k5Ops cacheK.ac.A0V_t1 cacheK.ac.Bv_SQ) * evalUBivLK5 gtK.q1_0_div_sc) +
          Polynomial.C (T_K * T_K) * (Polynomial.X ^ 0 * evalUPolyK5 (uMul k5Ops cacheK.ac.A0V_t2 cacheK.ac.Bv_SQ) * evalUBivLK5 gtK.q1_0_div_sc) +
          Polynomial.C gtK.Bv1_T_1701 * (Polynomial.X ^ 1 * evalUPolyK5 cacheK.ac.A0V_t0 * evalUBivLK5 gtK.q1_0_div_sc +
            Polynomial.C T_K * (Polynomial.X ^ 1 * evalUPolyK5 cacheK.ac.A0V_t1 * evalUBivLK5 gtK.q1_0_div_sc) +
            Polynomial.C (T_K * T_K) * (Polynomial.X ^ 1 * evalUPolyK5 cacheK.ac.A0V_t2 * evalUBivLK5 gtK.q1_0_div_sc))) := by
      simp only [R13_int_p, A0U_U_p, A0V_p, AY2_p, AY3_p, AX2_p, Bv_1701_p,
        evalUBivLK5_ubSub, evalUPolyK5_uMul, pow_zero, pow_one, one_mul, map_mul, pow_two]
      ring
    rw [hpoly]
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  rw [hcoeff_eq]; ring

private lemma R12_int_p_natDegree_le : R12_int_p.natDegree ≤ 12 := by
  have h13 : R13_int_p.natDegree ≤ 13 := by
    have hac := cacheK_ac_lens
    have hgt := gtK_lens
    have hUdeg : ∀ (l : UPoly K5) (n : ℕ), l.length ≤ n + 1 → (evalUPolyK5 l).natDegree ≤ n := fun l n h =>
      Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm => evalUPolyK5_natDegree_le l m (by omega)
    have hUBdeg : ∀ (l : UBivL K5) (n : ℕ), l.length ≤ n + 1 → (evalUBivLK5 l).natDegree ≤ n := fun l n h =>
      Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm => by
        rw [evalUBivLK5_coeff, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    have hA0U : A0U_U_p.natDegree ≤ 8 := (Polynomial.natDegree_add_le _ _).trans (max_le
      (hUdeg _ 8 hac.1)
      ((Polynomial.natDegree_C_mul_le _ _).trans (hUdeg _ 8 hac.2.1)))
    have hA0V : A0V_p.natDegree ≤ 9 := (Polynomial.natDegree_add_le _ _).trans (max_le
      ((Polynomial.natDegree_add_le _ _).trans (max_le
        (hUdeg _ 9 hac.2.2.1)
        ((Polynomial.natDegree_C_mul_le _ _).trans (hUdeg _ 9 hac.2.2.2.1))))
      ((Polynomial.natDegree_C_mul_le _ _).trans (hUdeg _ 9 hac.2.2.2.2.1)))
    have hAY2 : AY2_p.natDegree ≤ 9 := (Polynomial.natDegree_add_le _ _).trans (max_le
      (hUdeg _ 9 hac.2.2.2.2.2.2.2.2.1)
      ((Polynomial.natDegree_C_mul_le _ _).trans (hUdeg _ 9 hac.2.2.2.2.2.2.2.2.2.1)))
    have hAY3 : AY3_p.natDegree ≤ 10 := (Polynomial.natDegree_add_le _ _).trans (max_le
      (hUdeg _ 10 hac.2.2.2.2.2.2.2.2.2.2.1)
      ((Polynomial.natDegree_C_mul_le _ _).trans (hUdeg _ 10 hac.2.2.2.2.2.2.2.2.2.2.2.1)))
    have hAX2 : AX2_p.natDegree ≤ 10 := (Polynomial.natDegree_add_le _ _).trans (max_le
      ((Polynomial.natDegree_add_le _ _).trans (max_le
        (hUdeg _ 10 hac.2.2.2.2.2.2.2.2.2.2.2.2.1)
        ((Polynomial.natDegree_C_mul_le _ _).trans (hUdeg _ 10 hac.2.2.2.2.2.2.2.2.2.2.2.2.2.1))))
      ((Polynomial.natDegree_C_mul_le _ _).trans (hUdeg _ 10 hac.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)))
    have hBv : Bv_1701_p.natDegree ≤ 2 := (Polynomial.natDegree_add_le _ _).trans (max_le
      (hUdeg _ 2 hac.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
      ((Polynomial.natDegree_mul_le).trans (by simp)))
    have hq10 : (evalUBivLK5 gtK.q1_0_div_sc).natDegree ≤ 2 := hUBdeg _ 2 hgt.2.2.2.2.2.1
    have hq12 : (evalUBivLK5 gtK.q1_2_div_sc).natDegree ≤ 2 := hUBdeg _ 2 hgt.2.2.2.2.2.2
    have hq11 : (evalUBivLK5 gtK.q1_1_sc).natDegree ≤ 4 := hUBdeg _ 4 hgt.2.2.1
    have hDYqE : (evalUBivLK5 gtK.DY2_qE_63).natDegree ≤ 1 := hUBdeg _ 1 hgt.2.1
    have hqY0 : (evalUBivLK5 gtK.qY_0_321489).natDegree ≤ 3 := hUBdeg _ 3 hgt.2.2.2.1
    have hqX0 : (evalUBivLK5 gtK.qX_0_sc).natDegree ≤ 2 := hUBdeg _ 2 hgt.2.2.2.2.1
    have hXmul : ∀ P : K5[X], (Polynomial.X * P).natDegree ≤ 1 + P.natDegree := fun P =>
      Polynomial.natDegree_mul_le.trans (by simp)
    unfold R13_int_p
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
        · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
          · exact (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_mul_le.trans (by
              have := hXmul A0U_U_p; have := Polynomial.natDegree_sub_le (evalUBivLK5 gtK.q1_0_div_sc) (evalUBivLK5 gtK.q1_2_div_sc); omega))
          · exact (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_mul_le.trans (by
              have := hXmul AY3_p; omega))
        · exact (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_mul_le.trans (by omega))
      · exact (Polynomial.natDegree_C_mul_le _ _).trans ((Polynomial.natDegree_add_le _ _).trans (max_le
          (Polynomial.natDegree_mul_le.trans (by omega)) (Polynomial.natDegree_mul_le.trans (by omega))))
    · exact Polynomial.natDegree_mul_le.trans (by
        have := Polynomial.natDegree_mul_le (p := A0V_p) (q := Bv_1701_p); omega)
  exact (natDegree_divX_le_pred R13_int_p).trans (by omega)

-- Master Section 3 theorem: `∑_{r ∈ RQ5} residue r eta_L` expressed in terms of `evalBivLK5 (evalBTot k5Ops cacheK gtK T_K)`!
private lemma sum_RQ5_eta_L_eq_BTot :
    ∑ r ∈ RQ5, CrossedRationalResidue.residue r eta_L =
      ιL_K5 (evalBivLK5 (evalBTot k5Ops cacheK gtK T_K) * ((sc5_den * sc7_den : ℤ) : K5) /
        (81 * k5Params.Cv0 * (M_R_int : K5) * ((sc5_num * sc7_num : ℤ) : K5) *
          (D_int_all : K5) * evalSQ_K5 D_all_expr)) := by
  rw [Finset.sum_congr rfl residue_eta_L_eq_main, trace_AC_eta_AC_main_eq]
  set cK : K5 := 81 * k5Params.Cv0 * (M_R_int : K5)
  have hcK_ne : cK ≠ 0 := by
    have h81 : (81 : K5) ≠ 0 := by exact_mod_cast (by decide : (81 : ℕ) ≠ 0)
    have hMR : (M_R_int : K5) ≠ 0 := Int.cast_ne_zero.mpr (by unfold M_R_int M_A_int L_all_A M_mid_int; decide)
    exact mul_ne_zero (mul_ne_zero h81 k5Params_Cv0_ne) hMR
  have hmap : mapRatFunc ιL_K5 (toRat R12_int_p / (RatFunc.C cK * toRat (k5Params.Q7_z * k5Params.Q5_z))) =
      algebraMap CoverL[X] (RatFunc CoverL) (R12_int_p.map ιL_K5) /
      algebraMap CoverL[X] (RatFunc CoverL) (Polynomial.C (ιL_K5 cK) * (k5Params.Q7_z.map ιL_K5) * (k5Params.Q5_z.map ιL_K5)) := by
    simp only [map_div₀, map_mul, mapRatFunc_C, mapRatFunc_toRat,
      RatFunc.algebraMap_C, mul_assoc]
  rw [hmap]
  set D_L : CoverL[X] := Polynomial.C (ιL_K5 cK) * (k5Params.Q7_z.map ιL_K5) * (k5Params.Q5_z.map ιL_K5)
  have hres_r (r : CoverL) (hr : r ∈ RQ5) :
      CrossedRationalResidue.residue r
        (algebraMap CoverL[X] (RatFunc CoverL) (R12_int_p.map ιL_K5) /
         algebraMap CoverL[X] (RatFunc CoverL) D_L) =
      (R12_int_p.map ιL_K5).eval r /
        (ιL_K5 cK * (k5Params.Q7_z.map ιL_K5).eval r * (k5Params.Q5_z.map ιL_K5).derivative.eval r) := by
    have hr0 := mem_RQ5_iff.mp hr
    have hD0 : D_L.eval r = 0 := by simp [D_L, hr0]
    have hDd : D_L.derivative.eval r =
        ιL_K5 cK * (k5Params.Q7_z.map ιL_K5).eval r * (k5Params.Q5_z.map ιL_K5).derivative.eval r := by
      simp only [D_L, mul_assoc, Polynomial.derivative_mul,
        Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, hr0, mul_zero, zero_add]
    have hDd_ne : D_L.derivative.eval r ≠ 0 := by
      rw [hDd]
      have h7 := eval_ne_zero_of_isCoprime isCoprime_Q5_Q7 hr0
      have hd5 := eval_ne_zero_of_isCoprime isCoprime_Q5_Q5_deriv hr0
      rw [← Polynomial.derivative_map] at hd5
      exact mul_ne_zero (mul_ne_zero ((map_ne_zero_iff _ ιL_K5.injective).mpr hcK_ne) h7) hd5
    rw [simplePole_residue _ D_L r hD0 hDd_ne, hDd]
  rw [Finset.sum_congr rfl hres_r]
  have hR12_sum (r : CoverL) : (R12_int_p.map ιL_K5).eval r =
      ∑ k : Fin 13, ιL_K5 (R12_int_p.coeff k.val) * r ^ k.val := by
    have hdeg : (R12_int_p.map ιL_K5).natDegree < 13 :=
      lt_of_le_of_lt Polynomial.natDegree_map_le (by have := R12_int_p_natDegree_le; omega)
    conv_lhs => rw [Polynomial.as_sum_range' (R12_int_p.map ιL_K5) 13 hdeg, ← Fin.sum_univ_eq_sum_range]
    rw [← Polynomial.coe_evalRingHom, map_sum]
    simp only [Polynomial.coe_evalRingHom, Polynomial.eval_monomial, Polynomial.coeff_map]
  simp_rw [hR12_sum, Finset.sum_div]
  rw [Finset.sum_comm]
  have hterm (k : Fin 13) :
      ∑ r ∈ RQ5, ιL_K5 (R12_int_p.coeff k.val) * r ^ k.val /
        (ιL_K5 cK * (k5Params.Q7_z.map ιL_K5).eval r * (k5Params.Q5_z.map ιL_K5).derivative.eval r) =
      ιL_K5 (R12_int_p.coeff k.val * W_K5_scaled k / cK) := by
    have h1 : ∀ r ∈ RQ5,
        ιL_K5 (R12_int_p.coeff k.val) * r ^ k.val /
          (ιL_K5 cK * (k5Params.Q7_z.map ιL_K5).eval r * (k5Params.Q5_z.map ιL_K5).derivative.eval r) =
        (ιL_K5 (R12_int_p.coeff k.val) / ιL_K5 cK) *
          (r ^ k.val / ((k5Params.Q7_z.map ιL_K5).eval r * (k5Params.Q5_z.map ιL_K5).derivative.eval r)) := fun r _ => by ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, sum_RQ5_power_eq_W_k k]
    simp only [map_div₀, map_mul]; ring
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← map_sum]
  congr 1
  rw [evalBivLK5_BTot_eq_dot_W, Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl; intro k _
  simp only [W_K5_scaled, W_K5, cK]; ring

/-! ### Section 4: Factored Centered Grid × Kronecker Kernel Check (`sum_RQ5_eta_L`) -/

private def masterBits : ℕ := 474
private def masterDegS : ℕ := 70
private def masterLim : ℕ := Nat.pow 2 masterBits
private def bS2D : ℤ := Int.ofNat masterLim
private def bQ2D : ℤ := Int.ofNat (Nat.pow 2 (masterDegS * masterBits))
private def c2D : SQCache ℤ := evalSQCache intOps bS2D bQ2D
private def cPB2D : SQCache PB := evalSQCache pbOps ⟨1, 0, 0, 1⟩ ⟨0, 1, 0, 1⟩

private def checkMasterBounds : Bool :=
  (evalTStep pbOps ⟨1, 0, 0, 1⟩ cPB2D ⟨0, 0, 1, 10⟩).all fun row =>
    row.all fun b => Nat.blt b.dS masterDegS && Nat.blt b.dT 20 && Nat.blt b.M masterLim

private def checkMasterTChunk (lo : ℤ) (n : ℕ) : Bool :=
  allRange lo n fun t =>
    (evalTStep intOps bS2D c2D t).all fun row =>
      row.all fun z => z == 0

private lemma checkMasterTChunk_append (lo : ℤ) (m n : ℕ) :
    checkMasterTChunk lo (m + n) = (checkMasterTChunk lo m && checkMasterTChunk (lo + (m : ℤ)) n) :=
  allRange_append lo m n _

private lemma master_bounds_ok : checkMasterBounds = true := by decide +kernel
private lemma master_t_0 : checkMasterTChunk (-9) 4 = true := by decide +kernel
private lemma master_t_1 : checkMasterTChunk (-5) 4 = true := by decide +kernel
private lemma master_t_2 : checkMasterTChunk (-1) 4 = true := by decide +kernel
private lemma master_t_3 : checkMasterTChunk 3 4 = true := by decide +kernel
private lemma master_t_4 : checkMasterTChunk 7 4 = true := by decide +kernel

private lemma master_values_ok : checkMasterTChunk (-9) 20 = true := by
  rw [show (20 : ℕ) = 4 + 16 from rfl, checkMasterTChunk_append, master_t_0, Bool.true_and]
  rw [show ((-9 : ℤ) + (4 : ℕ)) = -5 from rfl, show (16 : ℕ) = 4 + 12 from rfl, checkMasterTChunk_append, master_t_1, Bool.true_and]
  rw [show ((-5 : ℤ) + (4 : ℕ)) = -1 from rfl, show (12 : ℕ) = 4 + 8 from rfl, checkMasterTChunk_append, master_t_2, Bool.true_and]
  rw [show ((-1 : ℤ) + (4 : ℕ)) = 3 from rfl, show (8 : ℕ) = 4 + 4 from rfl, checkMasterTChunk_append, master_t_3, Bool.true_and]
  exact master_t_4

private lemma master_bivL_zero_K5 :
    evalBivLK5 (evalTStep k5Ops S_K cacheK T_K) = 0 := by
  have hb_ok : checkMasterBounds = true := master_bounds_ok
  have hv_ok : checkMasterTChunk (-9) 20 = true := master_values_ok
  unfold checkMasterBounds at hb_ok
  unfold checkMasterTChunk at hv_ok
  let cP3 := evalSQCache poly3Ops (MvPolynomial.X 0) (MvPolynomial.X 1)
  let bP3 := evalTStep poly3Ops (MvPolynomial.X 0) cP3 (MvPolynomial.X 2)
  let bPB := evalTStep pbOps ⟨1, 0, 0, 1⟩ cPB2D ⟨0, 0, 1, 10⟩
  have hrelB : BRel (RespectsBound2D masterDegS 10) bP3 bPB :=
    evalTStep_rel (respectsBound2DRel masterDegS 10) (respectsBound2D_X0 masterDegS 10)
      (evalSQCache_rel (respectsBound2DRel masterDegS 10) (respectsBound2D_X0 masterDegS 10) (respectsBound2D_X1 masterDegS 10))
      (respectsBound2D_X2 masterDegS 10)
  have hbQ_eq : (((2 ^ masterBits : ℕ) ^ masterDegS : ℕ) : ℤ) = bQ2D := by
    rw [bQ2D, ← pow_mul, _root_.mul_comm]; rfl
  have hrelV (t : ℤ) :
      BRel (fun p z => MvPolynomial.eval (v3Int (2 ^ masterBits : ℕ) (((2 ^ masterBits : ℕ) ^ masterDegS : ℕ) : ℤ) t) p = z)
        bP3 (evalTStep intOps bS2D c2D t) :=
    evalTStep_rel (poly3ToIntRel (2 ^ masterBits : ℕ) (((2 ^ masterBits : ℕ) ^ masterDegS : ℕ) : ℤ) t)
      (by simp [v3Int, bS2D, masterLim])
      (evalSQCache_rel (poly3ToIntRel (2 ^ masterBits : ℕ) (((2 ^ masterBits : ℕ) ^ masterDegS : ℕ) : ℤ) t)
        (by simp [v3Int, bS2D, masterLim]) (by simp [v3Int, hbQ_eq]))
      (by simp [v3Int])
  have hrelK : BRel (fun p x => evalP3K5 p = x) bP3 (evalTStep k5Ops S_K cacheK T_K) :=
    evalTStep_rel poly3ToK5Rel (by simp [evalP3K5, v3K5])
      (evalSQCache_rel poly3ToK5Rel (by simp [evalP3K5, v3K5]) (by simp [evalP3K5, v3K5]))
      (by simp [evalP3K5, v3K5])
  have hallB : ∀ r ∈ bPB, ∀ b ∈ r, b.dS < masterDegS ∧ b.dT < 20 ∧ b.M < 2 ^ masterBits := by
    intro r hr b hb
    have h1 := List.all_eq_true.mp hb_ok r hr
    have h2 := List.all_eq_true.mp h1 b hb
    simp only [Bool.and_eq_true, Nat.blt_eq] at h2
    exact ⟨h2.1.1, h2.1.2, h2.2⟩
  have hallV : ∀ t ∈ rangeInt (-9) 20,
      ∀ r ∈ evalTStep intOps bS2D c2D t, ∀ z ∈ r, z = 0 := by
    intro t ht r hr z hz
    have h1 := allRange_spec (-9) 20 _ hv_ok t ht
    have h2 := List.all_eq_true.mp h1 r hr
    exact beq_iff_eq.mp (List.all_eq_true.mp h2 z hz)
  have hrow_zero : ∀ (D B : ℕ) (rP : UPoly P3Z) (rB : UPoly PB) (rV : ℤ → UPoly ℤ) (rK : UPoly K5),
      URel (RespectsBound2D D 10) rP rB →
      (∀ t, URel (fun p z => MvPolynomial.eval (v3Int (B : ℤ) ((B ^ D : ℕ) : ℤ) t) p = z) rP (rV t)) →
      URel (fun p x => evalP3K5 p = x) rP rK →
      (∀ b ∈ rB, b.dS < D ∧ b.dT < 20 ∧ b.M < B) →
      (∀ t ∈ rangeInt (-9) 20, ∀ z ∈ rV t, z = 0) →
      evalYListK5 rK = 0 := by
    intro D B rP
    induction rP with
    | nil =>
        intro rB rV rK _ _ hrK _ _
        cases hrK; rfl
    | cons p ps ih =>
        intro rB rV rK hrB hrV hrK haB haV
        cases hrB with | cons hb hbs =>
        cases hrK with | cons hk hks =>
        rename_i b bs k ks
        obtain ⟨hdS, hdT, hM⟩ := haB b (by simp)
        have hp0 : p = 0 := by
          apply mvPoly3_eq_zero_of_kronecker2D_gridT p b D 10 B (rangeInt (-9) 20)
            hb hdS (by rw [rangeInt_card]; exact hdT)
            (rangeInt_natAbs_le (-9) 20 10 (by decide) (by decide)) hM
          intro t ht
          have hvt := hrV t
          rcases hv : rV t with _ | ⟨z, zs⟩
          · rw [hv] at hvt; cases hvt
          · rw [hv] at hvt; cases hvt with | cons hz _ =>
            rw [hz]; exact haV t ht z (by simp [hv])
        have hk0 : k = 0 := by rw [← hk, hp0, map_zero]
        have htail0 : evalYListK5 ks = 0 := by
          apply ih bs (fun t => (rV t).tail) ks hbs
          · intro t
            have hvt := hrV t
            rcases hv : rV t with _ | ⟨z, zs⟩
            · rw [hv] at hvt; cases hvt
            · rw [hv] at hvt; cases hvt with | cons _ hzs => simpa [hv] using hzs
          · exact hks
          · intro x hx; exact haB x (by simp [hx])
          · intro t ht z hz
            rcases hv : rV t with _ | ⟨z0, zs⟩
            · simp [hv] at hz
            · simp only [hv, List.tail_cons] at hz
              exact haV t ht z (by simp [hv, hz])
        simp only [evalYListK5, hk0, htail0, mul_zero, add_zero]
  have hzero_gen : ∀ (D B : ℕ) (bP : BivL P3Z) (bB : BivL PB)
      (bV : ℤ → BivL ℤ) (bK : BivL K5),
      BRel (RespectsBound2D D 10) bP bB →
      (∀ t, BRel (fun p z => MvPolynomial.eval (v3Int (B : ℤ) ((B ^ D : ℕ) : ℤ) t) p = z) bP (bV t)) →
      BRel (fun p x => evalP3K5 p = x) bP bK →
      (∀ r ∈ bB, ∀ b ∈ r, b.dS < D ∧ b.dT < 20 ∧ b.M < B) →
      (∀ t ∈ rangeInt (-9) 20, ∀ r ∈ bV t, ∀ z ∈ r, z = 0) →
      evalBivLK5 bK = 0 := by
    intro D B bP
    induction bP with
    | nil =>
        intro bB bV bK _ _ hrK _ _
        cases hrK; rfl
    | cons r rs ih =>
        intro bB bV bK hrB hrV hrK haB haV
        cases hrB with | cons hrb hrbs =>
        cases hrK with | cons hrk hrks =>
        rename_i rB rBs rK rKs
        have hr0 : evalYListK5 rK = 0 := by
          apply hrow_zero D B r rB (fun t => (bV t).headD []) rK hrb
          · intro t
            have hvt := hrV t
            rcases hv : bV t with _ | ⟨rv, rvs⟩
            · rw [hv] at hvt; cases hvt
            · rw [hv] at hvt; cases hvt with | cons hrv _ => simpa [hv] using hrv
          · exact hrk
          · exact haB rB (by simp)
          · intro t ht z hz
            have hvt := hrV t
            rcases hv : bV t with _ | ⟨rv, rvs⟩
            · rw [hv] at hvt; cases hvt
            · simp only [hv, List.headD_cons] at hz
              exact haV t ht rv (by simp [hv]) z hz
        have htail0 : evalBivLK5 rKs = 0 := by
          apply ih rBs (fun t => (bV t).tail) rKs hrbs
          · intro t
            have hvt := hrV t
            rcases hv : bV t with _ | ⟨rv, rvs⟩
            · rw [hv] at hvt; cases hvt
            · rw [hv] at hvt; cases hvt with | cons _ hrvs => simpa [hv] using hrvs
          · exact hrks
          · intro r' hr'; exact haB r' (by simp [hr'])
          · intro t ht r' hr' z hz
            rcases hv : bV t with _ | ⟨rv, rvs⟩
            · simp [hv] at hr'
            · simp only [hv, List.tail_cons] at hr'
              exact haV t ht r' (by simp [hv, hr']) z hz
        simp only [evalBivLK5, hr0, htail0, mul_zero, add_zero]
  exact hzero_gen masterDegS (2 ^ masterBits) bP3 bPB (evalTStep intOps bS2D c2D) (evalTStep k5Ops S_K cacheK T_K) hrelB hrelV hrelK hallB hallV

-- Exact bridge from `evalBivLK5 (evalTStep k5Ops S_K cacheK T_K) = 0` to `sum_RQ5_eta_L`!
theorem sum_RQ5_eta_L :
    ∑ r ∈ RQ5, CrossedRationalResidue.residue r eta_L = ιL_K5 (toK5_RQ5 / L_K ^ 2) := by
  rw [sum_RQ5_eta_L_eq_BTot]
  congr 1
  -- Evaluate `evalBivLK5 (evalTStep k5Ops S_K cacheK T_K) = 0`!
  have hstep0 := master_bivL_zero_K5
  have hH0 := evalGeomT_AC_bridge.1
  have hCv0 := evalGeomT_AC_bridge.2.2.1
  have hCv0i := evalGeomT_AC_bridge.2.2.2.1
  have hRQ5_raw := cacheK_props.2.2.2.2.1
  have hD_all_eq := cacheK_props.2.2.2.1
  have hBTot_eq : (21 * S_K) ^ 2 * evalBivLK5 (evalBTot k5Ops cacheK gtK T_K) =
      (C_RHS_int : K5) * (21 * S_K) ^ 2 * gtK.Cv0_int * cacheK.D_div_L2 * evalBivK5 RQ5_biv := by
    have hstep_eval : evalBivLK5 (evalTStep k5Ops S_K cacheK T_K) =
        (21 * S_K) ^ 2 * evalBivLK5 (evalBTot k5Ops cacheK gtK T_K) -
        (C_RHS_int : K5) * (21 * S_K) ^ 2 * gtK.Cv0_int * cacheK.D_div_L2 * evalBivK5 RQ5_biv := by
      let P_ts : BivL K5 → Prop := fun b => evalBivLK5 b =
        (21 * S_K) ^ 2 * evalBivLK5 (evalBTot k5Ops cacheK gtK T_K) -
        (C_RHS_int : K5) * (21 * S_K) ^ 2 * gtK.Cv0_int * cacheK.D_div_L2 * evalBivK5 RQ5_biv
      suffices h : P_ts (evalTStep k5Ops S_K cacheK T_K) from h
      unfold evalTStep
      refine letB_intro fun gt hgt => letB_intro fun B_tot hB =>
        letB_intro fun s21 hs21 => letB_intro fun t21 ht21 => letB_intro fun nh0 hnh0 =>
        letB_intro fun lhs hlhs => letB_intro fun rhs_sc hrsc => letB_intro fun rhs_raw hrraw => ?_
      dsimp only [P_ts]
      have hgt' : gt = gtK := hgt
      rw [evalBivLK5_bivSub, evalBivLK5_bivSc, hlhs, hrsc, hrraw, hB, hRQ5_raw, hs21, ht21, hnh0, hgt']
      have hmul : ∀ a b : K5, k5Ops.mul a b = a * b := fun _ _ => rfl
      have hof : ∀ n : ℤ, k5Ops.ofInt n = (n : K5) := fun _ => rfl
      have hneg : ∀ a : K5, k5Ops.neg a = -a := fun _ => rfl
      simp only [hmul, hof, hneg, Int.cast_ofNat, hH0]
      rw [evalBivLK5_bivRedOnce, evalBivLK5_bivRedOnce]
      ring
    linear_combination hstep0 - hstep_eval
  have h21S_ne : (21 * S_K) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (mul_ne_zero (by exact_mod_cast (by decide : (21 : ℕ) ≠ 0)) S_K_ne_zero)
  have hBTot_cancel : evalBivLK5 (evalBTot k5Ops cacheK gtK T_K) =
      (C_RHS_int : K5) * gtK.Cv0_int * cacheK.D_div_L2 * ((D_RQ5 : K5) * toK5_RQ5) := by
    apply mul_left_cancel₀ h21S_ne
    have hDRQ5 : evalBivK5 RQ5_biv = (D_RQ5 : K5) * toK5_RQ5 := by
      rw [toK5_RQ5, mul_div_cancel₀ _ (Int.cast_ne_zero.mpr (by unfold D_RQ5; decide))]
    rw [hBTot_eq, hDRQ5]; ring
  -- Cancel `Cv0_int`, `cacheK.D_div_L2`, and match the exact integer constant identity via `by decide`!
  have hConstZ : C_RHS_int * D_RQ5 * (sc5_den * sc7_den) * 3 =
      (-25) * (sc5_num * sc7_num) * D_int_all * M_R_int := by
    unfold C_RHS_int D_RQ5 sc5_den sc7_den sc5_num sc7_num D_int_all M_R_int M_A_int L_all_A M_mid_int
    decide
  have hConstK : (C_RHS_int : K5) * (D_RQ5 : K5) * ((sc5_den * sc7_den : ℤ) : K5) * 3 =
      (-25 : K5) * ((sc5_num * sc7_num : ℤ) : K5) * (D_int_all : K5) * (M_R_int : K5) := by
    exact_mod_cast hConstZ
  have h81Cv0 : 81 * k5Params.Cv0 = (-(25 / 3 : K5)) * gtK.Cv0_int := by
    have h3 : (3 : K5) ≠ 0 := by exact_mod_cast (by decide : (3 : ℕ) ≠ 0)
    apply mul_left_cancel₀ h3
    calc (3 : K5) * (81 * k5Params.Cv0) = 243 * k5Params.Cv0 := by ring
      _ = gtK.Cv0_243 := hCv0.symm
      _ = -25 * gtK.Cv0_int := hCv0i
      _ = 3 * (-(25 / 3 : K5) * gtK.Cv0_int) := by ring
  have hL_ne : L_K ≠ 0 := by
    intro h0; exact fac_4_ne (by rw [fac_4_eq_neg_L, h0, neg_zero])
  have hCv0i_ne : gtK.Cv0_int ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h81Cv0
    exact mul_ne_zero (by exact_mod_cast (by decide : (81 : ℕ) ≠ 0)) k5Params_Cv0_ne h81Cv0
  have hDdiv_ne : cacheK.D_div_L2 ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hD_all_eq; exact D_all_K5_ne hD_all_eq
  have hMR_ne : (M_R_int : K5) ≠ 0 := Int.cast_ne_zero.mpr (by unfold M_R_int M_A_int L_all_A M_mid_int; decide)
  have hsc_ne : ((sc5_num * sc7_num : ℤ) : K5) ≠ 0 := Int.cast_ne_zero.mpr (by unfold sc5_num sc7_num; decide)
  have hDint_ne : (D_int_all : K5) ≠ 0 := Int.cast_ne_zero.mpr (by unfold D_int_all; decide)
  have h3_ne : (3 : K5) ≠ 0 := by exact_mod_cast (by decide : (3 : ℕ) ≠ 0)
  have h25_ne : (-25 : K5) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast (by decide : (25 : ℕ) ≠ 0))
  rw [hBTot_cancel, hD_all_eq, h81Cv0]
  rw [div_eq_div_iff
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (neg_ne_zero.mpr (div_ne_zero (by exact_mod_cast (by decide : (25 : ℕ) ≠ 0)) h3_ne)) hCv0i_ne)
      hMR_ne) hsc_ne) hDint_ne) (mul_ne_zero hDdiv_ne (pow_ne_zero 2 hL_ne)))
    (pow_ne_zero 2 hL_ne)]
  apply mul_left_cancel₀ h3_ne
  generalize (C_RHS_int : K5) = cR at hConstK ⊢
  generalize (D_RQ5 : K5) = cD at hConstK ⊢
  generalize ((sc5_den * sc7_den : ℤ) : K5) = cSD at hConstK ⊢
  generalize ((sc5_num * sc7_num : ℤ) : K5) = cSN at hConstK ⊢
  generalize (D_int_all : K5) = cDI at hConstK ⊢
  generalize (M_R_int : K5) = cMR at hConstK ⊢
  linear_combination (gtK.Cv0_int * cacheK.D_div_L2 * toK5_RQ5 * L_K ^ 2) * hConstK

/-! ### Section 5: Exact Global Residue Cancellation (`global_residue_cancellation`) -/

private def L5_glob_e : Expr :=
  .add (.add (.mul (.num 77) (.var 0)) (.mul (.num (-210)) (.var 1))) (.num 45)

private def LHS_glob_biv : Biv :=
  VerticalIdentity.bivAdd (scale (.pow L5_glob_e 2) 0 0 (VerticalIdentity.bivAdd P_horiz_biv (scale (.num 105) 0 0 RU_biv)))
    (VerticalIdentity.bivAdd (scale (.num 5) 0 0 RInf_biv) (scale (.num 147) 0 0 RQ5_biv))

private lemma global_biv_identity : evalBivK5 LHS_glob_biv = 0 := by
  have h := biv_denote_eq_of_kronecker3 vK5 x_K y_K 18 16 16 (2 ^ 105) LHS_glob_biv .nil (by decide +kernel)
  simpa only [evalBivK5, denote] using h

theorem global_residue_cancellation :
    toK5 P_horiz_5 = -toK5_RInf / L_K ^ 2 - toK5_RU - toK5_RQ5 / L_K ^ 2 := by
  have hid := global_biv_identity
  rw [LHS_glob_biv, evalBivK5_bivAdd, evalBivK5_bivAdd, evalBivK5_scale, evalBivK5_bivAdd,
    evalBivK5_scale, evalBivK5_scale, evalBivK5_scale] at hid
  have hL5 : ringEval vK5 (.pow L5_glob_e 2) = L_K ^ 2 := by
    simp only [L5_glob_e, ringEval, vK5, L_K, Int.cast_neg, Int.cast_ofNat]; ring
  have hP : evalBivK5 P_horiz_biv = (D_P : K5) * toK5 P_horiz_5 := by
    have hDP_ne : (D_P : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (by unfold D_P; decide)
    have hCmul : (D_P : K5) * toK5 (MvPolynomial.C (1 / (D_P : ℂ))) = 1 := by
      have h1 : (D_P : K5) = toK5 (MvPolynomial.C (D_P : ℂ)) := by
        have hC : MvPolynomial.C (D_P : ℂ) = (D_P : MvPolynomial (Fin 5) ℂ) :=
          map_intCast (MvPolynomial.C (σ := Fin 5) (R := ℂ)) D_P
        rw [hC, map_intCast]
      rw [h1, ← map_mul, ← map_mul, mul_one_div_cancel hDP_ne, map_one, map_one]
    have hev : toK5 (evalBiv5 P_horiz_biv) = evalBivK5 P_horiz_biv := by
      have hgen : ∀ b : Biv, toK5 (evalBiv5 b) = evalBivK5 b := by
        intro b; induction b with
        | nil => simp [evalBiv5, evalBivK5, denote]
        | cons e i j rest ih =>
            simp only [evalBiv5, evalBivK5, denote, map_add, map_mul, map_pow] at ih ⊢
            rw [ih]
            have hv : toK5 (ringEval vSQT e) = ringEval vK5 e := by
              induction e with
              | num c => simp [ringEval]
              | natCast n => simp [ringEval]
              | intCast z => simp [ringEval]
              | var k =>
                  match k with
                  | 0 => simp [ringEval, vSQT, vK5, toK5]
                  | 1 => simp [ringEval, vSQT, vK5, toK5]
                  | 2 => simp [ringEval, vSQT, vK5, toK5]
                  | _ + 3 => simp [ringEval, vSQT, vK5]
              | neg a ha => simp [ringEval] at ha ⊢; rw [ha]
              | add a b ha hb => simp [ringEval] at ha hb ⊢; rw [ha, hb]
              | sub a b ha hb => simp [ringEval] at ha hb ⊢; rw [ha, hb]
              | mul a b ha hb => simp [ringEval] at ha hb ⊢; rw [ha, hb]
              | pow a k ha => simp [ringEval] at ha ⊢; rw [ha]
            have hx3 : toK5 (MvPolynomial.X 3) = x_K := by simp [toK5]
            have hx4 : toK5 (MvPolynomial.X 4) = y_K := by simp [toK5]
            rw [hv, hx3, hx4]
      exact hgen P_horiz_biv
    rw [P_horiz_5, map_mul, hev, ← mul_assoc, hCmul, one_mul]
  have hRU : evalBivK5 RU_biv = (D_RU : K5) * toK5_RU := evalBivK5_RU
  have hRInf : evalBivK5 RInf_biv = (D_RInf : K5) * toK5_RInf := by
    rw [toK5_RInf, mul_div_cancel₀ _ (Int.cast_ne_zero.mpr (by unfold D_RInf; decide))]
  have hRQ5 : evalBivK5 RQ5_biv = (D_RQ5 : K5) * toK5_RQ5 := by
    rw [toK5_RQ5, mul_div_cancel₀ _ (Int.cast_ne_zero.mpr (by unfold D_RQ5; decide))]
  have hD_rels : (105 : K5) * (D_RU : K5) = (D_P : K5) ∧
      (5 : K5) * (D_RInf : K5) = (D_P : K5) ∧ (147 : K5) * (D_RQ5 : K5) = (D_P : K5) := by
    refine ⟨?_, ?_, ?_⟩
    · have hZ : (105 : ℤ) * D_RU = D_P := by unfold D_P D_RU; decide
      exact_mod_cast hZ
    · have hZ : (5 : ℤ) * D_RInf = D_P := by unfold D_P D_RInf; decide
      exact_mod_cast hZ
    · have hZ : (147 : ℤ) * D_RQ5 = D_P := by unfold D_P D_RQ5; decide
      exact_mod_cast hZ
  have hDP_ne : (D_P : K5) ≠ 0 := Int.cast_ne_zero.mpr (by unfold D_P; decide)
  have hL_ne : L_K ≠ 0 := fun h0 => fac_4_ne (by rw [fac_4_eq_neg_L, h0, neg_zero])
  rw [hL5, hP, hRU, hRInf, hRQ5] at hid
  simp only [ringEval, pow_zero, mul_one, Int.cast_ofNat] at hid
  have hfact : (D_P : K5) * (L_K ^ 2 * (toK5 P_horiz_5 + toK5_RU) + toK5_RInf + toK5_RQ5) = 0 := by
    linear_combination hid - L_K ^ 2 * toK5_RU * hD_rels.1 - toK5_RInf * hD_rels.2.1 - toK5_RQ5 * hD_rels.2.2
  have hsum0 : L_K ^ 2 * (toK5 P_horiz_5 + toK5_RU) + toK5_RInf + toK5_RQ5 = 0 :=
    (mul_eq_zero.mp hfact).resolve_left hDP_ne
  apply mul_left_cancel₀ (pow_ne_zero 2 hL_ne)
  field_simp [hL_ne]
  linear_combination hsum0

end SymmetricSexticResidual.LocalResidueQ5
