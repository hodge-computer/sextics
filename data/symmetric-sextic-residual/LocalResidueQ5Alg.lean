import Proposal.LocalResidueU0
import Proposal.Q5WeightsData
import HodgeComputer.Constructions.PolynomialEncoding.PolyOps

/-! Part 1 of `LocalResidueQ5`: `Q5`/`Q7` Euler power-sum recurrences (`sum_RQ5_power_eq_W_k`)
and regularity of `trace_AC eta_AC_reg` on `RQ5`, built on `PolynomialEncoding.KroneckerCheck` and `PolyOps`. -/

noncomputable section
namespace SymmetricSexticResidual.LocalResidueQ5
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.SheetCalculus
  SymmetricSexticResidual.CoverAlgebra SymmetricSexticResidual.CoverResidue
  SymmetricSexticResidual.LocalResidueData SymmetricSexticResidual.LocalResidueU0
  SymmetricSexticResidual.Q5WeightsData SymmetricSexticResidual.VerticalData
  SymmetricSexticResidual.VerticalIdentity
  PolynomialEncoding.KroneckerCheck QuadraticCovers
  CrossedRationalResidue Polynomial
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions PolynomialEncoding.BivariateExpressions
open PolynomialEncoding.PolyOps hiding dotW dotW_rel dotW_len
open scoped BigOperators

/-! ### Section 1: `PolyOps` / `PolBound` Centered Kronecker × Grid Engine and `Q5` Weight Traces -/

abbrev k5Ops : PolyOps K5 := ringOps K5
abbrev uOps : PolyOps Unit := unitOps
abbrev v3P3_SQ : ℕ → P3Z := v3P3_01
abbrev v3P3_SQT : ℕ → P3Z := v3P3_012

def v3K5 : Fin 3 → K5
  | 0 => S_K
  | 1 => Q_K
  | 2 => T_K

def evalP3K5 : P3Z →+* K5 :=
  MvPolynomial.eval₂Hom (Int.castRingHom K5) v3K5

lemma poly3ToK5Rel : PolyOpsRel poly3Ops k5Ops (fun p x => evalP3K5 p = x) :=
  poly3ToRingRel v3K5

abbrev dotW {α : Type*} (o : PolyOps α) (A W : UPoly α) (shift : ℕ) : UPoly α :=
  PolynomialEncoding.PolyOps.dotW o 13 5 A W shift

lemma dotW_rel {α β : Type*} {o1 : PolyOps α} {o2 : PolyOps β} {R : α → β → Prop}
    (hR : PolyOpsRel o1 o2 R) {A1 A2 W1 W2} (hA : URel R A1 A2) (hW : URel R W1 W2) (shift : ℕ) :
    URel R (dotW o1 A1 W1 shift) (dotW o2 A2 W2 shift) :=
  PolynomialEncoding.PolyOps.dotW_rel hR hA hW 13 5 shift

lemma dotW_len {α : Type*} (o : PolyOps α) (A W : UPoly α) (sh : ℕ) :
    (dotW o A W sh).length = 5 :=
  PolynomialEncoding.PolyOps.dotW_len o 13 5 A W sh

def vK5_SQ : ℕ → K5
  | 0 => S_K
  | 1 => Q_K
  | _ => 0

def evalSQ_K5 (e : Expr) : K5 := ringEval vK5_SQ e

lemma evalP3K5_ringEval_SQ (e : Expr) :
    evalP3K5 (ringEval v3P3_SQ e) = evalSQ_K5 e := by
  induction e with
  | num c => simp [evalP3K5, evalSQ_K5, ringEval]
  | natCast n => simp [evalP3K5, evalSQ_K5, ringEval]
  | intCast z => simp [evalP3K5, evalSQ_K5, ringEval]
  | var j =>
    match j with
    | 0 => simp [evalP3K5, evalSQ_K5, ringEval, v3P3_SQ, v3P3_01, v3K5, vK5_SQ]
    | 1 => simp [evalP3K5, evalSQ_K5, ringEval, v3P3_SQ, v3P3_01, v3K5, vK5_SQ]
    | _ + 2 => simp [evalP3K5, evalSQ_K5, ringEval, v3P3_SQ, v3P3_01, vK5_SQ]
  | neg a ha => simp [evalSQ_K5, ringEval] at ha ⊢; rw [ha]
  | add a b ha hb => simp [evalSQ_K5, ringEval] at ha hb ⊢; rw [ha, hb]
  | sub a b ha hb => simp [evalSQ_K5, ringEval] at ha hb ⊢; rw [ha, hb]
  | mul a b ha hb => simp [evalSQ_K5, ringEval] at ha hb ⊢; rw [ha, hb]
  | pow a k ha => simp [evalSQ_K5, ringEval] at ha ⊢; rw [ha]

-- Nonvanishing of `fac_0 .. fac_6` and `D_all_expr` in `K5` via `evLoc` mod 1009!
def vLoc_SQ : ℕ → LocK5
  | 0 => S_loc
  | 1 => Q_loc
  | _ => 0

def v1009_SQ : ℕ → ZMod 1009
  | 0 => 2
  | 1 => 3
  | _ => 0

lemma evalSQ_K5_ne_zero_of_mod1009 (e : Expr) (h : ringEval v1009_SQ e ≠ 0) :
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

lemma fac_0_ne : evalSQ_K5 fac_0 ≠ 0 := evalSQ_K5_ne_zero_of_mod1009 fac_0 (by decide)
lemma fac_1_ne : evalSQ_K5 fac_1 ≠ 0 := evalSQ_K5_ne_zero_of_mod1009 fac_1 (by decide)
lemma fac_2_ne : evalSQ_K5 fac_2 ≠ 0 := evalSQ_K5_ne_zero_of_mod1009 fac_2 (by decide)
lemma fac_3_ne : evalSQ_K5 fac_3 ≠ 0 := evalSQ_K5_ne_zero_of_mod1009 fac_3 (by decide)
lemma fac_4_ne : evalSQ_K5 fac_4 ≠ 0 := evalSQ_K5_ne_zero_of_mod1009 fac_4 (by decide)
lemma fac_5_ne : evalSQ_K5 fac_5 ≠ 0 := evalSQ_K5_ne_zero_of_mod1009 fac_5 (by decide)
lemma fac_6_ne : evalSQ_K5 fac_6 ≠ 0 := evalSQ_K5_ne_zero_of_mod1009 fac_6 (by decide)

lemma D_all_K5_ne : evalSQ_K5 D_all_expr ≠ 0 := by
  simp only [D_all_expr, evalSQ_K5, ringEval]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero fac_0_ne fac_1_ne) (pow_ne_zero 7 fac_2_ne)) (pow_ne_zero 13 fac_3_ne))
    (pow_ne_zero 2 fac_4_ne)) (pow_ne_zero 4 fac_5_ne)) fac_6_ne

lemma fac_4_eq_neg_L : evalSQ_K5 fac_4 = -L_K := by
  simp only [fac_4, evalSQ_K5, ringEval, vK5_SQ, L_K, Int.cast_neg, Int.cast_ofNat]; ring

-- Exact identification of `k5Params.Q5_z` and `k5Params.Q7_z` with `Q5WeightsData.Q5_c`, `Q7_c`!
lemma Q5_poly_eval_eq {R : Type*} [Field R] [CharZero R] (S Q U : R) :
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

lemma Q7_poly_eval_eq {R : Type*} [Field R] [CharZero R] (S Q U : R) :
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

def Q5_pol_K5 : K5[X] :=
  ∑ j : Fin 6, Polynomial.C (evalSQ_K5 (Q5_c j)) * Polynomial.X ^ j.val

def Q7_pol_K5 : K5[X] :=
  ∑ j : Fin 8, Polynomial.C (evalSQ_K5 (Q7_c j)) * Polynomial.X ^ j.val

lemma Q5_K5_eq_scaled :
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
      Polynomial.eval_C, Polynomial.eval_X]
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

lemma Q7_K5_eq_scaled :
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
      Polynomial.eval_C, Polynomial.eval_X]
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

lemma Q5_c5_eq_fac :
    evalSQ_K5 (Q5_c 5) = (lc5_const : K5) * evalSQ_K5 lc5_fac_expr := by
  simp only [Q5_c, Q5_c5, lc5_const, lc5_fac_expr, fac_3, fac_4, evalSQ_K5, ringEval, vK5_SQ,
    Int.cast_neg, Int.cast_ofNat]
  ring

lemma D_all_eq_lc5_mul :
    evalSQ_K5 D_all_expr = evalSQ_K5 lc5_fac_expr * evalSQ_K5 D_all_div_lc5_expr := by
  simp only [D_all_expr, lc5_fac_expr, D_all_div_lc5_expr, evalSQ_K5, ringEval]
  ring

-- Fast `PolyOps` evaluator for the 13 `Q5`/`Q7` recurrence & duality polynomials!
def W_num_expr (k : Fin 13) : Expr :=
  .mul (.num (N_k_mul k)) (.mul (D_quot_expr k) (N_k_expr k))

def q5Dot {α : Type*} (o : PolyOps α) (q50 q51 q52 q53 q54 q55 a0 a1 a2 a3 a4 a5 : α) : α :=
  o.add (o.add (o.add (o.mul q50 a0) (o.mul q51 a1)) (o.add (o.mul q52 a2) (o.mul q53 a3)))
        (o.add (o.mul q54 a4) (o.mul q55 a5))

lemma q5Dot_rel {α β : Type*} {o1 : PolyOps α} {o2 : PolyOps β} {R : α → β → Prop}
    (hR : PolyOpsRel o1 o2 R) {q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 : α}
    {q0' q1' q2' q3' q4' q5' a0' a1' a2' a3' a4' a5' : β}
    (hq0 : R q0 q0') (hq1 : R q1 q1') (hq2 : R q2 q2') (hq3 : R q3 q3') (hq4 : R q4 q4') (hq5 : R q5 q5')
    (ha0 : R a0 a0') (ha1 : R a1 a1') (ha2 : R a2 a2') (ha3 : R a3 a3') (ha4 : R a4 a4') (ha5 : R a5 a5') :
    R (q5Dot o1 q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5) (q5Dot o2 q0' q1' q2' q3' q4' q5' a0' a1' a2' a3' a4' a5') :=
  hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_mul hq0 ha0) (hR.rel_mul hq1 ha1))
    (hR.rel_add (hR.rel_mul hq2 ha2) (hR.rel_mul hq3 ha3)))
    (hR.rel_add (hR.rel_mul hq4 ha4) (hR.rel_mul hq5 ha5))

def q7Dot {α : Type*} (o : PolyOps α) (q70 q71 q72 q73 q74 q75 q76 q77 a0 a1 a2 a3 a4 a5 a6 a7 : α) : α :=
  o.add (o.add (o.add (o.mul q70 a0) (o.mul q71 a1)) (o.add (o.mul q72 a2) (o.mul q73 a3)))
        (o.add (o.add (o.mul q74 a4) (o.mul q75 a5)) (o.add (o.mul q76 a6) (o.mul q77 a7)))

lemma q7Dot_rel {α β : Type*} {o1 : PolyOps α} {o2 : PolyOps β} {R : α → β → Prop}
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

def q5q7RecList {α : Type*} (o : PolyOps α) (S Q : α) : List α :=
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

lemma q5q7RecList_rel {α β : Type*} {o1 : PolyOps α} {o2 : PolyOps β} {R : α → β → Prop}
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

def q5q7Lim : ℕ := Nat.pow 2 455
def q5q7B : ℤ := Int.ofNat q5q7Lim

def checkQ5Q7Bounds : Bool :=
  (q5q7RecList pbOps ⟨1, 0, 0, 1⟩ ⟨0, 1, 0, 25⟩).all fun b =>
    Nat.blt b.dQ 50 && Nat.beq b.dT 0 && Nat.blt b.M q5q7Lim

def checkQ5Q7Chunk (lo : ℤ) (n : ℕ) : Bool :=
  allRange lo n fun q =>
    (q5q7RecList intOps q5q7B q).all (fun z => z == 0)

lemma checkQ5Q7Chunk_append (lo : ℤ) (m n : ℕ) :
    checkQ5Q7Chunk lo (m + n) = (checkQ5Q7Chunk lo m && checkQ5Q7Chunk (lo + (m : ℤ)) n) :=
  allRange_append lo m n _

lemma q5q7_bounds_ok : checkQ5Q7Bounds = true := by decide +kernel
lemma q5q7_chunk_0 : checkQ5Q7Chunk (-24) 10 = true := by decide +kernel
lemma q5q7_chunk_1 : checkQ5Q7Chunk (-14) 10 = true := by decide +kernel
lemma q5q7_chunk_2 : checkQ5Q7Chunk (-4) 10 = true := by decide +kernel
lemma q5q7_chunk_3 : checkQ5Q7Chunk 6 10 = true := by decide +kernel
lemma q5q7_chunk_4 : checkQ5Q7Chunk 16 10 = true := by decide +kernel

lemma q5q7_values_ok : checkQ5Q7Chunk (-24) 50 = true := by
  rw [show (50 : ℕ) = 10 + 40 from rfl, checkQ5Q7Chunk_append, q5q7_chunk_0, Bool.true_and]
  rw [show ((-24 : ℤ) + (10 : ℕ)) = -14 from rfl, show (40 : ℕ) = 10 + 30 from rfl, checkQ5Q7Chunk_append, q5q7_chunk_1, Bool.true_and]
  rw [show ((-14 : ℤ) + (10 : ℕ)) = -4 from rfl, show (30 : ℕ) = 10 + 20 from rfl, checkQ5Q7Chunk_append, q5q7_chunk_2, Bool.true_and]
  rw [show ((-4 : ℤ) + (10 : ℕ)) = 6 from rfl, show (20 : ℕ) = 10 + 10 from rfl, checkQ5Q7Chunk_append, q5q7_chunk_3, Bool.true_and]
  exact q5q7_chunk_4

lemma q5q7RecList_poly3_zero :
    ∀ p ∈ q5q7RecList poly3Ops (MvPolynomial.X 0) (MvPolynomial.X 1), p = 0 := by
  have hb_ok : checkQ5Q7Bounds = true := q5q7_bounds_ok
  have hv_ok : checkQ5Q7Chunk (-24) 50 = true := q5q7_values_ok
  unfold checkQ5Q7Bounds at hb_ok
  unfold checkQ5Q7Chunk at hv_ok
  have hrelB := q5q7RecList_rel (respectsBoundRel 25 0) (respectsBound_X0 25 0) (respectsBound_X1 25 0)
  have hrelV : ∀ q ∈ rangeInt (-24) 50,
      List.Forall₂ (fun p z => MvPolynomial.eval (v3Int q5q7Lim q 0) p = z)
        (q5q7RecList poly3Ops (MvPolynomial.X 0) (MvPolynomial.X 1))
        (q5q7RecList intOps q5q7B q) := fun q _ =>
    q5q7RecList_rel (poly3ToIntRel q5q7Lim q 0) (by rw [MvPolynomial.eval_X, v3Int]; rfl) (by rw [MvPolynomial.eval_X, v3Int])
  have hallB : ∀ b ∈ q5q7RecList pbOps ⟨1, 0, 0, 1⟩ ⟨0, 1, 0, 25⟩, b.dQ < 50 ∧ b.dT = 0 ∧ b.M < q5q7Lim := by
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
  apply mvPoly3_eq_zero_of_kronecker_grid _ _ 25 0 q5q7Lim (rangeInt (-24) 50) {0}
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

lemma dq_pow_chain_eq (f0 f1 f2 f3 f4 f5 f6 : K5) :
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

lemma fac_K5_eqs :
    Q_K = evalSQ_K5 fac_0 ∧ S_K = evalSQ_K5 fac_1 ∧
    (-5 : K5) * S_K + 9 * Q_K = evalSQ_K5 fac_2 ∧
    -S_K + 3 * Q_K = evalSQ_K5 fac_3 ∧
    -45 + (-77 : K5) * S_K + 210 * Q_K = evalSQ_K5 fac_4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [fac_0, fac_1, fac_2, fac_3, fac_4, evalSQ_K5, ringEval, vK5_SQ, Int.cast_neg, Int.cast_ofNat]
  all_goals ring

lemma Q5_Q7_recurrences_K5 :
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
    refine letB_step (y := evalSQ_K5 fac_2) (by simpa [k5Ops, ringOps] using hf.2.2.1) ?_
    refine letB_step (y := evalSQ_K5 fac_3) (by simpa [k5Ops, ringOps] using hf.2.2.2.1) ?_
    refine letB_step (y := evalSQ_K5 fac_4) (by simpa [k5Ops, ringOps] using hf.2.2.2.2) ?_
    refine letB_step (hev_eq fac_5) ?_
    refine letB_step (hev_eq fac_6) ?_
    refine letB_step (y := evalSQ_K5 fac_2 ^ 2) (by dsimp [k5Ops, ringOps]; ring) ?_
    refine letB_step (y := evalSQ_K5 fac_2 ^ 4) (by dsimp [k5Ops, ringOps]; ring) ?_
    refine letB_step (y := evalSQ_K5 fac_2 ^ 6) (by dsimp [k5Ops, ringOps]; ring) ?_
    refine letB_step (y := evalSQ_K5 fac_2 ^ 7) (by dsimp [k5Ops, ringOps]; ring) ?_
    refine letB_step (y := evalSQ_K5 fac_3 ^ 3) (by dsimp [k5Ops, ringOps]; ring) ?_
    refine letB_step (y := evalSQ_K5 fac_3 ^ 6) (by dsimp [k5Ops, ringOps]; ring) ?_
    refine letB_step (y := evalSQ_K5 fac_3 ^ 9) (by dsimp [k5Ops, ringOps]; ring) ?_
    refine letB_step (y := evalSQ_K5 fac_3 ^ 12) (by dsimp [k5Ops, ringOps]; ring) ?_
    refine letB_step (y := evalSQ_K5 fac_3 ^ 13) (by dsimp [k5Ops, ringOps]; ring) ?_
    refine letB_step (y := evalSQ_K5 fac_4 ^ 2) (by dsimp [k5Ops, ringOps]; ring) ?_
    refine letB_step (y := evalSQ_K5 (D_quot_expr 0)) (by dsimp [k5Ops, ringOps]; rw [hD0]) ?_
    refine letB_step (y := evalSQ_K5 (D_quot_expr 1)) (by dsimp [k5Ops, ringOps]; rw [hD1, ← hf.2.1]) ?_
    refine letB_step (y := evalSQ_K5 (D_quot_expr 2)) (by dsimp [k5Ops, ringOps]; rw [hD2, ← hf.2.1]) ?_
    refine letB_step (y := evalSQ_K5 (D_quot_expr 3)) (by dsimp [k5Ops, ringOps]; rw [hD3, ← hf.2.1]) ?_
    refine letB_step (y := evalSQ_K5 (D_quot_expr 4)) (by dsimp [k5Ops, ringOps]; rw [hD4, ← hf.2.1]) ?_
    refine letB_step (y := evalSQ_K5 (D_quot_expr 8)) (by dsimp [k5Ops, ringOps]; rw [hD8, ← hf.2.1]) ?_
    refine letB_step (y := evalSQ_K5 (D_quot_expr 9)) (by dsimp [k5Ops, ringOps]; rw [hD9, ← hf.2.1]) ?_
    refine letB_step (y := evalSQ_K5 (D_quot_expr 10)) (by dsimp [k5Ops, ringOps]; rw [hD10, ← hf.2.1]) ?_
    refine letB_step (y := evalSQ_K5 (D_quot_expr 11)) (by dsimp [k5Ops, ringOps]; rw [hD11, ← hf.2.1]) ?_
    refine letB_step (y := evalSQ_K5 (D_quot_expr 12)) (by dsimp [k5Ops, ringOps]; rw [hD12, ← hf.2.1]) ?_
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
    refine letB_step (y := evalSQ_K5 D_all_div_lc5_expr) (by dsimp [k5Ops, ringOps]; rw [hDlc5, ← hf.1, ← hf.2.1]) ?_
    simp only [q5Dot, q7Dot, k5Ops, ringOps]; rfl
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
def W_K5 (k : Fin 13) : K5 :=
  evalSQ_K5 (W_num_expr k) / ((D_int_all : K5) * evalSQ_K5 D_all_expr)

-- Scaled Q5 weight for `k5Params.Q5_z`, `k5Params.Q7_z`
def W_K5_scaled (k : Fin 13) : K5 :=
  ((sc5_den * sc7_den : ℤ) : K5) / ((sc5_num * sc7_num : ℤ) : K5) * W_K5 k

lemma infinityCoefficient_apply (g : RatFunc CoverL) :
    CrossedRationalResidue.infinityCoefficient g =
      CrossedRationalResidue.residue (0 : CoverL) ((RatFunc.X ^ 2)⁻¹ * reciprocal g) := rfl

-- Euler residue trace on `X^m / Q5_pol` (`m = 0..4`) via `CrossedRationalResidue.residue_sum_eq_infinity`!
lemma sum_RQ5_euler_power (m : Fin 5) :
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
    simp only [Q5L, Q5_pol_K5, ← Polynomial.lcoeff_apply]
    simp only [Polynomial.lcoeff_apply, Fin.sum_univ_six]
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

def seqRec5 {K : Type*} [Field K] (c : Fin 6 → K) (init : Fin 5 → K) : ℕ → K
  | 0 => init 0
  | 1 => init 1
  | 2 => init 2
  | 3 => init 3
  | 4 => init 4
  | n + 5 => -(∑ j : Fin 5, c j.castSucc * seqRec5 c init (n + j.val)) / c (Fin.last 5)
termination_by n => n

-- 15-line Bézout proof identifying every `RQ5` power sum `k = 0..12` with `W_K5_scaled k`!
lemma sum_RQ5_power_eq_W_k (k : Fin 13) :
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
    simp only [Fin.val_castSucc, Fin.val_last, h5, mul_div_cancel₀ _ hlcL]
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
        simp only [Fin.val_castSucc, Fin.val_last, show m - 5 + 5 = m by omega] at hr1 hr2 hr3
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
      simp only [sc5_num, sc5_den, sc7_num, sc7_den, map_div₀, map_mul, map_ofNat,
        Int.cast_mul, Int.cast_ofNat, one_mul]
    rw [hsc, hQ5d]
    have hq7_div : Q7L.eval r = ιL_K5 1640558367 * (k5Params.Q7_z.map ιL_K5).eval r / ιL_K5 2 := by
      rw [eq_div_iff h2L, _root_.mul_comm, hQ7e]
    rw [hq7_div]
    field_simp [hq5d_ne, hq7e_ne, h2L, h5L, h7L]
  rw [hscale, hTk_eq, ← map_mul, W_K5_scaled]

/-! ### Section 2: 12-Variable `Q23` Split and Regularity of `eta_AC_reg` on `RQ5` -/

def Q23_of {R : Type*} [CommRing R] (q2 q1 q0 e3 e2 e1 e0 p4 p3 p2 p1 p0 : R) : R :=
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

lemma Q5_rem_split {R : Type*} [CommRing R] (q2 q1 q0 e3 e2 e1 e0 p4 p3 p2 p1 p0 : R) :
    e3 * (remDeg4_P1 q2 q1 q0 p4 p3 p2 p1 * remDeg3_d0 q2 q1 q0 e3 e2 e0 -
          remDeg4_P0 q2 q1 q0 p4 p3 p2 p0 * remDeg3_d1 q2 q1 q0 e3 e2 e1) =
    q2 ^ 2 * p4 * syl5 q2 q1 q0 e3 e2 e1 e0 +
    q2 ^ 3 * Q23_of q2 q1 q0 e3 e2 e1 e0 p4 p3 p2 p1 p0 := by
  simp only [remDeg4_P1, remDeg4_P0, remDeg3_d1, remDeg3_d0, syl5, Q23_of]
  ring

def p4_AC : A_C := (interp4 P18_z_AC).1

def Q23_AC : A_C :=
  let p := interp4 P18_z_AC
  Q23_of (pairC k5Params.d2_2) (pairC k5Params.d2_1) (pairC k5Params.d2_0)
    (pairC k5Params.d3_3) (pairC k5Params.d3_2) (pairC k5Params.d3_1) (pairC k5Params.d3_0)
    p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2

def eta_AC_main : A_C :=
  -(p4_AC * U_C ^ 3 * W_C * polyC k5Params.cb_h ^ 4) /
    (81 * ιC_K5 k5Params.Av0 * (2 * W_C + polyC k5Params.bW) *
      polyC k5Params.Q7_z * polyC k5Params.Q5_z)

def eta_AC_reg : A_C :=
  -(Q23_AC * U_C ^ 3 * W_C * polyC k5Params.cb_h ^ 4) /
    (81 * ιC_K5 k5Params.Av0 * (2 * W_C + polyC k5Params.bW) *
      polyC k5Params.Q7_z * pairC k5Params.res_z)

lemma Q7_K5_ne_zero : k5Params.Q7_z ≠ 0 := by
  intro h0
  obtain ⟨u, v, huv⟩ := isCoprime_Q5_Q7
  rw [h0, mul_zero, add_zero] at huv
  have hdeg := congrArg Polynomial.natDegree huv
  rw [Polynomial.natDegree_one] at hdeg
  have hu : u ≠ 0 := fun hu0 => by simp [hu0] at huv
  rw [Polynomial.natDegree_mul hu Q5_K5_ne_zero, Q5_K5_natDegree] at hdeg
  omega

lemma eta_AC_eq_main_add_reg : eta_AC = eta_AC_main + eta_AC_reg := by
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

lemma mapRatFunc_toRat (P : K5[X]) :
    mapRatFunc ιL_K5 (toRat P) = algebraMap CoverL[X] (RatFunc CoverL) (P.map ιL_K5) :=
  mapRatFunc_algebraMap ιL_K5 P

-- Regularity of `trace_AC eta_AC_reg` at every `r ∈ RQ5`!
structure RegQ5 (r : CoverL) (x : A_C) : Prop where
  c0 : RegularAt r (mapRatFunc ιL_K5 (coordsAC x).c0)
  c1 : RegularAt r (mapRatFunc ιL_K5 (coordsAC x).c1)

lemma regQ5_evalAC {r : CoverL} {p : PairAlg (RatFunc K5)}
    (h0 : RegularAt r (mapRatFunc ιL_K5 p.c0)) (h1 : RegularAt r (mapRatFunc ιL_K5 p.c1)) :
    RegQ5 r (evalAC p) :=
  ⟨by rwa [coordsAC_evalAC], by rwa [coordsAC_evalAC]⟩

lemma regQ5_zero (r : CoverL) : RegQ5 r 0 := by
  rw [show (0 : A_C) = evalAC ⟨0, 0⟩ by simp [evalAC]]
  exact regQ5_evalAC (by simp [regAt_zero]) (by simp [regAt_zero])

lemma regQ5_one (r : CoverL) : RegQ5 r 1 := by
  rw [show (1 : A_C) = evalAC ⟨1, 0⟩ by simp [evalAC]]
  exact regQ5_evalAC (by simp [regAt_one]) (by simp [regAt_zero])

lemma regQ5_ofNat (r : CoverL) (n : ℕ) [n.AtLeastTwo] : RegQ5 r (no_index (OfNat.ofNat n)) := by
  have h1 : (OfNat.ofNat n : A_C) = evalAC ⟨(n : RatFunc K5), 0⟩ := by
    simp [evalAC, show (OfNat.ofNat n : A_C) = (n : A_C) from rfl]
  rw [h1]
  exact regQ5_evalAC (by rw [map_natCast]; exact ⟨Polynomial.C (n : CoverL), 1, by simp, by simp⟩) (by simp [regAt_zero])

lemma regQ5_ιC_K5 (r : CoverL) (c : K5) : RegQ5 r (ιC_K5 c) := by
  rw [show ιC_K5 c = evalAC ⟨RatFunc.C c, 0⟩ by simp [evalAC, ιC_K5]]
  exact regQ5_evalAC (by simp [mapRatFunc_C, regAt_C]) (by simp [regAt_zero])

lemma regQ5_polyC (r : CoverL) (P : K5[X]) : RegQ5 r (polyC P) := by
  rw [show polyC P = evalAC ⟨toRat P, 0⟩ by simp [evalAC, polyC]]
  exact regQ5_evalAC (by rw [mapRatFunc_toRat]; exact ⟨P.map ιL_K5, 1, by simp, by simp⟩) (by simp [regAt_zero])

lemma regQ5_pairC (r : CoverL) (p : PairAlg K5[X]) : RegQ5 r (pairC p) := by
  rw [pairC]
  exact regQ5_evalAC
    (by simp only [PairAlg.map, mapRatFunc_toRat]; exact ⟨p.c0.map ιL_K5, 1, by simp, by simp⟩)
    (by simp only [PairAlg.map, mapRatFunc_toRat]; exact ⟨p.c1.map ιL_K5, 1, by simp, by simp⟩)

lemma regQ5_U_C (r : CoverL) : RegQ5 r U_C := by
  simpa [polyC, U_C, toRat] using regQ5_polyC r Polynomial.X

lemma regQ5_W_C (r : CoverL) : RegQ5 r W_C := by
  rw [← evalAC_W]
  exact regQ5_evalAC (by simp [PairAlg.W, regAt_zero]) (by simp [PairAlg.W, regAt_one])

lemma regQ5_add {r : CoverL} {x y : A_C} (hx : RegQ5 r x) (hy : RegQ5 r y) : RegQ5 r (x + y) := by
  rw [← evalAC_coordsAC x, ← evalAC_coordsAC y, ← evalAC_add]
  exact regQ5_evalAC
    (by simp only [PairAlg.add, map_add]; exact hx.1.add hy.1)
    (by simp only [PairAlg.add, map_add]; exact hx.2.add hy.2)

lemma regQ5_neg {r : CoverL} {x : A_C} (hx : RegQ5 r x) : RegQ5 r (-x) := by
  rw [← evalAC_coordsAC x, ← evalAC_neg]
  exact regQ5_evalAC (by simp only [PairAlg.neg, map_neg]; exact regAt_neg_local hx.1)
    (by simp only [PairAlg.neg, map_neg]; exact regAt_neg_local hx.2)

lemma regQ5_sub {r : CoverL} {x y : A_C} (hx : RegQ5 r x) (hy : RegQ5 r y) : RegQ5 r (x - y) := by
  rw [sub_eq_add_neg]; exact regQ5_add hx (regQ5_neg hy)

lemma regQ5_mul {r : CoverL} {x y : A_C} (hx : RegQ5 r x) (hy : RegQ5 r y) : RegQ5 r (x * y) := by
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

lemma regQ5_pow {r : CoverL} {x : A_C} (hx : RegQ5 r x) (n : ℕ) : RegQ5 r (x ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact regQ5_one r
  | succ k ih => rw [pow_succ]; exact regQ5_mul ih hx

lemma regQ5_div_polyC {r : CoverL} {x : A_C} {P : K5[X]} (hx : RegQ5 r x)
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

lemma regQ5_div_pairC {r : CoverL} {x : A_C} {y : PairAlg K5[X]} (hx : RegQ5 r x)
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

lemma regQ5_div_nat {r : CoverL} {x : A_C} (hx : RegQ5 r x) (n : ℕ) [hn : n.AtLeastTwo] :
    RegQ5 r (x / no_index (OfNat.ofNat n)) := by
  have heq : (OfNat.ofNat n : A_C) = polyC (Polynomial.C (n : K5)) := by
    simp [polyC, toRat, show (OfNat.ofNat n : A_C) = (n : A_C) from rfl]
  rw [heq]
  apply regQ5_div_polyC hx
  simp only [Polynomial.map_natCast, Polynomial.eval_natCast, map_natCast]
  exact (Nat.cast_ne_zero (R := CoverL)).mpr (NeZero.ne n)

lemma regularAt_trace_eta_AC_reg (r : CoverL) (hr : r ∈ RQ5) :
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
      repeat' (with_reducible first | apply regQ5_div_nat | apply regQ5_add | apply regQ5_sub | apply regQ5_neg | apply regQ5_mul | apply regQ5_pow | exact hs | exact hq | exact hU_reg | exact hV_reg | exact regQ5_ofNat r _)
    have hdHQ (s q v0 : A_C) (hs : RegQ5 r s) (hq : RegQ5 r q) (hv0 : RegQ5 r v0) : RegQ5 r (dH_dQ s q v0 U_C V_C) := by
      dsimp only [dH_dQ]
      repeat' (with_reducible first | apply regQ5_div_nat | apply regQ5_add | apply regQ5_sub | apply regQ5_neg | apply regQ5_mul | apply regQ5_pow | exact hs | exact hq | exact hv0 | exact hU_reg | exact hV_reg | exact regQ5_ofNat r _)
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
        repeat' (with_reducible first | exact hd10 | exact hd20 | exact hd21 | exact hξS | exact hξQ | apply regQ5_div_nat | apply regQ5_add | apply regQ5_sub | apply regQ5_mul | apply regQ5_pow | exact ha | exact hb | exact regQ5_zero r | exact regQ5_one r | exact regQ5_ofNat r _)
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
        repeat' (with_reducible first | apply regQ5_div_nat | apply regQ5_add | apply regQ5_neg | apply regQ5_mul | exact hv_r | exact hV_reg | exact regQ5_zero r | exact regQ5_ofNat r _)
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

lemma residue_eta_L_eq_main (r : CoverL) (hr : r ∈ RQ5) :
    CrossedRationalResidue.residue r eta_L =
      CrossedRationalResidue.residue r (mapRatFunc ιL_K5 (Algebra.trace (RatFunc K5) A_C eta_AC_main)) := by
  simp only [CoverResidue.eta_L, CoverResidue.eta, eta_AC_eq_main_add_reg, map_add]
  rw [(regularAt_trace_eta_AC_reg r hr).residue_eq_zero, add_zero]



end SymmetricSexticResidual.LocalResidueQ5
