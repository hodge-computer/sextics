import Proposal.LocalResidueQ5Alg

/-! Part 2 of `LocalResidueQ5`: `ACache`/`GeomSQ`/`SQCache`/`GeomT` definitions and `PolyOpsRel` lifts. -/

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

/-! ### Section 3: Generic `UPoly` / `BivL` / `UBivL` Algebra, Shift-Invariant `p4_AC`, and Trace Reduction -/

abbrev evalUPolyK5 : UPoly K5 → K5[X] := evalUPoly
abbrev evalYListK5 : UPoly K5 → K5 := evalYList y_K
abbrev evalBivLK5 : BivL K5 → K5 := evalBivL x_K y_K
abbrev evalUBivLK5 : UBivL K5 → K5[X] := evalUBivL x_K y_K

lemma evalUPolyK5_uAdd (a b : UPoly K5) :
    evalUPolyK5 (uAdd k5Ops a b) = evalUPolyK5 a + evalUPolyK5 b := evalUPoly_uAdd a b
lemma evalUPolyK5_uNeg (a : UPoly K5) :
    evalUPolyK5 (uNeg k5Ops a) = -evalUPolyK5 a := evalUPoly_uNeg a
lemma evalUPolyK5_uSub (a b : UPoly K5) :
    evalUPolyK5 (uSub k5Ops a b) = evalUPolyK5 a - evalUPolyK5 b := evalUPoly_uSub a b
lemma evalUPolyK5_uSc (c : K5) (a : UPoly K5) :
    evalUPolyK5 (uSc k5Ops c a) = Polynomial.C c * evalUPolyK5 a := evalUPoly_uSc c a
lemma evalUPolyK5_uShift (a : UPoly K5) :
    evalUPolyK5 (uShift k5Ops a) = Polynomial.X * evalUPolyK5 a := evalUPoly_uShift a
lemma evalUPolyK5_uMul (a b : UPoly K5) :
    evalUPolyK5 (uMul k5Ops a b) = evalUPolyK5 a * evalUPolyK5 b := evalUPoly_uMul a b
lemma evalUPolyK5_uTail (a : UPoly K5) :
    evalUPolyK5 a = Polynomial.C (a.headD 0) + Polynomial.X * evalUPolyK5 (uTail a) := evalUPoly_uTail a
lemma evalUPolyK5_coeff (a : UPoly K5) (k : ℕ) :
    (evalUPolyK5 a).coeff k = a.getD k 0 := evalUPoly_coeff a k
lemma evalUPolyK5_natDegree_le (a : UPoly K5) (k : ℕ) (hk : a.length ≤ k) :
    (evalUPolyK5 a).coeff k = 0 := evalUPoly_coeff_eq_zero_of_le a hk
lemma evalBivLK5_bivAdd (a b : BivL K5) :
    evalBivLK5 (bivAdd k5Ops a b) = evalBivLK5 a + evalBivLK5 b := evalBivL_bivAdd x_K y_K a b
lemma evalBivLK5_bivNeg (a : BivL K5) :
    evalBivLK5 (bivNeg k5Ops a) = -evalBivLK5 a := evalBivL_bivNeg x_K y_K a
lemma evalBivLK5_bivSub (a b : BivL K5) :
    evalBivLK5 (bivSub k5Ops a b) = evalBivLK5 a - evalBivLK5 b := evalBivL_bivSub x_K y_K a b
lemma evalBivLK5_bivSc (c : K5) (a : BivL K5) :
    evalBivLK5 (bivSc k5Ops c a) = c * evalBivLK5 a := evalBivL_bivSc x_K y_K c a
lemma evalBivLK5_bivMul (a b : BivL K5) :
    evalBivLK5 (bivMul k5Ops a b) = evalBivLK5 a * evalBivLK5 b := evalBivL_bivMul x_K y_K a b
lemma evalUBivLK5_ubAdd (a b : UBivL K5) :
    evalUBivLK5 (ubAdd k5Ops a b) = evalUBivLK5 a + evalUBivLK5 b := evalUBivL_ubAdd x_K y_K a b
lemma evalUBivLK5_ubNeg (a : UBivL K5) :
    evalUBivLK5 (ubNeg k5Ops a) = -evalUBivLK5 a := evalUBivL_ubNeg x_K y_K a
lemma evalUBivLK5_ubSub (a b : UBivL K5) :
    evalUBivLK5 (ubSub k5Ops a b) = evalUBivLK5 a - evalUBivLK5 b := evalUBivL_ubSub x_K y_K a b
lemma evalUBivLK5_ubSc (c : K5) (a : UBivL K5) :
    evalUBivLK5 (ubSc k5Ops c a) = Polynomial.C c * evalUBivLK5 a := evalUBivL_ubSc x_K y_K c a
lemma evalUBivLK5_ubBmul (b : BivL K5) (a : UBivL K5) :
    evalUBivLK5 (ubBmul k5Ops b a) = Polynomial.C (evalBivLK5 b) * evalUBivLK5 a := evalUBivL_ubBmul x_K y_K b a
lemma evalUBivLK5_ubShift (a : UBivL K5) :
    evalUBivLK5 (ubShift a) = Polynomial.X * evalUBivLK5 a := evalUBivL_ubShift x_K y_K a
lemma evalUBivLK5_ubMulU (u : UPoly K5) (a : UBivL K5) :
    evalUBivLK5 (ubMulU k5Ops u a) = evalUPolyK5 u * evalUBivLK5 a := evalUBivL_ubMulU x_K y_K u a
lemma evalUBivLK5_ubSynDiv1Rem (a : UBivL K5) :
    evalUBivLK5 a = Polynomial.C (evalBivLK5 (ubSynDiv1Rem k5Ops a).1) +
      (Polynomial.X - 1) * evalUBivLK5 (ubSynDiv1Rem k5Ops a).2 := evalUBivL_ubSynDiv1Rem x_K y_K a
lemma evalUBivLK5_coeff (a : UBivL K5) (k : ℕ) :
    (evalUBivLK5 a).coeff k = evalBivLK5 (a.getD k []) := evalUBivL_coeff x_K y_K a k
lemma evalBivLK5_combineBivDot_uAdd (B : UBivL K5) (c1 c2 : UPoly K5) :
    evalBivLK5 (combineBivDot k5Ops B (uAdd k5Ops c1 c2)) =
      evalBivLK5 (combineBivDot k5Ops B c1) + evalBivLK5 (combineBivDot k5Ops B c2) :=
  evalBivL_combineBivDot_uAdd x_K y_K B c1 c2
lemma evalBivLK5_combineBivDot_uSc (s : K5) (B : UBivL K5) (c : UPoly K5) :
    evalBivLK5 (combineBivDot k5Ops B (uSc k5Ops s c)) =
      s * evalBivLK5 (combineBivDot k5Ops B c) :=
  evalBivL_combineBivDot_uSc x_K y_K s B c

lemma F5_of_K5_zero : F5_of S_K Q_K T_K x_K y_K = 0 := by
  have h := F5_of_L (L := K5)
  simpa only [F5_of, H0_of, SL, QL, TL, xL, yL, ιL, Algebra.algebraMap_self, RingHom.id_apply] using h

lemma evalBivLK5_bivRedOnce (b : BivL K5) :
    evalBivLK5 (bivRedOnce k5Ops (21 * S_K) (-(21 * T_K)) (-(7 * H0_of S_K Q_K T_K)) b) =
      (21 * S_K) * evalBivLK5 b := by
  have hx2 : 21 * S_K * x_K ^ 2 = -(21 * T_K) * y_K ^ 2 + -(7 * H0_of S_K Q_K T_K) := by
    have hF := F5_of_K5_zero; unfold F5_of at hF; linear_combination 7 * hF
  exact evalBivL_bivRedOnce hx2 b

lemma evalBivLK5_combineBivDot_dotW (A : UPoly K5) (B : UBivL K5) (W : UPoly K5) (shift : ℕ)
    (hBlen : B.length ≤ 5) (hdeg : A.length + B.length + shift ≤ 15) :
    evalBivLK5 (combineBivDot k5Ops B (dotW k5Ops A W shift)) =
      ∑ k : Fin 13, ((Polynomial.X ^ shift * evalUPolyK5 A * evalUBivLK5 B).coeff (k.val + 1)) * W.getD k.val 0 :=
  evalBivL_combineBivDot_dotW x_K y_K 13 5 A B W shift hBlen hdeg

abbrev uEval_uAdd_P3Z := @uEval_uAdd P3Z _
abbrev uEval_uNeg_P3Z := @uEval_uNeg P3Z _
abbrev uEval_uSub_P3Z := @uEval_uSub P3Z _
abbrev uEval_uSc_P3Z := @uEval_uSc P3Z _
abbrev uEval_uShift_P3Z := @uEval_uShift P3Z _
abbrev uEval_uMul_P3Z := @uEval_uMul P3Z _
abbrev uEval_uMonomial_P3Z := @uEval_uMonomial P3Z _
abbrev uEval_uPow_P3Z := @uEval_uPow P3Z _

lemma evalP3K5_ringEval_SQT (e : Expr) :
    evalP3K5 (ringEval v3P3_SQT e) = ringEval vK5 e := by
  induction e with
  | num c => simp [evalP3K5, ringEval]
  | natCast n => simp [evalP3K5, ringEval]
  | intCast z => simp [evalP3K5, ringEval]
  | var j =>
      match j with
      | 0 => simp [evalP3K5, ringEval, v3P3_SQT, v3P3_012, v3K5, vK5]
      | 1 => simp [evalP3K5, ringEval, v3P3_SQT, v3P3_012, v3K5, vK5]
      | 2 => simp [evalP3K5, ringEval, v3P3_SQT, v3P3_012, v3K5, vK5]
      | _ + 3 => simp [evalP3K5, ringEval, v3P3_SQT, v3P3_012, vK5]
  | neg a ha => simp [ringEval] at ha ⊢; rw [ha]
  | add a b ha hb => simp [ringEval] at ha hb ⊢; rw [ha, hb]
  | sub a b ha hb => simp [ringEval] at ha hb ⊢; rw [ha, hb]
  | mul a b ha hb => simp [ringEval] at ha hb ⊢; rw [ha, hb]
  | pow a k ha => simp [ringEval] at ha ⊢; rw [ha]

-- Shift-invariant `numM_lead3` and degree-3 expansion of `numM` along `(a1 * z, b1 * z + b0)`
section NumMLead3
variable {R : Type*} [Field R] [CharZero R]

def numM_lead3 (mi : Fin 10) (S Q T a1 b1 U V : R) : R :=
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

lemma numM_isPoly3_core (mi : Fin 10) (S Q T a1 b1 b0 A2 A2_1 A2_0 A1 A1_0 A0 B2 B2_1 B2_0 B1 B1_0 B0 : R) :
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

lemma numM_isPoly3 (mi : Fin 10) (S Q T a1 b1 b0 U V : R) :
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

lemma numM_lead3_scale (mi : Fin 10) (S Q T a1 b1 U V lam : R) :
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
def L_all_A : ℤ := 235267436250
def M_A_int : ℤ := L_all_A * 16 * 45927 * 567 ^ 4
def M_mid_int : ℤ := 2250423
def M_R_int : ℤ := M_A_int * 1701 * M_mid_int
def C_RHS_int : ℤ := -5438812994401448072650932000000000000000

structure ACache (α : Type*) where
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

def evalACache {α : Type*} (o : PolyOps α) (S Q : α) : ACache α :=
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

structure GeomSQ (α : Type*) where
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

def evalGeomSQ {α : Type*} (o : PolyOps α) (S Q : α) : GeomSQ α :=
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

structure SQCache (α : Type*) where
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

def evalSQCache {α : Type*} (o : PolyOps α) (S Q : α) : SQCache α :=
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

structure GeomT (α : Type*) where
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

def evalGeomT {α : Type*} (o : PolyOps α) (S : α) (ca_p cb_p : UPoly α) (gsq : GeomSQ α) (T : α) : GeomT α :=
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

def evalBTot {α : Type*} (o : PolyOps α) (cache : SQCache α) (gt : GeomT α) (T : α) : BivL α :=
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

def evalTStep {α : Type*} (o : PolyOps α) (S : α) (cache : SQCache α) (T : α) : BivL α :=
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

structure ACacheRel (R : α → β → Prop) (a : ACache α) (b : ACache β) : Prop where
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

structure GeomSQRel (R : α → β → Prop) (a : GeomSQ α) (b : GeomSQ β) : Prop where
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

structure SQCacheRel (R : α → β → Prop) (a : SQCache α) (b : SQCache β) : Prop where
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

structure GeomTRel (R : α → β → Prop) (a : GeomT α) (b : GeomT β) : Prop where
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

lemma evalACache_rel (hR : PolyOpsRel o1 o2 R) {S1 Q1 : α} {S2 Q2 : β}
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

lemma evalGeomSQ_rel (hR : PolyOpsRel o1 o2 R) {S1 Q1 : α} {S2 Q2 : β}
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

lemma evalSQCache_rel (hR : PolyOpsRel o1 o2 R) {S1 Q1 : α} {S2 Q2 : β}
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

lemma evalGeomT_rel (hR : PolyOpsRel o1 o2 R) {S1 T1 : α} {S2 T2 : β}
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

lemma evalBTot_rel (hR : PolyOpsRel o1 o2 R) {c1 : SQCache α} {c2 : SQCache β}
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

lemma evalTStep_rel (hR : PolyOpsRel o1 o2 R) {S1 T1 : α} {S2 T2 : β}
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


end SymmetricSexticResidual.LocalResidueQ5
