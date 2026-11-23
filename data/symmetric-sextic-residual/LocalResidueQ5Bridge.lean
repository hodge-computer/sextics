import Proposal.LocalResidueQ5Poly

/-! Part 3 of `LocalResidueQ5`: `K5` polynomial identities and `evalACache_AC_bridge`. -/

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

def cacheK : SQCache K5 := evalSQCache k5Ops S_K Q_K
def gtK : GeomT K5 := evalGeomT k5Ops S_K cacheK.ac.ca_p cacheK.ac.cb_p cacheK.gsq T_K

lemma polyC_C (c : K5) : polyC (Polynomial.C c) = ιC_K5 c := by
  simp [polyC, ιC_K5, toRat]

lemma polyC_X : polyC (Polynomial.X : K5[X]) = U_C := by
  simp [polyC, U_C, toRat]

lemma polyC_add (p q : K5[X]) : polyC (p + q) = polyC p + polyC q := by
  simp [polyC]

lemma polyC_sub (p q : K5[X]) : polyC (p - q) = polyC p - polyC q := by
  simp [polyC]

lemma polyC_neg (p : K5[X]) : polyC (-p) = -polyC p := by
  simp [polyC]

lemma polyC_mul (p q : K5[X]) : polyC (p * q) = polyC p * polyC q := by
  simp [polyC]

lemma polyC_pow (p : K5[X]) (n : ℕ) : polyC (p ^ n) = polyC p ^ n := by
  simp [polyC]

-- Pure-ring identities for `dHS_243`, `dHQ0_27`, `dHS_bi_243`, `dHQ1_bi_189`
section PureRingBridge
variable {R : Type*} [Field R] [CharZero R]

lemma dHS_243_ring (a b U : R) :
    -25 * ((5 * a - 9 * b) * (15 * a - 9 * b)) +
    U * (429 * (a * a) - 1656 * (a * b) + 1404 * (b * b)) +
    U * (U * (-12 * ((a - 3 * b) * (a - 3 * b)))) = 243 * q1_a2 a b U 1 := by
  simp only [q1_a2, dH_dS]; ring

lemma dHQ0_27_ring (a b U : R) :
    50 * (a * (5 * a - 9 * b)) +
    U * (-92 * (a * a) + 312 * (a * b) - 198 * (b * b)) +
    U * (U * (4 * ((a - 3 * b) * (a - 3 * b)))) = 27 * q2_b2 a b U 1 := by
  simp only [q2_b2, dH_dQ]; ring

lemma dHS_bi_243_ring (S Q a b U : R) :
    -25 * ((15 * S - 9 * Q) * (5 * a - 9 * b) + (5 * S - 9 * Q) * (15 * a - 9 * b)) +
    U * (858 * S * a - 1656 * (S * b + Q * a) + 2808 * Q * b) +
    U * (U * (-24 * (S - 3 * Q) * (a - 3 * b))) = 243 * q1_a1 a b S Q U 1 := by
  simp only [q1_a1, dH_dS]; ring

lemma dHQ1_bi_189_ring (S Q a b U : R) :
    350 * ((10 * S - 9 * Q) * a - 9 * S * b) +
    U * (7 * (-184 * S * a + 312 * (S * b + Q * a) - 396 * Q * b) + 270 * b) +
    U * (U * (56 * (S - 3 * Q) * (a - 3 * b))) = 189 * q2_b1 a b S Q U 1 := by
  simp only [q2_b1, dH_dQ]; ring

lemma B1_of_eq_Av0_Cv0 (T U V : R) :
    B1_of T U V = 9 * U * ((-(4 / 243 : R) * (T - 3) ^ 3) * V - (-(25 / 243 : R) * T * (5 * T - 9) ^ 2)) := by
  simp only [B1_of]; ring

lemma E0_V_split (S Q T U V : R) :
    H_cub S Q T 1 U V =
      V * (U * H0_of S Q T + u_of U * A1_of S Q U 1) +
      (V - 1) * U * ((-(4 / 243 : R) * (T - 3) ^ 3) * V - (-(25 / 243 : R) * T * (5 * T - 9) ^ 2)) := by
  have h1 := H_cub_eq_H0_A1_B1 S Q T U V
  have hA : A1_of S Q U V = V * A1_of S Q U 1 := by simp only [A1_of]; ring
  rw [h1, hA, B1_of_eq_Av0_Cv0, v_of]
  ring

lemma cA1_dot_V1_ring (S Q T U : R) :
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

lemma QY_dot_V1_ring (S Q T x y U : R) :
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
    intro k; fin_cases k <;> simp [dLY_fn, v_of]
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
      mul_zero, zero_mul, zero_add, sub_zero]
    linear_combination y ^ 2 * hy2 + hy0
  simp only [QY_num]
  linear_combination DY2_of T y * hinner

lemma QX_dot_U1_ring (S Q T x y V : R) :
    let ca := q1_a0 S Q 1 1; let cb := q2_b0 S Q 1 1
    QX_num S Q T x y 1 V 0 * cb - QX_num S Q T x y 1 V 1 * ca = 0 := by
  intro ca cb
  have hca : ca = dH0_fn 0 S Q T := by simp only [ca, q1_a0, dH_dS, dH0_fn]; ring
  have hcb : cb = dH0_fn 1 S Q T := by simp only [cb, q2_b0, dH_dQ, dH0_fn]; ring
  have hLX1 : LX_of S Q x 1 = x := by simp only [LX_of, u3_of, u_of]; ring
  have hdLX1 : ∀ k : Fin 5, dLX_fn k (1 : R) = match k with | 3 => 1 | _ => 0 := by
    intro k; fin_cases k <;> simp [dLX_fn, u_of]; ring
  rw [hca, hcb]
  simp only [QX_num, Omega_F, dDY2_F, F_contract, om_fn, br_fn, dF5_fn, dDY2_fn, dLY_fn, hLX1, hdLX1
    ]
  ring

lemma QY_QX_U0V0_ring (S Q T x y : R) :
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
    simp only [QY_num, hom0, hom1, dDX2_F, F_contract, hbr3, hbr4, hd4]
    linear_combination DY2_of T y * S * T * dF5_fn 4 S Q T x y * dDX2_fn 3 S Q x * hbr0
  · have hd3 : dDY2_fn 3 T y = 0 := rfl
    simp only [QX_num, hom0, hom1, dDY2_F, F_contract, hbr3, hbr4, hd3]
    linear_combination DX2_of S Q x * S * T * dF5_fn 3 S Q T x y * dDY2_fn 4 T y * hbr0
  · simp [EB_of, hbr3, hbr4]

end PureRingBridge

-- Fast O(N) `letB_intro` structural decomposition of `cacheK` (`evalSQCache k5Ops S_K Q_K`)
lemma cacheK_props :
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
  have hf2' : f2 = evalSQ_K5 fac_2 := by rw [hf2]; dsimp only [k5Ops, ringOps]; rw [← hf.2.2.1]; push_cast; ring
  have hf3' : f3 = evalSQ_K5 fac_3 := by rw [hf3]; dsimp only [k5Ops, ringOps]; rw [← hf.2.2.2.1]; push_cast; ring
  have hf4' : f4 = evalSQ_K5 fac_4 := by rw [hf4]; dsimp only [k5Ops, ringOps]; rw [← hf.2.2.2.2]; push_cast; ring
  have hf2_2' : f2_2 = evalSQ_K5 fac_2 ^ 2 := by rw [hf2_2, hf2']; dsimp only [k5Ops, ringOps]; ring
  have hf2_4' : f2_4 = evalSQ_K5 fac_2 ^ 4 := by rw [hf2_4, hf2_2']; dsimp only [k5Ops, ringOps]; ring
  have hf2_6' : f2_6 = evalSQ_K5 fac_2 ^ 6 := by rw [hf2_6, hf2_4', hf2_2']; dsimp only [k5Ops, ringOps]; ring
  have hf2_7' : f2_7 = evalSQ_K5 fac_2 ^ 7 := by rw [hf2_7, hf2_6', hf2']; dsimp only [k5Ops, ringOps]; ring
  have hf3_3' : f3_3 = evalSQ_K5 fac_3 ^ 3 := by rw [hf3_3, hf3']; dsimp only [k5Ops, ringOps]; ring
  have hf3_6' : f3_6 = evalSQ_K5 fac_3 ^ 6 := by rw [hf3_6, hf3_3']; dsimp only [k5Ops, ringOps]; ring
  have hf3_9' : f3_9 = evalSQ_K5 fac_3 ^ 9 := by rw [hf3_9, hf3_6', hf3_3']; dsimp only [k5Ops, ringOps]; ring
  have hf3_12' : f3_12 = evalSQ_K5 fac_3 ^ 12 := by rw [hf3_12, hf3_9', hf3_3']; dsimp only [k5Ops, ringOps]; ring
  have hf3_13' : f3_13 = evalSQ_K5 fac_3 ^ 13 := by rw [hf3_13, hf3_12', hf3']; dsimp only [k5Ops, ringOps]; ring
  have hf4_2' : f4_2 = evalSQ_K5 fac_4 ^ 2 := by rw [hf4_2, hf4']; dsimp only [k5Ops, ringOps]; ring
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
    rw [hDall, hL2, hDdiv, hev2, hev2, hf2_7', hf3_13', hS1, hQ0]; dsimp only [k5Ops, ringOps]; ring
  · simp only [List.map_cons, List.map_nil, hevT, evalBivLK5, evalBivL, evalYList, evalBivK5, RQ5_biv, denote]; ring

lemma polyC_zero : polyC 0 = 0 := by simp only [polyC, toRat, map_zero]
lemma polyC_one : polyC 1 = 1 := by simp only [polyC, toRat, map_one]
lemma polyC_ofNat (n : ℕ) [n.AtLeastTwo] : polyC (no_index (OfNat.ofNat n)) = OfNat.ofNat n := by
  simp only [polyC, toRat, map_ofNat]

lemma polyC_ca_cb_eq_q10_q20 :
    polyC k5Params.ca_h = q1_a0 (ιC_K5 S_K) (ιC_K5 Q_K) U_C 1 ∧
    polyC k5Params.cb_h = q2_b0 (ιC_K5 S_K) (ιC_K5 Q_K) U_C 1 := by
  constructor <;> (
    simp only [CoverParams.ca_h, CoverParams.cb_h, CoverParams.quadU,
      CoverParams.inv9, CoverParams.inv27, CoverParams.inv81,
      k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q,
      polyC_add, polyC_sub, polyC_neg, polyC_mul, polyC_pow, polyC_C, polyC_X, polyC_ofNat, 
      map_add, map_sub, map_mul, map_inv₀, map_neg, map_pow, map_ofNat,
      q1_a0, q2_b0, dH_dS, dH_dQ]; ring)

def A0U_U_p : K5[X] :=
  evalUPolyK5 (uTail cacheK.ac.A0U_t0) + Polynomial.C T_K * evalUPolyK5 (uTail cacheK.ac.A0U_t1)

def A0V_p : K5[X] :=
  evalUPolyK5 cacheK.ac.A0V_t0 + Polynomial.C T_K * evalUPolyK5 cacheK.ac.A0V_t1 +
    Polynomial.C (T_K ^ 2) * evalUPolyK5 cacheK.ac.A0V_t2

def AY2_p : K5[X] :=
  evalUPolyK5 cacheK.ac.AY2_t0 + Polynomial.C T_K * evalUPolyK5 cacheK.ac.AY2_t1

def AY3_p : K5[X] :=
  evalUPolyK5 cacheK.ac.AY3_t0 + Polynomial.C T_K * evalUPolyK5 cacheK.ac.AY3_t1

def AX2_p : K5[X] :=
  evalUPolyK5 cacheK.ac.AX2_t0 + Polynomial.C T_K * evalUPolyK5 cacheK.ac.AX2_t1 +
    Polynomial.C (T_K ^ 2) * evalUPolyK5 cacheK.ac.AX2_t2

def Bv_1701_p : K5[X] :=
  evalUPolyK5 cacheK.ac.Bv_SQ + Polynomial.C gtK.Bv1_T_1701 * Polynomial.X

-- Fast O(N) `letB_intro` bridge for `cacheK.ac` (`evalACache k5Ops S_K Q_K`)!
lemma evalACache_K5_props :
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
  have hS3' : S3 = S_K ^ 3 := by rw [hS3, hS2']; dsimp only [k5Ops, ringOps]; ring
  have hQ3' : Q3 = Q_K ^ 3 := by rw [hQ3, hQ2']; dsimp only [k5Ops, ringOps]; ring
  have hSm3Q' : Sm3Q = S_K - 3 * Q_K := by rw [hSm3Q]; dsimp only [k5Ops, ringOps]; push_cast; ring
  have hSm3Q2' : Sm3Q2 = (S_K - 3 * Q_K) ^ 2 := by rw [hSm3Q2, hSm3Q']; dsimp only [k5Ops, ringOps]; ring
  have hA5' : A5 = 5 * S_K - 9 * Q_K := by rw [hA5]; dsimp only [k5Ops, ringOps]; push_cast; ring
  have hS15m9Q' : S15m9Q = 15 * S_K - 9 * Q_K := by rw [hS15m9Q]; dsimp only [k5Ops, ringOps]; push_cast; ring
  have hca0' : ca0 = -175 * ((5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)) := by
    rw [hca0, hA5']; dsimp only [k5Ops, ringOps]; push_cast; ring
  have hca1' : ca1 = 7 * (143 * S_K ^ 2 - 552 * (S_K * Q_K) + 468 * Q_K ^ 2) := by
    rw [hca1, hS2', hSQ', hQ2']; dsimp only [k5Ops, ringOps]; push_cast; ring
  have hca2' : ca2 = -28 * (S_K - 3 * Q_K) ^ 2 := by rw [hca2, hSm3Q2']; dsimp only [k5Ops, ringOps]; push_cast; ring
  have hcb0' : cb0 = 1050 * (S_K * (5 * S_K - 9 * Q_K)) := by rw [hcb0, hA5']; dsimp only [k5Ops, ringOps]; push_cast; ring
  have hcb1' : cb1 = 21 * (-92 * S_K ^ 2 + 312 * (S_K * Q_K) - 198 * Q_K ^ 2) + 810 * Q_K + 810 := by
    rw [hcb1, hS2', hSQ', hQ2']; dsimp only [k5Ops, ringOps]; push_cast; ring
  have hcb2' : cb2 = 84 * (S_K - 3 * Q_K) ^ 2 := by rw [hcb2, hSm3Q2']; dsimp only [k5Ops, ringOps]; push_cast; ring
  have hca_K : evalUPolyK5 ca_p = Polynomial.C 567 * k5Params.ca_h := by
    have hinf : Infinite K5 := Infinite.of_injective (Nat.cast : ℕ → K5) Nat.cast_injective
    apply Polynomial.funext; intro u
    rw [hca_p]; simp only [evalUPolyK5, evalUPoly, hca0', hca1', hca2', CoverParams.ca_h, CoverParams.quadU,
      CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3, k5Params_S, k5Params_Q,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_zero]; ring
  have hcb_K : evalUPolyK5 cb_p = Polynomial.C 567 * k5Params.cb_h := by
    have hinf : Infinite K5 := Infinite.of_injective (Nat.cast : ℕ → K5) Nat.cast_injective
    apply Polynomial.funext; intro u
    rw [hcb_p]; simp only [evalUPolyK5, evalUPoly, hcb0', hcb1', hcb2', CoverParams.cb_h, CoverParams.quadU,
      CoverParams.inv9, CoverParams.inv27, k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_zero]; ring
  have hca_e0 : (evalUPolyK5 ca_p).eval 0 = ca0 := by rw [hca_p]; simp [evalUPolyK5, evalUPoly]
  have hcb_e0 : (evalUPolyK5 cb_p).eval 0 = cb0 := by rw [hcb_p]; simp [evalUPolyK5, evalUPoly]
  -- Evaluate `l01, l12, l46` at `U = 0` in O(N) steps!
  have he0_b : (evalUPolyK5 b_p).eval 0 = -ca0 := by rw [hb_p, evalUPolyK5_uNeg, Polynomial.eval_neg, hca_e0]
  have he0_a5 : (evalUPolyK5 a5m9b).eval 0 = 5 * cb0 - 9 * (-ca0) := by
    rw [ha5m9b, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uSc]; simp [k5Ops, ringOps, hcb_e0, he0_b]
  have he0_a15 : (evalUPolyK5 a15m9b).eval 0 = 15 * cb0 - 9 * (-ca0) := by
    rw [ha15m9b, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uSc]; simp [k5Ops, ringOps, hcb_e0, he0_b]
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
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, 
      he0_a5, he0_a15]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_neg, Int.cast_ofNat, mul_zero, zero_mul, add_zero]; rfl
  have he0_B2 : (evalUPolyK5 B2).eval 0 = B2_0 := by
    rw [hB2]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSc, evalUPolyK5_uMul, evalUPolyK5_uShift,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, 
      hcb_e0, he0_a5]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_neg, Int.cast_ofNat, mul_zero, zero_mul, add_zero]; rfl
  have he0_A1 : (evalUPolyK5 A1).eval 0 = A1_0 := by
    rw [hA1]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSc, evalUPolyK5_uShift,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, 
      he0_a5, he0_a15, hS15m9Q']; dsimp only [k5Ops, ringOps]; simp only [Int.cast_neg, Int.cast_ofNat, mul_zero, zero_mul, add_zero]; rfl
  have he0_B1 : (evalUPolyK5 B1).eval 0 = B1_0 := by
    rw [hB1]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uShift,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      hcb_e0, he0_b]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_neg, Int.cast_ofNat, mul_zero, zero_mul, add_zero]; rfl
  have he0_D21 : (evalUPolyK5 D21).eval 0 = D21_0 := by
    rw [hD21]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, he0_A2, he0_B1, he0_A1, he0_B2]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_ofNat]; rfl
  have he0_D20 : (evalUPolyK5 D20).eval 0 = D20_0 := by
    rw [hD20]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, he0_A2, hcb_e0, hca_e0, he0_B2]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_ofNat]; rfl
  have he0_D10 : (evalUPolyK5 D10).eval 0 = D10_0 := by
    rw [hD10]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, he0_A1, hcb_e0, hca_e0, he0_B1]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_ofNat]; rfl
  have he0_m0 : (evalUPolyK5 m0).eval 0 = cb0 * cb0 * D10_0 - 2 * S_K * (cb0 * D20_0) + S_K * S_K * D21_0 := by
    rw [hm0]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      he0_aa, he0_D10, hcb_e0, he0_D20, hS2', he0_D21]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_ofNat]
  have he0_m1 : (evalUPolyK5 m1).eval 0 = cb0 * (-ca0) * D10_0 - (S_K * (-ca0) + Q_K * cb0) * D20_0 + S_K * Q_K * D21_0 := by
    rw [hm1]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      he0_ab, he0_D10, he0_sbqa, he0_D20, hSQ', he0_D21]
  have he0_m2 : (evalUPolyK5 m2).eval 0 = (-ca0) * (-ca0) * D10_0 - 2 * Q_K * ((-ca0) * D20_0) + Q_K * Q_K * D21_0 := by
    rw [hm2]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      he0_bb, he0_D10, he0_b, he0_D20, hQ2', he0_D21]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_ofNat]
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
      Polynomial.eval_C, he0_m4, he0_m6]; dsimp only [k5Ops, ringOps]; push_cast
    linear_combination A5 * hD21_0 - D20_0 * h5a9b + D21_0 * hA5'.symm
  have he0_l01 : (evalUPolyK5 l01).eval 0 = 0 := by
    rw [hl01]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, he0_m0, he0_m1]; dsimp only [k5Ops, ringOps]; push_cast
    linear_combination (cb0 * D10_0 - S_K * D20_0) * h5a9b - cb0 * A5 * hD20_0 +
      S_K * A5 * hD21_0 + (S_K * D21_0 - cb0 * D20_0) * hA5'.symm
  have he0_l12 : (evalUPolyK5 l12).eval 0 = 0 := by
    rw [hl12]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, he0_m1, he0_m2]; dsimp only [k5Ops, ringOps]; push_cast
    linear_combination ((-ca0) * D10_0 - Q_K * D20_0) * h5a9b - (-ca0) * A5 * hD20_0 +
      Q_K * A5 * hD21_0 + (Q_K * D21_0 - (-ca0) * D20_0) * hA5'.symm
  have hhead : ∀ (p : UPoly K5), p.headD 0 = (evalUPolyK5 p).eval 0 := fun p => by cases p <;> simp [evalUPolyK5, evalUPoly]
  -- Evaluate every node in `A_C` in O(N) steps!
  set S := ιC_K5 S_K; set Q := ιC_K5 Q_K
  set ca := polyC k5Params.ca_h; set cb := polyC k5Params.cb_h
  set a := (567 : A_C) * cb; set b := -((567 : A_C) * ca)
  have hp_ca : polyC (evalUPolyK5 ca_p) = 567 * ca := by rw [hca_K, polyC_mul, polyC_C]; simp [ca, map_ofNat]
  have hp_cb : polyC (evalUPolyK5 cb_p) = a := by rw [hcb_K, polyC_mul, polyC_C]; simp [a, cb, map_ofNat]
  have hp_b : polyC (evalUPolyK5 b_p) = b := by rw [hb_p, evalUPolyK5_uNeg, polyC_neg, hp_ca]
  have hp_am3b : polyC (evalUPolyK5 am3b_p) = a - 3 * b := by
    have hca_ex : polyC (evalUPolyK5 ca_p) = ιC_K5 ca0 + U_C * (ιC_K5 ca1 + U_C * ιC_K5 ca2) := by
      rw [hca_p]; simp only [evalUPolyK5, evalUPoly, polyC_add, polyC_mul, polyC_C, polyC_X, mul_zero, add_zero]
    have hcb_ex : polyC (evalUPolyK5 cb_p) = ιC_K5 cb0 + U_C * (ιC_K5 cb1 + U_C * ιC_K5 cb2) := by
      rw [hcb_p]; simp only [evalUPolyK5, evalUPoly, polyC_add, polyC_mul, polyC_C, polyC_X, mul_zero, add_zero]
    have h2 : cb2 - 3 * (-ca2) = 0 := by rw [hcb2', hca2']; ring
    have h2C : ιC_K5 cb2 + 3 * ιC_K5 ca2 = 0 := by
      have := congrArg ιC_K5 h2; simp only [map_sub, map_mul, map_neg, map_ofNat, map_zero] at this
      linear_combination this
    rw [ham3b_p]; simp only [evalUPolyK5, evalUPoly, k5Ops, ringOps, polyC_add, polyC_sub, polyC_neg, polyC_mul, polyC_C, polyC_X, polyC_ofNat,
      map_sub, map_mul, map_neg, map_ofNat, mul_zero, add_zero, Int.cast_ofNat]
    rw [← hp_cb, ← hp_b, hb_p, evalUPolyK5_uNeg, polyC_neg, hca_ex, hcb_ex]
    linear_combination -U_C ^ 2 * h2C
  have hp_a5 : polyC (evalUPolyK5 a5m9b) = 5 * a - 9 * b := by
    rw [ha5m9b, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uSc]
    simp only [polyC_sub, polyC_mul, polyC_C, hp_cb, hp_b]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_ofNat, map_ofNat]
  have hp_a15 : polyC (evalUPolyK5 a15m9b) = 15 * a - 9 * b := by
    rw [ha15m9b, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uSc]
    simp only [polyC_sub, polyC_mul, polyC_C, hp_cb, hp_b]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_ofNat, map_ofNat]
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
    rw [hA2]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uShift, evalUPolyK5_uMul, polyC_add, polyC_sub, polyC_mul, polyC_C, polyC_X, 
      hp_a5, hp_a15, hp_aa, hp_ab, hp_bb, hp_am3b2]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_neg, Int.cast_ofNat, map_neg, map_ofNat]
    exact dHS_243_ring a b U_C
  have hp_B2 : polyC (evalUPolyK5 B2) = B2_v := by
    rw [hB2]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uShift, evalUPolyK5_uMul, polyC_add, polyC_sub, polyC_mul, polyC_C, polyC_X, 
      hp_cb, hp_a5, hp_aa, hp_ab, hp_bb, hp_am3b2]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_neg, Int.cast_ofNat, map_neg, map_ofNat]
    exact dHQ0_27_ring a b U_C
  have hp_A1 : polyC (evalUPolyK5 A1) = A1_v := by
    rw [hA1]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uShift, polyC_add, polyC_sub, polyC_mul, polyC_C, polyC_X, polyC_ofNat, hS15m9Q', hA5', hSm3Q',
      map_sub, map_mul, map_ofNat, 
      hp_a5, hp_a15, hp_cb, hp_sbqa, hp_b, hp_am3b]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_neg, Int.cast_ofNat, map_neg, map_mul, map_sub, map_ofNat]
    change _ = 243 * q1_a1 a b S Q U_C 1
    rw [← dHS_bi_243_ring S Q a b U_C]
  have hp_B1 : polyC (evalUPolyK5 B1) = B1_v := by
    rw [hB1]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uShift, polyC_add, polyC_sub, polyC_mul, polyC_C, polyC_X, hSm3Q',
      hp_cb, hp_b, hp_sbqa, hp_am3b]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_neg, Int.cast_ofNat, map_neg, map_mul, map_sub, map_ofNat]
    change _ = 189 * q2_b1 a b S Q U_C 1
    rw [← dHQ1_bi_189_ring S Q a b U_C]
  have hp_D21 : polyC (evalUPolyK5 D21) = D21_v := by
    rw [hD21]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      polyC_sub, polyC_mul, polyC_C, hp_A2, hp_B1, hp_A1, hp_B2]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_ofNat, map_ofNat]; rfl
  have hp_D20 : polyC (evalUPolyK5 D20) = D20_v := by
    rw [hD20]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      polyC_sub, polyC_mul, polyC_C, hp_A2, hp_cb, hp_ca, hp_B2]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_ofNat, map_ofNat]; rfl
  have hp_D10 : polyC (evalUPolyK5 D10) = D10_v := by
    rw [hD10]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      polyC_sub, polyC_mul, polyC_C, hp_A1, hp_cb, hp_ca, hp_B1]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_ofNat, map_ofNat]; rfl
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
      polyC_add, polyC_sub, polyC_mul, polyC_C, hS2', map_mul, 
      hp_aa, hp_D10, hp_cb, hp_D20, hp_D21, hD21_m, hD20_m, hD10_m, Cscale, m, numM_lead3, a, S]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_ofNat, map_mul, map_ofNat]; ring
  have hp_m1 : polyC (evalUPolyK5 m1) = Cscale * m 1 := by
    rw [hm1]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      polyC_add, polyC_sub, polyC_mul, polyC_C, hSQ', map_mul,
      hp_ab, hp_D10, hp_sbqa, hp_D20, hp_D21, hD21_m, hD20_m, hD10_m, Cscale, m, numM_lead3, a, b, S, Q]; ring
  have hp_m2 : polyC (evalUPolyK5 m2) = Cscale * m 2 := by
    rw [hm2]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      polyC_add, polyC_sub, polyC_mul, polyC_C, hQ2', map_mul, 
      hp_bb, hp_D10, hp_b, hp_D20, hp_D21, hD21_m, hD20_m, hD10_m, Cscale, m, numM_lead3, b, Q]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_ofNat, map_mul, map_ofNat]; ring
  have hp_m4 : polyC (evalUPolyK5 m4) = Cscale * m 4 := by
    rw [hm4]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      polyC_sub, polyC_mul, polyC_C, hp_D21, hp_cb, hp_D20, hD21_m, hD20_m, Cscale, m, numM_lead3, a, S]; ring
  have hp_m6 : polyC (evalUPolyK5 m6) = Cscale * m 6 := by
    rw [hm6]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      polyC_sub, polyC_mul, polyC_C, hp_D21, hp_b, hp_D20, hD21_m, hD20_m, Cscale, m, numM_lead3, b, Q]; ring
  have hp_l01 : polyC (evalUPolyK5 l01) = 5 * (Cscale * m 0) - 9 * (Cscale * m 1) := by
    rw [hl01, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uSc]
    simp only [polyC_sub, polyC_mul, polyC_C, hp_m0, hp_m1]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_ofNat, map_ofNat]
  have hp_l12 : polyC (evalUPolyK5 l12) = 5 * (Cscale * m 1) - 9 * (Cscale * m 2) := by
    rw [hl12, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uSc]
    simp only [polyC_sub, polyC_mul, polyC_C, hp_m1, hp_m2]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_ofNat, map_ofNat]
  have hp_l46 : polyC (evalUPolyK5 l46) = 5 * (Cscale * m 4) - 9 * (Cscale * m 6) := by
    rw [hl46, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uSc]
    simp only [polyC_sub, polyC_mul, polyC_C, hp_m4, hp_m6]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_ofNat, map_ofNat]
  have hp_AY2b : polyC (evalUPolyK5 AY2_base) = ((-100 * 968178750 : ℤ) : A_C) * (5 * (Cscale * m 4) - 9 * (Cscale * m 6)) := by
    rw [hAY2_base, evalUPolyK5_uSc, polyC_mul, polyC_C, hp_l46]; dsimp only [k5Ops, ringOps]; simp only [map_intCast]
  refine ⟨hca_K, hcb_K, by rw [hca_e0, hca0'], by rw [hcb_e0, hcb0'], ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hhead]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSc, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, he0_l01, he0_l12, he0_l46, mul_zero, add_zero]
  · rw [hhead]; simp only [evalUPolyK5_uSc, Polynomial.eval_mul, Polynomial.eval_C, he0_l46, mul_zero]
  · simp only [evalUPolyK5_uSc, hAY2_base, Polynomial.eval_mul, Polynomial.eval_C, he0_l46, mul_zero]
  · simp only [evalUPolyK5_uSc, hAY2_base, Polynomial.eval_mul, Polynomial.eval_C, he0_l46, mul_zero]
  · simp [evalUPolyK5_uShift]
  · simp [evalUPolyK5_uShift]
  · simp [evalUPolyK5_uShift]
  · simp only [evalUPolyK5, evalUPoly, polyC_add, polyC_mul, polyC_C, polyC_X, mul_zero, add_zero]
    have h0 : Bv0_1701 = -175 * (S_K * (5 * S_K - 9 * Q_K) ^ 2) := by rw [hBv0, hA5']; dsimp only [k5Ops, ringOps]; push_cast; ring
    have h1 : Bv1_SQ_1701 = 7 * (143 * S_K ^ 3 - 828 * S_K ^ 2 * Q_K + 1404 * S_K * Q_K ^ 2 - 594 * Q_K ^ 3) +
        1215 * Q_K ^ 2 + 2430 * Q_K := by
      rw [hBv1SQ, hBv1S, hS3', hS2', hQ2', hQ3']; dsimp only [k5Ops, ringOps]; push_cast; ring
    have h2 : Bv2_1701 = -28 * (S_K - 3 * Q_K) ^ 3 := by rw [hBv2, hSm3Q2', hSm3Q']; dsimp only [k5Ops, ringOps]; push_cast; ring
    rw [h0, h1, h2]; ring
  · simp only [evalUPolyK5_uAdd, evalUPolyK5_uSc, polyC_add, polyC_mul, polyC_C,
      hp_l01, hp_l12, hp_l46]; dsimp only [k5Ops, ringOps, T]; simp only [map_intCast]
  · simp only [evalUPolyK5_uAdd, evalUPolyK5_uSc, polyC_add, polyC_mul, polyC_pow, polyC_C,
      map_pow, hp_m4, hp_m6, hp_D21, hD21_m]; dsimp only [k5Ops, ringOps, T]; simp only [map_intCast]
  · simp only [evalUPolyK5_uSc, polyC_add, polyC_mul, polyC_C, hp_AY2b]; dsimp only [k5Ops, ringOps, T]; simp only [map_intCast]
    generalize (((-100 * 968178750 : ℤ) : A_C) * (5 * (Cscale * m 4) - 9 * (Cscale * m 6))) = Z
    generalize ιC_K5 T_K = t; ring
  · simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uShift,
      polyC_add, polyC_sub, polyC_mul, polyC_C, polyC_X,
      hp_l01, hp_l12, hp_l46, hp_m0, hp_m1, hp_m6, hp_D21, hD21_m]; dsimp only [k5Ops, ringOps, T]; simp only [map_intCast, Int.cast_ofNat, map_ofNat]
  · simp only [evalUPolyK5_uAdd, evalUPolyK5_uSc, evalUPolyK5_uShift,
      polyC_add, polyC_mul, polyC_pow, polyC_C, polyC_X, map_pow, hp_m4, hp_D21, hD21_m]; dsimp only [k5Ops, ringOps, T]; simp only [map_intCast]

lemma evalUPolyK5_ca_cb :
    evalUPolyK5 cacheK.ac.ca_p = Polynomial.C 567 * k5Params.ca_h ∧
    evalUPolyK5 cacheK.ac.cb_p = Polynomial.C 567 * k5Params.cb_h :=
  ⟨evalACache_K5_props.1, evalACache_K5_props.2.1⟩

lemma A0U_head_zero :
    cacheK.ac.A0U_t0.headD 0 = 0 ∧ cacheK.ac.A0U_t1.headD 0 = 0 :=
  evalACache_K5_props.2.2.2.2.1

lemma evalACache_AC_bridge :
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

end SymmetricSexticResidual.LocalResidueQ5
