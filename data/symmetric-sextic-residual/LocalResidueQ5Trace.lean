import Proposal.LocalResidueQ5Bridge

/-! Part 4 of `LocalResidueQ5`: `evalGeomSQ_K5_props`, `evalGeomT_K5_props`, `p4_AC_eq`,
`trace_AC_eta_AC_main_eq`, and `sum_RQ5_eta_L_eq_BTot`. -/

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

lemma evalGeomSQ_K5_props :
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
  have hS3' : S3 = S_K ^ 3 := by rw [hS3, hS2']; dsimp only [k5Ops, ringOps]; ring
  have hS4' : S4 = S_K ^ 4 := by rw [hS4, hS2']; dsimp only [k5Ops, ringOps]; ring
  have hQ3' : Q3 = Q_K ^ 3 := by rw [hQ3, hQ2']; dsimp only [k5Ops, ringOps]; ring
  have hQ4' : Q4 = Q_K ^ 4 := by rw [hQ4, hQ2']; dsimp only [k5Ops, ringOps]; ring
  have hSm3Q' : Sm3Q = S_K - 3 * Q_K := by rw [hSm3Q]; dsimp only [k5Ops, ringOps]; push_cast; ring
  have hA5' : A5 = 5 * S_K - 9 * Q_K := by rw [hA5]; dsimp only [k5Ops, ringOps]; push_cast; ring
  have hS2x' : S2x = 2 * S_K := by rw [hS2x]; dsimp only [k5Ops, ringOps]; push_cast; ring
  have hu3_eq : evalBivLK5 u3 = x_K - S_K + 2 * Q_K := by
    rw [hu3]; simp only [evalBivLK5, evalBivL, evalYList, k5Ops, ringOps, Int.cast_ofNat]; ring
  have hu3_2_eq : evalBivLK5 u3_2 = (x_K - S_K + 2 * Q_K) ^ 2 := by
    rw [hu3_2, evalBivLK5_bivMul, hu3_eq]; ring
  have hLX0_eq : evalBivLK5 LX0 = 25 * S_K - 45 * Q_K := by
    rw [hLX0]; simp only [bivConst, evalBivLK5, evalBivL, evalYList, k5Ops, ringOps, Int.cast_ofNat]; ring
  have hLX1_eq : evalBivLK5 LX1 = 45 * Q_K - 25 * S_K + 27 * x_K := by
    rw [hLX1]; simp only [evalBivLK5, evalBivL, evalYList, k5Ops, ringOps, Int.cast_ofNat]; ring
  have hLX_ac : polyC (evalUBivLK5 LX_27) = 27 * LX_of S Q x U_C := by
    rw [hLX27]; simp only [evalUBivLK5, evalUBivL, hLX0_eq, hLX1_eq, polyC_add, polyC_sub, polyC_mul, polyC_C, polyC_X, polyC_ofNat,
      LX_of, u3_of, u_of, S, Q, x, map_add, map_sub, map_mul, map_ofNat, mul_zero, add_zero]; ring
  have hLX_e0 : (evalUBivLK5 LX_27).eval 0 = 25 * S_K - 45 * Q_K := by
    rw [hLX27]; simp [evalUBivLK5, evalUBivL, hLX0_eq]
  have hLX_e1 : (evalUBivLK5 LX_27).eval 1 = 27 * x_K := by
    rw [hLX27]; simp [evalUBivLK5, evalUBivL, hLX0_eq, hLX1_eq]; ring
  have hd0_ac : polyC (evalUBivLK5 dLX_0) = 27 * dLX_fn 0 U_C := by
    rw [hdLX0]; simp only [evalUBivLK5, evalUBivL, bivConst, evalBivL, evalYList, k5Ops, ringOps,
      polyC_add, polyC_neg, polyC_mul, polyC_X, polyC_ofNat, 
      dLX_fn, u_of, Int.cast_neg, Int.cast_ofNat,
      map_neg, map_ofNat, mul_zero, add_zero]; ring
  have hd0_e0 : (evalUBivLK5 dLX_0).eval 0 = 25 := by
    rw [hdLX0]; simp [evalUBivLK5, evalUBivL, bivConst, evalBivL, evalYList, k5Ops, ringOps]
  have hd0_e1 : (evalUBivLK5 dLX_0).eval 1 = 0 := by
    rw [hdLX0]; simp [evalUBivLK5, evalUBivL, bivConst, evalBivL, evalYList, k5Ops, ringOps]
  have hd1_ac : polyC (evalUBivLK5 dLX_1) = 27 * dLX_fn 1 U_C := by
    rw [hdLX1]; simp only [evalUBivLK5, evalUBivL, bivConst, evalBivL, evalYList, k5Ops, ringOps,
      polyC_add, polyC_neg, polyC_mul, polyC_X, polyC_ofNat, 
      dLX_fn, u_of, Int.cast_neg, Int.cast_ofNat,
      map_neg, map_ofNat, mul_zero, add_zero]; ring
  have hd1_e0 : (evalUBivLK5 dLX_1).eval 0 = -45 := by
    rw [hdLX1]; simp [evalUBivLK5, evalUBivL, bivConst, evalBivL, evalYList, k5Ops, ringOps]
  have hd1_e1 : (evalUBivLK5 dLX_1).eval 1 = 0 := by
    rw [hdLX1]; simp [evalUBivLK5, evalUBivL, bivConst, evalBivL, evalYList, k5Ops, ringOps]
  have hd3_ac : polyC (evalUBivLK5 dLX_3) = 27 * dLX_fn 3 U_C := by
    rw [hdLX3]; simp only [evalUBivLK5, evalUBivL, bivConst, evalBivL, evalYList, k5Ops, ringOps,
      polyC_add, polyC_mul, polyC_X, polyC_ofNat, polyC_zero,
      dLX_fn, Int.cast_ofNat,
      map_ofNat, map_zero, mul_zero, add_zero]; ring
  have hd3_e0 : (evalUBivLK5 dLX_3).eval 0 = 0 := by
    rw [hdLX3]; simp [evalUBivLK5, evalUBivL, evalBivL]
  have hd3_e1 : (evalUBivLK5 dLX_3).eval 1 = 27 := by
    rw [hdLX3]; simp [evalUBivLK5, evalUBivL, bivConst, evalBivL, evalYList, k5Ops, ringOps]
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
  · rw [hH0SQ, hpS, hS3', hS2', hQ2', hQ3']; dsimp only [k5Ops, ringOps]; push_cast; ring
  · simp only [evalBivLK5_bivAdd, evalBivLK5_bivSc, bivConst, evalBivLK5, evalBivL, evalYList, hu3_eq, hu3_2_eq,
      hS2', hSQ', hQ2', hQ3', DX2_of, u3_of, S, Q, x, map_add, map_sub, map_mul, map_pow,
      map_ofNat, map_zero]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_neg, Int.cast_ofNat, map_neg, map_mul, map_sub, map_pow, map_ofNat, mul_zero, add_zero]; ring
  · simp only [evalBivLK5_bivAdd, evalBivLK5_bivSc, bivConst, evalBivLK5, evalBivL, evalYList, hu3_eq, hu3_2_eq,
      hS2', hSQ', hQ2', dDX2_fn, u3_of, S, Q, x, map_add, map_sub, map_mul, map_pow,
      map_ofNat, map_zero]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_neg, Int.cast_ofNat, map_neg, map_mul, map_add, map_sub, map_ofNat, mul_zero, add_zero]; ring
  · simp only [evalBivLK5_bivAdd, evalBivLK5_bivSc, bivConst, evalBivLK5, evalBivL, evalYList, hu3_eq,
      hS2', hSQ', hQ2', dDX2_fn, u3_of, S, Q, x, map_add, map_sub, map_mul, 
      map_ofNat, map_zero]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_neg, Int.cast_ofNat, map_neg, map_mul, map_add, map_sub, map_ofNat, mul_zero, add_zero]; ring
  · simp only [evalBivLK5_bivAdd, evalBivLK5_bivSc, bivConst, evalBivLK5, evalBivL, evalYList, hu3_eq,
      hS2', hSQ', dDX2_fn, u3_of, S, Q, x, map_add, map_sub, map_mul, 
      map_ofNat, map_zero]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_neg, Int.cast_ofNat, map_neg, map_mul, map_add, map_ofNat, mul_zero, add_zero]; ring
  · simp only [evalBivLK5, evalBivL, evalYList, hS2', hSQ', hQ2', k5Ops, ringOps, dF5_fn, dH0_fn, S, Q, x, 
      map_add, map_sub, map_mul, map_neg, map_ofNat, map_zero, Int.cast_neg, Int.cast_ofNat]; ring
  · simp only [evalBivLK5, evalBivL, evalYList, hS2', hSQ', hQ2', k5Ops, ringOps, dF5_fn, dH0_fn, S, Q, 
      map_add, map_sub, map_mul, map_ofNat, map_zero, Int.cast_ofNat]; ring
  · simp only [evalBivLK5, evalBivL, evalYList, k5Ops, ringOps, dF5_fn, S, x, 
      map_add, map_mul, map_ofNat, map_zero, Int.cast_ofNat]; ring
  · simp only [evalBivLK5, evalBivL, evalYList, hS2', hSQ', hQ2', k5Ops, ringOps, q1_a0, dH_dS, Int.cast_neg, Int.cast_ofNat]; ring
  · simp only [evalBivLK5, evalBivL, evalYList, hS2', hSQ', hQ2', k5Ops, ringOps, q2_b0, dH_dQ, Int.cast_ofNat]; ring
  · simp only [evalBivLK5, evalBivL, evalYList, k5Ops, ringOps, Int.cast_ofNat]; ring
  · simp only [evalUBivLK5_ubAdd, evalUBivLK5_ubSc, polyC_add, polyC_mul, polyC_C, polyC_ofNat, hS2x', hd0_ac, hLX_ac,
      dLX_fn, LX_of, u3_of, u_of, S, Q, x, map_mul, map_ofNat]; ring
  · simp only [evalUBivLK5_ubAdd, evalUBivLK5_ubSc, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      hd0_e1, hLX_e1, mul_zero, zero_add]
  · simp only [evalUBivLK5_ubSc, polyC_mul, polyC_C, polyC_ofNat, hS2x', hd1_ac, dLX_fn, u_of, S, map_mul, map_ofNat]; ring
  · simp only [evalUBivLK5_ubSc, Polynomial.eval_mul, Polynomial.eval_C, hd1_e1, mul_zero]
  · simp only [evalUBivLK5_ubSc, polyC_mul, polyC_C, polyC_ofNat, hS2x', hd3_ac, dLX_fn, S, map_mul, map_ofNat]; ring
  · simp only [evalUBivLK5_ubSc, Polynomial.eval_mul, Polynomial.eval_C, hS2x', hd3_e1]; ring
  · simp only [evalUPolyK5, evalUPoly, hA5', hSm3Q', k5Ops, ringOps, polyC_add, polyC_sub, polyC_neg, polyC_mul, polyC_C, polyC_X, polyC_ofNat, A1_of, S, Q,
      map_sub, map_mul, map_neg, map_ofNat, mul_zero, add_zero,
      Int.cast_neg, Int.cast_ofNat]; ring
  · simp only [evalUPolyK5, evalUPoly, k5Ops, ringOps, Int.cast_neg, Int.cast_ofNat, hqC0_eq, hqC1_eq,
      polyC_add, polyC_mul, polyC_C, polyC_X, mul_zero, add_zero]; ring
  · simp only [List.getD_cons_zero, k5Ops, ringOps, Int.cast_neg, Int.cast_ofNat, hqC0_eq]
  · simp only [List.getD_cons_succ, List.getD_cons_zero, k5Ops, ringOps, Int.cast_neg, Int.cast_ofNat, hqC1_eq]
  · simp only [List.getD_cons_zero, k5Ops, ringOps, Int.cast_neg, Int.cast_ofNat, hqEx0_eq]
  · simp only [List.getD_cons_succ, List.getD_cons_zero, k5Ops, ringOps, Int.cast_neg, Int.cast_ofNat, hqEx1_eq]

-- Fast O(N) `letB_intro` bridge for `gtK` (`evalGeomT k5Ops S_K cacheK.ac.ca_p cacheK.ac.cb_p cacheK.gsq T_K`)!
lemma evalGeomT_K5_props :
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
      k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
      q2_b0, dH_dQ]; ring
  -- Scalar identities
  have hT2' : T2 = T_K * T_K := hT2
  have hT3' : T3 = T_K ^ 3 := by rw [hT3, hT2']; dsimp only [k5Ops, ringOps]; ring
  have hH0 : H0_7 = 7 * H0_of S_K Q_K T_K := by
    rw [hH0_7, hpT, hgsqP.1, hT3', hT2']; dsimp only [k5Ops, ringOps, H0_of]; push_cast; ring
  have hH0_2 : H0_7_2 = H0_7 ^ 2 := by rw [hH0_7_2]; dsimp only [k5Ops, ringOps]; ring
  have hAv0 : Av0_243 = 243 * k5Params.Av0 := by
    rw [hAv0_243, hTm3]; simp only [k5Ops, ringOps, CoverParams.Av0, CoverParams.inv243, k5Params_inv3, k5Params_T,
      Int.cast_neg, Int.cast_ofNat]; ring
  have hCv0 : Cv0_243 = 243 * k5Params.Cv0 := by
    rw [hCv0_243, hCv0_int, hT59]; simp only [k5Ops, ringOps, CoverParams.Cv0, CoverParams.inv243, k5Params_inv3, k5Params_T,
      Int.cast_neg, Int.cast_ofNat]; ring
  have hCv0i : Cv0_243 = -25 * Cv0_int := by rw [hCv0_243]; dsimp only [k5Ops, ringOps]; push_cast; ring
  have hBv1701 : polyC (evalUPolyK5 cacheK.ac.Bv_SQ + Polynomial.C Bv1_T_1701 * Polynomial.X) =
      1701 * (ιC_K5 k5Params.Av0 * polyC k5Params.bW) := by
    have hbW : ιC_K5 k5Params.Av0 * polyC k5Params.bW = polyC k5Params.Bv := by
      rw [CoverParams.bW, polyC_mul, polyC_C, ← mul_assoc, ← map_mul,
        k5Params_Av0_mul_inv, map_one, one_mul]
    rw [hbW, polyC_add, polyC_mul, polyC_C, polyC_X, hacP.2.2.2.2.2.2.2.1, hBv1_T, hT3', hT2']
    simp only [k5Ops, ringOps, CoverParams.Bv, CoverParams.Bv0, CoverParams.Bv1, CoverParams.Bv2, CoverParams.quadU,
      CoverParams.inv9, CoverParams.inv27, CoverParams.inv243, k5Params_inv3, k5Params_inv7,
      k5Params_S, k5Params_Q, k5Params_T, polyC_add, polyC_sub, polyC_neg, polyC_mul, polyC_pow, polyC_C, polyC_X, polyC_ofNat, 
      map_add, map_sub, map_mul, map_inv₀, map_neg, map_pow, map_ofNat, Int.cast_ofNat]; ring
  -- BivL & basic `A_C` evaluations
  have hv3_eq : evalBivLK5 v3 = y_K - T_K + 2 := by rw [hv3]; simp only [evalBivLK5, evalBivL, evalYList, k5Ops, ringOps, Int.cast_ofNat]; ring
  have hv3_2_eq : evalBivLK5 v3_2 = (y_K - T_K + 2) ^ 2 := by rw [hv3_2, evalBivLK5_bivMul, hv3_eq]; ring
  have hDY2 : ιC_K5 (evalBivLK5 DY2) = DY2_of T y := by
    rw [hDY2_d]; simp only [evalBivLK5_bivAdd, evalBivLK5_bivSc, bivConst, evalBivLK5, evalBivL, evalYList,
      hv3_eq, hv3_2_eq, hT2', DY2_of, v3_of, T, y, map_add, map_sub, map_mul, map_pow,
      map_ofNat, map_zero]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_neg, Int.cast_ofNat, map_neg, map_mul, map_sub, map_ofNat, mul_zero, add_zero]; ring
  have hdDY2 : ιC_K5 (evalBivLK5 dDY2_dy) = dDY2_fn 4 T y := by
    rw [hdDY2_d]; simp only [evalBivLK5_bivAdd, evalBivLK5_bivSc, bivConst, evalBivLK5, evalBivL, evalYList,
      hv3_eq, hT2', dDY2_fn, v3_of, T, y, map_add, map_sub, map_mul, map_ofNat, map_zero
      ]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_neg, Int.cast_ofNat, map_neg, map_mul, map_add, map_ofNat, mul_zero, add_zero]; ring
  have hST' : ST = S_K * T_K := hST
  have hST2' : ST2 = 2 * (S_K * T_K) := by rw [hST2, hST']; dsimp only [k5Ops, ringOps]; push_cast; ring
  have hW2_eq : ιC_K5 (evalBivLK5 W2) = S * T * DX2_of S Q x * DY2_of T y := by
    rw [hW2, evalBivLK5_bivSc, evalBivLK5_bivMul, hST', map_mul, map_mul, map_mul, hgsqP.2.2.1, hDY2]; ring
  have hdF5_4_eq : ιC_K5 (evalBivLK5 dF5_4) = 7 * dF5_fn 4 S Q T x y := by
    rw [hdF5_4]; simp only [evalBivLK5, evalBivL, evalYList, k5Ops, ringOps, dF5_fn, T, y, map_add, map_mul, map_ofNat, map_zero, Int.cast_ofNat]; ring
  have hLY0_K : evalBivLK5 LY0 = 25 * T_K - 45 := by
    rw [hLY0]; simp only [bivConst, evalBivLK5, evalBivL, evalYList, k5Ops, ringOps, Int.cast_ofNat]; ring
  have hLY1_K : evalBivLK5 LY1 = 45 - 25 * T_K + 27 * y_K := by
    rw [hLY1]; simp only [evalBivLK5, evalBivL, evalYList, k5Ops, ringOps, Int.cast_ofNat]; ring
  have hLY0_AC : ιC_K5 (evalBivLK5 LY0) = 27 * LY_of T y 0 := by
    rw [hLY0_K]; simp only [LY_of, v3_of, v_of, T, map_sub, map_mul, map_ofNat]; ring
  have hLY_eq : ιC_K5 (evalBivLK5 LY0) + V_C * ιC_K5 (evalBivLK5 LY1) = 27 * LY_of T y V_C := by
    rw [hLY0_K, hLY1_K]; simp only [LY_of, v3_of, v_of, T, y, map_add, map_sub, map_mul, map_ofNat]; ring
  have hPY_K : evalBivLK5 PY_4_1 = 54 * T_K := by
    rw [hPY41]; simp only [bivConst, evalBivLK5, evalBivL, evalYList, k5Ops, ringOps, Int.cast_ofNat]; ring
  -- Evaluate `br0_0..br1_4`, `omF1_*`, `dYF*`, `QX*` at `U = 0`, `U = 1`, and in `A_C`!
  have hbr0_3_e0 : (evalUBivLK5 br0_3).eval 0 = 0 := by
    rw [hbr0_3, evalUBivLK5_ubSc, evalUBivLK5_ubBmul]; simp [hgsqP.2.2.2.2.2.2.2.2.1.2.1]
  have hbr0_0_e0 : (evalUBivLK5 br0_0).eval 0 = -(2 * (S_K * T_K)) * ((25 * T_K - 45) * 25) - T_K * ((25 * T_K - 45) * (25 * S_K - 45 * Q_K)) := by
    rw [hbr0_0]; simp only [evalUBivLK5_ubSub, evalUBivLK5_ubSc, evalUBivLK5_ubBmul,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hST2', hLY0_K,
      hgsqP.2.2.2.2.2.2.1.2.1, hgsqP.2.2.2.2.2.1.2.1]; dsimp only [k5Ops, ringOps]
  have hbr0_1_e0 : (evalUBivLK5 br0_1).eval 0 = -(2 * (S_K * T_K)) * ((25 * T_K - 45) * (-45)) := by
    rw [hbr0_1]; simp only [evalUBivLK5_ubSc, evalUBivLK5_ubBmul,
      Polynomial.eval_mul, Polynomial.eval_C, hST2', hLY0_K, hgsqP.2.2.2.2.2.2.2.1.2.1]; dsimp only [k5Ops, ringOps]
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
    · rw [hbr0_3]; simp [evalUBivLK5_ubSc, evalUBivLK5_ubBmul, hST2', hgsqP.2.2.2.2.2.2.2.2.1.2.2]; dsimp only [k5Ops, ringOps]; ring
    · rw [hbr1_0]; simp [evalUBivLK5_ubSub, evalUBivLK5_ubSc, evalUBivLK5_ubBmul, hgsqP.2.2.2.2.2.2.1.2.2, hgsqP.2.2.2.2.2.1.2.2]
    · rw [hbr1_1]; simp [evalUBivLK5_ubSc, evalUBivLK5_ubBmul, hgsqP.2.2.2.2.2.2.2.1.2.2]
    · rw [hbr1_3]; simp [evalUBivLK5_ubSc, evalUBivLK5_ubBmul, hST2', hgsqP.2.2.2.2.2.2.2.2.1.2.2]; dsimp only [k5Ops, ringOps]; ring
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
      map_mul, map_ofNat, hca_p, hcb_p, hgsqP.2.2.1, hDY2, hdDY2,
      hgsqP.2.2.2.2.1.1, hgsqP.2.2.2.2.1.2.1, hgsqP.2.2.2.2.1.2.2.1,
      hgsqP.2.2.2.2.2.1.1, hgsqP.2.2.2.2.2.2.1.1, hgsqP.2.2.2.2.2.2.2.1.1, hgsqP.2.2.2.2.2.2.2.2.1.1,
      hgsqP.2.2.2.2.2.2.2.2.2.1.1, hgsqP.2.2.2.2.2.2.2.2.2.1.2.2.1, hgsqP.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1]; dsimp only [k5Ops, ringOps]; simp only [map_neg, map_mul, map_ofNat]
    have hd0 : dDY2_fn 0 T y = 0 := rfl
    have hd1 : dDY2_fn 1 T y = 0 := rfl
    have hd3 : dDY2_fn 3 T y = 0 := rfl
    simp only [QX_dot, QX_num, Omega_F, dDY2_F, F_contract, om_fn, br_fn, hd0, hd1, hd3, dLY_fn
      ]
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
      map_mul, hca_p, hcb_p, hDY2, hdF5_4_eq, hLY0_AC,
      hgsqP.2.2.2.1.1, hgsqP.2.2.2.1.2.1, hgsqP.2.2.2.1.2.2,
      hgsqP.2.2.2.2.2.1.1, hgsqP.2.2.2.2.2.2.1.1, hgsqP.2.2.2.2.2.2.2.1.1, hgsqP.2.2.2.2.2.2.2.2.1.1]; dsimp only [k5Ops, ringOps]; simp only [map_neg, map_mul, map_ofNat]
    have hd4 : dDX2_fn 4 S Q x = 0 := rfl
    have hdX4 : dLX_fn 4 U_C = 0 := rfl
    simp only [QY_num, Omega_F, dDX2_F, F_contract, om_fn, br_fn, hd4, hdX4, dLY_fn
      ]
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
    simp only [evalUBivLK5, evalUBivL, evalBivL, evalYList, k5Ops, ringOps, Int.cast_ofNat,
      hgsqP.2.2.2.2.2.2.2.2.2.2.2.2.1, hgsqP.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hgsqP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hgsqP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
      polyC_add, polyC_sub, polyC_neg, polyC_mul, polyC_pow, polyC_C, polyC_X, polyC_ofNat, S, Q, T, x, y,
      map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, mul_zero, add_zero]; ring
  have hAv_A : ιC_K5 k5Params.Av0 = -(4 / 243 : A_C) * (T - 3) ^ 3 := by
    simp only [CoverParams.Av0, CoverParams.inv243, k5Params_inv3, k5Params_T, T,
      map_mul, map_sub, map_neg, map_inv₀, map_pow, map_ofNat]; ring
  have hCv_A : ιC_K5 k5Params.Cv0 = -(25 / 243 : A_C) * T * (5 * T - 9) ^ 2 := by
    simp only [CoverParams.Cv0, CoverParams.inv243, k5Params_inv3, k5Params_T, T,
      map_mul, map_sub, map_neg, map_inv₀, map_pow, map_ofNat]; ring
  have hqY_AC : polyC (evalUBivLK5 qY_0_321489) -
      9 * (321489 / 63 : A_C) * polyC (evalUBivLK5 DY2_qE_63) * U_C * ιC_K5 k5Params.Av0 * V_C =
      321489 * (QY_dot / v_of V_C) := by
    have hQY0_eq : polyC (evalUBivLK5 qY_0_321489) =
        -2893401 * (QY_num S Q T x y U_C 0 0 * cb - QY_num S Q T x y U_C 0 1 * ca) +
        189 * ιC_K5 Cv0_243 * U_C * polyC (evalUBivLK5 DY2_qE_63) := by
      rw [hqY0, evalUBivLK5_ubAdd, evalUBivLK5_ubNeg, evalUBivLK5_ubSc, evalUBivLK5_ubShift,
        polyC_add, polyC_neg, polyC_mul, polyC_mul, polyC_C, polyC_X, hQYd0_AC]
      simp only [k5Ops, ringOps, map_mul, map_ofNat, Int.cast_ofNat]; ring
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
      polyC_sub, polyC_mul, polyC_C, hST2', 
      hW2_eq, hdF5_4_eq, hgsqP.2.2.2.2.1.2.2.1, hgsqP.2.2.2.2.2.2.2.2.1.1, hgsqP.2.2.2.2.2.1.1]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_ofNat, map_neg, map_mul, map_ofNat]
    have hdX4 : dLX_fn 4 U_C = 0 := rfl
    simp only [EB_of, W2_of, br_fn, hdX4, dLY_fn]
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
    simp only [evalUBivLK5_ubAdd, evalUBivLK5_ubSub, evalUBivLK5_ubSc, evalUBivLK5_ubShift, evalUBivLK5_ubMulU, polyC_add, polyC_sub, polyC_mul, polyC_C, polyC_X, 
      hgsqP.2.2.2.2.2.2.2.2.2.2.1]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_neg, Int.cast_ofNat, map_neg, map_mul, map_ofNat, hH0_AC, hAv0_AC, hCv0_AC]
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

lemma evalGeomT_AC_bridge :
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
def R13_int_p : K5[X] :=
  Polynomial.C (7 * gtK.Cv0_243) * (Polynomial.X * A0U_U_p * (evalUBivLK5 gtK.q1_0_div_sc - evalUBivLK5 gtK.q1_2_div_sc)) +
  Polynomial.C (45927 * gtK.Cv0_243 * gtK.H0_7_2) * (Polynomial.X * AY3_p * evalUBivLK5 gtK.DY2_qE_63) +
  Polynomial.C 7 * (A0V_p * evalUBivLK5 gtK.q1_1_sc) +
  Polynomial.C (243 * gtK.H0_7_2) * (AY2_p * evalUBivLK5 gtK.qY_0_321489 + AX2_p * evalUBivLK5 gtK.qX_0_sc) -
  A0V_p * Bv_1701_p * evalUBivLK5 gtK.q1_0_div_sc

def R12_int_p : K5[X] := R13_int_p.divX

lemma R13_int_p_eval_zero : R13_int_p.eval 0 = 0 := by
  have hac0 := evalACache_K5_props.2.2.2.2.2
  have hAY2_0 : AY2_p.eval 0 = 0 := by
    simp [AY2_p, hac0.1.1, hac0.1.2]
  have hAX2_0 : AX2_p.eval 0 = 0 := by
    simp [AX2_p, hac0.2.1.1, hac0.2.1.2.1, hac0.2.1.2.2]
  have hq0 := evalGeomT_K5_props.2.2.2.2.2.2.2.2.2
  simp only [R13_int_p, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, hAY2_0, hAX2_0, hq0.1, hq0.2.1, hq0.2.2.1, hq0.2.2.2]
  ring

lemma R13_int_p_eq_X_mul_R12 : R13_int_p = Polynomial.X * R12_int_p := by
  have h := Polynomial.X_mul_divX_add R13_int_p
  have hc0 : R13_int_p.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]; exact R13_int_p_eval_zero
  rw [hc0, map_zero, add_zero] at h
  exact h.symm

-- Step 1 of `trace_AC_eta_AC_main_eq`: extract `p4_AC = (interp4 P18_z_AC).1` via `numM_isPoly3`, `numM_lead3_scale`, `interp4_eq`!
lemma p4_AC_eq :
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
lemma trace_AC_eta_AC_main_eq :
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
lemma uAdd_len {α : Type*} (o : PolyOps α) : ∀ a b, (uAdd o a b).length = max a.length b.length
  | [], b => by simp [uAdd]
  | a :: as, [] => by simp [uAdd]
  | _ :: as, _ :: bs => by simp [uAdd, uAdd_len o as bs, Nat.succ_max_succ]

lemma uSub_len {α : Type*} (o : PolyOps α) : ∀ a b, (uSub o a b).length = max a.length b.length
  | [], b => by simp [uSub, uNeg]
  | a :: as, [] => by simp [uSub]
  | _ :: as, _ :: bs => by simp [uSub, uSub_len o as bs, Nat.succ_max_succ]

lemma uMul_len_le {α : Type*} (o : PolyOps α) :
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

lemma ubAdd_len {α : Type*} (o : PolyOps α) : ∀ a b, (ubAdd o a b).length = max a.length b.length
  | [], b => by simp [ubAdd]
  | a :: as, [] => by simp [ubAdd]
  | _ :: as, _ :: bs => by simp [ubAdd, ubAdd_len o as bs, Nat.succ_max_succ]

lemma ubSub_len {α : Type*} (o : PolyOps α) : ∀ a b, (ubSub o a b).length = max a.length b.length
  | [], b => by simp [ubSub, ubNeg]
  | a :: as, [] => by simp [ubSub]
  | _ :: as, _ :: bs => by simp [ubSub, ubSub_len o as bs, Nat.succ_max_succ]

lemma ubMulU_len_le {α : Type*} (o : PolyOps α) :
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

lemma ubSynDiv1Rem_len {α : Type*} (o : PolyOps α) :
    ∀ a, (ubSynDiv1Rem o a).2.length = a.length - 1
  | [] => rfl
  | [_] => rfl
  | _ :: b' :: rest => by
      have ih := ubSynDiv1Rem_len o (b' :: rest)
      simp only [ubSynDiv1Rem, List.length_cons] at ih ⊢
      omega

lemma uSc_len {α : Type*} (o : PolyOps α) (c : α) (a : UPoly α) : (uSc o c a).length = a.length :=
  List.length_map _

def acUnit : ACache Unit := evalACache uOps () ()
def gsqUnit : GeomSQ Unit := evalGeomSQ uOps () ()
def gtUnit : GeomT Unit := evalGeomT uOps () acUnit.ca_p acUnit.cb_p gsqUnit ()

lemma acUnit_lens :
    (uTail acUnit.A0U_t0).length ≤ 9 ∧ (uTail acUnit.A0U_t1).length ≤ 9 ∧
    acUnit.A0V_t0.length ≤ 10 ∧ acUnit.A0V_t1.length ≤ 10 ∧ acUnit.A0V_t2.length ≤ 10 ∧
    (uMul uOps acUnit.A0V_t0 acUnit.Bv_SQ).length ≤ 12 ∧
    (uMul uOps acUnit.A0V_t1 acUnit.Bv_SQ).length ≤ 12 ∧
    (uMul uOps acUnit.A0V_t2 acUnit.Bv_SQ).length ≤ 12 ∧
    acUnit.AY2_t0.length ≤ 10 ∧ acUnit.AY2_t1.length ≤ 10 ∧
    acUnit.AY3_t0.length ≤ 11 ∧ acUnit.AY3_t1.length ≤ 11 ∧
    acUnit.AX2_t0.length ≤ 11 ∧ acUnit.AX2_t1.length ≤ 11 ∧ acUnit.AX2_t2.length ≤ 11 ∧
    acUnit.Bv_SQ.length ≤ 3 := by decide +kernel

lemma gtUnit_lens :
    (ubSub uOps gtUnit.q1_0_div_sc gtUnit.q1_2_div_sc).length ≤ 3 ∧
    gtUnit.DY2_qE_63.length ≤ 2 ∧ gtUnit.q1_1_sc.length ≤ 5 ∧
    gtUnit.qY_0_321489.length ≤ 4 ∧ gtUnit.qX_0_sc.length ≤ 3 ∧ gtUnit.q1_0_div_sc.length ≤ 3 ∧
    gtUnit.q1_2_div_sc.length ≤ 3 := by decide +kernel

lemma cacheK_ac_lens :
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

lemma gtK_lens :
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
lemma evalBivLK5_BTot_eq_dot_W :
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

lemma R12_int_p_natDegree_le : R12_int_p.natDegree ≤ 12 := by
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
lemma sum_RQ5_eta_L_eq_BTot :
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


end SymmetricSexticResidual.LocalResidueQ5
