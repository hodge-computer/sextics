import Proposal.CoverAlgebra
import Proposal.SheetCalculus
import HodgeComputer.Constructions.QuadraticCovers.RationalCoverResidues
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.SplittingField.Construction

/-! Horizontal residue calculus on the algebraic cover `P_34 = 0` for
`symmetric-sextic-residual`:
1. First-order `Dual R` calculus, 4×4 Schur complement for `J_fib`, division-free degree-4
   quadratic remainder `remDeg4`, 5-point interpolation `interp4`, and functorial rational
   function maps `mapRatFunc`.
2. Irreducible quadratic cover field `A_C = AdjoinRoot (W^2 + bW * W + cW)` over `RatFunc K5`,
   explicit cover 1-form `eta : RatFunc K5 := Algebra.trace (RatFunc K5) A_C eta_AC`, and the
   Euler trace / two-branch expansion formulas.
3. Global regularity `regularAt_eta` outside `{0} ∪ R_{Q5} ∪ R_{34}` (handling `U = 1`,
   `nm_WU = 0`, and `cb_h = 0` via `G_sq_cancellation` and `a`-elimination symmetry).
4. Finite splitting field `L / K5`, nondegenerate sheet extraction `(a r, b r, r, V r) ∈ L^4`
   for every `r ∈ R_{34}`, and the exact simple-pole residue identity
   `CrossedRationalResidue.residue r eta_L = -P18_of ... / (81 * (J_fib ...).det)`. -/

noncomputable section
namespace SymmetricSexticResidual.CoverResidue
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.SheetCalculus
  SymmetricSexticResidual.CoverAlgebra QuadraticCovers CrossedRationalResidue Polynomial
open scoped BigOperators Matrix

/-- `SL(2)` shear invariance of the quadratic 3-form `m2*d10 - m1*d20 + m0*d21` under `t = t' + T*v`. -/
lemma numM_shear_inv {F : Type*} [Field F] [CharZero F] (mi : Fin 10) (S Q T a b U V : F) :
    numM mi a b (S - a * T) (Q - b * T) U V =
      let a2' := dH_dS a b U V
      let a0' := dH_dS S Q U V
      let a1' := dH_dS (a + S) (b + Q) U V - a2' - a0'
      let b2' := dH_dQ a b 0 U V
      let b0' := dH_dQ S Q 1 U V
      let b1' := (dH_dQ (a + S) (b + Q) 0 U V - b2' - dH_dQ S Q 0 U V) + (10 / 7) * b * U * V
      let d20' := a2' * b0' - a0' * b2'
      let d21' := a2' * b1' - a1' * b2'
      let d10' := a1' * b0' - a0' * b1'
      let (m2', m1', m0') : F × F × F := match mi with
        | 0 => (a ^ 2, 2 * a * S, S ^ 2)
        | 1 => (a * b, a * Q + b * S, S * Q)
        | 2 => (b ^ 2, 2 * b * Q, Q ^ 2)
        | 3 => (a, a * T + S, S * T)
        | 4 => (0, a, S)
        | 5 => (b, b * T + Q, Q * T)
        | 6 => (0, b, Q)
        | 7 => (1, 2 * T, T ^ 2)
        | 8 => (0, 1, T)
        | 9 => (0, 0, 1)
      (1 / 16) * (m2' * d10' - m1' * d20' + m0' * d21') := by
  have hshear (a2 a1 a0 b2 b1 b0 m2 m1 m0 : F) :
      let a1' := a1 + 2 * T * a2; let a0' := a0 + T * a1 + T ^ 2 * a2
      let b1' := b1 + 2 * T * b2; let b0' := b0 + T * b1 + T ^ 2 * b2
      let m1' := m1 + 2 * T * m2; let m0' := m0 + T * m1 + T ^ 2 * m2
      m2 * (a1 * b0 - a0 * b1) - m1 * (a2 * b0 - a0 * b2) + m0 * (a2 * b1 - a1 * b2) =
      m2 * (a1' * b0' - a0' * b1') - m1' * (a2 * b0' - a0' * b2) + m0' * (a2 * b1' - a1' * b2) := by
    ring
  have ha1' : q1_a1 a b (S - a * T) (Q - b * T) U V + 2 * T * q1_a2 a b U V =
      dH_dS (a + S) (b + Q) U V - dH_dS a b U V - dH_dS S Q U V := by
    simp only [q1_a1, q1_a2, dH_dS]; ring
  have ha0' : q1_a0 (S - a * T) (Q - b * T) U V + T * q1_a1 a b (S - a * T) (Q - b * T) U V +
      T ^ 2 * q1_a2 a b U V = dH_dS S Q U V := by
    simp only [q1_a0, q1_a1, q1_a2, dH_dS]; ring
  have hb1' : q2_b1 a b (S - a * T) (Q - b * T) U V + 2 * T * q2_b2 a b U V =
      (dH_dQ (a + S) (b + Q) 0 U V - dH_dQ a b 0 U V - dH_dQ S Q 0 U V) + (10 / 7) * b * U * V := by
    simp only [q2_b1, q2_b2, dH_dQ]; ring
  have hb0' : q2_b0 (S - a * T) (Q - b * T) U V + T * q2_b1 a b (S - a * T) (Q - b * T) U V +
      T ^ 2 * q2_b2 a b U V = dH_dQ S Q 1 U V := by
    simp only [q2_b0, q2_b1, q2_b2, dH_dQ]; ring
  dsimp only [numM]
  fin_cases mi <;>
    (dsimp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk];
     rw [hshear (q1_a2 a b U V) (q1_a1 a b (S - a * T) (Q - b * T) U V) (q1_a0 (S - a * T) (Q - b * T) U V)
       (q2_b2 a b U V) (q2_b1 a b (S - a * T) (Q - b * T) U V) (q2_b0 (S - a * T) (Q - b * T) U V)];
     rw [ha1', ha0', hb1', hb0'];
     dsimp only [q1_a2, q2_b2];
     ring)

/-- Every `numM mi` along any affine line `(a(z), b(z))` has degree `≤ 3` in `z`. -/
lemma numM_isPolyDeg3 {F : Type*} [Field F] [CharZero F]
    (mi : Fin 10) (S Q T U V a1 a0 b1 b0 : F) :
    IsPolyDeg 3 (fun z => numM mi (a1 * z + a0) (b1 * z + b0)
      (S - (a1 * z + a0) * T) (Q - (b1 * z + b0) * T) U V) := by
  have hfun : (fun z => numM mi (a1 * z + a0) (b1 * z + b0)
      (S - (a1 * z + a0) * T) (Q - (b1 * z + b0) * T) U V) = fun z =>
      let a := a1 * z + a0; let b := b1 * z + b0
      let a2' := dH_dS a b U V
      let a0' := dH_dS S Q U V
      let a1' := dH_dS (a + S) (b + Q) U V - a2' - a0'
      let b2' := dH_dQ a b 0 U V
      let b0' := dH_dQ S Q 1 U V
      let b1' := (dH_dQ (a + S) (b + Q) 0 U V - b2' - dH_dQ S Q 0 U V) + (10 / 7) * b * U * V
      let d20' := a2' * b0' - a0' * b2'
      let d21' := a2' * b1' - a1' * b2'
      let d10' := a1' * b0' - a0' * b1'
      let (m2', m1', m0') : F × F × F := match mi with
        | 0 => (a ^ 2, 2 * a * S, S ^ 2)
        | 1 => (a * b, a * Q + b * S, S * Q)
        | 2 => (b ^ 2, 2 * b * Q, Q ^ 2)
        | 3 => (a, a * T + S, S * T)
        | 4 => (0, a, S)
        | 5 => (b, b * T + Q, Q * T)
        | 6 => (0, b, Q)
        | 7 => (1, 2 * T, T ^ 2)
        | 8 => (0, 1, T)
        | 9 => (0, 0, 1)
      (1 / 16) * (m2' * d10' - m1' * d20' + m0' * d21') :=
    funext (fun z => numM_shear_inv mi S Q T (a1 * z + a0) (b1 * z + b0) U V)
  rw [hfun]
  have ha : IsPolyDeg 1 (fun z => a1 * z + a0) := IsPolyDeg.linear a1 a0
  have hb : IsPolyDeg 1 (fun z => b1 * z + b0) := IsPolyDeg.linear b1 b0
  have ha2' : IsPolyDeg 2 (fun z => dH_dS (a1 * z + a0) (b1 * z + b0) U V) := by
    have h1 := ((ha.sub (hb.smul_left 3)).sq).smul_left (-(4 / 81)) |>.smul_right (U ^ 2) |>.smul_right V
    have h2 := (((ha.sq.smul_left (143 / 81)).sub ((ha.mul hb).smul_left (184 / 27))).add
      (hb.sq.smul_left (52 / 9))).smul_right U |>.smul_right V
    have h3 := (((ha.smul_left 5).sub (hb.smul_left 9)).mul
      ((ha.smul_left 15).sub (hb.smul_left 9))).smul_left (25 / 243) |>.smul_right V
    exact ((h1.add h2).sub h3).congr (fun z => by simp only [dH_dS]; ring)
  have hb2' : IsPolyDeg 2 (fun z => dH_dQ (a1 * z + a0) (b1 * z + b0) 0 U V) := by
    have h1 := ((ha.sub (hb.smul_left 3)).sq).smul_left (4 / 27) |>.smul_right (U ^ 2) |>.smul_right V
    have h2 := (((ha.sq.smul_left (-(92 / 27))).add ((ha.mul hb).smul_left (104 / 9))).sub
      (hb.sq.smul_left (22 / 3))).smul_right U |>.smul_right V
    have h3 := (ha.mul ((ha.smul_left 5).sub (hb.smul_left 9))).smul_left (50 / 27) |>.smul_right V
    exact ((h1.add h2).add h3).congr (fun z => by simp only [dH_dQ]; ring)
  -- Notice `a1'` and `b1'` are linear in `(a, b)`!
  have ha1'_eq : ∀ z : F, dH_dS ((a1 * z + a0) + S) ((b1 * z + b0) + Q) U V -
      dH_dS (a1 * z + a0) (b1 * z + b0) U V - dH_dS S Q U V =
      (a1 * z + a0) * (-(8 / 81) * (S - 3 * Q) * U ^ 2 * V + ((286 / 81) * S - (184 / 27) * Q) * U * V -
        (25 / 243) * (150 * S - 180 * Q) * V) +
      (b1 * z + b0) * ((24 / 81) * (S - 3 * Q) * U ^ 2 * V + (-(184 / 27) * S + (104 / 9) * Q) * U * V -
        (25 / 243) * (-180 * S + 162 * Q) * V) := by
    intro z; simp only [dH_dS]; ring
  have hb1'_eq : ∀ z : F, (dH_dQ ((a1 * z + a0) + S) ((b1 * z + b0) + Q) 0 U V -
      dH_dQ (a1 * z + a0) (b1 * z + b0) 0 U V - dH_dQ S Q 0 U V) + (10 / 7) * (b1 * z + b0) * U * V =
      (a1 * z + a0) * ((8 / 27) * (S - 3 * Q) * U ^ 2 * V + (-(184 / 27) * S + (104 / 9) * Q) * U * V +
        (50 / 27) * (10 * S - 9 * Q) * V) +
      (b1 * z + b0) * (-(24 / 27) * (S - 3 * Q) * U ^ 2 * V + ((104 / 9) * S - (44 / 3) * Q + 10 / 7) * U * V +
        (50 / 27) * (-9 * S) * V) := by
    intro z; simp only [dH_dQ]; ring
  have ha1' : IsPolyDeg 1 (fun z => dH_dS ((a1 * z + a0) + S) ((b1 * z + b0) + Q) U V -
      dH_dS (a1 * z + a0) (b1 * z + b0) U V - dH_dS S Q U V) := by
    simp_rw [ha1'_eq]; exact (ha.smul_right _).add (hb.smul_right _)
  have hb1' : IsPolyDeg 1 (fun z => (dH_dQ ((a1 * z + a0) + S) ((b1 * z + b0) + Q) 0 U V -
      dH_dQ (a1 * z + a0) (b1 * z + b0) 0 U V - dH_dQ S Q 0 U V) + (10 / 7) * (b1 * z + b0) * U * V) := by
    simp_rw [hb1'_eq]; exact (ha.smul_right _).add (hb.smul_right _)
  have hd10 : IsPolyDeg 1 (fun z =>
      (dH_dS ((a1 * z + a0) + S) ((b1 * z + b0) + Q) U V - dH_dS (a1 * z + a0) (b1 * z + b0) U V - dH_dS S Q U V) *
        dH_dQ S Q 1 U V -
      dH_dS S Q U V * ((dH_dQ ((a1 * z + a0) + S) ((b1 * z + b0) + Q) 0 U V -
        dH_dQ (a1 * z + a0) (b1 * z + b0) 0 U V - dH_dQ S Q 0 U V) + (10 / 7) * (b1 * z + b0) * U * V)) :=
    (ha1'.smul_right _).sub (hb1'.smul_left _)
  have hd20 : IsPolyDeg 2 (fun z =>
      dH_dS (a1 * z + a0) (b1 * z + b0) U V * dH_dQ S Q 1 U V -
      dH_dS S Q U V * dH_dQ (a1 * z + a0) (b1 * z + b0) 0 U V) :=
    (ha2'.smul_right _).sub (hb2'.smul_left _)
  have hd21 : IsPolyDeg 3 (fun z =>
      dH_dS (a1 * z + a0) (b1 * z + b0) U V * ((dH_dQ ((a1 * z + a0) + S) ((b1 * z + b0) + Q) 0 U V -
        dH_dQ (a1 * z + a0) (b1 * z + b0) 0 U V - dH_dQ S Q 0 U V) + (10 / 7) * (b1 * z + b0) * U * V) -
      (dH_dS ((a1 * z + a0) + S) ((b1 * z + b0) + Q) U V - dH_dS (a1 * z + a0) (b1 * z + b0) U V - dH_dS S Q U V) *
        dH_dQ (a1 * z + a0) (b1 * z + b0) 0 U V) :=
    (ha2'.mul hb1').sub ((ha1'.mul hb2').mono (by omega))
  have hcomb {m2 m1 : F → F} {m0 : F} (hm2 : IsPolyDeg 2 m2) (hm1 : IsPolyDeg 1 m1) :
      IsPolyDeg 3 (fun z => (1 / 16 : F) * (m2 z * _ - m1 z * _ + m0 * _)) :=
    (((hm2.mul hd10).sub ((hm1.mul hd20).mono (by omega))).add (hd21.smul_left m0)).smul_left (1 / 16)
  fin_cases mi
  · exact hcomb ha.sq ((ha.smul_left 2).smul_right S)
  · exact hcomb (ha.mul hb) ((ha.smul_right Q).add (hb.smul_right S))
  · exact hcomb hb.sq ((hb.smul_left 2).smul_right Q)
  · exact hcomb (ha.mono (by omega)) ((ha.smul_right T).add ((IsPolyDeg.const S).mono (by omega)))
  · exact hcomb ((IsPolyDeg.const 0).mono (by omega)) ha
  · exact hcomb (hb.mono (by omega)) ((hb.smul_right T).add ((IsPolyDeg.const Q).mono (by omega)))
  · exact hcomb ((IsPolyDeg.const 0).mono (by omega)) hb
  · exact hcomb ((IsPolyDeg.const 1).mono (by omega)) ((IsPolyDeg.const (2 * T)).mono (by omega))
  · exact hcomb ((IsPolyDeg.const 0).mono (by omega)) ((IsPolyDeg.const 1).mono (by omega))
  · exact hcomb ((IsPolyDeg.const 0).mono (by omega)) ((IsPolyDeg.const 0).mono (by omega))

/-- `SheetCalculus.P18_of` along any affine line `(a(z), b(z))` has degree `≤ 4` in `z`. -/
lemma P18_of_isPolyDeg4 {F : Type*} [Field F] [CharZero F]
    (S Q T x y U V a1 a0 b1 b0 : F) :
    IsPolyDeg 4 (fun z => SheetCalculus.P18_of S Q T x y (a1 * z + a0) (b1 * z + b0) U V) := by
  have ha : IsPolyDeg 1 (fun z => a1 * z + a0) := IsPolyDeg.linear a1 a0
  have hb : IsPolyDeg 1 (fun z => b1 * z + b0) := IsPolyDeg.linear b1 b0
  have hm := fun i => numM_isPolyDeg3 i S Q T U V a1 a0 b1 b0
  have hA0U : IsPolyDeg 3 (fun z => A_0U (a1 * z + a0) (b1 * z + b0)
      (S - (a1 * z + a0) * T) (Q - (b1 * z + b0) * T) U V) := by
    refine ((((((hm 0).smul_left 5).sub ((hm 1).smul_left 9)).smul_left (-(19708 / 1257375))).add
      ((((hm 1).smul_left 5).sub ((hm 2).smul_left 9)).smul_left (1472 / 1257375))).sub
      ((((hm 3).smul_left 5).sub ((hm 5).smul_left 9)).smul_left (16 / 729)) |>.add
      ((((hm 4).smul_left 5).sub ((hm 6).smul_left 9)).smul_left (188 / 2025))).congr
      (fun z => by simp only [A_0U])
  have hA0V : IsPolyDeg 3 (fun z => A_0V (a1 * z + a0) (b1 * z + b0)
      (S - (a1 * z + a0) * T) (Q - (b1 * z + b0) * T) U V) := by
    refine ((((((hm 3).smul_left 5).sub ((hm 4).smul_left 9)).smul_left (-(892 / 3645))).add
      ((((hm 5).smul_left 5).sub ((hm 6).smul_left 9)).smul_left (40 / 81))).sub
      ((((hm 7).smul_left 5).sub ((hm 8).smul_left 9)).smul_left (112 / 2395)) |>.add
      ((((hm 8).smul_left 5).sub ((hm 9).smul_left 9)).smul_left (392 / 11975))).congr
      (fun z => by simp only [A_0V])
  have hAY : IsPolyDeg 3 (fun z => A_Y (a1 * z + a0) (b1 * z + b0)
      (S - (a1 * z + a0) * T) (Q - (b1 * z + b0) * T) U V) := by
    have t1 := (((((hm 3).smul_left 25).sub ((hm 4).smul_left 45)).sub ((hm 5).smul_left 45)).add
      ((hm 6).smul_left 81)).smul_left (-(100 / 243))
    have t2 := (((((((hm 0).smul_left 5).sub ((hm 1).smul_left 9)).smul_left (-(907876 / 33949125))).add
      ((((hm 1).smul_left 5).sub ((hm 2).smul_left 9)).smul_left (2258324 / 33949125))).add
      ((((hm 3).smul_left 5).sub ((hm 5).smul_left 9)).smul_left (8 / 243))).sub
      ((((hm 4).smul_left 5).sub ((hm 6).smul_left 9)).smul_left (64 / 675))).smul_left V
    have t3 := (((((hm 0).add ((hm 6).smul_left (2790 / 77))).add ((hm 8).smul_left 28)).sub
      ((hm 9).smul_left (5904 / 77))).smul_left (-(123236 / 24249375)) |>.add
      (((((hm 1).add ((hm 6).smul_left (927 / 77))).add ((hm 8).smul_left (49 / 5))).sub
      ((hm 9).smul_left (21159 / 770))).smul_left (492944 / 33949125))).smul_left (U * V)
    exact ((t1.add t2).add t3).congr (fun z => by simp only [A_Y])
  have hAX : IsPolyDeg 3 (fun z => A_X (a1 * z + a0) (b1 * z + b0)
      (S - (a1 * z + a0) * T) (Q - (b1 * z + b0) * T) U V) := by
    refine ((((((hm 3).smul_left 5).sub ((hm 4).smul_left 9)).smul_left (-(8 / 405))).sub
      ((((hm 7).smul_left 5).sub ((hm 8).smul_left 9)).smul_left (476 / 7185))).add
      ((((hm 8).smul_left 5).sub ((hm 9).smul_left 9)).smul_left (6916 / 35925))).smul_left U |>.congr
      (fun z => by simp only [A_X])
  have hM0 : IsPolyDeg 3 (fun z => A_0U (a1 * z + a0) (b1 * z + b0)
      (S - (a1 * z + a0) * T) (Q - (b1 * z + b0) * T) U V / U +
      A_0V (a1 * z + a0) (b1 * z + b0) (S - (a1 * z + a0) * T) (Q - (b1 * z + b0) * T) U V / V) :=
    (hA0U.div_const U).add (hA0V.div_const V)
  have hdot (v : Fin 3 → F) : IsPolyDeg 1 (fun z => dot_ab v (a1 * z + a0) (b1 * z + b0)) := by
    unfold dot_ab
    exact ((ha.smul_left (v 0)).add (hb.smul_left (v 1))).add ((IsPolyDeg.const (v 2)).mono (by omega))
  have hqY : IsPolyDeg 1 (fun z => dot_ab (QY_num S Q T x y U V) (a1 * z + a0) (b1 * z + b0) / v_of V) :=
    (hdot _).div_const _
  have hqX : IsPolyDeg 1 (fun z => dot_ab (QX_num S Q T x y U V) (a1 * z + a0) (b1 * z + b0) / u_of U) :=
    (hdot _).div_const _
  have hcA1 : IsPolyDeg 1 (fun z => cA1_of S Q T (a1 * z + a0) (b1 * z + b0) U V) := by
    unfold cA1_of
    exact ((ha.smul_left _).add (hb.smul_left _)).add ((IsPolyDeg.const _).mono (by omega))
  have hq1 : IsPolyDeg 1 (fun z =>
      H0_of S Q T * A1_of S Q U V * (dot_ab (QY_num S Q T x y U V) (a1 * z + a0) (b1 * z + b0) / v_of V) +
      H0_of S Q T * B1_of T U V * (dot_ab (QX_num S Q T x y U V) (a1 * z + a0) (b1 * z + b0) / u_of U) +
      (cA1_of S Q T (a1 * z + a0) (b1 * z + b0) U V / v_of V) * EB_of S Q T x y U V) :=
    ((hqY.smul_left _).add (hqX.smul_left _)).add ((hcA1.div_const _).smul_right _)
  unfold P18_of
  exact (hM0.mul hq1).add (((hAY.mul hqY).add (hAX.mul hqX)).smul_right _)

/-- Any root in a finite extension `L / K5` of a nonzero polynomial over `K5` whose coefficients
are killed by `δ 3` is itself killed by `δL 3`. -/
lemma δL3_eq_zero_of_isRoot {L : Type*} [Field L] [Algebra K5 L] [FiniteDimensional K5 L]
    (P : K5[X]) (hP : P ≠ 0) (hδ : ∀ k : ℕ, δ 3 (P.coeff k) = 0)
    (r : L) (hr : (P.map (algebraMap K5 L)).eval r = 0) :
    δL (L := L) 3 r = 0 := by
  let _ : Algebra ℤ K5 := Ring.toIntAlgebra K5
  let _ : Algebra ℤ L := Ring.toIntAlgebra L
  induction hd : P.natDegree using Nat.strong_induction_on generalizing P with
  | ind n ih =>
    have hdeg_pos : 0 < P.natDegree := by
      by_contra h0; push Not at h0
      have hC := Polynomial.eq_C_of_natDegree_eq_zero (Nat.le_zero.mp h0)
      rw [hC, Polynomial.map_C, Polynomial.eval_C] at hr
      have hc0 : P.coeff 0 = 0 := (algebraMap K5 L).injective (by simpa using hr)
      exact hP (by rw [hC, hc0, map_zero])
    have hev_deriv : δL (L := L) 3 ((P.map (algebraMap K5 L)).eval r) =
        (P.derivative.map (algebraMap K5 L)).eval r * δL (L := L) 3 r := by
      rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le Polynomial.natDegree_map_le),
        map_sum]
      have hterm (k : ℕ) :
          δL (L := L) 3 ((P.map (algebraMap K5 L)).coeff k * r ^ k) =
            (algebraMap K5 L) ((k : K5) * P.coeff k) * r ^ (k - 1) * δL (L := L) 3 r := by
        rw [Polynomial.coeff_map, (δL (L := L) 3).leibniz, δL_apply, hδ k, map_zero,
          smul_eq_mul, smul_eq_mul, mul_zero, add_zero, (δL (L := L) 3).leibniz_pow,
          smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast]
        ring
      simp_rw [hterm]
      rw [Nat.succ_eq_add_one, Finset.sum_range_succ']
      simp only [Nat.cast_zero, zero_mul, map_zero, add_zero, Nat.add_sub_cancel]
      rw [← Finset.sum_mul]
      congr 1
      rw [Polynomial.eval_eq_sum_range' (Nat.lt_of_le_of_lt Polynomial.natDegree_map_le
        (Polynomial.natDegree_derivative_lt (by omega : P.natDegree ≠ 0)))]
      apply Finset.sum_congr rfl; intro k _
      rw [Polynomial.coeff_map, Polynomial.coeff_derivative]
      simp only [Nat.cast_add, Nat.cast_one, map_mul, map_add, map_natCast, map_one]
      ring
    rw [hr, map_zero] at hev_deriv
    by_cases hPd : (P.derivative.map (algebraMap K5 L)).eval r = 0
    · have hPd_ne : P.derivative ≠ 0 := by
        intro h0
        have hc := congrArg (fun f : K5[X] => f.coeff (P.natDegree - 1)) h0
        rw [Polynomial.coeff_zero, Polynomial.coeff_derivative, Nat.sub_add_cancel hdeg_pos] at hc
        have hlc : P.coeff P.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
        have hnat : ((P.natDegree : K5)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have hc' : P.coeff P.natDegree * (P.natDegree : K5) = 0 := by
          simpa [Nat.cast_sub hdeg_pos] using hc
        exact mul_ne_zero hlc hnat hc'
      have hδd : ∀ k : ℕ, δ 3 (P.derivative.coeff k) = 0 := by
        intro k
        rw [Polynomial.coeff_derivative, (δ 3).leibniz, hδ (k + 1), smul_eq_mul, smul_eq_mul,
          mul_zero, add_zero]
        have hnat : δ 3 ((k : K5) + 1) = 0 := by
          rw [map_add, (δ 3).map_natCast, (δ 3).map_one_eq_zero, add_zero]
        rw [hnat, mul_zero]
      exact ih P.derivative.natDegree (by rw [← hd]; exact Polynomial.natDegree_derivative_lt (by omega))
        P.derivative hPd_ne hδd hPd rfl
    · exact (mul_eq_zero.mp hev_deriv.symm).resolve_left hPd

/-! ### Section 2: Quadratic Cover Field `A_C` and Explicit Cover 1-Form `eta : RatFunc K5` -/

abbrev toRat : K5[X] →+* RatFunc K5 := algebraMap K5[X] (RatFunc K5)

def E0_poly : (RatFunc K5)[X] :=
  X ^ 2 + C (toRat k5Params.bW) * X + C (toRat k5Params.cW)

lemma E0_poly_monic : E0_poly.Monic := by
  rw [E0_poly]
  have hdeg : (C (toRat k5Params.bW) * X + C (toRat k5Params.cW)).degree < (X ^ 2 : (RatFunc K5)[X]).degree := by
    refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (degree_C_mul_X_le _) (by rw [degree_X_pow]; exact WithBot.coe_lt_coe.mpr (by omega))
    · exact lt_of_le_of_lt degree_C_le (by rw [degree_X_pow]; exact WithBot.coe_lt_coe.mpr (by omega))
  rw [add_assoc]
  exact (monic_X_pow 2).add_of_left hdeg

lemma E0_poly_natDegree : E0_poly.natDegree = 2 := by
  rw [E0_poly, add_assoc]
  have hdeg : (C (toRat k5Params.bW) * X + C (toRat k5Params.cW)).natDegree < 2 := by
    refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (natDegree_C_mul_le _ _) (by simp)
    · simp
  rw [natDegree_add_eq_left_of_natDegree_lt (by simpa using hdeg), natDegree_X_pow]

/-- `disc_E0 = bW^2 - 4 * cW` is not a square in `K5[X]`, proved via `evLoc` mod 1009. -/
lemma E0_poly_irreducible : Irreducible E0_poly := by
  -- A monic degree-2 polynomial over a field is irreducible iff it has no root.
  by_contra hred
  have hdeg2 : E0_poly.natDegree = 2 := E0_poly_natDegree
  have hroot : ∃ w : RatFunc K5, E0_poly.eval w = 0 := by
    rw [irreducible_iff] at hred
    push Not at hred
    obtain ⟨p, q, hpq, hpu, hqu⟩ := hred (by
      intro hu; have := Polynomial.natDegree_eq_zero_of_isUnit hu; omega)
    have hp0 : p ≠ 0 := by intro h; rw [h, zero_mul] at hpq; exact E0_poly_monic.ne_zero hpq
    have hq0 : q ≠ 0 := by intro h; rw [h, mul_zero] at hpq; exact E0_poly_monic.ne_zero hpq
    have hsum : p.natDegree + q.natDegree = 2 := by rw [← natDegree_mul hp0 hq0, ← hpq, hdeg2]
    have hp1 : 1 ≤ p.natDegree := by
      by_contra hlt; push Not at hlt
      exact hpu (Polynomial.isUnit_iff_degree_eq_zero.mpr (by
        rw [Polynomial.degree_eq_natDegree hp0]; exact_mod_cast (by omega : p.natDegree = 0)))
    have hq1 : 1 ≤ q.natDegree := by
      by_contra hlt; push Not at hlt
      exact hqu (Polynomial.isUnit_iff_degree_eq_zero.mpr (by
        rw [Polynomial.degree_eq_natDegree hq0]; exact_mod_cast (by omega : q.natDegree = 0)))
    have hp_deg : p.natDegree = 1 := by omega
    set r0 := -p.coeff 0 / p.coeff 1
    refine ⟨r0, ?_⟩
    have hc1 : p.coeff 1 ≠ 0 := by rw [← hp_deg]; exact leadingCoeff_ne_zero.mpr hp0
    have hp_eq : p = C (p.coeff 1) * X + C (p.coeff 0) := by
      ext k
      rcases k with _ | _ | k
      · simp
      · simp
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < k + 2)]
        simp
    rw [hpq, eval_mul, hp_eq]
    simp only [eval_add, eval_mul, eval_C, eval_X, r0]
    rw [mul_div_cancel₀ _ hc1, neg_add_cancel, zero_mul]
  obtain ⟨w, hw⟩ := hroot
  simp only [E0_poly, eval_add, eval_mul, eval_pow, eval_C, eval_X] at hw
  have hsq : (2 * w + toRat k5Params.bW) ^ 2 = toRat k5Params.disc_E0 := by
    rw [CoverParams.disc_E0, map_sub, map_pow, map_mul, map_ofNat]
    linear_combination 4 * hw
  -- Clear denominator via coprime num/denom of `2 * w + toRat bW` in PID `K5[X]`.
  let u := 2 * w + toRat k5Params.bW
  let P := u.num; let Q := u.denom
  have hQ0 : Q ≠ 0 := u.denom_ne_zero
  have hu_eq : u = toRat P / toRat Q := u.num_div_denom.symm
  have hPQ : P ^ 2 = Q ^ 2 * k5Params.disc_E0 := by
    apply IsFractionRing.injective K5[X] (RatFunc K5)
    simp only [map_pow, map_mul]
    have hQrat : toRat Q ≠ 0 := polynomialMap_ne_zero hQ0
    have h2 : (toRat P / toRat Q) ^ 2 = toRat k5Params.disc_E0 := by rwa [← hu_eq]
    rw [div_pow, div_eq_iff (pow_ne_zero 2 hQrat)] at h2
    linear_combination h2
  have hcop : IsCoprime Q P := u.isCoprime_num_denom.symm
  have hQdvd : Q ∣ 1 := by
    have h1 : Q ∣ P ^ 2 := ⟨Q * k5Params.disc_E0, by linear_combination hPQ⟩
    exact (hcop.pow_right (n := 2)).dvd_of_dvd_mul_left (by simpa using h1)
  have hQunit : IsUnit Q := isUnit_of_dvd_one hQdvd
  obtain ⟨cQ, hcQ_u, hcQ⟩ := Polynomial.isUnit_iff.mp hQunit
  let f : K5[X] := C cQ⁻¹ * P
  have hf_sq : f ^ 2 = k5Params.disc_E0 := by
    dsimp only [f]
    rw [mul_pow, ← map_pow, hPQ, ← hcQ, ← map_pow, ← mul_assoc, ← map_mul,
      ← mul_pow, inv_mul_cancel₀ hcQ_u.ne_zero, one_pow, map_one, one_mul]
  -- Extract polynomial identity `d3 * (4 * c4^2 * d2 - d3^2) = 8 * c4^4 * d1` in `K5` and specialize via `evLoc`!
  have hdisc_deg : k5Params.disc_E0.natDegree ≤ 4 := by
    rw [CoverParams.disc_E0]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact natDegree_pow_le.trans (by
        have hb : k5Params.bW.natDegree ≤ 2 := by
          rw [CoverParams.bW]; exact (natDegree_C_mul_le _ _).trans (by
            rw [CoverParams.Bv, CoverParams.quadU]
            refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le (by simp) ?_)) ?_)
            · exact (natDegree_C_mul_le _ _).trans (by simp)
            · exact (natDegree_C_mul_le _ _).trans (by simp))
        omega)
    · refine (natDegree_mul_le).trans ?_
      have hc : k5Params.cW.natDegree ≤ 2 := by
        rw [CoverParams.cW]; exact (natDegree_C_mul_le _ _).trans (by simp)
      simp only [natDegree_ofNat, zero_add]; omega
  have hdisc_c4_loc : evLoc (locParams.disc_E0.coeff 4) = 309 := by
    rw [← Polynomial.coeff_map, CoverParams.map_disc_E0, locParams_map_evLoc,
      ← Poly1009.toPoly_c_disc_E0, Poly1009.toPoly_coeff_getD]
    decide
  have hdisc_map : locParams.disc_E0.map LocK5.subtype = k5Params.disc_E0 :=
    CoverParams.map_disc_E0 locParams LocK5.subtype
  have hdisc_coeff (k : ℕ) : (locParams.disc_E0.coeff k : K5) = k5Params.disc_E0.coeff k := by
    rw [← hdisc_map, Polynomial.coeff_map]; rfl
  have hdisc_c4_ne : k5Params.disc_E0.coeff 4 ≠ 0 := by
    rw [← hdisc_coeff 4]
    exact LocK5.ne_zero_of_evLoc (by rw [hdisc_c4_loc]; decide)
  have hf_ne : f ≠ 0 := by
    intro h0; rw [h0, zero_pow (by omega)] at hf_sq
    exact hdisc_c4_ne (by rw [← hf_sq, Polynomial.coeff_zero])
  have hf_deg : f.natDegree = 2 := by
    have h4 : k5Params.disc_E0.natDegree = 4 :=
      le_antisymm hdisc_deg (Polynomial.le_natDegree_of_ne_zero hdisc_c4_ne)
    have h2 : 2 * f.natDegree = 4 := by
      rw [← h4, ← hf_sq, Polynomial.natDegree_pow]
    omega
  have hf_form : f = C (f.coeff 0) + C (f.coeff 1) * X + C (f.coeff 2) * X ^ 2 := by
    ext k
    rcases k with _ | _ | _ | k
    · simp
    · simp
    · simp
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < k + 3)]
      simp
  set f0 := f.coeff 0; set f1 := f.coeff 1; set f2 := f.coeff 2
  have hexp : f ^ 2 = C (f0 ^ 2) + C (2 * f0 * f1) * X + C (2 * f0 * f2 + f1 ^ 2) * X ^ 2 +
      C (2 * f1 * f2) * X ^ 3 + C (f2 ^ 2) * X ^ 4 := by
    rw [hf_form]
    simp only [map_add, map_mul, map_pow, map_ofNat]
    ring
  have hf_sq_exp : C (f0 ^ 2) + C (2 * f0 * f1) * X + C (2 * f0 * f2 + f1 ^ 2) * X ^ 2 +
      C (2 * f1 * f2) * X ^ 3 + C (f2 ^ 2) * X ^ 4 = k5Params.disc_E0 :=
    hexp.symm.trans hf_sq
  have hf2_sq : f2 ^ 2 = k5Params.disc_E0.coeff 4 := by
    have h := congrArg (fun p : K5[X] => p.coeff 4) hf_sq_exp
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C,
      Polynomial.coeff_X, Polynomial.coeff_X_pow] at h
    simpa using h
  have hd3 : 2 * f1 * f2 = k5Params.disc_E0.coeff 3 := by
    have h := congrArg (fun p : K5[X] => p.coeff 3) hf_sq_exp
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C,
      Polynomial.coeff_X, Polynomial.coeff_X_pow] at h
    simpa using h
  have hd2 : 2 * f0 * f2 + f1 ^ 2 = k5Params.disc_E0.coeff 2 := by
    have h := congrArg (fun p : K5[X] => p.coeff 2) hf_sq_exp
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C,
      Polynomial.coeff_X, Polynomial.coeff_X_pow] at h
    simpa using h
  have hd1 : 2 * f0 * f1 = k5Params.disc_E0.coeff 1 := by
    have h := congrArg (fun p : K5[X] => p.coeff 1) hf_sq_exp
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C,
      Polynomial.coeff_X, Polynomial.coeff_X_pow] at h
    simpa using h
  have hrel : k5Params.disc_E0.coeff 3 * (4 * k5Params.disc_E0.coeff 4 * k5Params.disc_E0.coeff 2 -
      k5Params.disc_E0.coeff 3 ^ 2) = 8 * k5Params.disc_E0.coeff 4 ^ 2 * k5Params.disc_E0.coeff 1 := by
    rw [← hf2_sq, ← hd3, ← hd2, ← hd1]; ring
  have hrel_loc : locParams.disc_E0.coeff 3 * (4 * locParams.disc_E0.coeff 4 * locParams.disc_E0.coeff 2 -
      locParams.disc_E0.coeff 3 ^ 2) = 8 * locParams.disc_E0.coeff 4 ^ 2 * locParams.disc_E0.coeff 1 := by
    apply Subtype.ext
    push_cast [hdisc_coeff]
    exact hrel
  have hev := congrArg evLoc hrel_loc
  simp only [map_mul, map_sub, map_pow, map_ofNat] at hev
  have hevk (k : ℕ) : evLoc (locParams.disc_E0.coeff k) = Poly1009.c_disc_E0.getD k 0 := by
    rw [← Polynomial.coeff_map, CoverParams.map_disc_E0, locParams_map_evLoc,
      ← Poly1009.toPoly_c_disc_E0, Poly1009.toPoly_coeff_getD]
  rw [hevk 1, hevk 2, hevk 3, hevk 4] at hev
  exact (by decide : Poly1009.c_disc_E0.getD 3 0 * (4 * Poly1009.c_disc_E0.getD 4 0 *
    Poly1009.c_disc_E0.getD 2 0 - Poly1009.c_disc_E0.getD 3 0 ^ 2) ≠
    8 * Poly1009.c_disc_E0.getD 4 0 ^ 2 * Poly1009.c_disc_E0.getD 1 0) hev

instance : Fact (Irreducible E0_poly) := ⟨E0_poly_irreducible⟩

/-- The quadratic function field `A_C = K5(U)[W] / (W^2 + bW * W + cW)` (`W = U * V`). -/
abbrev A_C := AdjoinRoot E0_poly

instance : CharZero A_C :=
  charZero_of_injective_ringHom ((algebraMap (RatFunc K5) A_C).comp (algebraMap K5 (RatFunc K5))).injective

instance : FiniteDimensional (RatFunc K5) A_C :=
  Module.Finite.of_basis (AdjoinRoot.powerBasis' E0_poly_monic).basis

def W_C : A_C := AdjoinRoot.root E0_poly
def ιC_rat : RatFunc K5 →+* A_C := algebraMap (RatFunc K5) A_C
def ιC_K5 : K5 →+* A_C := ιC_rat.comp (algebraMap K5 (RatFunc K5))
def U_C : A_C := ιC_rat RatFunc.X
def V_C : A_C := W_C / U_C

lemma W_C_relation :
    W_C ^ 2 + ιC_rat (toRat k5Params.bW) * W_C + ιC_rat (toRat k5Params.cW) = 0 := by
  have he := AdjoinRoot.eval₂_root E0_poly
  change E0_poly.eval₂ ιC_rat W_C = 0 at he
  simpa only [E0_poly, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C] using he

/-- Embed a `PairAlg (RatFunc K5)` element `c0 + c1 * W` into `A_C`. -/
def evalAC (x : PairAlg (RatFunc K5)) : A_C :=
  ιC_rat x.c0 + ιC_rat x.c1 * W_C

lemma evalAC_zero : evalAC (PairAlg.zero : PairAlg (RatFunc K5)) = 0 := by simp [evalAC, PairAlg.zero]
lemma evalAC_one : evalAC (PairAlg.one : PairAlg (RatFunc K5)) = 1 := by simp [evalAC, PairAlg.one]
lemma evalAC_W : evalAC (PairAlg.W : PairAlg (RatFunc K5)) = W_C := by simp [evalAC, PairAlg.W]
lemma evalAC_ofScalar (s : RatFunc K5) : evalAC (PairAlg.ofScalar s) = ιC_rat s := by
  simp [evalAC, PairAlg.ofScalar]
lemma evalAC_add (x y : PairAlg (RatFunc K5)) :
    evalAC (PairAlg.add x y) = evalAC x + evalAC y := by
  simp only [evalAC, PairAlg.add, map_add]; ring
lemma evalAC_sub (x y : PairAlg (RatFunc K5)) :
    evalAC (PairAlg.sub x y) = evalAC x - evalAC y := by
  simp only [evalAC, PairAlg.sub, map_sub]; ring
lemma evalAC_neg (x : PairAlg (RatFunc K5)) :
    evalAC (PairAlg.neg x) = -evalAC x := by
  simp only [evalAC, PairAlg.neg, map_neg]; ring
lemma evalAC_smul (s : RatFunc K5) (x : PairAlg (RatFunc K5)) :
    evalAC (PairAlg.smul s x) = ιC_rat s * evalAC x := by
  simp only [evalAC, PairAlg.smul, map_mul]; ring
lemma evalAC_mul (x y : PairAlg (RatFunc K5)) :
    evalAC (PairAlg.mul (toRat k5Params.bW) (toRat k5Params.cW) x y) = evalAC x * evalAC y := by
  simp only [evalAC, PairAlg.mul, map_add, map_sub, map_mul]
  linear_combination -ιC_rat x.c1 * ιC_rat y.c1 * W_C_relation

/-- Extract `(c0, c1)` coordinates of an element of `A_C` in the power basis `{1, W_C}`. -/
def coordsAC (x : A_C) : PairAlg (RatFunc K5) :=
  let pb := AdjoinRoot.powerBasis' E0_poly_monic
  have hdim : pb.dim = 2 := by rw [AdjoinRoot.powerBasis'_dim, E0_poly_natDegree]
  ⟨pb.basis.repr x ⟨0, by omega⟩, pb.basis.repr x ⟨1, by omega⟩⟩

lemma evalAC_coordsAC (x : A_C) : evalAC (coordsAC x) = x := by
  let pb := AdjoinRoot.powerBasis' E0_poly_monic
  have hdim : pb.dim = 2 := by rw [AdjoinRoot.powerBasis'_dim, E0_poly_natDegree]
  have hsum := (pb.basis.sum_repr x).symm
  rw [show (Finset.univ : Finset (Fin pb.dim)) = {⟨0, by omega⟩, ⟨1, by omega⟩} by
    ext ⟨i, hi⟩; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, Fin.mk.injEq,
      true_iff]; omega] at hsum
  rw [Finset.sum_pair (by simp)] at hsum
  have hb0 : pb.basis ⟨0, by omega⟩ = 1 := by simp [pb, PowerBasis.basis_eq_pow]
  have hb1 : pb.basis ⟨1, by omega⟩ = W_C := by simp [pb, PowerBasis.basis_eq_pow, W_C]
  rw [hb0, hb1] at hsum
  simpa only [evalAC, coordsAC, Algebra.smul_def, ιC_rat, mul_one] using hsum.symm

lemma coordsAC_evalAC (p : PairAlg (RatFunc K5)) : coordsAC (evalAC p) = p := by
  let pb := AdjoinRoot.powerBasis' E0_poly_monic
  have hdim : pb.dim = 2 := by rw [AdjoinRoot.powerBasis'_dim, E0_poly_natDegree]
  have hb0 : pb.basis ⟨0, by omega⟩ = 1 := by simp [pb, PowerBasis.basis_eq_pow]
  have hb1 : pb.basis ⟨1, by omega⟩ = W_C := by simp [pb, PowerBasis.basis_eq_pow, W_C]
  have hev : evalAC p = p.c0 • pb.basis ⟨0, by omega⟩ + p.c1 • pb.basis ⟨1, by omega⟩ := by
    rw [hb0, hb1, evalAC, Algebra.smul_def, Algebra.smul_def, mul_one]; rfl
  ext
  · change pb.basis.repr (evalAC p) ⟨0, by omega⟩ = p.c0
    rw [hev, map_add, map_smul, map_smul, pb.basis.repr_self, pb.basis.repr_self]
    simp
  · change pb.basis.repr (evalAC p) ⟨1, by omega⟩ = p.c1
    rw [hev, map_add, map_smul, map_smul, pb.basis.repr_self, pb.basis.repr_self]
    simp

lemma evalAC_injective : Function.Injective evalAC :=
  Function.LeftInverse.injective coordsAC_evalAC

/-- Explicit trace of `c0 + c1 * W_C` from `A_C` to `RatFunc K5`. -/
lemma trace_AC_evalAC (p : PairAlg (RatFunc K5)) :
    Algebra.trace (RatFunc K5) A_C (evalAC p) = 2 * p.c0 - p.c1 * toRat k5Params.bW := by
  let pb := AdjoinRoot.powerBasis' E0_poly_monic
  have hdim : pb.dim = 2 := by rw [AdjoinRoot.powerBasis'_dim, E0_poly_natDegree]
  rw [Algebra.trace_eq_matrix_trace pb.basis]
  rw [Matrix.trace, show (Finset.univ : Finset (Fin pb.dim)) = {⟨0, by omega⟩, ⟨1, by omega⟩} by
    ext ⟨i, hi⟩; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, Fin.mk.injEq,
      true_iff]; omega]
  rw [Finset.sum_pair (by simp)]
  have hb0 : pb.basis ⟨0, by omega⟩ = 1 := by simp [pb, PowerBasis.basis_eq_pow]
  have hb1 : pb.basis ⟨1, by omega⟩ = W_C := by simp [pb, PowerBasis.basis_eq_pow, W_C]
  have h00 : (Algebra.leftMulMatrix pb.basis (evalAC p)).diag ⟨0, by omega⟩ = p.c0 := by
    rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, hb0, mul_one]
    exact congrArg PairAlg.c0 (coordsAC_evalAC p)
  have h11 : (Algebra.leftMulMatrix pb.basis (evalAC p)).diag ⟨1, by omega⟩ =
      p.c0 - p.c1 * toRat k5Params.bW := by
    rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, hb1, ← evalAC_W, ← evalAC_mul]
    have hc := congrArg PairAlg.c1 (coordsAC_evalAC (PairAlg.mul (toRat k5Params.bW) (toRat k5Params.cW) p PairAlg.W))
    simpa [coordsAC, PairAlg.mul, PairAlg.W] using hc
  rw [h00, h11]; ring

/-- Quadratic Euler trace identity in `A_C`: cancels `disc_E0` identically. -/
lemma trace_AC_euler (x y : PairAlg (RatFunc K5))
    (hnm : PairAlg.nm (toRat k5Params.bW) (toRat k5Params.cW) y ≠ 0) :
    Algebra.trace (RatFunc K5) A_C
      (evalAC x / (evalAC y * (2 * W_C + ιC_rat (toRat k5Params.bW)))) =
    (x.c1 * y.c0 - x.c0 * y.c1) / PairAlg.nm (toRat k5Params.bW) (toRat k5Params.cW) y := by
  have hdisc_ne : toRat k5Params.disc_E0 ≠ 0 := by
    apply polynomialMap_ne_zero
    intro h0
    have hloc : locParams.disc_E0 = 0 :=
      Polynomial.map_injective LocK5.subtype Subtype.val_injective (by rw [CoverParams.map_disc_E0]; exact h0)
    have hc4 := congrArg (fun p : LocK5[X] => evLoc (p.coeff 4)) hloc
    rw [Polynomial.coeff_zero, map_zero, ← Polynomial.coeff_map, CoverParams.map_disc_E0,
      locParams_map_evLoc, ← Poly1009.toPoly_c_disc_E0, Poly1009.toPoly_coeff_getD] at hc4
    exact (by decide : Poly1009.c_disc_E0.getD 4 0 ≠ 0) hc4
  have h2W_sq : (2 * W_C + ιC_rat (toRat k5Params.bW)) ^ 2 = ιC_rat (toRat k5Params.disc_E0) := by
    rw [CoverParams.disc_E0, map_sub, map_pow, map_mul, map_ofNat, map_sub, map_pow, map_mul, map_ofNat]
    linear_combination 4 * W_C_relation
  have h2W_ne : 2 * W_C + ιC_rat (toRat k5Params.bW) ≠ 0 := by
    intro h0; rw [h0, zero_pow (by omega)] at h2W_sq
    exact hdisc_ne (ιC_rat.injective (by simpa using h2W_sq.symm))
  have hy_conj : evalAC y * evalAC (PairAlg.conj (toRat k5Params.bW) y) =
      ιC_rat (PairAlg.nm (toRat k5Params.bW) (toRat k5Params.cW) y) := by
    rw [← evalAC_mul, ← evalAC_ofScalar]
    congr 1; ext <;> (simp only [PairAlg.mul, PairAlg.conj, PairAlg.nm, PairAlg.ofScalar]; ring)
  have hy_ne : evalAC y ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hy_conj
    exact hnm (ιC_rat.injective (by simpa using hy_conj.symm))
  set b := toRat k5Params.bW
  set c := toRat k5Params.cW
  set d := toRat k5Params.disc_E0
  set N := PairAlg.nm b c y
  let w2 : PairAlg (RatFunc K5) := ⟨b, 2⟩
  let prod : PairAlg (RatFunc K5) :=
    PairAlg.mul b c (PairAlg.mul b c x (PairAlg.conj b y)) w2
  have hquot : evalAC x / (evalAC y * (2 * W_C + ιC_rat b)) =
      ιC_rat (N * d)⁻¹ * evalAC prod := by
    have hprod_ev : evalAC prod = evalAC x * evalAC (PairAlg.conj b y) * (2 * W_C + ιC_rat b) := by
      dsimp only [prod, w2, b, c]
      rw [evalAC_mul, evalAC_mul]
      simp only [evalAC, map_ofNat]
      ring
    rw [hprod_ev]
    have hNd_ne : ιC_rat (N * d) ≠ 0 := (map_ne_zero_iff ιC_rat ιC_rat.injective).mpr (mul_ne_zero hnm hdisc_ne)
    rw [map_inv₀, div_eq_iff (mul_ne_zero hy_ne h2W_ne), eq_comm, mul_assoc, inv_mul_eq_iff_eq_mul₀ hNd_ne]
    calc evalAC x * evalAC (PairAlg.conj b y) * (2 * W_C + ιC_rat b) * (evalAC y * (2 * W_C + ιC_rat b))
        = evalAC x * (evalAC y * evalAC (PairAlg.conj b y)) * (2 * W_C + ιC_rat b) ^ 2 := by ring
      _ = evalAC x * ιC_rat N * ιC_rat d := by rw [hy_conj, h2W_sq]
      _ = ιC_rat (N * d) * evalAC x := by rw [map_mul]; ring
  rw [hquot, show ιC_rat (N * d)⁻¹ * evalAC prod = (N * d)⁻¹ • evalAC prod from
      (Algebra.smul_def (N * d)⁻¹ (evalAC prod)).symm,
    map_smul, trace_AC_evalAC, smul_eq_mul]
  have htr : 2 * prod.c0 - prod.c1 * b = d * (x.c1 * y.c0 - x.c0 * y.c1) := by
    have hd_eq : d = b ^ 2 - 4 * c := by
      simp only [d, b, c, CoverParams.disc_E0, map_sub, map_pow, map_mul, map_ofNat]
    rw [hd_eq]
    simp only [prod, PairAlg.mul, PairAlg.conj, w2]
    ring
  rw [htr]
  field_simp [hnm, hdisc_ne]

/-- Universal two-branch specialization of `Algebra.trace (RatFunc K5) A_C` to ANY field `F`
over which `E0_poly` splits into two distinct roots `w1, w2`. -/
lemma map_trace_AC_euler {F : Type*} [Field F] (φ : RatFunc K5 →+* F)
    (x y : PairAlg (RatFunc K5)) (w1 w2 : F)
    (hsum : w1 + w2 = -φ (toRat k5Params.bW))
    (hprod : w1 * w2 = φ (toRat k5Params.cW))
    (hsep : w1 ≠ w2)
    (hy1 : PairAlg.evalAt w1 (PairAlg.map φ y) ≠ 0)
    (hy2 : PairAlg.evalAt w2 (PairAlg.map φ y) ≠ 0) :
    φ (Algebra.trace (RatFunc K5) A_C
        (evalAC x / (evalAC y * (2 * W_C + ιC_rat (toRat k5Params.bW))))) =
      PairAlg.evalAt w1 (PairAlg.map φ x) /
        (PairAlg.evalAt w1 (PairAlg.map φ y) * (2 * w1 + φ (toRat k5Params.bW))) +
      PairAlg.evalAt w2 (PairAlg.map φ x) /
        (PairAlg.evalAt w2 (PairAlg.map φ y) * (2 * w2 + φ (toRat k5Params.bW))) := by
  have hnm_phi : PairAlg.nm (φ (toRat k5Params.bW)) (φ (toRat k5Params.cW)) (PairAlg.map φ y) ≠ 0 := by
    rw [PairAlg.evalAt_nm _ _ w1 w2 hsum hprod]
    exact mul_ne_zero hy1 hy2
  have hnm : PairAlg.nm (toRat k5Params.bW) (toRat k5Params.cW) y ≠ 0 := by
    intro h0; apply hnm_phi; rw [← PairAlg.map_nm, h0, map_zero]
  rw [trace_AC_euler x y hnm, map_div₀, map_sub, map_mul, map_mul, PairAlg.map_nm]
  exact (PairAlg.eulerTr_div (φ (toRat k5Params.bW)) (φ (toRat k5Params.cW)) w1 w2
    (PairAlg.map φ x) (PairAlg.map φ y) hsum hprod hsep hy1 hy2).symm

-- Polymorphic cover-to-`SheetCalculus` algebraic equations over ANY field `F` with `φ : K5 →+* F`.
section CoverEquations
variable {F : Type*} [Field F] [CharZero F] (φ : K5 →+* F)

private abbrev pU (P : K5[X]) (U : F) : F := (P.map φ).eval U
private abbrev pUW (x : PairAlg K5[X]) (U W : F) : F :=
  PairAlg.evalAt W (PairAlg.map (Polynomial.evalRingHom U |>.comp (Polynomial.mapRingHom φ)) x)

omit [CharZero F] in
private lemma pUW_eq (x : PairAlg K5[X]) (U W : F) :
    pUW φ x U W = pU φ x.c0 U + pU φ x.c1 U * W := rfl

lemma E0_of_cover (U W : F) (hU : U ≠ 0) :
    U * E_fn 0 (φ S_K) (φ Q_K) (φ T_K) 0 0 U (W / U) =
      φ k5Params.Av0 * (W ^ 2 + pU φ k5Params.bW U * W + pU φ k5Params.cW U) := by
  have hT3 : φ T_K - 3 ≠ 0 := by
    have := (map_ne_zero_iff φ φ.injective).mpr T_K_sub_3_ne
    simpa only [map_sub, map_ofNat] using this
  simp only [E_fn, H_cub, pU, CoverParams.bW, CoverParams.cW, CoverParams.Bv, CoverParams.quadU,
    CoverParams.Av0, CoverParams.Av0_inv, CoverParams.Cv0, CoverParams.Bv0, CoverParams.Bv1, CoverParams.Bv2,
    CoverParams.inv4, CoverParams.inv9, CoverParams.inv27, CoverParams.inv243,
    k5Params_inv2, k5Params_inv3, k5Params_inv7, k5Params_invT3, k5Params_S, k5Params_Q, k5Params_T,
    Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_ofNat,
    eval_add, eval_sub, eval_mul, eval_pow, eval_neg, eval_C, eval_X, eval_ofNat,
    map_add, map_sub, map_mul, map_pow, map_neg, map_inv₀, map_ofNat]
  field_simp [hU, hT3]; ring

lemma E1_of_cover (a b U W : F) (hU : U ≠ 0)
    (hW : W ^ 2 + pU φ k5Params.bW U * W + pU φ k5Params.cW U = 0) :
    U * E_fn 1 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) =
      pU φ k5Params.ca_h U * (W * a) + pU φ k5Params.cb_h U * (W * b) +
      pUW φ k5Params.c0W U W := by
  have hc0W_eq : pUW φ k5Params.c0W U W =
      φ k5Params.c0_V2 * W ^ 2 + φ k5Params.c0_V1 * U * W + φ k5Params.c0_V0 * U ^ 2 := by
    simp only [pUW_eq, CoverParams.c0W, CoverParams.toUW, pU,
      Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
      eval_sub, eval_mul, eval_pow, eval_C, eval_X]
    linear_combination -φ k5Params.c0_V2 * hW
  rw [hc0W_eq]
  simp only [E_fn, H_cub, pU, CoverParams.ca_h, CoverParams.cb_h, CoverParams.quadU,
    CoverParams.c0_V2, CoverParams.c0_V1, CoverParams.c0_V0,
    CoverParams.inv9, CoverParams.inv27, CoverParams.inv81,
    k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q, k5Params_T,
    Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_ofNat,
    eval_add, eval_sub, eval_mul, eval_pow, eval_neg, eval_C, eval_X, eval_ofNat,
    map_add, map_sub, map_mul, map_pow, map_neg, map_inv₀, map_ofNat]
  field_simp [hU]; ring

lemma E2_of_cover (a b U W : F) (hU : U ≠ 0)
    (hW : W ^ 2 + pU φ k5Params.bW U * W + pU φ k5Params.cW U = 0) :
    U * W * E_fn 2 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) =
      pU φ k5Params.q20 U * (W * a) ^ 2 + pU φ k5Params.q11 U * (W * a) * (W * b) +
      pU φ k5Params.q02 U * (W * b) ^ 2 + W * pUW φ k5Params.k2W U W := by
  have hk2W_eq : pUW φ k5Params.k2W U W =
      φ k5Params.k2_V2 * W ^ 2 + φ k5Params.k2_V1 * U * W + φ k5Params.k2_V0 * U ^ 2 := by
    simp only [pUW_eq, CoverParams.k2W, CoverParams.toUW, pU,
      Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
      eval_sub, eval_mul, eval_pow, eval_C, eval_X]
    linear_combination -φ k5Params.k2_V2 * hW
  rw [hk2W_eq]
  simp only [E_fn, H_cub, pU, CoverParams.q20, CoverParams.q11, CoverParams.q02, CoverParams.quadU,
    CoverParams.k2_V2, CoverParams.k2_V1, CoverParams.k2_V0,
    CoverParams.inv9, CoverParams.inv27, CoverParams.inv81,
    k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q, k5Params_T,
    Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_ofNat,
    eval_add, eval_sub, eval_mul, eval_pow, eval_neg, eval_C, eval_X, eval_ofNat,
    map_add, map_sub, map_mul, map_pow, map_neg, map_inv₀, map_ofNat]
  field_simp [hU]; ring

lemma E3_of_cover (a b U W : F) (hU : U ≠ 0)
    (hW : W ^ 2 + pU φ k5Params.bW U * W + pU φ k5Params.cW U = 0) :
    U * W ^ 2 * E_fn 3 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) =
      pU φ k5Params.c30 U * (W * a) ^ 3 + pU φ k5Params.c21 U * (W * a) ^ 2 * (W * b) +
      pU φ k5Params.c12 U * (W * a) * (W * b) ^ 2 + pU φ k5Params.c03 U * (W * b) ^ 3 +
      W ^ 2 * pUW φ k5Params.k3W U W := by
  have hk3W_eq : pUW φ k5Params.k3W U W =
      φ k5Params.k3_V2 * W ^ 2 + φ k5Params.k3_V1 * U * W + φ k5Params.k3_V0 * U ^ 2 := by
    simp only [pUW_eq, CoverParams.k3W, CoverParams.toUW, pU,
      Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
      eval_sub, eval_mul, eval_pow, eval_C, eval_X]
    linear_combination -φ k5Params.k3_V2 * hW
  rw [hk3W_eq]
  simp only [E_fn, H_cub, pU, CoverParams.c30, CoverParams.c21, CoverParams.c12, CoverParams.c03,
    CoverParams.quadU, CoverParams.k3_V2, CoverParams.k3_V1, CoverParams.k3_V0,
    CoverParams.inv9, CoverParams.inv27, CoverParams.inv243, k5Params_inv3,
    Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_ofNat, Polynomial.map_zero,
    eval_add, eval_mul, eval_pow, eval_neg, eval_C, eval_X, eval_ofNat, eval_zero,
    map_zero, map_mul, map_pow, map_neg, map_inv₀, map_ofNat]
  field_simp [hU]; ring

lemma E2_z_of_cover (z U W : F) (hU : U ≠ 0) (hW0 : W ≠ 0) (hcb : pU φ k5Params.cb_h U ≠ 0)
    (hW : W ^ 2 + pU φ k5Params.bW U * W + pU φ k5Params.cW U = 0) :
    let a := z / W
    let b := -(pU φ k5Params.ca_h U * z + pUW φ k5Params.c0W U W) / (W * pU φ k5Params.cb_h U)
    U * W * pU φ k5Params.cb_h U ^ 2 * E_fn 2 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) =
      pUW φ k5Params.d2_2 U W * z ^ 2 + pUW φ k5Params.d2_1 U W * z + pUW φ k5Params.d2_0 U W := by
  intro a b
  have h2 := E2_of_cover φ a b U W hU hW
  have hWa : W * a = z := mul_div_cancel₀ z hW0
  have hWb : pU φ k5Params.cb_h U * (W * b) = -(pU φ k5Params.ca_h U * z + pUW φ k5Params.c0W U W) := by
    dsimp only [b]; field_simp [hW0, hcb]
  have hd22 : pUW φ k5Params.d2_2 U W = pU φ k5Params.Q5_z U := by
    simp [pUW, CoverParams.d2_2, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar, pU]
  have hd21 : pUW φ k5Params.d2_1 U W =
      (-pU φ k5Params.q11 U * pU φ k5Params.cb_h U + 2 * pU φ k5Params.q02 U * pU φ k5Params.ca_h U) *
      pUW φ k5Params.c0W U W := by
    simp [pUW, CoverParams.d2_1, PairAlg.map_smul, PairAlg.evalAt_smul, pU]
  have hd20 : pUW φ k5Params.d2_0 U W =
      pU φ k5Params.q02 U * pUW φ k5Params.c0W U W ^ 2 +
      pU φ k5Params.cb_h U ^ 2 * (W * pUW φ k5Params.k2W U W) := by
    simp only [pUW, CoverParams.d2_0, CoverParams.pmul, PairAlg.map_add, PairAlg.map_smul,
      PairAlg.map_mul, PairAlg.map_W, PairAlg.evalAt_add, PairAlg.evalAt_smul,
      RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.coe_evalRingHom,
      Polynomial.map_pow, eval_pow, pU]
    rw [PairAlg.evalAt_mul _ _ W hW, PairAlg.evalAt_mul _ _ W hW, PairAlg.evalAt_W]
    ring
  rw [hd22, hd21, hd20]
  have hQ5 : pU φ k5Params.Q5_z U =
      pU φ k5Params.q20 U * pU φ k5Params.cb_h U ^ 2 -
      pU φ k5Params.q11 U * pU φ k5Params.ca_h U * pU φ k5Params.cb_h U +
      pU φ k5Params.q02 U * pU φ k5Params.ca_h U ^ 2 := by
    simp [pU, CoverParams.Q5_z]
  rw [hQ5]
  calc U * W * pU φ k5Params.cb_h U ^ 2 * E_fn 2 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U)
      = pU φ k5Params.cb_h U ^ 2 * (U * W * E_fn 2 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U)) := by ring
    _ = pU φ k5Params.cb_h U ^ 2 * (pU φ k5Params.q20 U * (W * a) ^ 2 +
        pU φ k5Params.q11 U * (W * a) * (W * b) + pU φ k5Params.q02 U * (W * b) ^ 2 +
        W * pUW φ k5Params.k2W U W) := by rw [h2]
    _ = _ := by
      rw [hWa]
      linear_combination (pU φ k5Params.q11 U * z * pU φ k5Params.cb_h U +
        pU φ k5Params.q02 U * (pU φ k5Params.cb_h U * (W * b) - (pU φ k5Params.ca_h U * z + pUW φ k5Params.c0W U W))) * hWb

lemma E3_z_of_cover (z U W : F) (hU : U ≠ 0) (hW0 : W ≠ 0) (hcb : pU φ k5Params.cb_h U ≠ 0)
    (hW : W ^ 2 + pU φ k5Params.bW U * W + pU φ k5Params.cW U = 0) :
    let a := z / W
    let b := -(pU φ k5Params.ca_h U * z + pUW φ k5Params.c0W U W) / (W * pU φ k5Params.cb_h U)
    U * W ^ 2 * pU φ k5Params.cb_h U ^ 3 * E_fn 3 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) =
      pUW φ k5Params.d3_3 U W * z ^ 3 + pUW φ k5Params.d3_2 U W * z ^ 2 +
      pUW φ k5Params.d3_1 U W * z + pUW φ k5Params.d3_0 U W := by
  intro a b
  have h3 := E3_of_cover φ a b U W hU hW
  have hWa : W * a = z := mul_div_cancel₀ z hW0
  have hWb : pU φ k5Params.cb_h U * (W * b) = -(pU φ k5Params.ca_h U * z + pUW φ k5Params.c0W U W) := by
    dsimp only [b]; field_simp [hW0, hcb]
  have hd33 : pUW φ k5Params.d3_3 U W = pU φ k5Params.Q7_z U := by
    simp [pUW, CoverParams.d3_3, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar, pU]
  have hd32 : pUW φ k5Params.d3_2 U W =
      (-pU φ k5Params.c21 U * pU φ k5Params.cb_h U ^ 2 +
       2 * pU φ k5Params.c12 U * pU φ k5Params.ca_h U * pU φ k5Params.cb_h U -
       3 * pU φ k5Params.c03 U * pU φ k5Params.ca_h U ^ 2) * pUW φ k5Params.c0W U W := by
    simp [pUW, CoverParams.d3_2, PairAlg.map_smul, PairAlg.evalAt_smul, pU]
  have hd31 : pUW φ k5Params.d3_1 U W =
      (pU φ k5Params.c12 U * pU φ k5Params.cb_h U - 3 * pU φ k5Params.c03 U * pU φ k5Params.ca_h U) *
      pUW φ k5Params.c0W U W ^ 2 := by
    simp only [pUW, CoverParams.d3_1, CoverParams.pmul, PairAlg.map_smul, PairAlg.map_mul,
      PairAlg.evalAt_smul, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.coe_evalRingHom,
      Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat, eval_sub, eval_mul, eval_ofNat, pU]
    rw [PairAlg.evalAt_mul _ _ W hW]; ring
  have hd30 : pUW φ k5Params.d3_0 U W =
      -pU φ k5Params.c03 U * pUW φ k5Params.c0W U W ^ 3 +
      pU φ k5Params.cb_h U ^ 3 * (W ^ 2 * pUW φ k5Params.k3W U W) := by
    simp only [pUW, CoverParams.d3_0, CoverParams.pmul, PairAlg.map_add, PairAlg.map_smul,
      PairAlg.map_mul, PairAlg.map_W, PairAlg.evalAt_add, PairAlg.evalAt_smul,
      RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.coe_evalRingHom,
      Polynomial.map_neg, Polynomial.map_pow, eval_neg, eval_pow, pU]
    rw [PairAlg.evalAt_mul _ _ W hW, PairAlg.evalAt_mul _ _ W hW,
      PairAlg.evalAt_mul _ _ W hW, PairAlg.evalAt_mul _ _ W hW, PairAlg.evalAt_W]
    ring
  rw [hd33, hd32, hd31, hd30]
  have hQ7 : pU φ k5Params.Q7_z U =
      pU φ k5Params.c30 U * pU φ k5Params.cb_h U ^ 3 -
      pU φ k5Params.c21 U * pU φ k5Params.ca_h U * pU φ k5Params.cb_h U ^ 2 +
      pU φ k5Params.c12 U * pU φ k5Params.ca_h U ^ 2 * pU φ k5Params.cb_h U -
      pU φ k5Params.c03 U * pU φ k5Params.ca_h U ^ 3 := by
    simp [pU, CoverParams.Q7_z]
  rw [hQ7]
  set Y := pU φ k5Params.cb_h U * (W * b)
  set Z := -(pU φ k5Params.ca_h U * z + pUW φ k5Params.c0W U W)
  have hstep : U * W ^ 2 * pU φ k5Params.cb_h U ^ 3 * E_fn 3 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) =
      pU φ k5Params.c30 U * pU φ k5Params.cb_h U ^ 3 * z ^ 3 +
      pU φ k5Params.c21 U * pU φ k5Params.cb_h U ^ 2 * z ^ 2 * Y +
      pU φ k5Params.c12 U * pU φ k5Params.cb_h U * z * Y ^ 2 +
      pU φ k5Params.c03 U * Y ^ 3 +
      pU φ k5Params.cb_h U ^ 3 * (W ^ 2 * pUW φ k5Params.k3W U W) := by
    have hmul : U * W ^ 2 * pU φ k5Params.cb_h U ^ 3 * E_fn 3 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) =
        pU φ k5Params.cb_h U ^ 3 * (U * W ^ 2 * E_fn 3 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U)) := by ring
    rw [hmul, h3, hWa]; dsimp only [Y]; ring
  rw [hstep, hWb]; dsimp only [Z]; ring

end CoverEquations

/-- Helper evaluating a polynomial `P : K5[X]` in `A_C` at `U_C`. -/
def polyC (P : K5[X]) : A_C := ιC_rat (toRat P)

/-- Helper evaluating a `PairAlg K5[X]` in `A_C` at `(U_C, W_C)`. -/
def pairC (x : PairAlg K5[X]) : A_C := evalAC (PairAlg.map toRat x)

/-- The `z`-parametrized `P18_of` function in `A_C` (`b`-elimination: `a = z / W_C`,
`b = -(ca_h * z + c0W) / (W_C * cb_h)`). -/
def P18_z_AC (z : A_C) : A_C :=
  SheetCalculus.P18_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K)
    (z / W_C) (-(polyC k5Params.ca_h * z + pairC k5Params.c0W) / (W_C * polyC k5Params.cb_h))
    U_C V_C

/-- Numerator of the un-traced algebraic cover 1-form `eta_AC ∈ A_C`. -/
def eta_AC_num : A_C :=
  let p := interp4 P18_z_AC
  let P1 := remDeg4_P1 (pairC k5Params.d2_2) (pairC k5Params.d2_1) (pairC k5Params.d2_0) p.1 p.2.1 p.2.2.1 p.2.2.2.1
  let P0 := remDeg4_P0 (pairC k5Params.d2_2) (pairC k5Params.d2_1) (pairC k5Params.d2_0) p.1 p.2.1 p.2.2.1 p.2.2.2.2
  (-(P1 * pairC k5Params.d0_z - P0 * pairC k5Params.d1_z) *
    U_C ^ 3 * W_C * polyC k5Params.cb_h ^ 4)

/-- The un-traced algebraic cover 1-form `eta_AC ∈ A_C`. -/
def eta_AC : A_C :=
  eta_AC_num /
    (81 * ιC_K5 k5Params.Av0 * (2 * W_C + polyC k5Params.bW) *
      polyC k5Params.Q5_z ^ 3 * pairC k5Params.res_z)

/-- The master rational 1-form `eta ∈ RatFunc K5` obtained by tracing `eta_AC` down from `A_C`. -/
def eta : RatFunc K5 := Algebra.trace (RatFunc K5) A_C eta_AC

/-! ### Section 3: Global Regularity of `eta_L` Outside `{0} ∪ R_{Q5} ∪ R_{34}` -/

section Regularity

lemma eval_ne_zero_of_isCoprime {L : Type*} [Field L] [Algebra K5 L]
    {P Q : K5[X]} (hcop : IsCoprime P Q) {r : L}
    (hP : (P.map (algebraMap K5 L)).eval r = 0) :
    (Q.map (algebraMap K5 L)).eval r ≠ 0 := by
  obtain ⟨u, v, huv⟩ := hcop
  intro hQ
  have h1 := congrArg (fun f : K5[X] => (f.map (algebraMap K5 L)).eval r) huv
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one,
    eval_add, eval_mul, eval_one, hP, hQ, mul_zero, add_zero] at h1
  exact zero_ne_one h1

-- Local ring closure properties of `RegularAt` and `valueAt` over any field `L`.
section LocalReg
variable {L : Type*} [Field L]

lemma regAt_zero (a : L) : RegularAt a (0 : RatFunc L) :=
  ⟨0, 1, by simp, by simp⟩

lemma regAt_one (a : L) : RegularAt a (1 : RatFunc L) :=
  ⟨1, 1, by simp, by simp⟩

lemma regAt_C (a c : L) : RegularAt a (RatFunc.C c) :=
  ⟨Polynomial.C c, 1, by simp, by simp⟩

lemma regAt_X (a : L) : RegularAt a (RatFunc.X : RatFunc L) :=
  ⟨Polynomial.X, 1, by simp, by simp⟩

lemma regAt_ofNat (a : L) (n : ℕ) [n.AtLeastTwo] :
    RegularAt a (OfNat.ofNat n : RatFunc L) :=
  ⟨Polynomial.C (OfNat.ofNat n), 1, by simp, by simp [map_ofNat]⟩

lemma regAt_neg_local {a : L} {f : RatFunc L} (hf : RegularAt a f) : RegularAt a (-f) := by
  obtain ⟨P, Q, hQ, rfl⟩ := hf
  exact ⟨-P, Q, hQ, by simp [neg_div]⟩

lemma regAt_sub_local {a : L} {f g : RatFunc L} (hf : RegularAt a f) (hg : RegularAt a g) :
    RegularAt a (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add (regAt_neg_local hg)

lemma regAt_mul_local {a : L} {f g : RatFunc L} (hf : RegularAt a f) (hg : RegularAt a g) :
    RegularAt a (f * g) := by
  obtain ⟨P, Q, hQ, rfl⟩ := hf
  obtain ⟨R, S, hS, rfl⟩ := hg
  refine ⟨P * R, Q * S, by simpa using mul_ne_zero hQ hS, ?_⟩
  simp only [map_mul]; ring

lemma regAt_pow_local {a : L} {f : RatFunc L} (hf : RegularAt a f) (n : ℕ) :
    RegularAt a (f ^ n) := by
  induction n with
  | zero => simpa using regAt_one a
  | succ k ih => rw [pow_succ]; exact regAt_mul_local ih hf

lemma valueAt_polynomial (a : L) (P : L[X]) :
    valueAt a (algebraMap L[X] (RatFunc L) P) = P.eval a := by
  have h := valueAt_div_polynomials a P 1 (by simp)
  simpa only [map_one, div_one, eval_one] using h

lemma valueAt_C (a c : L) : valueAt a (RatFunc.C c) = c := by
  rw [← RatFunc.algebraMap_C, valueAt_polynomial, eval_C]

lemma valueAt_X (a : L) : valueAt a (RatFunc.X : RatFunc L) = a := by
  rw [← RatFunc.algebraMap_X, valueAt_polynomial, eval_X]

lemma valueAt_mul_of_regularAt {a : L} {f g : RatFunc L}
    (hf : RegularAt a f) (hg : RegularAt a g) :
    valueAt a (f * g) = valueAt a f * valueAt a g := by
  obtain ⟨P, Q, hQ, rfl⟩ := hf
  obtain ⟨R, S, hS, rfl⟩ := hg
  rw [show algebraMap L[X] (RatFunc L) P / algebraMap L[X] (RatFunc L) Q *
      (algebraMap L[X] (RatFunc L) R / algebraMap L[X] (RatFunc L) S) =
      algebraMap L[X] (RatFunc L) (P * R) / algebraMap L[X] (RatFunc L) (Q * S) by
    simp only [map_mul]; ring]
  rw [valueAt_div_polynomials a (P * R) (Q * S) (by simpa using mul_ne_zero hQ hS),
    valueAt_div_polynomials a P Q hQ, valueAt_div_polynomials a R S hS, eval_mul, eval_mul]
  ring

lemma valueAt_pow_of_regularAt {a : L} {f : RatFunc L} (hf : RegularAt a f) (n : ℕ) :
    valueAt a (f ^ n) = (valueAt a f) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, ← map_one RatFunc.C, valueAt_C]
  | succ k ih => rw [pow_succ, pow_succ, valueAt_mul_of_regularAt (regAt_pow_local hf k) hf, ih]

lemma regAt_inv_of_valueAt_ne {a : L} {f : RatFunc L}
    (hf : RegularAt a f) (hne : valueAt a f ≠ 0) : RegularAt a f⁻¹ := by
  obtain ⟨P, Q, hQ, rfl⟩ := hf
  rw [valueAt_div_polynomials a P Q hQ] at hne
  have hP : P.eval a ≠ 0 := left_ne_zero_of_mul (by simpa [div_eq_mul_inv] using hne)
  exact ⟨Q, P, hP, by rw [inv_div]⟩

lemma regAt_div_of_valueAt_ne {a : L} {f g : RatFunc L}
    (hf : RegularAt a f) (hg : RegularAt a g) (hne : valueAt a g ≠ 0) :
    RegularAt a (f / g) := by
  rw [div_eq_mul_inv]; exact regAt_mul_local hf (regAt_inv_of_valueAt_ne hg hne)

lemma valueAt_div_of_regularAt {a : L} {f g : RatFunc L}
    (hf : RegularAt a f) (hg : RegularAt a g) (hne : valueAt a g ≠ 0) :
    valueAt a (f / g) = valueAt a f / valueAt a g := by
  have hg' : RegularAt a g⁻¹ := regAt_inv_of_valueAt_ne hg hne
  have hinv : valueAt a g⁻¹ = (valueAt a g)⁻¹ := by
    have h1 := valueAt_mul_of_regularAt hg hg'
    have hg0 : g ≠ 0 := by intro h0; rw [h0, map_zero] at hne; exact hne rfl
    rw [mul_inv_cancel₀ hg0, ← map_one RatFunc.C, valueAt_C] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm
  rw [div_eq_mul_inv, valueAt_mul_of_regularAt hf hg', hinv, div_eq_mul_inv]

end LocalReg

-- Nonzero constants and cover elements in `K5` and `A_C`.
lemma Av0_K5_ne_zero : k5Params.Av0 ≠ 0 := by
  have hT3 := T_K_sub_3_ne
  have h4 : (4 : K5) ≠ 0 := by exact_mod_cast (by decide : (4 : ℕ) ≠ 0)
  have h3 : (3 : K5) ≠ 0 := by exact_mod_cast (by decide : (3 : ℕ) ≠ 0)
  rw [CoverParams.Av0, CoverParams.inv243, k5Params_inv3, k5Params_T]
  exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h4) (pow_ne_zero 5 (inv_ne_zero h3)))
    (pow_ne_zero 3 hT3)

lemma cW_coeff2_K5_ne_zero : k5Params.cW.coeff 2 ≠ 0 := by
  have hmap : locParams.cW.map LocK5.subtype = k5Params.cW :=
    CoverParams.map_cW locParams LocK5.subtype
  have hcoe : k5Params.cW.coeff 2 = (locParams.cW.coeff 2 : K5) := by
    rw [← hmap, Polynomial.coeff_map]; rfl
  rw [hcoe]
  apply LocK5.ne_zero_of_evLoc
  rw [← Polynomial.coeff_map, CoverParams.map_cW, locParams_map_evLoc,
    ← Poly1009.toPoly_c_cW, Poly1009.toPoly_coeff_getD]
  decide

lemma cW_K5_ne_zero : k5Params.cW ≠ 0 := fun h => cW_coeff2_K5_ne_zero (by rw [h, coeff_zero])

lemma cW_eval_ne_zero {L : Type*} [Field L] [Algebra K5 L] {r : L} (hr0 : r ≠ 0) :
    (k5Params.cW.map (algebraMap K5 L)).eval r ≠ 0 := by
  have hcW : k5Params.cW = C (k5Params.cW.coeff 2) * X ^ 2 := by
    rw [CoverParams.cW, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp
  rw [hcW, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    eval_mul, eval_C, eval_pow, eval_X]
  exact mul_ne_zero ((map_ne_zero_iff _ (algebraMap K5 L).injective).mpr cW_coeff2_K5_ne_zero)
    (pow_ne_zero 2 hr0)

lemma nm_WU_eval_one : k5Params.nm_WU.eval 1 = H0_K / k5Params.Av0 := by
  have h0 := E0_of_cover (RingHom.id K5) 1 1 one_ne_zero
  simp only [pU, RingHom.id_apply, Polynomial.map_id, div_one, one_mul, one_pow] at h0
  have hH : E_fn 0 S_K Q_K T_K 0 0 1 1 = H0_K := by
    have h1 := H_cub_eq_H0_A1_B1 S_K Q_K T_K 1 1
    simp only [u_of, v_of, sub_self, zero_div, zero_mul, add_zero, one_mul] at h1
    change H_cub S_K Q_K T_K 1 1 1 = H0_K
    rw [h1]
    simpa [SL, QL, TL, ιL] using H0_of_L (L := K5)
  rw [hH] at h0
  have hnm : k5Params.nm_WU.eval 1 = 1 + k5Params.bW.eval 1 + k5Params.cW.eval 1 := by
    simp only [CoverParams.nm_WU, CoverParams.pnm, PairAlg.nm, eval_add, eval_sub, eval_mul,
      eval_pow, eval_neg, eval_X, eval_one]; ring
  rw [hnm, eq_div_iff Av0_K5_ne_zero]
  linear_combination -h0

lemma nm_WU_eval_one_ne {L : Type*} [Field L] [Algebra K5 L] :
    (k5Params.nm_WU.map (algebraMap K5 L)).eval 1 ≠ 0 := by
  have h : (k5Params.nm_WU.map (algebraMap K5 L)).eval 1 = algebraMap K5 L (k5Params.nm_WU.eval 1) := by
    simpa only [map_one] using Polynomial.eval_map_apply (algebraMap K5 L) (1 : K5)
  rw [h, nm_WU_eval_one]
  exact (map_ne_zero_iff _ (algebraMap K5 L).injective).mpr (div_ne_zero H0_K_ne_zero Av0_K5_ne_zero)

lemma nm_WU_K5_ne_zero : k5Params.nm_WU ≠ 0 := fun h => by
  have h1 := nm_WU_eval_one_ne (L := K5)
  rw [h, Polynomial.map_zero, eval_zero] at h1
  exact h1 rfl

lemma cb_h_K5_ne_zero : k5Params.cb_h ≠ 0 := by
  rw [cb_h_K5_eq_mul_monic]
  exact mul_ne_zero (Polynomial.C_ne_zero.mpr (LocK5.ne_zero_of_evLoc cb_h_lc_evLoc_ne))
    (cb_h_m_loc_spec.1.map LocK5.subtype).ne_zero

lemma ca_h_K5_ne_zero : k5Params.ca_h ≠ 0 := by
  intro h0
  have hcop := isCoprime_cb_h_ca_h
  rw [h0, isCoprime_zero_right] at hcop
  have hdeg := Polynomial.natDegree_eq_zero_of_isUnit hcop
  rw [cb_h_K5_eq_mul_monic, Polynomial.natDegree_C_mul (LocK5.ne_zero_of_evLoc cb_h_lc_evLoc_ne),
    cb_h_m_K5, cb_h_m_loc_spec.1.natDegree_map, cb_h_m_loc_spec.2.1] at hdeg
  omega

lemma Q5_K5_ne_zero : k5Params.Q5_z ≠ 0 := by
  intro h0; have := Q5_K5_natDegree; rw [h0, natDegree_zero] at this; omega

lemma nm_z_K5_ne_zero : k5Params.nm_z ≠ 0 := by
  rw [nm_z_K5_factor]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (Polynomial.C_ne_zero.mpr lc34_K5_ne_zero)
    (pow_ne_zero 15 X_ne_zero)) (pow_ne_zero 12 (cb_h_m_loc_spec.1.map LocK5.subtype).ne_zero))
    P34_K5_monic.ne_zero

lemma nm_disc_E2z_K5_ne_zero : k5Params.pnm k5Params.disc_E2z ≠ 0 := by
  intro h0
  have hcop := isCoprime_P34_nm_disc_E2z
  rw [h0, isCoprime_zero_right] at hcop
  have hdeg := Polynomial.natDegree_eq_zero_of_isUnit hcop
  rw [P34_K5_natDegree] at hdeg; omega

lemma polyC_ne_zero {P : K5[X]} (hP : P ≠ 0) : polyC P ≠ 0 :=
  (map_ne_zero_iff ιC_rat ιC_rat.injective).mpr (polynomialMap_ne_zero hP)

lemma pairC_ne_zero_of_pnm {x : PairAlg K5[X]} (h : k5Params.pnm x ≠ 0) : pairC x ≠ 0 := by
  intro h0
  have hnm : evalAC (PairAlg.map toRat x) *
      evalAC (PairAlg.conj (toRat k5Params.bW) (PairAlg.map toRat x)) =
      ιC_rat (toRat (k5Params.pnm x)) := by
    rw [← evalAC_mul, ← evalAC_ofScalar]
    congr 1; ext
    · simp only [PairAlg.mul, PairAlg.conj, PairAlg.ofScalar, PairAlg.map, CoverParams.pnm,
        PairAlg.nm, map_add, map_sub, map_mul, map_pow]; ring
    · simp only [PairAlg.mul, PairAlg.conj, PairAlg.ofScalar, PairAlg.map]; ring
  change evalAC (PairAlg.map toRat x) = 0 at h0
  rw [h0, zero_mul] at hnm
  exact polyC_ne_zero h hnm.symm

lemma U_C_ne_zero : U_C ≠ 0 := by
  have h : U_C = polyC X := by simp [U_C, polyC, RatFunc.algebraMap_X]
  rw [h]; exact polyC_ne_zero (X_ne_zero (R := K5))

lemma W_C_ne_zero : W_C ≠ 0 := by
  have hW : W_C = pairC PairAlg.W := by simp [pairC, PairAlg.map_W, evalAC_W]
  rw [hW]
  apply pairC_ne_zero_of_pnm
  simpa [CoverParams.pnm, PairAlg.nm, PairAlg.W] using cW_K5_ne_zero

lemma V_C_ne_zero : V_C ≠ 0 := div_ne_zero W_C_ne_zero U_C_ne_zero

lemma u_of_U_C_ne_zero : u_of U_C ≠ 0 := by
  have h9 : (9 : A_C) ≠ 0 := by exact_mod_cast (by decide : (9 : ℕ) ≠ 0)
  have h1 : U_C - 1 ≠ 0 := by
    have heq : U_C - 1 = polyC (X - 1) := by
      simp [polyC, U_C, map_sub, RatFunc.algebraMap_X]
    rw [heq]; exact polyC_ne_zero (Polynomial.monic_X_sub_C 1).ne_zero
  exact div_ne_zero h1 h9

lemma v_of_V_C_ne_zero : v_of V_C ≠ 0 := by
  have h9 : (9 : A_C) ≠ 0 := by exact_mod_cast (by decide : (9 : ℕ) ≠ 0)
  have hwu : W_C - U_C ≠ 0 := by
    have heq : W_C - U_C = pairC ⟨-X, 1⟩ := by
      simp [pairC, evalAC, PairAlg.map, U_C, RatFunc.algebraMap_X]; ring
    rw [heq]; exact pairC_ne_zero_of_pnm nm_WU_K5_ne_zero
  have h1 : V_C - 1 ≠ 0 := by
    rw [V_C, show W_C / U_C - 1 = (W_C - U_C) / U_C by
      rw [sub_div, div_self U_C_ne_zero]]
    exact div_ne_zero hwu U_C_ne_zero
  exact div_ne_zero h1 h9

/-- Homogenized `9 * U * G` element in `PairAlg K5[X]`. -/
def P_G_pair : PairAlg K5[X] :=
  ⟨C DX2_K * X * (X - 1) - C DY2_K * X, C DY2_K⟩

lemma nine_U_G_AC_eq :
    9 * U_C * G_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) U_C V_C =
      pairC P_G_pair := by
  have hDX : DX2_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 x_K) = ιC_K5 DX2_K := by
    have h := congrArg ιC_K5 (DX2_of_L (L := K5))
    simpa only [DX2_of, u3_of, SL, QL, xL, ιL, Algebra.algebraMap_self, RingHom.id_apply,
      map_add, map_sub, map_mul, map_pow, map_ofNat] using h
  have hDY : DY2_of (ιC_K5 T_K) (ιC_K5 y_K) = ιC_K5 DY2_K := by
    have h := congrArg ιC_K5 (DY2_of_L (L := K5))
    simpa only [DY2_of, v3_of, TL, yL, ιL, Algebra.algebraMap_self, RingHom.id_apply,
      map_add, map_sub, map_mul, map_pow, map_ofNat] using h
  have h9 : (9 : A_C) ≠ 0 := by exact_mod_cast (by decide : (9 : ℕ) ≠ 0)
  rw [G_of, hDX, hDY, u_of, v_of, V_C, pairC, P_G_pair, evalAC]
  simp only [PairAlg.map, map_sub, map_mul, map_one, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  change 9 * U_C * ((U_C - 1) / 9 * ιC_K5 DX2_K + (W_C / U_C - 1) / 9 * ιC_K5 DY2_K) =
    (ιC_K5 DX2_K * U_C * (U_C - 1) - ιC_K5 DY2_K * U_C) + ιC_K5 DY2_K * W_C
  have h1 : (9 : A_C) * ((U_C - 1) / 9) = U_C - 1 := mul_div_cancel₀ _ h9
  have h2 : (9 : A_C) * ((W_C / U_C - 1) / 9) = W_C / U_C - 1 := mul_div_cancel₀ _ h9
  have h3 : U_C * (W_C / U_C - 1) = W_C - U_C := by
    rw [mul_sub, mul_div_cancel₀ _ U_C_ne_zero, mul_one]
  linear_combination U_C * ιC_K5 DX2_K * h1 + U_C * ιC_K5 DY2_K * h2 + ιC_K5 DY2_K * h3

lemma pnm_P_G_eval_one {L : Type*} [Field L] [Algebra K5 L] :
    ((k5Params.pnm P_G_pair).map (algebraMap K5 L)).eval 1 =
      (algebraMap K5 L DY2_K) ^ 2 * (k5Params.nm_WU.map (algebraMap K5 L)).eval 1 := by
  simp only [CoverParams.pnm, P_G_pair, CoverParams.nm_WU, PairAlg.nm,
    Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_one,
    eval_add, eval_sub, eval_mul, eval_pow, eval_neg, eval_C, eval_X, eval_one]
  ring

lemma G_of_AC_ne_zero :
    G_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) U_C V_C ≠ 0 := by
  have hpnm_ne : k5Params.pnm P_G_pair ≠ 0 := by
    intro h0
    have h1 := pnm_P_G_eval_one (L := K5)
    rw [h0, Polynomial.map_zero, eval_zero] at h1
    exact mul_ne_zero (pow_ne_zero 2 DY2_K_ne_zero) (nm_WU_eval_one_ne (L := K5)) h1.symm
  have h9UG : 9 * U_C * G_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) U_C V_C ≠ 0 := by
    rw [nine_U_G_AC_eq]; exact pairC_ne_zero_of_pnm hpnm_ne
  exact right_ne_zero_of_mul h9UG

lemma F5_of_AC : F5_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) = 0 := by
  have h := congrArg ιC_K5 (F5_of_L (L := K5))
  simpa only [F5_of, H0_of, SL, QL, TL, xL, yL, ιL, Algebra.algebraMap_self, RingHom.id_apply,
    map_zero, map_add, map_sub, map_mul, map_pow, map_neg, map_div₀, map_ofNat] using h

-- Pure-ring `cB1_of` complement for `v_of V = 0` regularity.
def dB1_dT {R : Type*} [Field R] (T U V : R) : R :=
  (1 / 27) * U * (25 * (5 * T - 9) * (15 * T - 9) - 12 * (T - 3) ^ 2 * V)

def cB1_of {R : Type*} [Field R] (S Q T a b U V : R) : R :=
  let H0 := H0_of S Q T; let B1 := B1_of T U V
  (-B1 * dH0_fn 0 S Q T) * a + (-B1 * dH0_fn 1 S Q T) * b +
  (H0 * dB1_dT T U V - B1 * dH0_fn 2 S Q T)

lemma u_cA1_add_v_cB1 {F : Type*} [Field F] [CharZero F] (S Q T a b U V : F) :
    u_of U * cA1_of S Q T a b U V + v_of V * cB1_of S Q T a b U V =
      H0_of S Q T * E_fn 1 S Q T a b U V -
      (dH0_fn 0 S Q T * a + dH0_fn 1 S Q T * b + dH0_fn 2 S Q T) * E_fn 0 S Q T a b U V := by
  simp only [u_of, v_of, cA1_of, cB1_of, dA1_fn, dB1_dT, A1_of, B1_of, H0_of, dH0_fn, E_fn, H_cub]
  ring

/-- Regularized `P18_of` at `U = 1` (`qX = dot_ab CX_of / G^2`). -/
def P18_regX_of {F : Type*} [Field F] (S Q T x y a b U V : F) : F :=
  let ξS := S - a * T; let ξQ := Q - b * T
  let M0 := A_0U a b ξS ξQ U V / U + A_0V a b ξS ξQ U V / V
  let MY := A_Y a b ξS ξQ U V
  let MX := A_X a b ξS ξQ U V
  let H0 := H0_of S Q T
  let qY := dot_ab (QY_num S Q T x y U V) a b / v_of V
  let qX := dot_ab (CX_of S Q T x y U V) a b / G_of S Q T x y U V ^ 2
  let q1 := H0 * A1_of S Q U V * qY + H0 * B1_of T U V * qX +
    (cA1_of S Q T a b U V / v_of V) * EB_of S Q T x y U V
  M0 * q1 + (MY * qY + MX * qX) * H0 ^ 2

/-- Regularized `P18_of` at `V = 1` (`qY = dot_ab CY_of / G^2` and `cA1 / v = -cB1 / u`). -/
def P18_regY_of {F : Type*} [Field F] (S Q T x y a b U V : F) : F :=
  let ξS := S - a * T; let ξQ := Q - b * T
  let M0 := A_0U a b ξS ξQ U V / U + A_0V a b ξS ξQ U V / V
  let MY := A_Y a b ξS ξQ U V
  let MX := A_X a b ξS ξQ U V
  let H0 := H0_of S Q T
  let qY := dot_ab (CY_of S Q T x y U V) a b / G_of S Q T x y U V ^ 2
  let qX := dot_ab (QX_num S Q T x y U V) a b / u_of U
  let q1 := H0 * A1_of S Q U V * qY + H0 * B1_of T U V * qX +
    (-cB1_of S Q T a b U V / u_of U) * EB_of S Q T x y U V
  M0 * q1 + (MY * qY + MX * qX) * H0 ^ 2

lemma P18_eq_regX {F : Type*} [Field F] [CharZero F] (S Q T x y a b U V : F)
    (hF : F5_of S Q T x y = 0) (hE0 : E_fn 0 S Q T a b U V = 0)
    (hE1 : E_fn 1 S Q T a b U V = 0) (hU : U ≠ 0) (hV : V ≠ 0)
    (hu : u_of U ≠ 0) (hG : G_of S Q T x y U V ≠ 0) :
    P18_of S Q T x y a b U V = P18_regX_of S Q T x y a b U V := by
  have hCX := (G_sq_cancellation S Q T x y a b U V hF hE0 hE1 hU hV).2
  have hqX : dot_ab (QX_num S Q T x y U V) a b / u_of U =
      dot_ab (CX_of S Q T x y U V) a b / G_of S Q T x y U V ^ 2 := by
    rw [div_eq_div_iff hu (pow_ne_zero 2 hG)]
    linear_combination -hCX
  simp only [P18_of, P18_regX_of, hqX]

lemma P18_eq_regY {F : Type*} [Field F] [CharZero F] (S Q T x y a b U V : F)
    (hF : F5_of S Q T x y = 0) (hE0 : E_fn 0 S Q T a b U V = 0)
    (hE1 : E_fn 1 S Q T a b U V = 0) (hU : U ≠ 0) (hV : V ≠ 0)
    (hu : u_of U ≠ 0) (hv : v_of V ≠ 0) (hG : G_of S Q T x y U V ≠ 0) :
    P18_of S Q T x y a b U V = P18_regY_of S Q T x y a b U V := by
  have hCY := (G_sq_cancellation S Q T x y a b U V hF hE0 hE1 hU hV).1
  have hqY : dot_ab (QY_num S Q T x y U V) a b / v_of V =
      dot_ab (CY_of S Q T x y U V) a b / G_of S Q T x y U V ^ 2 := by
    rw [div_eq_div_iff hv (pow_ne_zero 2 hG)]
    linear_combination -hCY
  have hcA : cA1_of S Q T a b U V / v_of V = -cB1_of S Q T a b U V / u_of U := by
    have h := u_cA1_add_v_cB1 S Q T a b U V
    rw [hE0, hE1, mul_zero, mul_zero, sub_self] at h
    rw [div_eq_div_iff hv hu]
    linear_combination h
  simp only [P18_of, P18_regY_of, hqY, hcA]

lemma pU_ιC_K5 (P : K5[X]) : pU ιC_K5 P U_C = polyC P := by
  simp only [pU, polyC, U_C, ιC_K5, ← Polynomial.eval₂_eq_eval_map]
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp only [eval₂_add, map_add, hp, hq]
  | monomial n c =>
    rw [← C_mul_X_pow_eq_monomial]
    simp only [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, map_mul, map_pow,
      RatFunc.algebraMap_C, RatFunc.algebraMap_X, RingHom.comp_apply]; rfl

lemma pUW_ιC_K5 (x : PairAlg K5[X]) : pUW ιC_K5 x U_C W_C = pairC x := by
  rw [pUW_eq, pU_ιC_K5, pU_ιC_K5, pairC, evalAC]; rfl

lemma E0_AC_zero (a b : A_C) :
    E_fn 0 (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) a b U_C V_C = 0 := by
  have h0 := E0_of_cover ιC_K5 U_C W_C U_C_ne_zero
  have hW_eq : W_C ^ 2 + pU ιC_K5 k5Params.bW U_C * W_C + pU ιC_K5 k5Params.cW U_C = 0 := by
    rw [pU_ιC_K5, pU_ιC_K5]; exact W_C_relation
  rw [hW_eq, mul_zero] at h0
  exact (mul_eq_zero.mp h0).resolve_left U_C_ne_zero

lemma E1_AC_zero (z : A_C) :
    E_fn 1 (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K)
      (z / W_C) (-(polyC k5Params.ca_h * z + pairC k5Params.c0W) / (W_C * polyC k5Params.cb_h))
      U_C V_C = 0 := by
  have hW : W_C ^ 2 + pU ιC_K5 k5Params.bW U_C * W_C + pU ιC_K5 k5Params.cW U_C = 0 := by
    rw [pU_ιC_K5, pU_ιC_K5]; exact W_C_relation
  have h1 := E1_of_cover ιC_K5 (z / W_C)
    (-(polyC k5Params.ca_h * z + pairC k5Params.c0W) / (W_C * polyC k5Params.cb_h))
    U_C W_C U_C_ne_zero hW
  rw [pU_ιC_K5, pU_ιC_K5, pUW_ιC_K5] at h1
  have hcb : polyC k5Params.cb_h ≠ 0 := polyC_ne_zero cb_h_K5_ne_zero
  have hrhs : polyC k5Params.ca_h * (W_C * (z / W_C)) +
      polyC k5Params.cb_h * (W_C * (-(polyC k5Params.ca_h * z + pairC k5Params.c0W) /
        (W_C * polyC k5Params.cb_h))) + pairC k5Params.c0W = 0 := by
    field_simp [W_C_ne_zero, hcb]; ring
  rw [hrhs] at h1
  exact (mul_eq_zero.mp h1).resolve_left U_C_ne_zero

lemma P18_z_AC_eq_regX (z : A_C) :
    P18_z_AC z = P18_regX_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K)
      (z / W_C) (-(polyC k5Params.ca_h * z + pairC k5Params.c0W) / (W_C * polyC k5Params.cb_h))
      U_C V_C :=
  P18_eq_regX _ _ _ _ _ _ _ U_C V_C F5_of_AC (E0_AC_zero _ _) (E1_AC_zero z)
    U_C_ne_zero V_C_ne_zero u_of_U_C_ne_zero G_of_AC_ne_zero

lemma P18_z_AC_eq_regY (z : A_C) :
    P18_z_AC z = P18_regY_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K)
      (z / W_C) (-(polyC k5Params.ca_h * z + pairC k5Params.c0W) / (W_C * polyC k5Params.cb_h))
      U_C V_C :=
  P18_eq_regY _ _ _ _ _ _ _ U_C V_C F5_of_AC (E0_AC_zero _ _) (E1_AC_zero z)
    U_C_ne_zero V_C_ne_zero u_of_U_C_ne_zero v_of_V_C_ne_zero G_of_AC_ne_zero

/-- Mirror `a`-elimination `P18_of` function in `A_C`. -/
def P18_w_AC (w : A_C) : A_C :=
  SheetCalculus.P18_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K)
    (-(polyC k5Params.cb_h * w + pairC k5Params.c0W) / (W_C * polyC k5Params.ca_h))
    (w / W_C) U_C V_C

/-- Numerator of `eta_AC` under the mirror `a`-elimination. -/
def eta_AC_num_w : A_C :=
  let q := interp4 P18_w_AC
  let P1w := remDeg4_P1 (pairC k5Params.e2_2) (pairC k5Params.e2_1) (pairC k5Params.e2_0) q.1 q.2.1 q.2.2.1 q.2.2.2.1
  let P0w := remDeg4_P0 (pairC k5Params.e2_2) (pairC k5Params.e2_1) (pairC k5Params.e2_0) q.1 q.2.1 q.2.2.1 q.2.2.2.2
  let d1w := remDeg3_d1 (pairC k5Params.e2_2) (pairC k5Params.e2_1) (pairC k5Params.e2_0)
    (pairC k5Params.e3_3) (pairC k5Params.e3_2) (pairC k5Params.e3_1)
  let d0w := remDeg3_d0 (pairC k5Params.e2_2) (pairC k5Params.e2_1) (pairC k5Params.e2_0)
    (pairC k5Params.e3_3) (pairC k5Params.e3_2) (pairC k5Params.e3_0)
  (P1w * d0w - P0w * d1w) * U_C ^ 3 * W_C * polyC k5Params.ca_h ^ 4

/-- Exact algebraic equality of `eta_AC` with its mirror `a`-elimination form (no `cb_h` denominator). -/
lemma eta_AC_eq_a_elim :
    eta_AC = eta_AC_num_w /
      (81 * ιC_K5 k5Params.Av0 * (2 * W_C + polyC k5Params.bW) *
        polyC k5Params.Q5_z ^ 3 * pairC k5Params.res_w) := by
  dsimp only [eta_AC, eta_AC_num, eta_AC_num_w]
  set p := interp4 P18_z_AC with hp_def
  set q := interp4 P18_w_AC with hq_def
  set P1z := remDeg4_P1 (pairC k5Params.d2_2) (pairC k5Params.d2_1) (pairC k5Params.d2_0) p.1 p.2.1 p.2.2.1 p.2.2.2.1
  set P0z := remDeg4_P0 (pairC k5Params.d2_2) (pairC k5Params.d2_1) (pairC k5Params.d2_0) p.1 p.2.1 p.2.2.1 p.2.2.2.2
  set P1w := remDeg4_P1 (pairC k5Params.e2_2) (pairC k5Params.e2_1) (pairC k5Params.e2_0) q.1 q.2.1 q.2.2.1 q.2.2.2.1
  set P0w := remDeg4_P0 (pairC k5Params.e2_2) (pairC k5Params.e2_1) (pairC k5Params.e2_0) q.1 q.2.1 q.2.2.1 q.2.2.2.2
  set d1w := remDeg3_d1 (pairC k5Params.e2_2) (pairC k5Params.e2_1) (pairC k5Params.e2_0)
    (pairC k5Params.e3_3) (pairC k5Params.e3_2) (pairC k5Params.e3_1)
  set d0w := remDeg3_d0 (pairC k5Params.e2_2) (pairC k5Params.e2_1) (pairC k5Params.e2_0)
    (pairC k5Params.e3_3) (pairC k5Params.e3_2) (pairC k5Params.e3_0)
  have hcb : polyC k5Params.cb_h ≠ 0 := polyC_ne_zero cb_h_K5_ne_zero
  have hca : polyC k5Params.ca_h ≠ 0 := polyC_ne_zero ca_h_K5_ne_zero
  have hQ5 : polyC k5Params.Q5_z ≠ 0 := polyC_ne_zero Q5_K5_ne_zero
  have hres_z : pairC k5Params.res_z ≠ 0 := pairC_ne_zero_of_pnm nm_z_K5_ne_zero
  have hdisc_E2z : pairC k5Params.disc_E2z ≠ 0 := pairC_ne_zero_of_pnm nm_disc_E2z_K5_ne_zero
  have pairC_pmul (x y : PairAlg K5[X]) : pairC (k5Params.pmul x y) = pairC x * pairC y := by
    simp only [pairC, CoverParams.pmul, PairAlg.map_mul, evalAC_mul]
  have pairC_add (x y : PairAlg K5[X]) : pairC (PairAlg.add x y) = pairC x + pairC y := by
    simp only [pairC, PairAlg.map_add, evalAC_add]
  have pairC_sub (x y : PairAlg K5[X]) : pairC (PairAlg.sub x y) = pairC x - pairC y := by
    simp only [pairC, PairAlg.map_sub, evalAC_sub]
  have pairC_smul (s : K5[X]) (x : PairAlg K5[X]) : pairC (PairAlg.smul s x) = polyC s * pairC x := by
    simp only [pairC, polyC, PairAlg.map_smul, evalAC_smul]
  have pairC_ofScalar (s : K5[X]) : pairC (PairAlg.ofScalar s) = polyC s := by
    simp only [pairC, polyC, PairAlg.map_ofScalar, evalAC_ofScalar]
  have pairC_W : pairC PairAlg.W = W_C := by simp [pairC, PairAlg.map_W, evalAC_W]
  have polyC_add (P Q : K5[X]) : polyC (P + Q) = polyC P + polyC Q := by simp only [polyC, map_add]
  have polyC_sub (P Q : K5[X]) : polyC (P - Q) = polyC P - polyC Q := by simp only [polyC, map_sub]
  have polyC_neg (P : K5[X]) : polyC (-P) = -polyC P := by simp only [polyC, map_neg]
  have polyC_mul (P Q : K5[X]) : polyC (P * Q) = polyC P * polyC Q := by simp only [polyC, map_mul]
  have polyC_pow (P : K5[X]) (n : ℕ) : polyC (P ^ n) = polyC P ^ n := by simp only [polyC, map_pow]
  have polyC_ofNat (n : ℕ) [n.AtLeastTwo] : polyC (OfNat.ofNat n) = OfNat.ofNat n := by
    simp only [polyC, map_ofNat]
  -- Step 1: `ca_h^6 * res_z = cb_h^6 * res_w` via `syl5_elim_symm_aux`!
  have hres_symm : polyC k5Params.ca_h ^ 6 * pairC k5Params.res_z =
      polyC k5Params.cb_h ^ 6 * pairC k5Params.res_w := by
    apply mul_left_cancel₀ (pow_ne_zero 6 hcb)
    have haux := syl5_elim_symm_aux
      (polyC k5Params.ca_h) (polyC k5Params.cb_h) (pairC k5Params.c0W)
      (polyC k5Params.q20) (polyC k5Params.q11) (polyC k5Params.q02) (W_C * pairC k5Params.k2W)
      (polyC k5Params.c30) (polyC k5Params.c21) (polyC k5Params.c12) (polyC k5Params.c03)
      (W_C * W_C * pairC k5Params.k3W)
    have hpairC_evalAt (x : PairAlg K5[X]) :
        pairC x = PairAlg.evalAt W_C (PairAlg.map (ιC_rat.comp toRat) x) := rfl
    have hpair_syl5 (a2 a1 a0 b3 b2 b1 b0 : PairAlg K5[X]) :
        pairC (syl5Pair k5Params.bW k5Params.cW a2 a1 a0 b3 b2 b1 b0) =
          syl5 (pairC a2) (pairC a1) (pairC a0) (pairC b3) (pairC b2) (pairC b1) (pairC b0) := by
      simp only [hpairC_evalAt, map_syl5Pair]
      exact evalAt_syl5Pair _ _ _ _ _ _ _ _ _ W_C W_C_relation
    have hresz_eq : pairC k5Params.res_z = syl5 (pairC k5Params.d2_2) (pairC k5Params.d2_1)
        (pairC k5Params.d2_0) (pairC k5Params.d3_3) (pairC k5Params.d3_2)
        (pairC k5Params.d3_1) (pairC k5Params.d3_0) := hpair_syl5 ..
    have hresw_eq : pairC k5Params.res_w = syl5 (pairC k5Params.e2_2) (pairC k5Params.e2_1)
        (pairC k5Params.e2_0) (pairC k5Params.e3_3) (pairC k5Params.e3_2)
        (pairC k5Params.e3_1) (pairC k5Params.e3_0) := hpair_syl5 ..
    rw [hresz_eq, hresw_eq]
    have hQ5_eq : pairC k5Params.d2_2 =
        polyC k5Params.q20 * polyC k5Params.cb_h ^ 2 -
        polyC k5Params.q11 * polyC k5Params.ca_h * polyC k5Params.cb_h +
        polyC k5Params.q02 * polyC k5Params.ca_h ^ 2 := by
      simp only [CoverParams.d2_2, CoverParams.Q5_z, pairC_ofScalar, polyC_add, polyC_sub,
        polyC_mul, polyC_pow]
    have he22_eq : pairC k5Params.e2_2 = pairC k5Params.d2_2 := rfl
    have hQ7_eq : pairC k5Params.d3_3 =
        polyC k5Params.c30 * polyC k5Params.cb_h ^ 3 -
        polyC k5Params.c21 * polyC k5Params.ca_h * polyC k5Params.cb_h ^ 2 +
        polyC k5Params.c12 * polyC k5Params.ca_h ^ 2 * polyC k5Params.cb_h -
        polyC k5Params.c03 * polyC k5Params.ca_h ^ 3 := by
      simp only [CoverParams.d3_3, CoverParams.Q7_z, pairC_ofScalar, polyC_add, polyC_sub,
        polyC_mul, polyC_pow]
    have hd21 : pairC k5Params.d2_1 = (-polyC k5Params.q11 * polyC k5Params.cb_h +
        2 * polyC k5Params.q02 * polyC k5Params.ca_h) * pairC k5Params.c0W := by
      simp only [CoverParams.d2_1, pairC_smul, polyC_add, polyC_neg, polyC_mul, polyC_ofNat]
    have hd20 : pairC k5Params.d2_0 = polyC k5Params.q02 * pairC k5Params.c0W ^ 2 +
        polyC k5Params.cb_h ^ 2 * (W_C * pairC k5Params.k2W) := by
      simp only [CoverParams.d2_0, pairC_add, pairC_smul, pairC_pmul, pairC_W, polyC_pow]; ring
    have hd32 : pairC k5Params.d3_2 = (-polyC k5Params.c21 * polyC k5Params.cb_h ^ 2 +
        2 * polyC k5Params.c12 * polyC k5Params.ca_h * polyC k5Params.cb_h -
        3 * polyC k5Params.c03 * polyC k5Params.ca_h ^ 2) * pairC k5Params.c0W := by
      simp only [CoverParams.d3_2, pairC_smul, polyC_add, polyC_sub, polyC_neg, polyC_mul,
        polyC_pow, polyC_ofNat]
    have hd31 : pairC k5Params.d3_1 = (polyC k5Params.c12 * polyC k5Params.cb_h -
        3 * polyC k5Params.c03 * polyC k5Params.ca_h) * pairC k5Params.c0W ^ 2 := by
      simp only [CoverParams.d3_1, pairC_smul, pairC_pmul, polyC_sub, polyC_mul, polyC_ofNat]; ring
    have hd30 : pairC k5Params.d3_0 = -polyC k5Params.c03 * pairC k5Params.c0W ^ 3 +
        polyC k5Params.cb_h ^ 3 * (W_C * W_C * pairC k5Params.k3W) := by
      simp only [CoverParams.d3_0, pairC_add, pairC_smul, pairC_pmul, pairC_W, polyC_neg, polyC_pow]; ring
    have he21 : pairC k5Params.e2_1 = (-polyC k5Params.q11 * polyC k5Params.ca_h +
        2 * polyC k5Params.q20 * polyC k5Params.cb_h) * pairC k5Params.c0W := by
      simp only [CoverParams.e2_1, pairC_smul, polyC_add, polyC_neg, polyC_mul, polyC_ofNat]
    have he20 : pairC k5Params.e2_0 = polyC k5Params.q20 * pairC k5Params.c0W ^ 2 +
        polyC k5Params.ca_h ^ 2 * (W_C * pairC k5Params.k2W) := by
      simp only [CoverParams.e2_0, pairC_add, pairC_smul, pairC_pmul, pairC_W, polyC_pow]; ring
    have he33 : pairC k5Params.e3_3 = -polyC k5Params.c30 * polyC k5Params.cb_h ^ 3 +
        polyC k5Params.c21 * polyC k5Params.ca_h * polyC k5Params.cb_h ^ 2 -
        polyC k5Params.c12 * polyC k5Params.ca_h ^ 2 * polyC k5Params.cb_h +
        polyC k5Params.c03 * polyC k5Params.ca_h ^ 3 := by
      simp only [CoverParams.e3_3, pairC_ofScalar, polyC_add, polyC_sub, polyC_neg,
        polyC_mul, polyC_pow]
    have he32 : pairC k5Params.e3_2 = (-3 * polyC k5Params.c30 * polyC k5Params.cb_h ^ 2 +
        2 * polyC k5Params.c21 * polyC k5Params.ca_h * polyC k5Params.cb_h -
        polyC k5Params.c12 * polyC k5Params.ca_h ^ 2) * pairC k5Params.c0W := by
      simp only [CoverParams.e3_2, pairC_smul, polyC_add, polyC_sub, polyC_neg, polyC_mul,
        polyC_pow, polyC_ofNat]
    have he31 : pairC k5Params.e3_1 = (-3 * polyC k5Params.c30 * polyC k5Params.cb_h +
        polyC k5Params.c21 * polyC k5Params.ca_h) * pairC k5Params.c0W ^ 2 := by
      simp only [CoverParams.e3_1, pairC_smul, pairC_pmul, polyC_add, polyC_neg,
        polyC_mul, polyC_ofNat]; ring
    have he30 : pairC k5Params.e3_0 = -polyC k5Params.c30 * pairC k5Params.c0W ^ 3 +
        polyC k5Params.ca_h ^ 3 * (W_C * W_C * pairC k5Params.k3W) := by
      simp only [CoverParams.e3_0, pairC_add, pairC_smul, pairC_pmul, pairC_W, polyC_neg, polyC_pow]; ring
    rw [he22_eq, hQ5_eq, hQ7_eq, hd21, hd20, hd32, hd31, hd30, he21, he20, he33, he32, he31, he30]
    exact haux
  have hres_w : pairC k5Params.res_w ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hres_symm
    exact mul_ne_zero (pow_ne_zero 6 hca) hres_z hres_symm
  -- Step 2: `-(P1z * d0z - P0z * d1z) * ca_h^2 = (P1w * d0w - P0w * d1w) * cb_h^2` in SplittingField!
  have hcomb_symm :
      -(P1z * pairC k5Params.d0_z - P0z * pairC k5Params.d1_z) * polyC k5Params.ca_h ^ 2 =
        (P1w * d0w - P0w * d1w) * polyC k5Params.cb_h ^ 2 := by
    let Qz : A_C[X] := C (pairC k5Params.d2_2) * X ^ 2 + C (pairC k5Params.d2_1) * X +
      C (pairC k5Params.d2_0)
    let E := Polynomial.SplittingField Qz
    let j : A_C →+* E := algebraMap A_C E
    have : CharZero E := charZero_of_injective_ringHom j.injective
    apply j.injective
    have hQz_deg : Qz.natDegree = 2 := by
      have h2 : pairC k5Params.d2_2 ≠ 0 := by
        simpa [CoverParams.d2_2, pairC_ofScalar] using hQ5
      have hlt : (C (pairC k5Params.d2_1) * X + C (pairC k5Params.d2_0)).natDegree <
          (C (pairC k5Params.d2_2) * X ^ 2).natDegree := by
        rw [Polynomial.natDegree_C_mul_X_pow 2 (pairC k5Params.d2_2) h2]
        refine (natDegree_add_le _ _).trans_lt (max_lt ?_ (by simp))
        exact (natDegree_C_mul_le _ _).trans_lt (by simp)
      rw [show Qz = C (pairC k5Params.d2_2) * X ^ 2 +
          (C (pairC k5Params.d2_1) * X + C (pairC k5Params.d2_0)) by simp [Qz, add_assoc],
        natDegree_add_eq_left_of_natDegree_lt hlt,
        Polynomial.natDegree_C_mul_X_pow 2 (pairC k5Params.d2_2) h2]
    have hQz_lc : Qz.leadingCoeff = pairC k5Params.d2_2 := by
      rw [Polynomial.leadingCoeff, hQz_deg]
      simp [Qz, Polynomial.coeff_X_pow]
    have hsplit : (Qz.map j).Splits := Polynomial.SplittingField.splits Qz
    have hcard : (Qz.map j).roots.card = 2 := by
      rw [← Polynomial.Splits.natDegree_eq_card_roots hsplit, Polynomial.natDegree_map, hQz_deg]
    obtain ⟨z1, z2, hroots⟩ := Multiset.card_eq_two.mp hcard
    have hfac : Qz.map j = C (j (pairC k5Params.d2_2)) * (X - C z1) * (X - C z2) := by
      have hprod := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
        (show (Qz.map j).roots.card = (Qz.map j).natDegree by rw [hcard, Polynomial.natDegree_map, hQz_deg])
      rw [hroots, Polynomial.leadingCoeff_map, hQz_lc] at hprod
      simpa [mul_assoc] using hprod.symm
    have hq1_eq : j (pairC k5Params.d2_1) = -j (pairC k5Params.d2_2) * (z1 + z2) := by
      have h1 := congrArg (fun f : E[X] => f.coeff 1) hfac
      have hexp : C (j (pairC k5Params.d2_2)) * (X - C z1) * (X - C z2) =
          C (j (pairC k5Params.d2_2) * z1 * z2) +
          C (-j (pairC k5Params.d2_2) * (z1 + z2)) * X +
          C (j (pairC k5Params.d2_2)) * X ^ 2 := by
        simp only [map_add, map_mul, map_neg]; ring
      rw [hexp] at h1
      simp only [Qz, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
        Polynomial.map_pow, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C,
        Polynomial.coeff_X, Polynomial.coeff_X_pow] at h1
      simpa using h1
    have hq0_eq : j (pairC k5Params.d2_0) = j (pairC k5Params.d2_2) * z1 * z2 := by
      have h0 := congrArg (fun f : E[X] => f.coeff 0) hfac
      have hexp : C (j (pairC k5Params.d2_2)) * (X - C z1) * (X - C z2) =
          C (j (pairC k5Params.d2_2) * z1 * z2) +
          C (-j (pairC k5Params.d2_2) * (z1 + z2)) * X +
          C (j (pairC k5Params.d2_2)) * X ^ 2 := by
        simp only [map_add, map_mul, map_neg]; ring
      rw [hexp] at h0
      simp only [Qz, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
        Polynomial.map_pow, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C,
        Polynomial.coeff_X, Polynomial.coeff_X_pow] at h0
      simpa using h0
    have hz12_ne : z1 - z2 ≠ 0 := by
      intro h0
      have hd_eq : j (pairC k5Params.disc_E2z) =
          j (pairC k5Params.d2_2) ^ 2 * (z1 - z2) ^ 2 := by
        have hd : pairC k5Params.disc_E2z = pairC k5Params.d2_1 ^ 2 -
            4 * pairC k5Params.d2_2 * pairC k5Params.d2_0 := by
          simp only [CoverParams.disc_E2z, pairC_sub, pairC_smul, pairC_pmul, polyC_ofNat]; ring
        rw [hd, map_sub, map_pow, map_mul, map_mul, map_ofNat, hq1_eq, hq0_eq]; ring
      rw [h0, zero_pow (by omega), mul_zero] at hd_eq
      exact hdisc_E2z (j.injective (by simpa using hd_eq))
    let w1 : E := -(j (polyC k5Params.ca_h) * z1 + j (pairC k5Params.c0W)) / j (polyC k5Params.cb_h)
    let w2 : E := -(j (polyC k5Params.ca_h) * z2 + j (pairC k5Params.c0W)) / j (polyC k5Params.cb_h)
    have hcbE : j (polyC k5Params.cb_h) ≠ 0 := (map_ne_zero_iff j j.injective).mpr hcb
    have hcaE : j (polyC k5Params.ca_h) ≠ 0 := (map_ne_zero_iff j j.injective).mpr hca
    have hw12 : w1 - w2 = -(j (polyC k5Params.ca_h) / j (polyC k5Params.cb_h)) * (z1 - z2) := by
      dsimp only [w1, w2]; field_simp [hcbE]; ring
    have he21_eq : j (pairC k5Params.e2_1) = -j (pairC k5Params.e2_2) * (w1 + w2) := by
      have hrel : polyC k5Params.cb_h ^ 2 * pairC k5Params.e2_1 =
          2 * pairC k5Params.d2_2 * (-polyC k5Params.cb_h) * (-pairC k5Params.c0W) +
          polyC k5Params.ca_h * pairC k5Params.d2_1 * (-polyC k5Params.cb_h) := by
        simp only [CoverParams.e2_1, CoverParams.d2_2, CoverParams.d2_1, CoverParams.Q5_z,
          pairC_smul, pairC_ofScalar, polyC_add, polyC_sub, polyC_neg, polyC_mul, polyC_pow,
          polyC_ofNat]; ring
      have hrelE := congrArg j hrel
      simp only [map_add, map_mul, map_pow, map_neg, map_ofNat] at hrelE
      rw [hq1_eq] at hrelE
      have he22 : j (pairC k5Params.e2_2) = j (pairC k5Params.d2_2) := rfl
      rw [he22]
      dsimp only [w1, w2]
      apply mul_left_cancel₀ (pow_ne_zero 2 hcbE)
      field_simp [hcbE] at hrelE ⊢
      linear_combination hrelE
    have he20_eq : j (pairC k5Params.e2_0) = j (pairC k5Params.e2_2) * w1 * w2 := by
      have hrel : polyC k5Params.cb_h ^ 2 * pairC k5Params.e2_0 =
          pairC k5Params.d2_2 * (-pairC k5Params.c0W) ^ 2 +
          polyC k5Params.ca_h * pairC k5Params.d2_1 * (-pairC k5Params.c0W) +
          polyC k5Params.ca_h ^ 2 * pairC k5Params.d2_0 := by
        simp only [CoverParams.e2_0, CoverParams.d2_2, CoverParams.d2_1, CoverParams.d2_0,
          CoverParams.Q5_z, pairC_add, pairC_smul, pairC_pmul, pairC_ofScalar, pairC_W,
          polyC_add, polyC_sub, polyC_neg, polyC_mul, polyC_pow, polyC_ofNat]; ring
      have hrelE := congrArg j hrel
      simp only [map_add, map_mul, map_pow, map_neg] at hrelE
      rw [hq1_eq, hq0_eq] at hrelE
      have he22 : j (pairC k5Params.e2_2) = j (pairC k5Params.d2_2) := rfl
      rw [he22]
      dsimp only [w1, w2]
      apply mul_left_cancel₀ (pow_ne_zero 2 hcbE)
      field_simp [hcbE] at hrelE ⊢
      linear_combination hrelE
    have hE3_rel (z : E) :
        let w := -(j (polyC k5Params.ca_h) * z + j (pairC k5Params.c0W)) / j (polyC k5Params.cb_h)
        j (polyC k5Params.cb_h) ^ 3 *
          (j (pairC k5Params.e3_3) * w ^ 3 + j (pairC k5Params.e3_2) * w ^ 2 +
           j (pairC k5Params.e3_1) * w + j (pairC k5Params.e3_0)) =
        j (polyC k5Params.ca_h) ^ 3 *
          (j (pairC k5Params.d3_3) * z ^ 3 + j (pairC k5Params.d3_2) * z ^ 2 +
           j (pairC k5Params.d3_1) * z + j (pairC k5Params.d3_0)) := by
      intro w
      have h33 : polyC k5Params.cb_h ^ 3 * pairC k5Params.e3_3 =
          pairC k5Params.d3_3 * (-polyC k5Params.cb_h) ^ 3 := by
        simp only [CoverParams.e3_3, CoverParams.d3_3, CoverParams.Q7_z, pairC_ofScalar,
          polyC_add, polyC_sub, polyC_neg, polyC_mul, polyC_pow]; ring
      have h32 : polyC k5Params.cb_h ^ 3 * pairC k5Params.e3_2 =
          3 * pairC k5Params.d3_3 * (-polyC k5Params.cb_h) ^ 2 * (-pairC k5Params.c0W) +
          polyC k5Params.ca_h * pairC k5Params.d3_2 * (-polyC k5Params.cb_h) ^ 2 := by
        simp only [CoverParams.e3_2, CoverParams.d3_3, CoverParams.d3_2, CoverParams.Q7_z,
          pairC_smul, pairC_ofScalar, polyC_add, polyC_sub, polyC_neg, polyC_mul, polyC_pow,
          polyC_ofNat]; ring
      have h31 : polyC k5Params.cb_h ^ 3 * pairC k5Params.e3_1 =
          3 * pairC k5Params.d3_3 * (-polyC k5Params.cb_h) * (-pairC k5Params.c0W) ^ 2 +
          2 * (polyC k5Params.ca_h * pairC k5Params.d3_2) * (-polyC k5Params.cb_h) * (-pairC k5Params.c0W) +
          polyC k5Params.ca_h ^ 2 * pairC k5Params.d3_1 * (-polyC k5Params.cb_h) := by
        simp only [CoverParams.e3_1, CoverParams.d3_3, CoverParams.d3_2, CoverParams.d3_1,
          CoverParams.Q7_z, pairC_smul, pairC_pmul, pairC_ofScalar, polyC_add, polyC_sub,
          polyC_neg, polyC_mul, polyC_pow, polyC_ofNat]; ring
      have h30 : polyC k5Params.cb_h ^ 3 * pairC k5Params.e3_0 =
          pairC k5Params.d3_3 * (-pairC k5Params.c0W) ^ 3 +
          polyC k5Params.ca_h * pairC k5Params.d3_2 * (-pairC k5Params.c0W) ^ 2 +
          polyC k5Params.ca_h ^ 2 * pairC k5Params.d3_1 * (-pairC k5Params.c0W) +
          polyC k5Params.ca_h ^ 3 * pairC k5Params.d3_0 := by
        simp only [CoverParams.e3_0, CoverParams.d3_3, CoverParams.d3_2, CoverParams.d3_1,
          CoverParams.d3_0, CoverParams.Q7_z, pairC_add, pairC_smul, pairC_pmul, pairC_ofScalar,
          pairC_W, polyC_add, polyC_sub, polyC_neg, polyC_mul, polyC_pow, polyC_ofNat]; ring
      have j33 := congrArg j h33; have j32 := congrArg j h32
      have j31 := congrArg j h31; have j30 := congrArg j h30
      simp only [map_add, map_mul, map_pow, map_neg, map_ofNat] at j33 j32 j31 j30
      dsimp only [w]
      have hbw : j (polyC k5Params.cb_h) * (-(j (polyC k5Params.ca_h) * z + j (pairC k5Params.c0W)) /
          j (polyC k5Params.cb_h)) = -(j (polyC k5Params.ca_h) * z + j (pairC k5Params.c0W)) :=
        mul_div_cancel₀ _ hcbE
      linear_combination w ^ 3 * j33 + w ^ 2 * j32 + w * j31 + j30 +
        (j (pairC k5Params.d3_3) * ((-j (polyC k5Params.cb_h) * w - j (pairC k5Params.c0W)) ^ 2 +
          (-j (polyC k5Params.cb_h) * w - j (pairC k5Params.c0W)) * (j (polyC k5Params.ca_h) * z) +
          (j (polyC k5Params.ca_h) * z) ^ 2) +
         j (polyC k5Params.ca_h) * j (pairC k5Params.d3_2) *
          ((-j (polyC k5Params.cb_h) * w - j (pairC k5Params.c0W)) + j (polyC k5Params.ca_h) * z) +
         j (polyC k5Params.ca_h) ^ 2 * j (pairC k5Params.d3_1)) * (-hbw)
    -- Evaluate degree-4 polynomials `P18_z` and `P18_w` in `E` and match at `(z1, w1)` and `(z2, w2)`!
    let P18_z_E : E → E := fun z =>
      P18_of (j (ιC_K5 S_K)) (j (ιC_K5 Q_K)) (j (ιC_K5 T_K)) (j (ιC_K5 x_K)) (j (ιC_K5 y_K))
        (z / j W_C) (-(j (polyC k5Params.ca_h) * z + j (pairC k5Params.c0W)) /
          (j W_C * j (polyC k5Params.cb_h))) (j U_C) (j V_C)
    let P18_w_E : E → E := fun w =>
      P18_of (j (ιC_K5 S_K)) (j (ιC_K5 Q_K)) (j (ιC_K5 T_K)) (j (ιC_K5 x_K)) (j (ιC_K5 y_K))
        (-(j (polyC k5Params.cb_h) * w + j (pairC k5Params.c0W)) /
          (j W_C * j (polyC k5Params.ca_h))) (w / j W_C) (j U_C) (j V_C)
    have hmap_P18 (S Q T x y a b U V : A_C) :
        j (P18_of S Q T x y a b U V) = P18_of (j S) (j Q) (j T) (j x) (j y) (j a) (j b) (j U) (j V) := by
      simp only [P18_of, A_0U, A_0V, A_Y, A_X, numM, q1_a2, q1_a1, q1_a0, q2_b2, q2_b1, q2_b0,
        dH_dS, dH_dQ, H0_of, A1_of, B1_of, u_of, v_of, cA1_of, dA1_fn, dH0_fn, EB_of, W2_of,
        DX2_of, DY2_of, u3_of, v3_of, dF5_fn, br_fn, LX_of, LY_of, dLX_fn, dLY_fn,
        dot_ab, QY_num, QX_num, Omega_F, dDX2_F, dDY2_F, F_contract, om_fn, dDX2_fn, dDY2_fn,
        map_add, map_sub, map_mul, map_div₀, map_pow, map_neg, map_ofNat, map_one, map_zero]
    have hp_E : (j p.1, j p.2.1, j p.2.2.1, j p.2.2.2.1, j p.2.2.2.2) = interp4 P18_z_E := by
      simpa [hp_def] using map_interp4 j P18_z_AC P18_z_E (fun z => by
        simp only [P18_z_AC, P18_z_E, hmap_P18, map_div₀, map_neg, map_add, map_mul])
    have hq_E : (j q.1, j q.2.1, j q.2.2.1, j q.2.2.2.1, j q.2.2.2.2) = interp4 P18_w_E := by
      simpa [hq_def] using map_interp4 j P18_w_AC P18_w_E (fun w => by
        simp only [P18_w_AC, P18_w_E, hmap_P18, map_div₀, map_neg, map_add, map_mul])
    have hP18z_deg4 : IsPolyDeg 4 P18_z_E := by
      refine (P18_of_isPolyDeg4 (j (ιC_K5 S_K)) (j (ιC_K5 Q_K)) (j (ιC_K5 T_K))
        (j (ιC_K5 x_K)) (j (ιC_K5 y_K)) (j U_C) (j V_C)
        (j W_C)⁻¹ 0 (-j (polyC k5Params.ca_h) / (j W_C * j (polyC k5Params.cb_h)))
        (-j (pairC k5Params.c0W) / (j W_C * j (polyC k5Params.cb_h)))).congr (fun z => ?_)
      dsimp only [P18_z_E]; congr 1 <;> ring
    have hP18w_deg4 : IsPolyDeg 4 P18_w_E := by
      refine (P18_of_isPolyDeg4 (j (ιC_K5 S_K)) (j (ιC_K5 Q_K)) (j (ιC_K5 T_K))
        (j (ιC_K5 x_K)) (j (ιC_K5 y_K)) (j U_C) (j V_C)
        (-j (polyC k5Params.cb_h) / (j W_C * j (polyC k5Params.ca_h)))
        (-j (pairC k5Params.c0W) / (j W_C * j (polyC k5Params.ca_h)))
        (j W_C)⁻¹ 0).congr (fun w => ?_)
      dsimp only [P18_w_E]; congr 1 <;> ring
    have hPz_eval : ∀ z : E, P18_z_E z =
        j p.1 * z ^ 4 + j p.2.1 * z ^ 3 + j p.2.2.1 * z ^ 2 + j p.2.2.2.1 * z + j p.2.2.2.2 := by
      have h := hP18z_deg4.eq_deg4; rw [← hp_E] at h; exact h
    have hPw_eval : ∀ w : E, P18_w_E w =
        j q.1 * w ^ 4 + j q.2.1 * w ^ 3 + j q.2.2.1 * w ^ 2 + j q.2.2.2.1 * w + j q.2.2.2.2 := by
      have h := hP18w_deg4.eq_deg4; rw [← hq_E] at h; exact h
    have hPz_eq_Pw (z : E) : P18_w_E (-(j (polyC k5Params.ca_h) * z + j (pairC k5Params.c0W)) /
        j (polyC k5Params.cb_h)) = P18_z_E z := by
      dsimp only [P18_w_E, P18_z_E]
      congr 1
      · have hW_E : j W_C ≠ 0 := (map_ne_zero_iff j j.injective).mpr W_C_ne_zero
        field_simp [hW_E, hcaE, hcbE]; ring
      · ring
    -- Apply `remDeg4_comb_roots` to both `z` and `w`!
    have hd1z_map : j (pairC k5Params.d1_z) = remDeg3_d1 (j (pairC k5Params.d2_2))
        (j (pairC k5Params.d2_1)) (j (pairC k5Params.d2_0))
        (j (pairC k5Params.d3_3)) (j (pairC k5Params.d3_2)) (j (pairC k5Params.d3_1)) := by
      simp [CoverParams.d1_z, remDeg3_d1, pairC_sub, pairC_pmul]
    have hd0z_map : j (pairC k5Params.d0_z) = remDeg3_d0 (j (pairC k5Params.d2_2))
        (j (pairC k5Params.d2_1)) (j (pairC k5Params.d2_0))
        (j (pairC k5Params.d3_3)) (j (pairC k5Params.d3_2)) (j (pairC k5Params.d3_0)) := by
      simp [CoverParams.d0_z, remDeg3_d0, pairC_sub, pairC_pmul]
    have hcz := remDeg4_comb_roots (j (pairC k5Params.d2_2))
      (j (pairC k5Params.d3_3)) (j (pairC k5Params.d3_2)) (j (pairC k5Params.d3_1)) (j (pairC k5Params.d3_0))
      (j p.1) (j p.2.1) (j p.2.2.1) (j p.2.2.2.1) (j p.2.2.2.2) z1 z2
    have hcw := remDeg4_comb_roots (j (pairC k5Params.e2_2))
      (j (pairC k5Params.e3_3)) (j (pairC k5Params.e3_2)) (j (pairC k5Params.e3_1)) (j (pairC k5Params.e3_0))
      (j q.1) (j q.2.1) (j q.2.2.1) (j q.2.2.2.1) (j q.2.2.2.2) w1 w2
    dsimp only at hcz hcw
    rw [← hq1_eq, ← hq0_eq, ← hd1z_map, ← hd0z_map, ← hPz_eval z1, ← hPz_eval z2] at hcz
    rw [← he21_eq, ← he20_eq, ← hPw_eval w1, ← hPw_eval w2] at hcw
    have hP1z_map : remDeg4_P1 (j (pairC k5Params.d2_2)) (j (pairC k5Params.d2_1))
        (j (pairC k5Params.d2_0)) (j p.1) (j p.2.1) (j p.2.2.1) (j p.2.2.2.1) = j P1z := by
      simp [P1z, remDeg4_P1]
    have hP0z_map : remDeg4_P0 (j (pairC k5Params.d2_2)) (j (pairC k5Params.d2_1))
        (j (pairC k5Params.d2_0)) (j p.1) (j p.2.1) (j p.2.2.1) (j p.2.2.2.2) = j P0z := by
      simp [P0z, remDeg4_P0]
    have hP1w_map : remDeg4_P1 (j (pairC k5Params.e2_2)) (j (pairC k5Params.e2_1))
        (j (pairC k5Params.e2_0)) (j q.1) (j q.2.1) (j q.2.2.1) (j q.2.2.2.1) = j P1w := by
      simp [P1w, remDeg4_P1]
    have hP0w_map : remDeg4_P0 (j (pairC k5Params.e2_2)) (j (pairC k5Params.e2_1))
        (j (pairC k5Params.e2_0)) (j q.1) (j q.2.1) (j q.2.2.1) (j q.2.2.2.2) = j P0w := by
      simp [P0w, remDeg4_P0]
    have hd1w_map : remDeg3_d1 (j (pairC k5Params.e2_2)) (j (pairC k5Params.e2_1))
        (j (pairC k5Params.e2_0)) (j (pairC k5Params.e3_3)) (j (pairC k5Params.e3_2))
        (j (pairC k5Params.e3_1)) = j d1w := by
      simp [d1w, remDeg3_d1]
    have hd0w_map : remDeg3_d0 (j (pairC k5Params.e2_2)) (j (pairC k5Params.e2_1))
        (j (pairC k5Params.e2_0)) (j (pairC k5Params.e3_3)) (j (pairC k5Params.e3_2))
        (j (pairC k5Params.e3_0)) = j d0w := by
      simp [d0w, remDeg3_d0]
    rw [hP1z_map, hP0z_map] at hcz
    rw [hP1w_map, hP0w_map, hd1w_map, hd0w_map, hw12, hPz_eq_Pw z1, hPz_eq_Pw z2] at hcw
    have hE3_1 := hE3_rel z1; have hE3_2 := hE3_rel z2
    dsimp only at hE3_1 hE3_2
    change j (polyC k5Params.cb_h) ^ 3 * (j (pairC k5Params.e3_3) * w1 ^ 3 +
      j (pairC k5Params.e3_2) * w1 ^ 2 + j (pairC k5Params.e3_1) * w1 + j (pairC k5Params.e3_0)) = _ at hE3_1
    change j (polyC k5Params.cb_h) ^ 3 * (j (pairC k5Params.e3_3) * w2 ^ 3 +
      j (pairC k5Params.e3_2) * w2 ^ 2 + j (pairC k5Params.e3_1) * w2 + j (pairC k5Params.e3_0)) = _ at hE3_2
    have hmul : j (polyC k5Params.cb_h) ^ 3 *
        ((j P1w * j d0w - j P0w * j d1w) * (-(j (polyC k5Params.ca_h) / j (polyC k5Params.cb_h)) * (z1 - z2))) =
        j (polyC k5Params.ca_h) ^ 3 * ((j P1z * j (pairC k5Params.d0_z) - j P0z * j (pairC k5Params.d1_z)) * (z1 - z2)) := by
      rw [hcw, hcz]
      have he22 : j (pairC k5Params.e2_2) = j (pairC k5Params.d2_2) := rfl
      rw [he22]
      linear_combination j (pairC k5Params.d2_2) ^ 5 * P18_z_E z1 * hE3_2 -
        j (pairC k5Params.d2_2) ^ 5 * P18_z_E z2 * hE3_1
    have hfac_ne : j (polyC k5Params.ca_h) * (z1 - z2) ≠ 0 := mul_ne_zero hcaE hz12_ne
    simp only [map_neg, map_mul, map_sub, map_pow]
    apply mul_right_cancel₀ hfac_ne
    have hcb3 : j (polyC k5Params.cb_h) ^ 3 * (-(j (polyC k5Params.ca_h) / j (polyC k5Params.cb_h))) =
        -j (polyC k5Params.cb_h) ^ 2 * j (polyC k5Params.ca_h) := by
      have hc : j (polyC k5Params.cb_h) * (j (polyC k5Params.ca_h) / j (polyC k5Params.cb_h)) =
          j (polyC k5Params.ca_h) := mul_div_cancel₀ _ hcbE
      linear_combination -j (polyC k5Params.cb_h) ^ 2 * hc
    linear_combination hmul - (j P1w * j d0w - j P0w * j d1w) * (z1 - z2) * hcb3
  -- Step 3: Combine `hcomb_symm` and `hres_symm`!
  have hden_ne : (81 * ιC_K5 k5Params.Av0 * (2 * W_C + polyC k5Params.bW) *
      polyC k5Params.Q5_z ^ 3 : A_C) ≠ 0 := by
    have h2W : 2 * W_C + polyC k5Params.bW ≠ 0 := by
      intro h0
      have hsq : (2 * W_C + polyC k5Params.bW) ^ 2 = polyC k5Params.disc_E0 := by
        simp only [polyC, CoverParams.disc_E0, map_sub, map_pow, map_mul, map_ofNat]
        linear_combination 4 * W_C_relation
      rw [h0, zero_pow (by omega)] at hsq
      have hdisc_ne : k5Params.disc_E0 ≠ 0 := by
        intro hd0
        have hcop := isCoprime_P34_disc_E0
        rw [hd0, isCoprime_zero_right] at hcop
        have hdeg := Polynomial.natDegree_eq_zero_of_isUnit hcop
        rw [P34_K5_natDegree] at hdeg; omega
      exact polyC_ne_zero hdisc_ne hsq.symm
    have h81 : (81 : A_C) ≠ 0 := by exact_mod_cast (by decide : (81 : ℕ) ≠ 0)
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h81
      ((map_ne_zero_iff ιC_K5 ιC_K5.injective).mpr Av0_K5_ne_zero)) h2W) (pow_ne_zero 3 hQ5)
  rw [div_eq_div_iff (mul_ne_zero hden_ne hres_z) (mul_ne_zero hden_ne hres_w)]
  apply mul_left_cancel₀ (pow_ne_zero 2 hca)
  linear_combination
    U_C ^ 3 * W_C * (81 * ιC_K5 k5Params.Av0 * (2 * W_C + polyC k5Params.bW) *
      polyC k5Params.Q5_z ^ 3) * polyC k5Params.cb_h ^ 4 * pairC k5Params.res_w * hcomb_symm -
    U_C ^ 3 * W_C * (81 * ιC_K5 k5Params.Av0 * (2 * W_C + polyC k5Params.bW) *
      polyC k5Params.Q5_z ^ 3) * (P1w * d0w - P0w * d1w) * hres_symm

-- Regularity algebra in `A_C` relative to a point `r : L`.
section RegAC
variable {L : Type*} [Field L] [Algebra K5 L]

private abbrev RegAt (r : L) (g : RatFunc K5) : Prop :=
  RegularAt r (mapRatFunc (algebraMap K5 L) g)

private abbrev valAt (r : L) (g : RatFunc K5) : L :=
  valueAt r (mapRatFunc (algebraMap K5 L) g)

private abbrev RegUnitAt (r : L) (g : RatFunc K5) : Prop :=
  RegAt r g ∧ valAt r g ≠ 0

private structure RegAC (r : L) (x : A_C) : Prop where
  c0 : RegAt r (coordsAC x).c0
  c1 : RegAt r (coordsAC x).c1

private def nmAC (x : A_C) : RatFunc K5 :=
  PairAlg.nm (toRat k5Params.bW) (toRat k5Params.cW) (coordsAC x)

private lemma regAt_toRat (r : L) (P : K5[X]) : RegAt r (toRat P) := by
  rw [RegAt, mapRatFunc_algebraMap]; exact RegularAt.polynomial r _

private lemma valAt_toRat (r : L) (P : K5[X]) :
    valAt r (toRat P) = (P.map (algebraMap K5 L)).eval r := by
  rw [valAt, mapRatFunc_algebraMap, valueAt_polynomial]

private lemma regUnitAt_toRat {r : L} {P : K5[X]}
    (hP : (P.map (algebraMap K5 L)).eval r ≠ 0) : RegUnitAt r (toRat P) :=
  ⟨regAt_toRat r P, by rwa [valAt_toRat]⟩

private lemma regAt_add {r : L} {f g : RatFunc K5} (hf : RegAt r f) (hg : RegAt r g) :
    RegAt r (f + g) := by rw [RegAt, map_add]; exact hf.add hg
private lemma regAt_sub {r : L} {f g : RatFunc K5} (hf : RegAt r f) (hg : RegAt r g) :
    RegAt r (f - g) := by rw [RegAt, map_sub]; exact regAt_sub_local hf hg
private lemma regAt_neg {r : L} {f : RatFunc K5} (hf : RegAt r f) :
    RegAt r (-f) := by rw [RegAt, map_neg]; exact regAt_neg_local hf
private lemma regAt_mul {r : L} {f g : RatFunc K5} (hf : RegAt r f) (hg : RegAt r g) :
    RegAt r (f * g) := by rw [RegAt, map_mul]; exact regAt_mul_local hf hg
private lemma regAt_div {r : L} {f g : RatFunc K5} (hf : RegAt r f) (hg : RegUnitAt r g) :
    RegAt r (f / g) := by rw [RegAt, map_div₀]; exact regAt_div_of_valueAt_ne hf hg.1 hg.2
private lemma regAt_inv {r : L} {g : RatFunc K5} (hg : RegUnitAt r g) :
    RegAt r g⁻¹ := by rw [RegAt, map_inv₀]; exact regAt_inv_of_valueAt_ne hg.1 hg.2

private lemma regAC_evalAC {r : L} {p : PairAlg (RatFunc K5)}
    (h0 : RegAt r p.c0) (h1 : RegAt r p.c1) : RegAC r (evalAC p) :=
  ⟨by rw [coordsAC_evalAC]; exact h0, by rw [coordsAC_evalAC]; exact h1⟩

private lemma regAC_ιC_rat {r : L} {g : RatFunc K5} (hg : RegAt r g) : RegAC r (ιC_rat g) := by
  rw [← evalAC_ofScalar]
  exact regAC_evalAC hg (by dsimp only [PairAlg.ofScalar]; rw [← map_zero toRat]; exact regAt_toRat r 0)

private lemma regAC_polyC (r : L) (P : K5[X]) : RegAC r (polyC P) :=
  regAC_ιC_rat (regAt_toRat r P)

private lemma regAC_pairC (r : L) (x : PairAlg K5[X]) : RegAC r (pairC x) :=
  regAC_evalAC (regAt_toRat r x.c0) (regAt_toRat r x.c1)

private lemma regAC_ιC_K5 (r : L) (c : K5) : RegAC r (ιC_K5 c) := by
  have : ιC_K5 c = polyC (C c) := by simp [ιC_K5, polyC, RatFunc.algebraMap_C]
  rw [this]; exact regAC_polyC r (C c)

private lemma regAC_zero (r : L) : RegAC r 0 := by
  have : (0 : A_C) = polyC 0 := by simp [polyC]
  rw [this]; exact regAC_polyC r 0
private lemma regAC_one (r : L) : RegAC r 1 := by
  have : (1 : A_C) = polyC 1 := by simp [polyC]
  rw [this]; exact regAC_polyC r 1
private lemma regAC_ofNat (r : L) (n : ℕ) [n.AtLeastTwo] : RegAC r (OfNat.ofNat n) := by
  have : (OfNat.ofNat n : A_C) = polyC (C (OfNat.ofNat n)) := by
    simp [polyC, map_ofNat]
  rw [this]; exact regAC_polyC r _
private lemma regAC_W_C (r : L) : RegAC r W_C := by
  rw [← evalAC_W]
  exact regAC_evalAC
    (by dsimp only [PairAlg.W]; rw [← map_zero toRat]; exact regAt_toRat r 0)
    (by dsimp only [PairAlg.W]; rw [← map_one toRat]; exact regAt_toRat r 1)
private lemma regAC_U_C (r : L) : RegAC r U_C := by
  have : U_C = polyC X := by simp [U_C, polyC, RatFunc.algebraMap_X]
  rw [this]; exact regAC_polyC r X

private lemma regAC_add {r : L} {x y : A_C} (hx : RegAC r x) (hy : RegAC r y) : RegAC r (x + y) := by
  rw [← evalAC_coordsAC x, ← evalAC_coordsAC y, ← evalAC_add]
  exact regAC_evalAC (regAt_add hx.c0 hy.c0) (regAt_add hx.c1 hy.c1)

private lemma regAC_sub {r : L} {x y : A_C} (hx : RegAC r x) (hy : RegAC r y) : RegAC r (x - y) := by
  rw [← evalAC_coordsAC x, ← evalAC_coordsAC y, ← evalAC_sub]
  exact regAC_evalAC (regAt_sub hx.c0 hy.c0) (regAt_sub hx.c1 hy.c1)

private lemma regAC_neg {r : L} {x : A_C} (hx : RegAC r x) : RegAC r (-x) := by
  rw [← evalAC_coordsAC x, ← evalAC_neg]
  exact regAC_evalAC (regAt_neg hx.c0) (regAt_neg hx.c1)

private lemma regAC_mul {r : L} {x y : A_C} (hx : RegAC r x) (hy : RegAC r y) : RegAC r (x * y) := by
  rw [← evalAC_coordsAC x, ← evalAC_coordsAC y, ← evalAC_mul]
  exact regAC_evalAC
    (regAt_sub (regAt_mul hx.c0 hy.c0) (regAt_mul (regAt_mul hx.c1 hy.c1) (regAt_toRat r k5Params.cW)))
    (regAt_sub (regAt_add (regAt_mul hx.c0 hy.c1) (regAt_mul hx.c1 hy.c0))
      (regAt_mul (regAt_mul hx.c1 hy.c1) (regAt_toRat r k5Params.bW)))

private lemma regAC_pow {r : L} {x : A_C} (hx : RegAC r x) (n : ℕ) : RegAC r (x ^ n) := by
  induction n with
  | zero => simpa using regAC_one r
  | succ k ih => rw [pow_succ]; exact regAC_mul ih hx

private lemma regAC_div_rat {r : L} {x : A_C} {g : RatFunc K5}
    (hx : RegAC r x) (hg : RegUnitAt r g) : RegAC r (x / ιC_rat g) := by
  rw [div_eq_mul_inv, ← map_inv₀]
  exact regAC_mul hx (regAC_ιC_rat (regAt_inv hg))

private lemma regAC_div_polyC {r : L} {x : A_C} {P : K5[X]}
    (hx : RegAC r x) (hP : (P.map (algebraMap K5 L)).eval r ≠ 0) : RegAC r (x / polyC P) :=
  regAC_div_rat hx (regUnitAt_toRat hP)

private lemma regAC_div_ofNat {r : L} {x : A_C} (hx : RegAC r x) (n : ℕ) [n.AtLeastTwo]
    (hn : (OfNat.ofNat n : L) ≠ 0) : RegAC r (x / OfNat.ofNat n) := by
  have heq : (OfNat.ofNat n : A_C) = polyC (C (OfNat.ofNat n)) := by
    simp [polyC, map_ofNat]
  rw [heq]
  exact regAC_div_polyC hx (by rw [Polynomial.map_C, eval_C, map_ofNat]; exact hn)

private lemma nmAC_pairC (x : PairAlg K5[X]) : nmAC (pairC x) = toRat (k5Params.pnm x) := by
  simp only [nmAC, pairC, coordsAC_evalAC, CoverParams.pnm, PairAlg.nm, PairAlg.map,
    map_add, map_sub, map_mul, map_pow]

private lemma regAC_div_pairC {r : L} {x : A_C} {y : PairAlg K5[X]}
    (hx : RegAC r x) (hnm : ((k5Params.pnm y).map (algebraMap K5 L)).eval r ≠ 0) :
    RegAC r (x / pairC y) := by
  have hy_conj : pairC y * evalAC (PairAlg.conj (toRat k5Params.bW) (PairAlg.map toRat y)) =
      polyC (k5Params.pnm y) := by
    rw [pairC, ← evalAC_mul, polyC, ← evalAC_ofScalar]
    congr 1; ext
    · simp only [PairAlg.mul, PairAlg.conj, PairAlg.ofScalar, PairAlg.map, CoverParams.pnm,
        PairAlg.nm, map_add, map_sub, map_mul, map_pow]; ring
    · simp only [PairAlg.mul, PairAlg.conj, PairAlg.ofScalar, PairAlg.map]; ring
  have hnm_ne : k5Params.pnm y ≠ 0 := fun h0 => hnm (by rw [h0, Polynomial.map_zero, eval_zero])
  have hy_ne : pairC y ≠ 0 := pairC_ne_zero_of_pnm hnm_ne
  have hdiv : x / pairC y = (x * evalAC (PairAlg.conj (toRat k5Params.bW) (PairAlg.map toRat y))) /
      polyC (k5Params.pnm y) := by
    rw [div_eq_div_iff hy_ne (polyC_ne_zero hnm_ne)]
    linear_combination -x * hy_conj
  rw [hdiv]
  refine regAC_div_polyC (regAC_mul hx ?_) hnm
  exact regAC_evalAC
    (regAt_sub (regAt_toRat r y.c0) (regAt_mul (regAt_toRat r y.c1) (regAt_toRat r k5Params.bW)))
    (regAt_neg (regAt_toRat r y.c1))

private lemma regAC_div_W_C {r : L} {x : A_C} (hx : RegAC r x) (hr0 : r ≠ 0) :
    RegAC r (x / W_C) := by
  have hW : W_C = pairC PairAlg.W := by simp [pairC, PairAlg.map_W, evalAC_W]
  rw [hW]
  refine regAC_div_pairC hx ?_
  have hcW : k5Params.pnm PairAlg.W = k5Params.cW := by
    simp [CoverParams.pnm, PairAlg.nm, PairAlg.W]
  rw [hcW]; exact cW_eval_ne_zero hr0

private lemma regAC_div_U_C {r : L} {x : A_C} (hx : RegAC r x) (hr0 : r ≠ 0) :
    RegAC r (x / U_C) := by
  have hU : U_C = polyC X := by simp [U_C, polyC, RatFunc.algebraMap_X]
  rw [hU]; exact regAC_div_polyC hx (by simpa using hr0)

private lemma regAC_V_C {r : L} (hr0 : r ≠ 0) : RegAC r V_C :=
  regAC_div_U_C (regAC_W_C r) hr0

private lemma regAC_div_V_C {r : L} {x : A_C} (hx : RegAC r x) (hr0 : r ≠ 0) :
    RegAC r (x / V_C) := by
  rw [V_C, div_div_eq_mul_div]
  exact regAC_div_W_C (regAC_mul hx (regAC_U_C r)) hr0

private lemma regAC_div_u_of {r : L} {x : A_C} (hx : RegAC r x) (hr1 : r ≠ 1) :
    RegAC r (x / u_of U_C) := by
  have hu : u_of U_C = polyC (X - 1) / 9 := by
    simp [u_of, U_C, polyC, RatFunc.algebraMap_X]
  rw [hu, div_div_eq_mul_div]
  exact regAC_div_polyC (regAC_mul hx (regAC_ofNat r 9)) (by simpa [sub_eq_zero] using hr1)

private lemma regAC_div_v_of {r : L} {x : A_C} (hx : RegAC r x)
    (hnm : (k5Params.nm_WU.map (algebraMap K5 L)).eval r ≠ 0) :
    RegAC r (x / v_of V_C) := by
  have h9 : (9 : A_C) ≠ 0 := by exact_mod_cast (by decide : (9 : ℕ) ≠ 0)
  have hv : v_of V_C = pairC ⟨-X, 1⟩ / (9 * U_C) := by
    have heq : pairC ⟨-X, 1⟩ = W_C - U_C := by
      simp [pairC, evalAC, PairAlg.map, U_C, RatFunc.algebraMap_X]; ring
    rw [heq, v_of, V_C, eq_div_iff (mul_ne_zero h9 U_C_ne_zero)]
    have h1 : (9 : A_C) * ((W_C / U_C - 1) / 9) = W_C / U_C - 1 := mul_div_cancel₀ _ h9
    have h2 : U_C * (W_C / U_C - 1) = W_C - U_C := by
      rw [mul_sub, mul_div_cancel₀ _ U_C_ne_zero, mul_one]
    linear_combination U_C * h1 + h2
  rw [hv, div_div_eq_mul_div]
  exact regAC_div_pairC (regAC_mul hx (regAC_mul (regAC_ofNat r 9) (regAC_U_C r))) hnm

private lemma regAC_div_G_sq {r : L} {x : A_C} (hx : RegAC r x)
    (hG : ((k5Params.pnm P_G_pair).map (algebraMap K5 L)).eval r ≠ 0) :
    RegAC r (x / G_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) U_C V_C ^ 2) := by
  have h9 : (9 : A_C) ≠ 0 := by exact_mod_cast (by decide : (9 : ℕ) ≠ 0)
  have hGeq : G_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) U_C V_C =
      pairC P_G_pair / (9 * U_C) := by
    rw [eq_div_iff (mul_ne_zero h9 U_C_ne_zero), mul_comm, nine_U_G_AC_eq]
  rw [hGeq, div_pow, div_div_eq_mul_div, pow_two (pairC P_G_pair), ← div_div]
  exact regAC_div_pairC (regAC_div_pairC
    (regAC_mul hx (regAC_pow (regAC_mul (regAC_ofNat r 9) (regAC_U_C r)) 2)) hG) hG

private lemma regAt_trace_euler_pairC {r : L} {x : A_C} {y : PairAlg K5[X]}
    (hx : RegAC r x) (hnm : ((k5Params.pnm y).map (algebraMap K5 L)).eval r ≠ 0) :
    RegAt r (Algebra.trace (RatFunc K5) A_C (x / (pairC y * (2 * W_C + polyC k5Params.bW)))) := by
  have hnm_ne : k5Params.pnm y ≠ 0 := fun h0 => hnm (by rw [h0, Polynomial.map_zero, eval_zero])
  have hnm_rat : PairAlg.nm (toRat k5Params.bW) (toRat k5Params.cW) (PairAlg.map toRat y) ≠ 0 := by
    rw [← PairAlg.map_nm, show PairAlg.nm k5Params.bW k5Params.cW y = k5Params.pnm y from rfl]
    exact polynomialMap_ne_zero hnm_ne
  rw [← evalAC_coordsAC x, pairC, polyC, trace_AC_euler (coordsAC x) (PairAlg.map toRat y) hnm_rat]
  rw [← PairAlg.map_nm, show PairAlg.nm k5Params.bW k5Params.cW y = k5Params.pnm y from rfl]
  exact regAt_div
    (regAt_sub (regAt_mul hx.c1 (regAt_toRat r y.c0)) (regAt_mul hx.c0 (regAt_toRat r y.c1)))
    (regUnitAt_toRat hnm)

-- Polynomial `P18` components are always `RegAC r` whenever `a, b, U, V` are `RegAC r`!
private lemma regAC_poly_components {r : L} {a b : A_C} (ha : RegAC r a) (hb : RegAC r b) (hr0 : r ≠ 0) :
    let S := ιC_K5 S_K; let Q := ιC_K5 Q_K; let T := ιC_K5 T_K
    let x := ιC_K5 x_K; let y := ιC_K5 y_K
    let ξS := S - a * T; let ξQ := Q - b * T
    RegAC r (A_0U a b ξS ξQ U_C V_C / U_C + A_0V a b ξS ξQ U_C V_C / V_C) ∧
    RegAC r (A_Y a b ξS ξQ U_C V_C) ∧
    RegAC r (A_X a b ξS ξQ U_C V_C) ∧
    RegAC r (H0_of S Q T) ∧
    RegAC r (A1_of S Q U_C V_C) ∧
    RegAC r (B1_of T U_C V_C) ∧
    RegAC r (dot_ab (QY_num S Q T x y U_C V_C) a b) ∧
    RegAC r (dot_ab (QX_num S Q T x y U_C V_C) a b) ∧
    RegAC r (dot_ab (CY_of S Q T x y U_C V_C) a b) ∧
    RegAC r (dot_ab (CX_of S Q T x y U_C V_C) a b) ∧
    RegAC r (cA1_of S Q T a b U_C V_C) ∧
    RegAC r (cB1_of S Q T a b U_C V_C) ∧
    RegAC r (EB_of S Q T x y U_C V_C) := by
  intro S Q T x y ξS ξQ
  have hS : RegAC r S := regAC_ιC_K5 r S_K
  have hQ : RegAC r Q := regAC_ιC_K5 r Q_K
  have hT : RegAC r T := regAC_ιC_K5 r T_K
  have hx : RegAC r x := regAC_ιC_K5 r x_K
  have hy : RegAC r y := regAC_ιC_K5 r y_K
  have hU : RegAC r U_C := regAC_U_C r
  have hV : RegAC r V_C := regAC_V_C hr0
  have hξS : RegAC r ξS := regAC_sub hS (regAC_mul ha hT)
  have hξQ : RegAC r ξQ := regAC_sub hQ (regAC_mul hb hT)
  have hdiv_nat {z : A_C} (hz : RegAC r z) (n : ℕ) [hn2 : n.AtLeastTwo] : RegAC r (z / OfNat.ofNat n) := by
    have : CharZero L := charZero_of_injective_ringHom (algebraMap K5 L).injective
    have hn : (OfNat.ofNat n : L) ≠ 0 := by
      change (n : L) ≠ 0
      exact Nat.cast_ne_zero.mpr (by have := hn2.prop; omega)
    exact regAC_div_ofNat hz n hn
  have hclose_poly : ∀ (s q : A_C), RegAC r s → RegAC r q → RegAC r (dH_dS s q U_C V_C) := fun s q hs hq => by
    dsimp only [dH_dS]
    repeat (with_reducible (first | exact hs | exact hq | exact hU | exact hV |
                      exact regAC_ofNat r _ | apply hdiv_nat | apply regAC_add |
                      apply regAC_sub | apply regAC_neg | apply regAC_mul | apply regAC_pow))
  have hdHQ : ∀ (s q v0 : A_C), RegAC r s → RegAC r q → RegAC r v0 → RegAC r (dH_dQ s q v0 U_C V_C) :=
    fun s q v0 hs hq hv0 => by
      dsimp only [dH_dQ]
      repeat (with_reducible (first | exact hs | exact hq | exact hv0 | exact hU | exact hV |
                        exact regAC_ofNat r _ | apply hdiv_nat | apply regAC_add |
                        apply regAC_sub | apply regAC_neg | apply regAC_mul | apply regAC_pow))
  have hnumM (mi : Fin 10) : RegAC r (numM mi a b ξS ξQ U_C V_C) := by
    have ha2 : RegAC r (q1_a2 a b U_C V_C) := hclose_poly a b ha hb
    have ha0 : RegAC r (q1_a0 ξS ξQ U_C V_C) := hclose_poly ξS ξQ hξS hξQ
    have ha1 : RegAC r (q1_a1 a b ξS ξQ U_C V_C) :=
      regAC_sub (regAC_sub (hclose_poly _ _ (regAC_add ha hξS) (regAC_add hb hξQ)) ha2) ha0
    have hb2 : RegAC r (q2_b2 a b U_C V_C) := hdHQ a b 0 ha hb (regAC_zero r)
    have hb0 : RegAC r (q2_b0 ξS ξQ U_C V_C) := hdHQ ξS ξQ 1 hξS hξQ (regAC_one r)
    have hb1 : RegAC r (q2_b1 a b ξS ξQ U_C V_C) := by
      have h00 := hdHQ (a + ξS) (b + ξQ) 0 (regAC_add ha hξS) (regAC_add hb hξQ) (regAC_zero r)
      have h01 := hdHQ ξS ξQ 0 hξS hξQ (regAC_zero r)
      exact regAC_add (regAC_sub (regAC_sub h00 hb2) h01)
        (regAC_mul (regAC_mul (regAC_mul (hdiv_nat (regAC_ofNat r 10) 7) hb) hU) hV)
    have hd20 := regAC_sub (regAC_mul ha2 hb0) (regAC_mul ha0 hb2)
    have hd21 := regAC_sub (regAC_mul ha2 hb1) (regAC_mul ha1 hb2)
    have hd10 := regAC_sub (regAC_mul ha1 hb0) (regAC_mul ha0 hb1)
    have hcomb {m2 m1 m0 : A_C} (hm2 : RegAC r m2) (hm1 : RegAC r m1) (hm0 : RegAC r m0) :
        RegAC r ((1 / 16) * (m2 * (q1_a1 a b ξS ξQ U_C V_C * q2_b0 ξS ξQ U_C V_C -
            q1_a0 ξS ξQ U_C V_C * q2_b1 a b ξS ξQ U_C V_C) -
          m1 * (q1_a2 a b U_C V_C * q2_b0 ξS ξQ U_C V_C -
            q1_a0 ξS ξQ U_C V_C * q2_b2 a b U_C V_C) +
          m0 * (q1_a2 a b U_C V_C * q2_b1 a b ξS ξQ U_C V_C -
            q1_a1 a b ξS ξQ U_C V_C * q2_b2 a b U_C V_C))) :=
      regAC_mul (hdiv_nat (regAC_one r) 16)
        (regAC_add (regAC_sub (regAC_mul hm2 hd10) (regAC_mul hm1 hd20)) (regAC_mul hm0 hd21))
    fin_cases mi
    · exact hcomb (regAC_pow ha 2) (regAC_mul (regAC_mul (regAC_ofNat r 2) ha) hξS) (regAC_pow hξS 2)
    · exact hcomb (regAC_mul ha hb) (regAC_add (regAC_mul ha hξQ) (regAC_mul hb hξS)) (regAC_mul hξS hξQ)
    · exact hcomb (regAC_pow hb 2) (regAC_mul (regAC_mul (regAC_ofNat r 2) hb) hξQ) (regAC_pow hξQ 2)
    · exact hcomb ha hξS (regAC_zero r)
    · exact hcomb (regAC_zero r) ha hξS
    · exact hcomb hb hξQ (regAC_zero r)
    · exact hcomb (regAC_zero r) hb hξQ
    · exact hcomb (regAC_one r) (regAC_zero r) (regAC_zero r)
    · exact hcomb (regAC_zero r) (regAC_one r) (regAC_zero r)
    · exact hcomb (regAC_zero r) (regAC_zero r) (regAC_one r)
  have hA0U : RegAC r (A_0U a b ξS ξQ U_C V_C) := by
    dsimp only [A_0U]
    repeat (with_reducible (first | exact hnumM _ | exact regAC_ofNat r _ |
                    apply hdiv_nat | apply regAC_add | apply regAC_sub | apply regAC_neg | apply regAC_mul))
  have hA0V : RegAC r (A_0V a b ξS ξQ U_C V_C) := by
    dsimp only [A_0V]
    repeat (with_reducible (first | exact hnumM _ | exact regAC_ofNat r _ |
                    apply hdiv_nat | apply regAC_add | apply regAC_sub | apply regAC_neg | apply regAC_mul))
  have hAY : RegAC r (A_Y a b ξS ξQ U_C V_C) := by
    dsimp only [A_Y]
    repeat (with_reducible (first | exact hU | exact hV | exact hnumM _ | exact regAC_ofNat r _ |
                    apply hdiv_nat | apply regAC_add | apply regAC_sub | apply regAC_neg | apply regAC_mul))
  have hAX : RegAC r (A_X a b ξS ξQ U_C V_C) := by
    dsimp only [A_X]
    repeat (with_reducible (first | exact hU | exact hnumM _ | exact regAC_ofNat r _ |
                    apply hdiv_nat | apply regAC_add | apply regAC_sub | apply regAC_neg | apply regAC_mul))
  have hu : RegAC r (u_of U_C) := hdiv_nat (regAC_sub hU (regAC_one r)) 9
  have hv : RegAC r (v_of V_C) := hdiv_nat (regAC_sub hV (regAC_one r)) 9
  have hH0 : RegAC r (H0_of S Q T) := by
    dsimp only [H0_of]
    repeat (with_reducible (first | exact hS | exact hQ | exact hT | exact regAC_ofNat r _ |
                    apply hdiv_nat | apply regAC_add | apply regAC_sub | apply regAC_neg |
                    apply regAC_mul | apply regAC_pow))
  have hdH0 (k : Fin 3) : RegAC r (dH0_fn k S Q T) := by
    fin_cases k <;> dsimp only [dH0_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      repeat (with_reducible (first | exact hS | exact hQ | exact hT | exact regAC_ofNat r _ |
                      apply hdiv_nat | apply regAC_add | apply regAC_sub | apply regAC_neg |
                      apply regAC_mul | apply regAC_pow))
  have hdF5 (k : Fin 5) : RegAC r (dF5_fn k S Q T x y) := by
    fin_cases k <;> dsimp only [dF5_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      repeat (with_reducible (first | exact hS | exact hT | exact hx | exact hy | exact hdH0 _ | exact regAC_ofNat r _ |
                      apply regAC_add | apply regAC_mul | apply regAC_pow))
  have hu3 : RegAC r (u3_of S Q x) := by
    dsimp only [u3_of]
    repeat (with_reducible (first | exact hS | exact hQ | exact hx | exact regAC_ofNat r _ |
                    apply regAC_add | apply regAC_sub | apply regAC_mul))
  have hv3 : RegAC r (v3_of T y) := by
    dsimp only [v3_of]
    repeat (with_reducible (first | exact hT | exact hy | exact regAC_ofNat r _ |
                    apply regAC_add | apply regAC_sub))
  have hDX2 : RegAC r (DX2_of S Q x) := by
    dsimp only [DX2_of]
    repeat (with_reducible (first | exact hS | exact hQ | exact hu3 | exact regAC_ofNat r _ |
                    apply regAC_add | apply regAC_sub | apply regAC_mul | apply regAC_pow))
  have hDY2 : RegAC r (DY2_of T y) := by
    dsimp only [DY2_of]
    repeat (with_reducible (first | exact hT | exact hv3 | exact regAC_ofNat r _ |
                    apply regAC_add | apply regAC_sub | apply regAC_mul | apply regAC_pow))
  have hW2 : RegAC r (W2_of S Q T x y) := regAC_mul (regAC_mul (regAC_mul hS hT) hDX2) hDY2
  have hG : RegAC r (G_of S Q T x y U_C V_C) := regAC_add (regAC_mul hu hDX2) (regAC_mul hv hDY2)
  have hLX : RegAC r (LX_of S Q x U_C) := by
    dsimp only [LX_of]
    repeat (with_reducible (first | exact hu | exact hS | exact hQ | exact hu3 | exact hU |
                    exact regAC_ofNat r _ |
                    apply hdiv_nat | apply regAC_add | apply regAC_sub | apply regAC_mul))
  have hLY : RegAC r (LY_of T y V_C) := by
    dsimp only [LY_of]
    repeat (with_reducible (first | exact hv | exact hT | exact hv3 | exact hV |
                    exact regAC_ofNat r _ |
                    apply hdiv_nat | apply regAC_add | apply regAC_sub | apply regAC_mul))
  have hdLX (k : Fin 5) : RegAC r (dLX_fn k U_C) := by
    fin_cases k <;> dsimp only [dLX_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      repeat (with_reducible (first | exact hu | exact hU | exact regAC_zero r | exact regAC_ofNat r _ |
                      apply hdiv_nat | apply regAC_add | apply regAC_sub | apply regAC_neg | apply regAC_mul))
  have hdLY (k : Fin 5) : RegAC r (dLY_fn k V_C) := by
    fin_cases k <;> dsimp only [dLY_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      repeat (with_reducible (first | exact hv | exact hV | exact regAC_zero r | exact regAC_ofNat r _ |
                      apply hdiv_nat | apply regAC_add | apply regAC_neg | apply regAC_mul))
  have hbr (k : Fin 5) : RegAC r (br_fn k S Q T x y U_C V_C) := by
    dsimp only [br_fn]
    refine regAC_add ?_ (regAC_mul (regAC_mul (regAC_mul (regAC_ofNat r 2) hS) hT)
      (regAC_sub (regAC_mul hLX (hdLY k)) (regAC_mul hLY (hdLX k))))
    split
    · exact regAC_mul (regAC_mul (regAC_neg hT) hLX) hLY
    · exact regAC_mul (regAC_mul hS hLX) hLY
    · exact regAC_zero r
  have hd01 (m : Fin 5) : RegAC r (match m with | 0 => 1 | _ => 0) := by
    split
    · exact regAC_one r
    · exact regAC_zero r
  have hd21 (m : Fin 5) : RegAC r (match m with | 2 => 1 | _ => 0) := by
    split
    · exact regAC_one r
    · exact regAC_zero r
  have hdbr (k j : Fin 5) : RegAC r (dbr_fn k j S Q T x y U_C V_C) := by
    dsimp only [dbr_fn]
    refine regAC_add (regAC_add ?_
      (regAC_mul (regAC_mul (regAC_ofNat r 2) (regAC_add (regAC_mul (hd01 j) hT) (regAC_mul hS (hd21 j))))
        (regAC_sub (regAC_mul hLX (hdLY k)) (regAC_mul hLY (hdLX k)))))
      (regAC_mul (regAC_mul (regAC_mul (regAC_ofNat r 2) hS) hT)
        (regAC_sub (regAC_mul (hdLX j) (hdLY k)) (regAC_mul (hdLY j) (hdLX k))))
    split
    · exact regAC_neg (regAC_add (regAC_add (regAC_mul (regAC_mul (hd21 j) hLX) hLY)
        (regAC_mul (regAC_mul hT (hdLX j)) hLY)) (regAC_mul (regAC_mul hT hLX) (hdLY j)))
    · exact regAC_add (regAC_add (regAC_mul (regAC_mul (hd01 j) hLX) hLY)
        (regAC_mul (regAC_mul hS (hdLX j)) hLY)) (regAC_mul (regAC_mul hS hLX) (hdLY j))
    · exact regAC_zero r
  have hdDX2 (k : Fin 5) : RegAC r (dDX2_fn k S Q x) := by
    fin_cases k <;> dsimp only [dDX2_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      repeat (with_reducible (first | exact hS | exact hQ | exact hu3 | exact regAC_zero r | exact regAC_ofNat r _ |
                      apply regAC_add | apply regAC_sub | apply regAC_neg | apply regAC_mul | apply regAC_pow))
  have hdDY2 (k : Fin 5) : RegAC r (dDY2_fn k T y) := by
    fin_cases k <;> dsimp only [dDY2_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      repeat (with_reducible (first | exact hT | exact hv3 | exact regAC_zero r | exact regAC_one r | exact regAC_ofNat r _ |
                      apply regAC_add | apply regAC_sub | apply regAC_neg | apply regAC_mul | apply regAC_pow))
  have hdW2 (k : Fin 5) : RegAC r (dW2_fn k S Q T x y) := by
    dsimp only [dW2_fn]
    exact regAC_add (regAC_add (regAC_add
      (regAC_mul (regAC_mul (regAC_mul (hd01 k) hT) hDX2) hDY2)
      (regAC_mul (regAC_mul (regAC_mul hS (hd21 k)) hDX2) hDY2))
      (regAC_mul (regAC_mul (regAC_mul hS hT) (hdDX2 k)) hDY2))
      (regAC_mul (regAC_mul (regAC_mul hS hT) hDX2) (hdDY2 k))
  have hdG (k : Fin 5) : RegAC r (dG_fn k S Q T x y U_C V_C) :=
    regAC_add (regAC_mul hu (hdDX2 k)) (regAC_mul hv (hdDY2 k))
  have hFc (f2 : Fin 5 → Fin 5 → A_C) (hf2 : ∀ i j, RegAC r (f2 i j)) (i : Fin 3) :
      RegAC r (F_contract S Q T x y f2 i) := by
    fin_cases i <;> dsimp only [F_contract, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      exact regAC_add (regAC_add (regAC_mul (hdF5 4) (hf2 _ 3)) (regAC_mul (hdF5 3) (hf2 4 _)))
        (regAC_mul (hdF5 _) (hf2 3 4))
  have hdot (v : Fin 3 → A_C) (hv_reg : ∀ i, RegAC r (v i)) : RegAC r (dot_ab v a b) :=
    regAC_add (regAC_add (regAC_mul (hv_reg 0) ha) (regAC_mul (hv_reg 1) hb)) (hv_reg 2)
  have hom (i j : Fin 5) : RegAC r (om_fn i j S Q T x y U_C V_C) := by
    dsimp only [om_fn]
    have homX (k : Fin 5) : RegAC r (match k with
        | 0 => -25 * S * U_C + 15 * Q * U_C + 9 * x * U_C + 25 * S - 15 * Q
        | 1 => 30 * (U_C - 1) * S
        | 3 => 18 * U_C * S
        | _ => 0) := by
      split <;>
        repeat (with_reducible (first | exact hS | exact hQ | exact hx | exact hU |
                        exact regAC_zero r | exact regAC_one r | exact regAC_ofNat r _ |
                        apply regAC_add | apply regAC_sub | apply regAC_neg | apply regAC_mul))
    have homY (k : Fin 5) : RegAC r (match k with
        | 2 => -25 * T * V_C + 9 * y * V_C + 25 * T + 15 * V_C - 15
        | 4 => 18 * V_C * T
        | _ => 0) := by
      split <;>
        repeat (with_reducible (first | exact hT | exact hy | exact hV |
                        exact regAC_zero r | exact regAC_ofNat r _ |
                        apply regAC_add | apply regAC_sub | apply regAC_neg | apply regAC_mul))
    exact regAC_mul (hdiv_nat (regAC_one r) 81)
      (regAC_sub (regAC_mul (homX i) (homY j)) (regAC_mul (homX j) (homY i)))
  have hcurl (Phi : Fin 5 → A_C) (dPhi : Fin 5 → Fin 5 → A_C)
      (hP : ∀ k, RegAC r (Phi k)) (hdP : ∀ k l, RegAC r (dPhi k l)) (i j : Fin 5) :
      RegAC r (curl_num_fn Phi dPhi S Q T x y U_C V_C i j) := by
    dsimp only [curl_num_fn]
    repeat (with_reducible (first | exact hW2 | exact hG | exact hP _ | exact hdP _ _ | exact hdW2 _ | exact hdG _ |
                    exact regAC_ofNat r _ | apply regAC_sub | apply regAC_mul))
  have hA1 : RegAC r (A1_of S Q U_C V_C) := by
    dsimp only [A1_of]
    repeat (with_reducible (first | exact hS | exact hQ | exact hU | exact hV | exact regAC_one r | exact regAC_ofNat r _ |
                    apply hdiv_nat | apply regAC_sub | apply regAC_mul | apply regAC_pow))
  have hB1 : RegAC r (B1_of T U_C V_C) := by
    dsimp only [B1_of]
    repeat (with_reducible (first | exact hT | exact hU | exact hV | exact regAC_one r | exact regAC_ofNat r _ |
                    apply hdiv_nat | apply regAC_sub | apply regAC_mul | apply regAC_pow))
  have hdA1 (k : Fin 3) : RegAC r (dA1_fn k S Q U_C V_C) := by
    fin_cases k <;> dsimp only [dA1_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      repeat (with_reducible (first | exact hS | exact hQ | exact hU | exact hV |
                      exact regAC_zero r | exact regAC_one r | exact regAC_ofNat r _ |
                      apply hdiv_nat | apply regAC_add | apply regAC_sub | apply regAC_neg |
                      apply regAC_mul | apply regAC_pow))
  have hdB1 : RegAC r (dB1_dT T U_C V_C) := by
    dsimp only [dB1_dT]
    repeat (with_reducible (first | exact hT | exact hU | exact hV | exact regAC_one r | exact regAC_ofNat r _ |
                    apply hdiv_nat | apply regAC_sub | apply regAC_mul | apply regAC_pow))
  refine ⟨regAC_add (regAC_div_U_C hA0U hr0) (regAC_div_V_C hA0V hr0), hAY, hAX, hH0, hA1, hB1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hdot _ (fun i => regAC_mul hDY2 (regAC_sub
      (regAC_mul hDX2 (hFc _ (fun p q => regAC_mul (regAC_mul hS hT) (hom p q)) i))
      (hFc _ (fun p q => regAC_mul (regAC_mul hS hT)
        (regAC_sub (regAC_mul (hdDX2 p) (hbr q)) (regAC_mul (hdDX2 q) (hbr p)))) i)))
  · exact hdot _ (fun i => regAC_mul hDX2 (regAC_add
      (regAC_mul (regAC_neg hDY2) (hFc _ (fun p q => regAC_mul (regAC_mul hS hT) (hom p q)) i))
      (hFc _ (fun p q => regAC_mul (regAC_mul hS hT)
        (regAC_sub (regAC_mul (hdDY2 p) (hbr q)) (regAC_mul (hdDY2 q) (hbr p)))) i)))
  · exact hdot _ (fun i => hFc _ (fun p q => hcurl _ _ (fun k => regAC_mul hDY2 (hbr k))
      (fun k l => regAC_add (regAC_mul (hdDY2 l) (hbr k)) (regAC_mul hDY2 (hdbr k l))) p q) i)
  · exact hdot _ (fun i => hFc _ (fun p q => hcurl _ _ (fun k => regAC_mul (regAC_neg hDX2) (hbr k))
      (fun k l => regAC_sub (regAC_mul (regAC_neg (hdDX2 l)) (hbr k)) (regAC_mul hDX2 (hdbr k l))) p q) i)
  · dsimp only [cA1_of]
    repeat (with_reducible (first | exact hH0 | exact hA1 | exact ha | exact hb | exact hdA1 _ | exact hdH0 _ |
                    apply regAC_add | apply regAC_sub | apply regAC_mul))
  · dsimp only [cB1_of]
    repeat (with_reducible (first | exact hH0 | exact hB1 | exact ha | exact hb | exact hdB1 | exact hdH0 _ |
                    apply regAC_add | apply regAC_sub | apply regAC_neg | apply regAC_mul))
  · dsimp only [EB_of]
    repeat (with_reducible (first | exact hW2 | exact hdF5 _ | exact hbr _ | exact regAC_ofNat r _ |
                    apply regAC_sub | apply regAC_mul))

private lemma regAC_interp4 {r : L} {f : A_C → A_C}
    (hf : ∀ z : A_C, RegAC r z → RegAC r (f z)) :
    let p := interp4 f
    RegAC r p.1 ∧ RegAC r p.2.1 ∧ RegAC r p.2.2.1 ∧ RegAC r p.2.2.2.1 ∧ RegAC r p.2.2.2.2 := by
  have hdiv_nat {z : A_C} (hz : RegAC r z) (n : ℕ) [hn2 : n.AtLeastTwo] : RegAC r (z / OfNat.ofNat n) := by
    have : CharZero L := charZero_of_injective_ringHom (algebraMap K5 L).injective
    have hn : (OfNat.ofNat n : L) ≠ 0 := by
      change (n : L) ≠ 0
      exact Nat.cast_ne_zero.mpr (by have := hn2.prop; omega)
    exact regAC_div_ofNat hz n hn
  have h0 := hf 0 (regAC_zero r)
  have h1 := hf 1 (regAC_one r)
  have hm1 := hf (-1) (regAC_neg (regAC_one r))
  have h2 := hf 2 (regAC_ofNat r 2)
  have hm2 := hf (-2) (regAC_neg (regAC_ofNat r 2))
  simp only [interp4]
  refine ⟨?_, ?_, ?_, ?_, h0⟩
  · exact hdiv_nat (regAC_add (regAC_add (regAC_mul (regAC_neg (regAC_ofNat r 4)) (regAC_add h1 hm1))
      (regAC_add h2 hm2)) (regAC_mul (regAC_ofNat r 6) h0)) 24
  · exact hdiv_nat (regAC_add (regAC_mul (regAC_neg (regAC_ofNat r 2)) (regAC_sub h1 hm1))
      (regAC_sub h2 hm2)) 12
  · exact hdiv_nat (regAC_sub (regAC_sub (regAC_mul (regAC_ofNat r 16) (regAC_add h1 hm1))
      (regAC_add h2 hm2)) (regAC_mul (regAC_ofNat r 30) h0)) 24
  · exact hdiv_nat (regAC_sub (regAC_mul (regAC_ofNat r 8) (regAC_sub h1 hm1))
      (regAC_sub h2 hm2)) 12

private lemma regAC_remDeg4 {r : L} {q2 q1 q0 p4 p3 p2 p1 p0 : A_C}
    (hq2 : RegAC r q2) (hq1 : RegAC r q1) (hq0 : RegAC r q0)
    (hp4 : RegAC r p4) (hp3 : RegAC r p3) (hp2 : RegAC r p2)
    (hp1 : RegAC r p1) (hp0 : RegAC r p0) :
    RegAC r (remDeg4_P1 q2 q1 q0 p4 p3 p2 p1) ∧ RegAC r (remDeg4_P0 q2 q1 q0 p4 p3 p2 p0) := by
  have hr3 := regAC_sub (regAC_mul hq2 hp3) (regAC_mul hq1 hp4)
  have hr2 := regAC_sub (regAC_mul hq2 hp2) (regAC_mul hq0 hp4)
  have hs2 := regAC_sub (regAC_mul hq2 hr2) (regAC_mul hq1 hr3)
  have hs1 := regAC_sub (regAC_mul (regAC_pow hq2 2) hp1) (regAC_mul hq0 hr3)
  exact ⟨regAC_sub (regAC_mul hq2 hs1) (regAC_mul hq1 hs2),
         regAC_sub (regAC_mul (regAC_pow hq2 3) hp0) (regAC_mul hq0 hs2)⟩

private lemma regAC_remDeg3 {r : L} {q2 q1 q0 e3 e2 e1 e0 : A_C}
    (hq2 : RegAC r q2) (hq1 : RegAC r q1) (hq0 : RegAC r q0)
    (he3 : RegAC r e3) (he2 : RegAC r e2) (he1 : RegAC r e1) (he0 : RegAC r e0) :
    RegAC r (remDeg3_d1 q2 q1 q0 e3 e2 e1) ∧ RegAC r (remDeg3_d0 q2 q1 q0 e3 e2 e0) := by
  have ht2 := regAC_sub (regAC_mul hq2 he2) (regAC_mul hq1 he3)
  have ht1 := regAC_sub (regAC_mul hq2 he1) (regAC_mul hq0 he3)
  have ht0 := regAC_mul hq2 he0
  exact ⟨regAC_sub (regAC_mul hq2 ht1) (regAC_mul hq1 ht2),
         regAC_sub (regAC_mul hq2 ht0) (regAC_mul hq0 ht2)⟩

private lemma polyC_81_Av0_Q5_eq :
    polyC (C (81 * k5Params.Av0) * k5Params.Q5_z ^ 3) =
      81 * ιC_K5 k5Params.Av0 * polyC k5Params.Q5_z ^ 3 := by
  simp only [polyC, ιC_K5, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat, RingHom.comp_apply]
  rfl

private lemma regAt_eta_of_P18_z {r : L} (hr0 : r ≠ 0)
    (hQ5 : (k5Params.Q5_z.map (algebraMap K5 L)).eval r ≠ 0)
    (hP34 : (P34_K5.map (algebraMap K5 L)).eval r ≠ 0)
    (hcb : (k5Params.cb_h.map (algebraMap K5 L)).eval r ≠ 0)
    (hP18 : ∀ z : A_C, RegAC r z → RegAC r (P18_z_AC z)) :
    RegAt r eta := by
  have h81K : (81 : K5) ≠ 0 := by exact_mod_cast (by decide : (81 : ℕ) ≠ 0)
  have hnm_z : (k5Params.nm_z.map (algebraMap K5 L)).eval r ≠ 0 := by
    rw [nm_z_K5_factor]
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
      eval_mul, eval_pow, eval_C, eval_X]
    have hcbm : (cb_h_m_K5.map (algebraMap K5 L)).eval r ≠ 0 := by
      have h := congrArg (fun f : K5[X] => (f.map (algebraMap K5 L)).eval r) cb_h_K5_eq_mul_monic
      simp only [Polynomial.map_mul, Polynomial.map_C, eval_mul, eval_C] at h
      exact right_ne_zero_of_mul (h ▸ hcb)
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero
      ((map_ne_zero_iff _ (algebraMap K5 L).injective).mpr lc34_K5_ne_zero)
      (pow_ne_zero 15 hr0)) (pow_ne_zero 12 hcbm)) hP34
  have hnum_raw : RegAC r eta_AC_num := by
    obtain ⟨hp4, hp3, hp2, hp1, hp0⟩ := regAC_interp4 hP18
    obtain ⟨hP1, hP0⟩ := regAC_remDeg4 (regAC_pairC r _) (regAC_pairC r _) (regAC_pairC r _)
      hp4 hp3 hp2 hp1 hp0
    exact regAC_mul (regAC_mul (regAC_mul (regAC_neg (regAC_sub
      (regAC_mul hP1 (regAC_pairC r _)) (regAC_mul hP0 (regAC_pairC r _))))
      (regAC_pow (regAC_U_C r) 3)) (regAC_W_C r)) (regAC_pow (regAC_polyC r _) 4)
  have hnum : RegAC r (eta_AC_num / polyC (C (81 * k5Params.Av0) * k5Params.Q5_z ^ 3)) := by
    refine regAC_div_polyC hnum_raw ?_
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, eval_mul, eval_pow, eval_C]
    exact mul_ne_zero ((map_ne_zero_iff _ (algebraMap K5 L).injective).mpr
      (mul_ne_zero h81K Av0_K5_ne_zero)) (pow_ne_zero 3 hQ5)
  have heta_eq : eta_AC = (eta_AC_num / polyC (C (81 * k5Params.Av0) * k5Params.Q5_z ^ 3)) /
      (pairC k5Params.res_z * (2 * W_C + polyC k5Params.bW)) := by
    rw [eta_AC, polyC_81_Av0_Q5_eq, div_div]
    exact congrArg (eta_AC_num / ·) (by ring)
  rw [eta, heta_eq]
  exact regAt_trace_euler_pairC hnum hnm_z

-- Proof that `δ 3` kills every coefficient of `k5Params.bW` and `k5Params.nm_WU` (purely in S, Q, T).
private lemma δ3_k5Params_consts :
    δ 3 k5Params.Av0_inv = 0 ∧ δ 3 k5Params.Cv0 = 0 ∧
    δ 3 k5Params.Bv0 = 0 ∧ δ 3 k5Params.Bv1 = 0 ∧ δ 3 k5Params.Bv2 = 0 := by
  let _ : Algebra ℤ K5 := Ring.toIntAlgebra K5
  have hS : δ 3 S_K = 0 := by simp [δ_S]
  have hQ : δ 3 Q_K = 0 := by simp [δ_Q]
  have hT : δ 3 T_K = 0 := by simp [δ_T]
  have hinv (c : K5) (hc : δ 3 c = 0) : δ 3 c⁻¹ = 0 := by
    by_cases h : c = 0
    · subst h; simp
    · rw [(δ 3).leibniz_inv, hc, smul_zero]
  have hinv2 : δ 3 (2 : K5)⁻¹ = 0 := hinv 2 (δ_ofNat 3 2)
  have hinv3 : δ 3 (3 : K5)⁻¹ = 0 := hinv 3 (δ_ofNat 3 3)
  have hinv7 : δ 3 (7 : K5)⁻¹ = 0 := hinv 7 (δ_ofNat 3 7)
  have hinvT3 : δ 3 (T_K - 3)⁻¹ = 0 := hinv (T_K - 3) (by rw [map_sub, hT, δ_ofNat, sub_self])
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [CoverParams.Av0_inv, CoverParams.Cv0, CoverParams.Bv0, CoverParams.Bv1, CoverParams.Bv2,
      CoverParams.inv4, CoverParams.inv9, CoverParams.inv27, CoverParams.inv243,
      k5Params_inv2, k5Params_inv3, k5Params_inv7, k5Params_invT3, k5Params_S, k5Params_Q, k5Params_T,
      map_add, map_sub, map_neg, (δ 3).leibniz, (δ 3).leibniz_pow,
      hS, hQ, hT, hinv2, hinv3, hinv7, hinvT3, δ_ofNat,
      smul_eq_mul, nsmul_eq_mul, mul_zero, add_zero, sub_zero, neg_zero]

private lemma δ3_coeff_bW (k : ℕ) : δ 3 (k5Params.bW.coeff k) = 0 := by
  let _ : Algebra ℤ K5 := Ring.toIntAlgebra K5
  obtain ⟨hAi, _, hB0, hB1, hB2⟩ := δ3_k5Params_consts
  rw [CoverParams.bW, CoverParams.Bv, CoverParams.quadU]
  rcases k with _ | _ | _ | k <;>
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_X_pow,
      (δ 3).leibniz, hAi, hB0, hB1, hB2]

private lemma δ3_coeff_cW (k : ℕ) : δ 3 (k5Params.cW.coeff k) = 0 := by
  let _ : Algebra ℤ K5 := Ring.toIntAlgebra K5
  obtain ⟨hAi, hC0, _, _, _⟩ := δ3_k5Params_consts
  rw [CoverParams.cW, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  split_ifs
  · simp [(δ 3).leibniz, hAi, hC0]
  · simp

private lemma δ3_coeff_nm_WU (k : ℕ) : δ 3 (k5Params.nm_WU.coeff k) = 0 := by
  let _ : Algebra ℤ K5 := Ring.toIntAlgebra K5
  have hmul (P Q : K5[X]) (hP : ∀ j, δ 3 (P.coeff j) = 0) (hQ : ∀ j, δ 3 (Q.coeff j) = 0) (m : ℕ) :
      δ 3 ((P * Q).coeff m) = 0 := by
    rw [Polynomial.coeff_mul, map_sum]
    apply Finset.sum_eq_zero; intro x _
    rw [(δ 3).leibniz, hP, hQ, smul_eq_mul, smul_eq_mul, mul_zero, mul_zero, add_zero]
  have hX (j : ℕ) : δ 3 ((X : K5[X]).coeff j) = 0 := by
    rw [Polynomial.coeff_X]; split_ifs <;> simp [(δ 3).map_one_eq_zero]
  have hnm : k5Params.nm_WU = X * X + X * k5Params.bW + k5Params.cW := by
    simp only [CoverParams.nm_WU, CoverParams.pnm, PairAlg.nm]; ring
  rw [hnm, Polynomial.coeff_add, Polynomial.coeff_add, map_add, map_add,
    hmul _ _ hX hX, hmul _ _ hX δ3_coeff_bW, δ3_coeff_cW, add_zero, add_zero]

/-- At any root `r` of `nm_WU` in a finite extension `L / K5`, `nm(G)(r) ≠ 0` by `W_G_ne_zero`. -/
private lemma pnm_P_G_eval_ne_zero_of_nm_WU [FiniteDimensional K5 L] {r : L}
    (hr0 : r ≠ 0) (hnm : (k5Params.nm_WU.map (algebraMap K5 L)).eval r = 0) :
    ((k5Params.pnm P_G_pair).map (algebraMap K5 L)).eval r ≠ 0 := by
  let _ : Algebra ℤ K5 := Ring.toIntAlgebra K5
  let _ : Algebra ℤ L := Ring.toIntAlgebra L
  have hr1 : r ≠ 1 := fun h1 => nm_WU_eval_one_ne (L := L) (h1 ▸ hnm)
  have hnm_exp : r ^ 2 + r * (k5Params.bW.map (algebraMap K5 L)).eval r +
      (k5Params.cW.map (algebraMap K5 L)).eval r = 0 := by
    have h := hnm
    simp only [CoverParams.nm_WU, CoverParams.pnm, PairAlg.nm, Polynomial.map_add,
      Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg, Polynomial.map_X,
      Polynomial.map_one, eval_add, eval_sub, eval_mul, eval_pow, eval_neg, eval_X, eval_one] at h
    linear_combination h
  have hfac : ((k5Params.pnm P_G_pair).map (algebraMap K5 L)).eval r =
      (algebraMap K5 L DX2_K * r * (r - 1)) *
      (r * (r - 1) * algebraMap K5 L DX2_K -
        (2 * r + (k5Params.bW.map (algebraMap K5 L)).eval r) * algebraMap K5 L DY2_K) := by
    simp only [CoverParams.pnm, P_G_pair, PairAlg.nm, Polynomial.map_add, Polynomial.map_sub,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X, Polynomial.map_one,
      eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X, eval_one]
    linear_combination (algebraMap K5 L DY2_K) ^ 2 * hnm_exp
  rw [hfac]
  have hc1_ne : r * (r - 1) ≠ 0 := mul_ne_zero hr0 (sub_ne_zero.mpr hr1)
  have hDX_ne : algebraMap K5 L DX2_K ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K5 L).injective).mpr DX2_K_ne_zero
  refine mul_ne_zero (by rw [mul_assoc]; exact mul_ne_zero hDX_ne hc1_ne) ?_
  -- Apply `δL 3` to `c1 * DX2 - c2 * DY2 = 0` and contradict `SheetCalculus.W_G_ne_zero`!
  intro hlin
  set c1 : L := r * (r - 1)
  set c2 : L := 2 * r + (k5Params.bW.map (algebraMap K5 L)).eval r
  have hδr : δL (L := L) 3 r = 0 :=
    δL3_eq_zero_of_isRoot k5Params.nm_WU nm_WU_K5_ne_zero δ3_coeff_nm_WU r hnm
  have hδbW : δL (L := L) 3 ((k5Params.bW.map (algebraMap K5 L)).eval r) = 0 := by
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le Polynomial.natDegree_map_le), map_sum]
    apply Finset.sum_eq_zero; intro k _
    rw [Polynomial.coeff_map, (δL (L := L) 3).leibniz, δL_apply, δ3_coeff_bW k, map_zero,
      (δL (L := L) 3).leibniz_pow, hδr]
    simp
  have hδc1 : δL (L := L) 3 c1 = 0 := by
    dsimp only [c1]
    rw [(δL (L := L) 3).leibniz, map_sub, hδr, (δL (L := L) 3).map_one_eq_zero]; simp
  have hδc2 : δL (L := L) 3 c2 = 0 := by
    dsimp only [c2]
    have h2 : δL (L := L) 3 (2 : L) = 0 := by
      change δL (L := L) 3 ((2 : ℕ) : L) = 0; exact (δL (L := L) 3).map_natCast 2
    rw [map_add, (δL (L := L) 3).leibniz, h2, hδr, hδbW]; simp
  have hd1 : δL (L := L) 3 (c1 * algebraMap K5 L DX2_K) = c1 * algebraMap K5 L (δ 3 DX2_K) := by
    rw [(δL (L := L) 3).leibniz, hδc1, δL_apply]; simp [smul_eq_mul]
  have hd2 : δL (L := L) 3 (c2 * algebraMap K5 L DY2_K) = c2 * algebraMap K5 L (δ 3 DY2_K) := by
    rw [(δL (L := L) 3).leibniz, hδc2, δL_apply]; simp [smul_eq_mul]
  have hd := congrArg (δL (L := L) 3) hlin
  rw [map_zero, map_sub, hd1, hd2] at hd
  have hWG : c1 * algebraMap K5 L (DX2_K * δ 3 DY2_K - DY2_K * δ 3 DX2_K) = 0 := by
    simp only [map_sub, map_mul]
    linear_combination algebraMap K5 L (δ 3 DY2_K) * hlin - algebraMap K5 L DY2_K * hd
  exact mul_ne_zero hc1_ne ((map_ne_zero_iff _ (algebraMap K5 L).injective).mpr W_G_ne_zero) hWG

/-- **Global Regularity Theorem**: For any finite extension `L / K5`, `eta_L` is regular at
every `r : L` outside `{0} ∪ R_{Q5} ∪ R_{34}`. -/
theorem regularAt_eta_of_ne [FiniteDimensional K5 L] (r : L)
    (hr0 : r ≠ 0)
    (hQ5 : (k5Params.Q5_z.map (algebraMap K5 L)).eval r ≠ 0)
    (hP34 : (P34_K5.map (algebraMap K5 L)).eval r ≠ 0) :
    RegularAt r (mapRatFunc (algebraMap K5 L) eta) := by
  have h81K : (81 : K5) ≠ 0 := by exact_mod_cast (by decide : (81 : ℕ) ≠ 0)
  by_cases hcb : (k5Params.cb_h.map (algebraMap K5 L)).eval r = 0
  · -- Case 4: `cb_h(r) = 0` — use mirror `a`-elimination (`eta_AC_eq_a_elim`)!
    have hca : (k5Params.ca_h.map (algebraMap K5 L)).eval r ≠ 0 :=
      eval_ne_zero_of_isCoprime isCoprime_cb_h_ca_h hcb
    have hr1 : r ≠ 1 := by
      have h := eval_ne_zero_of_isCoprime isCoprime_cb_h_X_sub_1 hcb
      simpa [sub_eq_zero] using h
    have hnmWU : (k5Params.nm_WU.map (algebraMap K5 L)).eval r ≠ 0 :=
      eval_ne_zero_of_isCoprime isCoprime_cb_h_nm_WU hcb
    -- `nm_w(r) ≠ 0` from cancelling `cb_h_m^12` in `ca_h^12 * nm_z = cb_h^12 * nm_w`!
    have hnm_w : (k5Params.nm_w.map (algebraMap K5 L)).eval r ≠ 0 := by
      have hfac : C (((locParams.cb_h.coeff 2 : LocK5) : K5) ^ 12) * k5Params.nm_w =
          k5Params.ca_h ^ 12 * (C lc34_K5 * X ^ 15 * P34_K5) := by
        have h := k5Params_nm_z_elim_symm
        rw [nm_z_K5_factor, cb_h_K5_eq_mul_monic, mul_pow, ← map_pow] at h
        have hcbm12 : cb_h_m_K5 ^ 12 ≠ 0 :=
          pow_ne_zero 12 (cb_h_m_loc_spec.1.map LocK5.subtype).ne_zero
        apply mul_left_cancel₀ hcbm12
        linear_combination -h
      have hev := congrArg (fun f : K5[X] => (f.map (algebraMap K5 L)).eval r) hfac
      simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
        eval_mul, eval_pow, eval_C, eval_X] at hev
      have hrhs : ((k5Params.ca_h.map (algebraMap K5 L)).eval r) ^ 12 *
          (algebraMap K5 L lc34_K5 * r ^ 15 * (P34_K5.map (algebraMap K5 L)).eval r) ≠ 0 :=
        mul_ne_zero (pow_ne_zero 12 hca)
          (mul_ne_zero (mul_ne_zero
            ((map_ne_zero_iff _ (algebraMap K5 L).injective).mpr lc34_K5_ne_zero)
            (pow_ne_zero 15 hr0)) hP34)
      exact right_ne_zero_of_mul (hev.symm ▸ hrhs)
    have hP18w (w : A_C) (hw : RegAC r w) : RegAC r (P18_w_AC w) := by
      have ha : RegAC r (-(polyC k5Params.cb_h * w + pairC k5Params.c0W) / (W_C * polyC k5Params.ca_h)) := by
        rw [← div_div]
        exact regAC_div_polyC (regAC_div_W_C (regAC_neg (regAC_add
          (regAC_mul (regAC_polyC r _) hw) (regAC_pairC r _))) hr0) hca
      have hb : RegAC r (w / W_C) := regAC_div_W_C hw hr0
      obtain ⟨hM0, hMY, hMX, hH0, hA1, hB1, hQY, hQX, _, _, hcA1, _, hEB⟩ :=
        regAC_poly_components ha hb hr0
      unfold P18_w_AC P18_of
      have hqY := regAC_div_v_of hQY hnmWU
      have hqX := regAC_div_u_of hQX hr1
      exact regAC_add (regAC_mul hM0 (regAC_add (regAC_add
        (regAC_mul (regAC_mul hH0 hA1) hqY) (regAC_mul (regAC_mul hH0 hB1) hqX))
        (regAC_mul (regAC_div_v_of hcA1 hnmWU) hEB)))
        (regAC_mul (regAC_add (regAC_mul hMY hqY) (regAC_mul hMX hqX)) (regAC_pow hH0 2))
    have hnum_w_raw : RegAC r eta_AC_num_w := by
      obtain ⟨hq4, hq3, hq2, hq1, hq0⟩ := regAC_interp4 hP18w
      obtain ⟨hP1w, hP0w⟩ := regAC_remDeg4 (regAC_pairC r _) (regAC_pairC r _) (regAC_pairC r _)
        hq4 hq3 hq2 hq1 hq0
      obtain ⟨hd1w, hd0w⟩ := regAC_remDeg3 (regAC_pairC r _) (regAC_pairC r _) (regAC_pairC r _)
        (regAC_pairC r _) (regAC_pairC r _) (regAC_pairC r _) (regAC_pairC r _)
      exact regAC_mul (regAC_mul (regAC_mul
        (regAC_sub (regAC_mul hP1w hd0w) (regAC_mul hP0w hd1w))
        (regAC_pow (regAC_U_C r) 3)) (regAC_W_C r)) (regAC_pow (regAC_polyC r _) 4)
    have hnum_w : RegAC r (eta_AC_num_w / polyC (C (81 * k5Params.Av0) * k5Params.Q5_z ^ 3)) := by
      refine regAC_div_polyC hnum_w_raw ?_
      simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, eval_mul, eval_pow, eval_C]
      exact mul_ne_zero ((map_ne_zero_iff _ (algebraMap K5 L).injective).mpr
        (mul_ne_zero h81K Av0_K5_ne_zero)) (pow_ne_zero 3 hQ5)
    have heta_w : eta_AC = (eta_AC_num_w / polyC (C (81 * k5Params.Av0) * k5Params.Q5_z ^ 3)) /
        (pairC k5Params.res_w * (2 * W_C + polyC k5Params.bW)) := by
      rw [eta_AC_eq_a_elim, polyC_81_Av0_Q5_eq, div_div]
      exact congrArg (eta_AC_num_w / ·) (by ring)
    rw [eta, heta_w]
    exact regAt_trace_euler_pairC hnum_w hnm_w
  · -- Now `cb_h(r) ≠ 0`, so `a(z)` and `b(z)` are `RegAC r` for every `RegAC r z`!
    apply regAt_eta_of_P18_z hr0 hQ5 hP34 hcb
    intro z hz
    have ha : RegAC r (z / W_C) := regAC_div_W_C hz hr0
    have hb : RegAC r (-(polyC k5Params.ca_h * z + pairC k5Params.c0W) / (W_C * polyC k5Params.cb_h)) := by
      rw [← div_div]
      exact regAC_div_polyC (regAC_div_W_C (regAC_neg (regAC_add
        (regAC_mul (regAC_polyC r _) hz) (regAC_pairC r _))) hr0) hcb
    obtain ⟨hM0, hMY, hMX, hH0, hA1, hB1, hQY, hQX, hCY, hCX, hcA1, hcB1, hEB⟩ :=
      regAC_poly_components ha hb hr0
    by_cases hr1 : r = 1
    · -- Case 2: `r = 1` — use `P18_z_AC_eq_regX`!
      rw [P18_z_AC_eq_regX]
      have hnmWU : (k5Params.nm_WU.map (algebraMap K5 L)).eval r ≠ 0 := hr1 ▸ nm_WU_eval_one_ne
      have hG1 : ((k5Params.pnm P_G_pair).map (algebraMap K5 L)).eval r ≠ 0 := by
        rw [hr1, pnm_P_G_eval_one]
        exact mul_ne_zero (pow_ne_zero 2 ((map_ne_zero_iff _ (algebraMap K5 L).injective).mpr DY2_K_ne_zero))
          nm_WU_eval_one_ne
      unfold P18_regX_of
      have hqY := regAC_div_v_of hQY hnmWU
      have hqX := regAC_div_G_sq hCX hG1
      exact regAC_add (regAC_mul hM0 (regAC_add (regAC_add
        (regAC_mul (regAC_mul hH0 hA1) hqY) (regAC_mul (regAC_mul hH0 hB1) hqX))
        (regAC_mul (regAC_div_v_of hcA1 hnmWU) hEB)))
        (regAC_mul (regAC_add (regAC_mul hMY hqY) (regAC_mul hMX hqX)) (regAC_pow hH0 2))
    · by_cases hnmWU : (k5Params.nm_WU.map (algebraMap K5 L)).eval r = 0
      · -- Case 3: `nm_WU(r) = 0` — use `P18_z_AC_eq_regY` + `W_G_ne_zero`!
        rw [P18_z_AC_eq_regY]
        have hGnm := pnm_P_G_eval_ne_zero_of_nm_WU hr0 hnmWU
        unfold P18_regY_of
        have hqY := regAC_div_G_sq hCY hGnm
        have hqX := regAC_div_u_of hQX hr1
        exact regAC_add (regAC_mul hM0 (regAC_add (regAC_add
          (regAC_mul (regAC_mul hH0 hA1) hqY) (regAC_mul (regAC_mul hH0 hB1) hqX))
          (regAC_mul (regAC_div_u_of (regAC_neg hcB1) hr1) hEB)))
          (regAC_mul (regAC_add (regAC_mul hMY hqY) (regAC_mul hMX hqX)) (regAC_pow hH0 2))
      · -- Case 1: Generic point!
        unfold P18_z_AC P18_of
        have hqY := regAC_div_v_of hQY hnmWU
        have hqX := regAC_div_u_of hQX hr1
        exact regAC_add (regAC_mul hM0 (regAC_add (regAC_add
          (regAC_mul (regAC_mul hH0 hA1) hqY) (regAC_mul (regAC_mul hH0 hB1) hqX))
          (regAC_mul (regAC_div_v_of hcA1 hnmWU) hEB)))
          (regAC_mul (regAC_add (regAC_mul hMY hqY) (regAC_mul hMX hqX)) (regAC_pow hH0 2))

end RegAC
end Regularity

/-! ### Section 4: Splitting Field `CoverL / K5`, Sheet Extraction, and Residue Formula on `R_{34}` -/

section SplittingAndResidues
open scoped Classical

lemma residue_div_simpleZero {K : Type*} [Field K] (r : K) (f : RatFunc K) (D : K[X])
    (hf : RegularAt r f) (hD0 : D.eval r = 0) (hDd : D.derivative.eval r ≠ 0) :
    CrossedRationalResidue.residue r (f / algebraMap K[X] (RatFunc K) D) =
      valueAt r f / D.derivative.eval r := by
  obtain ⟨P, Q, hQ, rfl⟩ := hf
  rw [div_div, ← map_mul]
  have hQD0 : (Q * D).eval r = 0 := by simp [hD0]
  have hQDd : (Q * D).derivative.eval r = Q.eval r * D.derivative.eval r := by
    simp [derivative_mul, hD0]
  have hQDd_ne : (Q * D).derivative.eval r ≠ 0 := by rw [hQDd]; exact mul_ne_zero hQ hDd
  rw [simplePole_residue P (Q * D) r hQD0 hQDd_ne, hQDd, valueAt_div_polynomials r P Q hQ]
  field_simp [hQ, hDd]

lemma P34_K5_ne_zero : P34_K5 ≠ 0 := by
  intro h0
  have hdeg := P34_K5_natDegree
  rw [h0, natDegree_zero] at hdeg
  omega

/-- Base polynomial whose splitting field `L1` splits `eta.denom`, `P34_K5`, and `Q5_z`. -/
def Q_base : K5[X] := eta.denom * P34_K5 * k5Params.Q5_z

lemma Q_base_ne_zero : Q_base ≠ 0 :=
  mul_ne_zero (mul_ne_zero eta.denom_ne_zero P34_K5_ne_zero) Q5_K5_ne_zero

abbrev L1 : Type := Polynomial.SplittingField Q_base

/-- Product of all 34 fiber quadratics `W^2 + bW(r) * W + cW(r)` over `L1` for `r ∈ roots(P34)`. -/
def Q_quad : L1[X] :=
  ∏ r ∈ (P34_K5.map (algebraMap K5 L1)).roots.toFinset,
    (X ^ 2 + C ((k5Params.bW.map (algebraMap K5 L1)).eval r) * X +
      C ((k5Params.cW.map (algebraMap K5 L1)).eval r))

private lemma monic_quad_poly {F : Type*} [Field F] (b c : F) :
    (X ^ 2 + C b * X + C c : F[X]).Monic := by
  rw [add_assoc]
  apply (monic_X_pow 2).add_of_left
  refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
  · exact lt_of_le_of_lt (degree_C_mul_X_le _) (by rw [degree_X_pow]; exact WithBot.coe_lt_coe.mpr (by omega))
  · exact lt_of_le_of_lt degree_C_le (by rw [degree_X_pow]; exact WithBot.coe_lt_coe.mpr (by omega))

private lemma natDegree_quad_poly {F : Type*} [Field F] (b c : F) :
    (X ^ 2 + C b * X + C c : F[X]).natDegree = 2 := by
  rw [add_assoc]
  have hlt : (C b * X + C c : F[X]).natDegree < 2 := by
    refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ (by simp))
    exact lt_of_le_of_lt (natDegree_C_mul_le _ _) (by simp)
  rw [natDegree_add_eq_left_of_natDegree_lt (by simpa using hlt), natDegree_X_pow]

lemma Q_quad_ne_zero : Q_quad ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ _ => (monic_quad_poly _ _).ne_zero

/-- Finite splitting field `CoverL / K5` splitting `eta.denom`, `P34_K5`, `Q5_z`, and every
quadratic fiber `W^2 + bW(r) * W + cW(r)` above `r ∈ R34`. -/
abbrev CoverL : Type := Polynomial.SplittingField Q_quad

instance : FiniteDimensional K5 CoverL :=
  Module.Finite.trans L1 CoverL

instance : CharZero CoverL :=
  charZero_of_injective_ringHom (algebraMap K5 CoverL).injective

abbrev ιL_K5 : K5 →+* CoverL := algebraMap K5 CoverL

/-- The base-changed cover 1-form `eta_L ∈ RatFunc CoverL`. -/
def eta_L : RatFunc CoverL := mapRatFunc ιL_K5 eta

/-- The 34 horizontal branch points `R_{34} ⊆ CoverL`. -/
def R34 : Finset CoverL := (P34_K5.map ιL_K5).roots.toFinset

/-- The 5 `Q_5 = 0` branch points `R_{Q5} ⊆ CoverL`. -/
def RQ5 : Finset CoverL := (k5Params.Q5_z.map ιL_K5).roots.toFinset

private lemma Q_base_splits_L1 : (Q_base.map (algebraMap K5 L1)).Splits :=
  Polynomial.SplittingField.splits Q_base

lemma P34_splits_L1 : (P34_K5.map (algebraMap K5 L1)).Splits := by
  apply Q_base_splits_L1.of_dvd (Polynomial.map_ne_zero Q_base_ne_zero)
  refine ⟨(eta.denom * k5Params.Q5_z).map (algebraMap K5 L1), ?_⟩
  simp only [Q_base, Polynomial.map_mul]; ring

lemma P34_splits_CoverL : (P34_K5.map ιL_K5).Splits := by
  have h := P34_splits_L1.map (algebraMap L1 CoverL)
  rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq K5 L1 CoverL] at h

lemma Q5_splits_CoverL : (k5Params.Q5_z.map ιL_K5).Splits := by
  have h1 : (k5Params.Q5_z.map (algebraMap K5 L1)).Splits := by
    apply Q_base_splits_L1.of_dvd (Polynomial.map_ne_zero Q_base_ne_zero)
    refine ⟨(eta.denom * P34_K5).map (algebraMap K5 L1), ?_⟩
    simp only [Q_base, Polynomial.map_mul]; ring
  have h := h1.map (algebraMap L1 CoverL)
  rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq K5 L1 CoverL] at h

lemma eta_L_denom_splits : eta_L.denom.Splits := by
  have h1 : (eta.denom.map (algebraMap K5 L1)).Splits := by
    apply Q_base_splits_L1.of_dvd (Polynomial.map_ne_zero Q_base_ne_zero)
    refine ⟨(P34_K5 * k5Params.Q5_z).map (algebraMap K5 L1), ?_⟩
    simp only [Q_base, Polynomial.map_mul]; ring
  have h2 : (eta.denom.map ιL_K5).Splits := by
    have h := h1.map (algebraMap L1 CoverL)
    rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq K5 L1 CoverL] at h
  exact h2.of_dvd (Polynomial.map_ne_zero eta.denom_ne_zero) (mapRatFunc_denom_dvd ιL_K5 eta)

lemma mem_R34_iff {r : CoverL} : r ∈ R34 ↔ (P34_K5.map ιL_K5).eval r = 0 := by
  simp only [R34, Multiset.mem_toFinset, Polynomial.mem_roots (Polynomial.map_ne_zero P34_K5_ne_zero),
    Polynomial.IsRoot.def]

lemma mem_RQ5_iff {r : CoverL} : r ∈ RQ5 ↔ (k5Params.Q5_z.map ιL_K5).eval r = 0 := by
  simp only [RQ5, Multiset.mem_toFinset, Polynomial.mem_roots (Polynomial.map_ne_zero Q5_K5_ne_zero),
    Polynomial.IsRoot.def]

lemma zero_notMem_R34 : (0 : CoverL) ∉ R34 := by
  intro h0
  have h := eval_ne_zero_of_isCoprime isCoprime_P34_X (mem_R34_iff.mp h0)
  simp at h

lemma zero_notMem_RQ5 : (0 : CoverL) ∉ RQ5 := by
  intro h0
  have h := eval_ne_zero_of_isCoprime isCoprime_Q5_X (mem_RQ5_iff.mp h0)
  simp at h

lemma disjoint_R34_RQ5 : Disjoint R34 RQ5 := by
  rw [Finset.disjoint_left]
  intro r hr34 hr5
  exact eval_ne_zero_of_isCoprime isCoprime_P34_Q5 (mem_R34_iff.mp hr34) (mem_RQ5_iff.mp hr5)

lemma regularAt_eta_L_of_notMem (r : CoverL)
    (hr : r ∉ ({0} ∪ RQ5 ∪ R34 : Finset CoverL)) :
    RegularAt r eta_L := by
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hr
  exact regularAt_eta_of_ne r hr.1.1 (fun h => hr.1.2 (mem_RQ5_iff.mpr h))
    (fun h => hr.2 (mem_R34_iff.mpr h))

/-- Above every `r ∈ R34`, the fiber quadratic `W^2 + bW(r)*W + cW(r)` splits in `CoverL`
into two distinct roots `w1 ≠ w2`. -/
lemma E0_splits_at_R34 (r : CoverL) (hr : r ∈ R34) :
    ∃ w1 w2 : CoverL,
      w1 + w2 = -(k5Params.bW.map ιL_K5).eval r ∧
      w1 * w2 = (k5Params.cW.map ιL_K5).eval r ∧
      w1 ≠ w2 := by
  have hr_eval : (P34_K5.map ιL_K5).eval r = 0 := mem_R34_iff.mp hr
  have hmem : ∃ r1 ∈ (P34_K5.map (algebraMap K5 L1)).roots.toFinset, algebraMap L1 CoverL r1 = r := by
    have hfac := P34_splits_L1.eq_prod_roots
    have hmap := congrArg (fun p : L1[X] => (p.map (algebraMap L1 CoverL)).eval r) hfac
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq K5 L1 CoverL, hr_eval] at hmap
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_multiset_prod,
      Multiset.map_map, Function.comp_def, Polynomial.map_sub, Polynomial.map_X,
      eval_mul, eval_C, eval_multiset_prod, eval_sub, eval_X] at hmap
    have hlc : algebraMap L1 CoverL (P34_K5.map (algebraMap K5 L1)).leadingCoeff ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap L1 CoverL).injective).mpr
        (leadingCoeff_ne_zero.mpr (Polynomial.map_ne_zero P34_K5_ne_zero))
    have hprod0 := (mul_eq_zero.mp hmap.symm).resolve_left hlc
    obtain ⟨r1, hr1, hr1_eq⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hprod0)
    exact ⟨r1, Multiset.mem_toFinset.mpr hr1, (sub_eq_zero.mp hr1_eq).symm⟩
  obtain ⟨r1, hr1_mem, hr1_eq⟩ := hmem
  let q1 : L1[X] := X ^ 2 + C ((k5Params.bW.map (algebraMap K5 L1)).eval r1) * X +
    C ((k5Params.cW.map (algebraMap K5 L1)).eval r1)
  have hdvd : q1 ∣ Q_quad := Finset.dvd_prod_of_mem _ hr1_mem
  have hq_map : q1.map (algebraMap L1 CoverL) =
      X ^ 2 + C ((k5Params.bW.map ιL_K5).eval r) * X + C ((k5Params.cW.map ιL_K5).eval r) := by
    have hev (P : K5[X]) : algebraMap L1 CoverL ((P.map (algebraMap K5 L1)).eval r1) = (P.map ιL_K5).eval r := by
      rw [← Polynomial.eval_map_apply, Polynomial.map_map, ← IsScalarTower.algebraMap_eq K5 L1 CoverL, hr1_eq]
    simp only [q1, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_X, hev]
  have hsplit : (q1.map (algebraMap L1 CoverL)).Splits :=
    (Polynomial.SplittingField.splits Q_quad).of_dvd (Polynomial.map_ne_zero Q_quad_ne_zero)
      (Polynomial.map_dvd (algebraMap L1 CoverL) hdvd)
  rw [hq_map] at hsplit
  set b := (k5Params.bW.map ιL_K5).eval r
  set c := (k5Params.cW.map ιL_K5).eval r
  have hcard : (X ^ 2 + C b * X + C c : CoverL[X]).roots.card = 2 := by
    rw [← hsplit.natDegree_eq_card_roots, natDegree_quad_poly]
  obtain ⟨w1, w2, hroots⟩ := Multiset.card_eq_two.mp hcard
  have hfac : X ^ 2 + C b * X + C c = (X - C w1) * (X - C w2) := by
    have hprod := hsplit.eq_prod_roots
    rw [hroots, (monic_quad_poly b c).leadingCoeff, map_one, one_mul] at hprod
    simpa [mul_assoc] using hprod
  have hfac' : X ^ 2 + C b * X + C c = X ^ 2 + C (-(w1 + w2)) * X + C (w1 * w2) := by
    rw [hfac]; simp only [map_neg, map_add, map_mul]; ring
  have hsum : w1 + w2 = -b := by
    have hc1 := congrArg (fun p : CoverL[X] => p.coeff 1) hfac'
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_X_pow,
      Polynomial.coeff_C] at hc1
    norm_num at hc1
    linear_combination hc1
  have hprod : w1 * w2 = c := by
    have hc0 := congrArg (fun p : CoverL[X] => p.coeff 0) hfac'
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_X_pow,
      Polynomial.coeff_C] at hc0
    norm_num at hc0
    exact hc0.symm
  have hsep : w1 ≠ w2 := by
    intro heq
    have hdisc_ne : (k5Params.disc_E0.map ιL_K5).eval r ≠ 0 :=
      eval_ne_zero_of_isCoprime isCoprime_P34_disc_E0 hr_eval
    have hdisc_eq : (k5Params.disc_E0.map ιL_K5).eval r = (w1 - w2) ^ 2 := by
      simp only [CoverParams.disc_E0, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul,
        Polynomial.map_ofNat, eval_sub, eval_pow, eval_mul, eval_ofNat]
      change b ^ 2 - 4 * c = (w1 - w2) ^ 2
      rw [← hprod, show b = -(w1 + w2) by linear_combination hsum]; ring
    rw [heq, sub_self, zero_pow (by omega)] at hdisc_eq
    exact hdisc_ne hdisc_eq
  exact ⟨w1, w2, hsum, hprod, hsep⟩

-- Dual-number evaluation helpers and pure-field directional derivatives along `(a', b', 1, V')`.
section DualCoverDeriv
variable {F : Type*} [Field F] [CharZero F] (φ : K5 →+* F)

private abbrev pU_d (P : K5[X]) (U : F) : F := (P.derivative.map φ).eval U
private abbrev pU_D (P : K5[X]) (U : F) : Dual F := P.eval₂ (Dual.C.comp φ) ⟨U, 1⟩
private abbrev pUW_D (x : PairAlg K5[X]) (U W W' : F) : Dual F :=
  PairAlg.evalAt ⟨W, W'⟩ (PairAlg.map (Polynomial.eval₂RingHom (Dual.C.comp φ) ⟨U, 1⟩) x)

omit [CharZero F] in
private lemma pU_D_eq (P : K5[X]) (U : F) : pU_D φ P U = ⟨pU φ P U, pU_d φ P U⟩ := by
  rw [pU_D, ← Polynomial.eval₂_map, Dual.eval₂_eq, pU, pU_d, Polynomial.derivative_map, mul_one]

omit [CharZero F] in
private lemma pU_D_quadU (c0 c1 c2 : K5) (U : F) :
    pU_D φ (CoverParams.quadU c0 c1 c2) U =
      ⟨φ c0 + φ c1 * U + φ c2 * U ^ 2, φ c1 + 2 * φ c2 * U⟩ := by
  rw [pU_D_eq, pU, pU_d, CoverParams.quadU]
  ext
  · simp [eval_add, eval_mul, eval_pow, eval_C, eval_X]
  · simp [derivative_add, derivative_mul, derivative_C, derivative_X]
    ring

omit [CharZero F] in
private lemma pU_D_add (P Q : K5[X]) (U : F) : pU_D φ (P + Q) U = pU_D φ P U + pU_D φ Q U :=
  map_add (eval₂RingHom (Dual.C.comp φ) ⟨U, 1⟩) P Q
omit [CharZero F] in
private lemma pU_D_sub (P Q : K5[X]) (U : F) : pU_D φ (P - Q) U = pU_D φ P U - pU_D φ Q U :=
  map_sub (eval₂RingHom (Dual.C.comp φ) ⟨U, 1⟩) P Q
omit [CharZero F] in
private lemma pU_D_neg (P : K5[X]) (U : F) : pU_D φ (-P) U = -pU_D φ P U :=
  map_neg (eval₂RingHom (Dual.C.comp φ) ⟨U, 1⟩) P
omit [CharZero F] in
private lemma pU_D_mul (P Q : K5[X]) (U : F) : pU_D φ (P * Q) U = pU_D φ P U * pU_D φ Q U :=
  map_mul (eval₂RingHom (Dual.C.comp φ) ⟨U, 1⟩) P Q
omit [CharZero F] in
private lemma pU_D_pow (P : K5[X]) (n : ℕ) (U : F) : pU_D φ (P ^ n) U = pU_D φ P U ^ n :=
  map_pow (eval₂RingHom (Dual.C.comp φ) ⟨U, 1⟩) P n
omit [CharZero F] in
private lemma pU_D_C (c : K5) (U : F) : pU_D φ (C c) U = Dual.C (φ c) := by
  simp [pU_D]
omit [CharZero F] in
private lemma pU_D_X (U : F) : pU_D φ X U = ⟨U, 1⟩ := by
  simp [pU_D]
omit [CharZero F] in
private lemma pU_D_ofNat (n : ℕ) [n.AtLeastTwo] (U : F) :
    pU_D φ (OfNat.ofNat n) U = OfNat.ofNat n := by
  change eval₂RingHom (Dual.C.comp φ) ⟨U, 1⟩ (OfNat.ofNat n) = OfNat.ofNat n
  exact map_ofNat _ n

omit [CharZero F] in
private lemma pUW_D_val (x : PairAlg K5[X]) (U W W' : F) :
    (pUW_D φ x U W W').val = pUW φ x U W := by
  simp only [pUW_D, pUW, PairAlg.evalAt, PairAlg.map, Dual.add_val, Dual.mul_val,
    Polynomial.coe_eval₂RingHom, Polynomial.coe_evalRingHom, Polynomial.coe_mapRingHom,
    RingHom.comp_apply]
  change (pU_D φ x.c0 U).val + (pU_D φ x.c1 U).val * W = pU φ x.c0 U + pU φ x.c1 U * W
  rw [pU_D_eq, pU_D_eq]

omit [CharZero F] in
private lemma pUW_D_add (x y : PairAlg K5[X]) (U W W' : F) :
    pUW_D φ (PairAlg.add x y) U W W' = pUW_D φ x U W W' + pUW_D φ y U W W' := by
  simp only [pUW_D, PairAlg.map_add, PairAlg.evalAt_add]
omit [CharZero F] in
private lemma pUW_D_sub (x y : PairAlg K5[X]) (U W W' : F) :
    pUW_D φ (PairAlg.sub x y) U W W' = pUW_D φ x U W W' - pUW_D φ y U W W' := by
  simp only [pUW_D, PairAlg.map_sub, PairAlg.evalAt_sub]
omit [CharZero F] in
private lemma pUW_D_smul (s : K5[X]) (x : PairAlg K5[X]) (U W W' : F) :
    pUW_D φ (PairAlg.smul s x) U W W' = pU_D φ s U * pUW_D φ x U W W' := by
  simp only [pUW_D, PairAlg.map_smul, PairAlg.evalAt_smul, Polynomial.coe_eval₂RingHom]
omit [CharZero F] in
private lemma pUW_D_ofScalar (s : K5[X]) (U W W' : F) :
    pUW_D φ (PairAlg.ofScalar s) U W W' = pU_D φ s U := by
  simp only [pUW_D, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar, Polynomial.coe_eval₂RingHom]
omit [CharZero F] in
private lemma pUW_D_W (U W W' : F) : pUW_D φ PairAlg.W U W W' = ⟨W, W'⟩ := by
  simp only [pUW_D, PairAlg.map_W, PairAlg.evalAt_W]
omit [CharZero F] in
private lemma pUW_D_pmul (x y : PairAlg K5[X]) (U W W' : F)
    (hWD : (⟨W, W'⟩ : Dual F) ^ 2 + pU_D φ k5Params.bW U * ⟨W, W'⟩ + pU_D φ k5Params.cW U = 0) :
    pUW_D φ (k5Params.pmul x y) U W W' = pUW_D φ x U W W' * pUW_D φ y U W W' := by
  simp only [pUW_D, CoverParams.pmul, PairAlg.map_mul, Polynomial.coe_eval₂RingHom]
  exact PairAlg.evalAt_mul (pU_D φ k5Params.bW U) (pU_D φ k5Params.cW U) (⟨W, W'⟩ : Dual F) hWD _ _

omit [CharZero F] in
private lemma pUW_D_toUW (v0 v1 v2 : K5) (U W W' : F)
    (hWD : (⟨W, W'⟩ : Dual F) ^ 2 + pU_D φ k5Params.bW U * ⟨W, W'⟩ + pU_D φ k5Params.cW U = 0) :
    pUW_D φ (k5Params.toUW v0 v1 v2) U W W' =
      Dual.C (φ v2) * (⟨W, W'⟩ : Dual F) ^ 2 + Dual.C (φ v1) * (⟨U, 1⟩ : Dual F) * ⟨W, W'⟩ +
        Dual.C (φ v0) * (⟨U, 1⟩ : Dual F) ^ 2 := by
  unfold pUW_D CoverParams.toUW PairAlg.evalAt PairAlg.map
  simp only [Polynomial.coe_eval₂RingHom, map_sub, map_mul, map_pow, eval₂_C, eval₂_X, RingHom.comp_apply]
  change (Dual.C (φ v0) * (⟨U, 1⟩ : Dual F) ^ 2 - Dual.C (φ v2) * pU_D φ k5Params.cW U) +
    (Dual.C (φ v1) * (⟨U, 1⟩ : Dual F) - Dual.C (φ v2) * pU_D φ k5Params.bW U) * (⟨W, W'⟩ : Dual F) = _
  linear_combination -Dual.C (φ v2) * hWD

private lemma J_fib_03 (a b U W : F) (hU : U ≠ 0) :
    dE_dV 0 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) =
      φ k5Params.Av0 * (2 * W + pU φ k5Params.bW U) := by
  have hT3 : φ T_K - 3 ≠ 0 := by
    have := (map_ne_zero_iff φ φ.injective).mpr T_K_sub_3_ne
    simpa only [map_sub, map_ofNat] using this
  simp only [dE_dV, dH_dV, pU, CoverParams.bW, CoverParams.Bv, CoverParams.quadU,
    CoverParams.Av0, CoverParams.Av0_inv, CoverParams.Bv0, CoverParams.Bv1, CoverParams.Bv2,
    CoverParams.inv4, CoverParams.inv9, CoverParams.inv27, CoverParams.inv243,
    k5Params_inv2, k5Params_inv3, k5Params_inv7, k5Params_invT3, k5Params_S, k5Params_Q, k5Params_T,
    Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_ofNat,
    eval_add, eval_sub, eval_mul, eval_pow, eval_neg, eval_C, eval_X, eval_ofNat,
    map_add, map_sub, map_mul, map_pow, map_neg, map_inv₀, map_ofNat]
  field_simp [hU, hT3]; ring

private lemma J_fib_10 (a b U W : F) (hU : U ≠ 0) :
    U * dE_da 1 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) = pU φ k5Params.ca_h U * W := by
  simp only [dE_da, dH_dS, pU, CoverParams.ca_h, CoverParams.quadU,
    CoverParams.inv9, CoverParams.inv27, CoverParams.inv81,
    k5Params_inv3, k5Params_S, k5Params_Q,
    Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_ofNat,
    eval_add, eval_sub, eval_mul, eval_pow, eval_neg, eval_C, eval_X, eval_ofNat,
    map_add, map_sub, map_mul, map_pow, map_neg, map_inv₀, map_ofNat]
  field_simp [hU]; ring

private lemma J_fib_11 (a b U W : F) (hU : U ≠ 0) :
    U * dE_db 1 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) = pU φ k5Params.cb_h U * W := by
  simp only [dE_db, dH_dQ, pU, CoverParams.cb_h, CoverParams.quadU,
    CoverParams.inv9, CoverParams.inv27,
    k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q,
    Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_ofNat,
    eval_add, eval_sub, eval_mul, eval_pow, eval_neg, eval_C, eval_X, eval_ofNat,
    map_add, map_sub, map_mul, map_pow, map_neg, map_inv₀, map_ofNat]
  field_simp [hU]; ring

private lemma J_fib_20 (a b U W : F) (hU : U ≠ 0) :
    U * dE_da 2 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) =
      2 * pU φ k5Params.q20 U * (W * a) + pU φ k5Params.q11 U * (W * b) := by
  simp only [dE_da, dH_dS, pU, CoverParams.q20, CoverParams.q11, CoverParams.quadU,
    CoverParams.inv9, CoverParams.inv27, CoverParams.inv81,
    k5Params_inv3, k5Params_S, k5Params_Q,
    Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_ofNat,
    eval_add, eval_sub, eval_mul, eval_pow, eval_neg, eval_C, eval_X, eval_ofNat,
    map_add, map_sub, map_mul, map_pow, map_neg, map_inv₀, map_ofNat]
  field_simp [hU]; ring

private lemma J_fib_21 (a b U W : F) (hU : U ≠ 0) :
    U * dE_db 2 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) =
      pU φ k5Params.q11 U * (W * a) + 2 * pU φ k5Params.q02 U * (W * b) := by
  simp only [dE_db, dH_dQ, pU, CoverParams.q11, CoverParams.q02, CoverParams.quadU,
    CoverParams.inv9, CoverParams.inv27,
    k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q,
    Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_ofNat,
    eval_add, eval_sub, eval_mul, eval_pow, eval_neg, eval_C, eval_X, eval_ofNat,
    map_add, map_sub, map_mul, map_pow, map_neg, map_inv₀, map_ofNat]
  field_simp [hU]; ring

private lemma J_fib_minor12 (z U W : F) (hU : U ≠ 0) (hW0 : W ≠ 0) (hcb : pU φ k5Params.cb_h U ≠ 0) :
    let a := z / W
    let b := -(pU φ k5Params.ca_h U * z + pUW φ k5Params.c0W U W) / (W * pU φ k5Params.cb_h U)
    let M := J_fib (φ S_K) (φ Q_K) (φ T_K) a b U (W / U)
    M 1 1 * M 2 0 - M 1 0 * M 2 1 =
      W * (2 * pUW φ k5Params.d2_2 U W * z + pUW φ k5Params.d2_1 U W) / (U ^ 2 * pU φ k5Params.cb_h U) := by
  intro a b M
  have h10 : U * M 1 0 = pU φ k5Params.ca_h U * W := J_fib_10 φ a b U W hU
  have h11 : U * M 1 1 = pU φ k5Params.cb_h U * W := J_fib_11 φ a b U W hU
  have h20 : U * M 2 0 = 2 * pU φ k5Params.q20 U * (W * a) + pU φ k5Params.q11 U * (W * b) :=
    J_fib_20 φ a b U W hU
  have h21 : U * M 2 1 = pU φ k5Params.q11 U * (W * a) + 2 * pU φ k5Params.q02 U * (W * b) :=
    J_fib_21 φ a b U W hU
  have hWa : W * a = z := mul_div_cancel₀ z hW0
  have hWb : pU φ k5Params.cb_h U * (W * b) = -(pU φ k5Params.ca_h U * z + pUW φ k5Params.c0W U W) := by
    dsimp only [b]; field_simp [hW0, hcb]
  have hd22 : pUW φ k5Params.d2_2 U W =
      pU φ k5Params.q20 U * pU φ k5Params.cb_h U ^ 2 -
      pU φ k5Params.q11 U * pU φ k5Params.ca_h U * pU φ k5Params.cb_h U +
      pU φ k5Params.q02 U * pU φ k5Params.ca_h U ^ 2 := by
    simp [pUW, CoverParams.d2_2, CoverParams.Q5_z, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar, pU]
  have hd21 : pUW φ k5Params.d2_1 U W =
      (-pU φ k5Params.q11 U * pU φ k5Params.cb_h U + 2 * pU φ k5Params.q02 U * pU φ k5Params.ca_h U) *
      pUW φ k5Params.c0W U W := by
    simp [pUW, CoverParams.d2_1, PairAlg.map_smul, PairAlg.evalAt_smul, pU]
  rw [hd22, hd21, eq_div_iff (mul_ne_zero (pow_ne_zero 2 hU) hcb)]
  have hmul : (M 1 1 * M 2 0 - M 1 0 * M 2 1) * (U ^ 2 * pU φ k5Params.cb_h U) =
      pU φ k5Params.cb_h U * ((U * M 1 1) * (U * M 2 0) - (U * M 1 0) * (U * M 2 1)) := by ring
  rw [hmul, h10, h11, h20, h21, hWa]
  linear_combination W * (pU φ k5Params.q11 U * pU φ k5Params.cb_h U -
    2 * pU φ k5Params.q02 U * pU φ k5Params.ca_h U) * hWb

private lemma dE0_along (a b U W W' : F) (hU : U ≠ 0) :
    E_fn 0 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) +
    U * (dE_dU 0 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) +
      dE_dV 0 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) * ((W' * U - W) / U ^ 2)) =
    (Dual.C (φ k5Params.Av0) *
      ((⟨W, W'⟩ : Dual F) ^ 2 + pU_D φ k5Params.bW U * (⟨W, W'⟩ : Dual F) + pU_D φ k5Params.cW U)).eps := by
  have hT3 : φ T_K - 3 ≠ 0 := by
    have := (map_ne_zero_iff φ φ.injective).mpr T_K_sub_3_ne
    simpa only [map_sub, map_ofNat] using this
  have hbW : pU_D φ k5Params.bW U =
      Dual.C (φ k5Params.Av0_inv) *
        ⟨φ k5Params.Bv0 + φ k5Params.Bv1 * U + φ k5Params.Bv2 * U ^ 2,
          φ k5Params.Bv1 + 2 * φ k5Params.Bv2 * U⟩ := by
    rw [CoverParams.bW, pU_D_mul, pU_D_C, CoverParams.Bv, pU_D_quadU]
  have hcW : pU_D φ k5Params.cW U =
      Dual.C (φ (k5Params.Cv0 * k5Params.Av0_inv)) * ⟨U ^ 2, 2 * U⟩ := by
    rw [CoverParams.cW, pU_D_mul, pU_D_C, pU_D_pow, pU_D_X, Dual.pow_eq]
    congr 1; ext <;> simp
  rw [hbW, hcW, Dual.pow_eq]
  simp only [Dual.mul_eps, Dual.add_eps, Dual.mul_val, Dual.add_val, Dual.C_val, Dual.C_eps]
  simp only [E_fn, dE_dU, dE_dV, H_cub, dH_dU, dH_dV,
    CoverParams.Av0, CoverParams.Av0_inv, CoverParams.Cv0, CoverParams.Bv0, CoverParams.Bv1, CoverParams.Bv2,
    CoverParams.inv4, CoverParams.inv9, CoverParams.inv27, CoverParams.inv243,
    k5Params_inv2, k5Params_inv3, k5Params_inv7, k5Params_invT3, k5Params_S, k5Params_Q, k5Params_T,
    map_add, map_sub, map_mul, map_pow, map_neg, map_inv₀, map_ofNat]
  field_simp [hU, hT3]; ring

private lemma dE1_along (a b U W a' b' W' : F) (hU : U ≠ 0) :
    E_fn 1 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) +
    U * (dE_da 1 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) * a' +
      dE_db 1 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) * b' +
      dE_dU 1 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) +
      dE_dV 1 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) * ((W' * U - W) / U ^ 2)) =
    (pU_D φ k5Params.ca_h U * ((⟨W, W'⟩ : Dual F) * (⟨a, a'⟩ : Dual F)) +
      pU_D φ k5Params.cb_h U * ((⟨W, W'⟩ : Dual F) * (⟨b, b'⟩ : Dual F)) +
      Dual.C (φ k5Params.c0_V2) * (⟨W, W'⟩ : Dual F) ^ 2 +
      Dual.C (φ k5Params.c0_V1) * (⟨U, 1⟩ : Dual F) * (⟨W, W'⟩ : Dual F) +
      Dual.C (φ k5Params.c0_V0) * (⟨U, 1⟩ : Dual F) ^ 2).eps := by
  rw [CoverParams.ca_h, pU_D_quadU, CoverParams.cb_h, pU_D_quadU]
  simp only [Dual.pow_eq, Dual.mul_eps, Dual.add_eps, Dual.mul_val, Dual.C_val, Dual.C_eps]
  simp only [E_fn, dE_da, dE_db, dE_dU, dE_dV, H_cub, dH_dS, dH_dQ, dH_dU, dH_dV,
    CoverParams.c0_V2, CoverParams.c0_V1, CoverParams.c0_V0,
    CoverParams.inv9, CoverParams.inv27, CoverParams.inv81,
    k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q, k5Params_T,
    map_add, map_sub, map_mul, map_pow, map_neg, map_inv₀, map_ofNat]
  field_simp [hU]; ring

private lemma dE2_along (a b U W a' b' W' : F) (hU : U ≠ 0) :
    W * E_fn 2 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) +
    U * W' * E_fn 2 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) +
    U * W * (dE_da 2 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) * a' +
      dE_db 2 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) * b' +
      dE_dU 2 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) +
      dE_dV 2 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) * ((W' * U - W) / U ^ 2)) =
    (pU_D φ k5Params.q20 U * ((⟨W, W'⟩ : Dual F) * (⟨a, a'⟩ : Dual F)) ^ 2 +
      pU_D φ k5Params.q11 U * ((⟨W, W'⟩ : Dual F) * (⟨a, a'⟩ : Dual F)) * ((⟨W, W'⟩ : Dual F) * (⟨b, b'⟩ : Dual F)) +
      pU_D φ k5Params.q02 U * ((⟨W, W'⟩ : Dual F) * (⟨b, b'⟩ : Dual F)) ^ 2 +
      (⟨W, W'⟩ : Dual F) * (Dual.C (φ k5Params.k2_V2) * (⟨W, W'⟩ : Dual F) ^ 2 +
        Dual.C (φ k5Params.k2_V1) * (⟨U, 1⟩ : Dual F) * (⟨W, W'⟩ : Dual F) +
        Dual.C (φ k5Params.k2_V0) * (⟨U, 1⟩ : Dual F) ^ 2)).eps := by
  rw [CoverParams.q20, pU_D_quadU, CoverParams.q11, pU_D_quadU, CoverParams.q02, pU_D_quadU]
  simp only [Dual.pow_eq, Dual.mul_eps, Dual.add_eps, Dual.mul_val, Dual.add_val, Dual.C_val, Dual.C_eps]
  simp only [E_fn, dE_da, dE_db, dE_dU, dE_dV, H_cub, dH_dS, dH_dQ, dH_dU, dH_dV,
    CoverParams.k2_V2, CoverParams.k2_V1, CoverParams.k2_V0,
    CoverParams.inv9, CoverParams.inv27, CoverParams.inv81,
    k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q, k5Params_T,
    map_add, map_sub, map_mul, map_pow, map_neg, map_inv₀, map_ofNat]
  field_simp [hU]; ring

private lemma dE3_along (a b U W a' b' W' : F) (hU : U ≠ 0) :
    W ^ 2 * E_fn 3 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) +
    2 * U * W * W' * E_fn 3 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) +
    U * W ^ 2 * (dE_da 3 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) * a' +
      dE_db 3 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) * b' +
      dE_dU 3 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) +
      dE_dV 3 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) * ((W' * U - W) / U ^ 2)) =
    (pU_D φ k5Params.c30 U * ((⟨W, W'⟩ : Dual F) * (⟨a, a'⟩ : Dual F)) ^ 3 +
      pU_D φ k5Params.c21 U * ((⟨W, W'⟩ : Dual F) * (⟨a, a'⟩ : Dual F)) ^ 2 * ((⟨W, W'⟩ : Dual F) * (⟨b, b'⟩ : Dual F)) +
      pU_D φ k5Params.c12 U * ((⟨W, W'⟩ : Dual F) * (⟨a, a'⟩ : Dual F)) * ((⟨W, W'⟩ : Dual F) * (⟨b, b'⟩ : Dual F)) ^ 2 +
      pU_D φ k5Params.c03 U * ((⟨W, W'⟩ : Dual F) * (⟨b, b'⟩ : Dual F)) ^ 3 +
      (⟨W, W'⟩ : Dual F) ^ 2 * (Dual.C (φ k5Params.k3_V2) * (⟨W, W'⟩ : Dual F) ^ 2 +
        Dual.C (φ k5Params.k3_V1) * (⟨U, 1⟩ : Dual F) * (⟨W, W'⟩ : Dual F) +
        Dual.C (φ k5Params.k3_V0) * (⟨U, 1⟩ : Dual F) ^ 2)).eps := by
  rw [CoverParams.c30, pU_D_quadU, CoverParams.c21, pU_D_quadU, CoverParams.c12, pU_D_quadU,
    CoverParams.c03, pU_D_quadU]
  simp only [Dual.pow_eq, Dual.mul_eps, Dual.add_eps, Dual.mul_val, Dual.add_val, Dual.C_val, Dual.C_eps]
  simp only [E_fn, dE_da, dE_db, dE_dU, dE_dV, H_cub, dH_dS, dH_dQ, dH_dU, dH_dV,
    CoverParams.k3_V2, CoverParams.k3_V1, CoverParams.k3_V0,
    CoverParams.inv9, CoverParams.inv27, CoverParams.inv243,
    k5Params_inv3, map_zero, map_mul, map_pow, map_neg, map_inv₀, map_ofNat]
  field_simp [hU]; ring

-- Homogenization identity relating `(M_abSQ ...).det` to `CoverParams.detM_W`.
private lemma detM_W_of_cover (U W : F) (hU : U ≠ 0) (hW0 : W ≠ 0)
    (hcb : pU φ k5Params.cb_h U ≠ 0) (hd1 : pUW φ k5Params.d1_z U W ≠ 0)
    (hW : W ^ 2 + pU φ k5Params.bW U * W + pU φ k5Params.cW U = 0) :
    let z := -pUW φ k5Params.d0_z U W / pUW φ k5Params.d1_z U W
    let a := z / W
    let b := -(pU φ k5Params.ca_h U * z + pUW φ k5Params.c0W U W) / (W * pU φ k5Params.cb_h U)
    let Cc := pUW φ k5Params.C_sub U W
    (M_abSQ (φ S_K) (φ Q_K) (φ T_K) a b U (W / U)).det =
      -((W / U) / Cc ^ 2) ^ 4 * pUW φ k5Params.detM_W U W := by
  intro z a b Cc
  have pUW_add (x y : PairAlg K5[X]) : pUW φ (PairAlg.add x y) U W = pUW φ x U W + pUW φ y U W := by
    simp only [pUW, PairAlg.map_add, PairAlg.evalAt_add]
  have pUW_sub (x y : PairAlg K5[X]) : pUW φ (PairAlg.sub x y) U W = pUW φ x U W - pUW φ y U W := by
    simp only [pUW, PairAlg.map_sub, PairAlg.evalAt_sub]
  have pUW_smul (s : K5[X]) (x : PairAlg K5[X]) : pUW φ (PairAlg.smul s x) U W = pU φ s U * pUW φ x U W := by
    simp only [pUW, pU, PairAlg.map_smul, PairAlg.evalAt_smul, RingHom.comp_apply,
      Polynomial.coe_evalRingHom, Polynomial.coe_mapRingHom]
  have pUW_pmul (x y : PairAlg K5[X]) : pUW φ (k5Params.pmul x y) U W = pUW φ x U W * pUW φ y U W := by
    simp only [pUW, CoverParams.pmul, PairAlg.map_mul, RingHom.comp_apply,
      Polynomial.coe_evalRingHom, Polynomial.coe_mapRingHom]
    exact PairAlg.evalAt_mul (pU φ k5Params.bW U) (pU φ k5Params.cW U) W hW _ _
  have pUW_W : pUW φ PairAlg.W U W = W := by simp [pUW, PairAlg.map_W, PairAlg.evalAt_W]
  have pUW_zero : pUW φ PairAlg.zero U W = 0 := by simp [pUW, PairAlg.map_zero, PairAlg.evalAt_zero]
  have hCc_eq : Cc = W * pU φ k5Params.cb_h U * pUW φ k5Params.d1_z U W := by
    dsimp only [Cc, CoverParams.C_sub]; rw [pUW_pmul, pUW_W, pUW_smul]; ring
  have hCc_ne : Cc ≠ 0 := by rw [hCc_eq]; exact mul_ne_zero (mul_ne_zero hW0 hcb) hd1
  have hA_eq : pUW φ k5Params.A_sub U W = -pU φ k5Params.cb_h U * pUW φ k5Params.d0_z U W := by
    rw [CoverParams.A_sub, pUW_smul]; simp [pU]
  have hB_eq : pUW φ k5Params.B_sub U W =
      pU φ k5Params.ca_h U * pUW φ k5Params.d0_z U W - pUW φ k5Params.c0W U W * pUW φ k5Params.d1_z U W := by
    rw [CoverParams.B_sub, pUW_sub, pUW_smul, pUW_pmul]
  have ha_div : a = pUW φ k5Params.A_sub U W / Cc := by
    rw [hA_eq, hCc_eq]; dsimp only [a, z]; field_simp [hW0, hcb, hd1]
  have hb_div : b = pUW φ k5Params.B_sub U W / Cc := by
    rw [hB_eq, hCc_eq]; dsimp only [b, z]; field_simp [hW0, hcb, hd1]; ring
  let xS_p : PairAlg K5[X] := PairAlg.sub (PairAlg.smul (C k5Params.S) k5Params.C_sub)
    (PairAlg.smul (C k5Params.T) k5Params.A_sub)
  let xQ_p : PairAlg K5[X] := PairAlg.sub (PairAlg.smul (C k5Params.Q) k5Params.C_sub)
    (PairAlg.smul (C k5Params.T) k5Params.B_sub)
  have hξS_div : φ S_K - a * φ T_K = pUW φ xS_p U W / Cc := by
    dsimp only [xS_p]; rw [pUW_sub, pUW_smul, pUW_smul, ha_div]
    simp only [pU, Polynomial.map_C, eval_C, k5Params_S, k5Params_T]
    field_simp [hCc_ne]; ring
  have hξQ_div : φ Q_K - b * φ T_K = pUW φ xQ_p U W / Cc := by
    dsimp only [xQ_p]; rw [pUW_sub, pUW_smul, pUW_smul, hb_div]
    simp only [pU, Polynomial.map_C, eval_C, k5Params_Q, k5Params_T]
    field_simp [hCc_ne]; ring
  have hdHS_hom (s q : PairAlg K5[X]) :
      dH_dS (pUW φ s U W / Cc) (pUW φ q U W / Cc) U (W / U) =
        ((W / U) / Cc ^ 2) * pUW φ (k5Params.dH_dS_hom s q) U W := by
    simp only [CoverParams.dH_dS_hom, pUW_add, pUW_sub, pUW_smul, pUW_pmul, dH_dS, pU,
      CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, CoverParams.inv243, k5Params_inv3,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg, Polynomial.map_C, Polynomial.map_X,
      Polynomial.map_ofNat, eval_mul, eval_pow, eval_neg, eval_C, eval_X, eval_ofNat,
      map_mul, map_pow, map_neg, map_inv₀, map_ofNat]
    field_simp [hU, hCc_ne]; ring
  have hdHQ_hom (s q v0 : PairAlg K5[X]) :
      dH_dQ (pUW φ s U W / Cc) (pUW φ q U W / Cc) (pUW φ v0 U W / Cc) U (W / U) =
        ((W / U) / Cc ^ 2) * pUW φ (k5Params.dH_dQ_hom s q v0) U W := by
    simp only [CoverParams.dH_dQ_hom, pUW_add, pUW_sub, pUW_smul, pUW_pmul, dH_dQ, pU,
      CoverParams.inv9, CoverParams.inv27, k5Params_inv3, k5Params_inv7,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg, Polynomial.map_C, Polynomial.map_X,
      Polynomial.map_ofNat, eval_mul, eval_pow, eval_neg, eval_C, eval_X, eval_ofNat,
      map_mul, map_pow, map_neg, map_inv₀, map_ofNat]
    field_simp [hU, hCc_ne]; ring
  set lam : F := (W / U) / Cc ^ 2
  have ha2_eq : q1_a2 a b U (W / U) = lam * pUW φ (k5Params.dH_dS_hom k5Params.A_sub k5Params.B_sub) U W := by
    rw [q1_a2, ha_div, hb_div, hdHS_hom]
  have ha0_eq : q1_a0 (φ S_K - a * φ T_K) (φ Q_K - b * φ T_K) U (W / U) =
      lam * pUW φ (k5Params.dH_dS_hom xS_p xQ_p) U W := by
    rw [q1_a0, hξS_div, hξQ_div, hdHS_hom]
  have ha1_eq : q1_a1 a b (φ S_K - a * φ T_K) (φ Q_K - b * φ T_K) U (W / U) =
      lam * (pUW φ (k5Params.dH_dS_hom (PairAlg.add k5Params.A_sub xS_p) (PairAlg.add k5Params.B_sub xQ_p)) U W -
        pUW φ (k5Params.dH_dS_hom k5Params.A_sub k5Params.B_sub) U W -
        pUW φ (k5Params.dH_dS_hom xS_p xQ_p) U W) := by
    rw [q1_a1, hξS_div, hξQ_div, ha_div, hb_div, ← add_div, ← add_div, ← pUW_add, ← pUW_add,
      hdHS_hom, hdHS_hom, hdHS_hom]; ring
  have hb2_eq : q2_b2 a b U (W / U) =
      lam * pUW φ (k5Params.dH_dQ_hom k5Params.A_sub k5Params.B_sub PairAlg.zero) U W := by
    rw [q2_b2, ha_div, hb_div, show (0 : F) = pUW φ PairAlg.zero U W / Cc by simp [pUW_zero], hdHQ_hom]
  have hb0_eq : q2_b0 (φ S_K - a * φ T_K) (φ Q_K - b * φ T_K) U (W / U) =
      lam * pUW φ (k5Params.dH_dQ_hom xS_p xQ_p k5Params.C_sub) U W := by
    rw [q2_b0, hξS_div, hξQ_div, show (1 : F) = pUW φ k5Params.C_sub U W / Cc from (div_self hCc_ne).symm, hdHQ_hom]
  have hb1_eq : q2_b1 a b (φ S_K - a * φ T_K) (φ Q_K - b * φ T_K) U (W / U) =
      lam * (pUW φ (k5Params.dH_dQ_hom (PairAlg.add k5Params.A_sub xS_p) (PairAlg.add k5Params.B_sub xQ_p) PairAlg.zero) U W -
        pUW φ (k5Params.dH_dQ_hom k5Params.A_sub k5Params.B_sub PairAlg.zero) U W -
        pUW φ (k5Params.dH_dQ_hom xS_p xQ_p PairAlg.zero) U W +
        pU φ (C (10 * k5Params.inv7) * X) U * pUW φ (k5Params.pmul k5Params.B_sub k5Params.C_sub) U W) := by
    rw [q2_b1, hξS_div, hξQ_div, ha_div, hb_div, ← add_div, ← add_div, ← pUW_add, ← pUW_add,
      show (0 : F) = pUW φ PairAlg.zero U W / Cc by simp [pUW_zero],
      hdHQ_hom, hdHQ_hom, hdHQ_hom, pUW_pmul]
    simp only [pU, k5Params_inv7, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Polynomial.map_ofNat,
      eval_mul, eval_C, eval_X, eval_ofNat, map_mul, map_inv₀, map_ofNat]
    dsimp only [lam, Cc]
    field_simp [hU, hCc_ne]
  rw [M_abSQ_det]
  have hSmat : S_ab_mat a b (φ S_K - a * φ T_K) (φ Q_K - b * φ T_K) U (W / U) =
      Matrix.of ![![0, 0, q1_a0 (φ S_K - a * φ T_K) (φ Q_K - b * φ T_K) U (W / U),
                         q2_b0 (φ S_K - a * φ T_K) (φ Q_K - b * φ T_K) U (W / U)],
                  ![q1_a0 (φ S_K - a * φ T_K) (φ Q_K - b * φ T_K) U (W / U),
                    q2_b0 (φ S_K - a * φ T_K) (φ Q_K - b * φ T_K) U (W / U),
                    q1_a1 a b (φ S_K - a * φ T_K) (φ Q_K - b * φ T_K) U (W / U),
                    q2_b1 a b (φ S_K - a * φ T_K) (φ Q_K - b * φ T_K) U (W / U)],
                  ![q1_a1 a b (φ S_K - a * φ T_K) (φ Q_K - b * φ T_K) U (W / U),
                    q2_b1 a b (φ S_K - a * φ T_K) (φ Q_K - b * φ T_K) U (W / U),
                    q1_a2 a b U (W / U), q2_b2 a b U (W / U)],
                  ![q1_a2 a b U (W / U), q2_b2 a b U (W / U), 0, 0]] := rfl
  rw [hSmat, S_ab_mat_det, ha2_eq, ha1_eq, ha0_eq, hb2_eq, hb1_eq, hb0_eq]
  have hdetM : pUW φ k5Params.detM_W U W =
      let a2 := pUW φ (k5Params.dH_dS_hom k5Params.A_sub k5Params.B_sub) U W
      let a0 := pUW φ (k5Params.dH_dS_hom xS_p xQ_p) U W
      let a1 := pUW φ (k5Params.dH_dS_hom (PairAlg.add k5Params.A_sub xS_p) (PairAlg.add k5Params.B_sub xQ_p)) U W - a2 - a0
      let b2 := pUW φ (k5Params.dH_dQ_hom k5Params.A_sub k5Params.B_sub PairAlg.zero) U W
      let b0 := pUW φ (k5Params.dH_dQ_hom xS_p xQ_p k5Params.C_sub) U W
      let b1 := pUW φ (k5Params.dH_dQ_hom (PairAlg.add k5Params.A_sub xS_p) (PairAlg.add k5Params.B_sub xQ_p) PairAlg.zero) U W -
        b2 - pUW φ (k5Params.dH_dQ_hom xS_p xQ_p PairAlg.zero) U W +
        pU φ (C (10 * k5Params.inv7) * X) U * pUW φ (k5Params.pmul k5Params.B_sub k5Params.C_sub) U W
      (a2 * b0 - a0 * b2) ^ 2 - (a2 * b1 - a1 * b2) * (a1 * b0 - a0 * b1) := by
    dsimp only [CoverParams.detM_W]
    simp only [pUW_sub, pUW_add, pUW_pmul, pUW_smul]
    ring
  rw [hdetM]; ring

end DualCoverDeriv

-- Pointwise branch evaluation `valAC r w : A_C → CoverL` for `RegAC r` elements!
section BranchEval

private def valAC (r w : CoverL) (x : A_C) : CoverL :=
  valueAt r (mapRatFunc ιL_K5 (coordsAC x).c0) +
  valueAt r (mapRatFunc ιL_K5 (coordsAC x).c1) * w

private structure ValAC (r w : CoverL) (x : A_C) (v : CoverL) : Prop where
  reg : RegAC r x
  eq : valAC r w x = v

private lemma valAC_evalAC (r w : CoverL) (p : PairAlg (RatFunc K5)) :
    valAC r w (evalAC p) = valueAt r (mapRatFunc ιL_K5 p.c0) + valueAt r (mapRatFunc ιL_K5 p.c1) * w := by
  simp only [valAC, coordsAC_evalAC]

private lemma valAC_zero (r w : CoverL) : ValAC r w 0 0 := by
  refine ⟨regAC_zero r, ?_⟩
  rw [← evalAC_zero, valAC_evalAC]; simp [PairAlg.zero]

private lemma valAC_one (r w : CoverL) : ValAC r w 1 1 := by
  refine ⟨regAC_one r, ?_⟩
  rw [← evalAC_one, valAC_evalAC, PairAlg.one]
  simp only [map_one, map_zero, zero_mul, add_zero]
  rw [show (1 : RatFunc CoverL) = RatFunc.C 1 from (map_one RatFunc.C).symm, valueAt_C]

private lemma valAC_ofNat (r w : CoverL) (n : ℕ) [n.AtLeastTwo] :
    ValAC r w (OfNat.ofNat n) (OfNat.ofNat n) := by
  refine ⟨regAC_ofNat r n, ?_⟩
  have h1 : (OfNat.ofNat n : A_C) = evalAC (PairAlg.ofScalar (OfNat.ofNat n)) := by
    rw [evalAC_ofScalar, map_ofNat]
  rw [h1, valAC_evalAC, PairAlg.ofScalar]
  simp only [map_ofNat, map_zero, zero_mul, add_zero]
  have hc : (OfNat.ofNat n : RatFunc CoverL) = RatFunc.C (OfNat.ofNat n) := (map_ofNat RatFunc.C n).symm
  rw [hc, valueAt_C]

private lemma valAC_ιC_K5 (r w : CoverL) (c : K5) : ValAC r w (ιC_K5 c) (ιL_K5 c) := by
  refine ⟨regAC_ιC_K5 r c, ?_⟩
  have h1 : ιC_K5 c = evalAC (PairAlg.ofScalar (RatFunc.C c)) := by
    rw [evalAC_ofScalar]; rfl
  rw [h1, valAC_evalAC, PairAlg.ofScalar]
  simp only [mapRatFunc_C, map_zero, valueAt_C, zero_mul, add_zero]

private lemma valAC_polyC (r w : CoverL) (P : K5[X]) :
    ValAC r w (polyC P) ((P.map ιL_K5).eval r) := by
  refine ⟨regAC_polyC r P, ?_⟩
  rw [polyC, ← evalAC_ofScalar, valAC_evalAC, PairAlg.ofScalar]
  simp only [mapRatFunc_algebraMap, map_zero, valueAt_polynomial, zero_mul, add_zero]

private lemma valAC_pairC (r w : CoverL) (y : PairAlg K5[X]) :
    ValAC r w (pairC y) (pUW ιL_K5 y r w) := by
  refine ⟨regAC_pairC r y, ?_⟩
  rw [pairC, valAC_evalAC, PairAlg.map]
  simp only [mapRatFunc_algebraMap, valueAt_polynomial]
  rfl

private lemma valAC_U_C (r w : CoverL) : ValAC r w U_C r := by
  refine ⟨regAC_U_C r, ?_⟩
  have hU : U_C = polyC X := by simp [U_C, polyC, RatFunc.algebraMap_X]
  rw [hU]; simpa using (valAC_polyC r w X).eq

private lemma valAC_W_C (r w : CoverL) : ValAC r w W_C w := by
  refine ⟨regAC_W_C r, ?_⟩
  rw [← evalAC_W, valAC_evalAC, PairAlg.W]
  simp only [map_zero, map_one, zero_add]
  rw [show (1 : RatFunc CoverL) = RatFunc.C 1 from (map_one RatFunc.C).symm, valueAt_C, one_mul]

private lemma valAC_add {r w : CoverL} {x y : A_C} {vx vy : CoverL}
    (hx : ValAC r w x vx) (hy : ValAC r w y vy) : ValAC r w (x + y) (vx + vy) := by
  refine ⟨regAC_add hx.reg hy.reg, ?_⟩
  have hxy : coordsAC (x + y) = PairAlg.add (coordsAC x) (coordsAC y) := by
    apply evalAC_injective; rw [evalAC_coordsAC, evalAC_add, evalAC_coordsAC, evalAC_coordsAC]
  rw [valAC, hxy, PairAlg.add]
  simp only [map_add]
  have h1 := hx.eq; have h2 := hy.eq; dsimp only [valAC] at h1 h2
  linear_combination h1 + h2

private lemma valAC_sub {r w : CoverL} {x y : A_C} {vx vy : CoverL}
    (hx : ValAC r w x vx) (hy : ValAC r w y vy) : ValAC r w (x - y) (vx - vy) := by
  refine ⟨regAC_sub hx.reg hy.reg, ?_⟩
  have hxy : coordsAC (x - y) = PairAlg.sub (coordsAC x) (coordsAC y) := by
    apply evalAC_injective; rw [evalAC_coordsAC, evalAC_sub, evalAC_coordsAC, evalAC_coordsAC]
  rw [valAC, hxy, PairAlg.sub]
  simp only [map_sub]
  have h1 := hx.eq; have h2 := hy.eq; dsimp only [valAC] at h1 h2
  linear_combination h1 - h2

private lemma valAC_neg {r w : CoverL} {x : A_C} {vx : CoverL}
    (hx : ValAC r w x vx) : ValAC r w (-x) (-vx) := by
  refine ⟨regAC_neg hx.reg, ?_⟩
  have hxy : coordsAC (-x) = PairAlg.neg (coordsAC x) := by
    apply evalAC_injective; rw [evalAC_coordsAC, evalAC_neg, evalAC_coordsAC]
  rw [valAC, hxy, PairAlg.neg]
  simp only [map_neg]
  have h1 := hx.eq; dsimp only [valAC] at h1
  linear_combination -h1

private lemma valAC_mul {r w : CoverL}
    (hW : w ^ 2 + (k5Params.bW.map ιL_K5).eval r * w + (k5Params.cW.map ιL_K5).eval r = 0)
    {x y : A_C} {vx vy : CoverL}
    (hx : ValAC r w x vx) (hy : ValAC r w y vy) : ValAC r w (x * y) (vx * vy) := by
  refine ⟨regAC_mul hx.reg hy.reg, ?_⟩
  have hxy : coordsAC (x * y) = PairAlg.mul (toRat k5Params.bW) (toRat k5Params.cW) (coordsAC x) (coordsAC y) := by
    apply evalAC_injective; rw [evalAC_coordsAC, evalAC_mul, evalAC_coordsAC, evalAC_coordsAC]
  rw [valAC, hxy, PairAlg.mul]
  have hx0 : RegularAt r (mapRatFunc ιL_K5 (coordsAC x).c0) := hx.reg.c0
  have hx1 : RegularAt r (mapRatFunc ιL_K5 (coordsAC x).c1) := hx.reg.c1
  have hy0 : RegularAt r (mapRatFunc ιL_K5 (coordsAC y).c0) := hy.reg.c0
  have hy1 : RegularAt r (mapRatFunc ιL_K5 (coordsAC y).c1) := hy.reg.c1
  have hbW : RegularAt r (mapRatFunc ιL_K5 (toRat k5Params.bW)) := by
    rw [mapRatFunc_algebraMap]; exact RegularAt.polynomial r _
  have hcW : RegularAt r (mapRatFunc ιL_K5 (toRat k5Params.cW)) := by
    rw [mapRatFunc_algebraMap]; exact RegularAt.polynomial r _
  simp only [map_add, map_sub, map_mul]
  rw [valueAt_mul_of_regularAt hx0 hy0, valueAt_mul_of_regularAt hx0 hy1,
    valueAt_mul_of_regularAt hx1 hy0,
    valueAt_mul_of_regularAt (regAt_mul_local hx1 hy1) hcW,
    valueAt_mul_of_regularAt (regAt_mul_local hx1 hy1) hbW,
    valueAt_mul_of_regularAt hx1 hy1]
  simp only [mapRatFunc_algebraMap, valueAt_polynomial]
  have h1 := hx.eq; have h2 := hy.eq; dsimp only [valAC] at h1 h2
  rw [← h1, ← h2]
  linear_combination -valueAt r (mapRatFunc ιL_K5 (coordsAC x).c1) *
    valueAt r (mapRatFunc ιL_K5 (coordsAC y).c1) * hW

private lemma valAC_pow {r w : CoverL}
    (hW : w ^ 2 + (k5Params.bW.map ιL_K5).eval r * w + (k5Params.cW.map ιL_K5).eval r = 0)
    {x : A_C} {vx : CoverL} (hx : ValAC r w x vx) (n : ℕ) :
    ValAC r w (x ^ n) (vx ^ n) := by
  induction n with
  | zero => simpa using valAC_one r w
  | succ k ih => rw [pow_succ, pow_succ]; exact valAC_mul hW ih hx

private lemma valAC_div_of_reg {r w : CoverL}
    (hW : w ^ 2 + (k5Params.bW.map ιL_K5).eval r * w + (k5Params.cW.map ιL_K5).eval r = 0)
    {x y : A_C} {vx vy : CoverL}
    (hx : ValAC r w x vx) (hy : ValAC r w y vy) (hreg : RegAC r (x / y)) (hvy : vy ≠ 0) :
    ValAC r w (x / y) (vx / vy) := by
  refine ⟨hreg, ?_⟩
  have hy_ne : y ≠ 0 := by
    intro h0; subst h0
    have := hy.eq.symm.trans (valAC_zero r w).eq
    exact hvy this
  have hmul : valAC r w (x / y) * vy = vx := by
    have h := (valAC_mul hW ⟨hreg, rfl⟩ hy).eq
    rw [div_mul_cancel₀ x hy_ne, hx.eq] at h
    exact h.symm
  exact (eq_div_iff hvy).mpr hmul

private lemma valAC_div_nat {r w : CoverL}
    (hW : w ^ 2 + (k5Params.bW.map ιL_K5).eval r * w + (k5Params.cW.map ιL_K5).eval r = 0)
    {x : A_C} {vx : CoverL} (hx : ValAC r w x vx) (n : ℕ) [hn2 : n.AtLeastTwo] :
    ValAC r w (x / OfNat.ofNat n) (vx / OfNat.ofNat n) := by
  have hn : (OfNat.ofNat n : CoverL) ≠ 0 := by
    change (n : CoverL) ≠ 0
    exact Nat.cast_ne_zero.mpr (by have := hn2.prop; omega)
  exact valAC_div_of_reg hW hx (valAC_ofNat r w n) (regAC_div_ofNat hx.reg n hn) hn

private lemma valAC_P18_z_AC {r w : CoverL}
    (hr0 : r ≠ 0) (hr1 : r ≠ 1) (hw0 : w ≠ 0)
    (hcb : (k5Params.cb_h.map ιL_K5).eval r ≠ 0)
    (hnmWU : (k5Params.nm_WU.map ιL_K5).eval r ≠ 0)
    (hW : w ^ 2 + (k5Params.bW.map ιL_K5).eval r * w + (k5Params.cW.map ιL_K5).eval r = 0)
    {z : A_C} {vz : CoverL} (hz : ValAC r w z vz) :
    ValAC r w (P18_z_AC z)
      (SheetCalculus.P18_of (SL (L := CoverL)) QL TL xL yL
        (vz / w) (-(pU ιL_K5 k5Params.ca_h r * vz + pUW ιL_K5 k5Params.c0W r w) / (w * pU ιL_K5 k5Params.cb_h r))
        r (w / r)) := by
  have hS : ValAC r w (ιC_K5 S_K) SL := valAC_ιC_K5 r w S_K
  have hQ : ValAC r w (ιC_K5 Q_K) QL := valAC_ιC_K5 r w Q_K
  have hT : ValAC r w (ιC_K5 T_K) TL := valAC_ιC_K5 r w T_K
  have hx : ValAC r w (ιC_K5 x_K) xL := valAC_ιC_K5 r w x_K
  have hy : ValAC r w (ιC_K5 y_K) yL := valAC_ιC_K5 r w y_K
  have hU : ValAC r w U_C r := valAC_U_C r w
  have hW_v : ValAC r w W_C w := valAC_W_C r w
  have hV : ValAC r w V_C (w / r) :=
    valAC_div_of_reg hW hW_v hU (regAC_V_C hr0) hr0
  have hV_ne : w / r ≠ 0 := div_ne_zero hw0 hr0
  have hu_ne : u_of r ≠ 0 := by
    rw [u_of]; exact div_ne_zero (sub_ne_zero.mpr hr1) (by exact_mod_cast (by decide : (9 : ℕ) ≠ 0))
  have hv_ne : v_of (w / r) ≠ 0 := by
    rw [v_of]
    refine div_ne_zero (sub_ne_zero.mpr ?_) (by exact_mod_cast (by decide : (9 : ℕ) ≠ 0))
    intro hwr
    have hw_eq : w = r := by rw [div_eq_one_iff_eq hr0] at hwr; exact hwr
    have hnm0 : (k5Params.nm_WU.map ιL_K5).eval r = 0 := by
      simp only [CoverParams.nm_WU, CoverParams.pnm, PairAlg.nm, Polynomial.map_add,
        Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg,
        Polynomial.map_X, Polynomial.map_one, eval_add, eval_sub, eval_mul, eval_pow,
        eval_neg, eval_X, eval_one]
      rw [hw_eq] at hW; linear_combination hW
    exact hnmWU hnm0
  have ha : ValAC r w (z / W_C) (vz / w) :=
    valAC_div_of_reg hW hz hW_v (regAC_div_W_C hz.reg hr0) hw0
  have hb_reg : RegAC r (-(polyC k5Params.ca_h * z + pairC k5Params.c0W) / (W_C * polyC k5Params.cb_h)) := by
    rw [← div_div]
    exact regAC_div_polyC (regAC_div_W_C (regAC_neg (regAC_add
      (regAC_mul (regAC_polyC r _) hz.reg) (regAC_pairC r _))) hr0) hcb
  have hb : ValAC r w
      (-(polyC k5Params.ca_h * z + pairC k5Params.c0W) / (W_C * polyC k5Params.cb_h))
      (-(pU ιL_K5 k5Params.ca_h r * vz + pUW ιL_K5 k5Params.c0W r w) / (w * pU ιL_K5 k5Params.cb_h r)) :=
    valAC_div_of_reg hW
      (valAC_neg (valAC_add (valAC_mul hW (valAC_polyC r w _) hz) (valAC_pairC r w _)))
      (valAC_mul hW hW_v (valAC_polyC r w _)) hb_reg (mul_ne_zero hw0 hcb)
  set aC := z / W_C
  set bC := -(polyC k5Params.ca_h * z + pairC k5Params.c0W) / (W_C * polyC k5Params.cb_h)
  set aL := vz / w
  set bL := -(pU ιL_K5 k5Params.ca_h r * vz + pUW ιL_K5 k5Params.c0W r w) / (w * pU ιL_K5 k5Params.cb_h r)
  set ξSC := ιC_K5 S_K - aC * ιC_K5 T_K; set ξQC := ιC_K5 Q_K - bC * ιC_K5 T_K
  set ξSL := SL - aL * TL; set ξQL := QL - bL * TL
  have hξS : ValAC r w ξSC ξSL := valAC_sub hS (valAC_mul hW ha hT)
  have hξQ : ValAC r w ξQC ξQL := valAC_sub hQ (valAC_mul hW hb hT)
  have hmul {x y : A_C} {vx vy : CoverL} := @valAC_mul r w hW x y vx vy
  have hpow {x : A_C} {vx : CoverL} := @valAC_pow r w hW x vx
  have hdivn {x : A_C} {vx : CoverL} (hx : ValAC r w x vx) (n : ℕ) [n.AtLeastTwo] := valAC_div_nat hW hx n
  have hdHS : ∀ {s q : A_C} {vs vq : CoverL}, ValAC r w s vs → ValAC r w q vq →
      ValAC r w (dH_dS s q U_C V_C) (dH_dS vs vq r (w / r)) := fun hs hq => by
    dsimp only [dH_dS]
    repeat (with_reducible (first | exact hs | exact hq | exact hU | exact hV | exact valAC_ofNat r w _ | apply hdivn | apply valAC_add | apply valAC_sub | apply valAC_neg | apply hmul | apply hpow))
  have hdHQ : ∀ {s q v0 : A_C} {vs vq vv0 : CoverL}, ValAC r w s vs → ValAC r w q vq →
      ValAC r w v0 vv0 → ValAC r w (dH_dQ s q v0 U_C V_C) (dH_dQ vs vq vv0 r (w / r)) := fun hs hq hv0 => by
    dsimp only [dH_dQ]
    repeat (with_reducible (first | exact hs | exact hq | exact hv0 | exact hU | exact hV | exact valAC_ofNat r w _ | apply hdivn | apply valAC_add | apply valAC_sub | apply valAC_neg | apply hmul | apply hpow))
  have hnumM (mi : Fin 10) : ValAC r w (numM mi aC bC ξSC ξQC U_C V_C) (numM mi aL bL ξSL ξQL r (w / r)) := by
    have ha2 : ValAC r w (q1_a2 aC bC U_C V_C) (q1_a2 aL bL r (w / r)) := hdHS ha hb
    have ha0 : ValAC r w (q1_a0 ξSC ξQC U_C V_C) (q1_a0 ξSL ξQL r (w / r)) := hdHS hξS hξQ
    have ha1 : ValAC r w (q1_a1 aC bC ξSC ξQC U_C V_C) (q1_a1 aL bL ξSL ξQL r (w / r)) :=
      valAC_sub (valAC_sub (hdHS (valAC_add ha hξS) (valAC_add hb hξQ)) ha2) ha0
    have hb2 : ValAC r w (q2_b2 aC bC U_C V_C) (q2_b2 aL bL r (w / r)) := hdHQ ha hb (valAC_zero r w)
    have hb0 : ValAC r w (q2_b0 ξSC ξQC U_C V_C) (q2_b0 ξSL ξQL r (w / r)) := hdHQ hξS hξQ (valAC_one r w)
    have hb1 : ValAC r w (q2_b1 aC bC ξSC ξQC U_C V_C) (q2_b1 aL bL ξSL ξQL r (w / r)) := by
      have h00 := hdHQ (valAC_add ha hξS) (valAC_add hb hξQ) (valAC_zero r w)
      have h01 := hdHQ hξS hξQ (valAC_zero r w)
      exact valAC_add (valAC_sub (valAC_sub h00 hb2) h01)
        (hmul (hmul (hmul (hdivn (valAC_ofNat r w 10) 7) hb) hU) hV)
    have hd20 := valAC_sub (hmul ha2 hb0) (hmul ha0 hb2)
    have hd21 := valAC_sub (hmul ha2 hb1) (hmul ha1 hb2)
    have hd10 := valAC_sub (hmul ha1 hb0) (hmul ha0 hb1)
    have hcomb {m2 m1 m0 : A_C} {v2 v1 v0 : CoverL}
        (hm2 : ValAC r w m2 v2) (hm1 : ValAC r w m1 v1) (hm0 : ValAC r w m0 v0) :=
      hmul (hdivn (valAC_one r w) 16)
        (valAC_add (valAC_sub (hmul hm2 hd10) (hmul hm1 hd20)) (hmul hm0 hd21))
    fin_cases mi
    · exact hcomb (hpow ha 2) (hmul (hmul (valAC_ofNat r w 2) ha) hξS) (hpow hξS 2)
    · exact hcomb (hmul ha hb) (valAC_add (hmul ha hξQ) (hmul hb hξS)) (hmul hξS hξQ)
    · exact hcomb (hpow hb 2) (hmul (hmul (valAC_ofNat r w 2) hb) hξQ) (hpow hξQ 2)
    · exact hcomb ha hξS (valAC_zero r w)
    · exact hcomb (valAC_zero r w) ha hξS
    · exact hcomb hb hξQ (valAC_zero r w)
    · exact hcomb (valAC_zero r w) hb hξQ
    · exact hcomb (valAC_one r w) (valAC_zero r w) (valAC_zero r w)
    · exact hcomb (valAC_zero r w) (valAC_one r w) (valAC_zero r w)
    · exact hcomb (valAC_zero r w) (valAC_zero r w) (valAC_one r w)
  have hA0U : ValAC r w (A_0U aC bC ξSC ξQC U_C V_C) (A_0U aL bL ξSL ξQL r (w / r)) := by
    dsimp only [A_0U]
    repeat (with_reducible (first | exact hnumM _ | exact valAC_ofNat r w _ | apply hdivn | apply valAC_add | apply valAC_sub | apply valAC_neg | apply hmul))
  have hA0V : ValAC r w (A_0V aC bC ξSC ξQC U_C V_C) (A_0V aL bL ξSL ξQL r (w / r)) := by
    dsimp only [A_0V]
    repeat (with_reducible (first | exact hnumM _ | exact valAC_ofNat r w _ | apply hdivn | apply valAC_add | apply valAC_sub | apply valAC_neg | apply hmul))
  have hAY : ValAC r w (A_Y aC bC ξSC ξQC U_C V_C) (A_Y aL bL ξSL ξQL r (w / r)) := by
    dsimp only [A_Y]
    repeat (with_reducible (first | exact hU | exact hV | exact hnumM _ | exact valAC_ofNat r w _ | apply hdivn | apply valAC_add | apply valAC_sub | apply valAC_neg | apply hmul))
  have hAX : ValAC r w (A_X aC bC ξSC ξQC U_C V_C) (A_X aL bL ξSL ξQL r (w / r)) := by
    dsimp only [A_X]
    repeat (with_reducible (first | exact hU | exact hnumM _ | exact valAC_ofNat r w _ | apply hdivn | apply valAC_add | apply valAC_sub | apply valAC_neg | apply hmul))
  have hM0 : ValAC r w (A_0U aC bC ξSC ξQC U_C V_C / U_C + A_0V aC bC ξSC ξQC U_C V_C / V_C)
      (A_0U aL bL ξSL ξQL r (w / r) / r + A_0V aL bL ξSL ξQL r (w / r) / (w / r)) :=
    valAC_add (valAC_div_of_reg hW hA0U hU (regAC_div_U_C hA0U.reg hr0) hr0)
      (valAC_div_of_reg hW hA0V hV (regAC_div_V_C hA0V.reg hr0) hV_ne)
  have hu : ValAC r w (u_of U_C) (u_of r) := hdivn (valAC_sub hU (valAC_one r w)) 9
  have hv : ValAC r w (v_of V_C) (v_of (w / r)) := hdivn (valAC_sub hV (valAC_one r w)) 9
  have hH0 : ValAC r w (H0_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K)) (H0_of SL QL TL) := by
    dsimp only [H0_of]
    repeat (with_reducible (first | exact hS | exact hQ | exact hT | exact valAC_ofNat r w _ | apply hdivn | apply valAC_add | apply valAC_sub | apply valAC_neg | apply hmul | apply hpow))
  have hdH0 (k : Fin 3) : ValAC r w (dH0_fn k (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K)) (dH0_fn k SL QL TL) := by
    fin_cases k <;> dsimp only [dH0_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      repeat (with_reducible (first | exact hS | exact hQ | exact hT | exact valAC_ofNat r w _ | apply hdivn | apply valAC_add | apply valAC_sub | apply valAC_neg | apply hmul | apply hpow))
  have hdF5 (k : Fin 5) : ValAC r w (dF5_fn k (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K))
      (dF5_fn k SL QL TL xL yL) := by
    fin_cases k <;> dsimp only [dF5_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      repeat (with_reducible (first | exact hS | exact hT | exact hx | exact hy | exact hdH0 _ | exact valAC_ofNat r w _ | apply valAC_add | apply hmul | apply hpow))
  have hu3 : ValAC r w (u3_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 x_K)) (u3_of SL QL xL) := by
    dsimp only [u3_of]
    repeat (with_reducible (first | exact hS | exact hQ | exact hx | exact valAC_ofNat r w _ | apply valAC_add | apply valAC_sub | apply hmul))
  have hv3 : ValAC r w (v3_of (ιC_K5 T_K) (ιC_K5 y_K)) (v3_of TL yL) := by
    dsimp only [v3_of]
    repeat (with_reducible (first | exact hT | exact hy | exact valAC_ofNat r w _ | apply valAC_add | apply valAC_sub))
  have hDX2 : ValAC r w (DX2_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 x_K)) (DX2_of SL QL xL) := by
    dsimp only [DX2_of]
    repeat (with_reducible (first | exact hS | exact hQ | exact hu3 | exact valAC_ofNat r w _ | apply valAC_add | apply valAC_sub | apply hmul | apply hpow))
  have hDY2 : ValAC r w (DY2_of (ιC_K5 T_K) (ιC_K5 y_K)) (DY2_of TL yL) := by
    dsimp only [DY2_of]
    repeat (with_reducible (first | exact hT | exact hv3 | exact valAC_ofNat r w _ | apply valAC_add | apply valAC_sub | apply hmul | apply hpow))
  have hW2 : ValAC r w (W2_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K))
      (W2_of SL QL TL xL yL) := hmul (hmul (hmul hS hT) hDX2) hDY2
  have hLX : ValAC r w (LX_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 x_K) U_C) (LX_of SL QL xL r) := by
    dsimp only [LX_of]
    repeat (with_reducible (first | exact hu | exact hS | exact hQ | exact hu3 | exact hU | exact valAC_ofNat r w _ | apply hdivn | apply valAC_add | apply valAC_sub | apply hmul))
  have hLY : ValAC r w (LY_of (ιC_K5 T_K) (ιC_K5 y_K) V_C) (LY_of TL yL (w / r)) := by
    dsimp only [LY_of]
    repeat (with_reducible (first | exact hv | exact hT | exact hv3 | exact hV | exact valAC_ofNat r w _ | apply hdivn | apply valAC_add | apply valAC_sub | apply hmul))
  have hdLX (k : Fin 5) : ValAC r w (dLX_fn k U_C) (dLX_fn k r) := by
    fin_cases k <;> dsimp only [dLX_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      repeat (with_reducible (first | exact hu | exact hU | exact valAC_zero r w | exact valAC_ofNat r w _ | apply hdivn | apply valAC_add | apply valAC_sub | apply valAC_neg | apply hmul))
  have hdLY (k : Fin 5) : ValAC r w (dLY_fn k V_C) (dLY_fn k (w / r)) := by
    fin_cases k <;> dsimp only [dLY_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      repeat (with_reducible (first | exact hv | exact hV | exact valAC_zero r w | exact valAC_ofNat r w _ | apply hdivn | apply valAC_add | apply valAC_neg | apply hmul))
  have hbr (k : Fin 5) : ValAC r w (br_fn k (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) U_C V_C)
      (br_fn k SL QL TL xL yL r (w / r)) := by
    dsimp only [br_fn]
    refine valAC_add ?_ (hmul (hmul (hmul (valAC_ofNat r w 2) hS) hT)
      (valAC_sub (hmul hLX (hdLY k)) (hmul hLY (hdLX k))))
    fin_cases k
    · exact hmul (hmul (valAC_neg hT) hLX) hLY
    · exact valAC_zero r w
    · exact hmul (hmul hS hLX) hLY
    · exact valAC_zero r w
    · exact valAC_zero r w
  have hdDX2 (k : Fin 5) : ValAC r w (dDX2_fn k (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 x_K)) (dDX2_fn k SL QL xL) := by
    fin_cases k <;> dsimp only [dDX2_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      repeat (with_reducible (first | exact hS | exact hQ | exact hu3 | exact valAC_zero r w | exact valAC_ofNat r w _ | apply valAC_add | apply valAC_sub | apply valAC_neg | apply hmul | apply hpow))
  have hdDY2 (k : Fin 5) : ValAC r w (dDY2_fn k (ιC_K5 T_K) (ιC_K5 y_K)) (dDY2_fn k TL yL) := by
    fin_cases k <;> dsimp only [dDY2_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      repeat (with_reducible (first | exact hT | exact hv3 | exact valAC_zero r w | exact valAC_one r w | exact valAC_ofNat r w _ | apply valAC_add | apply valAC_sub | apply valAC_neg | apply hmul | apply hpow))
  have hFc (f2 : Fin 5 → Fin 5 → A_C) (v2 : Fin 5 → Fin 5 → CoverL)
      (hf2 : ∀ i j, ValAC r w (f2 i j) (v2 i j)) (i : Fin 3) :
      ValAC r w (F_contract (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) f2 i)
        (F_contract SL QL TL xL yL v2 i) := by
    fin_cases i <;> dsimp only [F_contract, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      exact valAC_add (valAC_add (hmul (hdF5 4) (hf2 _ 3)) (hmul (hdF5 3) (hf2 4 _))) (hmul (hdF5 _) (hf2 3 4))
  have hdot (v : Fin 3 → A_C) (vl : Fin 3 → CoverL) (hv_v : ∀ i, ValAC r w (v i) (vl i)) :
      ValAC r w (dot_ab v aC bC) (dot_ab vl aL bL) :=
    valAC_add (valAC_add (hmul (hv_v 0) ha) (hmul (hv_v 1) hb)) (hv_v 2)
  have hom (i j : Fin 5) : ValAC r w (om_fn i j (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) U_C V_C)
      (om_fn i j SL QL TL xL yL r (w / r)) := by
    dsimp only [om_fn]
    have homX (k : Fin 5) : ValAC r w
        (match k with
         | 0 => -25 * ιC_K5 S_K * U_C + 15 * ιC_K5 Q_K * U_C + 9 * ιC_K5 x_K * U_C + 25 * ιC_K5 S_K - 15 * ιC_K5 Q_K
         | 1 => 30 * (U_C - 1) * ιC_K5 S_K
         | 3 => 18 * U_C * ιC_K5 S_K
         | _ => 0)
        (match k with
         | 0 => -25 * SL * r + 15 * QL * r + 9 * xL * r + 25 * SL - 15 * QL
         | 1 => 30 * (r - 1) * SL
         | 3 => 18 * r * SL
         | _ => 0) := by
      rcases k with ⟨_ | _ | _ | _ | _ | k, hk⟩
      · change ValAC r w (-25 * ιC_K5 S_K * U_C + 15 * ιC_K5 Q_K * U_C + 9 * ιC_K5 x_K * U_C + 25 * ιC_K5 S_K - 15 * ιC_K5 Q_K)
            (-25 * SL * r + 15 * QL * r + 9 * xL * r + 25 * SL - 15 * QL)
        repeat (with_reducible (first | exact hS | exact hQ | exact hx | exact hU | exact valAC_ofNat r w _ | apply valAC_add | apply valAC_sub | apply valAC_neg | apply hmul))
      · change ValAC r w (30 * (U_C - 1) * ιC_K5 S_K) (30 * (r - 1) * SL)
        repeat (with_reducible (first | exact hS | exact hU | exact valAC_one r w | exact valAC_ofNat r w _ | apply valAC_sub | apply hmul))
      · exact valAC_zero r w
      · change ValAC r w (18 * U_C * ιC_K5 S_K) (18 * r * SL)
        exact hmul (hmul (valAC_ofNat r w 18) hU) hS
      · exact valAC_zero r w
      · omega
    have homY (k : Fin 5) : ValAC r w
        (match k with
         | 2 => -25 * ιC_K5 T_K * V_C + 9 * ιC_K5 y_K * V_C + 25 * ιC_K5 T_K + 15 * V_C - 15
         | 4 => 18 * V_C * ιC_K5 T_K
         | _ => 0)
        (match k with
         | 2 => -25 * TL * (w / r) + 9 * yL * (w / r) + 25 * TL + 15 * (w / r) - 15
         | 4 => 18 * (w / r) * TL
         | _ => 0) := by
      rcases k with ⟨_ | _ | _ | _ | _ | k, hk⟩
      · exact valAC_zero r w
      · exact valAC_zero r w
      · change ValAC r w (-25 * ιC_K5 T_K * V_C + 9 * ιC_K5 y_K * V_C + 25 * ιC_K5 T_K + 15 * V_C - 15)
            (-25 * TL * (w / r) + 9 * yL * (w / r) + 25 * TL + 15 * (w / r) - 15)
        repeat (with_reducible (first | exact hT | exact hy | exact hV | exact valAC_ofNat r w _ | apply valAC_add | apply valAC_sub | apply valAC_neg | apply hmul))
      · exact valAC_zero r w
      · change ValAC r w (18 * V_C * ιC_K5 T_K) (18 * (w / r) * TL)
        exact hmul (hmul (valAC_ofNat r w 18) hV) hT
      · omega
    exact hmul (hdivn (valAC_one r w) 81) (valAC_sub (hmul (homX i) (homY j)) (hmul (homX j) (homY i)))
  have hA1 : ValAC r w (A1_of (ιC_K5 S_K) (ιC_K5 Q_K) U_C V_C) (A1_of SL QL r (w / r)) := by
    dsimp only [A1_of]
    repeat (with_reducible (first | exact hS | exact hQ | exact hU | exact hV | exact valAC_one r w | exact valAC_ofNat r w _ | apply hdivn | apply valAC_sub | apply hmul | apply hpow))
  have hB1 : ValAC r w (B1_of (ιC_K5 T_K) U_C V_C) (B1_of TL r (w / r)) := by
    dsimp only [B1_of]
    repeat (with_reducible (first | exact hT | exact hU | exact hV | exact valAC_one r w | exact valAC_ofNat r w _ | apply hdivn | apply valAC_sub | apply hmul | apply hpow))
  have hdA1 (k : Fin 3) : ValAC r w (dA1_fn k (ιC_K5 S_K) (ιC_K5 Q_K) U_C V_C) (dA1_fn k SL QL r (w / r)) := by
    fin_cases k <;> dsimp only [dA1_fn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      repeat (with_reducible (first | exact hS | exact hQ | exact hU | exact hV | exact valAC_zero r w | exact valAC_one r w | exact valAC_ofNat r w _ | apply hdivn | apply valAC_add | apply valAC_sub | apply valAC_neg | apply hmul | apply hpow))
  have hQY : ValAC r w (dot_ab (QY_num (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) U_C V_C) aC bC)
      (dot_ab (QY_num SL QL TL xL yL r (w / r)) aL bL) :=
    hdot _ _ (fun i => hmul hDY2 (valAC_sub
      (hmul hDX2 (hFc _ _ (fun p q => hmul (hmul hS hT) (hom p q)) i))
      (hFc _ _ (fun p q => hmul (hmul hS hT) (valAC_sub (hmul (hdDX2 p) (hbr q)) (hmul (hdDX2 q) (hbr p)))) i)))
  have hQX : ValAC r w (dot_ab (QX_num (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) U_C V_C) aC bC)
      (dot_ab (QX_num SL QL TL xL yL r (w / r)) aL bL) :=
    hdot _ _ (fun i => hmul hDX2 (valAC_add
      (hmul (valAC_neg hDY2) (hFc _ _ (fun p q => hmul (hmul hS hT) (hom p q)) i))
      (hFc _ _ (fun p q => hmul (hmul hS hT) (valAC_sub (hmul (hdDY2 p) (hbr q)) (hmul (hdDY2 q) (hbr p)))) i)))
  have hcA1 : ValAC r w (cA1_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) aC bC U_C V_C)
      (cA1_of SL QL TL aL bL r (w / r)) := by
    dsimp only [cA1_of]
    repeat (with_reducible (first | exact hH0 | exact hA1 | exact ha | exact hb | exact hdA1 _ | exact hdH0 _ | apply valAC_add | apply valAC_sub | apply hmul))
  have hEB : ValAC r w (EB_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) U_C V_C)
      (EB_of SL QL TL xL yL r (w / r)) := by
    dsimp only [EB_of]
    repeat (with_reducible (first | exact hW2 | exact hdF5 _ | exact hbr _ | exact valAC_ofNat r w _ | apply valAC_sub | apply hmul))
  have hqY := valAC_div_of_reg hW hQY hv (regAC_div_v_of hQY.reg hnmWU) hv_ne
  have hqX := valAC_div_of_reg hW hQX hu (regAC_div_u_of hQX.reg hr1) hu_ne
  have hcA1_v := valAC_div_of_reg hW hcA1 hv (regAC_div_v_of hcA1.reg hnmWU) hv_ne
  unfold P18_z_AC P18_of
  exact valAC_add (hmul hM0 (valAC_add (valAC_add
    (hmul (hmul hH0 hA1) hqY) (hmul (hmul hH0 hB1) hqX)) (hmul hcA1_v hEB)))
    (hmul (valAC_add (hmul hAY hqY) (hmul hAX hqX)) (hpow hH0 2))

private lemma valAC_interp4 {r w : CoverL}
    (hW : w ^ 2 + (k5Params.bW.map ιL_K5).eval r * w + (k5Params.cW.map ιL_K5).eval r = 0)
    {f : A_C → A_C} {g : CoverL → CoverL}
    (hf : ∀ {z : A_C} {vz : CoverL}, ValAC r w z vz → ValAC r w (f z) (g vz)) :
    let p := interp4 f; let q := interp4 g
    ValAC r w p.1 q.1 ∧ ValAC r w p.2.1 q.2.1 ∧ ValAC r w p.2.2.1 q.2.2.1 ∧
    ValAC r w p.2.2.2.1 q.2.2.2.1 ∧ ValAC r w p.2.2.2.2 q.2.2.2.2 := by
  have h0 := hf (valAC_zero r w)
  have h1 := hf (valAC_one r w)
  have hm1 := hf (valAC_neg (valAC_one r w))
  have h2 := hf (valAC_ofNat r w 2)
  have hm2 := hf (valAC_neg (valAC_ofNat r w 2))
  have hmul {x y : A_C} {vx vy : CoverL} := @valAC_mul r w hW x y vx vy
  have hdivn {x : A_C} {vx : CoverL} (hx : ValAC r w x vx) (n : ℕ) [n.AtLeastTwo] := valAC_div_nat hW hx n
  dsimp only [interp4]
  refine ⟨?_, ?_, ?_, ?_, h0⟩
  · exact hdivn (valAC_add (valAC_add (hmul (valAC_neg (valAC_ofNat r w 4)) (valAC_add h1 hm1))
      (valAC_add h2 hm2)) (hmul (valAC_ofNat r w 6) h0)) 24
  · exact hdivn (valAC_add (hmul (valAC_neg (valAC_ofNat r w 2)) (valAC_sub h1 hm1))
      (valAC_sub h2 hm2)) 12
  · exact hdivn (valAC_sub (valAC_sub (hmul (valAC_ofNat r w 16) (valAC_add h1 hm1))
      (valAC_add h2 hm2)) (hmul (valAC_ofNat r w 30) h0)) 24
  · exact hdivn (valAC_sub (hmul (valAC_ofNat r w 8) (valAC_sub h1 hm1))
      (valAC_sub h2 hm2)) 12

private lemma valAC_remDeg4 {r w : CoverL}
    (hW : w ^ 2 + (k5Params.bW.map ιL_K5).eval r * w + (k5Params.cW.map ιL_K5).eval r = 0)
    {q2 q1 q0 p4 p3 p2 p1 p0 : A_C} {vq2 vq1 vq0 vp4 vp3 vp2 vp1 vp0 : CoverL}
    (hq2 : ValAC r w q2 vq2) (hq1 : ValAC r w q1 vq1) (hq0 : ValAC r w q0 vq0)
    (hp4 : ValAC r w p4 vp4) (hp3 : ValAC r w p3 vp3) (hp2 : ValAC r w p2 vp2)
    (hp1 : ValAC r w p1 vp1) (hp0 : ValAC r w p0 vp0) :
    ValAC r w (remDeg4_P1 q2 q1 q0 p4 p3 p2 p1) (remDeg4_P1 vq2 vq1 vq0 vp4 vp3 vp2 vp1) ∧
    ValAC r w (remDeg4_P0 q2 q1 q0 p4 p3 p2 p0) (remDeg4_P0 vq2 vq1 vq0 vp4 vp3 vp2 vp0) := by
  have hmul {x y : A_C} {vx vy : CoverL} := @valAC_mul r w hW x y vx vy
  have hpow {x : A_C} {vx : CoverL} := @valAC_pow r w hW x vx
  have hr3 := valAC_sub (hmul hq2 hp3) (hmul hq1 hp4)
  have hr2 := valAC_sub (hmul hq2 hp2) (hmul hq0 hp4)
  have hs2 := valAC_sub (hmul hq2 hr2) (hmul hq1 hr3)
  have hs1 := valAC_sub (hmul (hpow hq2 2) hp1) (hmul hq0 hr3)
  exact ⟨valAC_sub (hmul hq2 hs1) (hmul hq1 hs2),
         valAC_sub (hmul (hpow hq2 3) hp0) (hmul hq0 hs2)⟩

end BranchEval

/-- **Main Pointwise Sheet Extraction & Residue Identity on `R_{34}`**:
At every `r ∈ R34`, there is a unique nondegenerate sheet `(a, b, r, V) ∈ CoverL^4`
solving `E_0 = E_1 = E_2 = E_3 = 0` with `J_fib.det ≠ 0` and `M_abSQ.det ≠ 0`, and the
simple-pole residue of `eta_L` at `r` equals `-P18_of ... / (81 * (J_fib ...).det)`. -/
theorem residue_eta_L_at_R34 (r : CoverL) (hr : r ∈ R34) :
    ∃ a b V : CoverL,
      (∀ k : Fin 4, E_fn k SL QL TL a b r V = 0) ∧
      r ≠ 0 ∧ V ≠ 0 ∧ r ≠ 1 ∧ V ≠ 1 ∧
      (J_fib SL QL TL a b r V).det ≠ 0 ∧
      (M_abSQ SL QL TL a b r V).det ≠ 0 ∧
      CrossedRationalResidue.residue r eta_L =
        -P18_of SL QL TL xL yL a b r V / (81 * (J_fib SL QL TL a b r V).det) := by
  have hrP34 : (P34_K5.map ιL_K5).eval r = 0 := mem_R34_iff.mp hr
  -- 1. All 11 coprimality nonvanishings at `r ∈ R34`.
  have hr0 : r ≠ 0 := by simpa using eval_ne_zero_of_isCoprime isCoprime_P34_X hrP34
  have hr1 : r ≠ 1 := by
    have h := eval_ne_zero_of_isCoprime isCoprime_P34_X_sub_1 hrP34
    simpa [sub_eq_zero] using h
  have hQ5 : pU ιL_K5 k5Params.Q5_z r ≠ 0 := eval_ne_zero_of_isCoprime isCoprime_P34_Q5 hrP34
  have hcb : pU ιL_K5 k5Params.cb_h r ≠ 0 := eval_ne_zero_of_isCoprime isCoprime_P34_cb_h hrP34
  have hnmWU : pU ιL_K5 k5Params.nm_WU r ≠ 0 := eval_ne_zero_of_isCoprime isCoprime_P34_nm_WU hrP34
  have hnmd1 : pU ιL_K5 (k5Params.pnm k5Params.d1_z) r ≠ 0 :=
    eval_ne_zero_of_isCoprime isCoprime_P34_nm_d1_z hrP34
  have hnmdiscE2 : pU ιL_K5 (k5Params.pnm k5Params.disc_E2z) r ≠ 0 :=
    eval_ne_zero_of_isCoprime isCoprime_P34_nm_disc_E2z hrP34
  have hnmdetM : pU ιL_K5 (k5Params.pnm k5Params.detM_W) r ≠ 0 :=
    eval_ne_zero_of_isCoprime isCoprime_P34_nm_detM_W hrP34
  have hP34d : (P34_K5.derivative.map ιL_K5).eval r ≠ 0 :=
    eval_ne_zero_of_isCoprime isCoprime_P34_P34_deriv hrP34
  have hcbm : (cb_h_m_K5.map ιL_K5).eval r ≠ 0 := by
    have h := congrArg (fun f : K5[X] => (f.map ιL_K5).eval r) cb_h_K5_eq_mul_monic
    simp only [Polynomial.map_mul, Polynomial.map_C, eval_mul, eval_C] at h
    have hcb' : (k5Params.cb_h.map ιL_K5).eval r ≠ 0 := hcb
    rw [h] at hcb'
    exact right_ne_zero_of_mul hcb'
  have hnmz0 : (k5Params.nm_z.map ιL_K5).eval r = 0 := by
    rw [nm_z_K5_factor]
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
      eval_mul, eval_pow, eval_C, eval_X, hrP34, mul_zero]
  have hnmzd : (k5Params.nm_z.map ιL_K5).derivative.eval r ≠ 0 := by
    rw [nm_z_K5_factor]
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
      derivative_mul, eval_add, eval_mul, eval_pow, eval_C, eval_X, hrP34, mul_zero, zero_add,
      Polynomial.derivative_map]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero
      ((map_ne_zero_iff ιL_K5 ιL_K5.injective).mpr lc34_K5_ne_zero)
      (pow_ne_zero 15 hr0)) (pow_ne_zero 12 hcbm)) hP34d
  -- 2. Split fiber `E0` at `r` into distinct roots `w1 ≠ w2`, lift to `Dual CoverL`, select unique branch!
  obtain ⟨w1, w2, hw_sum, hw_prod, hw_sep⟩ := E0_splits_at_R34 r hr
  have h2w1 : 2 * w1 + pU ιL_K5 k5Params.bW r ≠ 0 := by
    have : 2 * w1 + pU ιL_K5 k5Params.bW r = w1 - w2 := by linear_combination hw_sum
    rw [this]; exact sub_ne_zero.mpr hw_sep
  have h2w2 : 2 * w2 + pU ιL_K5 k5Params.bW r ≠ 0 := by
    have : 2 * w2 + pU ιL_K5 k5Params.bW r = w2 - w1 := by linear_combination hw_sum
    rw [this]; exact sub_ne_zero.mpr hw_sep.symm
  set w1' : CoverL := -(pU_d ιL_K5 k5Params.bW r * w1 + pU_d ιL_K5 k5Params.cW r) /
    (2 * w1 + pU ιL_K5 k5Params.bW r)
  set w2' : CoverL := -(pU_d ιL_K5 k5Params.bW r * w2 + pU_d ιL_K5 k5Params.cW r) /
    (2 * w2 + pU ιL_K5 k5Params.bW r)
  have hW12_sum : (⟨w1, w1'⟩ : Dual CoverL) + ⟨w2, w2'⟩ = -pU_D ιL_K5 k5Params.bW r := by
    rw [pU_D_eq]
    ext
    · exact hw_sum
    · simp only [Dual.add_eps, Dual.neg_eps]
      have h1 : 2 * w1 + pU ιL_K5 k5Params.bW r = w1 - w2 := by linear_combination hw_sum
      have h2 : 2 * w2 + pU ιL_K5 k5Params.bW r = -(w1 - w2) := by linear_combination hw_sum
      dsimp only [w1', w2']; rw [h1, h2]
      have hne := sub_ne_zero.mpr hw_sep
      field_simp [hne]; ring
  have hW12_prod : (⟨w1, w1'⟩ : Dual CoverL) * ⟨w2, w2'⟩ = pU_D ιL_K5 k5Params.cW r := by
    rw [pU_D_eq]
    ext
    · exact hw_prod
    · simp only [Dual.mul_eps]
      have h1 : 2 * w1 + pU ιL_K5 k5Params.bW r = w1 - w2 := by linear_combination hw_sum
      have h2 : 2 * w2 + pU ιL_K5 k5Params.bW r = -(w1 - w2) := by linear_combination hw_sum
      dsimp only [w1', w2']; rw [h1, h2]
      have hne := sub_ne_zero.mpr hw_sep
      field_simp [hne]; ring
  have hres_nm_D : pUW_D ιL_K5 k5Params.res_z r w1 w1' * pUW_D ιL_K5 k5Params.res_z r w2 w2' =
      pU_D ιL_K5 k5Params.nm_z r := by
    let fD := Polynomial.eval₂RingHom (Dual.C.comp ιL_K5) (⟨r, 1⟩ : Dual CoverL)
    have hnm := PairAlg.evalAt_nm (fD k5Params.bW) (fD k5Params.cW)
      ⟨w1, w1'⟩ ⟨w2, w2'⟩ hW12_sum hW12_prod (PairAlg.map fD k5Params.res_z)
    rw [← PairAlg.map_nm] at hnm
    exact hnm.symm
  have hres_nm_val : pUW ιL_K5 k5Params.res_z r w1 * pUW ιL_K5 k5Params.res_z r w2 = 0 := by
    have h := congrArg Dual.val hres_nm_D
    simp only [Dual.mul_val, pUW_D_val, pU_D_eq] at h
    exact h.trans hnmz0
  have hres_nm_eps : pUW ιL_K5 k5Params.res_z r w1 * (pUW_D ιL_K5 k5Params.res_z r w2 w2').eps +
      (pUW_D ιL_K5 k5Params.res_z r w1 w1').eps * pUW ιL_K5 k5Params.res_z r w2 =
      (k5Params.nm_z.map ιL_K5).derivative.eval r := by
    have h := congrArg Dual.eps hres_nm_D
    simp only [Dual.mul_eps, pUW_D_val, pU_D_eq, pU_d] at h
    rw [Polynomial.derivative_map]
    exact h
  -- Select the unique branch `(w, w', w_c, w_c')` where `res_z(r, w) = 0`!
  have hbranch : ∃ w w' w_c w_c' : CoverL,
      (⟨w, w'⟩ : Dual CoverL) + ⟨w_c, w_c'⟩ = -pU_D ιL_K5 k5Params.bW r ∧
      (⟨w, w'⟩ : Dual CoverL) * ⟨w_c, w_c'⟩ = pU_D ιL_K5 k5Params.cW r ∧
      w ≠ w_c ∧
      pUW ιL_K5 k5Params.res_z r w = 0 ∧
      pUW ιL_K5 k5Params.res_z r w_c ≠ 0 ∧
      (pUW_D ιL_K5 k5Params.res_z r w w').eps * pUW ιL_K5 k5Params.res_z r w_c =
        (k5Params.nm_z.map ιL_K5).derivative.eval r := by
    rcases mul_eq_zero.mp hres_nm_val with h1 | h2
    · refine ⟨w1, w1', w2, w2', hW12_sum, hW12_prod, hw_sep, h1, ?_, ?_⟩
      · intro hc; rw [h1, hc, zero_mul, mul_zero, add_zero] at hres_nm_eps; exact hnmzd hres_nm_eps.symm
      · rw [h1, zero_mul, zero_add] at hres_nm_eps; exact hres_nm_eps
    · refine ⟨w2, w2', w1, w1', by rw [add_comm]; exact hW12_sum, by rw [mul_comm]; exact hW12_prod,
        hw_sep.symm, h2, ?_, ?_⟩
      · intro hc; rw [h2, hc, zero_mul, mul_zero, add_zero] at hres_nm_eps; exact hnmzd hres_nm_eps.symm
      · rw [h2, mul_zero, add_zero, mul_comm] at hres_nm_eps; exact hres_nm_eps
  obtain ⟨w, w', w_c, w_c', hW_sum_D, hW_prod_D, hw_sep_c, hres0, hresc, hres_eps_prod⟩ := hbranch
  have hWD : (⟨w, w'⟩ : Dual CoverL) ^ 2 + pU_D ιL_K5 k5Params.bW r * ⟨w, w'⟩ + pU_D ιL_K5 k5Params.cW r = 0 := by
    linear_combination (⟨w, w'⟩ : Dual CoverL) * hW_sum_D - hW_prod_D
  have hW_eq : w ^ 2 + pU ιL_K5 k5Params.bW r * w + pU ιL_K5 k5Params.cW r = 0 := by
    have h := congrArg Dual.val hWD
    simp only [Dual.pow_eq, Dual.add_val, Dual.mul_val, pU_D_eq, Dual.zero_val] at h
    exact h
  have hW_sum : w + w_c = -pU ιL_K5 k5Params.bW r := by
    have h := congrArg Dual.val hW_sum_D; simpa only [Dual.add_val, Dual.neg_val, pU_D_eq] using h
  have hW_prod : w * w_c = pU ιL_K5 k5Params.cW r := by
    have h := congrArg Dual.val hW_prod_D; simpa only [Dual.mul_val, pU_D_eq] using h
  -- Nonvanishings on the chosen branch `(r, w)`.
  have hnm_eval (x : PairAlg K5[X]) (h : pU ιL_K5 (k5Params.pnm x) r ≠ 0) : pUW ιL_K5 x r w ≠ 0 := by
    let fL := (Polynomial.evalRingHom r).comp (Polynomial.mapRingHom ιL_K5)
    have hfac := PairAlg.evalAt_nm (fL k5Params.bW) (fL k5Params.cW) w w_c hW_sum hW_prod (PairAlg.map fL x)
    rw [← PairAlg.map_nm] at hfac
    have h' : fL (PairAlg.nm k5Params.bW k5Params.cW x) ≠ 0 := h
    rw [hfac] at h'
    exact left_ne_zero_of_mul h'
  have hw_ne : w ≠ 0 := by
    have hcW_ne : pU ιL_K5 k5Params.cW r ≠ 0 := cW_eval_ne_zero hr0
    rw [← hW_prod] at hcW_ne
    exact left_ne_zero_of_mul hcW_ne
  have hV_ne : w / r ≠ 0 := div_ne_zero hw_ne hr0
  have hV1 : w / r ≠ 1 := by
    intro h1
    have hwr : w = r := (div_eq_one_iff_eq hr0).mp h1
    have h0 : pU ιL_K5 k5Params.nm_WU r = 0 := by
      simp only [pU, CoverParams.nm_WU, CoverParams.pnm, PairAlg.nm, Polynomial.map_add,
        Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg,
        Polynomial.map_X, Polynomial.map_one, eval_add, eval_sub, eval_mul, eval_pow,
        eval_neg, eval_X, eval_one]
      rw [hwr] at hW_eq; linear_combination hW_eq
    exact hnmWU h0
  have h2w_ne : 2 * w + pU ιL_K5 k5Params.bW r ≠ 0 := by
    have : 2 * w + pU ιL_K5 k5Params.bW r = w - w_c := by linear_combination hW_sum
    rw [this]; exact sub_ne_zero.mpr hw_sep_c
  have hd1_ne : pUW ιL_K5 k5Params.d1_z r w ≠ 0 := hnm_eval k5Params.d1_z hnmd1
  have hdiscE2_ne : pUW ιL_K5 k5Params.disc_E2z r w ≠ 0 := hnm_eval k5Params.disc_E2z hnmdiscE2
  have hdetM_ne : pUW ιL_K5 k5Params.detM_W r w ≠ 0 := hnm_eval k5Params.detM_W hnmdetM
  have hres_eps_ne : (pUW_D ιL_K5 k5Params.res_z r w w').eps ≠ 0 :=
    left_ne_zero_of_mul (hres_eps_prod.symm ▸ hnmzd)
  -- 3. Construct the sheet `(a_r, b_r, r, w / r)` and verify `E_0 = E_1 = E_2 = E_3 = 0`!
  set d2_2 := pUW ιL_K5 k5Params.d2_2 r w
  set d2_1 := pUW ιL_K5 k5Params.d2_1 r w
  set d2_0 := pUW ιL_K5 k5Params.d2_0 r w
  set d3_3 := pUW ιL_K5 k5Params.d3_3 r w
  set d3_2 := pUW ιL_K5 k5Params.d3_2 r w
  set d3_1 := pUW ιL_K5 k5Params.d3_1 r w
  set d3_0 := pUW ιL_K5 k5Params.d3_0 r w
  set d1_r := pUW ιL_K5 k5Params.d1_z r w
  set d0_r := pUW ιL_K5 k5Params.d0_z r w
  have hd2_2_eq : d2_2 = pU ιL_K5 k5Params.Q5_z r := by
    simp [d2_2, pUW, CoverParams.d2_2, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar, pU]
  have hd2_2_ne : d2_2 ≠ 0 := hd2_2_eq.symm ▸ hQ5
  have hd1_rem : d1_r = remDeg3_d1 d2_2 d2_1 d2_0 d3_3 d3_2 d3_1 := by
    have hmul := PairAlg.evalAt_mul (eval r (map ιL_K5 k5Params.bW)) (eval r (map ιL_K5 k5Params.cW)) w hW_eq
    simp only [d1_r, CoverParams.d1_z, remDeg3_d1, pUW, CoverParams.pmul, PairAlg.map_sub,
      PairAlg.map_mul, PairAlg.evalAt_sub, RingHom.comp_apply, Polynomial.coe_evalRingHom,
      Polynomial.coe_mapRingHom, hmul]
    rfl
  have hd0_rem : d0_r = remDeg3_d0 d2_2 d2_1 d2_0 d3_3 d3_2 d3_0 := by
    have hmul := PairAlg.evalAt_mul (eval r (map ιL_K5 k5Params.bW)) (eval r (map ιL_K5 k5Params.cW)) w hW_eq
    simp only [d0_r, CoverParams.d0_z, remDeg3_d0, pUW, CoverParams.pmul, PairAlg.map_sub,
      PairAlg.map_mul, PairAlg.evalAt_sub, RingHom.comp_apply, Polynomial.coe_evalRingHom,
      Polynomial.coe_mapRingHom, hmul]
    rfl
  have hres_syl5 : pUW ιL_K5 k5Params.res_z r w = syl5 d2_2 d2_1 d2_0 d3_3 d3_2 d3_1 d3_0 := by
    simp only [pUW, CoverParams.res_z, map_syl5Pair, RingHom.comp_apply, Polynomial.coe_evalRingHom,
      Polynomial.coe_mapRingHom]
    exact evalAt_syl5Pair _ _ _ _ _ _ _ _ _ w hW_eq
  set z_r : CoverL := -d0_r / d1_r
  have hE2_zr : d2_2 * z_r ^ 2 + d2_1 * z_r + d2_0 = 0 := by
    have hqs := q2_sq_mul_syl5 d2_2 d2_1 d2_0 d3_3 d3_2 d3_1 d3_0
    rw [← hres_syl5, hres0, mul_zero] at hqs
    dsimp only at hqs
    change 0 = d2_2 * (remDeg3_d0 d2_2 d2_1 d2_0 d3_3 d3_2 d3_0) ^ 2 -
      remDeg3_d0 d2_2 d2_1 d2_0 d3_3 d3_2 d3_0 * remDeg3_d1 d2_2 d2_1 d2_0 d3_3 d3_2 d3_1 * d2_1 +
      remDeg3_d1 d2_2 d2_1 d2_0 d3_3 d3_2 d3_1 ^ 2 * d2_0 at hqs
    rw [← hd1_rem, ← hd0_rem] at hqs
    apply mul_left_cancel₀ (pow_ne_zero 2 hd1_ne)
    dsimp only [z_r]; field_simp [hd1_ne]; linear_combination -hqs
  have hE3_zr : d3_3 * z_r ^ 3 + d3_2 * z_r ^ 2 + d3_1 * z_r + d3_0 = 0 := by
    have hrem := remDeg3_eq d2_2 d2_1 d2_0 d3_3 d3_2 d3_1 d3_0 z_r
    rw [hE2_zr, ← hd1_rem, ← hd0_rem, mul_zero, zero_add] at hrem
    have hlin : d1_r * z_r + d0_r = 0 := by dsimp only [z_r]; field_simp [hd1_ne]; ring
    rw [hlin] at hrem
    exact (mul_eq_zero.mp hrem).resolve_left (pow_ne_zero 2 hd2_2_ne)
  set a_r : CoverL := z_r / w
  set b_r : CoverL := -(pU ιL_K5 k5Params.ca_h r * z_r + pUW ιL_K5 k5Params.c0W r w) /
    (w * pU ιL_K5 k5Params.cb_h r)
  set V_r : CoverL := w / r
  have hE_all : ∀ k : Fin 4, E_fn k SL QL TL a_r b_r r V_r = 0 := by
    intro k; fin_cases k
    · have h0 := E0_of_cover ιL_K5 r w hr0
      rw [hW_eq, mul_zero] at h0
      exact (mul_eq_zero.mp h0).resolve_left hr0
    · have h1 := E1_of_cover ιL_K5 a_r b_r r w hr0 hW_eq
      have hrhs : pU ιL_K5 k5Params.ca_h r * (w * a_r) + pU ιL_K5 k5Params.cb_h r * (w * b_r) +
          pUW ιL_K5 k5Params.c0W r w = 0 := by
        dsimp only [a_r, b_r]; field_simp [hw_ne, hcb]; ring
      rw [hrhs] at h1
      exact (mul_eq_zero.mp h1).resolve_left hr0
    · have h2 := E2_z_of_cover ιL_K5 z_r r w hr0 hw_ne hcb hW_eq
      dsimp only at h2
      change r * w * pU ιL_K5 k5Params.cb_h r ^ 2 * E_fn 2 SL QL TL a_r b_r r V_r =
        d2_2 * z_r ^ 2 + d2_1 * z_r + d2_0 at h2
      rw [hE2_zr] at h2
      exact (mul_eq_zero.mp h2).resolve_left (mul_ne_zero (mul_ne_zero hr0 hw_ne) (pow_ne_zero 2 hcb))
    · have h3 := E3_z_of_cover ιL_K5 z_r r w hr0 hw_ne hcb hW_eq
      dsimp only at h3
      change r * w ^ 2 * pU ιL_K5 k5Params.cb_h r ^ 3 * E_fn 3 SL QL TL a_r b_r r V_r =
        d3_3 * z_r ^ 3 + d3_2 * z_r ^ 2 + d3_1 * z_r + d3_0 at h3
      rw [hE3_zr] at h3
      exact (mul_eq_zero.mp h3).resolve_left (mul_ne_zero (mul_ne_zero hr0 (pow_ne_zero 2 hw_ne)) (pow_ne_zero 3 hcb))
  -- 4. Compute `(M_abSQ ...).det ≠ 0` directly from `detM_W_of_cover`!
  have hM_ne : (M_abSQ SL QL TL a_r b_r r V_r).det ≠ 0 := by
    have hdet := detM_W_of_cover ιL_K5 r w hr0 hw_ne hcb hd1_ne hW_eq
    dsimp only at hdet
    rw [hdet]
    have hCc_ne : pUW ιL_K5 k5Params.C_sub r w ≠ 0 := by
      have hCc : pUW ιL_K5 k5Params.C_sub r w = w * pU ιL_K5 k5Params.cb_h r * d1_r := by
        simp only [pUW, CoverParams.C_sub, CoverParams.pmul, PairAlg.map_mul, PairAlg.map_smul,
          PairAlg.map_W, RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.coe_mapRingHom]
        rw [PairAlg.evalAt_mul (pU ιL_K5 k5Params.bW r) (pU ιL_K5 k5Params.cW r) w hW_eq,
          PairAlg.evalAt_W, PairAlg.evalAt_smul]
        change w * (pU ιL_K5 k5Params.cb_h r * d1_r) = _
        ring
      rw [hCc]; exact mul_ne_zero (mul_ne_zero hw_ne hcb) hd1_ne
    exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 4 (div_ne_zero hV_ne (pow_ne_zero 2 hCc_ne)))) hdetM_ne
  -- 5. Compute `(J_fib SL QL TL a_r b_r r V_r).det` via `Dual CoverL` + `det_J_fib_schur` + `syl5_eq_prod_roots`!
  set D22 := pUW_D ιL_K5 k5Params.d2_2 r w w'
  set D21 := pUW_D ιL_K5 k5Params.d2_1 r w w'
  set D20 := pUW_D ιL_K5 k5Params.d2_0 r w w'
  set D33 := pUW_D ιL_K5 k5Params.d3_3 r w w'
  set D32 := pUW_D ιL_K5 k5Params.d3_2 r w w'
  set D31 := pUW_D ιL_K5 k5Params.d3_1 r w w'
  set D30 := pUW_D ιL_K5 k5Params.d3_0 r w w'
  have h2dz_ne : 2 * d2_2 * z_r + d2_1 ≠ 0 := by
    have hsq : (2 * d2_2 * z_r + d2_1) ^ 2 = pUW ιL_K5 k5Params.disc_E2z r w := by
      have hdisc : pUW ιL_K5 k5Params.disc_E2z r w = d2_1 ^ 2 - 4 * d2_2 * d2_0 := by
        simp only [pUW, CoverParams.disc_E2z, CoverParams.pmul, PairAlg.map_sub, PairAlg.map_smul,
          PairAlg.map_mul, PairAlg.evalAt_sub, PairAlg.evalAt_smul, RingHom.comp_apply,
          Polynomial.coe_evalRingHom, Polynomial.coe_mapRingHom, Polynomial.map_ofNat, eval_ofNat]
        simp only [PairAlg.evalAt_mul _ _ w hW_eq]; ring
      rw [hdisc]; linear_combination 4 * d2_2 * hE2_zr
    intro h0; rw [h0, zero_pow (by omega)] at hsq; exact hdiscE2_ne hsq.symm
  set z_r' : CoverL := -(D22.eps * z_r ^ 2 + D21.eps * z_r + D20.eps) / (2 * d2_2 * z_r + d2_1)
  set Z_D : Dual CoverL := ⟨z_r, z_r'⟩
  have hD2_Z : D22 * Z_D ^ 2 + D21 * Z_D + D20 = 0 := by
    ext
    · simp only [Dual.add_val, Dual.mul_val, Dual.pow_eq, Dual.zero_val, D22, D21, D20, pUW_D_val]
      exact hE2_zr
    · simp only [Dual.add_eps, Dual.mul_eps, Dual.pow_eq, Dual.zero_eps, D22, D21, D20, pUW_D_val,
        Z_D, Nat.cast_ofNat, Nat.reduceSub, pow_one]
      change d2_2 * (2 * z_r * z_r') + D22.eps * z_r ^ 2 + (d2_1 * z_r' + D21.eps * z_r) + D20.eps = 0
      have hz' : (2 * d2_2 * z_r + d2_1) * z_r' = -(D22.eps * z_r ^ 2 + D21.eps * z_r + D20.eps) :=
        mul_div_cancel₀ _ h2dz_ne
      linear_combination hz'
  set W_D : Dual CoverL := ⟨w, w'⟩
  set cb_D : Dual CoverL := pU_D ιL_K5 k5Params.cb_h r
  set ca_D : Dual CoverL := pU_D ιL_K5 k5Params.ca_h r
  set c0W_D : Dual CoverL := pUW_D ιL_K5 k5Params.c0W r w w'
  have hW_D_val : W_D.val ≠ 0 := hw_ne
  have hcb_D_val : cb_D.val ≠ 0 := by simpa [cb_D, pU_D_eq] using hcb
  set A_D : Dual CoverL := Z_D * Dual.invOfNe W_D hW_D_val
  set B_D : Dual CoverL := -(ca_D * Z_D + c0W_D) * Dual.invOfNe (W_D * cb_D) (mul_ne_zero hW_D_val hcb_D_val)
  have hA_val : A_D.val = a_r := by simp [A_D, Z_D, W_D, Dual.invOfNe, a_r, div_eq_mul_inv]
  have hB_val : B_D.val = b_r := by
    simp [B_D, Z_D, W_D, Dual.invOfNe, b_r, ca_D, cb_D, c0W_D, pU_D_eq, pUW_D_val, div_eq_mul_inv]; ring
  set a_r' : CoverL := A_D.eps
  set b_r' : CoverL := B_D.eps
  have hA_eq : (⟨a_r, a_r'⟩ : Dual CoverL) = A_D := by ext <;> simp [hA_val, a_r']
  have hB_eq : (⟨b_r, b_r'⟩ : Dual CoverL) = B_D := by ext <;> simp [hB_val, b_r']
  have hWA_D : W_D * A_D = Z_D := by
    dsimp only [A_D]; rw [mul_comm Z_D, ← mul_assoc, Dual.mul_invOfNe, one_mul]
  have hcbWB_D : cb_D * (W_D * B_D) = -(ca_D * Z_D + c0W_D) := by
    dsimp only [B_D]
    calc cb_D * (W_D * (-(ca_D * Z_D + c0W_D) * Dual.invOfNe (W_D * cb_D) (mul_ne_zero hW_D_val hcb_D_val)))
        = -(ca_D * Z_D + c0W_D) * ((W_D * cb_D) * Dual.invOfNe (W_D * cb_D) (mul_ne_zero hW_D_val hcb_D_val)) := by ring
      _ = -(ca_D * Z_D + c0W_D) := by rw [Dual.mul_invOfNe, mul_one]
  set V_r' : CoverL := (w' * r - w) / r ^ 2
  set M : Matrix (Fin 4) (Fin 4) CoverL := J_fib SL QL TL a_r b_r r V_r
  have hM00 : M 0 0 = 0 := rfl
  have hM01 : M 0 1 = 0 := rfl
  have hM0 : M 0 2 + M 0 3 * V_r' = 0 := by
    have h0 := dE0_along ιL_K5 a_r b_r r w w' hr0
    rw [hE_all 0, zero_add, hWD, mul_zero, Dual.zero_eps] at h0
    exact (mul_eq_zero.mp h0).resolve_left hr0
  have hM1 : M 1 0 * a_r' + M 1 1 * b_r' + M 1 2 + M 1 3 * V_r' = 0 := by
    have h1 := dE1_along ιL_K5 a_r b_r r w a_r' b_r' w' hr0
    rw [hE_all 1, zero_add, hA_eq, hB_eq] at h1
    have hc0 := pUW_D_toUW ιL_K5 k5Params.c0_V0 k5Params.c0_V1 k5Params.c0_V2 r w w' hWD
    have hrhs_D : ca_D * (W_D * A_D) + cb_D * (W_D * B_D) +
        (Dual.C (ιL_K5 k5Params.c0_V2) * W_D ^ 2 + Dual.C (ιL_K5 k5Params.c0_V1) * ⟨r, 1⟩ * W_D +
          Dual.C (ιL_K5 k5Params.c0_V0) * ⟨r, 1⟩ ^ 2) = 0 := by
      rw [← hc0]
      change ca_D * (W_D * A_D) + cb_D * (W_D * B_D) + c0W_D = 0
      rw [hWA_D, hcbWB_D]; ring
    have h1_rhs : (ca_D * (W_D * A_D) + cb_D * (W_D * B_D) +
        Dual.C (ιL_K5 k5Params.c0_V2) * W_D ^ 2 + Dual.C (ιL_K5 k5Params.c0_V1) * ⟨r, 1⟩ * W_D +
        Dual.C (ιL_K5 k5Params.c0_V0) * ⟨r, 1⟩ ^ 2) = 0 := by linear_combination hrhs_D
    rw [h1_rhs, Dual.zero_eps] at h1
    exact (mul_eq_zero.mp h1).resolve_left hr0
  have hM2 : M 2 0 * a_r' + M 2 1 * b_r' + M 2 2 + M 2 3 * V_r' = 0 := by
    have h2 := dE2_along ιL_K5 a_r b_r r w a_r' b_r' w' hr0
    rw [hE_all 2, mul_zero, mul_zero, zero_add, zero_add, hA_eq, hB_eq] at h2
    have hk2 : pUW_D ιL_K5 k5Params.k2W r w w' =
        Dual.C (ιL_K5 k5Params.k2_V2) * W_D ^ 2 + Dual.C (ιL_K5 k5Params.k2_V1) * ⟨r, 1⟩ * W_D +
          Dual.C (ιL_K5 k5Params.k2_V0) * ⟨r, 1⟩ ^ 2 :=
      pUW_D_toUW ιL_K5 k5Params.k2_V0 k5Params.k2_V1 k5Params.k2_V2 r w w' hWD
    have h2D : pU_D ιL_K5 2 r = 2 := pU_D_ofNat ιL_K5 2 r
    have hD22_eq : D22 = pU_D ιL_K5 k5Params.q20 r * cb_D ^ 2 -
        pU_D ιL_K5 k5Params.q11 r * ca_D * cb_D + pU_D ιL_K5 k5Params.q02 r * ca_D ^ 2 := by
      simp only [D22, CoverParams.d2_2, CoverParams.Q5_z, pUW_D_ofScalar,
        pU_D_add, pU_D_sub, pU_D_mul, pU_D_pow]; rfl
    have hD21_eq : D21 = (-pU_D ιL_K5 k5Params.q11 r * cb_D + 2 * pU_D ιL_K5 k5Params.q02 r * ca_D) * c0W_D := by
      simp only [D21, CoverParams.d2_1, pUW_D_smul, pU_D_add, pU_D_mul, pU_D_neg, h2D]; rfl
    have hD20_eq : D20 = pU_D ιL_K5 k5Params.q02 r * c0W_D ^ 2 +
        cb_D ^ 2 * (W_D * pUW_D ιL_K5 k5Params.k2W r w w') := by
      simp only [D20, CoverParams.d2_0, pUW_D_add, pUW_D_smul, pUW_D_pmul ιL_K5 _ _ r w w' hWD,
        pUW_D_W, pU_D_pow]
      change pU_D ιL_K5 k5Params.q02 r * (c0W_D * c0W_D) +
        cb_D ^ 2 * (W_D * pUW_D ιL_K5 k5Params.k2W r w w') = _
      ring
    have hcb2_rhs : cb_D ^ 2 *
        (pU_D ιL_K5 k5Params.q20 r * (W_D * A_D) ^ 2 +
          pU_D ιL_K5 k5Params.q11 r * (W_D * A_D) * (W_D * B_D) +
          pU_D ιL_K5 k5Params.q02 r * (W_D * B_D) ^ 2 +
          W_D * (Dual.C (ιL_K5 k5Params.k2_V2) * W_D ^ 2 + Dual.C (ιL_K5 k5Params.k2_V1) * ⟨r, 1⟩ * W_D +
            Dual.C (ιL_K5 k5Params.k2_V0) * ⟨r, 1⟩ ^ 2)) = 0 := by
      rw [← hk2, hWA_D]
      have hcomb : cb_D ^ 2 * (pU_D ιL_K5 k5Params.q20 r * Z_D ^ 2 +
          pU_D ιL_K5 k5Params.q11 r * Z_D * (W_D * B_D) +
          pU_D ιL_K5 k5Params.q02 r * (W_D * B_D) ^ 2 +
          W_D * pUW_D ιL_K5 k5Params.k2W r w w') = D22 * Z_D ^ 2 + D21 * Z_D + D20 := by
        rw [hD22_eq, hD21_eq, hD20_eq]
        linear_combination (pU_D ιL_K5 k5Params.q11 r * Z_D * cb_D +
          pU_D ιL_K5 k5Params.q02 r * (cb_D * (W_D * B_D) - (ca_D * Z_D + c0W_D))) * hcbWB_D
      rw [hcomb, hD2_Z]
    let hcb2_inv := Dual.invOfNe (cb_D ^ 2) (by simp only [Dual.pow_eq]; exact pow_ne_zero 2 hcb_D_val)
    have hrhs0 : pU_D ιL_K5 k5Params.q20 r * (W_D * A_D) ^ 2 +
        pU_D ιL_K5 k5Params.q11 r * (W_D * A_D) * (W_D * B_D) +
        pU_D ιL_K5 k5Params.q02 r * (W_D * B_D) ^ 2 +
        W_D * (Dual.C (ιL_K5 k5Params.k2_V2) * W_D ^ 2 + Dual.C (ιL_K5 k5Params.k2_V1) * ⟨r, 1⟩ * W_D +
          Dual.C (ιL_K5 k5Params.k2_V0) * ⟨r, 1⟩ ^ 2) = 0 := by
      have hmul := congrArg (hcb2_inv * ·) hcb2_rhs
      rw [← mul_assoc, Dual.invOfNe_mul, one_mul, mul_zero] at hmul
      exact hmul
    rw [hrhs0, Dual.zero_eps] at h2
    exact (mul_eq_zero.mp h2).resolve_left (mul_ne_zero hr0 hw_ne)
  set E3_dot : CoverL := M 3 0 * a_r' + M 3 1 * b_r' + M 3 2 + M 3 3 * V_r'
  have hE3_D_eps : (D33 * Z_D ^ 3 + D32 * Z_D ^ 2 + D31 * Z_D + D30).eps =
      r * w ^ 2 * pU ιL_K5 k5Params.cb_h r ^ 3 * E3_dot := by
    have h3 := dE3_along ιL_K5 a_r b_r r w a_r' b_r' w' hr0
    rw [hE_all 3, mul_zero, mul_zero, zero_add, zero_add, hA_eq, hB_eq] at h3
    have hk3 : pUW_D ιL_K5 k5Params.k3W r w w' =
        Dual.C (ιL_K5 k5Params.k3_V2) * W_D ^ 2 + Dual.C (ιL_K5 k5Params.k3_V1) * ⟨r, 1⟩ * W_D +
          Dual.C (ιL_K5 k5Params.k3_V0) * ⟨r, 1⟩ ^ 2 :=
      pUW_D_toUW ιL_K5 k5Params.k3_V0 k5Params.k3_V1 k5Params.k3_V2 r w w' hWD
    have h2D : pU_D ιL_K5 2 r = 2 := pU_D_ofNat ιL_K5 2 r
    have h3D : pU_D ιL_K5 3 r = 3 := pU_D_ofNat ιL_K5 3 r
    have hD33_eq : D33 = pU_D ιL_K5 k5Params.c30 r * cb_D ^ 3 -
        pU_D ιL_K5 k5Params.c21 r * ca_D * cb_D ^ 2 +
        pU_D ιL_K5 k5Params.c12 r * ca_D ^ 2 * cb_D -
        pU_D ιL_K5 k5Params.c03 r * ca_D ^ 3 := by
      simp only [D33, CoverParams.d3_3, CoverParams.Q7_z, pUW_D_ofScalar,
        pU_D_add, pU_D_sub, pU_D_mul, pU_D_pow]; rfl
    have hD32_eq : D32 = (-pU_D ιL_K5 k5Params.c21 r * cb_D ^ 2 +
        2 * pU_D ιL_K5 k5Params.c12 r * ca_D * cb_D -
        3 * pU_D ιL_K5 k5Params.c03 r * ca_D ^ 2) * c0W_D := by
      simp only [D32, CoverParams.d3_2, pUW_D_smul, pU_D_add, pU_D_sub, pU_D_mul, pU_D_neg,
        pU_D_pow, h2D, h3D]; rfl
    have hD31_eq : D31 = (pU_D ιL_K5 k5Params.c12 r * cb_D - 3 * pU_D ιL_K5 k5Params.c03 r * ca_D) * c0W_D ^ 2 := by
      simp only [D31, CoverParams.d3_1, pUW_D_smul, pUW_D_pmul ιL_K5 _ _ r w w' hWD,
        pU_D_sub, pU_D_mul, h3D]
      change (pU_D ιL_K5 k5Params.c12 r * cb_D - 3 * pU_D ιL_K5 k5Params.c03 r * ca_D) * (c0W_D * c0W_D) = _
      ring
    have hD30_eq : D30 = -pU_D ιL_K5 k5Params.c03 r * c0W_D ^ 3 +
        cb_D ^ 3 * (W_D ^ 2 * pUW_D ιL_K5 k5Params.k3W r w w') := by
      simp only [D30, CoverParams.d3_0, pUW_D_add, pUW_D_smul, pUW_D_pmul ιL_K5 _ _ r w w' hWD,
        pUW_D_W, pU_D_neg, pU_D_pow]
      change -pU_D ιL_K5 k5Params.c03 r * (c0W_D * (c0W_D * c0W_D)) +
        cb_D ^ 3 * (W_D * W_D * pUW_D ιL_K5 k5Params.k3W r w w') = _
      ring
    set R3_D : Dual CoverL := pU_D ιL_K5 k5Params.c30 r * (W_D * A_D) ^ 3 +
      pU_D ιL_K5 k5Params.c21 r * (W_D * A_D) ^ 2 * (W_D * B_D) +
      pU_D ιL_K5 k5Params.c12 r * (W_D * A_D) * (W_D * B_D) ^ 2 +
      pU_D ιL_K5 k5Params.c03 r * (W_D * B_D) ^ 3 +
      W_D ^ 2 * (Dual.C (ιL_K5 k5Params.k3_V2) * W_D ^ 2 + Dual.C (ιL_K5 k5Params.k3_V1) * ⟨r, 1⟩ * W_D +
        Dual.C (ιL_K5 k5Params.k3_V0) * ⟨r, 1⟩ ^ 2)
    have hD3_eq : D33 * Z_D ^ 3 + D32 * Z_D ^ 2 + D31 * Z_D + D30 = cb_D ^ 3 * R3_D := by
      dsimp only [R3_D]
      rw [← hk3, hWA_D, hD33_eq, hD32_eq, hD31_eq, hD30_eq]
      set Y := cb_D * (W_D * B_D)
      set Z := -(ca_D * Z_D + c0W_D)
      have hstep : cb_D ^ 3 * (pU_D ιL_K5 k5Params.c30 r * Z_D ^ 3 +
          pU_D ιL_K5 k5Params.c21 r * Z_D ^ 2 * (W_D * B_D) +
          pU_D ιL_K5 k5Params.c12 r * Z_D * (W_D * B_D) ^ 2 +
          pU_D ιL_K5 k5Params.c03 r * (W_D * B_D) ^ 3 +
          W_D ^ 2 * pUW_D ιL_K5 k5Params.k3W r w w') =
          pU_D ιL_K5 k5Params.c30 r * cb_D ^ 3 * Z_D ^ 3 +
          pU_D ιL_K5 k5Params.c21 r * cb_D ^ 2 * Z_D ^ 2 * Y +
          pU_D ιL_K5 k5Params.c12 r * cb_D * Z_D * Y ^ 2 +
          pU_D ιL_K5 k5Params.c03 r * Y ^ 3 +
          cb_D ^ 3 * (W_D ^ 2 * pUW_D ιL_K5 k5Params.k3W r w w') := by dsimp only [Y]; ring
      rw [hstep, show Y = Z from hcbWB_D]; dsimp only [Z]; ring
    have hR3_val : R3_D.val = 0 := by
      have hval := congrArg Dual.val hD3_eq
      simp only [Dual.add_val, Dual.mul_val, Dual.pow_eq, D33, D32, D31, D30, pUW_D_val,
        cb_D, pU_D_eq] at hval
      change d3_3 * z_r ^ 3 + d3_2 * z_r ^ 2 + d3_1 * z_r + d3_0 = pU ιL_K5 k5Params.cb_h r ^ 3 * R3_D.val at hval
      rw [hE3_zr] at hval
      exact (mul_eq_zero.mp hval.symm).resolve_left (pow_ne_zero 3 hcb)
    have heps := congrArg Dual.eps hD3_eq
    rw [Dual.mul_eps, hR3_val, mul_zero, add_zero] at heps
    have hcb3_val : (cb_D ^ 3).val = pU ιL_K5 k5Params.cb_h r ^ 3 := by
      simp [cb_D, Dual.pow_eq, pU_D_eq]
    rw [heps, hcb3_val, ← h3]
    dsimp only [E3_dot, M, J_fib]; ring
  -- Relate `(pUW_D res_z).eps` to `E3_dot` via `syl5_eq_prod_roots` in `Dual CoverL`!
  have hres_eps_eq : (pUW_D ιL_K5 k5Params.res_z r w w').eps =
      -d1_r * (2 * d2_2 * z_r + d2_1) * r * w ^ 2 * pU ιL_K5 k5Params.cb_h r ^ 3 * E3_dot := by
    have hD22_val : D22.val ≠ 0 := by simpa [D22, pUW_D_val] using hd2_2_ne
    set Z2_D : Dual CoverL := -D21 * Dual.invOfNe D22 hD22_val - Z_D
    have hD21_fac : D21 = -D22 * (Z_D + Z2_D) := by
      dsimp only [Z2_D]
      calc D21 = (D22 * Dual.invOfNe D22 hD22_val) * D21 := by rw [Dual.mul_invOfNe, one_mul]
        _ = -D22 * (Z_D + (-D21 * Dual.invOfNe D22 hD22_val - Z_D)) := by ring
    have hD20_fac : D20 = D22 * Z_D * Z2_D := by
      linear_combination hD2_Z - Z_D * (by rw [hD21_fac]; ring : D22 * (Z_D + Z2_D) + D21 = 0)
    have hres_D_eq : pUW_D ιL_K5 k5Params.res_z r w w' =
        D22 ^ 3 * (D33 * Z_D ^ 3 + D32 * Z_D ^ 2 + D31 * Z_D + D30) *
          (D33 * Z2_D ^ 3 + D32 * Z2_D ^ 2 + D31 * Z2_D + D30) := by
      have hs : pUW_D ιL_K5 k5Params.res_z r w w' = syl5 D22 D21 D20 D33 D32 D31 D30 := by
        let fD := Polynomial.eval₂RingHom (Dual.C.comp ιL_K5) (⟨r, 1⟩ : Dual CoverL)
        change PairAlg.evalAt (⟨w, w'⟩ : Dual CoverL) (PairAlg.map fD k5Params.res_z) = _
        rw [CoverParams.res_z, map_syl5Pair]
        exact evalAt_syl5Pair (fD k5Params.bW) (fD k5Params.cW)
          (PairAlg.map fD k5Params.d2_2) (PairAlg.map fD k5Params.d2_1) (PairAlg.map fD k5Params.d2_0)
          (PairAlg.map fD k5Params.d3_3) (PairAlg.map fD k5Params.d3_2) (PairAlg.map fD k5Params.d3_1)
          (PairAlg.map fD k5Params.d3_0) (⟨w, w'⟩ : Dual CoverL) hWD
      rw [hs, hD21_fac, hD20_fac]
      exact syl5_eq_prod_roots D22 D33 D32 D31 D30 Z_D Z2_D
    have hE3_Z_val : (D33 * Z_D ^ 3 + D32 * Z_D ^ 2 + D31 * Z_D + D30).val = 0 := by
      simp only [Dual.add_val, Dual.mul_val, Dual.pow_eq, D33, D32, D31, D30, pUW_D_val]
      exact hE3_zr
    have hz2_val : Z2_D.val = -d2_1 / d2_2 - z_r := by
      simp only [Z2_D, Z_D, Dual.sub_val, Dual.mul_val, Dual.neg_val, Dual.invOfNe, D21, D22, pUW_D_val]
      change -d2_1 * d2_2⁻¹ - z_r = -d2_1 / d2_2 - z_r
      ring
    have hE3_Z2_val : d2_2 ^ 3 * (D33 * Z2_D ^ 3 + D32 * Z2_D ^ 2 + D31 * Z2_D + D30).val =
        -d1_r * (2 * d2_2 * z_r + d2_1) := by
      have hv : (D33 * Z2_D ^ 3 + D32 * Z2_D ^ 2 + D31 * Z2_D + D30).val =
          d3_3 * Z2_D.val ^ 3 + d3_2 * Z2_D.val ^ 2 + d3_1 * Z2_D.val + d3_0 := by
        simp only [Dual.add_val, Dual.mul_val, Dual.pow_eq, D33, D32, D31, D30, pUW_D_val]; rfl
      rw [hv]
      have hqZ2 : d2_2 * Z2_D.val ^ 2 + d2_1 * Z2_D.val + d2_0 = 0 := by
        rw [hz2_val]; field_simp [hd2_2_ne]; linear_combination d2_2 * hE2_zr
      have hrem := remDeg3_eq d2_2 d2_1 d2_0 d3_3 d3_2 d3_1 d3_0 Z2_D.val
      rw [hqZ2, mul_zero, zero_add, ← hd1_rem, ← hd0_rem] at hrem
      have hd0_eq : d0_r = -d1_r * z_r := by dsimp only [z_r]; field_simp [hd1_ne]
      calc d2_2 ^ 3 * (d3_3 * Z2_D.val ^ 3 + d3_2 * Z2_D.val ^ 2 + d3_1 * Z2_D.val + d3_0)
          = d2_2 * (d2_2 ^ 2 * (d3_3 * Z2_D.val ^ 3 + d3_2 * Z2_D.val ^ 2 + d3_1 * Z2_D.val + d3_0)) := by ring
        _ = d2_2 * (d1_r * Z2_D.val + d0_r) := by rw [hrem]
        _ = -d1_r * (2 * d2_2 * z_r + d2_1) := by rw [hz2_val, hd0_eq]; field_simp [hd2_2_ne]; ring
    have heps := congrArg Dual.eps hres_D_eq
    rw [Dual.mul_eps, Dual.mul_eps, Dual.mul_val, hE3_Z_val, mul_zero, mul_zero, add_zero, zero_mul, zero_add] at heps
    have hD22_3_val : (D22 ^ 3).val = d2_2 ^ 3 := by simp [D22, Dual.pow_eq, pUW_D_val]; rfl
    rw [hD22_3_val, hE3_D_eps] at heps
    calc (pUW_D ιL_K5 k5Params.res_z r w w').eps
        = (d2_2 ^ 3 * (D33 * Z2_D ^ 3 + D32 * Z2_D ^ 2 + D31 * Z2_D + D30).val) *
            (r * w ^ 2 * pU ιL_K5 k5Params.cb_h r ^ 3 * E3_dot) := by linear_combination heps
      _ = -d1_r * (2 * d2_2 * z_r + d2_1) * r * w ^ 2 * pU ιL_K5 k5Params.cb_h r ^ 3 * E3_dot := by
          rw [hE3_Z2_val]; ring
  have hM_det : M.det = -ιL_K5 k5Params.Av0 * (2 * w + pU ιL_K5 k5Params.bW r) *
      (pUW_D ιL_K5 k5Params.res_z r w w').eps / (d1_r * r ^ 3 * w * pU ιL_K5 k5Params.cb_h r ^ 4) := by
    have hschur := det_J_fib_schur M a_r' b_r' V_r' E3_dot hM00 hM01 hM0 hM1 hM2 rfl
    have h03 : M 0 3 = ιL_K5 k5Params.Av0 * (2 * w + pU ιL_K5 k5Params.bW r) := J_fib_03 ιL_K5 a_r b_r r w hr0
    have hmin : M 1 1 * M 2 0 - M 1 0 * M 2 1 =
        w * (2 * d2_2 * z_r + d2_1) / (r ^ 2 * pU ιL_K5 k5Params.cb_h r) :=
      J_fib_minor12 ιL_K5 z_r r w hr0 hw_ne hcb
    rw [hschur, h03, hmin, hres_eps_eq]
    field_simp [hd1_ne, hr0, hw_ne, hcb]
  have hAv0_ne : ιL_K5 k5Params.Av0 ≠ 0 := (map_ne_zero_iff ιL_K5 ιL_K5.injective).mpr Av0_K5_ne_zero
  have hJ_ne : M.det ≠ 0 := by
    rw [hM_det]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hAv0_ne) h2w_ne) hres_eps_ne)
      (mul_ne_zero (mul_ne_zero (mul_ne_zero hd1_ne (pow_ne_zero 3 hr0)) hw_ne) (pow_ne_zero 4 hcb))
  -- 6. Compute `CrossedRationalResidue.residue r eta_L` via `residue_div_simpleZero` + `ValAC`!
  refine ⟨a_r, b_r, V_r, hE_all, hr0, hV_ne, hr1, hV1, hJ_ne, hM_ne, ?_⟩
  let g_P18 : CoverL → CoverL := fun z =>
    SheetCalculus.P18_of SL QL TL xL yL
      (z / w) (-(pU ιL_K5 k5Params.ca_h r * z + pUW ιL_K5 k5Params.c0W r w) / (w * pU ιL_K5 k5Params.cb_h r))
      r V_r
  obtain ⟨hp4, hp3, hp2, hp1, hp0⟩ :=
    valAC_interp4 hW_eq (fun hz => valAC_P18_z_AC hr0 hr1 hw_ne hcb hnmWU hW_eq hz)
  obtain ⟨hP1_val, hP0_val⟩ :=
    valAC_remDeg4 hW_eq (valAC_pairC r w _) (valAC_pairC r w _) (valAC_pairC r w _) hp4 hp3 hp2 hp1 hp0
  set q := interp4 g_P18
  set P1_r := remDeg4_P1 d2_2 d2_1 d2_0 q.1 q.2.1 q.2.2.1 q.2.2.2.1
  set P0_r := remDeg4_P0 d2_2 d2_1 d2_0 q.1 q.2.1 q.2.2.1 q.2.2.2.2
  have hnum_raw_val : ValAC r w eta_AC_num
      (-(P1_r * d0_r - P0_r * d1_r) * r ^ 3 * w * pU ιL_K5 k5Params.cb_h r ^ 4) := by
    have hmul {x y : A_C} {vx vy : CoverL} := @valAC_mul r w hW_eq x y vx vy
    have hpow {x : A_C} {vx : CoverL} := @valAC_pow r w hW_eq x vx
    exact hmul (hmul (hmul (valAC_neg (valAC_sub
      (hmul hP1_val (valAC_pairC r w _)) (hmul hP0_val (valAC_pairC r w _))))
      (hpow (valAC_U_C r w) 3)) (valAC_W_C r w)) (hpow (valAC_polyC r w _) 4)
  have h81_ne : (81 : CoverL) ≠ 0 := by exact_mod_cast (by decide : (81 : ℕ) ≠ 0)
  set D_poly : K5[X] := C (81 * k5Params.Av0) * k5Params.Q5_z ^ 3
  have hD_eval : (D_poly.map ιL_K5).eval r = 81 * ιL_K5 k5Params.Av0 * pU ιL_K5 k5Params.Q5_z r ^ 3 := by
    simp only [D_poly, pU, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_ofNat, eval_mul, eval_pow, eval_C, eval_ofNat, map_mul, map_ofNat]
  have hD_ne : (D_poly.map ιL_K5).eval r ≠ 0 := by
    rw [hD_eval]; exact mul_ne_zero (mul_ne_zero h81_ne hAv0_ne) (pow_ne_zero 3 hQ5)
  set num_r : A_C := eta_AC_num / polyC D_poly
  have hnum_val : ValAC r w num_r
      ((-(P1_r * d0_r - P0_r * d1_r) * r ^ 3 * w * pU ιL_K5 k5Params.cb_h r ^ 4) /
        (81 * ιL_K5 k5Params.Av0 * pU ιL_K5 k5Params.Q5_z r ^ 3)) := by
    rw [← hD_eval]
    exact valAC_div_of_reg hW_eq hnum_raw_val (valAC_polyC r w D_poly)
      (regAC_div_polyC hnum_raw_val.reg hD_ne) hD_ne
  -- Compute `-(P1_r * d0_r - P0_r * d1_r)` using `remDeg4_eq` and `P18_of_isPolyDeg4`!
  have hP18_deg4 : IsPolyDeg 4 g_P18 := by
    have h := P18_of_isPolyDeg4 (SL (L := CoverL)) QL TL xL yL r V_r
      (1 / w) 0 (-pU ιL_K5 k5Params.ca_h r / (w * pU ιL_K5 k5Params.cb_h r))
      (-pUW ιL_K5 k5Params.c0W r w / (w * pU ιL_K5 k5Params.cb_h r))
    refine h.congr (fun z => ?_)
    dsimp only [g_P18]
    congr 1
    · ring
    · field_simp [hw_ne, hcb]; ring
  have hq_zr : q.1 * z_r ^ 4 + q.2.1 * z_r ^ 3 + q.2.2.1 * z_r ^ 2 + q.2.2.2.1 * z_r + q.2.2.2.2 =
      P18_of SL QL TL xL yL a_r b_r r V_r := (hP18_deg4.eq_deg4 z_r).symm
  have hcomb_zr : -(P1_r * d0_r - P0_r * d1_r) =
      d1_r * pU ιL_K5 k5Params.Q5_z r ^ 3 * P18_of SL QL TL xL yL a_r b_r r V_r := by
    have hrem := remDeg4_eq d2_2 d2_1 d2_0 q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 z_r
    rw [hE2_zr, mul_zero, zero_add, hq_zr] at hrem
    change d2_2 ^ 3 * P18_of SL QL TL xL yL a_r b_r r V_r = P1_r * z_r + P0_r at hrem
    have hd0_eq : d0_r = -d1_r * z_r := by dsimp only [z_r]; field_simp [hd1_ne]
    rw [← hd2_2_eq, hd0_eq]
    linear_combination -d1_r * hrem
  -- Express `eta_L` via `trace_AC_euler` and apply `residue_div_simpleZero`!
  have heta_euler : eta = ((coordsAC num_r).c1 * toRat k5Params.res_z.c0 -
      (coordsAC num_r).c0 * toRat k5Params.res_z.c1) / toRat k5Params.nm_z := by
    have heta_eq : eta_AC = num_r / (pairC k5Params.res_z * (2 * W_C + polyC k5Params.bW)) := by
      dsimp only [num_r, D_poly]
      rw [eta_AC, polyC_81_Av0_Q5_eq, div_div]
      exact congrArg (eta_AC_num / ·) (by ring)
    have hnm_rat : PairAlg.nm (toRat k5Params.bW) (toRat k5Params.cW) (PairAlg.map toRat k5Params.res_z) ≠ 0 := by
      rw [← PairAlg.map_nm, show PairAlg.nm k5Params.bW k5Params.cW k5Params.res_z = k5Params.nm_z from rfl]
      exact polynomialMap_ne_zero nm_z_K5_ne_zero
    conv_lhs =>
      rw [eta, heta_eq, ← evalAC_coordsAC num_r, pairC, polyC,
        trace_AC_euler (coordsAC num_r) (PairAlg.map toRat k5Params.res_z) hnm_rat, ← PairAlg.map_nm]
    rfl
  set N_L : RatFunc CoverL := mapRatFunc ιL_K5
    ((coordsAC num_r).c1 * toRat k5Params.res_z.c0 - (coordsAC num_r).c0 * toRat k5Params.res_z.c1)
  have hN_reg : RegularAt r N_L := by
    simp only [N_L, map_sub, map_mul, mapRatFunc_algebraMap]
    exact regAt_sub_local (regAt_mul_local hnum_val.reg.c1 (RegularAt.polynomial r _))
      (regAt_mul_local hnum_val.reg.c0 (RegularAt.polynomial r _))
  have heta_L_eq : eta_L = N_L / algebraMap CoverL[X] (RatFunc CoverL) (k5Params.nm_z.map ιL_K5) := by
    rw [eta_L, heta_euler, map_div₀, mapRatFunc_algebraMap]
  rw [heta_L_eq, residue_div_simpleZero r N_L (k5Params.nm_z.map ιL_K5) hN_reg hnmz0 hnmzd]
  have hval_N : valueAt r N_L = pUW ιL_K5 k5Params.res_z r w_c * valAC r w num_r /
      (2 * w + pU ιL_K5 k5Params.bW r) := by
    simp only [N_L, map_sub, map_mul, mapRatFunc_algebraMap]
    rw [valueAt_mul_of_regularAt hnum_val.reg.c1 (RegularAt.polynomial r _),
        valueAt_mul_of_regularAt hnum_val.reg.c0 (RegularAt.polynomial r _),
        valueAt_polynomial, valueAt_polynomial]
    have hc0_eq : (k5Params.res_z.c0.map ιL_K5).eval r = -(k5Params.res_z.c1.map ιL_K5).eval r * w := by
      have h := hres0; simp only [pUW_eq, pU] at h; linear_combination h
    have hrc_eq : pUW ιL_K5 k5Params.res_z r w_c =
        -(k5Params.res_z.c1.map ιL_K5).eval r * (2 * w + pU ιL_K5 k5Params.bW r) := by
      simp only [pUW_eq, pU, hc0_eq]
      linear_combination (k5Params.res_z.c1.map ιL_K5).eval r * hW_sum
    dsimp only [valAC]
    rw [hc0_eq, hrc_eq, eq_div_iff h2w_ne]
    ring
  rw [hval_N, hnum_val.eq, hcomb_zr, ← hres_eps_prod, hM_det]
  field_simp [h81_ne, hAv0_ne, hQ5, h2w_ne, hresc, hres_eps_ne, hd1_ne, hr0, hw_ne, hcb]

private lemma resDivW_L_sum {ι : Type*} (s : Finset ι) (f : ι → Fin 4 → CoverL) :
    resDivW_L (fun i => ∑ a ∈ s, f a i) = ∑ a ∈ s, resDivW_L (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, resDivW_L, map_zero, zero_mul, zero_div, sub_self, Finset.sum_const_zero]
  | insert a s ha ih =>
    have hfun : (fun i => ∑ b ∈ insert a s, f b i) = fun i => f a i + ∑ b ∈ s, f b i := by
      funext i; exact Finset.sum_insert ha
    rw [hfun, resDivW_L_add, ih, Finset.sum_insert ha]

/-- **Summed Horizontal Sheet Theorem on `CoverL`**:
There exists a single 4-component vector `w_H_L : Fin 4 → CoverL` (the sum of `w_horiz` over
all 34 nondegenerate sheets above `R34`) whose weighted residue divergence equals the sum of
all 34 finite residues of `eta_L` on `R34`. -/
theorem sum_R34_eq_sheet_div :
    ∃ w_H_L : Fin 4 → CoverL,
      2 * ιL (L := CoverL) W2_K * ιL (L := CoverL) H0_K ^ 2 * resDivW_L w_H_L =
        ∑ r ∈ R34, CrossedRationalResidue.residue r eta_L := by
  classical
  have hex : ∀ r : {r // r ∈ R34}, ∃ a b V : CoverL,
      (∀ k : Fin 4, E_fn k SL QL TL a b r.1 V = 0) ∧
      r.1 ≠ 0 ∧ V ≠ 0 ∧ r.1 ≠ 1 ∧ V ≠ 1 ∧
      (J_fib SL QL TL a b r.1 V).det ≠ 0 ∧
      (M_abSQ SL QL TL a b r.1 V).det ≠ 0 ∧
      CrossedRationalResidue.residue r.1 eta_L =
        -P18_of SL QL TL xL yL a b r.1 V / (81 * (J_fib SL QL TL a b r.1 V).det) :=
    fun r => residue_eta_L_at_R34 r.1 r.2
  choose a b V hspec using hex
  refine ⟨fun i => ∑ r ∈ R34.attach, w_horiz (a r) (b r) r.1 (V r) i, ?_⟩
  rw [resDivW_L_sum, Finset.mul_sum, ← Finset.sum_attach R34]
  apply Finset.sum_congr rfl
  intro r _
  obtain ⟨hE, hr0, hV0, hr1, hV1, hJ, hM, hres⟩ := hspec r
  rw [sheet_horiz_identity (a r) (b r) r.1 (V r) hE hr0 hV0 hr1 hV1 hJ hM, ← hres]

end SplittingAndResidues

end SymmetricSexticResidual.CoverResidue
