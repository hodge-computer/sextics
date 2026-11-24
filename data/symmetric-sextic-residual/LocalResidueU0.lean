import Proposal.CoverResidue
import Proposal.LocalResidueData
import Proposal.VerticalIdentity

/-! Local residue of `eta : RatFunc K5` at `U = 0`:
1. Reusable Laurent-series branch homomorphisms `branchHom`, two-branch trace splitting
   `map_trace_AC_eq_sum_branches`, `ValLead` / `ValDual` valuation calculus, scaled degree-4
   interpolation bounds `HasValGe.interp4_scaled`, and unconditional mod-`F5` `Biv` reduction
   `bivReduceX2`.
2. Exact leading-order `Dual K5` analysis of `d1_z`, `d0_z`, `res_z` on `W2_0` (yielding explicit
   monomial nonvanishing `(res_z W2_0).coeff 2 ≠ 0` and, via `nm_z_K5_factor`,
   `(res_z W1_0).coeff 13 ≠ 0`).
3. Vanishing of `(br1_0 eta_AC).coeff (-1) = 0` on branch `W1_0` via the common leading root
   `z1 = -(Cv0/Bv0) * S_K / T_K` of `E2_lead`, `E3_lead`, and `A0V_lead2`.
4. Exact evaluation `(br2_0 eta_AC).coeff (-1) = toK5_RU` on branch `W2_0` via double-root
   `Dual K5` evaluation at `z2 = w0 * S_K / (T_K - 3)` and Kronecker `decide +kernel`. -/

noncomputable section
namespace SymmetricSexticResidual.LocalResidueU0
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.SheetCalculus
  SymmetricSexticResidual.CoverAlgebra SymmetricSexticResidual.CoverResidue
  SymmetricSexticResidual.LocalResidueData SymmetricSexticResidual.VerticalIdentity
  PolynomialEncoding.KroneckerCheck QuadraticCovers CrossedRationalResidue Polynomial
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions PolynomialEncoding.BivariateExpressions
open scoped BigOperators LaurentSeries PowerSeries

/-! ### Section 1: Laurent Branch Homomorphisms, `ValLead`, `ValDual`, and `bivReduceX2` -/

abbrev ψ0 : RatFunc K5 →+* LaurentSeries K5 := CrossedRationalResidue.expansion (0 : K5)

lemma ψ0_C (c : K5) : ψ0 (RatFunc.C c) = HahnSeries.C c :=
  CrossedRationalResidue.expansion_C 0 c

lemma ψ0_X : ψ0 (RatFunc.X : RatFunc K5) = HahnSeries.single (1 : ℤ) (1 : K5) := by
  rw [← CrossedRationalResidue.uniformizer_zero]
  exact CrossedRationalResidue.expansion_uniformizer 0

lemma ψ0_toRat (P : K5[X]) : ψ0 (toRat P) = evalT P := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n c =>
    rw [← C_mul_X_pow_eq_monomial]
    simp only [map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X, ψ0_C, ψ0_X,
      evalT_C, evalT_X]

/-- Total ring homomorphism `A_C →+* LaurentSeries K5` specializing `(U, W)` to a Laurent branch. -/
def branchHom (ψ : RatFunc K5 →+* LaurentSeries K5) (W : LaurentSeries K5)
    (hW : W ^ 2 + ψ (toRat k5Params.bW) * W + ψ (toRat k5Params.cW) = 0) :
    A_C →+* LaurentSeries K5 :=
  AdjoinRoot.lift ψ W (by
    simp only [E0_poly, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]
    exact hW)

lemma branchHom_ιC_rat (ψ : RatFunc K5 →+* LaurentSeries K5) (W : LaurentSeries K5)
    (hW : W ^ 2 + ψ (toRat k5Params.bW) * W + ψ (toRat k5Params.cW) = 0) (f : RatFunc K5) :
    branchHom ψ W hW (ιC_rat f) = ψ f :=
  AdjoinRoot.lift_of _

lemma branchHom_W_C (ψ : RatFunc K5 →+* LaurentSeries K5) (W : LaurentSeries K5)
    (hW : W ^ 2 + ψ (toRat k5Params.bW) * W + ψ (toRat k5Params.cW) = 0) :
    branchHom ψ W hW W_C = W :=
  AdjoinRoot.lift_root _

lemma branchHom_polyC (ψ : RatFunc K5 →+* LaurentSeries K5) (W : LaurentSeries K5)
    (hW : W ^ 2 + ψ (toRat k5Params.bW) * W + ψ (toRat k5Params.cW) = 0) (P : K5[X]) :
    branchHom ψ W hW (polyC P) = ψ (toRat P) :=
  branchHom_ιC_rat ψ W hW (toRat P)

lemma branchHom_pairC (ψ : RatFunc K5 →+* LaurentSeries K5) (W : LaurentSeries K5)
    (hW : W ^ 2 + ψ (toRat k5Params.bW) * W + ψ (toRat k5Params.cW) = 0) (x : PairAlg K5[X]) :
    branchHom ψ W hW (pairC x) = PairAlg.evalAt W (PairAlg.map (ψ.comp toRat) x) := by
  simp only [pairC, evalAC, PairAlg.evalAt, PairAlg.map, map_add, map_mul,
    branchHom_ιC_rat, branchHom_W_C, RingHom.comp_apply]

lemma branchHom_ιC_K5 (ψ : RatFunc K5 →+* LaurentSeries K5)
    (hψC : ∀ c : K5, ψ (RatFunc.C c) = HahnSeries.C c)
    (W : LaurentSeries K5)
    (hW : W ^ 2 + ψ (toRat k5Params.bW) * W + ψ (toRat k5Params.cW) = 0) (c : K5) :
    branchHom ψ W hW (ιC_K5 c) = HahnSeries.C c := by
  change branchHom ψ W hW (ιC_rat (RatFunc.C c)) = HahnSeries.C c
  rw [branchHom_ιC_rat, hψC]

/-- Universal two-branch trace splitting into `LaurentSeries K5`. -/
lemma map_trace_AC_eq_sum_branches (ψ : RatFunc K5 →+* LaurentSeries K5)
    (W1 W2 : LaurentSeries K5)
    (hW1 : W1 ^ 2 + ψ (toRat k5Params.bW) * W1 + ψ (toRat k5Params.cW) = 0)
    (hW2 : W2 ^ 2 + ψ (toRat k5Params.bW) * W2 + ψ (toRat k5Params.cW) = 0)
    (hsum : W1 + W2 = -ψ (toRat k5Params.bW)) (x : A_C) :
    ψ (Algebra.trace (RatFunc K5) A_C x) =
      branchHom ψ W1 hW1 x + branchHom ψ W2 hW2 x := by
  rw [← evalAC_coordsAC x, trace_AC_evalAC]
  simp only [evalAC, map_add, map_sub, map_mul, map_ofNat, branchHom_ιC_rat, branchHom_W_C]
  linear_combination -ψ (coordsAC x).c1 * hsum

/-- Transport `eta_AC` across `branchHom` directly into `LaurentSeries K5`. -/
lemma branchHom_eta_AC (ψ : RatFunc K5 →+* LaurentSeries K5)
    (hψC : ∀ c : K5, ψ (RatFunc.C c) = HahnSeries.C c)
    (W : LaurentSeries K5)
    (hW : W ^ 2 + ψ (toRat k5Params.bW) * W + ψ (toRat k5Params.cW) = 0) :
    let U := ψ RatFunc.X
    let V := W / U
    let fP := ψ.comp toRat
    let ca := fP k5Params.ca_h
    let cb := fP k5Params.cb_h
    let c0W := PairAlg.evalAt W (PairAlg.map fP k5Params.c0W)
    let d2_2 := PairAlg.evalAt W (PairAlg.map fP k5Params.d2_2)
    let d2_1 := PairAlg.evalAt W (PairAlg.map fP k5Params.d2_1)
    let d2_0 := PairAlg.evalAt W (PairAlg.map fP k5Params.d2_0)
    let d1 := PairAlg.evalAt W (PairAlg.map fP k5Params.d1_z)
    let d0 := PairAlg.evalAt W (PairAlg.map fP k5Params.d0_z)
    let res := PairAlg.evalAt W (PairAlg.map fP k5Params.res_z)
    let g : LaurentSeries K5 → LaurentSeries K5 := fun z =>
      P18_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K)
        (z / W) (-(ca * z + c0W) / (W * cb)) U V
    let p := interp4 g
    let P1 := remDeg4_P1 d2_2 d2_1 d2_0 p.1 p.2.1 p.2.2.1 p.2.2.2.1
    let P0 := remDeg4_P0 d2_2 d2_1 d2_0 p.1 p.2.1 p.2.2.1 p.2.2.2.2
    branchHom ψ W hW eta_AC =
      (-(P1 * d0 - P0 * d1) * U ^ 3 * W * cb ^ 4) /
      (81 * HahnSeries.C k5Params.Av0 * (2 * W + fP k5Params.bW) * fP k5Params.Q5_z ^ 3 * res) := by
  intro U V fP ca cb c0W d2_2 d2_1 d2_0 d1 d0 res g p P1 P0
  let br := branchHom ψ W hW
  have hbr_K5 : ∀ c : K5, br (ιC_K5 c) = HahnSeries.C c := branchHom_ιC_K5 ψ hψC W hW
  have hbr_U : br U_C = U := branchHom_ιC_rat ψ W hW RatFunc.X
  have hbr_W : br W_C = W := branchHom_W_C ψ W hW
  have hbr_V : br V_C = V := by simp only [V_C, map_div₀, hbr_W, hbr_U, V]
  have hbr_poly : ∀ P : K5[X], br (polyC P) = fP P := branchHom_polyC ψ W hW
  have hbr_pair : ∀ x : PairAlg K5[X], br (pairC x) = PairAlg.evalAt W (PairAlg.map fP x) :=
    branchHom_pairC ψ W hW
  have hbr_P18 : ∀ z : A_C, br (P18_z_AC z) = g (br z) := by
    intro z
    simp only [P18_z_AC, g, P18_of, A_0U, A_0V, A_Y, A_X, numM, q1_a2, q1_a1, q1_a0,
      q2_b2, q2_b1, q2_b0, dH_dS, dH_dQ, H0_of, A1_of, B1_of, cA1_of, dA1_fn, dH0_fn,
      dot_ab, QY_num, QX_num, Omega_F, dDX2_F, dDY2_F, F_contract, dF5_fn, dDX2_fn, dDY2_fn,
      DX2_of, DY2_of, u3_of, v3_of, om_fn, br_fn, LX_of, LY_of, dLX_fn, dLY_fn, EB_of,
      W2_of, u_of, v_of, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat,
      map_one, map_zero, hbr_K5, hbr_U, hbr_W, hbr_V, hbr_poly, hbr_pair, ca, cb, c0W]
  have hint : (br (interp4 P18_z_AC).1, br (interp4 P18_z_AC).2.1,
      br (interp4 P18_z_AC).2.2.1, br (interp4 P18_z_AC).2.2.2.1,
      br (interp4 P18_z_AC).2.2.2.2) = p :=
    map_interp4 br P18_z_AC g hbr_P18
  have hp4 : br (interp4 P18_z_AC).1 = p.1 := congrArg Prod.fst hint
  have hp3 : br (interp4 P18_z_AC).2.1 = p.2.1 := congrArg (fun t => t.2.1) hint
  have hp2 : br (interp4 P18_z_AC).2.2.1 = p.2.2.1 := congrArg (fun t => t.2.2.1) hint
  have hp1 : br (interp4 P18_z_AC).2.2.2.1 = p.2.2.2.1 := congrArg (fun t => t.2.2.2.1) hint
  have hp0 : br (interp4 P18_z_AC).2.2.2.2 = p.2.2.2.2 := congrArg (fun t => t.2.2.2.2) hint
  change br eta_AC = _
  simp only [eta_AC, eta_AC_num, remDeg4_P1, remDeg4_P0, map_div₀, map_mul, map_sub, map_add,
    map_neg, map_pow, map_ofNat, hbr_K5, hbr_U, hbr_W, hbr_poly, hbr_pair,
    hp4, hp3, hp2, hp1, hp0]
  rfl

-- Unconditional mod-`F5` `Biv` reduction in `K5` (`21 * S_K * x_K^2 = -(21 * T_K * y_K^2 + 7 * H0_K)`).
def vK5 : ℕ → K5
  | 0 => S_K
  | 1 => Q_K
  | 2 => T_K
  | _ => 0

def evalBivK5 (p : Biv) : K5 := denote vK5 x_K y_K p

def toK5_RU : K5 := evalBivK5 RU_biv / (D_RU : K5)
def toK5_RInf : K5 := evalBivK5 RInf_biv / (D_RInf : K5)
def toK5_RQ5 : K5 := evalBivK5 RQ5_biv / (D_RQ5 : K5)
def L_K : K5 := 77 * S_K - 210 * Q_K + 45

lemma evalBivK5_RU : evalBivK5 RU_biv = (D_RU : K5) * toK5_RU := by
  rw [toK5_RU, mul_div_cancel₀ _ (by unfold D_RU; exact_mod_cast (by decide : (11644549875 : ℕ) ≠ 0))]

lemma ringEval_vK5_H0_int_e : ringEval vK5 H0_int_e = 7 * H0_K := by
  have hH0 : H0_K = H0_of S_K Q_K T_K := by
    rw [H0_K, ← toK5_poly4, H0_4, H0_3, poly3ToPoly4, H0_of]
    simp only [toK5, poly4ToPoly5, tanIdx, map_add, map_sub, map_mul, map_pow, map_neg,
      map_ofNat, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, poly4ToK5, k4ToK5]
    have h57 : (algebraMap Poly4 K4 (MvPolynomial.C (5 / 7 : ℂ))) = (5 / 7 : K4) := by
      have h7 : (7 : K4) ≠ 0 := by exact_mod_cast (by decide : (7 : ℕ) ≠ 0)
      apply mul_left_cancel₀ h7
      have h1 : (7 : K4) * algebraMap Poly4 K4 (MvPolynomial.C (5 / 7 : ℂ)) =
          algebraMap Poly4 K4 (MvPolynomial.C (7 * (5 / 7 : ℂ))) := by
        rw [← map_ofNat (algebraMap Poly4 K4) 7, ← map_mul, ← map_ofNat MvPolynomial.C 7, ← map_mul]
      rw [h1, show (7 : ℂ) * (5 / 7 : ℂ) = 5 by norm_num, map_ofNat, map_ofNat, mul_div_cancel₀ _ h7]
    have h107 : (algebraMap Poly4 K4 (MvPolynomial.C (10 / 7 : ℂ))) = (10 / 7 : K4) := by
      have h7 : (7 : K4) ≠ 0 := by exact_mod_cast (by decide : (7 : ℕ) ≠ 0)
      apply mul_left_cancel₀ h7
      have h1 : (7 : K4) * algebraMap Poly4 K4 (MvPolynomial.C (10 / 7 : ℂ)) =
          algebraMap Poly4 K4 (MvPolynomial.C (7 * (10 / 7 : ℂ))) := by
        rw [← map_ofNat (algebraMap Poly4 K4) 7, ← map_mul, ← map_ofNat MvPolynomial.C 7, ← map_mul]
      rw [h1, show (7 : ℂ) * (10 / 7 : ℂ) = 10 by norm_num, map_ofNat, map_ofNat, mul_div_cancel₀ _ h7]
    rw [h57, h107]; simp only [map_div₀, map_ofNat]
  rw [hH0, H0_int_e, H0_of]
  simp only [ringEval, eS, eQ, eT, vK5, Int.cast_neg, Int.cast_ofNat]
  ring

lemma K5_21_S_x_sq : 21 * S_K * x_K ^ 2 = -(21 * T_K * y_K ^ 2 + ringEval vK5 H0_int_e) := by
  rw [ringEval_vK5_H0_int_e]
  have h := x_K_sq_relation
  change 3 * S_K * x_K ^ 2 + 3 * T_K * y_K ^ 2 + H0_K = 0 at h
  linear_combination 7 * h

/-- Single-pass mod-`F5` `x^2`-reduction on `Biv` (multiplies denotation by `21 * S_K`). -/
def bivReduceX2 : Biv → Biv
  | .nil => .nil
  | .cons a i j p =>
    let rest := bivReduceX2 p
    match i with
    | 0 => merge 512 (.cons (.mul (.mul (.num 21) eS) a) 0 j .nil) rest
    | 1 => merge 512 (.cons (.mul (.mul (.num 21) eS) a) 1 j .nil) rest
    | i' + 2 =>
      let t1 := .cons (.mul (.mul (.num (-21)) eT) a) i' (j + 2) .nil
      let t2 := .cons (.mul (.neg H0_int_e) a) i' j .nil
      merge 512 (merge 512 t1 t2) rest

lemma evalBivK5_bivReduceX2 (p : Biv) :
    evalBivK5 (bivReduceX2 p) = 21 * S_K * evalBivK5 p := by
  induction p with
  | nil => simp [bivReduceX2, evalBivK5, denote]
  | cons a i j p ih =>
    rcases i with _ | _ | i'
    · simp only [bivReduceX2, evalBivK5, merge_denote, denote, ringEval, eS, vK5, Int.cast_ofNat,
        add_zero, pow_zero, mul_one] at ih ⊢
      rw [ih]; ring
    · simp only [bivReduceX2, evalBivK5, merge_denote, denote, ringEval, eS, vK5, Int.cast_ofNat,
        add_zero, pow_one] at ih ⊢
      rw [ih]; ring
    · simp only [bivReduceX2, evalBivK5, merge_denote, denote, ringEval, eT, vK5,
        Int.cast_neg, Int.cast_ofNat, add_zero] at ih ⊢
      rw [ih]
      have hsq : x_K ^ (i' + 2) = x_K ^ i' * x_K ^ 2 := by rw [pow_add]
      have hy : y_K ^ (j + 2) = y_K ^ j * y_K ^ 2 := by rw [pow_add]
      rw [hsq, hy]
      linear_combination -(ringEval vK5 a * x_K ^ i' * y_K ^ j) * K5_21_S_x_sq

lemma evalBivK5_bivAdd (p q : Biv) : evalBivK5 (bivAdd p q) = evalBivK5 p + evalBivK5 q :=
  merge_denote vK5 x_K y_K 512 p q

lemma evalBivK5_bivSub (p q : Biv) : evalBivK5 (bivSub p q) = evalBivK5 p - evalBivK5 q := by
  rw [bivSub, evalBivK5, merge_denote, negBiv_denote, ← sub_eq_add_neg]; rfl

lemma evalBivK5_bivMul (p q : Biv) : evalBivK5 (bivMul p q) = evalBivK5 p * evalBivK5 q :=
  multiply_denote vK5 x_K y_K p q

lemma evalBivK5_bivScale (c : ℤ) (p : Biv) : evalBivK5 (bivScale c p) = (c : K5) * evalBivK5 p := by
  rw [bivScale, evalBivK5, scale_denote]; simp [ringEval, evalBivK5]

lemma evalBivK5_scale (e : Expr) (i j : ℕ) (p : Biv) :
    evalBivK5 (scale e i j p) = ringEval vK5 e * x_K ^ i * y_K ^ j * evalBivK5 p := by
  simpa [evalBivK5] using scale_denote vK5 x_K y_K e i j p

lemma quadU_coeff_zero {R : Type*} [CommRing R] (a0 a1 a2 : R) :
    (CoverParams.quadU a0 a1 a2).coeff 0 = a0 := by simp [CoverParams.quadU]

lemma quadU_coeff_one {R : Type*} [CommRing R] (a0 a1 a2 : R) :
    (CoverParams.quadU a0 a1 a2).coeff 1 = a1 := by simp [CoverParams.quadU]

lemma quadU_coeff_two {R : Type*} [CommRing R] (a0 a1 a2 : R) :
    (CoverParams.quadU a0 a1 a2).coeff 2 = a2 := by simp [CoverParams.quadU]

/-! ### Section 2: Exact `Dual K5` Analysis of `W2_0` and `res_z` Nonvanishing on Both Branches -/

lemma W1_0_eq_ψ0 : W1_0 ^ 2 + ψ0 (toRat k5Params.bW) * W1_0 + ψ0 (toRat k5Params.cW) = 0 := by
  rw [ψ0_toRat, ψ0_toRat]; exact W1_0_eq

lemma W2_0_eq_ψ0 : W2_0 ^ 2 + ψ0 (toRat k5Params.bW) * W2_0 + ψ0 (toRat k5Params.cW) = 0 := by
  rw [ψ0_toRat, ψ0_toRat]; exact W2_0_eq

lemma W1_W2_0_sum_ψ0 : W1_0 + W2_0 = -ψ0 (toRat k5Params.bW) := by
  rw [ψ0_toRat]; exact W1_W2_0_sum

abbrev br1_0 : A_C →+* LaurentSeries K5 := branchHom ψ0 W1_0 W1_0_eq_ψ0
abbrev br2_0 : A_C →+* LaurentSeries K5 := branchHom ψ0 W2_0 W2_0_eq_ψ0

lemma W2_0_coeff1 : W2_0.coeff 1 = -(k5Params.Bv1 * k5Params.Av0_inv) := by
  rw [W2_0, HahnSeries.coeff_sub, HahnSeries.coeff_neg, HasValGe_W1_0 1 (by omega), sub_zero,
    evalT_bW_eq]
  change -(HahnSeries.ofPowerSeries ℤ K5 b0PS).coeff (1 : ℕ) = _
  rw [HahnSeries.ofPowerSeries_apply_coeff]
  simp only [b0PS, map_add, PowerSeries.coeff_C, PowerSeries.coeff_C_mul, PowerSeries.coeff_X,
    PowerSeries.coeff_X_pow, mul_assoc]
  norm_num

lemma W2_0_valDual :
    ValDual 0 W2_0 ⟨-(k5Params.Bv0 * k5Params.Av0_inv), -(k5Params.Bv1 * k5Params.Av0_inv)⟩ :=
  ⟨HasValGe_W2_0, W2_0_coeff0, W2_0_coeff1⟩

private lemma evalT_toUW_valDual_W2 (v0 v1 v2 : K5) :
    let w0 := -(k5Params.Bv0 * k5Params.Av0_inv)
    let w1 := -(k5Params.Bv1 * k5Params.Av0_inv)
    ValDual 0 (PairAlg.evalAt W2_0 (PairAlg.map evalT (k5Params.toUW v0 v1 v2)))
      (Dual.C v2 * (⟨w0, w1⟩ : Dual K5) ^ 2 + Dual.C v1 * ⟨0, 1⟩ * ⟨w0, w1⟩) := by
  intro w0 w1
  have heq : PairAlg.evalAt W2_0 (PairAlg.map evalT (k5Params.toUW v0 v1 v2)) =
      HahnSeries.C v2 * W2_0 ^ 2 + HahnSeries.C v1 * HahnSeries.single 1 1 * W2_0 +
      HahnSeries.C v0 * HahnSeries.single 2 1 := by
    simp only [PairAlg.evalAt, PairAlg.map, CoverParams.toUW, map_sub, map_mul, map_pow,
      evalT_C, evalT_X, HahnSeries.single_pow]
    have h2p : (2 : ℕ) • (1 : ℤ) = 2 := by decide
    simp only [one_pow, h2p]
    linear_combination -HahnSeries.C v2 * W2_0_eq
  rw [heq]
  have h1 : ValDual 0 (HahnSeries.C v2 * W2_0 ^ 2) (Dual.C v2 * (⟨w0, w1⟩ : Dual K5) ^ 2) := by
    simpa only [zero_add, mul_zero] using (ValDual.of_C v2).mul (W2_0_valDual.pow 2)
  have h2 : ValLead 1 (HahnSeries.C v1 * HahnSeries.single 1 1 * W2_0) (v1 * w0) := by
    have ha := ((ValLead.of_C v1).mul (ValLead.of_single 1 1)).mul W2_0_valDual.toValLead
    simpa only [zero_add, add_zero, mul_one] using ha
  have h3 : HasValGe 2 (HahnSeries.C v0 * HahnSeries.single 2 1) := by
    simpa only [zero_add] using (HasValGe.of_C v0).mul (HasValGe.single 2 (1 : K5))
  have h12 : ValDual 0 (HahnSeries.C v2 * W2_0 ^ 2 + HahnSeries.C v1 * HahnSeries.single 1 1 * W2_0)
      (Dual.C v2 * (⟨w0, w1⟩ : Dual K5) ^ 2 + Dual.C v1 * ⟨0, 1⟩ * ⟨w0, w1⟩) := by
    refine (h1.add_shift1 h2).eq_d ?_
    ext <;> simp [Dual.C]
  exact h12.add_high h3

-- Exact `U = 0` scalar polynomial `ValDual 0` helpers
private lemma quadU_valDual (a0 a1 a2 : K5) :
    ValDual 0 (evalT (CoverParams.quadU a0 a1 a2)) ⟨a0, a1⟩ := by
  simpa only [quadU_coeff_zero, quadU_coeff_one] using ValDual.of_evalT (CoverParams.quadU a0 a1 a2)

-- Exact factored `d1_z`, `d0_z`, `res_z` on `W2_0`!
/-- Polymorphic algebraic core for the `ε`-part of `remDeg3_d0` at `W2_0`.
Evaluating `ring` over an abstract `[Field R] [CharZero R]` avoids carrying `K5`'s
`AdjoinRoot` instance stack through the degree-25 expansion. -/
private lemma hrem_d0_eps_alg {R : Type*} [Field R] [CharZero R] (S Q T : R)
    (caD cbD q20D q11D q02D c30D c21D c12D c03D c0W_s Wk2_s W2k3_s : Dual R)
    (hca : caD = ⟨-(25 / 81 : R) * (5 * S - 9 * Q) * (5 * S - 3 * Q),
      (143 / 81 : R) * S ^ 2 - (184 / 27) * S * Q + (52 / 9) * Q ^ 2⟩)
    (hcb : cbD = ⟨(50 / 27 : R) * S * (5 * S - 9 * Q),
      -(92 / 27 : R) * S ^ 2 + (104 / 9) * S * Q - (22 / 3) * Q ^ 2 + (10 / 7) * Q + 10 / 7⟩)
    (hq20 : q20D = ⟨-(625 / 81 : R) * S + (250 / 27) * Q, (143 / 81 : R) * S - (92 / 27) * Q⟩)
    (hq11 : q11D = ⟨(500 / 27 : R) * S - (50 / 3) * Q, -(184 / 27 : R) * S + (104 / 9) * Q⟩)
    (hq02 : q02D = ⟨-(25 / 3 : R) * S, (52 / 9 : R) * S - (22 / 3) * Q + 5 / 7⟩)
    (hc30 : c30D = ⟨-(625 / 243 : R), (143 / 243 : R)⟩)
    (hc21 : c21D = ⟨(250 / 27 : R), -(92 / 27 : R)⟩)
    (hc12 : c12D = ⟨-(25 / 3 : R), (52 / 9 : R)⟩)
    (hc03 : c03D = ⟨0, -(22 / 9 : R)⟩)
    (hc0W : c0W_s =
      let A := 5 * S - 9 * Q; let B := T - 3
      let w0n := -(25 / 4 : R) * S * A ^ 2
      let w1n := (243 / 4 : R) * (143 / 243 * S ^ 3 - 92 / 27 * S ^ 2 * Q + 52 / 9 * S * Q ^ 2 -
        22 / 9 * Q ^ 3 + 143 / 243 * T ^ 3 - 92 / 27 * T ^ 2 + 52 / 9 * T - 22 / 9 +
        5 / 7 * Q ^ 2 + 10 / 7 * Q)
      ⟨-(4 / 81 : R) * w0n ^ 2,
       -(4 / 81 : R) * (2 * w0n * w1n) + (143 / 81 * T ^ 2 - 184 / 27 * T + 52 / 9) * w0n * B⟩)
    (hWk2 : Wk2_s =
      let A := 5 * S - 9 * Q; let B := T - 3
      let w0n := -(25 / 4 : R) * S * A ^ 2
      let w1n := (243 / 4 : R) * (143 / 243 * S ^ 3 - 92 / 27 * S ^ 2 * Q + 52 / 9 * S * Q ^ 2 -
        22 / 9 * Q ^ 3 + 143 / 243 * T ^ 3 - 92 / 27 * T ^ 2 + 52 / 9 * T - 22 / 9 +
        5 / 7 * Q ^ 2 + 10 / 7 * Q)
      ⟨-(4 / 81 : R) * w0n ^ 3,
       -(4 / 81 : R) * (3 * w0n ^ 2 * w1n) + (143 / 81 * T - 92 / 27) * w0n ^ 2 * B ^ 2⟩)
    (hW2k3 : W2k3_s =
      let A := 5 * S - 9 * Q; let B := T - 3
      let w0n := -(25 / 4 : R) * S * A ^ 2
      let w1n := (243 / 4 : R) * (143 / 243 * S ^ 3 - 92 / 27 * S ^ 2 * Q + 52 / 9 * S * Q ^ 2 -
        22 / 9 * Q ^ 3 + 143 / 243 * T ^ 3 - 92 / 27 * T ^ 2 + 52 / 9 * T - 22 / 9 +
        5 / 7 * Q ^ 2 + 10 / 7 * Q)
      ⟨-(4 / 243 : R) * w0n ^ 4,
       -(4 / 243 : R) * (4 * w0n ^ 3 * w1n) + (143 / 243 : R) * w0n ^ 3 * B ^ 3⟩) :
    let D22 : Dual R := q20D * cbD ^ 2 - q11D * caD * cbD + q02D * caD ^ 2
    let D21_s : Dual R := (-q11D * cbD + 2 * q02D * caD) * c0W_s
    let D20_s : Dual R := q02D * c0W_s ^ 2 + cbD ^ 2 * Wk2_s
    let D33 : Dual R := c30D * cbD ^ 3 - c21D * caD * cbD ^ 2 + c12D * caD ^ 2 * cbD - c03D * caD ^ 3
    let D32_s : Dual R := (-c21D * cbD ^ 2 + 2 * c12D * caD * cbD - 3 * c03D * caD ^ 2) * c0W_s
    let D30_s : Dual R := -c03D * c0W_s ^ 3 + cbD ^ 3 * W2k3_s
    (remDeg3_d0 D22 D21_s D20_s D33 D32_s D30_s).eps =
      (-59604644775390625 / 103769130575703096 : R) *
        (225 * S - 45 * Q + 77 * T - 189) * S ^ 8 * (-(5 * S - 9 * Q)) ^ 17 := by
  subst hca hcb hq20 hq11 hq02 hc30 hc21 hc12 hc03 hc0W hWk2 hW2k3
  intro D22 D21_s D20_s D33 D32_s D30_s
  set A : R := 5 * S - 9 * Q
  set w0n : R := -(25 / 4 : R) * S * A ^ 2
  have h2v : (2 : Dual R).val = 2 := by rw [← one_add_one_eq_two, Dual.add_val]; exact one_add_one_eq_two
  have h2e : (2 : Dual R).eps = 0 := by rw [← one_add_one_eq_two, Dual.add_eps]; exact add_zero 0
  have h3v : (3 : Dual R).val = 3 := by
    rw [show (3 : Dual R) = 2 + 1 by ring, Dual.add_val, h2v, show (1 : Dual R).val = 1 from rfl]; ring
  have h3e : (3 : Dual R).eps = 0 := by rw [show (3 : Dual R) = 2 + 1 by ring, Dual.add_eps, h2e]; exact add_zero 0
  have hD22_v : D22.val = (15625 / 59049 : R) * S * A ^ 4 := by
    simp only [D22, Dual.add_val, Dual.sub_val, Dual.mul_val, Dual.pow_eq, A]; ring
  have hD21_v : D21_s.val = (15625 / 59049 : R) * S * A ^ 4 * (-2 * w0n * S) := by
    simp only [D21_s, Dual.add_val, Dual.mul_val, Dual.neg_val, h2v, w0n, A]; ring
  have hD20_v : D20_s.val = (15625 / 59049 : R) * S * A ^ 4 * (w0n * S) ^ 2 := by
    simp only [D20_s, Dual.add_val, Dual.mul_val, Dual.pow_eq, w0n, A]; ring
  have hD33_v : D33.val = -(781250 / 4782969 : R) * S * A ^ 5 := by
    simp only [D33, Dual.add_val, Dual.sub_val, Dual.mul_val, Dual.pow_eq, A]; ring
  have hD32_v : D32_s.val = -(781250 / 4782969 : R) * S * A ^ 5 * (-6 * w0n * S) := by
    simp only [D32_s, Dual.add_val, Dual.sub_val, Dual.mul_val, Dual.neg_val, Dual.pow_eq, h2v, h3v, w0n, A]; ring
  have hD30_v : D30_s.val = -(781250 / 4782969 : R) * S * A ^ 5 * (-4 * (w0n * S) ^ 3) := by
    simp only [D30_s, Dual.add_val, Dual.mul_val, Dual.neg_val, Dual.pow_eq, w0n, A]; ring
  have hd0_eps_id :
      (remDeg3_d0 D22 D21_s D20_s D33 D32_s D30_s).eps =
        D22.val ^ 2 * D30_s.eps + (2 * D22.val * D30_s.val - D20_s.val * D32_s.val) * D22.eps +
        D20_s.val * D33.val * D21_s.eps + (D21_s.val * D33.val - D22.val * D32_s.val) * D20_s.eps +
        D20_s.val * D21_s.val * D33.eps - D20_s.val * D22.val * D32_s.eps := by
    simp only [remDeg3_d0, Dual.sub_eps, Dual.mul_eps, Dual.sub_val, Dual.mul_val]; ring
  have hd0_eps_simp :
      (remDeg3_d0 D22 D21_s D20_s D33 D32_s D30_s).eps =
        ((15625 / 59049 : R) * S * A ^ 4) ^ 2 *
          (D30_s.eps - (w0n * S) ^ 2 * D32_s.eps - 2 * (w0n * S) ^ 3 * D33.eps) +
        ((15625 / 59049 : R) * S * A ^ 4) * (-(781250 / 4782969 : R) * S * A ^ 5) * (w0n * S) *
          (4 * D20_s.eps + (w0n * S) * D21_s.eps - 2 * (w0n * S) ^ 2 * D22.eps) := by
    rw [hd0_eps_id, hD22_v, hD21_v, hD20_v, hD33_v, hD32_v, hD30_v]; ring
  rw [hd0_eps_simp]
  simp only [D22, D21_s, D20_s, D33, D32_s, D30_s,
    Dual.add_val, Dual.sub_val, Dual.mul_val, Dual.neg_val, Dual.pow_eq,
    Dual.add_eps, Dual.sub_eps, Dual.mul_eps, Dual.neg_eps, h2v, h2e, h3v, h3e,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, w0n, A]
  ring

/-- Abstract `ValLead 2` transport for `syl5` from the linear remainder `(d1_z, d0_z)`
with opaque series and scalar arguments (avoids unfolding transparent `let`/`set` chains
during `ValLead` arithmetic and kernel typechecking). -/
private lemma valLead_syl5_of_rem {K : Type*} [Field K]
    {q2s q1s q0s e3s e2s e1s e0s d1s d0s : LaurentSeries K}
    {q2_0 z2 d1_1 d0_1 cd : K}
    (hq2 : ValLead 0 q2s q2_0) (hq1 : ValLead 0 q1s (-2 * q2_0 * z2))
    (hq0 : ValLead 0 q0s (q2_0 * z2 ^ 2))
    (hd1 : ValLead 1 d1s d1_1) (hd0 : ValLead 1 d0s d0_1)
    (hd1_eq : d1s = remDeg3_d1 q2s q1s q0s e3s e2s e1s)
    (hd0_eq : d0s = remDeg3_d0 q2s q1s q0s e3s e2s e0s)
    (hcd : d0_1 + z2 * d1_1 = cd) (hq2_ne : q2_0 ≠ 0) :
    ValLead 2 (syl5 q2s q1s q0s e3s e2s e1s e0s) (cd ^ 2 / q2_0) := by
  have hqs := q2_sq_mul_syl5 q2s q1s q0s e3s e2s e1s e0s
  have hrhs_L : ValLead 2 (q2s * d0s ^ 2 - d0s * d1s * q1s + d1s ^ 2 * q0s) (q2_0 * cd ^ 2) := by
    have ht1 : ValLead 2 (q2s * d0s ^ 2) (q2_0 * d0_1 ^ 2) :=
      (hq2.mul (hd0.pow 2)).eq_k (by omega)
    have ht2 : ValLead 2 (d0s * d1s * q1s) (d0_1 * d1_1 * (-2 * q2_0 * z2)) :=
      ((hd0.mul hd1).mul hq1).eq_k (by omega)
    have ht3 : ValLead 2 (d1s ^ 2 * q0s) (d1_1 ^ 2 * (q2_0 * z2 ^ 2)) :=
      ((hd1.pow 2).mul hq0).eq_k (by omega)
    refine ((ht1.sub ht2).add ht3).eq_c ?_
    rw [← hcd]; ring
  have hq2sq_L : ValLead 0 (q2s ^ 2) (q2_0 ^ 2) := (hq2.pow 2).eq_k (by omega)
  have hq2s_ne : q2s ^ 2 ≠ 0 := fun h0 => pow_ne_zero 2 hq2_ne (by rw [← hq2sq_L.c0, h0]; rfl)
  have hdiv : syl5 q2s q1s q0s e3s e2s e1s e0s =
      (q2s * d0s ^ 2 - d0s * d1s * q1s + d1s ^ 2 * q0s) / q2s ^ 2 := by
    rw [eq_div_iff hq2s_ne, _root_.mul_comm, hqs, hd1_eq, hd0_eq]; rfl
  rw [hdiv]
  exact (hrhs_L.div_of_ne hq2sq_L (pow_ne_zero 2 hq2_ne)).eq_k (by omega) |>.eq_c (by
    field_simp [hq2_ne])

lemma W2_0_d1_d0_res :
    let A := 5 * S_K - 9 * Q_K
    let B := T_K - 3
    let w0 := -(k5Params.Bv0 * k5Params.Av0_inv)
    let z2 := w0 * S_K / B
    let q2_0 := (15625 / 59049 : K5) * S_K * A ^ 4
    let d1_1 := (-2384185791015625 / 25942282643925774 : K5) *
      (225 * S_K - 45 * Q_K + 77 * T_K - 210) * S_K ^ 6 * (-A) ^ 15 / B ^ 8
    let d0_1 := (-59604644775390625 / 103769130575703096 : K5) *
      (225 * S_K - 45 * Q_K + 77 * T_K - 189) * S_K ^ 8 * (-A) ^ 17 / B ^ 12
    let cd := (-59604644775390625 / 4941387170271576 : K5) * S_K ^ 8 * (-A) ^ 17 / B ^ 12
    ValLead 1 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d1_z)) d1_1 ∧
    ValLead 1 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d0_z)) d0_1 ∧
    d0_1 + z2 * d1_1 = cd ∧
    ValLead 2 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.res_z)) (cd ^ 2 / q2_0) ∧
    cd ≠ 0 ∧ q2_0 ≠ 0 := by
  intro A B w0 z2 q2_0 d1_1 d0_1 cd
  have hB : B ≠ 0 := T_K_sub_3_ne
  have hS : S_K ≠ 0 := S_K_ne_zero
  have hA : A ≠ 0 := fiveS_sub_9Q_ne
  have hw0_eq : w0 = -(25 / 4 : K5) * S_K * A ^ 2 / B ^ 3 := by
    simp only [w0, CoverParams.Bv0, CoverParams.Av0_inv, CoverParams.inv4, CoverParams.inv243,
      k5Params_inv2, k5Params_inv3, k5Params_invT3, k5Params_S, k5Params_Q, A, B]
    field_simp [hB]; ring
  have hw1_eq : -(k5Params.Bv1 * k5Params.Av0_inv) = (243 / 4 : K5) * k5Params.Bv1 / B ^ 3 := by
    simp only [CoverParams.Av0_inv, CoverParams.inv4, k5Params_inv2, k5Params_invT3, B]
    field_simp [hB]; ring
  -- Build `ValDual 0` for all `d2_2..0, d3_3..0` in `Dual K5`, then evaluate `remDeg3_d1/d0`!
  set caD : Dual K5 := ⟨k5Params.ca_h.coeff 0, k5Params.ca_h.coeff 1⟩
  set cbD : Dual K5 := ⟨k5Params.cb_h.coeff 0, k5Params.cb_h.coeff 1⟩
  set q20D : Dual K5 := ⟨k5Params.q20.coeff 0, k5Params.q20.coeff 1⟩
  set q11D : Dual K5 := ⟨k5Params.q11.coeff 0, k5Params.q11.coeff 1⟩
  set q02D : Dual K5 := ⟨k5Params.q02.coeff 0, k5Params.q02.coeff 1⟩
  set c30D : Dual K5 := ⟨k5Params.c30.coeff 0, k5Params.c30.coeff 1⟩
  set c21D : Dual K5 := ⟨k5Params.c21.coeff 0, k5Params.c21.coeff 1⟩
  set c12D : Dual K5 := ⟨k5Params.c12.coeff 0, k5Params.c12.coeff 1⟩
  set c03D : Dual K5 := ⟨k5Params.c03.coeff 0, k5Params.c03.coeff 1⟩
  set WD : Dual K5 := ⟨w0, -(k5Params.Bv1 * k5Params.Av0_inv)⟩
  set c0WD : Dual K5 := Dual.C k5Params.c0_V2 * WD ^ 2 + Dual.C k5Params.c0_V1 * ⟨0, 1⟩ * WD
  set k2WD : Dual K5 := Dual.C k5Params.k2_V2 * WD ^ 2 + Dual.C k5Params.k2_V1 * ⟨0, 1⟩ * WD
  set k3WD : Dual K5 := Dual.C k5Params.k3_V2 * WD ^ 2 + Dual.C k5Params.k3_V1 * ⟨0, 1⟩ * WD
  have hca : ValDual 0 (evalT k5Params.ca_h) caD := ValDual.of_evalT _
  have hcb : ValDual 0 (evalT k5Params.cb_h) cbD := ValDual.of_evalT _
  have hq20 : ValDual 0 (evalT k5Params.q20) q20D := ValDual.of_evalT _
  have hq11 : ValDual 0 (evalT k5Params.q11) q11D := ValDual.of_evalT _
  have hq02 : ValDual 0 (evalT k5Params.q02) q02D := ValDual.of_evalT _
  have hc30 : ValDual 0 (evalT k5Params.c30) c30D := ValDual.of_evalT _
  have hc21 : ValDual 0 (evalT k5Params.c21) c21D := ValDual.of_evalT _
  have hc12 : ValDual 0 (evalT k5Params.c12) c12D := ValDual.of_evalT _
  have hc03 : ValDual 0 (evalT k5Params.c03) c03D := ValDual.of_evalT _
  have hc0W : ValDual 0 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.c0W)) c0WD :=
    evalT_toUW_valDual_W2 _ _ _
  have hk2W : ValDual 0 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.k2W)) k2WD :=
    evalT_toUW_valDual_W2 _ _ _
  have hk3W : ValDual 0 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.k3W)) k3WD :=
    evalT_toUW_valDual_W2 _ _ _
  set D22 : Dual K5 := q20D * cbD ^ 2 - q11D * caD * cbD + q02D * caD ^ 2
  set D21 : Dual K5 := (-q11D * cbD + 2 * q02D * caD) * c0WD
  set D20 : Dual K5 := q02D * c0WD ^ 2 + cbD ^ 2 * (WD * k2WD)
  set D33 : Dual K5 := c30D * cbD ^ 3 - c21D * caD * cbD ^ 2 + c12D * caD ^ 2 * cbD - c03D * caD ^ 3
  set D32 : Dual K5 := (-c21D * cbD ^ 2 + 2 * c12D * caD * cbD - 3 * c03D * caD ^ 2) * c0WD
  set D31 : Dual K5 := (c12D * cbD - 3 * c03D * caD) * c0WD ^ 2
  set D30 : Dual K5 := -c03D * c0WD ^ 3 + cbD ^ 3 * (WD ^ 2 * k3WD)
  have hmul0 {f g : LaurentSeries K5} {a b : Dual K5} (hf : ValDual 0 f a) (hg : ValDual 0 g b) :
      ValDual 0 (f * g) (a * b) := by simpa only [zero_add] using hf.mul hg
  have hpow0 {f : LaurentSeries K5} {a : Dual K5} (hf : ValDual 0 f a) (m : ℕ) :
      ValDual 0 (f ^ m) (a ^ m) := by simpa only [mul_zero] using hf.pow m
  have hD22 : ValDual 0 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d2_2)) D22 := by
    simp only [CoverParams.d2_2, CoverParams.Q5_z, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar,
      map_add, map_sub, map_mul, map_pow]
    exact ((hmul0 hq20 (hpow0 hcb 2)).sub (hmul0 (hmul0 hq11 hca) hcb)).add (hmul0 hq02 (hpow0 hca 2))
  have hD21 : ValDual 0 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d2_1)) D21 := by
    simp only [CoverParams.d2_1, PairAlg.map_smul, PairAlg.evalAt_smul, map_add, map_neg, map_mul, map_ofNat]
    exact hmul0 ((hmul0 hq11.neg hcb).add (hmul0 (hmul0 (ValDual.of_nat 2) hq02) hca)) hc0W
  have hD20 : ValDual 0 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d2_0)) D20 := by
    simp only [CoverParams.d2_0, CoverParams.pmul, PairAlg.map_add, PairAlg.map_smul, PairAlg.map_mul,
      PairAlg.map_W, PairAlg.evalAt_add, PairAlg.evalAt_smul, PairAlg.evalAt_mul _ _ W2_0 W2_0_eq,
      PairAlg.evalAt_W, map_pow]
    exact (hmul0 hq02 (hmul0 hc0W hc0W |>.eq_d (by ring))).add (hmul0 (hpow0 hcb 2) (hmul0 W2_0_valDual hk2W))
  have hD33 : ValDual 0 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d3_3)) D33 := by
    simp only [CoverParams.d3_3, CoverParams.Q7_z, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar,
      map_add, map_sub, map_mul, map_pow]
    exact (((hmul0 hc30 (hpow0 hcb 3)).sub (hmul0 (hmul0 hc21 hca) (hpow0 hcb 2))).add
      (hmul0 (hmul0 hc12 (hpow0 hca 2)) hcb)).sub (hmul0 hc03 (hpow0 hca 3))
  have hD32 : ValDual 0 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d3_2)) D32 := by
    simp only [CoverParams.d3_2, PairAlg.map_smul, PairAlg.evalAt_smul, map_add, map_sub,
      map_neg, map_mul, map_pow, map_ofNat]
    exact hmul0 (((hmul0 hc21.neg (hpow0 hcb 2)).add
      (hmul0 (hmul0 (hmul0 (ValDual.of_nat 2) hc12) hca) hcb)).sub
      (hmul0 (hmul0 (ValDual.of_nat 3) hc03) (hpow0 hca 2))) hc0W
  have hD31 : ValDual 0 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d3_1)) D31 := by
    simp only [CoverParams.d3_1, CoverParams.pmul, PairAlg.map_smul, PairAlg.map_mul,
      PairAlg.evalAt_smul, PairAlg.evalAt_mul _ _ W2_0 W2_0_eq, map_sub, map_mul, map_ofNat]
    exact hmul0 ((hmul0 hc12 hcb).sub (hmul0 (hmul0 (ValDual.of_nat 3) hc03) hca))
      (hmul0 hc0W hc0W |>.eq_d (by ring))
  have hD30 : ValDual 0 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d3_0)) D30 := by
    simp only [CoverParams.d3_0, CoverParams.pmul, PairAlg.map_add, PairAlg.map_smul, PairAlg.map_mul,
      PairAlg.map_W, PairAlg.evalAt_add, PairAlg.evalAt_smul, PairAlg.evalAt_mul _ _ W2_0 W2_0_eq,
      PairAlg.evalAt_W, map_neg, map_pow]
    exact (hmul0 hc03.neg (hmul0 hc0W (hmul0 hc0W hc0W) |>.eq_d (by ring))).add
      (hmul0 (hpow0 hcb 3) (hmul0 (hmul0 W2_0_valDual W2_0_valDual |>.eq_d (by ring)) hk3W))
  have hd1_D : ValDual 0 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d1_z))
      (remDeg3_d1 D22 D21 D20 D33 D32 D31) := by
    simp only [CoverParams.d1_z, CoverParams.pmul, PairAlg.map_sub, PairAlg.map_mul,
      PairAlg.evalAt_sub, PairAlg.evalAt_mul _ _ W2_0 W2_0_eq, remDeg3_d1]
    exact (hmul0 hD22 ((hmul0 hD22 hD31).sub (hmul0 hD20 hD33))).sub
      (hmul0 hD21 ((hmul0 hD22 hD32).sub (hmul0 hD21 hD33)))
  have hd0_D : ValDual 0 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d0_z))
      (remDeg3_d0 D22 D21 D20 D33 D32 D30) := by
    simp only [CoverParams.d0_z, CoverParams.pmul, PairAlg.map_sub, PairAlg.map_mul,
      PairAlg.evalAt_sub, PairAlg.evalAt_mul _ _ W2_0 W2_0_eq, remDeg3_d0]
    exact (hmul0 hD22 (hmul0 hD22 hD30)).sub (hmul0 hD20 ((hmul0 hD22 hD32).sub (hmul0 hD21 hD33)))
  -- Compute explicit `(S_K, Q_K, T_K)` values of `D22..D30` using `A = 5*S_K - 9*Q_K, B = T_K - 3`!
  have hca0 : k5Params.ca_h.coeff 0 = -(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K) := by
    simp only [CoverParams.ca_h, quadU_coeff_zero, CoverParams.inv81, CoverParams.inv27,
      k5Params_inv3, k5Params_S, k5Params_Q]; ring
  have hca1 : k5Params.ca_h.coeff 1 = (143 / 81 : K5) * S_K ^ 2 - (184 / 27) * S_K * Q_K + (52 / 9) * Q_K ^ 2 := by
    simp only [CoverParams.ca_h, quadU_coeff_one, CoverParams.inv81, CoverParams.inv27, CoverParams.inv9,
      k5Params_inv3, k5Params_S, k5Params_Q]; ring
  have hcb0 : k5Params.cb_h.coeff 0 = (50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K) := by
    simp only [CoverParams.cb_h, quadU_coeff_zero, CoverParams.inv27, CoverParams.inv9,
      k5Params_inv3, k5Params_S, k5Params_Q]; ring
  have hcb1 : k5Params.cb_h.coeff 1 = -(92 / 27 : K5) * S_K ^ 2 + (104 / 9) * S_K * Q_K -
      (22 / 3) * Q_K ^ 2 + (10 / 7) * Q_K + 10 / 7 := by
    simp only [CoverParams.cb_h, quadU_coeff_one, CoverParams.inv27, CoverParams.inv9,
      k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q]; ring
  have hq20_0 : k5Params.q20.coeff 0 = -(625 / 81 : K5) * S_K + (250 / 27) * Q_K := by
    simp only [CoverParams.q20, quadU_coeff_zero, CoverParams.inv81, CoverParams.inv27,
      k5Params_inv3, k5Params_S, k5Params_Q]; ring
  have hq20_1 : k5Params.q20.coeff 1 = (143 / 81 : K5) * S_K - (92 / 27) * Q_K := by
    simp only [CoverParams.q20, quadU_coeff_one, CoverParams.inv81, CoverParams.inv27,
      k5Params_inv3, k5Params_S, k5Params_Q]; ring
  have hq11_0 : k5Params.q11.coeff 0 = (500 / 27 : K5) * S_K - (50 / 3) * Q_K := by
    simp only [CoverParams.q11, quadU_coeff_zero, CoverParams.inv27, k5Params_inv3, k5Params_S, k5Params_Q]; ring
  have hq11_1 : k5Params.q11.coeff 1 = -(184 / 27 : K5) * S_K + (104 / 9) * Q_K := by
    simp only [CoverParams.q11, quadU_coeff_one, CoverParams.inv27, CoverParams.inv9,
      k5Params_inv3, k5Params_S, k5Params_Q]; ring
  have hq02_0 : k5Params.q02.coeff 0 = -(25 / 3 : K5) * S_K := by
    simp only [CoverParams.q02, quadU_coeff_zero, k5Params_inv3, k5Params_S]; ring
  have hq02_1 : k5Params.q02.coeff 1 = (52 / 9 : K5) * S_K - (22 / 3) * Q_K + 5 / 7 := by
    simp only [CoverParams.q02, quadU_coeff_one, CoverParams.inv9, k5Params_inv3, k5Params_inv7,
      k5Params_S, k5Params_Q]; ring
  have hc30_0 : k5Params.c30.coeff 0 = -(625 / 243 : K5) := by
    simp only [CoverParams.c30, quadU_coeff_zero, CoverParams.inv243, k5Params_inv3]; ring
  have hc30_1 : k5Params.c30.coeff 1 = (143 / 243 : K5) := by
    simp only [CoverParams.c30, quadU_coeff_one, CoverParams.inv243, k5Params_inv3]; ring
  have hc21_0 : k5Params.c21.coeff 0 = (250 / 27 : K5) := by
    simp only [CoverParams.c21, quadU_coeff_zero, CoverParams.inv27, k5Params_inv3]; ring
  have hc21_1 : k5Params.c21.coeff 1 = -(92 / 27 : K5) := by
    simp only [CoverParams.c21, quadU_coeff_one, CoverParams.inv27, k5Params_inv3]; ring
  have hc12_0 : k5Params.c12.coeff 0 = -(25 / 3 : K5) := by
    simp only [CoverParams.c12, quadU_coeff_zero, k5Params_inv3]; ring
  have hc12_1 : k5Params.c12.coeff 1 = (52 / 9 : K5) := by
    simp only [CoverParams.c12, quadU_coeff_one, CoverParams.inv9, k5Params_inv3]; ring
  have hc03_0 : k5Params.c03.coeff 0 = 0 := by
    simp only [CoverParams.c03, quadU_coeff_zero]
  have hc03_1 : k5Params.c03.coeff 1 = -(22 / 9 : K5) := by
    simp only [CoverParams.c03, quadU_coeff_one, CoverParams.inv9, k5Params_inv3]; ring
  -- Factor `iB = B⁻¹` cleanly out of `c0WD`, `WD * k2WD`, `WD^2 * k3WD` so `remDeg3_d1/d0` are division-free `ring`!
  set iB : K5 := B⁻¹
  have hiB : B * iB = 1 := mul_inv_cancel₀ hB
  set w0n : K5 := -(25 / 4 : K5) * S_K * A ^ 2
  set w1n : K5 := (243 / 4 : K5) * k5Params.Bv1
  have hw0_iB : w0 = w0n * iB ^ 3 := by rw [hw0_eq, div_eq_mul_inv, inv_pow]
  have hw1_iB : -(k5Params.Bv1 * k5Params.Av0_inv) = w1n * iB ^ 3 := by
    rw [hw1_eq, div_eq_mul_inv, inv_pow]
  set c0W_s : Dual K5 := ⟨-(4 / 81 : K5) * w0n ^ 2, -(4 / 81 : K5) * (2 * w0n * w1n) + k5Params.c0_V1 * w0n * B⟩
  set Wk2_s : Dual K5 := ⟨-(4 / 81 : K5) * w0n ^ 3, -(4 / 81 : K5) * (3 * w0n ^ 2 * w1n) + k5Params.k2_V1 * w0n ^ 2 * B ^ 2⟩
  set W2k3_s : Dual K5 := ⟨-(4 / 243 : K5) * w0n ^ 4, -(4 / 243 : K5) * (4 * w0n ^ 3 * w1n) + k5Params.k3_V1 * w0n ^ 3 * B ^ 3⟩
  have hc0WD_eq : c0WD = Dual.C (iB ^ 4) * c0W_s := by
    have hc0V2 : k5Params.c0_V2 = -(4 / 81 : K5) * B ^ 2 := by
      simp only [CoverParams.c0_V2, CoverParams.inv81, k5Params_inv3, k5Params_T, B]; ring
    ext
    · simp only [c0WD, c0W_s, WD, Dual.add_val, Dual.mul_val, Dual.pow_eq, Dual.C_val, hw0_iB, hc0V2]
      linear_combination -(4 / 81 : K5) * w0n ^ 2 * iB ^ 4 * (B * iB + 1) * hiB
    · simp only [c0WD, c0W_s, WD, Dual.add_eps, Dual.mul_eps, Dual.mul_val, Dual.pow_eq,
        Dual.C_val, Dual.C_eps, Nat.cast_ofNat, Nat.reduceSub, pow_one, hw0_iB, hw1_iB, hc0V2]
      linear_combination -(4 / 81 : K5) * (2 * w0n * w1n) * iB ^ 4 * (B * iB + 1) * hiB -
        k5Params.c0_V1 * w0n * iB ^ 3 * hiB
  have hWk2_eq : WD * k2WD = Dual.C (iB ^ 8) * Wk2_s := by
    have hk2V2 : k5Params.k2_V2 = -(4 / 81 : K5) * B := by
      simp only [CoverParams.k2_V2, CoverParams.inv81, k5Params_inv3, k5Params_T, B]; ring
    ext
    · simp only [k2WD, Wk2_s, WD, Dual.add_val, Dual.mul_val, Dual.pow_eq, Dual.C_val, hw0_iB, hk2V2]
      linear_combination -(4 / 81 : K5) * w0n ^ 3 * iB ^ 8 * hiB
    · simp only [k2WD, Wk2_s, WD, Dual.add_val, Dual.add_eps, Dual.mul_eps, Dual.mul_val,
        Dual.pow_eq, Dual.C_val, Dual.C_eps, Nat.cast_ofNat, Nat.reduceSub, pow_one, hw0_iB, hw1_iB, hk2V2]
      linear_combination -(4 / 81 : K5) * (3 * w0n ^ 2 * w1n) * iB ^ 8 * hiB -
        k5Params.k2_V1 * w0n ^ 2 * iB ^ 6 * (B * iB + 1) * hiB
  have hW2k3_eq : WD ^ 2 * k3WD = Dual.C (iB ^ 12) * W2k3_s := by
    have hk3V2 : k5Params.k3_V2 = -(4 / 243 : K5) := by
      simp only [CoverParams.k3_V2, CoverParams.inv243, k5Params_inv3]; ring
    ext
    · simp only [k3WD, W2k3_s, WD, Dual.add_val, Dual.mul_val, Dual.pow_eq, Dual.C_val, hw0_iB, hk3V2]; ring
    · simp only [k3WD, W2k3_s, WD, Dual.add_val, Dual.add_eps, Dual.mul_eps, Dual.mul_val,
        Dual.pow_eq, Dual.C_val, Dual.C_eps, Nat.cast_ofNat, Nat.reduceSub, pow_one, hw0_iB, hw1_iB, hk3V2]
      linear_combination -k5Params.k3_V1 * w0n ^ 3 * iB ^ 9 * ((B * iB) ^ 2 + B * iB + 1) * hiB
  set D21_s : Dual K5 := (-q11D * cbD + 2 * q02D * caD) * c0W_s
  set D20_s : Dual K5 := q02D * c0W_s ^ 2 + cbD ^ 2 * Wk2_s
  set D32_s : Dual K5 := (-c21D * cbD ^ 2 + 2 * c12D * caD * cbD - 3 * c03D * caD ^ 2) * c0W_s
  set D31_s : Dual K5 := (c12D * cbD - 3 * c03D * caD) * c0W_s ^ 2
  set D30_s : Dual K5 := -c03D * c0W_s ^ 3 + cbD ^ 3 * W2k3_s
  have hD21_sc : D21 = Dual.C (iB ^ 4) * D21_s := by dsimp only [D21, D21_s]; rw [hc0WD_eq]; ring
  have hD20_sc : D20 = Dual.C (iB ^ 8) * D20_s := by
    have hpow : Dual.C (iB ^ 4) ^ 2 = Dual.C (iB ^ 8) := by
      ext <;> simp only [Dual.pow_eq, Dual.C_val, Dual.C_eps] <;> ring
    change q02D * c0WD ^ 2 + cbD ^ 2 * (WD * k2WD) = Dual.C (iB ^ 8) * (q02D * c0W_s ^ 2 + cbD ^ 2 * Wk2_s)
    rw [hc0WD_eq, hWk2_eq, mul_pow, hpow]; ring
  have hD32_sc : D32 = Dual.C (iB ^ 4) * D32_s := by dsimp only [D32, D32_s]; rw [hc0WD_eq]; ring
  have hD31_sc : D31 = Dual.C (iB ^ 8) * D31_s := by
    have hpow : Dual.C (iB ^ 4) ^ 2 = Dual.C (iB ^ 8) := by
      ext <;> simp only [Dual.pow_eq, Dual.C_val, Dual.C_eps] <;> ring
    change (c12D * cbD - 3 * c03D * caD) * c0WD ^ 2 = Dual.C (iB ^ 8) * ((c12D * cbD - 3 * c03D * caD) * c0W_s ^ 2)
    rw [hc0WD_eq, mul_pow, hpow]; ring
  have hD30_sc : D30 = Dual.C (iB ^ 12) * D30_s := by
    have hpow : Dual.C (iB ^ 4) ^ 3 = Dual.C (iB ^ 12) := by
      ext <;> simp only [Dual.pow_eq, Dual.C_val, Dual.C_eps] <;> ring
    change -c03D * c0WD ^ 3 + cbD ^ 3 * (WD ^ 2 * k3WD) = Dual.C (iB ^ 12) * (-c03D * c0W_s ^ 3 + cbD ^ 3 * W2k3_s)
    rw [hc0WD_eq, hW2k3_eq, mul_pow, hpow]; ring
  -- Flatten `D22..D30_s` into plain `K5` values first so `remDeg3_d1/d0` close in <0.1s!
  have h2v : (2 : Dual K5).val = 2 := by rw [← one_add_one_eq_two, Dual.add_val]; exact one_add_one_eq_two
  have h2e : (2 : Dual K5).eps = 0 := by rw [← one_add_one_eq_two, Dual.add_eps]; exact add_zero 0
  have h3v : (3 : Dual K5).val = 3 := by
    rw [show (3 : Dual K5) = 2 + 1 by ring, Dual.add_val, h2v, show (1 : Dual K5).val = 1 from rfl]; ring
  have h3e : (3 : Dual K5).eps = 0 := by rw [show (3 : Dual K5) = 2 + 1 by ring, Dual.add_eps, h2e]; exact add_zero 0
  have hD22_v : D22.val = (15625 / 59049 : K5) * S_K * A ^ 4 := by
    simp only [D22, Dual.add_val, Dual.sub_val, Dual.mul_val, Dual.pow_eq,
      q20D, q11D, q02D, caD, cbD, hq20_0, hq11_0, hq02_0, hca0, hcb0, A]; ring
  have hD21_v : D21_s.val = (15625 / 59049 : K5) * S_K * A ^ 4 * (-2 * w0n * S_K) := by
    simp only [D21_s, c0W_s, Dual.add_val, Dual.mul_val, Dual.neg_val, h2v,
      q11D, q02D, caD, cbD, hq11_0, hq02_0, hca0, hcb0, w0n, A]; ring
  have hD20_v : D20_s.val = (15625 / 59049 : K5) * S_K * A ^ 4 * (w0n * S_K) ^ 2 := by
    simp only [D20_s, c0W_s, Wk2_s, Dual.add_val, Dual.mul_val, Dual.pow_eq,
      q02D, cbD, hq02_0, hcb0, w0n, A]; ring
  have hD33_v : D33.val = -(781250 / 4782969 : K5) * S_K * A ^ 5 := by
    simp only [D33, Dual.add_val, Dual.sub_val, Dual.mul_val, Dual.pow_eq,
      c30D, c21D, c12D, c03D, caD, cbD, hc30_0, hc21_0, hc12_0, hc03_0, hca0, hcb0, A]; ring
  have hD32_v : D32_s.val = -(781250 / 4782969 : K5) * S_K * A ^ 5 * (-6 * w0n * S_K) := by
    simp only [D32_s, c0W_s, Dual.add_val, Dual.sub_val, Dual.mul_val, Dual.neg_val, Dual.pow_eq, h2v, h3v,
      c21D, c12D, c03D, caD, cbD, hc21_0, hc12_0, hc03_0, hca0, hcb0, w0n, A]; ring
  have hD31_v : D31_s.val = -(781250 / 4782969 : K5) * S_K * A ^ 5 * (9 * (w0n * S_K) ^ 2) := by
    simp only [D31_s, c0W_s, Dual.sub_val, Dual.mul_val, Dual.pow_eq, h3v,
      c12D, c03D, caD, cbD, hc12_0, hc03_0, hca0, hcb0, w0n, A]; ring
  have hD30_v : D30_s.val = -(781250 / 4782969 : K5) * S_K * A ^ 5 * (-4 * (w0n * S_K) ^ 3) := by
    simp only [D30_s, c0W_s, W2k3_s, Dual.add_val, Dual.mul_val, Dual.neg_val, Dual.pow_eq,
      c03D, cbD, hc03_0, hcb0, w0n, A]; ring
  set d22e := D22.eps; set d21e := D21_s.eps; set d20e := D20_s.eps
  set d33e := D33.eps; set d32e := D32_s.eps; set d31e := D31_s.eps
  have hd1_eps_id :
      (remDeg3_d1 D22 D21_s D20_s D33 D32_s D31_s).eps =
        D22.val ^ 2 * d31e + (2 * D22.val * D31_s.val - D20_s.val * D33.val - D21_s.val * D32_s.val) * d22e +
        (2 * D21_s.val * D33.val - D22.val * D32_s.val) * d21e - D22.val * D33.val * d20e +
        (D21_s.val ^ 2 - D22.val * D20_s.val) * d33e - D21_s.val * D22.val * d32e := by
    simp only [remDeg3_d1, Dual.sub_eps, Dual.mul_eps, Dual.sub_val, Dual.mul_val,
      d22e, d21e, d20e, d33e, d32e, d31e]; ring
  -- Notice the miracle: `D2_v(z) = D22_v*(z - r)^2`, `D3_v(z) = D33_v*(z - r)^2*(z - 4r)`!
  have hd1_eps_simp :
      (remDeg3_d1 D22 D21_s D20_s D33 D32_s D31_s).eps =
        ((15625 / 59049 : K5) * S_K * A ^ 4) ^ 2 *
          (d31e + 2 * (w0n * S_K) * d32e + 3 * (w0n * S_K) ^ 2 * d33e) -
        ((15625 / 59049 : K5) * S_K * A ^ 4) * (-(781250 / 4782969 : K5) * S_K * A ^ 5) *
          (d20e - 2 * (w0n * S_K) * d21e - 5 * (w0n * S_K) ^ 2 * d22e) := by
    rw [hd1_eps_id, hD22_v, hD21_v, hD20_v, hD33_v, hD32_v, hD31_v]; ring
  have hrem_d1 : remDeg3_d1 D22 D21 D20 D33 D32 D31 = ⟨0, d1_1⟩ := by
    have hsc : remDeg3_d1 D22 D21 D20 D33 D32 D31 = Dual.C (iB ^ 8) * remDeg3_d1 D22 D21_s D20_s D33 D32_s D31_s := by
      simp only [remDeg3_d1, hD21_sc, hD20_sc, hD32_sc, hD31_sc]
      have hpow : Dual.C (iB ^ 4) * Dual.C (iB ^ 4) = Dual.C (iB ^ 8) := by
        ext <;> simp only [Dual.mul_val, Dual.mul_eps, Dual.C_val, Dual.C_eps] <;> ring
      linear_combination -(D21_s * (D22 * D32_s - D21_s * D33)) * hpow
    have hpoly : remDeg3_d1 D22 D21_s D20_s D33 D32_s D31_s =
        ⟨0, (-2384185791015625 / 25942282643925774 : K5) *
          (225 * S_K - 45 * Q_K + 77 * T_K - 210) * S_K ^ 6 * (-A) ^ 15⟩ := by
      ext
      · simp only [remDeg3_d1, Dual.sub_val, Dual.mul_val, hD22_v, hD21_v, hD20_v, hD33_v, hD32_v, hD31_v]; ring
      · rw [hd1_eps_simp]
        simp only [d22e, d21e, d20e, d33e, d32e, d31e, D22, D21_s, D20_s, D33, D32_s, D31_s, c0W_s, Wk2_s,
          Dual.add_val, Dual.sub_val, Dual.mul_val, Dual.neg_val, Dual.pow_eq,
          Dual.add_eps, Dual.sub_eps, Dual.mul_eps, Dual.neg_eps, h2v, h2e, h3v, h3e,
          Nat.cast_ofNat, Nat.reduceSub, pow_one,
          q20D, q11D, q02D, c30D, c21D, c12D, c03D, caD, cbD,
          hq20_0, hq20_1, hq11_0, hq11_1, hq02_0, hq02_1,
          hc30_0, hc30_1, hc21_0, hc21_1, hc12_0, hc12_1, hc03_0, hc03_1,
          hca0, hca1, hcb0, hcb1, w0n, w1n,
          CoverParams.Bv1, CoverParams.c0_V1, CoverParams.k2_V1,
          CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, CoverParams.inv243,
          k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q, k5Params_T, A, B]
        ring
    rw [hsc, hpoly]
    ext
    · simp only [Dual.mul_val, Dual.C_val, mul_zero]
    · simp only [Dual.mul_eps, Dual.C_val, Dual.C_eps, mul_zero, add_zero, d1_1, iB, div_eq_mul_inv, inv_pow]; ring
  have hrem_d0 : remDeg3_d0 D22 D21 D20 D33 D32 D30 = ⟨0, d0_1⟩ := by
    have hsc : remDeg3_d0 D22 D21 D20 D33 D32 D30 = Dual.C (iB ^ 12) * remDeg3_d0 D22 D21_s D20_s D33 D32_s D30_s := by
      simp only [remDeg3_d0, hD21_sc, hD20_sc, hD32_sc, hD30_sc]
      have hpow : Dual.C (iB ^ 8) * Dual.C (iB ^ 4) = Dual.C (iB ^ 12) := by
        ext <;> simp only [Dual.mul_val, Dual.mul_eps, Dual.C_val, Dual.C_eps] <;> ring
      linear_combination -(D20_s * (D22 * D32_s - D21_s * D33)) * hpow
    have hpoly : remDeg3_d0 D22 D21_s D20_s D33 D32_s D30_s =
        ⟨0, (-59604644775390625 / 103769130575703096 : K5) *
          (225 * S_K - 45 * Q_K + 77 * T_K - 189) * S_K ^ 8 * (-A) ^ 17⟩ := by
      ext
      · simp only [remDeg3_d0, Dual.sub_val, Dual.mul_val, hD22_v, hD21_v, hD20_v, hD33_v, hD32_v, hD30_v]; ring
      · have hBv1 : k5Params.Bv1 =
            143 / 243 * S_K ^ 3 - 92 / 27 * S_K ^ 2 * Q_K + 52 / 9 * S_K * Q_K ^ 2 -
            22 / 9 * Q_K ^ 3 + 143 / 243 * T_K ^ 3 - 92 / 27 * T_K ^ 2 + 52 / 9 * T_K - 22 / 9 +
            5 / 7 * Q_K ^ 2 + 10 / 7 * Q_K := by
          simp only [CoverParams.Bv1, CoverParams.inv9, CoverParams.inv27, CoverParams.inv243,
            k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q, k5Params_T]; ring
        have hc0V1 : k5Params.c0_V1 = 143 / 81 * T_K ^ 2 - 184 / 27 * T_K + 52 / 9 := by
          simp only [CoverParams.c0_V1, CoverParams.inv9, CoverParams.inv27, CoverParams.inv81,
            k5Params_inv3, k5Params_T]; ring
        have hk2V1 : k5Params.k2_V1 = 143 / 81 * T_K - 92 / 27 := by
          simp only [CoverParams.k2_V1, CoverParams.inv27, CoverParams.inv81,
            k5Params_inv3, k5Params_T]; ring
        have hk3V1 : k5Params.k3_V1 = 143 / 243 := by
          simp only [CoverParams.k3_V1, CoverParams.inv243, k5Params_inv3]; ring
        exact hrem_d0_eps_alg S_K Q_K T_K caD cbD q20D q11D q02D c30D c21D c12D c03D c0W_s Wk2_s W2k3_s
          (Dual.ext hca0 hca1) (Dual.ext hcb0 hcb1) (Dual.ext hq20_0 hq20_1) (Dual.ext hq11_0 hq11_1)
          (Dual.ext hq02_0 hq02_1) (Dual.ext hc30_0 hc30_1) (Dual.ext hc21_0 hc21_1)
          (Dual.ext hc12_0 hc12_1) (Dual.ext hc03_0 hc03_1)
          (by dsimp only [c0W_s, w0n, w1n, A, B]; rw [hBv1, hc0V1])
          (by dsimp only [Wk2_s, w0n, w1n, A, B]; rw [hBv1, hk2V1])
          (by dsimp only [W2k3_s, w0n, w1n, A, B]; rw [hBv1, hk3V1])
    rw [hsc, hpoly]
    ext
    · simp only [Dual.mul_val, Dual.C_val, mul_zero]
    · simp only [Dual.mul_eps, Dual.C_val, Dual.C_eps, mul_zero, add_zero, d0_1, iB, div_eq_mul_inv, inv_pow]; ring
  rw [hrem_d1] at hd1_D
  rw [hrem_d0] at hd0_D
  have hd1_L : ValLead 1 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d1_z)) d1_1 :=
    ⟨hd1_D.val.inc hd1_D.c0, hd1_D.c1⟩
  have hd0_L : ValLead 1 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d0_z)) d0_1 :=
    ⟨hd0_D.val.inc hd0_D.c0, hd0_D.c1⟩
  have hcd_eq : d0_1 + z2 * d1_1 = cd := by
    dsimp only [d0_1, d1_1, z2, cd]
    rw [hw0_iB]
    simp only [div_eq_mul_inv, inv_pow, w0n, iB]
    clear_value A B
    ring
  have hq2_ne : q2_0 ≠ 0 := by
    have hc : (15625 / 59049 : K5) ≠ 0 := div_ne_zero
      (by exact_mod_cast (by decide : (15625 : ℕ) ≠ 0))
      (by exact_mod_cast (by decide : (59049 : ℕ) ≠ 0))
    exact mul_ne_zero (mul_ne_zero hc hS) (pow_ne_zero 4 hA)
  have hcd_ne : cd ≠ 0 := by
    have hc : (-59604644775390625 / 4941387170271576 : K5) ≠ 0 := div_ne_zero
      (neg_ne_zero.mpr (by exact_mod_cast (by decide : (59604644775390625 : ℕ) ≠ 0)))
      (by exact_mod_cast (by decide : (4941387170271576 : ℕ) ≠ 0))
    exact div_ne_zero (mul_ne_zero (mul_ne_zero hc (pow_ne_zero 8 hS))
      (pow_ne_zero 17 (neg_ne_zero.mpr hA))) (pow_ne_zero 12 hB)
  -- Deduce `ValLead 2 (res_z W2_0) (cd ^ 2 / q2_0)` directly from `q2_sq_mul_syl5`!
  have hres_L : ValLead 2 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.res_z)) (cd ^ 2 / q2_0) := by
    set q2s := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d2_2)
    set q1s := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d2_1)
    set q0s := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d2_0)
    set e3s := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d3_3)
    set e2s := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d3_2)
    set e1s := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d3_1)
    set e0s := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d3_0)
    have hq2_L : ValLead 0 q2s q2_0 := hD22.toValLead.eq_c hD22_v
    have hq1_L : ValLead 0 q1s (-2 * q2_0 * z2) := hD21.toValLead.eq_c (by
      rw [hD21_sc, Dual.mul_val, Dual.C_val, hD21_v]
      dsimp only [z2, q2_0]; rw [hw0_iB]; simp only [div_eq_mul_inv, iB]; ring)
    have hq0_L : ValLead 0 q0s (q2_0 * z2 ^ 2) := hD20.toValLead.eq_c (by
      rw [hD20_sc, Dual.mul_val, Dual.C_val, hD20_v]
      dsimp only [z2, q2_0]; rw [hw0_iB]; simp only [div_eq_mul_inv, iB]; ring)
    have hres_eq : PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.res_z) =
        syl5 q2s q1s q0s e3s e2s e1s e0s := by
      rw [CoverParams.res_z, map_syl5Pair]
      exact evalAt_syl5Pair _ _ _ _ _ _ _ _ _ W2_0 W2_0_eq
    have hd1_eq : PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d1_z) =
        remDeg3_d1 q2s q1s q0s e3s e2s e1s := by
      simp only [CoverParams.d1_z, CoverParams.pmul, PairAlg.map_sub, PairAlg.map_mul,
        PairAlg.evalAt_sub, PairAlg.evalAt_mul _ _ W2_0 W2_0_eq, remDeg3_d1]; rfl
    have hd0_eq : PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d0_z) =
        remDeg3_d0 q2s q1s q0s e3s e2s e0s := by
      simp only [CoverParams.d0_z, CoverParams.pmul, PairAlg.map_sub, PairAlg.map_mul,
        PairAlg.evalAt_sub, PairAlg.evalAt_mul _ _ W2_0 W2_0_eq, remDeg3_d0]; rfl
    rw [hres_eq]
    exact valLead_syl5_of_rem hq2_L hq1_L hq0_L hd1_L hd0_L hd1_eq hd0_eq hcd_eq hq2_ne
  exact ⟨hd1_L, hd0_L, hcd_eq, hres_L, hcd_ne, hq2_ne⟩

lemma nm_z_coeff15_ne : (evalT k5Params.nm_z).coeff 15 ≠ 0 := by
  have hfac := nm_z_K5_factor
  have hc0_cb : cb_h_m_K5.coeff 0 ≠ 0 := by
    intro h0
    have hev : cb_h_m_K5.eval 0 = 0 := by rwa [← Polynomial.coeff_zero_eq_eval_zero]
    have hcb0 : k5Params.cb_h.eval 0 = 0 := by
      rw [cb_h_K5_eq_mul_monic, eval_mul, hev, mul_zero]
    exact eval_ne_zero_of_isCoprime (L := K5) isCoprime_cb_h_X
      (by simpa using hcb0) (by simp)
  have hc0_P34 : P34_K5.coeff 0 ≠ 0 := by
    intro h0
    have hev : P34_K5.eval 0 = 0 := by rwa [← Polynomial.coeff_zero_eq_eval_zero]
    exact eval_ne_zero_of_isCoprime (L := K5) isCoprime_P34_X
      (by simpa using hev) (by simp)
  have h15 : k5Params.nm_z.coeff 15 = lc34_K5 * cb_h_m_K5.coeff 0 ^ 12 * P34_K5.coeff 0 := by
    rw [hfac]
    have hmul : C lc34_K5 * X ^ 15 * cb_h_m_K5 ^ 12 * P34_K5 =
        X ^ 15 * (C lc34_K5 * cb_h_m_K5 ^ 12 * P34_K5) := by ring
    rw [hmul, Polynomial.coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self,
      Polynomial.coeff_zero_eq_eval_zero, eval_mul, eval_mul, eval_pow, eval_C,
      ← Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coeff_zero_eq_eval_zero]
  change (evalT k5Params.nm_z).coeff (15 : ℕ) ≠ 0
  rw [evalT_coeff, h15]
  exact mul_ne_zero (mul_ne_zero lc34_K5_ne_zero (pow_ne_zero 12 hc0_cb)) hc0_P34

lemma res_z_W1_0_val_ne :
    HasValGe 13 (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.res_z)) ∧
    (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.res_z)).coeff 13 ≠ 0 := by
  have hnm : evalT k5Params.nm_z =
      PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.res_z) *
      PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.res_z) := by
    rw [CoverParams.nm_z, CoverParams.pnm, PairAlg.map_nm]
    exact PairAlg.evalAt_nm _ _ W1_0 W2_0 W1_W2_0_sum W1_W2_0_prod _
  have h15 : HasValGe 15 (evalT k5Params.nm_z) := by
    intro n hn
    by_cases hneg : n < 0
    · exact HasValGe.evalT k5Params.nm_z n hneg
    · set m : ℕ := n.toNat
      have hnm' : n = (m : ℤ) := by omega
      rw [hnm', evalT_coeff]
      exact (Polynomial.X_pow_dvd_iff.mp X_pow_15_dvd_nm_z_K5) m (by omega)
  obtain ⟨_, _, _, hres2, hcd_ne, hq2_ne⟩ := W2_0_d1_d0_res
  have hr2_ne : (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.res_z)).coeff 2 ≠ 0 := by
    rw [hres2.c0]; exact div_ne_zero (pow_ne_zero 2 hcd_ne) hq2_ne
  have hres2_ne : PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.res_z) ≠ 0 :=
    fun h0 => hr2_ne (by rw [h0]; rfl)
  have hdiv : PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.res_z) =
      evalT k5Params.nm_z / PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.res_z) :=
    eq_div_of_mul_eq hres2_ne hnm.symm
  obtain ⟨hval, hc⟩ := h15.div_of_lead_ne hres2.val hr2_ne
  rw [← hdiv] at hval hc
  refine ⟨hval, ?_⟩
  rw [show (13 : ℤ) = 15 - 2 by omega, hc]
  exact div_ne_zero nm_z_coeff15_ne hr2_ne

/-- Generic `ValLead` transport for the 10 quadratic line-section numerators `numM mi`
with opaque series arguments (avoids unfolding transparent `set` bindings during `isDefEq`). -/
lemma numM_ValLead_of {k1 : ℤ} {a_s b_s ξS_s ξQ_s U V : LaurentSeries K5}
    {a0 b0 ξS0 ξQ0 a2_0 a1_0 a0_0 b2_0 b1_0 b0_0 : K5}
    (ha : ValLead 0 a_s a0) (hb : ValLead 0 b_s b0)
    (hξS : ValLead 0 ξS_s ξS0) (hξQ : ValLead 0 ξQ_s ξQ0)
    (ha2 : ValLead k1 (q1_a2 a_s b_s U V) a2_0)
    (ha1 : ValLead k1 (q1_a1 a_s b_s ξS_s ξQ_s U V) a1_0)
    (ha0 : ValLead k1 (q1_a0 ξS_s ξQ_s U V) a0_0)
    (hb2 : ValLead k1 (q2_b2 a_s b_s U V) b2_0)
    (hb1 : ValLead k1 (q2_b1 a_s b_s ξS_s ξQ_s U V) b1_0)
    (hb0 : ValLead k1 (q2_b0 ξS_s ξQ_s U V) b0_0) (mi : Fin 10) :
    ValLead (2 * k1) (numM mi a_s b_s ξS_s ξQ_s U V)
      (let (c2, c1, c0) : K5 × K5 × K5 := match mi with
        | 0 => (a0 ^ 2, 2 * a0 * ξS0, ξS0 ^ 2)
        | 1 => (a0 * b0, a0 * ξQ0 + b0 * ξS0, ξS0 * ξQ0)
        | 2 => (b0 ^ 2, 2 * b0 * ξQ0, ξQ0 ^ 2)
        | 3 => (a0, ξS0, 0)
        | 4 => (0, a0, ξS0)
        | 5 => (b0, ξQ0, 0)
        | 6 => (0, b0, ξQ0)
        | 7 => (1, 0, 0)
        | 8 => (0, 1, 0)
        | 9 => (0, 0, 1)
       (1 / 16 : K5) * (c2 * (a1_0 * b0_0 - a0_0 * b1_0) -
         c1 * (a2_0 * b0_0 - a0_0 * b2_0) + c0 * (a2_0 * b1_0 - a1_0 * b2_0))) := by
  have hd20 := ((ha2.mul hb0).sub (ha0.mul hb2)).eq_k (k' := 2 * k1) (by omega)
  have hd21 := ((ha2.mul hb1).sub (ha1.mul hb2)).eq_k (k' := 2 * k1) (by omega)
  have hd10 := ((ha1.mul hb0).sub (ha0.mul hb1)).eq_k (k' := 2 * k1) (by omega)
  have hc16 : ValLead 0 (1 / 16 : LaurentSeries K5) (1 / 16 : K5) := by
    rw [show (1 / 16 : LaurentSeries K5) = HahnSeries.C (1 / 16 : K5) by simp only [map_div₀, map_ofNat, map_one]]
    exact ValLead.of_C _
  have hcomb {m2 m1 m0 : LaurentSeries K5} {c2 c1 c0 : K5}
      (hm2 : ValLead 0 m2 c2) (hm1 : ValLead 0 m1 c1) (hm0 : ValLead 0 m0 c0) :
      ValLead (2 * k1) ((1 / 16 : LaurentSeries K5) * (m2 * (q1_a1 a_s b_s ξS_s ξQ_s U V * q2_b0 ξS_s ξQ_s U V -
        q1_a0 ξS_s ξQ_s U V * q2_b1 a_s b_s ξS_s ξQ_s U V) -
        m1 * (q1_a2 a_s b_s U V * q2_b0 ξS_s ξQ_s U V - q1_a0 ξS_s ξQ_s U V * q2_b2 a_s b_s U V) +
        m0 * (q1_a2 a_s b_s U V * q2_b1 a_s b_s ξS_s ξQ_s U V - q1_a1 a_s b_s ξS_s ξQ_s U V * q2_b2 a_s b_s U V)))
        ((1 / 16 : K5) * (c2 * (a1_0 * b0_0 - a0_0 * b1_0) -
          c1 * (a2_0 * b0_0 - a0_0 * b2_0) + c0 * (a2_0 * b1_0 - a1_0 * b2_0))) :=
    (hc16.mul ((((hm2.mul hd10).eq_k (k' := 2 * k1) (by omega)).sub
      ((hm1.mul hd20).eq_k (k' := 2 * k1) (by omega))).add
      ((hm0.mul hd21).eq_k (k' := 2 * k1) (by omega)))).eq_k (k' := 2 * k1) (by omega)
  have h0L : ValLead 0 (0 : LaurentSeries K5) (0 : K5) := by simpa only [map_zero] using ValLead.of_C (0 : K5)
  have h1L : ValLead 0 (1 : LaurentSeries K5) (1 : K5) := by simpa only [map_one] using ValLead.of_C (1 : K5)
  have h2L : ValLead 0 (2 : LaurentSeries K5) (2 : K5) := by simpa only [one_add_one_eq_two] using h1L.add h1L
  fin_cases mi
  · dsimp only [numM]; exact hcomb ((ha.pow 2).eq_k (k' := 0) (by omega)) (((h2L.mul ha).mul hξS).eq_k (k' := 0) (by omega)) ((hξS.pow 2).eq_k (k' := 0) (by omega))
  · dsimp only [numM]; exact hcomb ((ha.mul hb).eq_k (k' := 0) (by omega)) (((ha.mul hξQ).eq_k (k' := 0) (by omega)).add ((hb.mul hξS).eq_k (k' := 0) (by omega))) ((hξS.mul hξQ).eq_k (k' := 0) (by omega))
  · dsimp only [numM]; exact hcomb ((hb.pow 2).eq_k (k' := 0) (by omega)) (((h2L.mul hb).mul hξQ).eq_k (k' := 0) (by omega)) ((hξQ.pow 2).eq_k (k' := 0) (by omega))
  · dsimp only [numM]; exact hcomb ha hξS h0L
  · dsimp only [numM]; exact hcomb h0L ha hξS
  · dsimp only [numM]; exact hcomb hb hξQ h0L
  · dsimp only [numM]; exact hcomb h0L hb hξQ
  · dsimp only [numM]; exact hcomb h1L h0L h0L
  · dsimp only [numM]; exact hcomb h0L h1L h0L
  · dsimp only [numM]; exact hcomb h0L h0L h1L

/-- Generic `ValDual` transport for the 10 quadratic line-section numerators `numM mi`
with opaque series arguments (avoids unfolding transparent `set` bindings during `isDefEq`). -/
lemma numM_ValDual_of {k1 : ℤ} {a_s b_s ξS_s ξQ_s U V : LaurentSeries K5}
    {aD bD ξSD ξQD a2D a1D a0D b2D b1D b0D : Dual K5}
    (ha : ValDual 0 a_s aD) (hb : ValDual 0 b_s bD)
    (hξS : ValDual 0 ξS_s ξSD) (hξQ : ValDual 0 ξQ_s ξQD)
    (ha2 : ValDual k1 (q1_a2 a_s b_s U V) a2D)
    (ha1 : ValDual k1 (q1_a1 a_s b_s ξS_s ξQ_s U V) a1D)
    (ha0 : ValDual k1 (q1_a0 ξS_s ξQ_s U V) a0D)
    (hb2 : ValDual k1 (q2_b2 a_s b_s U V) b2D)
    (hb1 : ValDual k1 (q2_b1 a_s b_s ξS_s ξQ_s U V) b1D)
    (hb0 : ValDual k1 (q2_b0 ξS_s ξQ_s U V) b0D) (mi : Fin 10) :
    ValDual (2 * k1) (numM mi a_s b_s ξS_s ξQ_s U V)
      (let (c2, c1, c0) : Dual K5 × Dual K5 × Dual K5 := match mi with
        | 0 => (aD ^ 2, 2 * aD * ξSD, ξSD ^ 2)
        | 1 => (aD * bD, aD * ξQD + bD * ξSD, ξSD * ξQD)
        | 2 => (bD ^ 2, 2 * bD * ξQD, ξQD ^ 2)
        | 3 => (aD, ξSD, 0)
        | 4 => (0, aD, ξSD)
        | 5 => (bD, ξQD, 0)
        | 6 => (0, bD, ξQD)
        | 7 => (1, 0, 0)
        | 8 => (0, 1, 0)
        | 9 => (0, 0, 1)
       Dual.C (1 / 16 : K5) * (c2 * (a1D * b0D - a0D * b1D) -
         c1 * (a2D * b0D - a0D * b2D) + c0 * (a2D * b1D - a1D * b2D))) := by
  have hd20 := ((ha2.mul hb0).sub (ha0.mul hb2)).eq_k (k' := 2 * k1) (by omega)
  have hd21 := ((ha2.mul hb1).sub (ha1.mul hb2)).eq_k (k' := 2 * k1) (by omega)
  have hd10 := ((ha1.mul hb0).sub (ha0.mul hb1)).eq_k (k' := 2 * k1) (by omega)
  have hc16 : ValDual 0 (1 / 16 : LaurentSeries K5) (Dual.C (1 / 16 : K5)) := by
    rw [show (1 / 16 : LaurentSeries K5) = HahnSeries.C (1 / 16 : K5) by simp only [map_div₀, map_ofNat, map_one]]
    exact ValDual.of_C _
  have hcomb {m2 m1 m0 : LaurentSeries K5} {c2 c1 c0 : Dual K5}
      (hm2 : ValDual 0 m2 c2) (hm1 : ValDual 0 m1 c1) (hm0 : ValDual 0 m0 c0) :
      ValDual (2 * k1) ((1 / 16 : LaurentSeries K5) * (m2 * (q1_a1 a_s b_s ξS_s ξQ_s U V * q2_b0 ξS_s ξQ_s U V -
        q1_a0 ξS_s ξQ_s U V * q2_b1 a_s b_s ξS_s ξQ_s U V) -
        m1 * (q1_a2 a_s b_s U V * q2_b0 ξS_s ξQ_s U V - q1_a0 ξS_s ξQ_s U V * q2_b2 a_s b_s U V) +
        m0 * (q1_a2 a_s b_s U V * q2_b1 a_s b_s ξS_s ξQ_s U V - q1_a1 a_s b_s ξS_s ξQ_s U V * q2_b2 a_s b_s U V)))
        (Dual.C (1 / 16 : K5) * (c2 * (a1D * b0D - a0D * b1D) -
          c1 * (a2D * b0D - a0D * b2D) + c0 * (a2D * b1D - a1D * b2D))) :=
    (hc16.mul ((((hm2.mul hd10).eq_k (k' := 2 * k1) (by omega)).sub
      ((hm1.mul hd20).eq_k (k' := 2 * k1) (by omega))).add
      ((hm0.mul hd21).eq_k (k' := 2 * k1) (by omega)))).eq_k (k' := 2 * k1) (by omega)
  have h0D : ValDual 0 (0 : LaurentSeries K5) (0 : Dual K5) := by simpa only [map_zero] using ValDual.of_C (0 : K5)
  have h1D : ValDual 0 (1 : LaurentSeries K5) (1 : Dual K5) := by simpa only [map_one] using ValDual.of_C (1 : K5)
  have h2D : ValDual 0 (2 : LaurentSeries K5) (2 : Dual K5) := by simpa only [one_add_one_eq_two] using h1D.add h1D
  fin_cases mi
  · dsimp only [numM]; exact hcomb ((ha.pow 2).eq_k (k' := 0) (by omega)) (((h2D.mul ha).mul hξS).eq_k (k' := 0) (by omega)) ((hξS.pow 2).eq_k (k' := 0) (by omega))
  · dsimp only [numM]; exact hcomb ((ha.mul hb).eq_k (k' := 0) (by omega)) (((ha.mul hξQ).eq_k (k' := 0) (by omega)).add ((hb.mul hξS).eq_k (k' := 0) (by omega))) ((hξS.mul hξQ).eq_k (k' := 0) (by omega))
  · dsimp only [numM]; exact hcomb ((hb.pow 2).eq_k (k' := 0) (by omega)) (((h2D.mul hb).mul hξQ).eq_k (k' := 0) (by omega)) ((hξQ.pow 2).eq_k (k' := 0) (by omega))
  · dsimp only [numM]; exact hcomb ha hξS h0D
  · dsimp only [numM]; exact hcomb h0D ha hξS
  · dsimp only [numM]; exact hcomb hb hξQ h0D
  · dsimp only [numM]; exact hcomb h0D hb hξQ
  · dsimp only [numM]; exact hcomb h1D h0D h0D
  · dsimp only [numM]; exact hcomb h0D h1D h0D
  · dsimp only [numM]; exact hcomb h0D h0D h1D

lemma A0U_ValLead_of {k : ℤ} {a_s b_s ξS_s ξQ_s U V : LaurentSeries K5}
    {c : Fin 10 → K5} (hm : ∀ i, ValLead k (numM i a_s b_s ξS_s ξQ_s U V) (c i)) :
    ValLead k (A_0U a_s b_s ξS_s ξQ_s U V)
      (-(19708 / 1257375 : K5) * (5 * c 0 - 9 * c 1) +
       (1472 / 1257375 : K5) * (5 * c 1 - 9 * c 2) -
       (16 / 729 : K5) * (5 * c 3 - 9 * c 5) +
       (188 / 2025 : K5) * (5 * c 4 - 9 * c 6)) := by
  unfold A_0U
  have hC (r : K5) {f : LaurentSeries K5} {a : K5} (hf : ValLead k f a) :
      ValLead k (HahnSeries.C r * f) (r * a) := ((ValLead.of_C r).mul hf).eq_k (k' := k) (by omega)
  have hpair (i j : Fin 10) :
      ValLead k (5 * numM i a_s b_s ξS_s ξQ_s U V - 9 * numM j a_s b_s ξS_s ξQ_s U V)
        (5 * c i - 9 * c j) := by
    have h5 : ValLead k (5 * numM i a_s b_s ξS_s ξQ_s U V) (5 * c i) := by
      simpa only [map_ofNat] using hC 5 (hm i)
    have h9 : ValLead k (9 * numM j a_s b_s ξS_s ξQ_s U V) (9 * c j) := by
      simpa only [map_ofNat] using hC 9 (hm j)
    exact h5.sub h9
  simpa only [map_div₀, map_neg, map_ofNat] using
    (((hC (-(19708 / 1257375 : K5)) (hpair 0 1)).add
      (hC (1472 / 1257375 : K5) (hpair 1 2))).sub
      (hC (16 / 729 : K5) (hpair 3 5))).add
      (hC (188 / 2025 : K5) (hpair 4 6))

lemma A0V_ValLead_of {k : ℤ} {a_s b_s ξS_s ξQ_s U V : LaurentSeries K5}
    {c : Fin 10 → K5} (hm : ∀ i, ValLead k (numM i a_s b_s ξS_s ξQ_s U V) (c i)) :
    ValLead k (A_0V a_s b_s ξS_s ξQ_s U V)
      (-(892 / 3645 : K5) * (5 * c 3 - 9 * c 4) +
       (40 / 81 : K5) * (5 * c 5 - 9 * c 6) -
       (112 / 2395 : K5) * (5 * c 7 - 9 * c 8) +
       (392 / 11975 : K5) * (5 * c 8 - 9 * c 9)) := by
  unfold A_0V
  have hC (r : K5) {f : LaurentSeries K5} {a : K5} (hf : ValLead k f a) :
      ValLead k (HahnSeries.C r * f) (r * a) := ((ValLead.of_C r).mul hf).eq_k (k' := k) (by omega)
  have hpair (i j : Fin 10) :
      ValLead k (5 * numM i a_s b_s ξS_s ξQ_s U V - 9 * numM j a_s b_s ξS_s ξQ_s U V)
        (5 * c i - 9 * c j) := by
    have h5 : ValLead k (5 * numM i a_s b_s ξS_s ξQ_s U V) (5 * c i) := by
      simpa only [map_ofNat] using hC 5 (hm i)
    have h9 : ValLead k (9 * numM j a_s b_s ξS_s ξQ_s U V) (9 * c j) := by
      simpa only [map_ofNat] using hC 9 (hm j)
    exact h5.sub h9
  simpa only [map_div₀, map_neg, map_ofNat] using
    (((hC (-(892 / 3645 : K5)) (hpair 3 4)).add
      (hC (40 / 81 : K5) (hpair 5 6))).sub
      (hC (112 / 2395 : K5) (hpair 7 8))).add
      (hC (392 / 11975 : K5) (hpair 8 9))

lemma A0U_ValDual_of {k : ℤ} {a_s b_s ξS_s ξQ_s U V : LaurentSeries K5}
    {d : Fin 10 → Dual K5} (hm : ∀ i, ValDual k (numM i a_s b_s ξS_s ξQ_s U V) (d i)) :
    ValDual k (A_0U a_s b_s ξS_s ξQ_s U V)
      (Dual.C (-(19708 / 1257375 : K5)) * (5 * d 0 - 9 * d 1) +
       Dual.C (1472 / 1257375 : K5) * (5 * d 1 - 9 * d 2) -
       Dual.C (16 / 729 : K5) * (5 * d 3 - 9 * d 5) +
       Dual.C (188 / 2025 : K5) * (5 * d 4 - 9 * d 6)) := by
  unfold A_0U
  have hC (r : K5) {f : LaurentSeries K5} {x : Dual K5} (hf : ValDual k f x) :
      ValDual k (HahnSeries.C r * f) (Dual.C r * x) := ((ValDual.of_C r).mul hf).eq_k (k' := k) (by omega)
  have h1v : (1 : Dual K5).val = 1 := rfl
  have h1e : (1 : Dual K5).eps = 0 := rfl
  have hC5 : Dual.C (5 : K5) = (5 : Dual K5) := by
    ext
    · change (5 : K5) = (5 : Dual K5).val
      rw [show (5 : Dual K5) = 1 + 1 + 1 + 1 + 1 by ring]; simp only [Dual.add_val, h1v]; ring
    · change (0 : K5) = (5 : Dual K5).eps
      rw [show (5 : Dual K5) = 1 + 1 + 1 + 1 + 1 by ring]; simp only [Dual.add_eps, h1e]; ring
  have hC9 : Dual.C (9 : K5) = (9 : Dual K5) := by
    ext
    · change (9 : K5) = (9 : Dual K5).val
      rw [show (9 : Dual K5) = 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by ring]; simp only [Dual.add_val, h1v]; ring
    · change (0 : K5) = (9 : Dual K5).eps
      rw [show (9 : Dual K5) = 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by ring]; simp only [Dual.add_eps, h1e]; ring
  have hpair (i j : Fin 10) :
      ValDual k (5 * numM i a_s b_s ξS_s ξQ_s U V - 9 * numM j a_s b_s ξS_s ξQ_s U V)
        (5 * d i - 9 * d j) := by
    have h5 : ValDual k (5 * numM i a_s b_s ξS_s ξQ_s U V) (5 * d i) := by
      simpa only [map_ofNat, hC5] using hC 5 (hm i)
    have h9 : ValDual k (9 * numM j a_s b_s ξS_s ξQ_s U V) (9 * d j) := by
      simpa only [map_ofNat, hC9] using hC 9 (hm j)
    exact h5.sub h9
  simpa only [map_div₀, map_neg, map_ofNat] using
    (((hC (-(19708 / 1257375 : K5)) (hpair 0 1)).add
      (hC (1472 / 1257375 : K5) (hpair 1 2))).sub
      (hC (16 / 729 : K5) (hpair 3 5))).add
      (hC (188 / 2025 : K5) (hpair 4 6))

private lemma numM_pair0_eq_zero {S : Type*} [CommRing S] (a b xS xQ w u1 u0 : S) :
    let dHS0 := fun s q => -25 * (5 * s - 9 * q) * (15 * s - 9 * q) * w
    let dHQ0 := fun s q => 50 * s * (5 * s - 9 * q) * w
    let a2 := dHS0 a b
    let a0 := dHS0 xS xQ
    let a1 := dHS0 (a + xS) (b + xQ) - a2 - a0
    let b2 := dHQ0 a b
    let b0 := dHQ0 xS xQ
    let b1 := dHQ0 (a + xS) (b + xQ) - b2 - b0
    let d20 := a2 * b0 - a0 * b2
    let d21 := a2 * b1 - a1 * b2
    let d10 := a1 * b0 - a0 * b1
    (u1 * (5 * a - 9 * b)) * d10 - (u1 * (5 * xS - 9 * xQ) + u0 * (5 * a - 9 * b)) * d20 +
      (u0 * (5 * xS - 9 * xQ)) * d21 = 0 := by
  dsimp only; ring

private lemma A0U_at_zero {R : Type*} [Field R] (a b xS xQ w : R) :
    A_0U a b xS xQ 0 w = 0 := by
  simp only [A_0U, numM, q1_a2, q1_a1, q1_a0, q2_b2, q2_b1, q2_b0, dH_dS, dH_dQ]; ring

private lemma AY_t1_at_zero {R : Type*} [Field R] (a b xS xQ w : R) :
    25 * numM 3 a b xS xQ 0 w - 45 * numM 4 a b xS xQ 0 w -
    45 * numM 5 a b xS xQ 0 w + 81 * numM 6 a b xS xQ 0 w = 0 := by
  simp only [numM, q1_a2, q1_a1, q1_a0, q2_b2, q2_b1, q2_b0, dH_dS, dH_dQ]; ring

private lemma A0V_at_zero_xiS0 {R : Type*} [Field R] [CharZero R] (a b xQ w : R)
    (hrel : 5 * a - 9 * b = 5 * xQ) :
    A_0V a b 0 xQ 0 w = 0 := by
  have hxQ : xQ = a - (9 / 5 : R) * b := by
    have h5 : (5 : R) ≠ 0 := by exact_mod_cast (by decide : (5 : ℕ) ≠ 0)
    apply mul_left_cancel₀ h5
    linear_combination -hrel
  rw [hxQ]
  simp only [A_0V, numM, q1_a2, q1_a1, q1_a0, q2_b2, q2_b1, q2_b0, dH_dS, dH_dQ]
  ring

private lemma QY_num_00_factor {R : Type*} [Field R] [CharZero R] (S Q T x y a b : R) :
    (5 * S - 9 * Q) * (5 * T - 9) * dot_ab (QY_num S Q T x y 0 0) a b =
    4 * y * (-25 * S + 45 * Q + 27 * x) * S ^ 2 * T ^ 2 * DY2_of T y *
      ((-(25 / 81 : R) * (5 * S - 9 * Q) * (5 * S - 3 * Q)) * a * (-T * (5 * T - 9) ^ 2) +
       ((50 / 27 : R) * S * (5 * S - 9 * Q)) * b * (-T * (5 * T - 9) ^ 2) +
       S * (5 * S - 9 * Q) ^ 2 * (-(25 / 81 : R) * (5 * T - 9) * (5 * T - 3))) := by
  simp only [dot_ab, QY_num, Omega_F, dDX2_F, F_contract, dF5_fn, dH0_fn, dDX2_fn,
    u3_of, v3_of, om_fn, br_fn, LX_of, LY_of, dLX_fn, dLY_fn, u_of, v_of]
  ring

private lemma QX_num_00_factor {R : Type*} [Field R] [CharZero R] (S Q T x y a b : R) :
    (5 * S - 9 * Q) * (5 * T - 9) * dot_ab (QX_num S Q T x y 0 0) a b =
    4 * x * (-25 * T + 45 + 27 * y) * S ^ 2 * T ^ 2 * DX2_of S Q x *
      ((-(25 / 81 : R) * (5 * S - 9 * Q) * (5 * S - 3 * Q)) * a * (-T * (5 * T - 9) ^ 2) +
       ((50 / 27 : R) * S * (5 * S - 9 * Q)) * b * (-T * (5 * T - 9) ^ 2) +
       S * (5 * S - 9 * Q) ^ 2 * (-(25 / 81 : R) * (5 * T - 9) * (5 * T - 3))) := by
  simp only [dot_ab, QX_num, Omega_F, dDY2_F, F_contract, dF5_fn, dH0_fn, dDY2_fn,
    u3_of, v3_of, om_fn, br_fn, LX_of, LY_of, dLX_fn, dLY_fn, u_of, v_of]
  ring

private lemma dual_det_split {R : Type*} [CommRing R] (A1 A2 B1 B2 : Dual R) (da1 da2 db1 db2 : R) :
    (A1 + ⟨0, da1⟩) * (B2 + ⟨0, db2⟩) - (A2 + ⟨0, da2⟩) * (B1 + ⟨0, db1⟩) =
    (A1 * B2 - A2 * B1) + ⟨0, A1.val * db2 + da1 * B2.val - A2.val * db1 - da2 * B1.val⟩ := by
  ext <;> simp only [Dual.add_val, Dual.sub_val, Dual.mul_val, Dual.add_eps, Dual.sub_eps, Dual.mul_eps] <;> ring

private lemma dual_mul_eps0 {R : Type*} [CommRing R] (m : Dual R) (e : R) :
    m * ⟨0, e⟩ = ⟨0, m.val * e⟩ := by
  ext <;> simp only [Dual.mul_val, Dual.mul_eps] <;> ring

private lemma dual_minor_pair_eq {R : Type*} [Field R]
    (aD bD xSD xQD wD u1 u0 : Dual R) (da2 da1 da0 db2 db1 db0 : R) :
    let dHS0 := fun s q : Dual R => Dual.C (-(25 / 243 : R)) * (5 * s - 9 * q) * (15 * s - 9 * q) * wD
    let dHQ0 := fun s q : Dual R => Dual.C (50 / 27 : R) * s * (5 * s - 9 * q) * wD
    let A2 := dHS0 aD bD
    let A0 := dHS0 xSD xQD
    let A1 := dHS0 (aD + xSD) (bD + xQD) - A2 - A0
    let B2 := dHQ0 aD bD
    let B0 := dHQ0 xSD xQD
    let B1 := dHQ0 (aD + xSD) (bD + xQD) - B2 - B0
    let a2 := A2 + ⟨0, da2⟩
    let a1 := A1 + ⟨0, da1⟩
    let a0 := A0 + ⟨0, da0⟩
    let b2 := B2 + ⟨0, db2⟩
    let b1 := B1 + ⟨0, db1⟩
    let b0 := B0 + ⟨0, db0⟩
    let d20 := a2 * b0 - a0 * b2
    let d21 := a2 * b1 - a1 * b2
    let d10 := a1 * b0 - a0 * b1
    let m2 := u1 * (5 * aD - 9 * bD)
    let m1 := u1 * (5 * xSD - 9 * xQD) + u0 * (5 * aD - 9 * bD)
    let m0 := u0 * (5 * xSD - 9 * xQD)
    m2 * d10 - m1 * d20 + m0 * d21 =
      ⟨0, m2.val * (A1.val * db0 + da1 * B0.val - A0.val * db1 - da0 * B1.val) -
          m1.val * (A2.val * db0 + da2 * B0.val - A0.val * db2 - da0 * B2.val) +
          m0.val * (A2.val * db1 + da2 * B1.val - A1.val * db2 - da1 * B2.val)⟩ := by
  dsimp only
  set dHS0 : Dual R → Dual R → Dual R := fun s q => Dual.C (-(25 / 243 : R)) * (5 * s - 9 * q) * (15 * s - 9 * q) * wD
  set dHQ0 : Dual R → Dual R → Dual R := fun s q => Dual.C (50 / 27 : R) * s * (5 * s - 9 * q) * wD
  set A2 := dHS0 aD bD
  set A0 := dHS0 xSD xQD
  set A1 := dHS0 (aD + xSD) (bD + xQD) - A2 - A0
  set B2 := dHQ0 aD bD
  set B0 := dHQ0 xSD xQD
  set B1 := dHQ0 (aD + xSD) (bD + xQD) - B2 - B0
  set m2 := u1 * (5 * aD - 9 * bD)
  set m1 := u1 * (5 * xSD - 9 * xQD) + u0 * (5 * aD - 9 * bD)
  set m0 := u0 * (5 * xSD - 9 * xQD)
  rw [dual_det_split A1 A0 B1 B0 da1 da0 db1 db0,
      dual_det_split A2 A0 B2 B0 da2 da0 db2 db0,
      dual_det_split A2 A1 B2 B1 da2 da1 db2 db1]
  simp only [mul_add, dual_mul_eps0]
  have h0 : m2 * (A1 * B0 - A0 * B1) - m1 * (A2 * B0 - A0 * B2) + m0 * (A2 * B1 - A1 * B2) = 0 := by
    have hc1 : Dual.C (-(25 / 243 : R)) = Dual.C (1 / 243 : R) * (-25 : Dual R) := by
      rw [← map_ofNat Dual.C 25, ← map_neg Dual.C, ← map_mul Dual.C]; congr 1; ring
    have hc2 : Dual.C (50 / 27 : R) = Dual.C (1 / 27 : R) * (50 : Dual R) := by
      rw [← map_ofNat Dual.C 50, ← map_mul Dual.C]; congr 1; ring
    have hA (s q : Dual R) : dHS0 s q = Dual.C (1 / 243 : R) * (-25 * (5 * s - 9 * q) * (15 * s - 9 * q) * wD) := by
      simp only [dHS0, hc1]; ring
    have hB (s q : Dual R) : dHQ0 s q = Dual.C (1 / 27 : R) * (50 * s * (5 * s - 9 * q) * wD) := by
      simp only [dHQ0, hc2]; ring
    have hmul : m2 * (A1 * B0 - A0 * B1) - m1 * (A2 * B0 - A0 * B2) + m0 * (A2 * B1 - A1 * B2) =
        Dual.C (1 / 243 : R) * Dual.C (1 / 27 : R) *
        (let fS := fun s q : Dual R => -25 * (5 * s - 9 * q) * (15 * s - 9 * q) * wD
         let fQ := fun s q : Dual R => 50 * s * (5 * s - 9 * q) * wD
         let x2 := fS aD bD; let x0 := fS xSD xQD; let x1 := fS (aD + xSD) (bD + xQD) - x2 - x0
         let y2 := fQ aD bD; let y0 := fQ xSD xQD; let y1 := fQ (aD + xSD) (bD + xQD) - y2 - y0
         m2 * (x1 * y0 - x0 * y1) - m1 * (x2 * y0 - x0 * y2) + m0 * (x2 * y1 - x1 * y2)) := by
      dsimp only [A2, A1, A0, B2, B1, B0]
      simp only [hA, hB]; ring
    rw [hmul, show (let fS := fun s q : Dual R => -25 * (5 * s - 9 * q) * (15 * s - 9 * q) * wD
         let fQ := fun s q : Dual R => 50 * s * (5 * s - 9 * q) * wD
         let x2 := fS aD bD; let x0 := fS xSD xQD; let x1 := fS (aD + xSD) (bD + xQD) - x2 - x0
         let y2 := fQ aD bD; let y0 := fQ xSD xQD; let y1 := fQ (aD + xSD) (bD + xQD) - y2 - y0
         m2 * (x1 * y0 - x0 * y1) - m1 * (x2 * y0 - x0 * y2) + m0 * (x2 * y1 - x1 * y2)) = 0 from
      numM_pair0_eq_zero aD bD xSD xQD wD u1 u0, mul_zero]
  calc m2 * (A1 * B0 - A0 * B1) + ⟨0, m2.val * (A1.val * db0 + da1 * B0.val - A0.val * db1 - da0 * B1.val)⟩ -
        (m1 * (A2 * B0 - A0 * B2) + ⟨0, m1.val * (A2.val * db0 + da2 * B0.val - A0.val * db2 - da0 * B2.val)⟩) +
        (m0 * (A2 * B1 - A1 * B2) + ⟨0, m0.val * (A2.val * db1 + da2 * B1.val - A1.val * db2 - da1 * B2.val)⟩)
      = (m2 * (A1 * B0 - A0 * B1) - m1 * (A2 * B0 - A0 * B2) + m0 * (A2 * B1 - A1 * B2)) +
        ⟨0, m2.val * (A1.val * db0 + da1 * B0.val - A0.val * db1 - da0 * B1.val) -
            m1.val * (A2.val * db0 + da2 * B0.val - A0.val * db2 - da0 * B2.val) +
            m0.val * (A2.val * db1 + da2 * B1.val - A1.val * db2 - da1 * B2.val)⟩ := by
        ext <;> simp only [Dual.add_val, Dual.sub_val, Dual.add_eps, Dual.sub_eps] <;> ring
    _ = ⟨0, m2.val * (A1.val * db0 + da1 * B0.val - A0.val * db1 - da0 * B1.val) -
            m1.val * (A2.val * db0 + da2 * B0.val - A0.val * db2 - da0 * B2.val) +
            m0.val * (A2.val * db1 + da2 * B1.val - A1.val * db2 - da1 * B2.val)⟩ := by
        rw [h0, zero_add]

private lemma dual_minor_pair_eq_const {R : Type*} [Field R]
    (aD bD xSD xQD wD u1 u0 : Dual R) (da2 da1 da0 db2 db1 db0 : R) :
    let mk := fun (a b xS xQ w u1' u0' : Dual R) =>
      let dHS0 := fun s q : Dual R => Dual.C (-(25 / 243 : R)) * (5 * s - 9 * q) * (15 * s - 9 * q) * w
      let dHQ0 := fun s q : Dual R => Dual.C (50 / 27 : R) * s * (5 * s - 9 * q) * w
      let A2 := dHS0 a b; let A0 := dHS0 xS xQ; let A1 := dHS0 (a + xS) (b + xQ) - A2 - A0
      let B2 := dHQ0 a b; let B0 := dHQ0 xS xQ; let B1 := dHQ0 (a + xS) (b + xQ) - B2 - B0
      let a2 := A2 + ⟨0, da2⟩; let a1 := A1 + ⟨0, da1⟩; let a0 := A0 + ⟨0, da0⟩
      let b2 := B2 + ⟨0, db2⟩; let b1 := B1 + ⟨0, db1⟩; let b0 := B0 + ⟨0, db0⟩
      let d20 := a2 * b0 - a0 * b2; let d21 := a2 * b1 - a1 * b2; let d10 := a1 * b0 - a0 * b1
      let m2 := u1' * (5 * a - 9 * b)
      let m1 := u1' * (5 * xS - 9 * xQ) + u0' * (5 * a - 9 * b)
      let m0 := u0' * (5 * xS - 9 * xQ)
      m2 * d10 - m1 * d20 + m0 * d21
    mk aD bD xSD xQD wD u1 u0 =
      ⟨0, (mk (Dual.C aD.val) (Dual.C bD.val) (Dual.C xSD.val) (Dual.C xQD.val)
        (Dual.C wD.val) (Dual.C u1.val) (Dual.C u0.val)).eps⟩ := by
  dsimp only
  rw [dual_minor_pair_eq aD bD xSD xQD wD u1 u0 da2 da1 da0 db2 db1 db0,
      dual_minor_pair_eq (Dual.C aD.val) (Dual.C bD.val) (Dual.C xSD.val) (Dual.C xQD.val)
        (Dual.C wD.val) (Dual.C u1.val) (Dual.C u0.val) da2 da1 da0 db2 db1 db0]
  congr 1

lemma EB_bilinear_UV {R : Type*} [Field R] [CharZero R] (S Q T x y U V : R) :
    EB_of S Q T x y U V =
      EB_of S Q T x y 0 0 +
      (EB_of S Q T x y 0 1 - EB_of S Q T x y 0 0) * V +
      (EB_of S Q T x y 1 0 - EB_of S Q T x y 0 0) * U +
      (EB_of S Q T x y 1 1 - EB_of S Q T x y 1 0 - EB_of S Q T x y 0 1 + EB_of S Q T x y 0 0) * U * V := by
  simp only [EB_of, br_fn, LX_of, LY_of, dLX_fn, dLY_fn, u_of, v_of]
  ring

lemma QY_bilinear_UV {R : Type*} [Field R] [CharZero R] (S Q T x y U V : R) (i : Fin 3) :
    QY_num S Q T x y U V i =
      QY_num S Q T x y 0 0 i +
      (QY_num S Q T x y 0 1 i - QY_num S Q T x y 0 0 i) * V +
      (QY_num S Q T x y 1 0 i - QY_num S Q T x y 0 0 i) * U +
      (QY_num S Q T x y 1 1 i - QY_num S Q T x y 1 0 i - QY_num S Q T x y 0 1 i + QY_num S Q T x y 0 0 i) * U * V := by
  fin_cases i <;>
    (simp only [QY_num, Omega_F, dDX2_F, F_contract, om_fn, br_fn, LX_of, LY_of, dLX_fn, dLY_fn, u_of, v_of]; ring)

lemma QX_bilinear_UV {R : Type*} [Field R] [CharZero R] (S Q T x y U V : R) (i : Fin 3) :
    QX_num S Q T x y U V i =
      QX_num S Q T x y 0 0 i +
      (QX_num S Q T x y 0 1 i - QX_num S Q T x y 0 0 i) * V +
      (QX_num S Q T x y 1 0 i - QX_num S Q T x y 0 0 i) * U +
      (QX_num S Q T x y 1 1 i - QX_num S Q T x y 1 0 i - QX_num S Q T x y 0 1 i + QX_num S Q T x y 0 0 i) * U * V := by
  fin_cases i <;>
    (simp only [QX_num, Omega_F, dDY2_F, F_contract, om_fn, br_fn, LX_of, LY_of, dLX_fn, dLY_fn, u_of, v_of]; ring)

private lemma QX_num_01_sub_00_factor {R : Type*} [Field R] [CharZero R] (S Q T x y a b : R) :
    (T - 3) * ((QX_num S Q T x y 0 1 0 - QX_num S Q T x y 0 0 0) * a +
      (QX_num S Q T x y 0 1 1 - QX_num S Q T x y 0 0 1) * b +
      (QX_num S Q T x y 0 1 2 - QX_num S Q T x y 0 0 2)) =
    (80 / 81 : R) * x * T ^ 2 * S ^ 2 * (T - 3) ^ 3 *
      (23 * S ^ 3 - 82 * S ^ 2 * Q + 71 * S * Q ^ 2 + 4 * Q ^ 3 -
        50 * S ^ 2 * x + 90 * S * Q * x + 27 * S * x ^ 2) *
      ((T - 3) * (-(5 * S - 3 * Q) * a + 6 * S * b) + S * (5 * S - 9 * Q)) := by
  simp only [QX_num, Omega_F, dDY2_F, F_contract, dF5_fn, dH0_fn, dDY2_fn, DX2_of, DY2_of,
    om_fn, br_fn, LX_of, LY_of, dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of]
  ring

/-! ### Section 3: Branch 1 (`W1_0`) Vanishing Residue `(br1_0 eta_AC).coeff (-1) = 0` -/

private lemma hasValGe_div_nat_mul {k : ℤ} {f : LaurentSeries K5} (p q : ℕ) (hf : HasValGe k f) :
    HasValGe k (((p : LaurentSeries K5) / (q : LaurentSeries K5)) * f) := by
  rw [show ((p : LaurentSeries K5) / (q : LaurentSeries K5)) = HahnSeries.C ((p : K5) / (q : K5)) by
    simp only [map_div₀, map_natCast]]
  exact ((HasValGe.of_C _).mul hf).mono (by omega)

private lemma hasValGe_neg_div_nat_mul {k : ℤ} {f : LaurentSeries K5} (p q : ℕ) (hf : HasValGe k f) :
    HasValGe k (-((p : LaurentSeries K5) / (q : LaurentSeries K5)) * f) := by
  rw [show -((p : LaurentSeries K5) / (q : LaurentSeries K5)) = HahnSeries.C (-((p : K5) / (q : K5))) by
    simp only [map_div₀, map_neg, map_natCast]]
  exact ((HasValGe.of_C _).mul hf).mono (by omega)

private lemma br1_0_numM_bounds
    {a_s b_s U V : LaurentSeries K5} {a0 b0 w2 : K5}
    (hw2_ne : w2 ≠ 0)
    (ha_L : ValLead 0 a_s a0) (hb_L : ValLead 0 b_s b0)
    (hU_L : ValLead 1 U 1) (hV_L : ValLead 1 V w2) :
    let ξS_s := HahnSeries.C S_K - a_s * HahnSeries.C T_K
    let ξQ_s := HahnSeries.C Q_K - b_s * HahnSeries.C T_K
    let ξS0 : K5 := S_K - a0 * T_K
    let ξQ0 : K5 := Q_K - b0 * T_K
    ValLead 1 (A_0U a_s b_s ξS_s ξQ_s U V / U + A_0V a_s b_s ξS_s ξQ_s U V / V)
      (A_0V a0 b0 ξS0 ξQ0 0 w2 / w2) ∧
    HasValGe 3 (A_Y a_s b_s ξS_s ξQ_s U V) ∧
    HasValGe 3 (A_X a_s b_s ξS_s ξQ_s U V) := by
  intro ξS_s ξQ_s ξS0 ξQ0
  have hξS_L : ValLead 0 ξS_s ξS0 :=
    (ValLead.of_C S_K).sub ((ha_L.mul (ValLead.of_C T_K)).eq_k (by omega))
  have hξQ_L : ValLead 0 ξQ_s ξQ0 :=
    (ValLead.of_C Q_K).sub ((hb_L.mul (ValLead.of_C T_K)).eq_k (by omega))
  -- At `U = O(t), V = w2*t + O(t^2)`, `dH_dS` and `dH_dQ` have `ValLead 1` with `U = 0`!
  have hdH_S_L {s q : LaurentSeries K5} {s0 q0 : K5} (hs : ValLead 0 s s0) (hq : ValLead 0 q q0) :
      ValLead 1 (dH_dS s q U V) (-(25 / 243 : K5) * (5 * s0 - 9 * q0) * (15 * s0 - 9 * q0) * w2) := by
    unfold dH_dS
    have h1 : HasValGe 2 (-(4 / 81 : LaurentSeries K5) * (s - 3 * q) ^ 2 * U ^ 2 * V) := by
      have hsq : HasValGe 0 ((s - 3 * q) ^ 2) := ((hs.val.sub ((HasValGe.of_nat 3).mul hq.val |>.mono (by omega))).pow 2).mono (by omega)
      have hc4 : HasValGe 0 (-(4 / 81 : LaurentSeries K5)) := by
        have : -(4 / 81 : LaurentSeries K5) = HahnSeries.C (-(4 / 81 : K5)) := by simp only [map_div₀, map_neg, map_ofNat]
        rw [this]; exact HasValGe.of_C _
      exact (((hc4.mul hsq).mul (hU_L.val.pow 2)).mul hV_L.val).mono (by omega)
    have h2 : HasValGe 2 (((143 / 81 : LaurentSeries K5) * s ^ 2 - (184 / 27) * s * q +
        (52 / 9) * q ^ 2) * U * V) := by
      have hq0 : HasValGe 0 ((143 / 81 : LaurentSeries K5) * s ^ 2 - (184 / 27) * s * q + (52 / 9) * q ^ 2) := by
        have hc (r : K5) : HasValGe 0 (HahnSeries.C r) := HasValGe.of_C r
        have ha : HasValGe 0 ((143 / 81 : LaurentSeries K5) * s ^ 2) := by
          rw [show (143 / 81 : LaurentSeries K5) = HahnSeries.C (143 / 81 : K5) by simp only [map_div₀, map_ofNat]]
          exact ((hc _).mul (hs.val.pow 2)).mono (by omega)
        have hb : HasValGe 0 ((184 / 27 : LaurentSeries K5) * s * q) := by
          rw [show (184 / 27 : LaurentSeries K5) = HahnSeries.C (184 / 27 : K5) by simp only [map_div₀, map_ofNat]]
          exact (((hc _).mul hs.val).mul hq.val).mono (by omega)
        have hcc : HasValGe 0 ((52 / 9 : LaurentSeries K5) * q ^ 2) := by
          rw [show (52 / 9 : LaurentSeries K5) = HahnSeries.C (52 / 9 : K5) by simp only [map_div₀, map_ofNat]]
          exact ((hc _).mul (hq.val.pow 2)).mono (by omega)
        exact (ha.sub hb).add hcc
      exact ((hq0.mul hU_L.val).mul hV_L.val).mono (by omega)
    have h3 : ValLead 1 ((25 / 243 : LaurentSeries K5) * (5 * s - 9 * q) * (15 * s - 9 * q) * V)
        ((25 / 243 : K5) * (5 * s0 - 9 * q0) * (15 * s0 - 9 * q0) * w2) := by
      have hc : ValLead 0 (25 / 243 : LaurentSeries K5) (25 / 243 : K5) := by
        rw [show (25 / 243 : LaurentSeries K5) = HahnSeries.C (25 / 243 : K5) by simp only [map_div₀, map_ofNat]]; exact ValLead.of_C _
      have hl1 : ValLead 0 (5 * s - 9 * q) (5 * s0 - 9 * q0) :=
        (((ValLead.of_nat 5).mul hs).eq_k (by omega)).sub (((ValLead.of_nat 9).mul hq).eq_k (by omega))
          |>.eq_c (by push_cast; rfl)
      have hl2 : ValLead 0 (15 * s - 9 * q) (15 * s0 - 9 * q0) :=
        (((ValLead.of_nat 15).mul hs).eq_k (by omega)).sub (((ValLead.of_nat 9).mul hq).eq_k (by omega))
          |>.eq_c (by push_cast; rfl)
      exact (((hc.mul hl1).mul hl2).mul hV_L).eq_k (by omega)
    rw [sub_eq_add_neg, add_comm]
    exact (h3.neg.add_high (h1.add h2)).eq_c (by ring)
  have hdH_Q_L {s q : LaurentSeries K5} {s0 q0 v0 : K5} (hs : ValLead 0 s s0) (hq : ValLead 0 q q0) :
      ValLead 1 (dH_dQ s q (HahnSeries.C v0) U V) ((50 / 27 : K5) * s0 * (5 * s0 - 9 * q0) * w2) := by
    unfold dH_dQ
    have h1 : HasValGe 2 ((4 / 27 : LaurentSeries K5) * (s - 3 * q) ^ 2 * U ^ 2 * V) := by
      rw [show (4 / 27 : LaurentSeries K5) = HahnSeries.C (4 / 27 : K5) by simp only [map_div₀, map_ofNat]]
      have hsq : HasValGe 0 ((s - 3 * q) ^ 2) :=
        ((hs.val.sub ((HasValGe.of_nat 3).mul hq.val |>.mono (by omega))).pow 2).mono (by omega)
      exact ((((HasValGe.of_C _).mul hsq).mul (hU_L.val.pow 2)).mul hV_L.val).mono (by omega)
    have h2 : HasValGe 2 ((-(92 / 27 : LaurentSeries K5) * s ^ 2 + (104 / 9) * s * q -
        (22 / 3) * q ^ 2 + (10 / 7) * q * HahnSeries.C v0 +
        (10 / 7) * HahnSeries.C v0 ^ 2) * U * V) := by
      have hq0 : HasValGe 0 (-(92 / 27 : LaurentSeries K5) * s ^ 2 + (104 / 9) * s * q -
          (22 / 3) * q ^ 2 + (10 / 7) * q * HahnSeries.C v0 + (10 / 7) * HahnSeries.C v0 ^ 2) := by
        have ha : HasValGe 0 (-(92 / 27 : LaurentSeries K5) * s ^ 2) := by
          rw [show -(92 / 27 : LaurentSeries K5) = HahnSeries.C (-(92 / 27 : K5)) by simp only [map_div₀, map_neg, map_ofNat]]
          exact ((HasValGe.of_C _).mul (hs.val.pow 2)).mono (by omega)
        have hb : HasValGe 0 ((104 / 9 : LaurentSeries K5) * s * q) := by
          rw [show (104 / 9 : LaurentSeries K5) = HahnSeries.C (104 / 9 : K5) by simp only [map_div₀, map_ofNat]]
          exact (((HasValGe.of_C _).mul hs.val).mul hq.val).mono (by omega)
        have hc : HasValGe 0 ((22 / 3 : LaurentSeries K5) * q ^ 2) := by
          rw [show (22 / 3 : LaurentSeries K5) = HahnSeries.C (22 / 3 : K5) by simp only [map_div₀, map_ofNat]]
          exact ((HasValGe.of_C _).mul (hq.val.pow 2)).mono (by omega)
        have hd : HasValGe 0 ((10 / 7 : LaurentSeries K5) * q * HahnSeries.C v0) := by
          rw [show (10 / 7 : LaurentSeries K5) = HahnSeries.C (10 / 7 : K5) by simp only [map_div₀, map_ofNat]]
          exact (((HasValGe.of_C _).mul hq.val).mul (HasValGe.of_C v0)).mono (by omega)
        have he : HasValGe 0 ((10 / 7 : LaurentSeries K5) * HahnSeries.C v0 ^ 2) := by
          rw [show (10 / 7 : LaurentSeries K5) = HahnSeries.C (10 / 7 : K5) by simp only [map_div₀, map_ofNat]]
          exact ((HasValGe.of_C _).mul ((HasValGe.of_C v0).pow 2)).mono (by omega)
        exact (((ha.add hb).sub hc).add hd).add he
      exact ((hq0.mul hU_L.val).mul hV_L.val).mono (by omega)
    have h3 : ValLead 1 ((50 / 27 : LaurentSeries K5) * s * (5 * s - 9 * q) * V)
        ((50 / 27 : K5) * s0 * (5 * s0 - 9 * q0) * w2) := by
      have hc : ValLead 0 (50 / 27 : LaurentSeries K5) (50 / 27 : K5) := by
        rw [show (50 / 27 : LaurentSeries K5) = HahnSeries.C (50 / 27 : K5) by simp only [map_div₀, map_ofNat]]; exact ValLead.of_C _
      have hl1 : ValLead 0 (5 * s - 9 * q) (5 * s0 - 9 * q0) :=
        (((ValLead.of_nat 5).mul hs).eq_k (by omega)).sub (((ValLead.of_nat 9).mul hq).eq_k (by omega))
          |>.eq_c (by push_cast; rfl)
      exact (((hc.mul hs).mul hl1).mul hV_L).eq_k (by omega)
    rw [add_comm]
    exact h3.add_high (h1.add h2)
  -- All `numM i` have `ValLead 2` equal to `numM i a0 b0 ξS0 ξQ0 0 w2`!
  have hnumM_L (mi : Fin 10) :
      ValLead 2 (numM mi a_s b_s ξS_s ξQ_s U V) (numM mi a0 b0 ξS0 ξQ0 0 w2) := by
    have ha2 := hdH_S_L ha_L hb_L
    have ha0 := hdH_S_L hξS_L hξQ_L
    have ha1 := ((hdH_S_L (ha_L.add hξS_L) (hb_L.add hξQ_L)).sub ha2).sub ha0
    have hb2 : ValLead 1 (q2_b2 a_s b_s U V) ((50 / 27 : K5) * a0 * (5 * a0 - 9 * b0) * w2) := by
      simpa [q2_b2] using hdH_Q_L (v0 := 0) ha_L hb_L
    have hb0 : ValLead 1 (q2_b0 ξS_s ξQ_s U V) ((50 / 27 : K5) * ξS0 * (5 * ξS0 - 9 * ξQ0) * w2) := by
      simpa [q2_b0] using hdH_Q_L (v0 := 1) hξS_L hξQ_L
    have hb1 : ValLead 1 (q2_b1 a_s b_s ξS_s ξQ_s U V)
        ((50 / 27 : K5) * (a0 + ξS0) * (5 * (a0 + ξS0) - 9 * (b0 + ξQ0)) * w2 -
         (50 / 27 : K5) * a0 * (5 * a0 - 9 * b0) * w2 -
         (50 / 27 : K5) * ξS0 * (5 * ξS0 - 9 * ξQ0) * w2) := by
      unfold q2_b1
      have hbase := ((hdH_Q_L (v0 := 0) (ha_L.add hξS_L) (hb_L.add hξQ_L)).sub
        (hdH_Q_L (v0 := 0) ha_L hb_L)).sub (hdH_Q_L (v0 := 0) hξS_L hξQ_L)
      have hbase' : ValLead 1 (dH_dQ (a_s + ξS_s) (b_s + ξQ_s) 0 U V - dH_dQ a_s b_s 0 U V -
          dH_dQ ξS_s ξQ_s 0 U V)
          ((50 / 27 : K5) * (a0 + ξS0) * (5 * (a0 + ξS0) - 9 * (b0 + ξQ0)) * w2 -
           (50 / 27 : K5) * a0 * (5 * a0 - 9 * b0) * w2 -
           (50 / 27 : K5) * ξS0 * (5 * ξS0 - 9 * ξQ0) * w2) := by
        simpa only [map_zero] using hbase
      have hextra : HasValGe 2 ((10 / 7 : LaurentSeries K5) * b_s * U * V) := by
        rw [show (10 / 7 : LaurentSeries K5) = HahnSeries.C (10 / 7 : K5) by simp only [map_div₀, map_ofNat]]
        exact ((((HasValGe.of_C _).mul hb_L.val).mul hU_L.val).mul hV_L.val).mono (by omega)
      exact hbase'.add_high hextra
    let a2_0 : K5 := -(25 / 243 : K5) * (5 * a0 - 9 * b0) * (15 * a0 - 9 * b0) * w2
    let a0_0 : K5 := -(25 / 243 : K5) * (5 * ξS0 - 9 * ξQ0) * (15 * ξS0 - 9 * ξQ0) * w2
    let a1_0 : K5 := -(25 / 243 : K5) * (5 * (a0 + ξS0) - 9 * (b0 + ξQ0)) * (15 * (a0 + ξS0) - 9 * (b0 + ξQ0)) * w2 - a2_0 - a0_0
    let b2_0 : K5 := (50 / 27 : K5) * a0 * (5 * a0 - 9 * b0) * w2
    let b0_0 : K5 := (50 / 27 : K5) * ξS0 * (5 * ξS0 - 9 * ξQ0) * w2
    let b1_0 : K5 := (50 / 27 : K5) * (a0 + ξS0) * (5 * (a0 + ξS0) - 9 * (b0 + ξQ0)) * w2 - b2_0 - b0_0
    have ha2_0 : q1_a2 a0 b0 0 w2 = a2_0 := by simp only [q1_a2, dH_dS, a2_0]; ring
    have ha0_0 : q1_a0 ξS0 ξQ0 0 w2 = a0_0 := by simp only [q1_a0, dH_dS, a0_0]; ring
    have ha1_0 : q1_a1 a0 b0 ξS0 ξQ0 0 w2 = a1_0 := by simp only [q1_a1, dH_dS, a1_0, a2_0, a0_0]; ring
    have hb2_0 : q2_b2 a0 b0 0 w2 = b2_0 := by simp only [q2_b2, dH_dQ, b2_0]; ring
    have hb0_0 : q2_b0 ξS0 ξQ0 0 w2 = b0_0 := by simp only [q2_b0, dH_dQ, b0_0]; ring
    have hb1_0 : q2_b1 a0 b0 ξS0 ξQ0 0 w2 = b1_0 := by simp only [q2_b1, dH_dQ, b1_0, b2_0, b0_0]; ring
    have hraw := (numM_ValLead_of ha_L hb_L hξS_L hξQ_L ha2 ha1 ha0 hb2 hb1 hb0 mi).eq_k (k' := 2) (by omega)
    exact hraw.eq_c (by
      dsimp only [numM]; rw [ha2_0, ha1_0, ha0_0, hb2_0, hb1_0, hb0_0]; rfl)
  -- Helper: `ValLead 2 (A_0U ...) 0` -> `HasValGe 3 (A_0U ...)`!
  have hA0U_3 : HasValGe 3 (A_0U a_s b_s ξS_s ξQ_s U V) :=
    ((A0U_ValLead_of hnumM_L).eq_c (A0U_at_zero a0 b0 ξS0 ξQ0 w2)).hasValGe_succ
  have hA0V_L : ValLead 2 (A_0V a_s b_s ξS_s ξQ_s U V) (A_0V a0 b0 ξS0 ξQ0 0 w2) :=
    (A0V_ValLead_of hnumM_L).eq_c rfl
  have hM0_L : ValLead 1 (A_0U a_s b_s ξS_s ξQ_s U V / U + A_0V a_s b_s ξS_s ξQ_s U V / V)
      (A_0V a0 b0 ξS0 ξQ0 0 w2 / w2) := by
    have hU2 : HasValGe 2 (A_0U a_s b_s ξS_s ξQ_s U V / U) :=
      (hA0U_3.div_of_lead_ne hU_L.val (by rw [hU_L.c0]; exact one_ne_zero)).1.mono (by omega)
    have hV1 : ValLead 1 (A_0V a_s b_s ξS_s ξQ_s U V / V) (A_0V a0 b0 ξS0 ξQ0 0 w2 / w2) :=
      (hA0V_L.div_of_ne hV_L hw2_ne).eq_k (by omega)
    rw [add_comm]; exact hV1.add_high hU2
  have hAY_3 : HasValGe 3 (A_Y a_s b_s ξS_s ξQ_s U V) := by
    unfold A_Y
    have ht1 : HasValGe 3 (-(100 / 243 : LaurentSeries K5) *
        (25 * numM 3 a_s b_s ξS_s ξQ_s U V - 45 * numM 4 a_s b_s ξS_s ξQ_s U V -
         45 * numM 5 a_s b_s ξS_s ξQ_s U V + 81 * numM 6 a_s b_s ξS_s ξQ_s U V)) := by
      have h25 := ((ValLead.of_C (25 : K5)).mul (hnumM_L 3)).eq_k (k' := 2) (by omega)
      have h45a := ((ValLead.of_C (45 : K5)).mul (hnumM_L 4)).eq_k (k' := 2) (by omega)
      have h45b := ((ValLead.of_C (45 : K5)).mul (hnumM_L 5)).eq_k (k' := 2) (by omega)
      have h81 := ((ValLead.of_C (81 : K5)).mul (hnumM_L 6)).eq_k (k' := 2) (by omega)
      simp only [map_ofNat] at h25 h45a h45b h81
      have hcomb : HasValGe 3 (25 * numM 3 a_s b_s ξS_s ξQ_s U V - 45 * numM 4 a_s b_s ξS_s ξQ_s U V -
          45 * numM 5 a_s b_s ξS_s ξQ_s U V + 81 * numM 6 a_s b_s ξS_s ξQ_s U V) :=
        ((((h25.sub h45a).sub h45b).add h81).eq_c (AY_t1_at_zero a0 b0 ξS0 ξQ0 w2)).hasValGe_succ.mono (by omega)
      exact hasValGe_neg_div_nat_mul 100 243 hcomb
    have hm2 (i : Fin 10) : HasValGe 2 (numM i a_s b_s ξS_s ξQ_s U V) := (hnumM_L i).val
    have hnat2 (n : ℕ) {f : LaurentSeries K5} (hf : HasValGe 2 f) : HasValGe 2 ((n : LaurentSeries K5) * f) :=
      ((HasValGe.of_nat n).mul hf).mono (by omega)
    have ht2 : HasValGe 3 (V * (-(907876 / 33949125) * (5 * numM 0 a_s b_s ξS_s ξQ_s U V - 9 * numM 1 a_s b_s ξS_s ξQ_s U V) +
        (2258324 / 33949125) * (5 * numM 1 a_s b_s ξS_s ξQ_s U V - 9 * numM 2 a_s b_s ξS_s ξQ_s U V) +
        (8 / 243) * (5 * numM 3 a_s b_s ξS_s ξQ_s U V - 9 * numM 5 a_s b_s ξS_s ξQ_s U V) -
        (64 / 675) * (5 * numM 4 a_s b_s ξS_s ξQ_s U V - 9 * numM 6 a_s b_s ξS_s ξQ_s U V))) := by
      have hinner : HasValGe 2 (-(907876 / 33949125 : LaurentSeries K5) * (5 * numM 0 a_s b_s ξS_s ξQ_s U V - 9 * numM 1 a_s b_s ξS_s ξQ_s U V) +
          (2258324 / 33949125) * (5 * numM 1 a_s b_s ξS_s ξQ_s U V - 9 * numM 2 a_s b_s ξS_s ξQ_s U V) +
          (8 / 243) * (5 * numM 3 a_s b_s ξS_s ξQ_s U V - 9 * numM 5 a_s b_s ξS_s ξQ_s U V) -
          (64 / 675) * (5 * numM 4 a_s b_s ξS_s ξQ_s U V - 9 * numM 6 a_s b_s ξS_s ξQ_s U V)) := by
        have hp (i j : Fin 10) : HasValGe 2 (5 * numM i a_s b_s ξS_s ξQ_s U V - 9 * numM j a_s b_s ξS_s ξQ_s U V) :=
          (hnat2 5 (hm2 i)).sub (hnat2 9 (hm2 j))
        exact (((hasValGe_neg_div_nat_mul 907876 33949125 (hp 0 1)).add
          (hasValGe_div_nat_mul 2258324 33949125 (hp 1 2))).add
          (hasValGe_div_nat_mul 8 243 (hp 3 5))).sub
          (hasValGe_div_nat_mul 64 675 (hp 4 6))
      exact (hV_L.val.mul hinner).mono (by omega)
    have ht3 : HasValGe 3 (U * V * (-(123236 / 24249375) * (numM 0 a_s b_s ξS_s ξQ_s U V +
        (2790 / 77) * numM 6 a_s b_s ξS_s ξQ_s U V + 28 * numM 8 a_s b_s ξS_s ξQ_s U V -
        (5904 / 77) * numM 9 a_s b_s ξS_s ξQ_s U V) +
        (492944 / 33949125) * (numM 1 a_s b_s ξS_s ξQ_s U V +
        (927 / 77) * numM 6 a_s b_s ξS_s ξQ_s U V + (49 / 5) * numM 8 a_s b_s ξS_s ξQ_s U V -
        (21159 / 770) * numM 9 a_s b_s ξS_s ξQ_s U V))) := by
      have hinner : HasValGe 2 (-(123236 / 24249375 : LaurentSeries K5) * (numM 0 a_s b_s ξS_s ξQ_s U V +
          (2790 / 77) * numM 6 a_s b_s ξS_s ξQ_s U V + 28 * numM 8 a_s b_s ξS_s ξQ_s U V -
          (5904 / 77) * numM 9 a_s b_s ξS_s ξQ_s U V) +
          (492944 / 33949125) * (numM 1 a_s b_s ξS_s ξQ_s U V +
          (927 / 77) * numM 6 a_s b_s ξS_s ξQ_s U V + (49 / 5) * numM 8 a_s b_s ξS_s ξQ_s U V -
          (21159 / 770) * numM 9 a_s b_s ξS_s ξQ_s U V)) :=
        (hasValGe_neg_div_nat_mul 123236 24249375
          ((((hm2 0).add (hasValGe_div_nat_mul 2790 77 (hm2 6))).add (hnat2 28 (hm2 8))).sub
            (hasValGe_div_nat_mul 5904 77 (hm2 9)))).add
        (hasValGe_div_nat_mul 492944 33949125
          ((((hm2 1).add (hasValGe_div_nat_mul 927 77 (hm2 6))).add (hasValGe_div_nat_mul 49 5 (hm2 8))).sub
            (hasValGe_div_nat_mul 21159 770 (hm2 9))))
      exact ((hU_L.val.mul hV_L.val).mul hinner).mono (by omega)
    exact (ht1.add ht2).add ht3
  have hAX_3 : HasValGe 3 (A_X a_s b_s ξS_s ξQ_s U V) := by
    unfold A_X
    have hm2 (i : Fin 10) : HasValGe 2 (numM i a_s b_s ξS_s ξQ_s U V) := (hnumM_L i).val
    have hnat2 (n : ℕ) {f : LaurentSeries K5} (hf : HasValGe 2 f) : HasValGe 2 ((n : LaurentSeries K5) * f) :=
      ((HasValGe.of_nat n).mul hf).mono (by omega)
    have hp (i j : Fin 10) : HasValGe 2 (5 * numM i a_s b_s ξS_s ξQ_s U V - 9 * numM j a_s b_s ξS_s ξQ_s U V) :=
      (hnat2 5 (hm2 i)).sub (hnat2 9 (hm2 j))
    have hinner : HasValGe 2 (-(8 / 405 : LaurentSeries K5) * (5 * numM 3 a_s b_s ξS_s ξQ_s U V - 9 * numM 4 a_s b_s ξS_s ξQ_s U V) -
        (476 / 7185) * (5 * numM 7 a_s b_s ξS_s ξQ_s U V - 9 * numM 8 a_s b_s ξS_s ξQ_s U V) +
        (6916 / 35925) * (5 * numM 8 a_s b_s ξS_s ξQ_s U V - 9 * numM 9 a_s b_s ξS_s ξQ_s U V)) :=
      ((hasValGe_neg_div_nat_mul 8 405 (hp 3 4)).sub (hasValGe_div_nat_mul 476 7185 (hp 7 8))).add
        (hasValGe_div_nat_mul 6916 35925 (hp 8 9))
    exact (hU_L.val.mul hinner).mono (by omega)
  exact ⟨hM0_L, hAY_3, hAX_3⟩

private lemma map_EB_of {R R' : Type*} [Field R] [Field R'] (f : R →+* R')
    (S Q T x y U V : R) :
    EB_of (f S) (f Q) (f T) (f x) (f y) (f U) (f V) = f (EB_of S Q T x y U V) := by
  simp only [EB_of, W2_of, DX2_of, DY2_of, dF5_fn, br_fn, LX_of, LY_of,
    dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of,
    map_add, map_sub, map_mul, map_div₀, map_pow, map_ofNat, map_one, map_zero]

private lemma map_QY_num {R R' : Type*} [Field R] [Field R'] (f : R →+* R')
    (S Q T x y U V : R) (i : Fin 3) :
    QY_num (f S) (f Q) (f T) (f x) (f y) (f U) (f V) i = f (QY_num S Q T x y U V i) := by
  fin_cases i <;>
    simp only [QY_num, Omega_F, dDX2_F, F_contract, dF5_fn, dH0_fn, dDX2_fn, DX2_of, DY2_of,
      om_fn, br_fn, LX_of, LY_of, dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of,
      map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat, map_zero, map_one]

private lemma map_QX_num {R R' : Type*} [Field R] [Field R'] (f : R →+* R')
    (S Q T x y U V : R) (i : Fin 3) :
    QX_num (f S) (f Q) (f T) (f x) (f y) (f U) (f V) i = f (QX_num S Q T x y U V i) := by
  fin_cases i <;>
    simp only [QX_num, Omega_F, dDY2_F, F_contract, dF5_fn, dH0_fn, dDY2_fn, DX2_of, DY2_of,
      om_fn, br_fn, LX_of, LY_of, dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of,
      map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat, map_zero, map_one]

private lemma EB_of_zero_zero {F : Type*} [Field F] [CharZero F] (S Q T x y : F) :
    EB_of S Q T x y 0 0 = 0 := by
  simp only [EB_of, br_fn, dLX_fn, dLY_fn]; ring

private lemma br1_0_q1_bound {a_s b_s U V : LaurentSeries K5} {w2 a0 b0 : K5}
    (ha_L : ValLead 0 a_s a0) (hb_L : ValLead 0 b_s b0)
    (hU_L : ValLead 1 U 1) (hV_L : ValLead 1 V w2)
    (hw2_eq : S_K * (5 * S_K - 9 * Q_K) ^ 2 * w2 = -T_K * (5 * T_K - 9) ^ 2)
    (hlin0 : (-(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)) * (w2 * a0) +
      ((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)) * (w2 * b0) + k5Params.c0_V0 = 0) :
    HasValGe 1 (dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / v_of V) ∧
    HasValGe 1 (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / u_of U) ∧
    HasValGe 2
      (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) *
        A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V *
        (dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
          (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / v_of V) +
      H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) *
        B1_of (HahnSeries.C T_K) U V *
        (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
          (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / u_of U) +
      (cA1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) a_s b_s U V / v_of V) *
        EB_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V) ∧
    HasValGe 0 (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)) := by
  have hA := fiveS_sub_9Q_ne; have hC := fiveT_sub_9_ne
  have hA1_1 : HasValGe 1 (A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V) := by
    unfold A1_of
    have h0 : HasValGe 0 (25 * HahnSeries.C S_K * (5 * HahnSeries.C S_K - 9 * HahnSeries.C Q_K) ^ 2 -
        4 * (HahnSeries.C S_K - 3 * HahnSeries.C Q_K) ^ 3 * U) := by
      have ha : HasValGe 0 (25 * HahnSeries.C S_K * (5 * HahnSeries.C S_K - 9 * HahnSeries.C Q_K) ^ 2) :=
        (((HasValGe.of_nat 25).mul (HasValGe.of_C S_K)).mul
          ((((HasValGe.of_nat 5).mul (HasValGe.of_C S_K)).sub ((HasValGe.of_nat 9).mul (HasValGe.of_C Q_K))).pow 2)).mono (by omega)
      have hb : HasValGe 0 (4 * (HahnSeries.C S_K - 3 * HahnSeries.C Q_K) ^ 3 * U) :=
        (((HasValGe.of_nat 4).mul (((HasValGe.of_C S_K).sub ((HasValGe.of_nat 3).mul (HasValGe.of_C Q_K) |>.mono (k2 := 0) (by omega))).pow 3)).mul
          (hU_L.val.mono (k2 := 0) (by omega))).mono (by omega)
      exact ha.sub hb
    rw [show (1 / 27 : LaurentSeries K5) = HahnSeries.C (1 / 27 : K5) by simp only [map_div₀, map_ofNat, map_one]]
    exact (((HasValGe.of_C _).mul hV_L.val).mul h0).mono (by omega)
  have hB1_1 : HasValGe 1 (B1_of (HahnSeries.C T_K) U V) := by
    unfold B1_of
    have h0 : HasValGe 0 (25 * HahnSeries.C T_K * (5 * HahnSeries.C T_K - 9) ^ 2 -
        4 * (HahnSeries.C T_K - 3) ^ 3 * V) := by
      have ha : HasValGe 0 (25 * HahnSeries.C T_K * (5 * HahnSeries.C T_K - 9) ^ 2) :=
        (((HasValGe.of_nat 25).mul (HasValGe.of_C T_K)).mul
          ((((HasValGe.of_nat 5).mul (HasValGe.of_C T_K)).sub (HasValGe.of_nat 9)).pow 2)).mono (by omega)
      have hb : HasValGe 0 (4 * (HahnSeries.C T_K - 3) ^ 3 * V) :=
        (((HasValGe.of_nat 4).mul (((HasValGe.of_C T_K).sub (HasValGe.of_nat 3)).pow 3)).mul
          (hV_L.val.mono (k2 := 0) (by omega))).mono (by omega)
      exact ha.sub hb
    rw [show (1 / 27 : LaurentSeries K5) = HahnSeries.C (1 / 27 : K5) by simp only [map_div₀, map_ofNat, map_one]]
    exact (((HasValGe.of_C _).mul hU_L.val).mul h0).mono (by omega)
  have hH0_0 : HasValGe 0 (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)) := by
    have h : H0_of (HahnSeries.C S_K : LaurentSeries K5) (HahnSeries.C Q_K) (HahnSeries.C T_K) =
        HahnSeries.C (H0_of S_K Q_K T_K) := by
      simp only [H0_of, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]
    rw [h]; exact HasValGe.of_C _
  have hcA1_1 : HasValGe 1 (cA1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) a_s b_s U V) := by
    have hdA1 (k : Fin 3) : HasValGe 1 (dA1_fn k (HahnSeries.C S_K) (HahnSeries.C Q_K) U V) := by
      fin_cases k
      · unfold dA1_fn
        rw [show (1 / 27 : LaurentSeries K5) = HahnSeries.C (1 / 27 : K5) by simp only [map_div₀, map_ofNat, map_one]]
        have h0 : HasValGe 0 (25 * (5 * HahnSeries.C S_K - 9 * HahnSeries.C Q_K) *
            (15 * HahnSeries.C S_K - 9 * HahnSeries.C Q_K) - 12 * (HahnSeries.C S_K - 3 * HahnSeries.C Q_K) ^ 2 * U) := by
          have ha : HasValGe 0 _ := (((HasValGe.of_nat 25).mul (((HasValGe.of_nat 5).mul (HasValGe.of_C S_K)).sub
            ((HasValGe.of_nat 9).mul (HasValGe.of_C Q_K)))).mul
            (((HasValGe.of_nat 15).mul (HasValGe.of_C S_K)).sub ((HasValGe.of_nat 9).mul (HasValGe.of_C Q_K)))).mono (by omega)
          have hb : HasValGe 0 _ := (((HasValGe.of_nat 12).mul (((HasValGe.of_C S_K).sub
            ((HasValGe.of_nat 3).mul (HasValGe.of_C Q_K) |>.mono (k2 := 0) (by omega))).pow 2)).mul
            (hU_L.val.mono (k2 := 0) (by omega))).mono (by omega)
          exact ha.sub hb
        exact (((HasValGe.of_C _).mul hV_L.val).mul h0).mono (by omega)
      · unfold dA1_fn
        rw [show (1 / 27 : LaurentSeries K5) = HahnSeries.C (1 / 27 : K5) by simp only [map_div₀, map_ofNat, map_one]]
        have h0 : HasValGe 0 (-(450 : LaurentSeries K5) * HahnSeries.C S_K * (5 * HahnSeries.C S_K - 9 * HahnSeries.C Q_K) +
            36 * (HahnSeries.C S_K - 3 * HahnSeries.C Q_K) ^ 2 * U) := by
          have ha : HasValGe 0 _ := ((((HasValGe.of_nat 450).neg).mul (HasValGe.of_C S_K)).mul
            (((HasValGe.of_nat 5).mul (HasValGe.of_C S_K)).sub ((HasValGe.of_nat 9).mul (HasValGe.of_C Q_K)))).mono (by omega)
          have hb : HasValGe 0 _ := (((HasValGe.of_nat 36).mul (((HasValGe.of_C S_K).sub
            ((HasValGe.of_nat 3).mul (HasValGe.of_C Q_K) |>.mono (k2 := 0) (by omega))).pow 2)).mul
            (hU_L.val.mono (k2 := 0) (by omega))).mono (by omega)
          exact ha.add hb
        exact (((HasValGe.of_C _).mul hV_L.val).mul h0).mono (by omega)
      · exact HasValGe.zero 1
    have hdH0_0 (k : Fin 3) : HasValGe 0 (dH0_fn k (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)) := by
      have h : dH0_fn k (HahnSeries.C S_K : LaurentSeries K5) (HahnSeries.C Q_K) (HahnSeries.C T_K) =
          HahnSeries.C (dH0_fn k S_K Q_K T_K) := by
        fin_cases k <;> simp only [dH0_fn, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]
      rw [h]; exact HasValGe.of_C _
    unfold cA1_of
    exact ((((hH0_0.mul (hdA1 0)).sub (hA1_1.mul (hdH0_0 0) |>.mono (by omega))).mul ha_L.val |>.mono (by omega)).add
      (((hH0_0.mul (hdA1 1)).sub (hA1_1.mul (hdH0_0 1) |>.mono (by omega))).mul hb_L.val |>.mono (by omega))).add
      (((hH0_0.mul (hdA1 2)).sub (hA1_1.mul (hdH0_0 2) |>.mono (by omega))).mono (by omega))
  have hU0 : ValLead 0 U 0 := ValLead.of_hasValGe_succ hU_L.val
  have hV0 : ValLead 0 V 0 := ValLead.of_hasValGe_succ hV_L.val
  have hu_L : ValLead 0 (u_of U) (-(1 / 9 : K5)) := by
    unfold u_of
    have h9 : (9 : K5) ≠ 0 := by exact_mod_cast (by decide : (9 : ℕ) ≠ 0)
    exact ((hU0.sub (ValLead.of_C 1)).div_of_ne (ValLead.of_nat 9) h9).eq_k (by omega) |>.eq_c (by ring)
  have hv_L : ValLead 0 (v_of V) (-(1 / 9 : K5)) := by
    unfold v_of
    have h9 : (9 : K5) ≠ 0 := by exact_mod_cast (by decide : (9 : ℕ) ≠ 0)
    exact ((hV0.sub (ValLead.of_C 1)).div_of_ne (ValLead.of_nat 9) h9).eq_k (by omega) |>.eq_c (by ring)
  have hneg19_ne : (-(1 / 9 : K5)) ≠ 0 := neg_ne_zero.mpr (div_ne_zero one_ne_zero (by exact_mod_cast (by decide : (9 : ℕ) ≠ 0)))
  have hlinUV0 {f0 f1 f2 f3 : K5} :
      ValLead 0 (HahnSeries.C f0 + HahnSeries.C f1 * V + HahnSeries.C f2 * U + HahnSeries.C f3 * U * V) f0 := by
    have hhi : HasValGe 1 (HahnSeries.C f1 * V + HahnSeries.C f2 * U + HahnSeries.C f3 * U * V) :=
      ((((HasValGe.of_C f1).mul hV_L.val).mono (by omega)).add
        (((HasValGe.of_C f2).mul hU_L.val).mono (by omega))).add
        ((((HasValGe.of_C f3).mul hU_L.val).mul hV_L.val).mono (by omega))
    have hre : HahnSeries.C f0 + HahnSeries.C f1 * V + HahnSeries.C f2 * U + HahnSeries.C f3 * U * V =
        HahnSeries.C f0 + (HahnSeries.C f1 * V + HahnSeries.C f2 * U + HahnSeries.C f3 * U * V) := by ring
    rw [hre]; exact (ValLead.of_C f0).add_high hhi
  have hEB_1 : HasValGe 1 (EB_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V) := by
    have hbi := EB_bilinear_UV (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V
    have h00 := map_EB_of (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 0 0
    have h01 := map_EB_of (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 0 1
    have h10 := map_EB_of (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 1 0
    have h11 := map_EB_of (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 1 1
    simp only [map_zero, map_one] at h00 h01 h10 h11
    rw [hbi, h00, h01, h10, h11, ← map_sub, ← map_sub, ← map_sub, ← map_sub, ← map_add]
    exact (hlinUV0.eq_c (EB_of_zero_zero S_K Q_K T_K x_K y_K)).hasValGe_succ
  have hQY_0 (i : Fin 3) : ValLead 0 (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K)
      (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V i)
      (QY_num S_K Q_K T_K x_K y_K 0 0 i) := by
    have hbi := QY_bilinear_UV (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V i
    have h00 := map_QY_num (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 0 0 i
    have h01 := map_QY_num (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 0 1 i
    have h10 := map_QY_num (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 1 0 i
    have h11 := map_QY_num (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 1 1 i
    simp only [map_zero, map_one] at h00 h01 h10 h11
    rw [hbi, h00, h01, h10, h11, ← map_sub, ← map_sub, ← map_sub, ← map_sub, ← map_add]
    exact hlinUV0
  have hQX_0 (i : Fin 3) : ValLead 0 (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K)
      (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V i)
      (QX_num S_K Q_K T_K x_K y_K 0 0 i) := by
    have hbi := QX_bilinear_UV (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V i
    have h00 := map_QX_num (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 0 0 i
    have h01 := map_QX_num (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 0 1 i
    have h10 := map_QX_num (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 1 0 i
    have h11 := map_QX_num (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 1 1 i
    simp only [map_zero, map_one] at h00 h01 h10 h11
    rw [hbi, h00, h01, h10, h11, ← map_sub, ← map_sub, ← map_sub, ← map_sub, ← map_add]
    exact hlinUV0
  have hqY_1 : HasValGe 1 (dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / v_of V) := by
    have hdot : ValLead 0 (dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s)
        (dot_ab (QY_num S_K Q_K T_K x_K y_K 0 0) a0 b0) := by
      unfold dot_ab
      exact (((hQY_0 0).mul ha_L).eq_k (by omega)).add (((hQY_0 1).mul hb_L).eq_k (by omega)) |>.add (hQY_0 2)
    have hzero : dot_ab (QY_num S_K Q_K T_K x_K y_K 0 0) a0 b0 = 0 := by
      apply mul_left_cancel₀ (mul_ne_zero hA hC)
      rw [mul_zero]
      have hstep : (5 * S_K - 9 * Q_K) * (5 * T_K - 9) *
          dot_ab (QY_num S_K Q_K T_K x_K y_K 0 0) a0 b0 =
          4 * y_K * (-25 * S_K + 45 * Q_K + 27 * x_K) * S_K ^ 2 * T_K ^ 2 * DY2_of T_K y_K *
            (S_K * (5 * S_K - 9 * Q_K) ^ 2 *
              ((-(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)) * (w2 * a0) +
               ((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)) * (w2 * b0) + k5Params.c0_V0)) := by
        have hlin' : S_K * (5 * S_K - 9 * Q_K) ^ 2 *
            ((-(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)) * (w2 * a0) +
             ((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)) * (w2 * b0) + k5Params.c0_V0) =
            (-(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)) * a0 * (S_K * (5 * S_K - 9 * Q_K) ^ 2 * w2) +
            ((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)) * b0 * (S_K * (5 * S_K - 9 * Q_K) ^ 2 * w2) +
            S_K * (5 * S_K - 9 * Q_K) ^ 2 * k5Params.c0_V0 := by ring
        rw [hlin', hw2_eq]
        have hc0 : k5Params.c0_V0 = -(25 / 81 : K5) * (5 * T_K - 9) * (5 * T_K - 3) := by
          simp only [CoverParams.c0_V0, CoverParams.inv81, k5Params_inv3, k5Params_T]; ring
        rw [hc0]
        exact QY_num_00_factor S_K Q_K T_K x_K y_K a0 b0
      rw [hstep, hlin0, mul_zero, mul_zero]
    exact (((hdot.eq_c hzero).div_of_ne hv_L hneg19_ne).eq_k (k' := 0) (by omega) |>.eq_c (zero_div _)).hasValGe_succ
  have hqX_1 : HasValGe 1 (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / u_of U) := by
    have hdot : ValLead 0 (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s)
        (dot_ab (QX_num S_K Q_K T_K x_K y_K 0 0) a0 b0) := by
      unfold dot_ab
      exact (((hQX_0 0).mul ha_L).eq_k (by omega)).add (((hQX_0 1).mul hb_L).eq_k (by omega)) |>.add (hQX_0 2)
    have hzero : dot_ab (QX_num S_K Q_K T_K x_K y_K 0 0) a0 b0 = 0 := by
      apply mul_left_cancel₀ (mul_ne_zero hA hC)
      rw [mul_zero]
      have hstep : (5 * S_K - 9 * Q_K) * (5 * T_K - 9) *
          dot_ab (QX_num S_K Q_K T_K x_K y_K 0 0) a0 b0 =
          4 * x_K * (-25 * T_K + 45 + 27 * y_K) * S_K ^ 2 * T_K ^ 2 * DX2_of S_K Q_K x_K *
            (S_K * (5 * S_K - 9 * Q_K) ^ 2 *
              ((-(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)) * (w2 * a0) +
               ((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)) * (w2 * b0) + k5Params.c0_V0)) := by
        have hlin' : S_K * (5 * S_K - 9 * Q_K) ^ 2 *
            ((-(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)) * (w2 * a0) +
             ((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)) * (w2 * b0) + k5Params.c0_V0) =
            (-(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)) * a0 * (S_K * (5 * S_K - 9 * Q_K) ^ 2 * w2) +
            ((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)) * b0 * (S_K * (5 * S_K - 9 * Q_K) ^ 2 * w2) +
            S_K * (5 * S_K - 9 * Q_K) ^ 2 * k5Params.c0_V0 := by ring
        rw [hlin', hw2_eq]
        have hc0 : k5Params.c0_V0 = -(25 / 81 : K5) * (5 * T_K - 9) * (5 * T_K - 3) := by
          simp only [CoverParams.c0_V0, CoverParams.inv81, k5Params_inv3, k5Params_T]; ring
        rw [hc0]
        exact QX_num_00_factor S_K Q_K T_K x_K y_K a0 b0
      rw [hstep, hlin0, mul_zero, mul_zero]
    exact (((hdot.eq_c hzero).div_of_ne hu_L hneg19_ne).eq_k (k' := 0) (by omega) |>.eq_c (zero_div _)).hasValGe_succ
  have hq1_2 : HasValGe 2
      (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) *
        A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V *
        (dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
          (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / v_of V) +
      H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) *
        B1_of (HahnSeries.C T_K) U V *
        (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
          (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / u_of U) +
      (cA1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) a_s b_s U V / v_of V) *
        EB_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V) := by
    have ht1 : HasValGe 2 _ := ((hH0_0.mul hA1_1).mul hqY_1).mono (by omega)
    have ht2 : HasValGe 2 _ := ((hH0_0.mul hB1_1).mul hqX_1).mono (by omega)
    have ht3 : HasValGe 2 _ := ((hcA1_1.div_of_lead_ne hv_L.val (hv_L.c0.symm ▸ hneg19_ne)).1.mul hEB_1).mono (by omega)
    exact (ht1.add ht2).add ht3
  exact ⟨hqY_1, hqX_1, hq1_2, hH0_0⟩

lemma P18_of_HahnC_eq (S Q T x y : K5) (a b U V : LaurentSeries K5) :
    P18_of (R := LaurentSeries K5) (HahnSeries.C S) (HahnSeries.C Q) (HahnSeries.C T) (HahnSeries.C x) (HahnSeries.C y) a b U V =
    (A_0U a b (HahnSeries.C S - a * HahnSeries.C T) (HahnSeries.C Q - b * HahnSeries.C T) U V / U +
     A_0V a b (HahnSeries.C S - a * HahnSeries.C T) (HahnSeries.C Q - b * HahnSeries.C T) U V / V) *
      (H0_of (HahnSeries.C S) (HahnSeries.C Q) (HahnSeries.C T) *
        A1_of (HahnSeries.C S) (HahnSeries.C Q) U V *
        (dot_ab (QY_num (HahnSeries.C S) (HahnSeries.C Q) (HahnSeries.C T)
          (HahnSeries.C x) (HahnSeries.C y) U V) a b / v_of V) +
       H0_of (HahnSeries.C S) (HahnSeries.C Q) (HahnSeries.C T) *
        B1_of (HahnSeries.C T) U V *
        (dot_ab (QX_num (HahnSeries.C S) (HahnSeries.C Q) (HahnSeries.C T)
          (HahnSeries.C x) (HahnSeries.C y) U V) a b / u_of U) +
       (cA1_of (HahnSeries.C S) (HahnSeries.C Q) (HahnSeries.C T) a b U V / v_of V) *
        EB_of (HahnSeries.C S) (HahnSeries.C Q) (HahnSeries.C T)
          (HahnSeries.C x) (HahnSeries.C y) U V) +
    (A_Y a b (HahnSeries.C S - a * HahnSeries.C T) (HahnSeries.C Q - b * HahnSeries.C T) U V *
      (dot_ab (QY_num (HahnSeries.C S) (HahnSeries.C Q) (HahnSeries.C T)
        (HahnSeries.C x) (HahnSeries.C y) U V) a b / v_of V) +
     A_X a b (HahnSeries.C S - a * HahnSeries.C T) (HahnSeries.C Q - b * HahnSeries.C T) U V *
      (dot_ab (QX_num (HahnSeries.C S) (HahnSeries.C Q) (HahnSeries.C T)
        (HahnSeries.C x) (HahnSeries.C y) U V) a b / u_of U)) *
    H0_of (HahnSeries.C S) (HahnSeries.C Q) (HahnSeries.C T) ^ 2 := by
  unfold P18_of
  congr 1

private lemma br1_0_g_scaled_core {a_s b_s U V : LaurentSeries K5} {w2 a0 b0 : K5}
    (hw2_ne : w2 ≠ 0) (ha_L : ValLead 0 a_s a0) (hb_L : ValLead 0 b_s b0)
    (hU_L : ValLead 1 U 1) (hV_L : ValLead 1 V w2)
    (hw2_eq : S_K * (5 * S_K - 9 * Q_K) ^ 2 * w2 = -T_K * (5 * T_K - 9) ^ 2)
    (hlin0 : (-(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)) * (w2 * a0) +
      ((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)) * (w2 * b0) + k5Params.c0_V0 = 0) :
    HasValGe 3 (P18_of (R := LaurentSeries K5) (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) a_s b_s U V) ∧
      (a0 = S_K / T_K → 5 * a0 - 9 * b0 = 5 * (Q_K - b0 * T_K) →
        (P18_of (R := LaurentSeries K5) (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
          (HahnSeries.C x_K) (HahnSeries.C y_K) a_s b_s U V).coeff 3 = 0) := by
  have hT := T_K_ne_zero
  obtain ⟨hM0_L, hAY_3, hAX_3⟩ := br1_0_numM_bounds hw2_ne ha_L hb_L hU_L hV_L
  obtain ⟨hqY_1, hqX_1, hq1_2, hH0_0⟩ := br1_0_q1_bound ha_L hb_L hU_L hV_L hw2_eq hlin0
  have hrest_4 : HasValGe 4
      ((A_Y a_s b_s (HahnSeries.C S_K - a_s * HahnSeries.C T_K) (HahnSeries.C Q_K - b_s * HahnSeries.C T_K) U V *
        (dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
          (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / v_of V) +
        A_X a_s b_s (HahnSeries.C S_K - a_s * HahnSeries.C T_K) (HahnSeries.C Q_K - b_s * HahnSeries.C T_K) U V *
        (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
          (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / u_of U)) *
      H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) ^ 2) :=
    (((hAY_3.mul hqY_1).mono (k2 := 4) (by omega)).add ((hAX_3.mul hqX_1).mono (k2 := 4) (by omega))).mul
      (hH0_0.pow 2) |>.mono (by omega)
  rw [P18_of_HahnC_eq]
  refine ⟨((hM0_L.val.mul hq1_2).mono (by omega)).add (hrest_4.mono (by omega)), ?_⟩
  intro ha0_eq hrel
  have hξS0 : S_K - a0 * T_K = 0 := by rw [ha0_eq, div_mul_cancel₀ _ hT, sub_self]
  have hA0V_0 : A_0V a0 b0 (S_K - a0 * T_K) (Q_K - b0 * T_K) 0 w2 = 0 := by
    rw [hξS0]; exact A0V_at_zero_xiS0 a0 b0 (Q_K - b0 * T_K) w2 hrel
  have hM0_2 : HasValGe 2
      (A_0U a_s b_s (HahnSeries.C S_K - a_s * HahnSeries.C T_K) (HahnSeries.C Q_K - b_s * HahnSeries.C T_K) U V / U +
       A_0V a_s b_s (HahnSeries.C S_K - a_s * HahnSeries.C T_K) (HahnSeries.C Q_K - b_s * HahnSeries.C T_K) U V / V) :=
    (hM0_L.eq_c (by rw [hA0V_0, zero_div])).hasValGe_succ
  have hg_4 : HasValGe 4 _ :=
    ((hM0_2.mul hq1_2).mono (k2 := 4) (by omega)).add hrest_4
  exact hg_4 3 (by omega)

private lemma br1_0_g_scaled {W1s U V ca cb c0W : LaurentSeries K5} {w2 z1 : K5}
    (hw2_ne : w2 ≠ 0) (hcb0_ne : (50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K) ≠ 0)
    (hw2_L : ValLead 2 W1s w2) (hU_L : ValLead 1 U 1) (hV_L : ValLead 1 V w2)
    (hca_L : ValLead 0 ca (-(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)))
    (hcb_L : ValLead 0 cb ((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)))
    (hc0W_L : ValLead 2 c0W k5Params.c0_V0)
    (hz1_def : z1 = w2 * S_K / T_K)
    (hw2_eq : S_K * (5 * S_K - 9 * Q_K) ^ 2 * w2 = -T_K * (5 * T_K - 9) ^ 2)
    (hz1_mul : (5 * S_K - 9 * Q_K) ^ 2 * z1 = -(5 * T_K - 9) ^ 2) :
    let g : LaurentSeries K5 → LaurentSeries K5 := fun z =>
      P18_of (R := LaurentSeries K5) (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K)
        (z / W1s) (-(ca * z + c0W) / (W1s * cb)) U V
    ∀ c : K5, HasValGe 3 (g (HahnSeries.single 2 c)) ∧
      (c = z1 → (g (HahnSeries.single 2 c)).coeff 3 = 0) := by
  have hS := S_K_ne_zero; have hT := T_K_ne_zero
  have hA := fiveS_sub_9Q_ne; have hC := fiveT_sub_9_ne
  intro g c
  set z : LaurentSeries K5 := HahnSeries.single 2 c
  let a0 : K5 := c / w2
  let b0 : K5 := -((-(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)) * c + k5Params.c0_V0) /
    (w2 * ((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)))
  have hz_L : ValLead 2 z c := ValLead.of_single 2 c
  have ha_L : ValLead 0 (z / W1s) a0 :=
    (hz_L.div_of_ne hw2_L hw2_ne).eq_k (by omega)
  have hb_L : ValLead 0 (-(ca * z + c0W) / (W1s * cb)) b0 := by
    have hnum : ValLead 2 (-(ca * z + c0W))
        (-((-(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)) * c + k5Params.c0_V0)) :=
      (((hca_L.mul hz_L).eq_k (by omega)).add hc0W_L).neg
    have hden : ValLead 2 (W1s * cb) (w2 * ((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K))) :=
      (hw2_L.mul hcb_L).eq_k (by omega)
    exact (hnum.div_of_ne hden (mul_ne_zero hw2_ne hcb0_ne)).eq_k (by omega)
  have hlin0 : (-(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)) * (w2 * a0) +
      ((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)) * (w2 * b0) + k5Params.c0_V0 = 0 := by
    dsimp only [a0, b0]; field_simp [hw2_ne, hcb0_ne]; ring
  obtain ⟨hge, hzero⟩ := br1_0_g_scaled_core hw2_ne ha_L hb_L hU_L hV_L hw2_eq hlin0
  refine ⟨hge, fun hcz1 => ?_⟩
  have ha0_eq : a0 = S_K / T_K := by dsimp only [a0]; rw [hcz1, hz1_def]; field_simp [hw2_ne, hT]
  have hrel : 5 * a0 - 9 * b0 = 5 * (Q_K - b0 * T_K) := by
    have hwa : w2 * a0 = z1 := by dsimp only [a0]; rw [hcz1]; field_simp [hw2_ne]
    have h50_27 : (50 / 27 : K5) ≠ 0 := div_ne_zero
      (by exact_mod_cast (by decide : (50 : ℕ) ≠ 0))
      (by exact_mod_cast (by decide : (27 : ℕ) ≠ 0))
    have hTb : T_K * (5 * T_K - 9) * b0 = 5 * (Q_K * T_K - S_K) := by
      apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero h50_27 hA) hC)
      have h1 : (5 * S_K - 9 * Q_K) ^ 2 *
          ((-(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)) * z1 +
           ((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)) * (w2 * b0) + k5Params.c0_V0) = 0 := by
        rw [← hwa, hlin0, mul_zero]
      have h2 : (5 * S_K - 9 * Q_K) ^ 2 *
          ((-(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)) * z1 +
           ((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)) * (w2 * b0) + k5Params.c0_V0) =
          (-(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)) * ((5 * S_K - 9 * Q_K) ^ 2 * z1) +
          ((50 / 27 : K5) * (5 * S_K - 9 * Q_K)) * (S_K * (5 * S_K - 9 * Q_K) ^ 2 * w2) * b0 +
          (5 * S_K - 9 * Q_K) ^ 2 * k5Params.c0_V0 := by ring
      rw [h2, hz1_mul, hw2_eq] at h1
      simp only [CoverParams.c0_V0, CoverParams.inv81, k5Params_inv3, k5Params_T] at h1
      linear_combination -h1
    apply mul_left_cancel₀ hT
    have haT : T_K * a0 = S_K := by rw [ha0_eq, mul_div_cancel₀ _ hT]
    linear_combination hTb + 5 * haT
  exact hzero ha0_eq hrel

lemma br1_0_eta_AC_coeff_neg_one : (br1_0 eta_AC).coeff (-1) = 0 := by
  have hbr := branchHom_eta_AC ψ0 ψ0_C W1_0 W1_0_eq_ψ0
  simp only [ψ0_X] at hbr
  have hfP : ψ0.comp toRat = evalT := RingHom.ext ψ0_toRat
  simp only [hfP] at hbr
  change br1_0 eta_AC = _ at hbr
  rw [hbr]
  set U := HahnSeries.single (1 : ℤ) (1 : K5)
  set V := W1_0 / U
  set ca := evalT k5Params.ca_h
  set cb := evalT k5Params.cb_h
  set c0W := PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.c0W)
  set d2_2 := PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d2_2)
  set d2_1 := PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d2_1)
  set d2_0 := PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d2_0)
  set d1 := PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d1_z)
  set d0 := PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d0_z)
  set res := PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.res_z)
  set g : LaurentSeries K5 → LaurentSeries K5 := fun z =>
    P18_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K)
      (z / W1_0) (-(ca * z + c0W) / (W1_0 * cb)) U V
  set p := interp4 g
  set P1 := remDeg4_P1 d2_2 d2_1 d2_0 p.1 p.2.1 p.2.2.1 p.2.2.2.1
  set P0 := remDeg4_P0 d2_2 d2_1 d2_0 p.1 p.2.1 p.2.2.1 p.2.2.2.2
  have hp_def : p = interp4 g := rfl
  have hP1_def : P1 = remDeg4_P1 d2_2 d2_1 d2_0 p.1 p.2.1 p.2.2.1 p.2.2.2.1 := rfl
  have hP0_def : P0 = remDeg4_P0 d2_2 d2_1 d2_0 p.1 p.2.1 p.2.2.1 p.2.2.2.2 := rfl
  clear_value P1 P0 p
  -- Show `HasValGe 13` on denominator with nonzero coeff 13, and `HasValGe 13` on numerator!
  have hS := S_K_ne_zero; have hT := T_K_ne_zero
  have hA := fiveS_sub_9Q_ne; have hC := fiveT_sub_9_ne
  set w2 : K5 := -(k5Params.Cv0 / k5Params.Bv0)
  have hw2_ne : w2 ≠ 0 := neg_ne_zero.mpr (div_ne_zero k5Params_Cv0_ne k5Params_Bv0_ne)
  have hw2_L : ValLead 2 W1_0 w2 := ⟨HasValGe_W1_0, W1_0_coeff2⟩
  have hU_L : ValLead 1 U 1 := ValLead.of_single 1 1
  have hV_L : ValLead 1 V w2 := (hw2_L.div_of_ne hU_L one_ne_zero).eq_k (by omega) |>.eq_c (div_one w2)
  have hca_L : ValLead 0 ca (-(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)) :=
    (ValLead.of_evalT _).eq_c (by
      simp only [CoverParams.ca_h, quadU_coeff_zero, CoverParams.inv81, CoverParams.inv27, k5Params_inv3, k5Params_S, k5Params_Q]; ring)
  have hcb_L : ValLead 0 cb ((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)) :=
    (ValLead.of_evalT _).eq_c (by
      simp only [CoverParams.cb_h, quadU_coeff_zero, CoverParams.inv27, CoverParams.inv9, k5Params_inv3, k5Params_S, k5Params_Q]; ring)
  have hcb0_ne : (50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (div_ne_zero (by exact_mod_cast (by decide : (50 : ℕ) ≠ 0))
      (by exact_mod_cast (by decide : (27 : ℕ) ≠ 0))) hS) hA
  have hQ5_L : ValLead 0 (evalT k5Params.Q5_z) ((15625 / 59049 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 4) :=
    (ValLead.of_evalT _).eq_c (by
      simp only [Polynomial.coeff_zero_eq_eval_zero, CoverParams.Q5_z, CoverParams.q20, CoverParams.q11,
        CoverParams.q02, CoverParams.ca_h, CoverParams.cb_h, CoverParams.quadU,
        CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3, k5Params_S, k5Params_Q,
        eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X]; ring)
  have hQ50_ne : (15625 / 59049 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 4 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (div_ne_zero (by exact_mod_cast (by decide : (15625 : ℕ) ≠ 0))
      (by exact_mod_cast (by decide : (59049 : ℕ) ≠ 0))) hS) (pow_ne_zero 4 hA)
  have h2W_L : ValLead 0 (2 * W1_0 + evalT k5Params.bW) (k5Params.Bv0 * k5Params.Av0_inv) := by
    have hbW0 : ValLead 0 (evalT k5Params.bW) (k5Params.Bv0 * k5Params.Av0_inv) :=
      (ValLead.of_evalT _).eq_c (by
        simp only [CoverParams.bW, CoverParams.Bv, coeff_C_mul, quadU_coeff_zero]; ring)
    have h2w : HasValGe 1 (2 * W1_0) := ((HasValGe.of_nat 2).mul HasValGe_W1_0).mono (by omega)
    rw [add_comm]
    exact hbW0.add_high h2w
  have h2W0_ne : k5Params.Bv0 * k5Params.Av0_inv ≠ 0 := by
    have hAi : k5Params.Av0_inv ≠ 0 := fun h => by
      have := k5Params_Av0_mul_inv; rw [h, mul_zero] at this; exact zero_ne_one this
    exact mul_ne_zero k5Params_Bv0_ne hAi
  -- Denominator has `HasValGe 13` and nonzero coeff 13!
  obtain ⟨hres_val, hres_ne⟩ : HasValGe 13 res ∧ res.coeff 13 ≠ 0 := res_z_W1_0_val_ne
  clear_value res
  have hden_L : ValLead 13
      (81 * HahnSeries.C k5Params.Av0 * (2 * W1_0 + evalT k5Params.bW) *
        evalT k5Params.Q5_z ^ 3 * res)
      (81 * k5Params.Av0 * (k5Params.Bv0 * k5Params.Av0_inv) *
        ((15625 / 59049 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 4) ^ 3 * res.coeff 13) := by
    have h := ((((ValLead.of_nat 81).mul (ValLead.of_C k5Params.Av0)).mul h2W_L).mul
      (hQ5_L.pow 3)).mul ⟨hres_val, rfl⟩
    exact h.eq_k (by omega) |>.eq_c (by push_cast; rfl)
  have hden_ne : (81 * HahnSeries.C k5Params.Av0 * (2 * W1_0 + evalT k5Params.bW) *
      evalT k5Params.Q5_z ^ 3 * res).coeff 13 ≠ 0 := by
    rw [hden_L.c0]
    have h81 : (81 : K5) ≠ 0 := by exact_mod_cast (by decide : (81 : ℕ) ≠ 0)
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h81 k5Params_Av0_ne) h2W0_ne)
      (pow_ne_zero 3 hQ50_ne)) hres_ne
  -- Helper `toUW` along `W1_0`: `ValLead 2 (toUW v0 v1 v2) v0`!
  have htoUW_1 (v0 v1 v2 : K5) :
      ValLead 2 (PairAlg.evalAt W1_0 (PairAlg.map evalT (k5Params.toUW v0 v1 v2))) v0 := by
    have heq : PairAlg.evalAt W1_0 (PairAlg.map evalT (k5Params.toUW v0 v1 v2)) =
        HahnSeries.C v0 * HahnSeries.single 2 1 +
        (HahnSeries.C v2 * W1_0 ^ 2 + HahnSeries.C v1 * HahnSeries.single 1 1 * W1_0) := by
      simp only [PairAlg.evalAt, PairAlg.map, CoverParams.toUW, map_sub, map_mul, map_pow,
        evalT_C, evalT_X, HahnSeries.single_pow]
      have h2p : (2 : ℕ) • (1 : ℤ) = 2 := by decide
      simp only [one_pow, h2p]
      linear_combination -HahnSeries.C v2 * W1_0_eq
    rw [heq]
    have ht0 : ValLead 2 (HahnSeries.C v0 * HahnSeries.single 2 1) v0 :=
      ((ValLead.of_C v0).mul (ValLead.of_single 2 1)).eq_k (by omega) |>.eq_c (mul_one v0)
    have ht1 : HasValGe 3 (HahnSeries.C v2 * W1_0 ^ 2 + HahnSeries.C v1 * HahnSeries.single 1 1 * W1_0) :=
      (((HasValGe.of_C v2).mul (HasValGe_W1_0.pow 2)).mono (by omega)).add
        ((((HasValGe.of_C v1).mul (HasValGe.single 1 1)).mul HasValGe_W1_0).mono (by omega))
    exact ht0.add_high ht1
  have hc0W_L : ValLead 2 c0W k5Params.c0_V0 := htoUW_1 _ _ _
  have hk2W_L : ValLead 2 (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.k2W)) k5Params.k2_V0 :=
    htoUW_1 _ _ _
  have hk3W_L : ValLead 2 (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.k3W)) k5Params.k3_V0 :=
    htoUW_1 _ _ _
  -- Valuations of `d2_2..0, d3_3..0, d1, d0` along `W1_0`!
  have hd2_2_L : ValLead 0 d2_2 ((15625 / 59049 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 4) := by
    simpa only [d2_2, CoverParams.d2_2, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar] using hQ5_L
  have hd2_1_L : ValLead 2 d2_1 (-(1250 / 729 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 2 * k5Params.c0_V0) := by
    simp only [d2_1, CoverParams.d2_1, PairAlg.map_smul, PairAlg.evalAt_smul]
    have hsc : ValLead 0 (evalT (-k5Params.q11 * k5Params.cb_h + 2 * k5Params.q02 * k5Params.ca_h))
        (-(1250 / 729 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 2) := (ValLead.of_evalT _).eq_c (by
      simp only [Polynomial.coeff_zero_eq_eval_zero, CoverParams.q11, CoverParams.q02,
        CoverParams.ca_h, CoverParams.cb_h, CoverParams.quadU,
        CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3, k5Params_S, k5Params_Q,
        eval_add, eval_neg, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat]; ring)
    exact (hsc.mul hc0W_L).eq_k (by omega)
  have hd2_0_L : ValLead 4 d2_0
      (-(25 / 3 : K5) * S_K * k5Params.c0_V0 ^ 2 +
       ((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)) ^ 2 * (w2 * k5Params.k2_V0)) := by
    simp only [d2_0, CoverParams.d2_0, CoverParams.pmul, PairAlg.map_add, PairAlg.map_smul,
      PairAlg.map_mul, PairAlg.map_W, PairAlg.evalAt_add, PairAlg.evalAt_smul,
      PairAlg.evalAt_mul _ _ W1_0 W1_0_eq, PairAlg.evalAt_W, map_pow]
    have hq02 : ValLead 0 (evalT k5Params.q02) (-(25 / 3 : K5) * S_K) := (ValLead.of_evalT _).eq_c (by
      simp only [CoverParams.q02, quadU_coeff_zero, k5Params_inv3, k5Params_S]; ring)
    exact ((hq02.mul (hc0W_L.mul hc0W_L)).eq_k (by omega) |>.eq_c (by ring)).add
      (((hcb_L.pow 2).mul (hw2_L.mul hk2W_L)).eq_k (by omega))
  have hd3_3_L : ValLead 0 (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_3))
      (-(781250 / 4782969 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 5) := by
    simp only [CoverParams.d3_3, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar]
    exact (ValLead.of_evalT _).eq_c (by
      simp only [Polynomial.coeff_zero_eq_eval_zero, CoverParams.Q7_z, CoverParams.c30,
        CoverParams.c21, CoverParams.c12, CoverParams.c03, CoverParams.ca_h, CoverParams.cb_h,
        CoverParams.quadU, CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, CoverParams.inv243,
        k5Params_inv3, k5Params_S, k5Params_Q, eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X]; ring)
  have hd3_2_L : ValLead 2 (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_2))
      ((62500 / 19683 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 3 * k5Params.c0_V0) := by
    simp only [CoverParams.d3_2, PairAlg.map_smul, PairAlg.evalAt_smul]
    have hsc : ValLead 0 (evalT (-k5Params.c21 * k5Params.cb_h ^ 2 +
        2 * k5Params.c12 * k5Params.ca_h * k5Params.cb_h - 3 * k5Params.c03 * k5Params.ca_h ^ 2))
        ((62500 / 19683 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 3) := (ValLead.of_evalT _).eq_c (by
      simp only [Polynomial.coeff_zero_eq_eval_zero, CoverParams.c21, CoverParams.c12, CoverParams.c03,
        CoverParams.ca_h, CoverParams.cb_h, CoverParams.quadU, CoverParams.inv9, CoverParams.inv27,
        CoverParams.inv81, k5Params_inv3, k5Params_S, k5Params_Q,
        eval_add, eval_sub, eval_neg, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat]; ring)
    exact (hsc.mul hc0W_L).eq_k (by omega)
  have hd3_1_L : ValLead 4 (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_1))
      (-(1250 / 81 : K5) * S_K * (5 * S_K - 9 * Q_K) * k5Params.c0_V0 ^ 2) := by
    simp only [CoverParams.d3_1, CoverParams.pmul, PairAlg.map_smul, PairAlg.map_mul,
      PairAlg.evalAt_smul, PairAlg.evalAt_mul _ _ W1_0 W1_0_eq]
    have hsc : ValLead 0 (evalT (k5Params.c12 * k5Params.cb_h - 3 * k5Params.c03 * k5Params.ca_h))
        (-(1250 / 81 : K5) * S_K * (5 * S_K - 9 * Q_K)) := (ValLead.of_evalT _).eq_c (by
      simp only [Polynomial.coeff_zero_eq_eval_zero, CoverParams.c12, CoverParams.c03,
        CoverParams.ca_h, CoverParams.cb_h, CoverParams.quadU, CoverParams.inv9, CoverParams.inv27,
        CoverParams.inv81, k5Params_inv3, k5Params_S, k5Params_Q,
        eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat]; ring)
    exact (hsc.mul (hc0W_L.mul hc0W_L)).eq_k (by omega) |>.eq_c (by ring)
  have hd3_0_L : ValLead 6 (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_0))
      (((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)) ^ 3 * (w2 ^ 2 * k5Params.k3_V0)) := by
    simp only [CoverParams.d3_0, CoverParams.pmul, PairAlg.map_add, PairAlg.map_smul, PairAlg.map_mul,
      PairAlg.map_W, PairAlg.evalAt_add, PairAlg.evalAt_smul, PairAlg.evalAt_mul _ _ W1_0 W1_0_eq,
      PairAlg.evalAt_W, map_neg, map_pow]
    have hc03 : HasValGe 1 (evalT k5Params.c03) :=
      (HasValGe.evalT _).inc (by
        change (evalT k5Params.c03).coeff (0 : ℕ) = 0
        rw [evalT_coeff]; simp [CoverParams.c03, CoverParams.quadU])
    have ht7 : HasValGe 7 (-evalT k5Params.c03 * (c0W * (c0W * c0W))) :=
      (hc03.neg.mul (hc0W_L.val.mul (hc0W_L.val.mul hc0W_L.val))).mono (by omega)
    rw [add_comm]
    exact (((hcb_L.pow 3).mul ((hw2_L.mul hw2_L).mul hk3W_L)).eq_k (by omega) |>.eq_c (by ring)).add_high ht7
  have hd1_val : HasValGe 4 d1 := by
    simp only [d1, CoverParams.d1_z, CoverParams.pmul, PairAlg.map_sub, PairAlg.map_mul,
      PairAlg.evalAt_sub, PairAlg.evalAt_mul _ _ W1_0 W1_0_eq]
    exact ((hd2_2_L.val.mul ((hd2_2_L.val.mul hd3_1_L.val).sub (hd2_0_L.val.mul hd3_3_L.val))).mono (by omega)).sub
      ((hd2_1_L.val.mul ((hd2_2_L.val.mul hd3_2_L.val).sub (hd2_1_L.val.mul hd3_3_L.val))).mono (by omega))
  have hd0_val : HasValGe 6 d0 := by
    simp only [d0, CoverParams.d0_z, CoverParams.pmul, PairAlg.map_sub, PairAlg.map_mul,
      PairAlg.evalAt_sub, PairAlg.evalAt_mul _ _ W1_0 W1_0_eq]
    exact ((hd2_2_L.val.mul (hd2_2_L.val.mul hd3_0_L.val)).mono (by omega)).sub
      ((hd2_0_L.val.mul ((hd2_2_L.val.mul hd3_2_L.val).sub (hd2_1_L.val.mul hd3_3_L.val))).mono (by omega))
  have hd1_eq : remDeg3_d1 d2_2 d2_1 d2_0
      (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_3))
      (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_2))
      (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_1)) = d1 := by
    simp only [d1, CoverParams.d1_z, CoverParams.pmul, PairAlg.map_sub, PairAlg.map_mul,
      PairAlg.evalAt_sub, PairAlg.evalAt_mul _ _ W1_0 W1_0_eq, remDeg3_d1]; rfl
  have hd0_eq : remDeg3_d0 d2_2 d2_1 d2_0
      (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_3))
      (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_2))
      (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_0)) = d0 := by
    simp only [d0, CoverParams.d0_z, CoverParams.pmul, PairAlg.map_sub, PairAlg.map_mul,
      PairAlg.evalAt_sub, PairAlg.evalAt_mul _ _ W1_0 W1_0_eq, remDeg3_d0]; rfl
  clear_value d2_2 d2_1 d2_0 d1 d0
  -- Common leading root `z1 = w2 * S_K / T_K` (`(5S - 9Q)^2 * z1 = -(5T - 9)^2`)!
  set z1 : K5 := w2 * S_K / T_K
  have hw2_eq : S_K * (5 * S_K - 9 * Q_K) ^ 2 * w2 = -T_K * (5 * T_K - 9) ^ 2 := by
    dsimp only [w2]
    rw [mul_neg, mul_div_assoc', neg_eq_iff_eq_neg, div_eq_iff k5Params_Bv0_ne]
    simp only [CoverParams.Cv0, CoverParams.Bv0, CoverParams.inv243, k5Params_inv3,
      k5Params_S, k5Params_Q, k5Params_T]; ring
  have hz1_mul : (5 * S_K - 9 * Q_K) ^ 2 * z1 = -(5 * T_K - 9) ^ 2 := by
    apply mul_left_cancel₀ hT
    have h1 : T_K * ((5 * S_K - 9 * Q_K) ^ 2 * z1) = S_K * (5 * S_K - 9 * Q_K) ^ 2 * w2 := by
      dsimp only [z1]; field_simp [hT]
    rw [h1, hw2_eq]; ring
  -- Show `HasValGe 3 (g (single 2 c))` for all `c : K5`, AND `(g (single 2 z1)).coeff 3 = 0`!
  have hg_scaled : ∀ c : K5, HasValGe 3 (g (HahnSeries.single 2 c)) ∧
      (c = z1 → (g (HahnSeries.single 2 c)).coeff 3 = 0) :=
    br1_0_g_scaled hw2_ne hcb0_ne hw2_L hU_L hV_L hca_L hcb_L hc0W_L rfl hw2_eq hz1_mul
  -- Apply `HasValGe.interp4_scaled` (`s = 2, k = 3`) -> `p4..p0` have `val ≥ -5, -3, -1, 1, 3`!
  have hg_deg4 : IsPolyDeg 4 g := by
    have h := P18_of_isPolyDeg4 (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V (1 / W1_0) 0 (-ca / (W1_0 * cb)) (-c0W / (W1_0 * cb))
    refine h.congr (fun z => ?_)
    dsimp only [g]
    have hW_ne : W1_0 ≠ 0 := fun h0 => hw2_ne (by rw [← hw2_L.c0, h0]; rfl)
    have hcb_ne : cb ≠ 0 := fun h0 => hcb0_ne (by rw [← hcb_L.c0, h0]; rfl)
    congr 1
    · ring
    · field_simp [hW_ne, hcb_ne]; ring
  obtain ⟨hp4, hp3, hp2, hp1, hp0⟩ : HasValGe (-5) p.1 ∧ HasValGe (-3) p.2.1 ∧
      HasValGe (-1) p.2.2.1 ∧ HasValGe 1 p.2.2.2.1 ∧ HasValGe 3 p.2.2.2.2 :=
    hp_def.symm ▸ HasValGe.interp4_scaled (s := 2) (k := 3) hg_deg4 (fun c => (hg_scaled c).1)
  -- Hence `HasValGe 1 P1` and `HasValGe 3 P0`!
  have hP1_val : HasValGe 1 P1 := by
    rw [hP1_def]; simp only [remDeg4_P1]
    have hr3 : HasValGe (-3) (d2_2 * p.2.1 - d2_1 * p.1) :=
      ((hd2_2_L.val.mul hp3).mono (by omega)).sub ((hd2_1_L.val.mul hp4).mono (by omega))
    have hr2 : HasValGe (-1) (d2_2 * p.2.2.1 - d2_0 * p.1) :=
      ((hd2_2_L.val.mul hp2).mono (by omega)).sub ((hd2_0_L.val.mul hp4).mono (by omega))
    have hs2 : HasValGe (-1) (d2_2 * (d2_2 * p.2.2.1 - d2_0 * p.1) - d2_1 * (d2_2 * p.2.1 - d2_1 * p.1)) :=
      ((hd2_2_L.val.mul hr2).mono (by omega)).sub ((hd2_1_L.val.mul hr3).mono (by omega))
    have hs1 : HasValGe 1 (d2_2 ^ 2 * p.2.2.2.1 - d2_0 * (d2_2 * p.2.1 - d2_1 * p.1)) :=
      (((hd2_2_L.val.pow 2).mul hp1).mono (by omega)).sub ((hd2_0_L.val.mul hr3).mono (by omega))
    exact ((hd2_2_L.val.mul hs1).mono (by omega)).sub ((hd2_1_L.val.mul hs2).mono (by omega))
  have hP0_val : HasValGe 3 P0 := by
    rw [hP0_def]; simp only [remDeg4_P0]
    have hr3 : HasValGe (-3) (d2_2 * p.2.1 - d2_1 * p.1) :=
      ((hd2_2_L.val.mul hp3).mono (by omega)).sub ((hd2_1_L.val.mul hp4).mono (by omega))
    have hr2 : HasValGe (-1) (d2_2 * p.2.2.1 - d2_0 * p.1) :=
      ((hd2_2_L.val.mul hp2).mono (by omega)).sub ((hd2_0_L.val.mul hp4).mono (by omega))
    have hs2 : HasValGe (-1) (d2_2 * (d2_2 * p.2.2.1 - d2_0 * p.1) - d2_1 * (d2_2 * p.2.1 - d2_1 * p.1)) :=
      ((hd2_2_L.val.mul hr2).mono (by omega)).sub ((hd2_1_L.val.mul hr3).mono (by omega))
    exact (((hd2_2_L.val.pow 3).mul hp0).mono (by omega)).sub ((hd2_0_L.val.mul hs2).mono (by omega))
  -- Evaluate `E2(single 2 z1)` (`HasValGe 5`), `E3(single 2 z1)` (`HasValGe 7`), and `g(single 2 z1)` (`HasValGe 4`)!
  set β : LaurentSeries K5 := HahnSeries.single 2 z1
  have hβ_L : ValLead 2 β z1 := ValLead.of_single 2 z1
  have hE2_β : HasValGe 5 (d2_2 * β ^ 2 + d2_1 * β + d2_0) := by
    have hL := (((hd2_2_L.mul (hβ_L.pow 2)).eq_k (by omega)).add ((hd2_1_L.mul hβ_L).eq_k (by omega))).add hd2_0_L
    refine (hL.eq_c ?_).hasValGe_succ
    apply mul_left_cancel₀ (mul_ne_zero hS (pow_ne_zero 4 hA))
    rw [mul_zero]
    have hstep :
        S_K * (5 * S_K - 9 * Q_K) ^ 4 *
          ((15625 / 59049 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 4 * z1 ^ 2 +
           -(1250 / 729) * S_K * (5 * S_K - 9 * Q_K) ^ 2 * k5Params.c0_V0 * z1 +
           (-(25 / 3) * S_K * k5Params.c0_V0 ^ 2 + ((50 / 27) * S_K * (5 * S_K - 9 * Q_K)) ^ 2 * (w2 * k5Params.k2_V0))) =
        (15625 / 59049 : K5) * S_K ^ 2 * (5 * S_K - 9 * Q_K) ^ 4 * ((5 * S_K - 9 * Q_K) ^ 2 * z1) ^ 2 -
        (1250 / 729) * S_K ^ 2 * (5 * S_K - 9 * Q_K) ^ 4 * k5Params.c0_V0 * ((5 * S_K - 9 * Q_K) ^ 2 * z1) -
        (25 / 3) * S_K ^ 2 * (5 * S_K - 9 * Q_K) ^ 4 * k5Params.c0_V0 ^ 2 +
        (2500 / 729) * S_K ^ 2 * (5 * S_K - 9 * Q_K) ^ 4 * k5Params.k2_V0 * (S_K * (5 * S_K - 9 * Q_K) ^ 2 * w2) := by ring
    rw [hstep, hz1_mul, hw2_eq]
    simp only [CoverParams.c0_V0, CoverParams.k2_V0, CoverParams.inv81, k5Params_inv3, k5Params_T]
    generalize 5 * S_K - 9 * Q_K = A'
    ring
  have hE3_β : HasValGe 7 (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_3) * β ^ 3 +
      PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_2) * β ^ 2 +
      PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_1) * β +
      PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_0)) := by
    have hL := ((((hd3_3_L.mul (hβ_L.pow 3)).eq_k (by omega)).add
      ((hd3_2_L.mul (hβ_L.pow 2)).eq_k (by omega))).add ((hd3_1_L.mul hβ_L).eq_k (by omega))).add hd3_0_L
    refine (hL.eq_c ?_).hasValGe_succ
    apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 hS) (pow_ne_zero 6 hA))
    rw [mul_zero]
    have hstep :
        S_K ^ 2 * (5 * S_K - 9 * Q_K) ^ 6 *
          (-(781250 / 4782969 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 5 * z1 ^ 3 +
           (62500 / 19683) * S_K * (5 * S_K - 9 * Q_K) ^ 3 * k5Params.c0_V0 * z1 ^ 2 +
           -(1250 / 81) * S_K * (5 * S_K - 9 * Q_K) * k5Params.c0_V0 ^ 2 * z1 +
           ((50 / 27) * S_K * (5 * S_K - 9 * Q_K)) ^ 3 * (w2 ^ 2 * k5Params.k3_V0)) =
        -(781250 / 4782969 : K5) * S_K ^ 3 * (5 * S_K - 9 * Q_K) ^ 5 * ((5 * S_K - 9 * Q_K) ^ 2 * z1) ^ 3 +
        (62500 / 19683) * S_K ^ 3 * (5 * S_K - 9 * Q_K) ^ 5 * k5Params.c0_V0 * ((5 * S_K - 9 * Q_K) ^ 2 * z1) ^ 2 -
        (1250 / 81) * S_K ^ 3 * (5 * S_K - 9 * Q_K) ^ 5 * k5Params.c0_V0 ^ 2 * ((5 * S_K - 9 * Q_K) ^ 2 * z1) +
        (125000 / 19683) * S_K ^ 3 * (5 * S_K - 9 * Q_K) ^ 5 * k5Params.k3_V0 * (S_K * (5 * S_K - 9 * Q_K) ^ 2 * w2) ^ 2 := by ring
    rw [hstep, hz1_mul, hw2_eq]
    simp only [CoverParams.c0_V0, CoverParams.k3_V0, CoverParams.inv81, CoverParams.inv243, k5Params_inv3, k5Params_T]
    generalize 5 * S_K - 9 * Q_K = A'
    ring
  -- By `remDeg4_eq` and `remDeg3_eq` at `β`: `P1.coeff 1 * z1 + P0.coeff 3 = 0` AND `d1.coeff 4 * z1 + d0.coeff 6 = 0`!
  have hP_lin : P1.coeff 1 * z1 + P0.coeff 3 = 0 := by
    have hrem := remDeg4_eq d2_2 d2_1 d2_0 p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 β
    rw [← hP1_def, ← hP0_def] at hrem
    conv_lhs at hrem => rw [hp_def]; dsimp only [interp4]; rw [← hg_deg4.eq_deg4 β]
    have hβ_def : β = HahnSeries.single 2 z1 := rfl
    have hgβ : HasValGe 4 (g β) := hβ_def.symm ▸ ((hg_scaled z1).1.inc ((hg_scaled z1).2 rfl))
    have hlhs : HasValGe 4 (d2_2 ^ 3 * g β) := ((hd2_2_L.val.pow 3).mul hgβ).mono (by omega)
    have hQ : HasValGe (-1) (d2_2 ^ 2 * p.1 * β ^ 2 + d2_2 * (d2_2 * p.2.1 - d2_1 * p.1) * β +
        (d2_2 * (d2_2 * p.2.2.1 - d2_0 * p.1) - d2_1 * (d2_2 * p.2.1 - d2_1 * p.1))) := by
      have ha : HasValGe (-1) _ := (((hd2_2_L.val.pow 2).mul hp4).mul (hβ_L.val.pow 2)).mono (by omega)
      have hb : HasValGe (-1) _ := ((hd2_2_L.val.mul (((hd2_2_L.val.mul hp3).mono (k2 := -3) (by omega)).sub
        ((hd2_1_L.val.mul hp4).mono (k2 := -3) (by omega)))).mul hβ_L.val).mono (by omega)
      have hc : HasValGe (-1) _ := ((hd2_2_L.val.mul (((hd2_2_L.val.mul hp2).mono (k2 := -1) (by omega)).sub
        ((hd2_0_L.val.mul hp4).mono (k2 := -1) (by omega)))).mono (k2 := -1) (by omega)).sub
        ((hd2_1_L.val.mul (((hd2_2_L.val.mul hp3).mono (k2 := -3) (by omega)).sub
        ((hd2_1_L.val.mul hp4).mono (k2 := -3) (by omega)))).mono (k2 := -1) (by omega))
      exact (ha.add hb).add hc
    have hmul4 : HasValGe 4 ((d2_2 ^ 2 * p.1 * β ^ 2 + d2_2 * (d2_2 * p.2.1 - d2_1 * p.1) * β +
        (d2_2 * (d2_2 * p.2.2.1 - d2_0 * p.1) - d2_1 * (d2_2 * p.2.1 - d2_1 * p.1))) *
        (d2_2 * β ^ 2 + d2_1 * β + d2_0)) := (hQ.mul hE2_β).mono (by omega)
    have hc3 := congrArg (fun f : LaurentSeries K5 => f.coeff 3) hrem
    rw [hlhs 3 (by omega), HahnSeries.coeff_add, hmul4 3 (by omega), zero_add, HahnSeries.coeff_add,
      show (3 : ℤ) = 1 + 2 by omega, hP1_val.coeff_mul_min hβ_L.val, hβ_L.c0] at hc3
    exact hc3.symm
  have hd_lin : d1.coeff 4 * z1 + d0.coeff 6 = 0 := by
    have hrem := remDeg3_eq d2_2 d2_1 d2_0
      (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_3))
      (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_2))
      (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_1))
      (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_0)) β
    rw [hd1_eq, hd0_eq] at hrem
    have hlhs : HasValGe 7 (d2_2 ^ 2 * _) := ((hd2_2_L.val.pow 2).mul hE3_β).mono (by omega)
    have hQ : HasValGe 2 (d2_2 * PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_3) * β +
        (d2_2 * PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_2) -
         d2_1 * PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_3))) :=
      (((hd2_2_L.val.mul hd3_3_L.val).mul hβ_L.val).mono (by omega)).add
        (((hd2_2_L.val.mul hd3_2_L.val).mono (by omega)).sub ((hd2_1_L.val.mul hd3_3_L.val).mono (by omega)))
    have hmul7 : HasValGe 7 ((d2_2 * PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_3) * β +
        (d2_2 * PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_2) -
         d2_1 * PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_3))) *
        (d2_2 * β ^ 2 + d2_1 * β + d2_0)) := (hQ.mul hE2_β).mono (by omega)
    have hc6 := congrArg (fun f : LaurentSeries K5 => f.coeff 6) hrem
    rw [hlhs 6 (by omega), HahnSeries.coeff_add, hmul7 6 (by omega), zero_add, HahnSeries.coeff_add,
      show (6 : ℤ) = 4 + 2 by omega, hd1_val.coeff_mul_min hβ_L.val, hβ_L.c0] at hc6
    exact hc6.symm
  -- Therefore `(P1 * d0 - P0 * d1)` jumps from 7 to 8, numerator jumps to 13, and quotient has `HasValGe 0`!
  have hcomb_8 : HasValGe 8 (P1 * d0 - P0 * d1) := by
    have h7 : HasValGe 7 (P1 * d0 - P0 * d1) :=
      ((hP1_val.mul hd0_val).mono (by omega)).sub ((hP0_val.mul hd1_val).mono (by omega))
    apply h7.inc
    rw [HahnSeries.coeff_sub, show (7 : ℤ) = 1 + 6 by omega, hP1_val.coeff_mul_min hd0_val,
      show (1 + 6 : ℤ) = 3 + 4 by omega, hP0_val.coeff_mul_min hd1_val]
    linear_combination P1.coeff 1 * hd_lin - d1.coeff 4 * hP_lin
  have hnum_13 : HasValGe 13 (-(P1 * d0 - P0 * d1) * U ^ 3 * W1_0 * cb ^ 4) :=
    (((hcomb_8.neg.mul (hU_L.val.pow 3)).mul HasValGe_W1_0).mul (hcb_L.val.pow 4)).mono (by omega)
  have hquot_0 : HasValGe 0
      ((-(P1 * d0 - P0 * d1) * U ^ 3 * W1_0 * cb ^ 4) /
        (81 * HahnSeries.C k5Params.Av0 * (2 * W1_0 + evalT k5Params.bW) *
          evalT k5Params.Q5_z ^ 3 * res)) :=
    (hnum_13.div_of_lead_ne hden_L.val hden_ne).1.mono (by omega)
  exact hquot_0 (-1) (by omega)

/-! ### Section 4: Branch 2 (`W2_0`) Exact Residue `(br2_0 eta_AC).coeff (-1) = toK5_RU` -/

-- Sparse `Biv` encoding of `QY_V0`, `EB_V0`, and the cancelled `U = 0` Branch 2 identity!
private def eA5 : Expr := .sub (.mul (.num 5) eS) (.mul (.num 9) eQ)
private def e5S3Q : Expr := .sub (.mul (.num 5) eS) (.mul (.num 3) eQ)
private def eB5 : Expr := .sub eT (.num 3)

private def dH0_7_e : Fin 3 → Expr
  | 0 => .add (.add (.mul (.num (-42)) (.pow eS 2)) (.mul (.num 84) (.mul eS eQ)))
           (.mul (.num (-21)) (.pow eQ 2))
  | 1 => .add (.add (.mul (.num 42) (.pow eS 2)) (.mul (.num (-42)) (.mul eS eQ)))
           (.add (.mul (.num (-42)) (.pow eQ 2)) (.add (.mul (.num 10) eQ) (.num 10)))
  | 2 => .add (.add (.mul (.num (-42)) (.pow eT 2)) (.mul (.num 84) eT)) (.num (-21))

private def dF5_7_biv : Fin 5 → Biv
  | 0 => .cons (.num 21) 2 0 (.cons (dH0_7_e 0) 0 0 .nil)
  | 1 => .cons (dH0_7_e 1) 0 0 .nil
  | 2 => .cons (.num 21) 0 2 (.cons (dH0_7_e 2) 0 0 .nil)
  | 3 => .cons (.mul (.num 42) eS) 1 0 .nil
  | 4 => .cons (.mul (.num 42) eT) 0 1 .nil

private def dDX2_biv : Fin 5 → Biv
  | 0 => .cons (.num (-27)) 2 0
      (.cons (.add (.mul (.num 100) eS) (.mul (.num (-90)) eQ)) 1 0
        (.cons (.add (.add (.mul (.num (-69)) (.pow eS 2)) (.mul (.num 164) (.mul eS eQ)))
          (.mul (.num (-71)) (.pow eQ 2))) 0 0 .nil))
  | 1 => .cons (.mul (.num (-90)) eS) 1 0
      (.cons (.add (.add (.mul (.num 82) (.pow eS 2)) (.mul (.num (-142)) (.mul eS eQ)))
        (.mul (.num (-12)) (.pow eQ 2))) 0 0 .nil)
  | 2 => .nil
  | 3 => .cons (.mul (.num (-54)) eS) 1 0
      (.cons (.add (.mul (.num 50) (.pow eS 2)) (.mul (.num (-90)) (.mul eS eQ))) 0 0 .nil)
  | 4 => .nil

-- `243 * br_V0` (coeff of `V^1` at `U = 0` of `243 * br_fn k`):
private def LY_V1_27_biv : Biv :=
  .cons (.num 27) 0 1 (.cons (.add (.mul (.num (-25)) eT) (.num 45)) 0 0 .nil)

private def LY_V1_9_biv : Biv :=
  .cons (.num 9) 0 1 (.cons (.add (.mul (.num (-25)) eT) (.num 15)) 0 0 .nil)

private def br_V0_243_biv : Fin 5 → Biv
  | 0 => scale (.mul (.num (-5)) (.mul eT e5S3Q)) 0 0 LY_V1_27_biv
  | 1 => scale (.mul (.num 30) (.mul eS eT)) 0 0 LY_V1_27_biv
  | 2 => scale (.mul (.num 5) (.mul eS eA5)) 0 0 LY_V1_9_biv
  | 3 => .nil
  | 4 => .cons (.mul (.num 90) (.mul (.mul eS eT) eA5)) 0 0 .nil

-- `81 * om_V0` (coeff of `V^1` at `U = 0` of `81 * om_fn p q`):
-- `omX(0) = [25*S - 15*Q, -30*S, 0, 0, 0]`, `omY_V1 = [0, 0, -25*T + 9*y + 15, 0, 18*T]`!
private def omX0_e : Fin 5 → Expr
  | 0 => .sub (.mul (.num 25) eS) (.mul (.num 15) eQ)
  | 1 => .mul (.num (-30)) eS
  | _ => .num 0

private def omY_V1_biv : Fin 5 → Biv
  | 2 => .cons (.num 9) 0 1 (.cons (.add (.mul (.num (-25)) eT) (.num 15)) 0 0 .nil)
  | 4 => .cons (.mul (.num 18) eT) 0 0 .nil
  | _ => .nil

private def om_V0_81_biv (p q : Fin 5) : Biv :=
  bivSub (scale (omX0_e p) 0 0 (omY_V1_biv q)) (scale (omX0_e q) 0 0 (omY_V1_biv p))

-- `1701 * QY_V0 i` (`= 243 * 7 * QY_V0 i` so both `3 * (81 * om)` and `243 * br` share factor `243`!)
private def F_contract_7_biv (f2 : Fin 5 → Fin 5 → Biv) (i : Fin 3) : Biv :=
  let idx : Fin 5 := match i with | 0 => 0 | 1 => 1 | 2 => 2
  bivAdd (bivAdd (bivMul (dF5_7_biv 4) (f2 idx 3)) (bivMul (dF5_7_biv 3) (f2 4 idx)))
    (bivMul (dF5_7_biv idx) (f2 3 4))

private def QY_V0_1701_biv (i : Fin 3) : Biv :=
  let Om := F_contract_7_biv (fun p q => scale (.mul (.num 3) (.mul eS eT)) 0 0 (om_V0_81_biv p q)) i
  let dX := F_contract_7_biv (fun p q => scale (.mul eS eT) 0 0
    (bivSub (bivMul (dDX2_biv p) (br_V0_243_biv q)) (bivMul (dDX2_biv q) (br_V0_243_biv p)))) i
  bivMul DY2_biv (bivSub (bivMul DX2_biv Om) dX)

-- `9 * EB_V0 / (S * A5) = -40 * S * T * x * W2`:
private def EB_V0_9_div_SA5_biv : Biv :=
  scale (.mul (.num (-40)) (.mul eS eT)) 1 0 W2_biv

-- Build `q1_int_v_divSA52` and `q1_int_e_red_divSA52` directly as `Biv`s!
-- Wait: recall `QY_V0_1701_biv = 1701 * QY_V0 = 3 * 567 * QY_V0`!
-- So `3 * q1_int = 3 * 11907 * q1`:
--   Term 1 (`H0 * A1 * qY`): `(7 * H0) * (25) * (QY_V0_1701 · (a_num, b_num, den_ab))` (div by `S * A5^2`!)
--     Check factor: `7 * 27 * (1701 / 9) = 7 * 27 * 189 = 35721 = 3 * 11907`!
--   Term 2 (`cA1_div_v * EB`): `189 * (cA1_21_div_A5) * (EB_V0_9_div_SA5)` (div by `S * A5^2`!)
--     Check factor: `189 * 21 * 9 = 35721 = 3 * 11907`!!
private def cA1_21_div_A5_e : Fin 3 → Expr
  | 0 => .sub (.mul H0_int_e (.mul (.num 25) (.sub (.mul (.num 15) eS) (.mul (.num 9) eQ))))
           (.mul (.mul (.num 25) (.mul eS eA5)) (dH0_7_e 0))
  | 1 => .sub (.mul H0_int_e (.mul (.num (-450)) eS))
           (.mul (.mul (.num 25) (.mul eS eA5)) (dH0_7_e 1))
  | 2 => .neg (.mul (.mul (.num 25) (.mul eS eA5)) (dH0_7_e 2))

private def q1_v_35721_biv : Biv :=
  let a0_e := .mul (.num 6) (.pow eS 2)
  let b0_e := .mul (.num 6) (.mul eS eQ)
  let d0_e := .mul (.num 6) (.mul eS eB5)
  let qY0 := bivAdd (bivAdd (scale a0_e 0 0 (QY_V0_1701_biv 0)) (scale b0_e 0 0 (QY_V0_1701_biv 1)))
    (scale d0_e 0 0 (QY_V0_1701_biv 2))
  let t1 := scale (.mul (.num 25) H0_int_e) 0 0 qY0
  let cA0_e := .add (.add (.mul (cA1_21_div_A5_e 0) a0_e) (.mul (cA1_21_div_A5_e 1) b0_e))
    (.mul (cA1_21_div_A5_e 2) d0_e)
  let t2 := scale (.mul (.num 189) cA0_e) 0 0 EB_V0_9_div_SA5_biv
  bivAdd t1 t2

private def q1_e_35721_divB5_biv : Biv :=
  let a1_e := .mul (.num 6) eS
  let b1_e := e5S3Q
  let qY1 := bivAdd (scale a1_e 0 0 (QY_V0_1701_biv 0)) (scale b1_e 0 0 (QY_V0_1701_biv 1))
  let t1 := scale (.mul (.num 25) H0_int_e) 0 0 qY1
  let cA1_e := .add (.mul (cA1_21_div_A5_e 0) a1_e) (.mul (cA1_21_div_A5_e 1) b1_e)
  let t2 := scale (.mul (.num 189) cA1_e) 0 0 EB_V0_9_div_SA5_biv
  bivAdd t1 t2

private def Q_quad_U0_e : Expr :=
  .add (.add (.add (.mul (.num 11943020) (.pow eS 2)) (.mul (.num (-876486)) (.mul eS eQ)))
    (.add (.mul (.num 8382500) (.mul eS eT)) (.mul (.num 5029500) (.mul eQ eT))))
  (.add (.mul (.num (-14837025)) eS) (.mul (.num (-33647355)) eQ))

private def L_U0_e : Expr :=
  .add (.add (.mul (.num 225) eS) (.mul (.num (-45)) eQ)) (.add (.mul (.num 77) eT) (.num (-210)))

private def LHS_U0_biv : Biv :=
  let t1 := scale (.mul (.num 173215980) (.mul eS e5S3Q)) 0 0 q1_e_35721_divB5_biv
  let t2 := scale (.mul (.num (-42)) Q_quad_U0_e) 0 0 q1_v_35721_biv
  let t3 := scale (.mul (.num 8248380) (.mul e5S3Q L_U0_e)) 0 0 q1_v_35721_biv
  bivReduceX2 (bivAdd (bivAdd t1 t2) t3)

private def RHS_U0_biv : Biv :=
  -- `21 * 3 * 189000 = 11907000` (extra factor 3 because `q1_35721 = 3 * q1_11907`)!
  scale (.mul (.num 11907000) (.mul (.pow eS 3) eA5)) 0 0 RU_biv

-- THE KERNEL-VERIFIED 5-VARIABLE `U = 0` RESIDUE IDENTITY (< 1s!)
theorem U0_biv_identity : evalBivK5 LHS_U0_biv = evalBivK5 RHS_U0_biv := by
  apply biv_denote_eq_of_kronecker3 vK5 x_K y_K 20 16 18 (2 ^ 140) LHS_U0_biv RHS_U0_biv
  decide +kernel

-- Bridge `evalBivK5` of `QY_V0_1701_biv`, `EB_V0_9_div_SA5_biv`, `q1_v_35721_biv`, `q1_e_35721_divB5_biv` to `SheetCalculus`!
private lemma evalBivK5_DX2 : evalBivK5 DX2_biv = DX2_of S_K Q_K x_K := by
  simp only [evalBivK5, DX2_biv, denote, ringEval, eS, eQ, vK5, DX2_of, u3_of,
    Int.cast_neg, Int.cast_ofNat]; ring

private lemma evalBivK5_DY2 : evalBivK5 DY2_biv = DY2_of T_K y_K := by
  simp only [evalBivK5, DY2_biv, denote, ringEval, eT, vK5, DY2_of, v3_of,
    Int.cast_neg, Int.cast_ofNat]; ring

private lemma evalBivK5_W2 : evalBivK5 W2_biv = W2_of S_K Q_K T_K x_K y_K := by
  rw [W2_biv, evalBivK5_bivMul, evalBivK5_scale, evalBivK5_DX2, evalBivK5_DY2]
  simp only [ringEval, eS, eT, vK5, W2_of, pow_zero, mul_one]

private lemma ringEval_dH0_7 (k : Fin 3) : ringEval vK5 (dH0_7_e k) = 7 * dH0_fn k S_K Q_K T_K := by
  fin_cases k <;> (simp only [dH0_7_e, dH0_fn, ringEval, eS, eQ, eT, vK5, Int.cast_neg, Int.cast_ofNat]; ring)

private lemma evalBivK5_dF5_7 (k : Fin 5) : evalBivK5 (dF5_7_biv k) = 7 * dF5_fn k S_K Q_K T_K x_K y_K := by
  fin_cases k <;>
    (simp only [evalBivK5, dF5_7_biv, dF5_fn, denote, ringEval, eS, eQ, eT, vK5,
      Int.cast_neg, Int.cast_ofNat, dH0_fn, dH0_7_e]; ring)

private lemma evalBivK5_dDX2 (k : Fin 5) : evalBivK5 (dDX2_biv k) = dDX2_fn k S_K Q_K x_K := by
  fin_cases k <;>
    simp only [evalBivK5, dDX2_biv, dDX2_fn,
       denote, ringEval, eS, eQ, vK5, u3_of, Int.cast_neg, Int.cast_ofNat]
  all_goals ring

private lemma evalBivK5_br_V0_243 (k : Fin 5) :
    evalBivK5 (br_V0_243_biv k) = 243 * (br_fn k S_K Q_K T_K x_K y_K 0 1 - br_fn k S_K Q_K T_K x_K y_K 0 0) := by
  fin_cases k <;>
    (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, evalBivK5, br_V0_243_biv, br_fn,
      LY_V1_27_biv, LY_V1_9_biv, eA5, e5S3Q, 
      scale_denote, denote, ringEval, eS, eQ, eT, vK5,
      LX_of, LY_of, dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of,
      Int.cast_neg, Int.cast_ofNat]; ring)

private lemma evalBivK5_om_V0_81 (p q : Fin 5) :
    evalBivK5 (om_V0_81_biv p q) = 81 * (om_fn p q S_K Q_K T_K x_K y_K 0 1 - om_fn p q S_K Q_K T_K x_K y_K 0 0) := by
  fin_cases p <;> fin_cases q <;>
    (rw [om_V0_81_biv, evalBivK5_bivSub]; simp only [evalBivK5_scale];
     simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, omX0_e, omY_V1_biv, om_fn,
       evalBivK5, denote, ringEval, eS, eQ, eT, vK5, Int.cast_neg, Int.cast_ofNat]; ring)

private lemma evalBivK5_QY_V0_1701 (i : Fin 3) :
    evalBivK5 (QY_V0_1701_biv i) =
      1701 * (QY_num S_K Q_K T_K x_K y_K 0 1 i - QY_num S_K Q_K T_K x_K y_K 0 0 i) := by
  have hQY_lin (V : K5) :
      QY_num S_K Q_K T_K x_K y_K 0 V i - QY_num S_K Q_K T_K x_K y_K 0 0 i =
      DY2_of T_K y_K * (DX2_of S_K Q_K x_K *
        F_contract S_K Q_K T_K x_K y_K (fun p q => S_K * T_K *
          (om_fn p q S_K Q_K T_K x_K y_K 0 V - om_fn p q S_K Q_K T_K x_K y_K 0 0)) i -
        F_contract S_K Q_K T_K x_K y_K (fun p q => S_K * T_K *
          (dDX2_fn p S_K Q_K x_K * (br_fn q S_K Q_K T_K x_K y_K 0 V - br_fn q S_K Q_K T_K x_K y_K 0 0) -
           dDX2_fn q S_K Q_K x_K * (br_fn p S_K Q_K T_K x_K y_K 0 V - br_fn p S_K Q_K T_K x_K y_K 0 0))) i) := by
    simp only [QY_num, Omega_F, dDX2_F, F_contract]; ring
  rw [hQY_lin 1, QY_V0_1701_biv, evalBivK5_bivMul, evalBivK5_DY2, evalBivK5_bivSub,
    evalBivK5_bivMul, evalBivK5_DX2]
  fin_cases i <;> (
    dsimp only [F_contract_7_biv, F_contract]
    simp only [evalBivK5_bivAdd, evalBivK5_bivMul, evalBivK5_scale,
      evalBivK5_bivSub, evalBivK5_dF5_7, evalBivK5_om_V0_81, evalBivK5_dDX2, evalBivK5_br_V0_243,
      ringEval, eS, eT, vK5, Int.cast_ofNat, pow_zero, mul_one]
    ring)

private lemma evalBivK5_EB_V0 :
    S_K * (5 * S_K - 9 * Q_K) * evalBivK5 EB_V0_9_div_SA5_biv = 9 * EB_of S_K Q_K T_K x_K y_K 0 1 := by
  rw [EB_V0_9_div_SA5_biv, evalBivK5_scale, evalBivK5_W2]
  simp only [ringEval, eS, eT, vK5, Int.cast_neg, Int.cast_ofNat, pow_one, pow_zero, mul_one,
    EB_of, dF5_fn, br_fn, LX_of, LY_of, dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of]
  ring

private lemma quad_mul_coeff1 {F : Type*} [Field F] [CharZero F] (p0 p1 p2 q0 q1 q2 : F) :
    p0 * q1 + p1 * q0 =
      (8 * ((p0 + p1 + p2) * (q0 + q1 + q2) - (p0 - p1 + p2) * (q0 - q1 + q2)) -
        ((p0 + 2 * p1 + 4 * p2) * (q0 + 2 * q1 + 4 * q2) -
         (p0 - 2 * p1 + 4 * p2) * (q0 - 2 * q1 + 4 * q2))) / 12 := by ring

private def dHS_12_of {R : Type*} [CommRing R] (ι : K5 →+* R) (s q : R) : Dual R :=
  ⟨ι (-(25 / 243 : K5)) * (5 * s - 9 * q) * (15 * s - 9 * q),
   ι (143 / 81 : K5) * s ^ 2 - ι (184 / 27 : K5) * s * q + ι (52 / 9 : K5) * q ^ 2⟩

private def dHQ_12_of {R : Type*} [CommRing R] (ι : K5 →+* R) (s q : R) (v0 : K5) : Dual R :=
  ⟨ι (50 / 27 : K5) * s * (5 * s - 9 * q),
   ι (-(92 / 27 : K5)) * s ^ 2 + ι (104 / 9 : K5) * s * q - ι (22 / 3 : K5) * q ^ 2 +
     ι ((10 / 7 : K5) * v0) * q + ι ((10 / 7 : K5) * v0 ^ 2)⟩

private def numM_12_of {R : Type*} [CommRing R] (ι : K5 →+* R) (mi : Fin 10) (a b : R) : R :=
  let ξS := ι S_K - a * ι T_K
  let ξQ := ι Q_K - b * ι T_K
  let a2 := dHS_12_of ι a b; let a0 := dHS_12_of ι ξS ξQ
  let a1 := dHS_12_of ι (a + ξS) (b + ξQ) - a2 - a0
  let b2 := dHQ_12_of ι a b 0; let b0 := dHQ_12_of ι ξS ξQ 1
  let b1 := dHQ_12_of ι (a + ξS) (b + ξQ) 0 - b2 - dHQ_12_of ι ξS ξQ 0 + ⟨0, ι (10 / 7 : K5) * b⟩
  let d20 := a2 * b0 - a0 * b2; let d21 := a2 * b1 - a1 * b2; let d10 := a1 * b0 - a0 * b1
  let (m2, m1, m0) : R × R × R := match mi with
    | 0 => (a ^ 2, 2 * a * ξS, ξS ^ 2)
    | 1 => (a * b, a * ξQ + b * ξS, ξS * ξQ)
    | 2 => (b ^ 2, 2 * b * ξQ, ξQ ^ 2)
    | 3 => (a, ξS, 0)
    | 4 => (0, a, ξS)
    | 5 => (b, ξQ, 0)
    | 6 => (0, b, ξQ)
    | 7 => (1, 0, 0)
    | 8 => (0, 1, 0)
    | 9 => (0, 0, 1)
  ι (1 / 16 : K5) * (m2 * d10.eps - m1 * d20.eps + m0 * d21.eps)

private def A0U_12_of {R : Type*} [CommRing R] (ι : K5 →+* R) (a b : R) : R :=
  let m := fun i => numM_12_of ι i a b
  ι (-(19708 / 1257375 : K5)) * (5 * m 0 - 9 * m 1) +
  ι (1472 / 1257375 : K5) * (5 * m 1 - 9 * m 2) -
  ι (16 / 729 : K5) * (5 * m 3 - 9 * m 5) +
  ι (188 / 2025 : K5) * (5 * m 4 - 9 * m 6)

private lemma map_numM_12_of {R R' : Type*} [CommRing R] [CommRing R']
    (f : R →+* R') (ι : K5 →+* R) (mi : Fin 10) (a b : R) :
    f (numM_12_of ι mi a b) = numM_12_of (f.comp ι) mi (f a) (f b) := by
  fin_cases mi <;>
    simp only [numM_12_of, dHS_12_of, dHQ_12_of, Dual.add_val, Dual.add_eps, Dual.sub_val, Dual.sub_eps,
      Dual.mul_eps, map_add, map_sub, map_mul, map_pow, map_ofNat, map_zero, map_one,
      RingHom.comp_apply]

private lemma map_A0U_12_of {R R' : Type*} [CommRing R] [CommRing R']
    (f : R →+* R') (ι : K5 →+* R) (a b : R) :
    f (A0U_12_of ι a b) = A0U_12_of (f.comp ι) (f a) (f b) := by
  simp only [A0U_12_of, map_add, map_sub, map_mul, map_ofNat, RingHom.comp_apply, map_numM_12_of]

private lemma numM_12_of_eq_interp (mi : Fin 10) (a b : K5) :
    numM_12_of (RingHom.id K5) mi a b =
      (8 * (numM mi a b (S_K - a * T_K) (Q_K - b * T_K) 1 1 -
            numM mi a b (S_K - a * T_K) (Q_K - b * T_K) (-1) 1) -
        (numM mi a b (S_K - a * T_K) (Q_K - b * T_K) 2 1 -
         numM mi a b (S_K - a * T_K) (Q_K - b * T_K) (-2) 1)) / 12 := by
  set ξS := S_K - a * T_K
  set ξQ := Q_K - b * T_K
  have hS_form (s q U : K5) :
      dH_dS s q U 1 = (dHS_12_of (RingHom.id K5) s q).val +
        (dHS_12_of (RingHom.id K5) s q).eps * U + (-(4 / 81 : K5) * (s - 3 * q) ^ 2) * U ^ 2 := by
    simp only [dH_dS, dHS_12_of, RingHom.id_apply]; ring
  have hQ_form (s q v0 U : K5) :
      dH_dQ s q v0 U 1 = (dHQ_12_of (RingHom.id K5) s q v0).val +
        (dHQ_12_of (RingHom.id K5) s q v0).eps * U + ((4 / 27 : K5) * (s - 3 * q) ^ 2) * U ^ 2 := by
    simp only [dH_dQ, dHQ_12_of, RingHom.id_apply]; ring
  set a2D := dHS_12_of (RingHom.id K5) a b
  set a0D := dHS_12_of (RingHom.id K5) ξS ξQ
  set a1D := dHS_12_of (RingHom.id K5) (a + ξS) (b + ξQ) - a2D - a0D
  set b2D := dHQ_12_of (RingHom.id K5) a b 0
  set b0D := dHQ_12_of (RingHom.id K5) ξS ξQ 1
  set b1D := dHQ_12_of (RingHom.id K5) (a + ξS) (b + ξQ) 0 - b2D - dHQ_12_of (RingHom.id K5) ξS ξQ 0 +
    ⟨0, (10 / 7 : K5) * b⟩
  set p2_2 : K5 := -(4 / 81 : K5) * (a - 3 * b) ^ 2
  set p0_2 : K5 := -(4 / 81 : K5) * (ξS - 3 * ξQ) ^ 2
  set p1_2 : K5 := -(4 / 81 : K5) * ((a + ξS) - 3 * (b + ξQ)) ^ 2 - p2_2 - p0_2
  set q2_2 : K5 := (4 / 27 : K5) * (a - 3 * b) ^ 2
  set q0_2 : K5 := (4 / 27 : K5) * (ξS - 3 * ξQ) ^ 2
  set q1_2 : K5 := (4 / 27 : K5) * ((a + ξS) - 3 * (b + ξQ)) ^ 2 - q2_2 - q0_2
  have ha2 (U : K5) : q1_a2 a b U 1 = a2D.val + a2D.eps * U + p2_2 * U ^ 2 := hS_form a b U
  have ha0 (U : K5) : q1_a0 ξS ξQ U 1 = a0D.val + a0D.eps * U + p0_2 * U ^ 2 := hS_form ξS ξQ U
  have ha1 (U : K5) : q1_a1 a b ξS ξQ U 1 = a1D.val + a1D.eps * U + p1_2 * U ^ 2 := by
    simp only [q1_a1, hS_form, a1D, Dual.sub_val, Dual.sub_eps, p1_2]; ring
  have hb2 (U : K5) : q2_b2 a b U 1 = b2D.val + b2D.eps * U + q2_2 * U ^ 2 := hQ_form a b 0 U
  have hb0 (U : K5) : q2_b0 ξS ξQ U 1 = b0D.val + b0D.eps * U + q0_2 * U ^ 2 := hQ_form ξS ξQ 1 U
  have hb1 (U : K5) : q2_b1 a b ξS ξQ U 1 = b1D.val + b1D.eps * U + q1_2 * U ^ 2 := by
    simp only [q2_b1, hQ_form, b1D, Dual.add_val, Dual.add_eps, Dual.sub_val, Dual.sub_eps, q1_2]; ring
  have hcomb (m2 m1 m0 : K5) :
      (1 / 16 : K5) * (m2 * (a1D * b0D - a0D * b1D).eps - m1 * (a2D * b0D - a0D * b2D).eps +
        m0 * (a2D * b1D - a1D * b2D).eps) =
      (8 * ((1 / 16 : K5) * (m2 * ((a1D.val + a1D.eps * 1 + p1_2 * 1 ^ 2) * (b0D.val + b0D.eps * 1 + q0_2 * 1 ^ 2) -
            (a0D.val + a0D.eps * 1 + p0_2 * 1 ^ 2) * (b1D.val + b1D.eps * 1 + q1_2 * 1 ^ 2)) -
          m1 * ((a2D.val + a2D.eps * 1 + p2_2 * 1 ^ 2) * (b0D.val + b0D.eps * 1 + q0_2 * 1 ^ 2) -
            (a0D.val + a0D.eps * 1 + p0_2 * 1 ^ 2) * (b2D.val + b2D.eps * 1 + q2_2 * 1 ^ 2)) +
          m0 * ((a2D.val + a2D.eps * 1 + p2_2 * 1 ^ 2) * (b1D.val + b1D.eps * 1 + q1_2 * 1 ^ 2) -
            (a1D.val + a1D.eps * 1 + p1_2 * 1 ^ 2) * (b2D.val + b2D.eps * 1 + q2_2 * 1 ^ 2))) -
        (1 / 16 : K5) * (m2 * ((a1D.val + a1D.eps * (-1) + p1_2 * (-1) ^ 2) * (b0D.val + b0D.eps * (-1) + q0_2 * (-1) ^ 2) -
            (a0D.val + a0D.eps * (-1) + p0_2 * (-1) ^ 2) * (b1D.val + b1D.eps * (-1) + q1_2 * (-1) ^ 2)) -
          m1 * ((a2D.val + a2D.eps * (-1) + p2_2 * (-1) ^ 2) * (b0D.val + b0D.eps * (-1) + q0_2 * (-1) ^ 2) -
            (a0D.val + a0D.eps * (-1) + p0_2 * (-1) ^ 2) * (b2D.val + b2D.eps * (-1) + q2_2 * (-1) ^ 2)) +
          m0 * ((a2D.val + a2D.eps * (-1) + p2_2 * (-1) ^ 2) * (b1D.val + b1D.eps * (-1) + q1_2 * (-1) ^ 2) -
            (a1D.val + a1D.eps * (-1) + p1_2 * (-1) ^ 2) * (b2D.val + b2D.eps * (-1) + q2_2 * (-1) ^ 2)))) -
       ((1 / 16 : K5) * (m2 * ((a1D.val + a1D.eps * 2 + p1_2 * 2 ^ 2) * (b0D.val + b0D.eps * 2 + q0_2 * 2 ^ 2) -
            (a0D.val + a0D.eps * 2 + p0_2 * 2 ^ 2) * (b1D.val + b1D.eps * 2 + q1_2 * 2 ^ 2)) -
          m1 * ((a2D.val + a2D.eps * 2 + p2_2 * 2 ^ 2) * (b0D.val + b0D.eps * 2 + q0_2 * 2 ^ 2) -
            (a0D.val + a0D.eps * 2 + p0_2 * 2 ^ 2) * (b2D.val + b2D.eps * 2 + q2_2 * 2 ^ 2)) +
          m0 * ((a2D.val + a2D.eps * 2 + p2_2 * 2 ^ 2) * (b1D.val + b1D.eps * 2 + q1_2 * 2 ^ 2) -
            (a1D.val + a1D.eps * 2 + p1_2 * 2 ^ 2) * (b2D.val + b2D.eps * 2 + q2_2 * 2 ^ 2))) -
        (1 / 16 : K5) * (m2 * ((a1D.val + a1D.eps * (-2) + p1_2 * (-2) ^ 2) * (b0D.val + b0D.eps * (-2) + q0_2 * (-2) ^ 2) -
            (a0D.val + a0D.eps * (-2) + p0_2 * (-2) ^ 2) * (b1D.val + b1D.eps * (-2) + q1_2 * (-2) ^ 2)) -
          m1 * ((a2D.val + a2D.eps * (-2) + p2_2 * (-2) ^ 2) * (b0D.val + b0D.eps * (-2) + q0_2 * (-2) ^ 2) -
            (a0D.val + a0D.eps * (-2) + p0_2 * (-2) ^ 2) * (b2D.val + b2D.eps * (-2) + q2_2 * (-2) ^ 2)) +
          m0 * ((a2D.val + a2D.eps * (-2) + p2_2 * (-2) ^ 2) * (b1D.val + b1D.eps * (-2) + q1_2 * (-2) ^ 2) -
            (a1D.val + a1D.eps * (-2) + p1_2 * (-2) ^ 2) * (b2D.val + b2D.eps * (-2) + q2_2 * (-2) ^ 2))))) / 12 := by
    simp only [Dual.sub_eps, Dual.mul_eps]
    ring
  fin_cases mi <;> (
    simp only [numM_12_of, numM, ha2, ha1, ha0, hb2, hb1, hb0, RingHom.id_apply]
    exact hcomb _ _ _)


private lemma br2_0_numM_bounds
    {a_s b_s U V : LaurentSeries K5} {a0 b0 w0 : K5}
    (hw0_ne : w0 ≠ 0)
    (ha_L : ValLead 0 a_s a0) (hb_L : ValLead 0 b_s b0)
    (hU_L : ValLead 1 U 1) (hV_L : ValLead (-1) V w0) :
    let ξS_s := HahnSeries.C S_K - a_s * HahnSeries.C T_K
    let ξQ_s := HahnSeries.C Q_K - b_s * HahnSeries.C T_K
    ValLead (-2) (A_0U a_s b_s ξS_s ξQ_s U V / U + A_0V a_s b_s ξS_s ξQ_s U V / V)
      (w0 ^ 2 * A0U_12_of (RingHom.id K5) a0 b0) ∧
    HasValGe (-2) (A_Y a_s b_s ξS_s ξQ_s U V) ∧
    HasValGe (-1) (A_X a_s b_s ξS_s ξQ_s U V) := by
  let dHS_D : K5 → K5 → Dual K5 := fun s q =>
    ⟨-(25 / 243 : K5) * (5 * s - 9 * q) * (15 * s - 9 * q) * w0,
     ((143 / 81 : K5) * s ^ 2 - (184 / 27) * s * q + (52 / 9) * q ^ 2) * w0⟩
  let dHQ_D : K5 → K5 → K5 → Dual K5 := fun s q v0 =>
    ⟨(50 / 27 : K5) * s * (5 * s - 9 * q) * w0,
     (-(92 / 27 : K5) * s ^ 2 + (104 / 9) * s * q - (22 / 3) * q ^ 2 +
      (10 / 7) * q * v0 + (10 / 7) * v0 ^ 2) * w0⟩
  let numM_D : Fin 10 → K5 → K5 → Dual K5 := fun mi a b =>
    let ξS := S_K - a * T_K; let ξQ := Q_K - b * T_K
    let a2 := dHS_D a b; let a0 := dHS_D ξS ξQ
    let a1 := dHS_D (a + ξS) (b + ξQ) - a2 - a0
    let b2 := dHQ_D a b 0; let b0 := dHQ_D ξS ξQ 1
    let b1 := dHQ_D (a + ξS) (b + ξQ) 0 - b2 - dHQ_D ξS ξQ 0 + ⟨0, (10 / 7 : K5) * b * w0⟩
    let d20 := a2 * b0 - a0 * b2; let d21 := a2 * b1 - a1 * b2; let d10 := a1 * b0 - a0 * b1
    let (m2, m1, m0) : K5 × K5 × K5 := match mi with
      | 0 => (a ^ 2, 2 * a * ξS, ξS ^ 2)
      | 1 => (a * b, a * ξQ + b * ξS, ξS * ξQ)
      | 2 => (b ^ 2, 2 * b * ξQ, ξQ ^ 2)
      | 3 => (a, ξS, 0)
      | 4 => (0, a, ξS)
      | 5 => (b, ξQ, 0)
      | 6 => (0, b, ξQ)
      | 7 => (1, 0, 0)
      | 8 => (0, 1, 0)
      | 9 => (0, 0, 1)
    Dual.C (1 / 16 : K5) * (Dual.C m2 * d10 - Dual.C m1 * d20 + Dual.C m0 * d21)
  let A0U_D : K5 → K5 → Dual K5 := fun a b =>
    let m := fun i => numM_D i a b
    Dual.C (-(19708 / 1257375 : K5)) * (5 * m 0 - 9 * m 1) +
    Dual.C (1472 / 1257375 : K5) * (5 * m 1 - 9 * m 2) -
    Dual.C (16 / 729 : K5) * (5 * m 3 - 9 * m 5) +
    Dual.C (188 / 2025 : K5) * (5 * m 4 - 9 * m 6)
  intro ξS_s ξQ_s
  have ha_D : ValDual 0 a_s ⟨a0, a_s.coeff 1⟩ := ⟨ha_L.val, ha_L.c0, rfl⟩
  have hb_D : ValDual 0 b_s ⟨b0, b_s.coeff 1⟩ := ⟨hb_L.val, hb_L.c0, rfl⟩
  have hV_D : ValDual (-1) V ⟨w0, V.coeff 0⟩ := ⟨hV_L.val, hV_L.c0, rfl⟩
  have hξS_D : ValDual 0 ξS_s ⟨S_K - a0 * T_K, -a_s.coeff 1 * T_K⟩ :=
    ((ValDual.of_C S_K).sub ((ha_D.mul (ValDual.of_C T_K)).eq_k (by omega))).eq_d
      (by ext <;> simp [Dual.C])
  have hξQ_D : ValDual 0 ξQ_s ⟨Q_K - b0 * T_K, -b_s.coeff 1 * T_K⟩ :=
    ((ValDual.of_C Q_K).sub ((hb_D.mul (ValDual.of_C T_K)).eq_k (by omega))).eq_d
      (by ext <;> simp [Dual.C])
  -- Generic `ValDual (-1)` for `dH_dS` and `dH_dQ` at `U = t, V = w0*t^{-1} + v1`!
  let dHS_gen : Dual K5 → Dual K5 → Dual K5 := fun sD qD =>
    Dual.C (-(25 / 243 : K5)) * (5 * sD - 9 * qD) * (15 * sD - 9 * qD) * ⟨w0, V.coeff 0⟩ +
    ⟨0, ((143 / 81 : K5) * sD.val ^ 2 - (184 / 27) * sD.val * qD.val + (52 / 9) * qD.val ^ 2) * w0⟩
  let dHQ_gen : Dual K5 → Dual K5 → K5 → Dual K5 := fun sD qD v0 =>
    Dual.C (50 / 27 : K5) * sD * (5 * sD - 9 * qD) * ⟨w0, V.coeff 0⟩ +
    ⟨0, (-(92 / 27 : K5) * sD.val ^ 2 + (104 / 9) * sD.val * qD.val - (22 / 3) * qD.val ^ 2 +
      (10 / 7) * qD.val * v0 + (10 / 7) * v0 ^ 2) * w0⟩
  have hdHS_VD {s q : LaurentSeries K5} {sD qD : Dual K5} (hs : ValDual 0 s sD) (hq : ValDual 0 q qD) :
      ValDual (-1) (dH_dS s q U V) (dHS_gen sD qD) := by
    unfold dH_dS
    have h1 : HasValGe 1 (-(4 / 81 : LaurentSeries K5) * (s - 3 * q) ^ 2 * U ^ 2 * V) := by
      rw [show -(4 / 81 : LaurentSeries K5) = HahnSeries.C (-(4 / 81 : K5)) by simp only [map_div₀, map_neg, map_ofNat]]
      have hsq : HasValGe 0 ((s - 3 * q) ^ 2) :=
        ((hs.val.sub ((HasValGe.of_nat 3).mul hq.val |>.mono (by omega))).pow 2).mono (by omega)
      exact ((((HasValGe.of_C _).mul hsq).mul (hU_L.val.pow 2)).mul hV_L.val).mono (by omega)
    have h2 : ValLead 0 (((143 / 81 : LaurentSeries K5) * s ^ 2 - (184 / 27) * s * q +
        (52 / 9) * q ^ 2) * U * V)
        (((143 / 81 : K5) * sD.val ^ 2 - (184 / 27) * sD.val * qD.val + (52 / 9) * qD.val ^ 2) * w0) := by
      have ha : ValLead 0 ((143 / 81 : LaurentSeries K5) * s ^ 2) ((143 / 81 : K5) * sD.val ^ 2) := by
        rw [show (143 / 81 : LaurentSeries K5) = HahnSeries.C (143 / 81 : K5) by simp only [map_div₀, map_ofNat]]
        exact ((ValLead.of_C _).mul (hs.toValLead.pow 2)).eq_k (by omega)
      have hb : ValLead 0 ((184 / 27 : LaurentSeries K5) * s * q) ((184 / 27 : K5) * sD.val * qD.val) := by
        rw [show (184 / 27 : LaurentSeries K5) = HahnSeries.C (184 / 27 : K5) by simp only [map_div₀, map_ofNat]]
        exact (((ValLead.of_C _).mul hs.toValLead).mul hq.toValLead).eq_k (by omega)
      have hc : ValLead 0 ((52 / 9 : LaurentSeries K5) * q ^ 2) ((52 / 9 : K5) * qD.val ^ 2) := by
        rw [show (52 / 9 : LaurentSeries K5) = HahnSeries.C (52 / 9 : K5) by simp only [map_div₀, map_ofNat]]
        exact ((ValLead.of_C _).mul (hq.toValLead.pow 2)).eq_k (by omega)
      exact ((((ha.sub hb).add hc).mul hU_L).mul hV_L).eq_k (by omega) |>.eq_c (by ring)
    have h3 : ValDual (-1) (-(25 / 243 : LaurentSeries K5) * (5 * s - 9 * q) * (15 * s - 9 * q) * V)
        (Dual.C (-(25 / 243 : K5)) * (5 * sD - 9 * qD) * (15 * sD - 9 * qD) * ⟨w0, V.coeff 0⟩) := by
      have hc : ValDual 0 (-(25 / 243 : LaurentSeries K5)) (Dual.C (-(25 / 243 : K5))) := by
        rw [show -(25 / 243 : LaurentSeries K5) = HahnSeries.C (-(25 / 243 : K5)) by simp only [map_div₀, map_neg, map_ofNat]]; exact ValDual.of_C _
      have hl1 : ValDual 0 (5 * s - 9 * q) (5 * sD - 9 * qD) :=
        (((ValDual.of_nat 5).mul hs).eq_k (by omega)).sub (((ValDual.of_nat 9).mul hq).eq_k (by omega))
      have hl2 : ValDual 0 (15 * s - 9 * q) (15 * sD - 9 * qD) :=
        (((ValDual.of_nat 15).mul hs).eq_k (by omega)).sub (((ValDual.of_nat 9).mul hq).eq_k (by omega))
      exact (((hc.mul hl1).mul hl2).mul hV_D).eq_k (by omega)
    have hre : -(4 / 81 : LaurentSeries K5) * (s - 3 * q) ^ 2 * U ^ 2 * V +
        ((143 / 81) * s ^ 2 - (184 / 27) * s * q + (52 / 9) * q ^ 2) * U * V -
        (25 / 243) * (5 * s - 9 * q) * (15 * s - 9 * q) * V =
        (-(25 / 243) * (5 * s - 9 * q) * (15 * s - 9 * q) * V +
         ((143 / 81) * s ^ 2 - (184 / 27) * s * q + (52 / 9) * q ^ 2) * U * V) +
        (-(4 / 81) * (s - 3 * q) ^ 2 * U ^ 2 * V) := by ring
    rw [hre]
    exact (h3.add_shift1 h2).add_high h1
  have hdHQ_VD {s q : LaurentSeries K5} {sD qD : Dual K5} {v0 : K5} (hs : ValDual 0 s sD) (hq : ValDual 0 q qD) :
      ValDual (-1) (dH_dQ s q (HahnSeries.C v0) U V) (dHQ_gen sD qD v0) := by
    unfold dH_dQ
    have h1 : HasValGe 1 ((4 / 27 : LaurentSeries K5) * (s - 3 * q) ^ 2 * U ^ 2 * V) := by
      rw [show (4 / 27 : LaurentSeries K5) = HahnSeries.C (4 / 27 : K5) by simp only [map_div₀, map_ofNat]]
      have hsq : HasValGe 0 ((s - 3 * q) ^ 2) :=
        ((hs.val.sub ((HasValGe.of_nat 3).mul hq.val |>.mono (by omega))).pow 2).mono (by omega)
      exact ((((HasValGe.of_C _).mul hsq).mul (hU_L.val.pow 2)).mul hV_L.val).mono (by omega)
    have h2 : ValLead 0 ((-(92 / 27 : LaurentSeries K5) * s ^ 2 + (104 / 9) * s * q -
        (22 / 3) * q ^ 2 + (10 / 7) * q * HahnSeries.C v0 + (10 / 7) * HahnSeries.C v0 ^ 2) * U * V)
        ((-(92 / 27 : K5) * sD.val ^ 2 + (104 / 9) * sD.val * qD.val - (22 / 3) * qD.val ^ 2 +
          (10 / 7) * qD.val * v0 + (10 / 7) * v0 ^ 2) * w0) := by
      have ha : ValLead 0 (-(92 / 27 : LaurentSeries K5) * s ^ 2) (-(92 / 27 : K5) * sD.val ^ 2) := by
        rw [show -(92 / 27 : LaurentSeries K5) = HahnSeries.C (-(92 / 27 : K5)) by simp only [map_div₀, map_neg, map_ofNat]]
        exact ((ValLead.of_C _).mul (hs.toValLead.pow 2)).eq_k (by omega)
      have hb : ValLead 0 ((104 / 9 : LaurentSeries K5) * s * q) ((104 / 9 : K5) * sD.val * qD.val) := by
        rw [show (104 / 9 : LaurentSeries K5) = HahnSeries.C (104 / 9 : K5) by simp only [map_div₀, map_ofNat]]
        exact (((ValLead.of_C _).mul hs.toValLead).mul hq.toValLead).eq_k (by omega)
      have hc : ValLead 0 ((22 / 3 : LaurentSeries K5) * q ^ 2) ((22 / 3 : K5) * qD.val ^ 2) := by
        rw [show (22 / 3 : LaurentSeries K5) = HahnSeries.C (22 / 3 : K5) by simp only [map_div₀, map_ofNat]]
        exact ((ValLead.of_C _).mul (hq.toValLead.pow 2)).eq_k (by omega)
      have hd : ValLead 0 ((10 / 7 : LaurentSeries K5) * q * HahnSeries.C v0) ((10 / 7 : K5) * qD.val * v0) := by
        rw [show (10 / 7 : LaurentSeries K5) = HahnSeries.C (10 / 7 : K5) by simp only [map_div₀, map_ofNat]]
        exact (((ValLead.of_C _).mul hq.toValLead).mul (ValLead.of_C v0)).eq_k (by omega)
      have he : ValLead 0 ((10 / 7 : LaurentSeries K5) * HahnSeries.C v0 ^ 2) ((10 / 7 : K5) * v0 ^ 2) := by
        rw [show (10 / 7 : LaurentSeries K5) = HahnSeries.C (10 / 7 : K5) by simp only [map_div₀, map_ofNat]]
        exact ((ValLead.of_C _).mul ((ValLead.of_C v0).pow 2)).eq_k (by omega)
      exact ((((((ha.add hb).sub hc).add hd).add he).mul hU_L).mul hV_L).eq_k (by omega) |>.eq_c (by ring)
    have h3 : ValDual (-1) ((50 / 27 : LaurentSeries K5) * s * (5 * s - 9 * q) * V)
        (Dual.C (50 / 27 : K5) * sD * (5 * sD - 9 * qD) * ⟨w0, V.coeff 0⟩) := by
      have hc : ValDual 0 (50 / 27 : LaurentSeries K5) (Dual.C (50 / 27 : K5)) := by
        rw [show (50 / 27 : LaurentSeries K5) = HahnSeries.C (50 / 27 : K5) by simp only [map_div₀, map_ofNat]]; exact ValDual.of_C _
      have hl1 : ValDual 0 (5 * s - 9 * q) (5 * sD - 9 * qD) :=
        (((ValDual.of_nat 5).mul hs).eq_k (by omega)).sub (((ValDual.of_nat 9).mul hq).eq_k (by omega))
      exact (((hc.mul hs).mul hl1).mul hV_D).eq_k (by omega)
    have hre : (4 / 27 : LaurentSeries K5) * (s - 3 * q) ^ 2 * U ^ 2 * V +
        (-(92 / 27) * s ^ 2 + (104 / 9) * s * q - (22 / 3) * q ^ 2 +
          (10 / 7) * q * HahnSeries.C v0 + (10 / 7) * HahnSeries.C v0 ^ 2) * U * V +
        (50 / 27) * s * (5 * s - 9 * q) * V =
        ((50 / 27) * s * (5 * s - 9 * q) * V +
         (-(92 / 27) * s ^ 2 + (104 / 9) * s * q - (22 / 3) * q ^ 2 +
          (10 / 7) * q * HahnSeries.C v0 + (10 / 7) * HahnSeries.C v0 ^ 2) * U * V) +
        ((4 / 27) * (s - 3 * q) ^ 2 * U ^ 2 * V) := by ring
    rw [hre]
    exact (h3.add_shift1 h2).add_high h1
  -- Every `numM i` has `ValDual (-2)` (and hence `HasValGe (-2)`)!
  let aD : Dual K5 := ⟨a0, a_s.coeff 1⟩
  let bD : Dual K5 := ⟨b0, b_s.coeff 1⟩
  let ξSD : Dual K5 := ⟨S_K - a0 * T_K, -a_s.coeff 1 * T_K⟩
  let ξQD : Dual K5 := ⟨Q_K - b0 * T_K, -b_s.coeff 1 * T_K⟩
  let a2_g : Dual K5 := dHS_gen aD bD
  let a0_g : Dual K5 := dHS_gen ξSD ξQD
  let a1_g : Dual K5 := dHS_gen (aD + ξSD) (bD + ξQD) - a2_g - a0_g
  let b2_g : Dual K5 := dHQ_gen aD bD 0
  let b0_g : Dual K5 := dHQ_gen ξSD ξQD 1
  let b1_g : Dual K5 := dHQ_gen (aD + ξSD) (bD + ξQD) 0 - b2_g - dHQ_gen ξSD ξQD 0 + ⟨0, (10 / 7 : K5) * b0 * w0⟩
  let d20_g : Dual K5 := a2_g * b0_g - a0_g * b2_g
  let d21_g : Dual K5 := a2_g * b1_g - a1_g * b2_g
  let d10_g : Dual K5 := a1_g * b0_g - a0_g * b1_g
  let numM_gen : Fin 10 → Dual K5 := fun mi =>
    let (m2, m1, m0) : Dual K5 × Dual K5 × Dual K5 := match mi with
      | 0 => (aD ^ 2, 2 * aD * ξSD, ξSD ^ 2)
      | 1 => (aD * bD, aD * ξQD + bD * ξSD, ξSD * ξQD)
      | 2 => (bD ^ 2, 2 * bD * ξQD, ξQD ^ 2)
      | 3 => (aD, ξSD, 0)
      | 4 => (0, aD, ξSD)
      | 5 => (bD, ξQD, 0)
      | 6 => (0, bD, ξQD)
      | 7 => (1, 0, 0)
      | 8 => (0, 1, 0)
      | 9 => (0, 0, 1)
    Dual.C (1 / 16 : K5) * (m2 * d10_g - m1 * d20_g + m0 * d21_g)
  have hnumM_VD (mi : Fin 10) : ValDual (-2) (numM mi a_s b_s ξS_s ξQ_s U V) (numM_gen mi) := by
    have ha2 : ValDual (-1) (q1_a2 a_s b_s U V) a2_g := hdHS_VD ha_D hb_D
    have ha0 : ValDual (-1) (q1_a0 ξS_s ξQ_s U V) a0_g := hdHS_VD hξS_D hξQ_D
    have ha1 : ValDual (-1) (q1_a1 a_s b_s ξS_s ξQ_s U V) a1_g :=
      ((hdHS_VD (ha_D.add hξS_D) (hb_D.add hξQ_D)).sub ha2).sub ha0
    have hb2 : ValDual (-1) (q2_b2 a_s b_s U V) b2_g := by
      unfold q2_b2; simpa only [map_zero] using hdHQ_VD (v0 := 0) ha_D hb_D
    have hb0 : ValDual (-1) (q2_b0 ξS_s ξQ_s U V) b0_g := by
      unfold q2_b0; simpa only [map_one] using hdHQ_VD (v0 := 1) hξS_D hξQ_D
    have hb1 : ValDual (-1) (q2_b1 a_s b_s ξS_s ξQ_s U V) b1_g := by
      unfold q2_b1
      have hbase := ((hdHQ_VD (v0 := 0) (ha_D.add hξS_D) (hb_D.add hξQ_D)).sub
        (hdHQ_VD (v0 := 0) ha_D hb_D)).sub (hdHQ_VD (v0 := 0) hξS_D hξQ_D)
      have hbase' : ValDual (-1) (dH_dQ (a_s + ξS_s) (b_s + ξQ_s) 0 U V - dH_dQ a_s b_s 0 U V -
          dH_dQ ξS_s ξQ_s 0 U V) (dHQ_gen (aD + ξSD) (bD + ξQD) 0 - b2_g - dHQ_gen ξSD ξQD 0) := by
        simpa only [map_zero] using hbase
      have hextra : ValLead 0 ((10 / 7 : LaurentSeries K5) * b_s * U * V) ((10 / 7 : K5) * b0 * w0) := by
        rw [show (10 / 7 : LaurentSeries K5) = HahnSeries.C (10 / 7 : K5) by simp only [map_div₀, map_ofNat]]
        exact ((((ValLead.of_C _).mul hb_D.toValLead).mul hU_L).mul hV_L).eq_k (by omega) |>.eq_c (by ring)
      exact hbase'.add_shift1 hextra
    exact (numM_ValDual_of ha_D hb_D hξS_D hξQ_D ha2 ha1 ha0 hb2 hb1 hb0 mi).eq_k (k' := -2) (by omega)
  -- Every pair `5 * numM_gen i - 9 * numM_gen j` for `(0,1), (1,2), (3,5), (4,6)` equals
  -- `⟨0, (5 * numM_D i a0 b0 - 9 * numM_D j a0 b0).eps⟩` (independent of `a1, b1, V.coeff 0`)!
  set ξS0 : K5 := S_K - a0 * T_K
  set ξQ0 : K5 := Q_K - b0 * T_K
  set a1_D : Dual K5 := dHS_D (a0 + ξS0) (b0 + ξQ0) - dHS_D a0 b0 - dHS_D ξS0 ξQ0
  set b1_D : Dual K5 := dHQ_D (a0 + ξS0) (b0 + ξQ0) 0 - dHQ_D a0 b0 0 - dHQ_D ξS0 ξQ0 0 + ⟨0, (10 / 7 : K5) * b0 * w0⟩
  set d20_D : Dual K5 := dHS_D a0 b0 * dHQ_D ξS0 ξQ0 1 - dHS_D ξS0 ξQ0 * dHQ_D a0 b0 0
  set d21_D : Dual K5 := dHS_D a0 b0 * b1_D - a1_D * dHQ_D a0 b0 0
  set d10_D : Dual K5 := a1_D * dHQ_D ξS0 ξQ0 1 - dHS_D ξS0 ξQ0 * b1_D
  have hnumM_D_eq (mi : Fin 10) : numM_D mi a0 b0 =
      let (m2, m1, m0) : K5 × K5 × K5 := match mi with
        | 0 => (a0 ^ 2, 2 * a0 * ξS0, ξS0 ^ 2)
        | 1 => (a0 * b0, a0 * ξQ0 + b0 * ξS0, ξS0 * ξQ0)
        | 2 => (b0 ^ 2, 2 * b0 * ξQ0, ξQ0 ^ 2)
        | 3 => (a0, ξS0, 0)
        | 4 => (0, a0, ξS0)
        | 5 => (b0, ξQ0, 0)
        | 6 => (0, b0, ξQ0)
        | 7 => (1, 0, 0)
        | 8 => (0, 1, 0)
        | 9 => (0, 0, 1)
      Dual.C (1 / 16 : K5) * (Dual.C m2 * d10_D - Dual.C m1 * d20_D + Dual.C m0 * d21_D) := rfl
  have hpair_eq (u1 u0 : Dual K5) :
      Dual.C (1 / 16 : K5) *
        ((u1 * (5 * aD - 9 * bD)) * d10_g - (u1 * (5 * ξSD - 9 * ξQD) + u0 * (5 * aD - 9 * bD)) * d20_g +
         (u0 * (5 * ξSD - 9 * ξQD)) * d21_g) =
      ⟨0, (Dual.C (1 / 16 : K5) *
        (Dual.C (u1.val * (5 * a0 - 9 * b0)) * d10_D -
         Dual.C (u1.val * (5 * ξS0 - 9 * ξQ0) + u0.val * (5 * a0 - 9 * b0)) * d20_D +
         Dual.C (u0.val * (5 * ξS0 - 9 * ξQ0)) * d21_D)).eps⟩ := by
    set wD : Dual K5 := ⟨w0, V.coeff 0⟩
    set dHS0 : Dual K5 → Dual K5 → Dual K5 := fun s q => Dual.C (-(25 / 243 : K5)) * (5 * s - 9 * q) * (15 * s - 9 * q) * wD
    set dHQ0 : Dual K5 → Dual K5 → Dual K5 := fun s q => Dual.C (50 / 27 : K5) * s * (5 * s - 9 * q) * wD
    set dHS0_C : Dual K5 → Dual K5 → Dual K5 := fun s q => Dual.C (-(25 / 243 : K5)) * (5 * s - 9 * q) * (15 * s - 9 * q) * Dual.C w0
    set dHQ0_C : Dual K5 → Dual K5 → Dual K5 := fun s q => Dual.C (50 / 27 : K5) * s * (5 * s - 9 * q) * Dual.C w0
    set da2 := (dHS_D a0 b0).eps
    set da0 := (dHS_D ξS0 ξQ0).eps
    set da1 := (dHS_D (a0 + ξS0) (b0 + ξQ0) - dHS_D a0 b0 - dHS_D ξS0 ξQ0).eps
    set db2 := (dHQ_D a0 b0 0).eps
    set db0 := (dHQ_D ξS0 ξQ0 1).eps
    set db1 := (dHQ_D (a0 + ξS0) (b0 + ξQ0) 0 - dHQ_D a0 b0 0 - dHQ_D ξS0 ξQ0 0 + ⟨0, (10 / 7 : K5) * b0 * w0⟩).eps
    have ha2_g : a2_g = dHS0 aD bD + ⟨0, da2⟩ := rfl
    have ha0_g : a0_g = dHS0 ξSD ξQD + ⟨0, da0⟩ := rfl
    have ha1_g : a1_g = (dHS0 (aD + ξSD) (bD + ξQD) - dHS0 aD bD - dHS0 ξSD ξQD) + ⟨0, da1⟩ := by
      ext <;> simp only [a1_g, a2_g, a0_g, dHS_gen, dHS0, dHS_D, da1, aD, bD, ξSD, ξQD, wD, ξS0, ξQ0,
        Dual.add_val, Dual.sub_val, Dual.add_eps, Dual.sub_eps] <;> ring
    have hb2_g : b2_g = dHQ0 aD bD + ⟨0, db2⟩ := rfl
    have hb0_g : b0_g = dHQ0 ξSD ξQD + ⟨0, db0⟩ := rfl
    have hb1_g : b1_g = (dHQ0 (aD + ξSD) (bD + ξQD) - dHQ0 aD bD - dHQ0 ξSD ξQD) + ⟨0, db1⟩ := by
      ext <;> simp only [b1_g, b2_g, dHQ_gen, dHQ0, dHQ_D, db1, aD, bD, ξSD, ξQD, wD, ξS0, ξQ0,
        Dual.add_val, Dual.sub_val, Dual.add_eps, Dual.sub_eps] <;> ring
    have hdS0_C (s q : K5) :
        dHS0_C (Dual.C s) (Dual.C q) = Dual.C (-(25 / 243 : K5) * (5 * s - 9 * q) * (15 * s - 9 * q) * w0) := by
      simp only [dHS0_C, map_mul, map_sub, map_ofNat]
    have hdQ0_C (s q : K5) :
        dHQ0_C (Dual.C s) (Dual.C q) = Dual.C ((50 / 27 : K5) * s * (5 * s - 9 * q) * w0) := by
      simp only [dHQ0_C, map_mul, map_sub, map_ofNat]
    have ha2_D : dHS_D a0 b0 = dHS0_C (Dual.C a0) (Dual.C b0) + ⟨0, da2⟩ := by
      rw [hdS0_C]; ext <;> simp only [dHS_D, da2, Dual.add_val, Dual.C_val, Dual.add_eps, Dual.C_eps] <;> ring
    have ha0_D : dHS_D ξS0 ξQ0 = dHS0_C (Dual.C ξS0) (Dual.C ξQ0) + ⟨0, da0⟩ := by
      rw [hdS0_C]; ext <;> simp only [dHS_D, da0, Dual.add_val, Dual.C_val, Dual.add_eps, Dual.C_eps] <;> ring
    have ha1_D : a1_D =
        (dHS0_C (Dual.C a0 + Dual.C ξS0) (Dual.C b0 + Dual.C ξQ0) -
          dHS0_C (Dual.C a0) (Dual.C b0) - dHS0_C (Dual.C ξS0) (Dual.C ξQ0)) + ⟨0, da1⟩ := by
      dsimp only [a1_D]
      rw [← map_add Dual.C, ← map_add Dual.C, hdS0_C, hdS0_C, hdS0_C]
      ext <;> simp only [dHS_D, da1, Dual.add_val, Dual.sub_val, Dual.C_val, Dual.add_eps, Dual.sub_eps, Dual.C_eps] <;> ring
    have hb2_D : dHQ_D a0 b0 0 = dHQ0_C (Dual.C a0) (Dual.C b0) + ⟨0, db2⟩ := by
      rw [hdQ0_C]; ext <;> simp only [dHQ_D, db2, Dual.add_val, Dual.C_val, Dual.add_eps, Dual.C_eps] <;> ring
    have hb0_D : dHQ_D ξS0 ξQ0 1 = dHQ0_C (Dual.C ξS0) (Dual.C ξQ0) + ⟨0, db0⟩ := by
      rw [hdQ0_C]; ext <;> simp only [dHQ_D, db0, Dual.add_val, Dual.C_val, Dual.add_eps, Dual.C_eps] <;> ring
    have hb1_D : b1_D =
        (dHQ0_C (Dual.C a0 + Dual.C ξS0) (Dual.C b0 + Dual.C ξQ0) -
          dHQ0_C (Dual.C a0) (Dual.C b0) - dHQ0_C (Dual.C ξS0) (Dual.C ξQ0)) + ⟨0, db1⟩ := by
      dsimp only [b1_D]
      rw [← map_add Dual.C, ← map_add Dual.C, hdQ0_C, hdQ0_C, hdQ0_C]
      ext <;> simp only [dHQ_D, db1, Dual.add_val, Dual.sub_val, Dual.C_val, Dual.add_eps, Dual.sub_eps, Dual.C_eps]; ring
    have hcore := dual_minor_pair_eq_const aD bD ξSD ξQD wD u1 u0 da2 da1 da0 db2 db1 db0
    dsimp only at hcore
    have hL : (u1 * (5 * aD - 9 * bD)) * d10_g - (u1 * (5 * ξSD - 9 * ξQD) + u0 * (5 * aD - 9 * bD)) * d20_g +
        (u0 * (5 * ξSD - 9 * ξQD)) * d21_g =
        ⟨0, (Dual.C (u1.val * (5 * a0 - 9 * b0)) * d10_D -
         Dual.C (u1.val * (5 * ξS0 - 9 * ξQ0) + u0.val * (5 * a0 - 9 * b0)) * d20_D +
         Dual.C (u0.val * (5 * ξS0 - 9 * ξQ0)) * d21_D).eps⟩ := by
      rw [show d10_g = a1_g * b0_g - a0_g * b1_g from rfl,
          show d20_g = a2_g * b0_g - a0_g * b2_g from rfl,
          show d21_g = a2_g * b1_g - a1_g * b2_g from rfl,
          show d10_D = a1_D * dHQ_D ξS0 ξQ0 1 - dHS_D ξS0 ξQ0 * b1_D from rfl,
          show d20_D = dHS_D a0 b0 * dHQ_D ξS0 ξQ0 1 - dHS_D ξS0 ξQ0 * dHQ_D a0 b0 0 from rfl,
          show d21_D = dHS_D a0 b0 * b1_D - a1_D * dHQ_D a0 b0 0 from rfl,
          ha2_g, ha1_g, ha0_g, hb2_g, hb1_g, hb0_g,
          ha1_D, ha2_D, ha0_D, hb1_D, hb2_D, hb0_D]
      have hm2C : Dual.C (u1.val * (5 * a0 - 9 * b0)) = Dual.C u1.val * (5 * Dual.C a0 - 9 * Dual.C b0) := by
        simp only [map_mul, map_sub, map_ofNat]
      have hm1C : Dual.C (u1.val * (5 * ξS0 - 9 * ξQ0) + u0.val * (5 * a0 - 9 * b0)) =
          Dual.C u1.val * (5 * Dual.C ξS0 - 9 * Dual.C ξQ0) + Dual.C u0.val * (5 * Dual.C a0 - 9 * Dual.C b0) := by
        simp only [map_add, map_mul, map_sub, map_ofNat]
      have hm0C : Dual.C (u0.val * (5 * ξS0 - 9 * ξQ0)) = Dual.C u0.val * (5 * Dual.C ξS0 - 9 * Dual.C ξQ0) := by
        simp only [map_mul, map_sub, map_ofNat]
      rw [hm2C, hm1C, hm0C]
      exact hcore
    rw [hL]
    ext <;> simp only [Dual.mul_val, Dual.mul_eps, Dual.C_val, Dual.C_eps] <;> ring
  clear_value dHS_gen dHQ_gen a2_g a0_g a1_g b2_g b0_g b1_g d20_g d21_g d10_g a1_D b1_D d20_D d21_D d10_D
  have hp01_eq : 5 * numM_gen 0 - 9 * numM_gen 1 = ⟨0, (5 * numM_D 0 a0 b0 - 9 * numM_D 1 a0 b0).eps⟩ := by
    have h := hpair_eq aD ξSD
    have hL : 5 * numM_gen 0 - 9 * numM_gen 1 = Dual.C (1 / 16 : K5) *
        ((aD * (5 * aD - 9 * bD)) * d10_g - (aD * (5 * ξSD - 9 * ξQD) + ξSD * (5 * aD - 9 * bD)) * d20_g +
         (ξSD * (5 * ξSD - 9 * ξQD)) * d21_g) := by
      simp only [numM_gen]; ring
    have hR : 5 * numM_D 0 a0 b0 - 9 * numM_D 1 a0 b0 = Dual.C (1 / 16 : K5) *
        (Dual.C (aD.val * (5 * a0 - 9 * b0)) * d10_D -
         Dual.C (aD.val * (5 * ξS0 - 9 * ξQ0) + ξSD.val * (5 * a0 - 9 * b0)) * d20_D +
         Dual.C (ξSD.val * (5 * ξS0 - 9 * ξQ0)) * d21_D) := by
      rw [hnumM_D_eq 0, hnumM_D_eq 1]; dsimp only [aD, ξSD, ξS0, ξQ0]
      simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]; ring
    rw [hL, hR]; exact h
  have hp12_eq : 5 * numM_gen 1 - 9 * numM_gen 2 = ⟨0, (5 * numM_D 1 a0 b0 - 9 * numM_D 2 a0 b0).eps⟩ := by
    have h := hpair_eq bD ξQD
    have hL : 5 * numM_gen 1 - 9 * numM_gen 2 = Dual.C (1 / 16 : K5) *
        ((bD * (5 * aD - 9 * bD)) * d10_g - (bD * (5 * ξSD - 9 * ξQD) + ξQD * (5 * aD - 9 * bD)) * d20_g +
         (ξQD * (5 * ξSD - 9 * ξQD)) * d21_g) := by
      simp only [numM_gen]; ring
    have hR : 5 * numM_D 1 a0 b0 - 9 * numM_D 2 a0 b0 = Dual.C (1 / 16 : K5) *
        (Dual.C (bD.val * (5 * a0 - 9 * b0)) * d10_D -
         Dual.C (bD.val * (5 * ξS0 - 9 * ξQ0) + ξQD.val * (5 * a0 - 9 * b0)) * d20_D +
         Dual.C (ξQD.val * (5 * ξS0 - 9 * ξQ0)) * d21_D) := by
      rw [hnumM_D_eq 1, hnumM_D_eq 2]; dsimp only [bD, ξQD, ξS0, ξQ0]
      simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]; ring
    rw [hL, hR]; exact h
  have hp35_eq : 5 * numM_gen 3 - 9 * numM_gen 5 = ⟨0, (5 * numM_D 3 a0 b0 - 9 * numM_D 5 a0 b0).eps⟩ := by
    have h := hpair_eq 1 0
    have hL : 5 * numM_gen 3 - 9 * numM_gen 5 = Dual.C (1 / 16 : K5) *
        ((1 * (5 * aD - 9 * bD)) * d10_g - (1 * (5 * ξSD - 9 * ξQD) + 0 * (5 * aD - 9 * bD)) * d20_g +
         (0 * (5 * ξSD - 9 * ξQD)) * d21_g) := by
      simp only [numM_gen]; ring
    have hR : 5 * numM_D 3 a0 b0 - 9 * numM_D 5 a0 b0 = Dual.C (1 / 16 : K5) *
        (Dual.C ((1 : Dual K5).val * (5 * a0 - 9 * b0)) * d10_D -
         Dual.C ((1 : Dual K5).val * (5 * ξS0 - 9 * ξQ0) + (0 : Dual K5).val * (5 * a0 - 9 * b0)) * d20_D +
         Dual.C ((0 : Dual K5).val * (5 * ξS0 - 9 * ξQ0)) * d21_D) := by
      rw [hnumM_D_eq 3, hnumM_D_eq 5]
      simp only [Dual.one_val, Dual.zero_val, map_add, map_sub, map_mul, map_zero, map_one, map_ofNat]; ring
    rw [hL, hR]; exact h
  have hp46_eq : 5 * numM_gen 4 - 9 * numM_gen 6 = ⟨0, (5 * numM_D 4 a0 b0 - 9 * numM_D 6 a0 b0).eps⟩ := by
    have h := hpair_eq 0 1
    have hL : 5 * numM_gen 4 - 9 * numM_gen 6 = Dual.C (1 / 16 : K5) *
        ((0 * (5 * aD - 9 * bD)) * d10_g - (0 * (5 * ξSD - 9 * ξQD) + 1 * (5 * aD - 9 * bD)) * d20_g +
         (1 * (5 * ξSD - 9 * ξQD)) * d21_g) := by
      simp only [numM_gen]; ring
    have hR : 5 * numM_D 4 a0 b0 - 9 * numM_D 6 a0 b0 = Dual.C (1 / 16 : K5) *
        (Dual.C ((0 : Dual K5).val * (5 * a0 - 9 * b0)) * d10_D -
         Dual.C ((0 : Dual K5).val * (5 * ξS0 - 9 * ξQ0) + (1 : Dual K5).val * (5 * a0 - 9 * b0)) * d20_D +
         Dual.C ((1 : Dual K5).val * (5 * ξS0 - 9 * ξQ0)) * d21_D) := by
      rw [hnumM_D_eq 4, hnumM_D_eq 6]
      simp only [Dual.one_val, Dual.zero_val, map_add, map_sub, map_mul, map_zero, map_one, map_ofNat]; ring
    rw [hL, hR]; exact h
  have hA0U_L : ValLead (-1) (A_0U a_s b_s ξS_s ξQ_s U V) (A0U_D a0 b0).eps := by
    have hVD := A0U_ValDual_of hnumM_VD
    have heq_D : Dual.C (-(19708 / 1257375 : K5)) * (5 * numM_gen 0 - 9 * numM_gen 1) +
        Dual.C (1472 / 1257375 : K5) * (5 * numM_gen 1 - 9 * numM_gen 2) -
        Dual.C (16 / 729 : K5) * (5 * numM_gen 3 - 9 * numM_gen 5) +
        Dual.C (188 / 2025 : K5) * (5 * numM_gen 4 - 9 * numM_gen 6) = ⟨0, (A0U_D a0 b0).eps⟩ := by
      rw [hp01_eq, hp12_eq, hp35_eq, hp46_eq]
      ext <;> simp only [A0U_D, Dual.add_val, Dual.sub_val, Dual.mul_val, Dual.C_val,
        Dual.add_eps, Dual.sub_eps, Dual.mul_eps, Dual.C_eps] <;> ring
    rw [heq_D] at hVD
    exact ⟨hVD.val.inc hVD.c0, hVD.c1⟩
  -- `A_0V / V` has `HasValGe (-1)`, so `M0` has `ValLead (-2) M0 (A0U_D a0 b0).eps`!
  have hm_m2 (i : Fin 10) : HasValGe (-2) (numM i a_s b_s ξS_s ξQ_s U V) := (hnumM_VD i).val
  have hnat_m2 (n : ℕ) {f : LaurentSeries K5} (hf : HasValGe (-2) f) : HasValGe (-2) ((n : LaurentSeries K5) * f) :=
    ((HasValGe.of_nat n).mul hf).mono (by omega)
  have hp_m2 (i j : Fin 10) : HasValGe (-2) (5 * numM i a_s b_s ξS_s ξQ_s U V - 9 * numM j a_s b_s ξS_s ξQ_s U V) :=
    (hnat_m2 5 (hm_m2 i)).sub (hnat_m2 9 (hm_m2 j))
  have hA0V_m2 : HasValGe (-2) (A_0V a_s b_s ξS_s ξQ_s U V) := by
    unfold A_0V
    exact (((hasValGe_neg_div_nat_mul 892 3645 (hp_m2 3 4)).add
      (hasValGe_div_nat_mul 40 81 (hp_m2 5 6))).sub
      (hasValGe_div_nat_mul 112 2395 (hp_m2 7 8))).add
      (hasValGe_div_nat_mul 392 11975 (hp_m2 8 9))
  have hM0_L : ValLead (-2) (A_0U a_s b_s ξS_s ξQ_s U V / U + A_0V a_s b_s ξS_s ξQ_s U V / V)
      (A0U_D a0 b0).eps := by
    have h1 := (hA0U_L.div_of_ne hU_L one_ne_zero).eq_k (k' := -2) (by omega) |>.eq_c (div_one _)
    have h2 : HasValGe (-1) (A_0V a_s b_s ξS_s ξQ_s U V / V) :=
      (hA0V_m2.div_of_lead_ne hV_L.val (hV_L.c0.symm ▸ hw0_ne)).1.mono (by omega)
    exact h1.add_high h2
  -- `A_Y` has `HasValGe (-2)` (because the `V` part multiplies `A_0U`-type combinations which have `HasValGe (-1)`!),
  -- and `A_X` has `HasValGe (-1)`!
  have hAY_m2 : HasValGe (-2) (A_Y a_s b_s ξS_s ξQ_s U V) := by
    unfold A_Y
    have ht1 : HasValGe (-2) (-(100 / 243 : LaurentSeries K5) *
        (25 * numM 3 a_s b_s ξS_s ξQ_s U V - 45 * numM 4 a_s b_s ξS_s ξQ_s U V -
         45 * numM 5 a_s b_s ξS_s ξQ_s U V + 81 * numM 6 a_s b_s ξS_s ξQ_s U V)) :=
      hasValGe_neg_div_nat_mul 100 243 ((((hnat_m2 25 (hm_m2 3)).sub (hnat_m2 45 (hm_m2 4))).sub
        (hnat_m2 45 (hm_m2 5))).add (hnat_m2 81 (hm_m2 6)))
    have ht2_inner : HasValGe (-1) (-(907876 / 33949125 : LaurentSeries K5) *
          (5 * numM 0 a_s b_s ξS_s ξQ_s U V - 9 * numM 1 a_s b_s ξS_s ξQ_s U V) +
        (2258324 / 33949125) * (5 * numM 1 a_s b_s ξS_s ξQ_s U V - 9 * numM 2 a_s b_s ξS_s ξQ_s U V) +
        (8 / 243) * (5 * numM 3 a_s b_s ξS_s ξQ_s U V - 9 * numM 5 a_s b_s ξS_s ξQ_s U V) -
        (64 / 675) * (5 * numM 4 a_s b_s ξS_s ξQ_s U V - 9 * numM 6 a_s b_s ξS_s ξQ_s U V)) := by
      have hp1 (i j : Fin 10) (h0 : (5 * numM_gen i - 9 * numM_gen j).val = 0) :
          HasValGe (-1) (5 * numM i a_s b_s ξS_s ξQ_s U V - 9 * numM j a_s b_s ξS_s ξQ_s U V) := by
        have h := (((ValDual.of_nat 5).mul (hnumM_VD i)).eq_k (k' := -2) (by omega)).sub
          (((ValDual.of_nat 9).mul (hnumM_VD j)).eq_k (k' := -2) (by omega))
        exact h.val.inc (by rw [h.c0]; simpa only [Nat.cast_ofNat] using h0)
      have hz01 : (5 * numM_gen 0 - 9 * numM_gen 1).val = 0 := by rw [hp01_eq]
      have hz12 : (5 * numM_gen 1 - 9 * numM_gen 2).val = 0 := by rw [hp12_eq]
      have hz35 : (5 * numM_gen 3 - 9 * numM_gen 5).val = 0 := by rw [hp35_eq]
      have hz46 : (5 * numM_gen 4 - 9 * numM_gen 6).val = 0 := by rw [hp46_eq]
      exact (((hasValGe_neg_div_nat_mul 907876 33949125 (hp1 0 1 hz01)).add
        (hasValGe_div_nat_mul 2258324 33949125 (hp1 1 2 hz12))).add
        (hasValGe_div_nat_mul 8 243 (hp1 3 5 hz35))).sub
        (hasValGe_div_nat_mul 64 675 (hp1 4 6 hz46))
    have ht2 := (hV_L.val.mul ht2_inner).mono (k2 := -2) (by omega)
    have ht3_inner : HasValGe (-2) (-(123236 / 24249375 : LaurentSeries K5) *
          (numM 0 a_s b_s ξS_s ξQ_s U V + (2790 / 77) * numM 6 a_s b_s ξS_s ξQ_s U V +
           28 * numM 8 a_s b_s ξS_s ξQ_s U V - (5904 / 77) * numM 9 a_s b_s ξS_s ξQ_s U V) +
        (492944 / 33949125) * (numM 1 a_s b_s ξS_s ξQ_s U V +
          (927 / 77) * numM 6 a_s b_s ξS_s ξQ_s U V + (49 / 5) * numM 8 a_s b_s ξS_s ξQ_s U V -
          (21159 / 770) * numM 9 a_s b_s ξS_s ξQ_s U V)) :=
      (hasValGe_neg_div_nat_mul 123236 24249375
        ((((hm_m2 0).add (hasValGe_div_nat_mul 2790 77 (hm_m2 6))).add (hnat_m2 28 (hm_m2 8))).sub
          (hasValGe_div_nat_mul 5904 77 (hm_m2 9)))).add
      (hasValGe_div_nat_mul 492944 33949125
        ((((hm_m2 1).add (hasValGe_div_nat_mul 927 77 (hm_m2 6))).add (hasValGe_div_nat_mul 49 5 (hm_m2 8))).sub
          (hasValGe_div_nat_mul 21159 770 (hm_m2 9))))
    have ht3 := ((hU_L.val.mul hV_L.val).mul ht3_inner).mono (k2 := -2) (by omega)
    exact (ht1.add ht2).add ht3
  have hAX_m1 : HasValGe (-1) (A_X a_s b_s ξS_s ξQ_s U V) := by
    unfold A_X
    have hinner : HasValGe (-2) (-(8 / 405 : LaurentSeries K5) * (5 * numM 3 a_s b_s ξS_s ξQ_s U V - 9 * numM 4 a_s b_s ξS_s ξQ_s U V) -
        (476 / 7185) * (5 * numM 7 a_s b_s ξS_s ξQ_s U V - 9 * numM 8 a_s b_s ξS_s ξQ_s U V) +
        (6916 / 35925) * (5 * numM 8 a_s b_s ξS_s ξQ_s U V - 9 * numM 9 a_s b_s ξS_s ξQ_s U V)) :=
      ((hasValGe_neg_div_nat_mul 8 405 (hp_m2 3 4)).sub (hasValGe_div_nat_mul 476 7185 (hp_m2 7 8))).add
        (hasValGe_div_nat_mul 6916 35925 (hp_m2 8 9))
    exact (hU_L.val.mul hinner).mono (by omega)
  have hA0U_D_eq (a b : K5) : (A0U_D a b).eps = w0 ^ 2 * A0U_12_of (RingHom.id K5) a b := by
    have hmi (mi : Fin 10) : (numM_D mi a b).eps = w0 ^ 2 * numM_12_of (RingHom.id K5) mi a b := by
      have hdHS (s q : K5) : dHS_D s q = Dual.C w0 * dHS_12_of (RingHom.id K5) s q := by
        ext <;> simp only [dHS_D, dHS_12_of, Dual.C_val, Dual.C_eps, Dual.mul_val, Dual.mul_eps, RingHom.id_apply] <;> ring
      have hdHQ (s q v0 : K5) : dHQ_D s q v0 = Dual.C w0 * dHQ_12_of (RingHom.id K5) s q v0 := by
        ext <;> simp only [dHQ_D, dHQ_12_of, Dual.C_val, Dual.C_eps, Dual.mul_val, Dual.mul_eps, RingHom.id_apply] <;> ring
      have hscale : ∀ (m2 m1 m0 : K5) (A2 A1 A0 B2 B1 B0 : Dual K5),
          (Dual.C (1 / 16 : K5) *
            (Dual.C m2 * ((Dual.C w0 * A1) * (Dual.C w0 * B0) - (Dual.C w0 * A0) * (Dual.C w0 * B1)) -
             Dual.C m1 * ((Dual.C w0 * A2) * (Dual.C w0 * B0) - (Dual.C w0 * A0) * (Dual.C w0 * B2)) +
             Dual.C m0 * ((Dual.C w0 * A2) * (Dual.C w0 * B1) - (Dual.C w0 * A1) * (Dual.C w0 * B2)))).eps =
          w0 ^ 2 * (Dual.C (1 / 16 : K5) *
            (Dual.C m2 * (A1 * B0 - A0 * B1) -
             Dual.C m1 * (A2 * B0 - A0 * B2) +
             Dual.C m0 * (A2 * B1 - A1 * B2))).eps := by
        intro m2 m1 m0 A2 A1 A0 B2 B1 B0
        simp only [Dual.C_val, Dual.C_eps, Dual.add_val, Dual.add_eps, Dual.sub_val, Dual.sub_eps,
          Dual.mul_val, Dual.mul_eps]
        ring
      have hsub : ∀ x y z : Dual K5, Dual.C w0 * x - Dual.C w0 * y - Dual.C w0 * z = Dual.C w0 * (x - y - z) :=
        fun x y z => by ring
      have hsub1 : ∀ x y z : Dual K5, Dual.C w0 * x - Dual.C w0 * y - Dual.C w0 * z + ⟨0, (10 / 7 : K5) * b * w0⟩ =
          Dual.C w0 * (x - y - z + ⟨0, (10 / 7 : K5) * b⟩) := by
        intro x y z; ext <;> simp only [Dual.C_val, Dual.C_eps, Dual.add_val, Dual.add_eps, Dual.sub_val, Dual.sub_eps,
          Dual.mul_val, Dual.mul_eps] <;> ring
      dsimp only [numM_D, numM_12_of]
      rw [hdHS, hdHS, hdHS, hdHQ, hdHQ, hdHQ, hdHQ, hsub, hsub1]
      have hC_rhs : ∀ (m2 m1 m0 : K5) (d10 d20 d21 : Dual K5),
          (Dual.C (1 / 16 : K5) * (Dual.C m2 * d10 - Dual.C m1 * d20 + Dual.C m0 * d21)).eps =
          (1 / 16 : K5) * (m2 * d10.eps - m1 * d20.eps + m0 * d21.eps) := by
        intro m2 m1 m0 d10 d20 d21
        simp only [Dual.C_val, Dual.C_eps, Dual.add_eps, Dual.sub_eps, Dual.mul_eps]; ring
      fin_cases mi <;> (simp only [RingHom.id_apply]; rw [hscale, hC_rhs])
    simp only [A0U_D, A0U_12_of, Dual.C_val, Dual.C_eps, Dual.add_eps, Dual.sub_eps, Dual.mul_eps,
      Dual.ofNat_val, Dual.ofNat_eps, RingHom.id_apply, hmi]
    ring
  exact ⟨hM0_L.eq_c (hA0U_D_eq a0 b0), hAY_m2, hAX_m1⟩

private lemma br2_0_q1_lead
    {a_s b_s U V : LaurentSeries K5} {w0 ca0 cb0 c0W0 a0 b0 : K5}
    (hw0_eq : w0 = -(25 / 4 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 2 / (T_K - 3) ^ 3)
    (hw0_ne : w0 ≠ 0)
    (hca0 : ca0 = -(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K))
    (hcb0 : cb0 = (50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K))
    (hc0W0 : c0W0 = k5Params.c0_V2 * w0 ^ 2)
    (hlin_raw : ca0 * w0 * a0 + cb0 * w0 * b0 + c0W0 = 0)
    (ha_L : ValLead 0 a_s a0) (hb_L : ValLead 0 b_s b0)
    (hU_L : ValLead 1 U 1) (hV_L : ValLead (-1) V w0) :
    let q1_lead0 : K5 → K5 → K5 := fun a b =>
      let qY0 := 9 * ((QY_num S_K Q_K T_K x_K y_K 0 1 0 - QY_num S_K Q_K T_K x_K y_K 0 0 0) * a +
        (QY_num S_K Q_K T_K x_K y_K 0 1 1 - QY_num S_K Q_K T_K x_K y_K 0 0 1) * b +
        (QY_num S_K Q_K T_K x_K y_K 0 1 2 - QY_num S_K Q_K T_K x_K y_K 0 0 2))
      let cA0 := 9 * ((H0_of S_K Q_K T_K * dA1_fn 0 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 0 S_K Q_K T_K) * a +
        (H0_of S_K Q_K T_K * dA1_fn 1 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 1 S_K Q_K T_K) * b +
        (H0_of S_K Q_K T_K * dA1_fn 2 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 2 S_K Q_K T_K))
      w0 * (H0_of S_K Q_K T_K * A1_of S_K Q_K 0 1 * qY0 + cA0 * EB_of S_K Q_K T_K x_K y_K 0 1)
    HasValGe 0 (dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / v_of V) ∧
    HasValGe 0 (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / u_of U) ∧
    ValLead (-1)
      (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) *
        A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V *
        (dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
          (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / v_of V) +
       H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) *
        B1_of (HahnSeries.C T_K) U V *
        (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
          (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / u_of U) +
       (cA1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) a_s b_s U V / v_of V) *
        EB_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V)
      (q1_lead0 a0 b0) ∧
    HasValGe 0 (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)) := by
  have hA := fiveS_sub_9Q_ne; have hB := T_K_sub_3_ne
  set A := 5 * S_K - 9 * Q_K
  set B := T_K - 3
  intro q1_lead0
  have h9_ne : (9 : K5) ≠ 0 := by exact_mod_cast (by decide : (9 : ℕ) ≠ 0)
  have hU0 : ValLead 0 U 0 := ValLead.of_hasValGe_succ hU_L.val
  have hu_L : ValLead 0 (u_of U) (-(1 / 9 : K5)) := by
    unfold u_of
    exact ((hU0.sub (ValLead.of_C 1)).div_of_ne (ValLead.of_nat 9) h9_ne).eq_k (by omega) |>.eq_c (by ring)
  have hv_L : ValLead (-1) (v_of V) (w0 / 9) := by
    unfold v_of
    rw [show (V - 1 : LaurentSeries K5) = V + HahnSeries.C (-1 : K5) by
      simp only [map_neg, map_one]; ring]
    exact ((hV_L.add_high (HasValGe.of_C (-1 : K5))).div_of_ne
      (ValLead.of_nat 9) h9_ne).eq_k (by omega)
  have hw09_ne : w0 / 9 ≠ 0 := div_ne_zero hw0_ne h9_ne
  have hneg19_ne : (-(1 / 9 : K5)) ≠ 0 := neg_ne_zero.mpr (div_ne_zero one_ne_zero h9_ne)
  have hlinUV {f0 f1 f2 f3 : K5} :
      ValLead (-1) (HahnSeries.C f0 + HahnSeries.C f1 * V + HahnSeries.C f2 * U + HahnSeries.C f3 * U * V)
        (f1 * w0) := by
    have ht1 : ValLead (-1) (HahnSeries.C f1 * V) (f1 * w0) :=
      ((ValLead.of_C f1).mul hV_L).eq_k (by omega)
    have hhi : HasValGe 0 (HahnSeries.C f0 + HahnSeries.C f2 * U + HahnSeries.C f3 * U * V) :=
      ((HasValGe.of_C f0).add (((HasValGe.of_C f2).mul hU_L.val).mono (by omega))).add
        ((((HasValGe.of_C f3).mul hU_L.val).mul hV_L.val).mono (by omega))
    have hre : HahnSeries.C f0 + HahnSeries.C f1 * V + HahnSeries.C f2 * U + HahnSeries.C f3 * U * V =
        HahnSeries.C f1 * V + (HahnSeries.C f0 + HahnSeries.C f2 * U + HahnSeries.C f3 * U * V) := by ring
    rw [hre]; exact ht1.add_high hhi
  have hA1_L : ValLead (-1) (A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V) (A1_of S_K Q_K 0 1 * w0) := by
    have heq : A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V =
        HahnSeries.C 0 + HahnSeries.C (A1_of S_K Q_K 0 1) * V + HahnSeries.C 0 * U +
        HahnSeries.C (A1_of S_K Q_K 1 1 - A1_of S_K Q_K 0 1) * U * V := by
      simp only [A1_of, map_sub, map_mul, map_div₀, map_pow, map_ofNat, map_one, map_zero]
      ring
    rw [heq]; exact hlinUV
  have hB1_0 : HasValGe 0 (B1_of (HahnSeries.C T_K) U V) := by
    unfold B1_of
    rw [show (1 / 27 : LaurentSeries K5) = HahnSeries.C (1 / 27 : K5) by simp only [map_div₀, map_ofNat, map_one]]
    have hinner : HasValGe (-1) (25 * HahnSeries.C T_K * (5 * HahnSeries.C T_K - 9) ^ 2 -
        4 * (HahnSeries.C T_K - 3) ^ 3 * V) :=
      ((((HasValGe.of_nat 25).mul (HasValGe.of_C T_K)).mul
        ((((HasValGe.of_nat 5).mul (HasValGe.of_C T_K)).sub (HasValGe.of_nat 9)).pow 2)).mono (by omega)).sub
      ((((HasValGe.of_nat 4).mul (((HasValGe.of_C T_K).sub (HasValGe.of_nat 3)).pow 3)).mul hV_L.val).mono (by omega))
    exact (((HasValGe.of_C _).mul hU_L.val).mul hinner).mono (by omega)
  have hEB_L : ValLead (-1) (EB_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V) (EB_of S_K Q_K T_K x_K y_K 0 1 * w0) := by
    have hbi := EB_bilinear_UV (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V
    have h00 := map_EB_of (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 0 0
    have h01 := map_EB_of (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 0 1
    have h10 := map_EB_of (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 1 0
    have h11 := map_EB_of (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 1 1
    simp only [map_zero, map_one] at h00 h01 h10 h11
    rw [hbi, h00, h01, h10, h11, ← map_sub, ← map_sub, ← map_sub, ← map_sub, ← map_add]
    exact hlinUV.eq_c (by rw [EB_of_zero_zero, sub_zero])
  have hQY_L (i : Fin 3) : ValLead (-1)
      (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V i)
      ((QY_num S_K Q_K T_K x_K y_K 0 1 i - QY_num S_K Q_K T_K x_K y_K 0 0 i) * w0) := by
    have hbi := QY_bilinear_UV (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V i
    have h00 := map_QY_num (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 0 0 i
    have h01 := map_QY_num (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 0 1 i
    have h10 := map_QY_num (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 1 0 i
    have h11 := map_QY_num (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 1 1 i
    simp only [map_zero, map_one] at h00 h01 h10 h11
    rw [hbi, h00, h01, h10, h11, ← map_sub, ← map_sub, ← map_sub, ← map_sub, ← map_add]
    exact hlinUV
  have hQX_L (i : Fin 3) : ValLead (-1)
      (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V i)
      ((QX_num S_K Q_K T_K x_K y_K 0 1 i - QX_num S_K Q_K T_K x_K y_K 0 0 i) * w0) := by
    have hbi := QX_bilinear_UV (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V i
    have h00 := map_QX_num (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 0 0 i
    have h01 := map_QX_num (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 0 1 i
    have h10 := map_QX_num (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 1 0 i
    have h11 := map_QX_num (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 1 1 i
    simp only [map_zero, map_one] at h00 h01 h10 h11
    rw [hbi, h00, h01, h10, h11, ← map_sub, ← map_sub, ← map_sub, ← map_sub, ← map_add]
    exact hlinUV
  have hQX_0 : HasValGe 0 (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / u_of U) := by
    have hdot : ValLead (-1) (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s) 0 := by
      have h1 : ValLead (-1) (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
          (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s)
          (((QX_num S_K Q_K T_K x_K y_K 0 1 0 - QX_num S_K Q_K T_K x_K y_K 0 0 0) * a0 +
            (QX_num S_K Q_K T_K x_K y_K 0 1 1 - QX_num S_K Q_K T_K x_K y_K 0 0 1) * b0 +
            (QX_num S_K Q_K T_K x_K y_K 0 1 2 - QX_num S_K Q_K T_K x_K y_K 0 0 2)) * w0) := by
        unfold dot_ab
        exact ((((hQX_L 0).mul ha_L).eq_k (by omega)).add
          (((hQX_L 1).mul hb_L).eq_k (by omega))).add (hQX_L 2) |>.eq_c (by ring)
      refine h1.eq_c ?_
      have hlin0 : B * (-(5 * S_K - 3 * Q_K) * a0 + 6 * S_K * b0) + S_K * A = 0 := by
        have h2581 : (25 / 81 : K5) ≠ 0 := div_ne_zero
          (by exact_mod_cast (by decide : (25 : ℕ) ≠ 0))
          (by exact_mod_cast (by decide : (81 : ℕ) ≠ 0))
        have hw0_mul : B ^ 3 * w0 = -(25 / 4 : K5) * S_K * A ^ 2 := by
          rw [hw0_eq, mul_div_cancel₀ _ (pow_ne_zero 3 hB)]
        apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero h2581 hA) (mul_ne_zero (pow_ne_zero 2 hB) hw0_ne))
        rw [mul_zero]
        have hident :
            (25 / 81 : K5) * A * (B ^ 2 * w0) * (B * (-(5 * S_K - 3 * Q_K) * a0 + 6 * S_K * b0) + S_K * A) =
            B ^ 3 * (ca0 * w0 * a0 + cb0 * w0 * b0 + c0W0) +
            (4 / 81 : K5) * B ^ 2 * w0 * (B ^ 3 * w0 + (25 / 4 : K5) * S_K * A ^ 2) := by
          rw [hca0, hcb0, hc0W0]; simp only [CoverParams.c0_V2, CoverParams.inv81, k5Params_inv3, k5Params_T, A, B]
          ring
        rw [hident, hlin_raw, mul_zero, zero_add, hw0_mul]
        ring
      have hprop : B * ((QX_num S_K Q_K T_K x_K y_K 0 1 0 - QX_num S_K Q_K T_K x_K y_K 0 0 0) * a0 +
          (QX_num S_K Q_K T_K x_K y_K 0 1 1 - QX_num S_K Q_K T_K x_K y_K 0 0 1) * b0 +
          (QX_num S_K Q_K T_K x_K y_K 0 1 2 - QX_num S_K Q_K T_K x_K y_K 0 0 2)) =
          (80 / 81 : K5) * x_K * T_K ^ 2 * S_K ^ 2 * B ^ 3 *
            (23 * S_K ^ 3 - 82 * S_K ^ 2 * Q_K + 71 * S_K * Q_K ^ 2 + 4 * Q_K ^ 3 -
              50 * S_K ^ 2 * x_K + 90 * S_K * Q_K * x_K + 27 * S_K * x_K ^ 2) *
            (B * (-(5 * S_K - 3 * Q_K) * a0 + 6 * S_K * b0) + S_K * A) :=
        QX_num_01_sub_00_factor S_K Q_K T_K x_K y_K a0 b0
      have hzero : (QX_num S_K Q_K T_K x_K y_K 0 1 0 - QX_num S_K Q_K T_K x_K y_K 0 0 0) * a0 +
          (QX_num S_K Q_K T_K x_K y_K 0 1 1 - QX_num S_K Q_K T_K x_K y_K 0 0 1) * b0 +
          (QX_num S_K Q_K T_K x_K y_K 0 1 2 - QX_num S_K Q_K T_K x_K y_K 0 0 2) = 0 := by
        apply mul_left_cancel₀ hB
        rw [mul_zero, hprop, hlin0, mul_zero]
      rw [hzero, zero_mul]
    exact (hdot.hasValGe_succ.div_of_lead_ne hu_L.val (hu_L.c0.symm ▸ hneg19_ne)).1.mono (by omega)
  have hqY_L : ValLead 0
      (dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / v_of V)
      (9 * ((QY_num S_K Q_K T_K x_K y_K 0 1 0 - QY_num S_K Q_K T_K x_K y_K 0 0 0) * a0 +
            (QY_num S_K Q_K T_K x_K y_K 0 1 1 - QY_num S_K Q_K T_K x_K y_K 0 0 1) * b0 +
            (QY_num S_K Q_K T_K x_K y_K 0 1 2 - QY_num S_K Q_K T_K x_K y_K 0 0 2))) := by
    have hdot : ValLead (-1) (dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s)
        (((QY_num S_K Q_K T_K x_K y_K 0 1 0 - QY_num S_K Q_K T_K x_K y_K 0 0 0) * a0 +
          (QY_num S_K Q_K T_K x_K y_K 0 1 1 - QY_num S_K Q_K T_K x_K y_K 0 0 1) * b0 +
          (QY_num S_K Q_K T_K x_K y_K 0 1 2 - QY_num S_K Q_K T_K x_K y_K 0 0 2)) * w0) := by
      unfold dot_ab
      exact ((((hQY_L 0).mul ha_L).eq_k (by omega)).add
        (((hQY_L 1).mul hb_L).eq_k (by omega))).add (hQY_L 2) |>.eq_c (by ring)
    exact (hdot.div_of_ne hv_L hw09_ne).eq_k (by omega) |>.eq_c (by
      have hdiv (x : K5) : x * w0 / (w0 / 9) = 9 * x := by
        rw [div_div_eq_mul_div, mul_right_comm, mul_div_cancel_right₀ _ hw0_ne, _root_.mul_comm]
      exact hdiv _)
  have hH0_L : ValLead 0 (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)) (H0_of S_K Q_K T_K) := by
    rw [show H0_of (HahnSeries.C S_K : LaurentSeries K5) (HahnSeries.C Q_K) (HahnSeries.C T_K) = HahnSeries.C (H0_of S_K Q_K T_K) by
      simp only [H0_of, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]]
    exact ValLead.of_C _
  have hcA1_L : ValLead (-1) (cA1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) a_s b_s U V)
      (((H0_of S_K Q_K T_K * dA1_fn 0 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 0 S_K Q_K T_K) * a0 +
        (H0_of S_K Q_K T_K * dA1_fn 1 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 1 S_K Q_K T_K) * b0 +
        (H0_of S_K Q_K T_K * dA1_fn 2 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 2 S_K Q_K T_K)) * w0) := by
    have hdA1_L (k : Fin 3) : ValLead (-1) (dA1_fn k (HahnSeries.C S_K) (HahnSeries.C Q_K) U V)
        (dA1_fn k S_K Q_K 0 1 * w0) := by
      fin_cases k
      · change ValLead (-1) (dA1_fn 0 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V) (dA1_fn 0 S_K Q_K 0 1 * w0)
        have heq : dA1_fn 0 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V =
            HahnSeries.C 0 + HahnSeries.C (dA1_fn 0 S_K Q_K 0 1) * V + HahnSeries.C 0 * U +
            HahnSeries.C (dA1_fn 0 S_K Q_K 1 1 - dA1_fn 0 S_K Q_K 0 1) * U * V := by
          simp only [dA1_fn, map_sub, map_mul, map_div₀, map_pow, map_ofNat, map_one, map_zero]; ring
        rw [heq]; exact hlinUV
      · change ValLead (-1) (dA1_fn 1 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V) (dA1_fn 1 S_K Q_K 0 1 * w0)
        have heq : dA1_fn 1 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V =
            HahnSeries.C 0 + HahnSeries.C (dA1_fn 1 S_K Q_K 0 1) * V + HahnSeries.C 0 * U +
            HahnSeries.C (dA1_fn 1 S_K Q_K 1 1 - dA1_fn 1 S_K Q_K 0 1) * U * V := by
          simp only [dA1_fn, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat, map_one, map_zero]; ring
        rw [heq]; exact hlinUV
      · exact (ValLead.of_hasValGe_succ (HasValGe.zero 0)).eq_c (by simp [dA1_fn])
    have hdH0_L (k : Fin 3) : ValLead 0 (dH0_fn k (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K))
        (dH0_fn k S_K Q_K T_K) := by
      rw [show dH0_fn k (HahnSeries.C S_K : LaurentSeries K5) (HahnSeries.C Q_K) (HahnSeries.C T_K) = HahnSeries.C (dH0_fn k S_K Q_K T_K) by
        fin_cases k <;> simp only [dH0_fn, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]]
      exact ValLead.of_C _
    unfold cA1_of
    exact (((((hH0_L.mul (hdA1_L 0)).sub (hA1_L.mul (hdH0_L 0) |>.eq_k (by omega))).mul ha_L).eq_k (by omega)).add
      ((((hH0_L.mul (hdA1_L 1)).sub (hA1_L.mul (hdH0_L 1) |>.eq_k (by omega))).mul hb_L).eq_k (by omega))).add
      (((hH0_L.mul (hdA1_L 2)).sub (hA1_L.mul (hdH0_L 2) |>.eq_k (by omega))).eq_k (by omega))
      |>.eq_c (by ring)
  have hq1_L : ValLead (-1)
      (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) *
        A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V *
        (dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
          (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / v_of V) +
       H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) *
        B1_of (HahnSeries.C T_K) U V *
        (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
          (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / u_of U) +
       (cA1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) a_s b_s U V / v_of V) *
        EB_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V)
      (q1_lead0 a0 b0) := by
    have ht1 := ((hH0_L.mul hA1_L).mul hqY_L).eq_k (k' := -1) (by omega)
    have ht2 : HasValGe 0 (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) *
        B1_of (HahnSeries.C T_K) U V *
        (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
          (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / u_of U)) :=
      ((hH0_L.val.mul hB1_0).mul hQX_0).mono (by omega)
    have ht3 := ((hcA1_L.div_of_ne hv_L hw09_ne).mul hEB_L).eq_k (k' := -1) (by omega)
    have hre : ∀ x y z : LaurentSeries K5, x + y + z = (x + z) + y := fun x y z => by ring
    rw [hre]
    exact ((ht1.add ht3).add_high ht2).eq_c (by
      have hcomb (h a qy ca eb : K5) :
          h * (a * w0) * (9 * qy) + ca * w0 / (w0 / 9) * (eb * w0) =
            w0 * (h * a * (9 * qy) + 9 * ca * eb) := by
        have hdiv : ca * w0 / (w0 / 9) = 9 * ca := by
          rw [div_div_eq_mul_div, mul_right_comm, mul_div_cancel_right₀ _ hw0_ne, _root_.mul_comm]
        rw [hdiv]; ring
      exact hcomb _ _ _ _ _)
  exact ⟨hqY_L.val, hQX_0, hq1_L, hH0_L.val⟩

private lemma br2_0_g_lead_core
    {a_s b_s U V : LaurentSeries K5} {w0 ca0 cb0 c0W0 a0 b0 : K5}
    (hw0_eq : w0 = -(25 / 4 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 2 / (T_K - 3) ^ 3)
    (hw0_ne : w0 ≠ 0)
    (hca0 : ca0 = -(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K))
    (hcb0 : cb0 = (50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K))
    (hc0W0 : c0W0 = k5Params.c0_V2 * w0 ^ 2)
    (hlin_raw : ca0 * w0 * a0 + cb0 * w0 * b0 + c0W0 = 0)
    (ha_L : ValLead 0 a_s a0) (hb_L : ValLead 0 b_s b0)
    (hU_L : ValLead 1 U 1) (hV_L : ValLead (-1) V w0) :
    let q1_lead0 : K5 → K5 → K5 := fun a b =>
      let qY0 := 9 * ((QY_num S_K Q_K T_K x_K y_K 0 1 0 - QY_num S_K Q_K T_K x_K y_K 0 0 0) * a +
        (QY_num S_K Q_K T_K x_K y_K 0 1 1 - QY_num S_K Q_K T_K x_K y_K 0 0 1) * b +
        (QY_num S_K Q_K T_K x_K y_K 0 1 2 - QY_num S_K Q_K T_K x_K y_K 0 0 2))
      let cA0 := 9 * ((H0_of S_K Q_K T_K * dA1_fn 0 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 0 S_K Q_K T_K) * a +
        (H0_of S_K Q_K T_K * dA1_fn 1 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 1 S_K Q_K T_K) * b +
        (H0_of S_K Q_K T_K * dA1_fn 2 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 2 S_K Q_K T_K))
      w0 * (H0_of S_K Q_K T_K * A1_of S_K Q_K 0 1 * qY0 + cA0 * EB_of S_K Q_K T_K x_K y_K 0 1)
    ValLead (-3)
      (P18_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) a_s b_s U V)
      (w0 ^ 2 * A0U_12_of (RingHom.id K5) a0 b0 * q1_lead0 a0 b0) := by
  intro q1_lead0
  obtain ⟨hM0_L, hAY_m2, hAX_m1⟩ := br2_0_numM_bounds hw0_ne ha_L hb_L hU_L hV_L
  obtain ⟨hqY_0, hQX_0, hq1_L, hH0_0⟩ := br2_0_q1_lead hw0_eq hw0_ne hca0 hcb0 hc0W0 hlin_raw ha_L hb_L hU_L hV_L
  have hrest : HasValGe (-2)
      ((A_Y a_s b_s (HahnSeries.C S_K - a_s * HahnSeries.C T_K) (HahnSeries.C Q_K - b_s * HahnSeries.C T_K) U V *
        (dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
          (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / v_of V) +
        A_X a_s b_s (HahnSeries.C S_K - a_s * HahnSeries.C T_K) (HahnSeries.C Q_K - b_s * HahnSeries.C T_K) U V *
        (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
          (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / u_of U)) *
       H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) ^ 2) :=
    (((hAY_m2.mul hqY_0).mono (k2 := -2) (by omega)).add ((hAX_m1.mul hQX_0).mono (k2 := -2) (by omega))).mul
      (hH0_0.pow 2) |>.mono (by omega)
  rw [P18_of_HahnC_eq]
  exact ((hM0_L.mul hq1_L).eq_k (by omega)).add_high hrest

private lemma br2_0_g_lead
    {W2s U V ca cb c0W : LaurentSeries K5} {w0 ca0 cb0 c0W0 : K5}
    (hw0_eq : w0 = -(25 / 4 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 2 / (T_K - 3) ^ 3)
    (hw0_ne : w0 ≠ 0) (hcb0_ne : cb0 ≠ 0)
    (hca0 : ca0 = -(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K))
    (hcb0 : cb0 = (50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K))
    (hc0W0 : c0W0 = k5Params.c0_V2 * w0 ^ 2)
    (hw0_L : ValLead 0 W2s w0) (hU_L : ValLead 1 U 1) (hV_L : ValLead (-1) V w0)
    (hca_L : ValLead 0 ca ca0) (hcb_L : ValLead 0 cb cb0) (hc0W_L : ValLead 0 c0W c0W0) :
    let q1_lead0 : K5 → K5 → K5 := fun a b =>
      let qY0 := 9 * ((QY_num S_K Q_K T_K x_K y_K 0 1 0 - QY_num S_K Q_K T_K x_K y_K 0 0 0) * a +
        (QY_num S_K Q_K T_K x_K y_K 0 1 1 - QY_num S_K Q_K T_K x_K y_K 0 0 1) * b +
        (QY_num S_K Q_K T_K x_K y_K 0 1 2 - QY_num S_K Q_K T_K x_K y_K 0 0 2))
      let cA0 := 9 * ((H0_of S_K Q_K T_K * dA1_fn 0 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 0 S_K Q_K T_K) * a +
        (H0_of S_K Q_K T_K * dA1_fn 1 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 1 S_K Q_K T_K) * b +
        (H0_of S_K Q_K T_K * dA1_fn 2 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 2 S_K Q_K T_K))
      w0 * (H0_of S_K Q_K T_K * A1_of S_K Q_K 0 1 * qY0 + cA0 * EB_of S_K Q_K T_K x_K y_K 0 1)
    ∀ z : K5,
      let a := z / w0; let b := -(ca0 * z + c0W0) / (w0 * cb0)
      ValLead (-3)
        (P18_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
          (HahnSeries.C x_K) (HahnSeries.C y_K)
          (HahnSeries.C z / W2s) (-(ca * HahnSeries.C z + c0W) / (W2s * cb)) U V)
        (w0 ^ 2 * A0U_12_of (RingHom.id K5) a b * q1_lead0 a b) := by
  intro q1_lead0 z
  let a0 : K5 := z / w0
  let b0 : K5 := -(ca0 * z + c0W0) / (w0 * cb0)
  have ha_L : ValLead 0 (HahnSeries.C z / W2s) a0 := ((ValLead.of_C z).div_of_ne hw0_L hw0_ne).eq_k (by omega)
  have hb_L : ValLead 0 (-(ca * HahnSeries.C z + c0W) / (W2s * cb)) b0 := by
    have hnum : ValLead 0 (-(ca * HahnSeries.C z + c0W)) (-(ca0 * z + c0W0)) :=
      (((hca_L.mul (ValLead.of_C z)).eq_k (by omega)).add hc0W_L).neg
    have hden : ValLead 0 (W2s * cb) (w0 * cb0) := (hw0_L.mul hcb_L).eq_k (by omega)
    exact (hnum.div_of_ne hden (mul_ne_zero hw0_ne hcb0_ne)).eq_k (by omega)
  have hlin_raw : ca0 * w0 * a0 + cb0 * w0 * b0 + c0W0 = 0 := by
    dsimp only [a0, b0]; field_simp [hw0_ne, hcb0_ne]; ring
  exact br2_0_g_lead_core hw0_eq hw0_ne hca0 hcb0 hc0W0 hlin_raw ha_L hb_L hU_L hV_L

private def br2_0_m_sc {F : Type*} [Field F] (S Q T : F) (mi : Fin 10) : Dual F :=
  let B := T - 3
  let d_ab := 6 * S * B
  let a_s : Dual F := ⟨6 * S ^ 2, 6 * S * B⟩
  let b_s : Dual F := ⟨6 * S * Q, (5 * S - 3 * Q) * B⟩
  let ξS_s : Dual F := ⟨-18 * S ^ 2, -6 * S * B * T⟩
  let ξQ_s : Dual F := ⟨-18 * S * Q, -(5 * S - 3 * Q) * B * T⟩
  let dHS_v := fun s q : Dual F => Dual.C (-(25 / 243 : F)) * (5 * s - 9 * q) * (15 * s - 9 * q)
  let dHS_e := fun s q : Dual F =>
    Dual.C (143 / 81 : F) * s ^ 2 - Dual.C (184 / 27 : F) * s * q + Dual.C (52 / 9 : F) * q ^ 2
  let dHQ_v := fun s q : Dual F => Dual.C (50 / 27 : F) * s * (5 * s - 9 * q)
  let dHQ_e := fun (s q : Dual F) (v0 : F) =>
    Dual.C (-(92 / 27 : F)) * s ^ 2 + Dual.C (104 / 9 : F) * s * q - Dual.C (22 / 3 : F) * q ^ 2 +
      Dual.C ((10 / 7 : F) * v0) * q + Dual.C ((10 / 7 : F) * v0 ^ 2)
  let a2_v := dHS_v a_s b_s; let a2_e := dHS_e a_s b_s
  let a0_v := dHS_v ξS_s ξQ_s; let a0_e := dHS_e ξS_s ξQ_s
  let a1_v := dHS_v (a_s + ξS_s) (b_s + ξQ_s) - a2_v - a0_v
  let a1_e := dHS_e (a_s + ξS_s) (b_s + ξQ_s) - a2_e - a0_e
  let b2_v := dHQ_v a_s b_s; let b2_e := dHQ_e a_s b_s 0
  let b0_v := dHQ_v ξS_s ξQ_s; let b0_e := dHQ_e ξS_s ξQ_s d_ab
  let b1_v := dHQ_v (a_s + ξS_s) (b_s + ξQ_s) - b2_v - b0_v
  let b1_e := dHQ_e (a_s + ξS_s) (b_s + ξQ_s) 0 - b2_e - dHQ_e ξS_s ξQ_s 0 + Dual.C ((10 / 7 : F) * d_ab) * b_s
  let d20_e := a2_v * b0_e + a2_e * b0_v - a0_v * b2_e - a0_e * b2_v
  let d21_e := a2_v * b1_e + a2_e * b1_v - a1_v * b2_e - a1_e * b2_v
  let d10_e := a1_v * b0_e + a1_e * b0_v - a0_v * b1_e - a0_e * b1_v
  let (m2, m1, m0) : Dual F × Dual F × Dual F := match mi with
    | 0 => (a_s ^ 2, 2 * a_s * ξS_s, ξS_s ^ 2)
    | 1 => (a_s * b_s, a_s * ξQ_s + b_s * ξS_s, ξS_s * ξQ_s)
    | 2 => (b_s ^ 2, 2 * b_s * ξQ_s, ξQ_s ^ 2)
    | 3 => (Dual.C d_ab * a_s, Dual.C d_ab * ξS_s, 0)
    | 4 => (0, Dual.C d_ab * a_s, Dual.C d_ab * ξS_s)
    | 5 => (Dual.C d_ab * b_s, Dual.C d_ab * ξQ_s, 0)
    | 6 => (0, Dual.C d_ab * b_s, Dual.C d_ab * ξQ_s)
    | 7 => (Dual.C (d_ab ^ 2), 0, 0)
    | 8 => (0, Dual.C (d_ab ^ 2), 0)
    | 9 => (0, 0, Dual.C (d_ab ^ 2))
  Dual.C (1 / 16 : F) * (m2 * d10_e - m1 * d20_e + m0 * d21_e)

private lemma br2_0_A0U_scaled_poly {F : Type*} [Field F] [CharZero F] (S Q T : F) :
    let A := 5 * S - 9 * Q
    let B := T - 3
    let d_ab := 6 * S * B
    let Q_quad := 11943020 * S ^ 2 - 876486 * S * Q + 8382500 * S * T +
      5029500 * Q * T - 14837025 * S - 33647355 * Q
    Dual.C (-(19708 / 1257375 : F)) * (5 * br2_0_m_sc S Q T 0 - 9 * br2_0_m_sc S Q T 1) +
      Dual.C (1472 / 1257375 : F) * (5 * br2_0_m_sc S Q T 1 - 9 * br2_0_m_sc S Q T 2) -
      Dual.C (16 / 729 : F) * (5 * br2_0_m_sc S Q T 3 - 9 * br2_0_m_sc S Q T 5) +
      Dual.C (188 / 2025 : F) * (5 * br2_0_m_sc S Q T 4 - 9 * br2_0_m_sc S Q T 6) =
    Dual.C (d_ab ^ 3) * ⟨(8248380 / 51331077 : F) * (5 * S - 3 * Q) * S ^ 3 * A ^ 2,
      -(2 / 51331077 : F) * B * S ^ 2 * A ^ 2 * Q_quad⟩ := by
  intro A B d_ab Q_quad
  let a_s : Dual F := ⟨6 * S ^ 2, 6 * S * B⟩
  let b_s : Dual F := ⟨6 * S * Q, (5 * S - 3 * Q) * B⟩
  let ξS_s : Dual F := ⟨-18 * S ^ 2, -6 * S * B * T⟩
  let ξQ_s : Dual F := ⟨-18 * S * Q, -(5 * S - 3 * Q) * B * T⟩
  let dHS_v := fun s q : Dual F => Dual.C (-(25 / 243 : F)) * (5 * s - 9 * q) * (15 * s - 9 * q)
  let dHS_e := fun s q : Dual F =>
    Dual.C (143 / 81 : F) * s ^ 2 - Dual.C (184 / 27 : F) * s * q + Dual.C (52 / 9 : F) * q ^ 2
  let dHQ_v := fun s q : Dual F => Dual.C (50 / 27 : F) * s * (5 * s - 9 * q)
  let dHQ_e := fun (s q : Dual F) (v0 : F) =>
    Dual.C (-(92 / 27 : F)) * s ^ 2 + Dual.C (104 / 9 : F) * s * q - Dual.C (22 / 3 : F) * q ^ 2 +
      Dual.C ((10 / 7 : F) * v0) * q + Dual.C ((10 / 7 : F) * v0 ^ 2)
  let a2_v := dHS_v a_s b_s; let a2_e := dHS_e a_s b_s
  let a0_v := dHS_v ξS_s ξQ_s; let a0_e := dHS_e ξS_s ξQ_s
  let a1_v := dHS_v (a_s + ξS_s) (b_s + ξQ_s) - a2_v - a0_v
  let a1_e := dHS_e (a_s + ξS_s) (b_s + ξQ_s) - a2_e - a0_e
  let b2_v := dHQ_v a_s b_s; let b2_e := dHQ_e a_s b_s 0
  let b0_v := dHQ_v ξS_s ξQ_s; let b0_e := dHQ_e ξS_s ξQ_s d_ab
  let b1_v := dHQ_v (a_s + ξS_s) (b_s + ξQ_s) - b2_v - b0_v
  let b1_e := dHQ_e (a_s + ξS_s) (b_s + ξQ_s) 0 - b2_e - dHQ_e ξS_s ξQ_s 0 + Dual.C ((10 / 7 : F) * d_ab) * b_s
  set d20 : Dual F := a2_v * b0_e + a2_e * b0_v - a0_v * b2_e - a0_e * b2_v
  set d21 : Dual F := a2_v * b1_e + a2_e * b1_v - a1_v * b2_e - a1_e * b2_v
  set d10 : Dual F := a1_v * b0_e + a1_e * b0_v - a0_v * b1_e - a0_e * b1_v
  have hd20 : d20 =
      ⟨-(4000 / 7 : F) * B * (-3 * Q + B) * (-5 * S + 3 * Q) * (-A) * S ^ 4,
       -(400 / 21 : F) * (-A) * B ^ 2 * S ^ 3 *
         (259 * S ^ 3 - 1722 * S ^ 2 * Q + 1932 * S * Q ^ 2 + 125 * S ^ 2 * T -
           150 * S * Q * T + 45 * Q ^ 2 * T + 270 * Q ^ 2 - 90 * Q * T + 270 * Q)⟩ := by
    ext <;> (simp only [d20, a2_v, a2_e, a0_v, a0_e, b2_v, b2_e, b0_v, b0_e,
      dHS_v, dHS_e, dHQ_v, dHQ_e, a_s, b_s, ξS_s, ξQ_s, d_ab, A, B,
      Dual.C_val, Dual.C_eps, Dual.add_val, Dual.sub_val, Dual.mul_val, Dual.pow_eq,
      Dual.add_eps, Dual.sub_eps, Dual.mul_eps, Dual.ofNat_val, Dual.ofNat_eps,
      Nat.cast_ofNat, Nat.reduceSub, pow_one, add_zero, mul_zero, zero_mul]; ring)
  have hd21 : d21 =
      ⟨-(4000 / 7 : F) * B * Q * (-5 * S + 3 * Q) * (-A) * S ^ 4,
       (400 / 63 : F) * (-A) * B ^ 2 * S ^ 3 *
         (259 * S ^ 3 - 1722 * S ^ 2 * Q + 1932 * S * Q ^ 2 + 375 * S ^ 2 - 450 * S * Q + 405 * Q ^ 2)⟩ := by
    ext <;> (simp only [d21, a2_v, a2_e, a1_v, a1_e, a0_v, a0_e, b2_v, b2_e, b1_v, b1_e, b0_v, 
      dHS_v, dHS_e, dHQ_v, dHQ_e, a_s, b_s, ξS_s, ξQ_s, d_ab, A, B,
      Dual.C_val, Dual.C_eps, Dual.add_val, Dual.sub_val, Dual.mul_val, Dual.pow_eq,
      Dual.add_eps, Dual.sub_eps, Dual.mul_eps, Dual.ofNat_val, Dual.ofNat_eps,
      Nat.cast_ofNat, Nat.reduceSub, pow_one, add_zero, mul_zero, zero_mul]; ring)
  have hd10 : d10 =
      ⟨(12000 / 7 : F) * B * (-3 * Q + 2 * B) * (-5 * S + 3 * Q) * (-A) * S ^ 4,
       -(400 / 7 : F) * (-A) * B ^ 2 * S ^ 3 *
         (-259 * S ^ 3 + 1722 * S ^ 2 * Q - 1932 * S * Q ^ 2 - 250 * S ^ 2 * T +
           300 * S * Q * T - 90 * Q ^ 2 * T + 30 * Q * T ^ 2 + 375 * S ^ 2 - 450 * S * Q - 135 * Q ^ 2 - 270 * Q)⟩ := by
    ext <;> (simp only [d10, a2_v, a2_e, a1_v, a1_e, a0_v, a0_e, b2_v, b2_e, b1_v, b1_e, b0_v, b0_e,
      dHS_v, dHS_e, dHQ_v, dHQ_e, a_s, b_s, ξS_s, ξQ_s, d_ab, A, B,
      Dual.C_val, Dual.C_eps, Dual.add_val, Dual.sub_val, Dual.mul_val, Dual.pow_eq,
      Dual.add_eps, Dual.sub_eps, Dual.mul_eps, Dual.ofNat_val, Dual.ofNat_eps,
      Nat.cast_ofNat, Nat.reduceSub, pow_one, add_zero, mul_zero, zero_mul]; ring)
  have hbr_m (mi : Fin 10) : br2_0_m_sc S Q T mi =
      let (m2, m1, m0) : Dual F × Dual F × Dual F := match mi with
        | 0 => (a_s ^ 2, 2 * a_s * ξS_s, ξS_s ^ 2)
        | 1 => (a_s * b_s, a_s * ξQ_s + b_s * ξS_s, ξS_s * ξQ_s)
        | 2 => (b_s ^ 2, 2 * b_s * ξQ_s, ξQ_s ^ 2)
        | 3 => (Dual.C d_ab * a_s, Dual.C d_ab * ξS_s, 0)
        | 4 => (0, Dual.C d_ab * a_s, Dual.C d_ab * ξS_s)
        | 5 => (Dual.C d_ab * b_s, Dual.C d_ab * ξQ_s, 0)
        | 6 => (0, Dual.C d_ab * b_s, Dual.C d_ab * ξQ_s)
        | 7 => (Dual.C (d_ab ^ 2), 0, 0)
        | 8 => (0, Dual.C (d_ab ^ 2), 0)
        | 9 => (0, 0, Dual.C (d_ab ^ 2))
      Dual.C (1 / 16 : F) * (m2 * d10 - m1 * d20 + m0 * d21) := rfl
  have hlin :
      Dual.C (-(19708 / 1257375 : F)) * (5 * br2_0_m_sc S Q T 0 - 9 * br2_0_m_sc S Q T 1) +
        Dual.C (1472 / 1257375 : F) * (5 * br2_0_m_sc S Q T 1 - 9 * br2_0_m_sc S Q T 2) -
        Dual.C (16 / 729 : F) * (5 * br2_0_m_sc S Q T 3 - 9 * br2_0_m_sc S Q T 5) +
        Dual.C (188 / 2025 : F) * (5 * br2_0_m_sc S Q T 4 - 9 * br2_0_m_sc S Q T 6) =
      Dual.C (1 / 16 : F) *
        ((Dual.C (-(19708 / 1257375 : F)) * (5 * a_s ^ 2 - 9 * (a_s * b_s)) +
          Dual.C (1472 / 1257375 : F) * (5 * (a_s * b_s) - 9 * b_s ^ 2) -
          Dual.C (16 / 729 : F) * (5 * (Dual.C d_ab * a_s) - 9 * (Dual.C d_ab * b_s))) * d10 -
         (Dual.C (-(19708 / 1257375 : F)) * (5 * (2 * a_s * ξS_s) - 9 * (a_s * ξQ_s + b_s * ξS_s)) +
          Dual.C (1472 / 1257375 : F) * (5 * (a_s * ξQ_s + b_s * ξS_s) - 9 * (2 * b_s * ξQ_s)) -
          Dual.C (16 / 729 : F) * (5 * (Dual.C d_ab * ξS_s) - 9 * (Dual.C d_ab * ξQ_s)) +
          Dual.C (188 / 2025 : F) * (5 * (Dual.C d_ab * a_s) - 9 * (Dual.C d_ab * b_s))) * d20 +
         (Dual.C (-(19708 / 1257375 : F)) * (5 * ξS_s ^ 2 - 9 * (ξS_s * ξQ_s)) +
          Dual.C (1472 / 1257375 : F) * (5 * (ξS_s * ξQ_s) - 9 * ξQ_s ^ 2) +
          Dual.C (188 / 2025 : F) * (5 * (Dual.C d_ab * ξS_s) - 9 * (Dual.C d_ab * ξQ_s))) * d21) := by
    rw [hbr_m 0, hbr_m 1, hbr_m 2, hbr_m 3, hbr_m 4, hbr_m 5, hbr_m 6]
    ring
  rw [hlin, hd10, hd20, hd21]
  ext <;> (simp only [a_s, b_s, ξS_s, ξQ_s, d_ab, A, B, Q_quad,
    Dual.C_val, Dual.C_eps, Dual.add_val, Dual.sub_val, Dual.mul_val, Dual.pow_eq,
    Dual.add_eps, Dual.sub_eps, Dual.mul_eps, Dual.ofNat_val, Dual.ofNat_eps,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, add_zero, zero_mul]; ring)

private lemma br2_0_A0U_Z2_eval :
    let A := 5 * S_K - 9 * Q_K
    let B := T_K - 3
    let d_ab := 6 * S_K * B
    let Q_quad := 11943020 * S_K ^ 2 - 876486 * S_K * Q_K + 8382500 * S_K * T_K +
      5029500 * Q_K * T_K - 14837025 * S_K - 33647355 * Q_K
    let a_du : Dual K5 := Dual.C d_ab⁻¹ * ⟨6 * S_K ^ 2, 6 * S_K * B⟩
    let b_du : Dual K5 := Dual.C d_ab⁻¹ * ⟨6 * S_K * Q_K, (5 * S_K - 3 * Q_K) * B⟩
    Dual.C (d_ab ^ 3) * A0U_12_of Dual.C a_du b_du =
      ⟨(8248380 / 51331077 : K5) * (5 * S_K - 3 * Q_K) * S_K ^ 3 * A ^ 2,
       -(2 / 51331077 : K5) * B * S_K ^ 2 * A ^ 2 * Q_quad⟩ := by
  intro A B d_ab Q_quad a_du b_du
  have hS := S_K_ne_zero; have hB := T_K_sub_3_ne
  have h6_ne : (6 : K5) ≠ 0 := by exact_mod_cast (by decide : (6 : ℕ) ≠ 0)
  have hd_ab_ne : d_ab ≠ 0 := mul_ne_zero (mul_ne_zero h6_ne hS) hB
  set inv_d : K5 := d_ab⁻¹
  have hd_inv : d_ab * inv_d = 1 := mul_inv_cancel₀ hd_ab_ne
  set a_s : Dual K5 := ⟨6 * S_K ^ 2, 6 * S_K * B⟩
  set b_s : Dual K5 := ⟨6 * S_K * Q_K, (5 * S_K - 3 * Q_K) * B⟩
  set ξS_s : Dual K5 := ⟨-18 * S_K ^ 2, -6 * S_K * B * T_K⟩
  set ξQ_s : Dual K5 := ⟨-18 * S_K * Q_K, -(5 * S_K - 3 * Q_K) * B * T_K⟩
  have ha_du_eq : a_du = Dual.C inv_d * a_s := rfl
  have hb_du_eq : b_du = Dual.C inv_d * b_s := rfl
  have hξS_eq : Dual.C S_K - a_du * Dual.C T_K = Dual.C inv_d * ξS_s := by
    ext
    · simp only [a_du, ξS_s, Dual.C_val, Dual.sub_val, Dual.mul_val]
      have h := hd_inv; dsimp only [d_ab, B] at h ⊢; linear_combination -S_K * h
    · simp only [a_du, ξS_s, Dual.C_val, Dual.C_eps, Dual.sub_eps, Dual.mul_eps, Dual.mul_val]; ring
  have hξQ_eq : Dual.C Q_K - b_du * Dual.C T_K = Dual.C inv_d * ξQ_s := by
    ext
    · simp only [b_du, ξQ_s, Dual.C_val, Dual.sub_val, Dual.mul_val]
      have h := hd_inv; dsimp only [d_ab, B] at h ⊢; linear_combination -Q_K * h
    · simp only [b_du, ξQ_s, Dual.C_val, Dual.C_eps, Dual.sub_eps, Dual.mul_eps, Dual.mul_val]; ring
  let dHS_v := fun s q : Dual K5 => Dual.C (-(25 / 243 : K5)) * (5 * s - 9 * q) * (15 * s - 9 * q)
  let dHS_e := fun s q : Dual K5 =>
    Dual.C (143 / 81 : K5) * s ^ 2 - Dual.C (184 / 27 : K5) * s * q + Dual.C (52 / 9 : K5) * q ^ 2
  let dHQ_v := fun s q : Dual K5 => Dual.C (50 / 27 : K5) * s * (5 * s - 9 * q)
  let dHQ_e := fun (s q : Dual K5) (v0 : K5) =>
    Dual.C (-(92 / 27 : K5)) * s ^ 2 + Dual.C (104 / 9 : K5) * s * q - Dual.C (22 / 3 : K5) * q ^ 2 +
      Dual.C ((10 / 7 : K5) * v0) * q + Dual.C ((10 / 7 : K5) * v0 ^ 2)
  have hdHS_v (s q : Dual K5) : (dHS_12_of Dual.C (Dual.C inv_d * s) (Dual.C inv_d * q)).val =
      Dual.C (inv_d ^ 2) * dHS_v s q := by
    simp only [dHS_12_of, dHS_v, map_pow]; ring
  have hdHS_e (s q : Dual K5) : (dHS_12_of Dual.C (Dual.C inv_d * s) (Dual.C inv_d * q)).eps =
      Dual.C (inv_d ^ 2) * dHS_e s q := by
    simp only [dHS_12_of, dHS_e, map_pow]; ring
  have hdHQ_v (s q : Dual K5) (v0 : K5) : (dHQ_12_of Dual.C (Dual.C inv_d * s) (Dual.C inv_d * q) v0).val =
      Dual.C (inv_d ^ 2) * dHQ_v s q := by
    simp only [dHQ_12_of, dHQ_v, map_pow]; ring
  have hdHQ0_e (s q : Dual K5) : (dHQ_12_of Dual.C (Dual.C inv_d * s) (Dual.C inv_d * q) 0).eps =
      Dual.C (inv_d ^ 2) * dHQ_e s q 0 := by
    simp only [dHQ_12_of, dHQ_e, mul_zero, zero_pow (by decide : 2 ≠ 0), map_zero, zero_mul, add_zero, map_pow]; ring
  have hdHQ1_e (s q : Dual K5) : (dHQ_12_of Dual.C (Dual.C inv_d * s) (Dual.C inv_d * q) 1).eps =
      Dual.C (inv_d ^ 2) * dHQ_e s q d_ab := by
    have h1 : Dual.C (10 / 7 : K5) * (Dual.C inv_d * q) = Dual.C (inv_d ^ 2) * (Dual.C ((10 / 7 : K5) * d_ab) * q) := by
      have : (10 / 7 : K5) * inv_d = inv_d ^ 2 * ((10 / 7 : K5) * d_ab) := by
        linear_combination -((10 / 7 : K5) * inv_d) * hd_inv
      rw [← mul_assoc, ← map_mul, this, map_mul, mul_assoc]
    have h2 : Dual.C (10 / 7 : K5) = Dual.C (inv_d ^ 2) * Dual.C ((10 / 7 : K5) * d_ab ^ 2) := by
      rw [← map_mul]; congr 1
      linear_combination -((10 / 7 : K5) * (d_ab * inv_d + 1)) * hd_inv
    simp only [dHQ_12_of, dHQ_e, mul_one, one_pow]
    rw [h1, h2]; simp only [map_pow]; ring
  let a2_v := dHS_v a_s b_s; let a2_e := dHS_e a_s b_s
  let a0_v := dHS_v ξS_s ξQ_s; let a0_e := dHS_e ξS_s ξQ_s
  let a1_v := dHS_v (a_s + ξS_s) (b_s + ξQ_s) - a2_v - a0_v
  let a1_e := dHS_e (a_s + ξS_s) (b_s + ξQ_s) - a2_e - a0_e
  let b2_v := dHQ_v a_s b_s; let b2_e := dHQ_e a_s b_s 0
  let b0_v := dHQ_v ξS_s ξQ_s; let b0_e := dHQ_e ξS_s ξQ_s d_ab
  let b1_v := dHQ_v (a_s + ξS_s) (b_s + ξQ_s) - b2_v - b0_v
  let b1_e := dHQ_e (a_s + ξS_s) (b_s + ξQ_s) 0 - b2_e - dHQ_e ξS_s ξQ_s 0 + Dual.C ((10 / 7 : K5) * d_ab) * b_s
  let d20_e := a2_v * b0_e + a2_e * b0_v - a0_v * b2_e - a0_e * b2_v
  let d21_e := a2_v * b1_e + a2_e * b1_v - a1_v * b2_e - a1_e * b2_v
  let d10_e := a1_v * b0_e + a1_e * b0_v - a0_v * b1_e - a0_e * b1_v
  let m_sc : Fin 10 → Dual K5 := fun mi =>
    let (m2, m1, m0) : Dual K5 × Dual K5 × Dual K5 := match mi with
      | 0 => (a_s ^ 2, 2 * a_s * ξS_s, ξS_s ^ 2)
      | 1 => (a_s * b_s, a_s * ξQ_s + b_s * ξS_s, ξS_s * ξQ_s)
      | 2 => (b_s ^ 2, 2 * b_s * ξQ_s, ξQ_s ^ 2)
      | 3 => (Dual.C d_ab * a_s, Dual.C d_ab * ξS_s, 0)
      | 4 => (0, Dual.C d_ab * a_s, Dual.C d_ab * ξS_s)
      | 5 => (Dual.C d_ab * b_s, Dual.C d_ab * ξQ_s, 0)
      | 6 => (0, Dual.C d_ab * b_s, Dual.C d_ab * ξQ_s)
      | 7 => (Dual.C (d_ab ^ 2), 0, 0)
      | 8 => (0, Dual.C (d_ab ^ 2), 0)
      | 9 => (0, 0, Dual.C (d_ab ^ 2))
    Dual.C (1 / 16 : K5) * (m2 * d10_e - m1 * d20_e + m0 * d21_e)
  have hm_eq (mi : Fin 10) : m_sc mi = br2_0_m_sc S_K Q_K T_K mi := rfl
  have hnum_sc (mi : Fin 10) : Dual.C (d_ab ^ 6) * numM_12_of Dual.C mi a_du b_du = m_sc mi := by
    have hs : a_du + Dual.C inv_d * ξS_s = Dual.C inv_d * (a_s + ξS_s) := by rw [ha_du_eq]; ring
    have hq : b_du + Dual.C inv_d * ξQ_s = Dual.C inv_d * (b_s + ξQ_s) := by rw [hb_du_eq]; ring
    have hb_term : Dual.C (10 / 7 : K5) * b_du = Dual.C (inv_d ^ 2) * (Dual.C ((10 / 7 : K5) * d_ab) * b_s) := by
      have : (10 / 7 : K5) * inv_d = inv_d ^ 2 * ((10 / 7 : K5) * d_ab) := by
        linear_combination -((10 / 7 : K5) * inv_d) * hd_inv
      rw [hb_du_eq, ← mul_assoc, ← map_mul, this, map_mul, mul_assoc]
    have hd_pow6 : Dual.C (d_ab ^ 6) * (Dual.C inv_d ^ 2 * Dual.C (inv_d ^ 4)) = (1 : Dual K5) := by
      rw [← map_pow, ← map_mul, ← map_mul, ← map_one Dual.C]; congr 1
      rw [show d_ab ^ 6 * (inv_d ^ 2 * inv_d ^ 4) = (d_ab * inv_d) ^ 6 by ring, hd_inv, one_pow]
    have hd_pow5 : Dual.C (d_ab ^ 6) * (Dual.C inv_d * Dual.C (inv_d ^ 4)) = Dual.C d_ab := by
      rw [← map_mul, ← map_mul]; congr 1
      rw [show d_ab ^ 6 * (inv_d * inv_d ^ 4) = d_ab * (d_ab * inv_d) ^ 5 by ring, hd_inv, one_pow, mul_one]
    have hd_pow4 : Dual.C (d_ab ^ 6) * Dual.C (inv_d ^ 4) = Dual.C (d_ab ^ 2) := by
      rw [← map_mul]; congr 1
      rw [show d_ab ^ 6 * inv_d ^ 4 = d_ab ^ 2 * (d_ab * inv_d) ^ 4 by ring, hd_inv, one_pow, mul_one]
    have hdet : ∀ (x y z w : Dual (Dual K5)) (xv xe yv ye zv ze wv we : Dual K5),
        x.val = Dual.C (inv_d ^ 2) * xv → x.eps = Dual.C (inv_d ^ 2) * xe →
        y.val = Dual.C (inv_d ^ 2) * yv → y.eps = Dual.C (inv_d ^ 2) * ye →
        z.val = Dual.C (inv_d ^ 2) * zv → z.eps = Dual.C (inv_d ^ 2) * ze →
        w.val = Dual.C (inv_d ^ 2) * wv → w.eps = Dual.C (inv_d ^ 2) * we →
        (x * y - z * w).eps = Dual.C (inv_d ^ 4) * (xv * ye + xe * yv - zv * we - ze * wv) := by
      intro x y z w xv xe yv ye zv ze wv we hxv hxe hyv hye hzv hze hwv hwe
      simp only [Dual.sub_eps, Dual.mul_eps, hxv, hxe, hyv, hye, hzv, hze, hwv, hwe]
      have hp : Dual.C (inv_d ^ 2) * Dual.C (inv_d ^ 2) = Dual.C (inv_d ^ 4) := by
        rw [← map_mul]; congr 1; ring
      linear_combination (xv * ye + xe * yv - zv * we - ze * wv) * hp
    have h10 : ((dHS_12_of Dual.C (a_du + Dual.C inv_d * ξS_s) (b_du + Dual.C inv_d * ξQ_s) -
        dHS_12_of Dual.C a_du b_du - dHS_12_of Dual.C (Dual.C inv_d * ξS_s) (Dual.C inv_d * ξQ_s)) *
        dHQ_12_of Dual.C (Dual.C inv_d * ξS_s) (Dual.C inv_d * ξQ_s) 1 -
        dHS_12_of Dual.C (Dual.C inv_d * ξS_s) (Dual.C inv_d * ξQ_s) *
        (dHQ_12_of Dual.C (a_du + Dual.C inv_d * ξS_s) (b_du + Dual.C inv_d * ξQ_s) 0 -
          dHQ_12_of Dual.C a_du b_du 0 - dHQ_12_of Dual.C (Dual.C inv_d * ξS_s) (Dual.C inv_d * ξQ_s) 0 +
          ⟨0, Dual.C (10 / 7 : K5) * b_du⟩)).eps = Dual.C (inv_d ^ 4) * d10_e := by
      refine hdet _ _ _ _ a1_v a1_e b0_v b0_e a0_v a0_e b1_v b1_e ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · rw [hs, hq]; simp only [ha_du_eq, hb_du_eq, Dual.sub_val, hdHS_v, a1_v, a2_v, a0_v]; ring
      · rw [hs, hq]; simp only [ha_du_eq, hb_du_eq, Dual.sub_eps, hdHS_e, a1_e, a2_e, a0_e]; ring
      · exact hdHQ_v _ _ _
      · exact hdHQ1_e _ _
      · exact hdHS_v _ _
      · exact hdHS_e _ _
      · rw [hs, hq]; simp only [ha_du_eq, hb_du_eq, Dual.add_val, Dual.sub_val, hdHQ_v, b1_v, b2_v, b0_v]; ring
      · rw [hs, hq, hb_term]; simp only [ha_du_eq, hb_du_eq, Dual.add_eps, Dual.sub_eps, hdHQ0_e, b1_e, b2_e]; ring
    have h20 : (dHS_12_of Dual.C a_du b_du *
        dHQ_12_of Dual.C (Dual.C inv_d * ξS_s) (Dual.C inv_d * ξQ_s) 1 -
        dHS_12_of Dual.C (Dual.C inv_d * ξS_s) (Dual.C inv_d * ξQ_s) *
        dHQ_12_of Dual.C a_du b_du 0).eps = Dual.C (inv_d ^ 4) * d20_e := by
      rw [ha_du_eq, hb_du_eq]
      refine hdet _ _ _ _ a2_v a2_e b0_v b0_e a0_v a0_e b2_v b2_e ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · exact hdHS_v _ _
      · exact hdHS_e _ _
      · exact hdHQ_v _ _ _
      · exact hdHQ1_e _ _
      · exact hdHS_v _ _
      · exact hdHS_e _ _
      · exact hdHQ_v _ _ _
      · exact hdHQ0_e _ _
    have h21 : (dHS_12_of Dual.C a_du b_du *
        (dHQ_12_of Dual.C (a_du + Dual.C inv_d * ξS_s) (b_du + Dual.C inv_d * ξQ_s) 0 -
          dHQ_12_of Dual.C a_du b_du 0 - dHQ_12_of Dual.C (Dual.C inv_d * ξS_s) (Dual.C inv_d * ξQ_s) 0 +
          ⟨0, Dual.C (10 / 7 : K5) * b_du⟩) -
        (dHS_12_of Dual.C (a_du + Dual.C inv_d * ξS_s) (b_du + Dual.C inv_d * ξQ_s) -
          dHS_12_of Dual.C a_du b_du - dHS_12_of Dual.C (Dual.C inv_d * ξS_s) (Dual.C inv_d * ξQ_s)) *
        dHQ_12_of Dual.C a_du b_du 0).eps = Dual.C (inv_d ^ 4) * d21_e := by
      refine hdet _ _ _ _ a2_v a2_e b1_v b1_e a1_v a1_e b2_v b2_e ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · rw [ha_du_eq, hb_du_eq]; exact hdHS_v _ _
      · rw [ha_du_eq, hb_du_eq]; exact hdHS_e _ _
      · rw [hs, hq]; simp only [ha_du_eq, hb_du_eq, Dual.add_val, Dual.sub_val, hdHQ_v, b1_v, b2_v, b0_v]; ring
      · rw [hs, hq, hb_term]; simp only [ha_du_eq, hb_du_eq, Dual.add_eps, Dual.sub_eps, hdHQ0_e, b1_e, b2_e]; ring
      · rw [hs, hq]; simp only [ha_du_eq, hb_du_eq, Dual.sub_val, hdHS_v, a1_v, a2_v, a0_v]; ring
      · rw [hs, hq]; simp only [ha_du_eq, hb_du_eq, Dual.sub_eps, hdHS_e, a1_e, a2_e, a0_e]; ring
      · rw [ha_du_eq, hb_du_eq]; exact hdHQ_v _ _ _
      · rw [ha_du_eq, hb_du_eq]; exact hdHQ0_e _ _
    clear_value a2_v a2_e a0_v a0_e a1_v a1_e b2_v b2_e b0_v b0_e b1_v b1_e d20_e d21_e d10_e
    have hbody (m2 m1 m0 : Dual K5) :
        Dual.C (d_ab ^ 6) * (Dual.C (1 / 16 : K5) *
          ((Dual.C inv_d ^ 2 * m2) * (Dual.C (inv_d ^ 4) * d10_e) -
           (Dual.C inv_d ^ 2 * m1) * (Dual.C (inv_d ^ 4) * d20_e) +
           (Dual.C inv_d ^ 2 * m0) * (Dual.C (inv_d ^ 4) * d21_e))) =
        Dual.C (1 / 16 : K5) * (m2 * d10_e - m1 * d20_e + m0 * d21_e) := by
      linear_combination (Dual.C (1 / 16 : K5) * (m2 * d10_e - m1 * d20_e + m0 * d21_e)) * hd_pow6
    have hbody1 (m2 m1 m0 : Dual K5) :
        Dual.C (d_ab ^ 6) * (Dual.C (1 / 16 : K5) *
          ((Dual.C inv_d * m2) * (Dual.C (inv_d ^ 4) * d10_e) -
           (Dual.C inv_d * m1) * (Dual.C (inv_d ^ 4) * d20_e) +
           (Dual.C inv_d * m0) * (Dual.C (inv_d ^ 4) * d21_e))) =
        Dual.C (1 / 16 : K5) * ((Dual.C d_ab * m2) * d10_e - (Dual.C d_ab * m1) * d20_e + (Dual.C d_ab * m0) * d21_e) := by
      linear_combination (Dual.C (1 / 16 : K5) * (m2 * d10_e - m1 * d20_e + m0 * d21_e)) * hd_pow5
    have hbody0 (m2 m1 m0 : Dual K5) :
        Dual.C (d_ab ^ 6) * (Dual.C (1 / 16 : K5) *
          (m2 * (Dual.C (inv_d ^ 4) * d10_e) -
           m1 * (Dual.C (inv_d ^ 4) * d20_e) +
           m0 * (Dual.C (inv_d ^ 4) * d21_e))) =
        Dual.C (1 / 16 : K5) * ((Dual.C (d_ab ^ 2) * m2) * d10_e - (Dual.C (d_ab ^ 2) * m1) * d20_e + (Dual.C (d_ab ^ 2) * m0) * d21_e) := by
      linear_combination (Dual.C (1 / 16 : K5) * (m2 * d10_e - m1 * d20_e + m0 * d21_e)) * hd_pow4
    dsimp only [numM_12_of, m_sc]
    rw [hξS_eq, hξQ_eq, h10, h20, h21]
    fin_cases mi
    · rw [show a_du ^ 2 * (Dual.C (inv_d ^ 4) * d10_e) - 2 * a_du * (Dual.C inv_d * ξS_s) * (Dual.C (inv_d ^ 4) * d20_e) +
            (Dual.C inv_d * ξS_s) ^ 2 * (Dual.C (inv_d ^ 4) * d21_e) =
            (Dual.C inv_d ^ 2 * a_s ^ 2) * (Dual.C (inv_d ^ 4) * d10_e) -
            (Dual.C inv_d ^ 2 * (2 * a_s * ξS_s)) * (Dual.C (inv_d ^ 4) * d20_e) +
            (Dual.C inv_d ^ 2 * ξS_s ^ 2) * (Dual.C (inv_d ^ 4) * d21_e) by rw [ha_du_eq]; ring]
      exact hbody _ _ _
    · rw [show (a_du * b_du) * (Dual.C (inv_d ^ 4) * d10_e) -
            (a_du * (Dual.C inv_d * ξQ_s) + b_du * (Dual.C inv_d * ξS_s)) * (Dual.C (inv_d ^ 4) * d20_e) +
            (Dual.C inv_d * ξS_s * (Dual.C inv_d * ξQ_s)) * (Dual.C (inv_d ^ 4) * d21_e) =
            (Dual.C inv_d ^ 2 * (a_s * b_s)) * (Dual.C (inv_d ^ 4) * d10_e) -
            (Dual.C inv_d ^ 2 * (a_s * ξQ_s + b_s * ξS_s)) * (Dual.C (inv_d ^ 4) * d20_e) +
            (Dual.C inv_d ^ 2 * (ξS_s * ξQ_s)) * (Dual.C (inv_d ^ 4) * d21_e) by rw [ha_du_eq, hb_du_eq]; ring]
      exact hbody _ _ _
    · rw [show b_du ^ 2 * (Dual.C (inv_d ^ 4) * d10_e) - 2 * b_du * (Dual.C inv_d * ξQ_s) * (Dual.C (inv_d ^ 4) * d20_e) +
            (Dual.C inv_d * ξQ_s) ^ 2 * (Dual.C (inv_d ^ 4) * d21_e) =
            (Dual.C inv_d ^ 2 * b_s ^ 2) * (Dual.C (inv_d ^ 4) * d10_e) -
            (Dual.C inv_d ^ 2 * (2 * b_s * ξQ_s)) * (Dual.C (inv_d ^ 4) * d20_e) +
            (Dual.C inv_d ^ 2 * ξQ_s ^ 2) * (Dual.C (inv_d ^ 4) * d21_e) by rw [hb_du_eq]; ring]
      exact hbody _ _ _
    · simpa only [ha_du_eq, mul_zero, zero_mul] using hbody1 a_s ξS_s 0
    · simpa only [ha_du_eq, mul_zero, zero_mul] using hbody1 0 a_s ξS_s
    · simpa only [hb_du_eq, mul_zero, zero_mul] using hbody1 b_s ξQ_s 0
    · simpa only [hb_du_eq, mul_zero, zero_mul] using hbody1 0 b_s ξQ_s
    · simpa only [mul_one, mul_zero, zero_mul] using hbody0 1 0 0
    · simpa only [mul_one, mul_zero, zero_mul] using hbody0 0 1 0
    · simpa only [mul_one, mul_zero, zero_mul] using hbody0 0 0 1
  have hpoly : Dual.C (d_ab ^ 6) * A0U_12_of Dual.C a_du b_du =
      Dual.C (d_ab ^ 3) * ⟨(8248380 / 51331077 : K5) * (5 * S_K - 3 * Q_K) * S_K ^ 3 * A ^ 2,
        -(2 / 51331077 : K5) * B * S_K ^ 2 * A ^ 2 * Q_quad⟩ := by
    have hlhs : Dual.C (d_ab ^ 6) * A0U_12_of Dual.C a_du b_du =
        Dual.C (-(19708 / 1257375 : K5)) * (5 * m_sc 0 - 9 * m_sc 1) +
        Dual.C (1472 / 1257375 : K5) * (5 * m_sc 1 - 9 * m_sc 2) -
        Dual.C (16 / 729 : K5) * (5 * m_sc 3 - 9 * m_sc 5) +
        Dual.C (188 / 2025 : K5) * (5 * m_sc 4 - 9 * m_sc 6) := by
      simp only [A0U_12_of, ← hnum_sc]; ring
    rw [hlhs, hm_eq 0, hm_eq 1, hm_eq 2, hm_eq 3, hm_eq 4, hm_eq 5, hm_eq 6]
    exact br2_0_A0U_scaled_poly S_K Q_K T_K
  have hmul_eq : Dual.C (d_ab ^ 3) * (Dual.C (d_ab ^ 3) * A0U_12_of Dual.C a_du b_du) =
      Dual.C (d_ab ^ 3) * ⟨(8248380 / 51331077 : K5) * (5 * S_K - 3 * Q_K) * S_K ^ 3 * A ^ 2,
        -(2 / 51331077 : K5) * B * S_K ^ 2 * A ^ 2 * Q_quad⟩ := by
    rw [← mul_assoc, ← map_mul, show d_ab ^ 3 * d_ab ^ 3 = d_ab ^ 6 by ring, hpoly]
  ext
  · apply mul_left_cancel₀ (pow_ne_zero 3 hd_ab_ne)
    have h := congrArg Dual.val hmul_eq
    simp only [Dual.mul_val, Dual.C_val] at h
    exact h
  · apply mul_left_cancel₀ (pow_ne_zero 3 hd_ab_ne)
    have h := congrArg Dual.eps hmul_eq
    simp only [Dual.mul_eps, Dual.mul_val, Dual.C_val, Dual.C_eps, zero_mul, add_zero] at h ⊢
    exact h

private lemma br2_0_q1_biv_eval (w0 : K5) :
    let A := 5 * S_K - 9 * Q_K
    let B := T_K - 3
    let q1_c := fun k : Fin 3 =>
      9 * w0 * (H0_of S_K Q_K T_K * A1_of S_K Q_K 0 1 *
          (QY_num S_K Q_K T_K x_K y_K 0 1 k - QY_num S_K Q_K T_K x_K y_K 0 0 k) +
        (H0_of S_K Q_K T_K * dA1_fn k S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn k S_K Q_K T_K) *
          EB_of S_K Q_K T_K x_K y_K 0 1)
    w0 * S_K * A ^ 2 * evalBivK5 q1_v_35721_biv =
      35721 * (q1_c 0 * (6 * S_K ^ 2) + q1_c 1 * (6 * S_K * Q_K) + q1_c 2 * (6 * S_K * B)) ∧
    w0 * S_K * A ^ 2 * B * evalBivK5 q1_e_35721_divB5_biv =
      35721 * (q1_c 0 * (6 * S_K * B) + q1_c 1 * ((5 * S_K - 3 * Q_K) * B)) := by
  intro A B q1_c
  have hH0_ev : ringEval vK5 H0_int_e = 7 * H0_of S_K Q_K T_K := by
    simp only [H0_int_e, ringEval, eS, eQ, eT, vK5, H0_of, Int.cast_neg, Int.cast_ofNat]; ring
  have hcA1_ev (k : Fin 3) : A * ringEval vK5 (cA1_21_div_A5_e k) =
      189 * (H0_of S_K Q_K T_K * dA1_fn k S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn k S_K Q_K T_K) := by
    fin_cases k <;>
      (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
        cA1_21_div_A5_e, ringEval, hH0_ev, ringEval_dH0_7, eA5, eS, eQ, vK5,
        A1_of, dA1_fn, Int.cast_neg, Int.cast_ofNat, A]; ring)
  have hA1_01 : A1_of S_K Q_K 0 1 = (25 / 27 : K5) * S_K * A ^ 2 := by
    simp only [A1_of, A]; ring
  have hEB : S_K * A * evalBivK5 EB_V0_9_div_SA5_biv = 9 * EB_of S_K Q_K T_K x_K y_K 0 1 :=
    evalBivK5_EB_V0
  constructor
  · simp only [q1_v_35721_biv, evalBivK5_bivAdd, evalBivK5_scale, evalBivK5_QY_V0_1701,
      ringEval, hH0_ev, eS, eQ, eB5, eT, vK5, Int.cast_ofNat, pow_zero, mul_one]
    have he1 : w0 * S_K * A ^ 2 *
        (189 * (ringEval vK5 (cA1_21_div_A5_e 0) * (6 * S_K ^ 2) +
          ringEval vK5 (cA1_21_div_A5_e 1) * (6 * (S_K * Q_K)) +
          ringEval vK5 (cA1_21_div_A5_e 2) * (6 * (S_K * (T_K - 3)))) *
          evalBivK5 EB_V0_9_div_SA5_biv) =
        189 * w0 * (A * ringEval vK5 (cA1_21_div_A5_e 0) * (6 * S_K ^ 2) +
          A * ringEval vK5 (cA1_21_div_A5_e 1) * (6 * S_K * Q_K) +
          A * ringEval vK5 (cA1_21_div_A5_e 2) * (6 * S_K * B)) *
        (S_K * A * evalBivK5 EB_V0_9_div_SA5_biv) := by dsimp only [B]; ring
    rw [mul_add, he1, hcA1_ev 0, hcA1_ev 1, hcA1_ev 2, hEB]
    simp only [q1_c, hA1_01, B]; ring
  · simp only [q1_e_35721_divB5_biv, evalBivK5_bivAdd, evalBivK5_scale, evalBivK5_QY_V0_1701,
      ringEval, hH0_ev, eS, eQ, e5S3Q, vK5, Int.cast_ofNat, pow_zero, mul_one]
    have he1 : w0 * S_K * A ^ 2 * B *
        (189 * (ringEval vK5 (cA1_21_div_A5_e 0) * (6 * S_K) +
          ringEval vK5 (cA1_21_div_A5_e 1) * (5 * S_K - 3 * Q_K)) *
          evalBivK5 EB_V0_9_div_SA5_biv) =
        189 * w0 * B * (A * ringEval vK5 (cA1_21_div_A5_e 0) * (6 * S_K) +
          A * ringEval vK5 (cA1_21_div_A5_e 1) * (5 * S_K - 3 * Q_K)) *
        (S_K * A * evalBivK5 EB_V0_9_div_SA5_biv) := by ring
    rw [mul_add, he1, hcA1_ev 0, hcA1_ev 1, hEB]
    simp only [q1_c, hA1_01]; ring

private lemma br2_0_final_cancel
    {w0 P_val P_eps P1_0 P0_0 : K5}
    (hw0_eq : w0 = -(25 / 4 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 2 / (T_K - 3) ^ 3)
    (hw0_ne : w0 ≠ 0)
    (hden_ne : 81 * k5Params.Av0 * w0 * ((15625 / 59049 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 4) ^ 3 *
      (((-59604644775390625 / 4941387170271576 : K5) * S_K ^ 8 * (-(5 * S_K - 9 * Q_K)) ^ 17 / (T_K - 3) ^ 12) ^ 2 /
        ((15625 / 59049 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 4)) ≠ 0)
    (hq2_ne : (15625 / 59049 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 4 ≠ 0)
    (hcd_eq : ((-59604644775390625 / 103769130575703096 : K5) *
        (225 * S_K - 45 * Q_K + 77 * T_K - 189) * S_K ^ 8 * (-(5 * S_K - 9 * Q_K)) ^ 17 / (T_K - 3) ^ 12) +
      (w0 * S_K / (T_K - 3)) *
        ((-2384185791015625 / 25942282643925774 : K5) *
          (225 * S_K - 45 * Q_K + 77 * T_K - 210) * S_K ^ 6 * (-(5 * S_K - 9 * Q_K)) ^ 15 / (T_K - 3) ^ 8) =
      (-59604644775390625 / 4941387170271576 : K5) * S_K ^ 8 * (-(5 * S_K - 9 * Q_K)) ^ 17 / (T_K - 3) ^ 12)
    (hP_val : ((15625 / 59049 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 4) ^ 3 * P_val =
      P1_0 * (w0 * S_K / (T_K - 3)) + P0_0)
    (hP_eps : ((15625 / 59049 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 4) ^ 3 * P_eps = P1_0 * w0)
    (hPg0_Z2_prod : Dual.C (35721 * (6 * S_K * (T_K - 3)) ^ 4) * ⟨P_val, P_eps⟩ =
      Dual.C (w0 ^ 2) *
        ⟨(8248380 / 51331077 : K5) * (5 * S_K - 3 * Q_K) * S_K ^ 3 * (5 * S_K - 9 * Q_K) ^ 2,
         -(2 / 51331077 : K5) * (T_K - 3) * S_K ^ 2 * (5 * S_K - 9 * Q_K) ^ 2 *
           (11943020 * S_K ^ 2 - 876486 * S_K * Q_K + 8382500 * S_K * T_K +
            5029500 * Q_K * T_K - 14837025 * S_K - 33647355 * Q_K)⟩ *
        ⟨w0 * S_K * (5 * S_K - 9 * Q_K) ^ 2 * evalBivK5 q1_v_35721_biv,
         w0 * S_K * (5 * S_K - 9 * Q_K) ^ 2 * (T_K - 3) * evalBivK5 q1_e_35721_divB5_biv⟩) :
    -(P1_0 * ((-59604644775390625 / 103769130575703096 : K5) *
        (225 * S_K - 45 * Q_K + 77 * T_K - 189) * S_K ^ 8 * (-(5 * S_K - 9 * Q_K)) ^ 17 / (T_K - 3) ^ 12) -
      P0_0 * ((-2384185791015625 / 25942282643925774 : K5) *
        (225 * S_K - 45 * Q_K + 77 * T_K - 210) * S_K ^ 6 * (-(5 * S_K - 9 * Q_K)) ^ 15 / (T_K - 3) ^ 8)) *
      w0 * ((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)) ^ 4 /
      (81 * k5Params.Av0 * w0 * ((15625 / 59049 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 4) ^ 3 *
        (((-59604644775390625 / 4941387170271576 : K5) * S_K ^ 8 * (-(5 * S_K - 9 * Q_K)) ^ 17 / (T_K - 3) ^ 12) ^ 2 /
          ((15625 / 59049 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 4))) =
    toK5_RU := by
  have hS := S_K_ne_zero; have hB := T_K_sub_3_ne
  have h21_ne : (21 : K5) ≠ 0 := by exact_mod_cast (by decide : (21 : ℕ) ≠ 0)
  have h6_ne : (6 : K5) ≠ 0 := by exact_mod_cast (by decide : (6 : ℕ) ≠ 0)
  have h35_ne : (35721 : K5) ≠ 0 := by exact_mod_cast (by decide : (35721 : ℕ) ≠ 0)
  have hL_U0_eq : ringEval vK5 L_U0_e = 225 * S_K - 45 * Q_K + 77 * T_K - 210 := by
    simp only [L_U0_e, ringEval, eS, eQ, eT, vK5, Int.cast_neg, Int.cast_ofNat]; ring
  have hQ_quad_eq : ringEval vK5 Q_quad_U0_e =
      11943020 * S_K ^ 2 - 876486 * S_K * Q_K + 8382500 * S_K * T_K +
        5029500 * Q_K * T_K - 14837025 * S_K - 33647355 * Q_K := by
    simp only [Q_quad_U0_e, ringEval, eS, eQ, eT, vK5, Int.cast_neg, Int.cast_ofNat]; ring
  have hU0_id : 21 * S_K * (173215980 * S_K * (5 * S_K - 3 * Q_K) * evalBivK5 q1_e_35721_divB5_biv -
      42 * (11943020 * S_K ^ 2 - 876486 * S_K * Q_K + 8382500 * S_K * T_K +
          5029500 * Q_K * T_K - 14837025 * S_K - 33647355 * Q_K) * evalBivK5 q1_v_35721_biv +
      8248380 * (5 * S_K - 3 * Q_K) * (225 * S_K - 45 * Q_K + 77 * T_K - 210) *
        evalBivK5 q1_v_35721_biv) =
      11907000 * S_K ^ 3 * (5 * S_K - 9 * Q_K) * ((D_RU : K5) * toK5_RU) := by
    have h := U0_biv_identity
    rw [LHS_U0_biv, RHS_U0_biv, evalBivK5_bivReduceX2, evalBivK5_bivAdd, evalBivK5_bivAdd,
      evalBivK5_scale, evalBivK5_scale, evalBivK5_scale, evalBivK5_scale, evalBivK5_RU] at h
    simp only [ringEval, hL_U0_eq, hQ_quad_eq, eS, e5S3Q, eA5, eQ, vK5,
      Int.cast_neg, Int.cast_ofNat, pow_zero, mul_one] at h
    linear_combination h
  have hk1 : (21 * (-(25 / 4 : K5)) * (-2384185791015625 / 25942282643925774) : K5) =
      -(-59604644775390625 / 4941387170271576) := by
    have hq : (21 * (-(25 / 4 : ℚ)) * (-2384185791015625 / 25942282643925774) : ℚ) =
        -(-59604644775390625 / 4941387170271576) := by norm_num
    simpa only [map_mul, map_div₀, map_neg, map_ofNat] using congrArg (Rat.castHom K5) hq
  have hk2 : (-(15625 / 59049 : K5) ^ 3 * (50 / 27) ^ 4 * (1 / (21 * 51331077)) *
      11907000 * (D_RU : K5) * (-(25 / 4)) ^ 4 : K5) =
      21 * 35721 * 81 * (-(4 / 243)) * 6 ^ 4 * (15625 / 59049) ^ 2 *
      (-(-59604644775390625 / 4941387170271576)) * (-(25 / 4)) ^ 2 := by
    have hq : (-(15625 / 59049 : ℚ) ^ 3 * (50 / 27) ^ 4 * (1 / (21 * 51331077)) *
        11907000 * (11644549875 : ℚ) * (-(25 / 4)) ^ 4 : ℚ) =
        21 * 35721 * 81 * (-(4 / 243)) * 6 ^ 4 * (15625 / 59049) ^ 2 *
        (-(-59604644775390625 / 4941387170271576)) * (-(25 / 4)) ^ 2 := by norm_num
    have hDRU : (D_RU : K5) = (11644549875 : K5) := by unfold D_RU; push_cast; rfl
    rw [hDRU]
    simpa only [map_mul, map_div₀, map_neg, map_pow, map_one, map_ofNat] using congrArg (Rat.castHom K5) hq
  have hk3 : (1 / (21 * 51331077) : K5) * 173215980 = 8248380 / 51331077 ∧
      (1 / (21 * 51331077) : K5) * 42 = 2 / 51331077 ∧
      (1 / (21 * 51331077) : K5) * 8248380 * 21 = 8248380 / 51331077 := by
    have hq : (1 / (21 * 51331077) : ℚ) * 173215980 = 8248380 / 51331077 ∧
        (1 / (21 * 51331077) : ℚ) * 42 = 2 / 51331077 ∧
        (1 / (21 * 51331077) : ℚ) * 8248380 * 21 = 8248380 / 51331077 := by norm_num
    refine ⟨?_, ?_, ?_⟩
    · simpa only [map_mul, map_div₀, map_one, map_ofNat] using congrArg (Rat.castHom K5) hq.1
    · simpa only [map_mul, map_div₀, map_one, map_ofNat] using congrArg (Rat.castHom K5) hq.2.1
    · simpa only [map_mul, map_div₀, map_one, map_ofNat] using congrArg (Rat.castHom K5) hq.2.2
  have hAv0_eq : k5Params.Av0 = -(4 / 243 : K5) * (T_K - 3) ^ 3 := by
    simp only [CoverParams.Av0, CoverParams.inv243, k5Params_inv3, k5Params_T]; ring
  rw [hAv0_eq] at hden_ne ⊢
  generalize evalBivK5 q1_v_35721_biv = q1_v at hPg0_Z2_prod hU0_id
  generalize evalBivK5 q1_e_35721_divB5_biv = q1_e at hPg0_Z2_prod hU0_id
  generalize toK5_RU = RU_val at hU0_id ⊢
  generalize (-(25 / 4 : K5)) = r25 at hw0_eq hk1 hk2
  generalize (15625 / 59049 : K5) = r15 at hden_ne hq2_ne hP_val hP_eps hk2 ⊢
  generalize (-59604644775390625 / 4941387170271576 : K5) = rcd at hden_ne hcd_eq hk1 hk2 ⊢
  generalize (-59604644775390625 / 103769130575703096 : K5) = rd0 at hcd_eq ⊢
  generalize (-2384185791015625 / 25942282643925774 : K5) = rd1 at hcd_eq hk1 ⊢
  generalize (50 / 27 : K5) = r50 at hk2 ⊢
  generalize (-(4 / 243 : K5)) = r4 at hden_ne hk2 ⊢
  generalize (8248380 / 51331077 : K5) = r82 at hPg0_Z2_prod hk3
  generalize (2 / 51331077 : K5) = r2 at hPg0_Z2_prod hk3
  generalize (1 / (21 * 51331077) : K5) = rinv at hk2 hk3
  generalize (173215980 : K5) = r173 at hU0_id hk3
  generalize (8248380 : K5) = r82i at hU0_id hk3
  generalize (11907000 : K5) = r119 at hU0_id hk2
  generalize (D_RU : K5) = rDRU at hU0_id hk2
  generalize (35721 : K5) = r35 at h35_ne hPg0_Z2_prod hk2
  generalize (11943020 * S_K ^ 2 - 876486 * S_K * Q_K + 8382500 * S_K * T_K +
      5029500 * Q_K * T_K - 14837025 * S_K - 33647355 * Q_K : K5) = Qq at hPg0_Z2_prod hU0_id
  generalize (225 * S_K - 45 * Q_K + 77 * T_K - 210 : K5) = L210 at hcd_eq hU0_id ⊢
  generalize (225 * S_K - 45 * Q_K + 77 * T_K - 189 : K5) = L189 at hcd_eq ⊢
  generalize (5 * S_K - 9 * Q_K : K5) = A at hw0_eq hden_ne hq2_ne hcd_eq hP_val hP_eps hPg0_Z2_prod hU0_id ⊢
  generalize (5 * S_K - 3 * Q_K : K5) = A3 at hPg0_Z2_prod hU0_id
  generalize (T_K - 3 : K5) = B at hB hw0_eq hden_ne hcd_eq hP_val hPg0_Z2_prod ⊢
  have hB3 : B ^ 3 ≠ 0 := pow_ne_zero 3 hB
  have hB8 : B ^ 8 ≠ 0 := pow_ne_zero 8 hB
  have hB12 : B ^ 12 ≠ 0 := pow_ne_zero 12 hB
  have hw0_B3 : w0 * B ^ 3 = r25 * S_K * A ^ 2 := by rw [hw0_eq, div_mul_cancel₀ _ hB3]
  have hd_ab_ne : 6 * S_K * B ≠ 0 := mul_ne_zero (mul_ne_zero h6_ne hS) hB
  have hPv : r35 * (6 * S_K * B) ^ 4 * P_val = w0 ^ 3 * r82 * A3 * S_K ^ 4 * A ^ 4 * q1_v := by
    have h := congrArg Dual.val hPg0_Z2_prod
    simp only [Dual.mul_val, Dual.C_val] at h; rw [h]; ring
  have hPe : r35 * (6 * S_K * B) ^ 4 * P_eps =
      w0 ^ 3 * S_K ^ 3 * A ^ 4 * B * (r82 * S_K * A3 * q1_e - r2 * Qq * q1_v) := by
    have h := congrArg Dual.eps hPg0_Z2_prod
    simp only [Dual.mul_val, Dual.mul_eps, Dual.C_val, Dual.C_eps, zero_mul, add_zero] at h; rw [h]; ring
  set cd : K5 := rcd * S_K ^ 8 * (-A) ^ 17 / B ^ 12
  set d1 : K5 := rd1 * L210 * S_K ^ 6 * (-A) ^ 15 / B ^ 8
  set d0 : K5 := rd0 * L189 * S_K ^ 8 * (-A) ^ 17 / B ^ 12
  set q2 : K5 := r15 * S_K * A ^ 4
  have hcd_B12 : cd * B ^ 12 = rcd * S_K ^ 8 * (-A) ^ 17 := by dsimp only [cd]; rw [div_mul_cancel₀ _ hB12]
  have hw0_d1 : 21 * S_K * (w0 * d1) = -L210 * B * cd := by
    apply mul_left_cancel₀ hB12
    have h1 : B ^ 12 * (21 * S_K * (w0 * d1)) = 21 * S_K * B * (w0 * B ^ 3) * (d1 * B ^ 8) := by ring
    have hd1_B8 : d1 * B ^ 8 = rd1 * L210 * S_K ^ 6 * (-A) ^ 15 := by dsimp only [d1]; rw [div_mul_cancel₀ _ hB8]
    rw [h1, hw0_B3, hd1_B8, show B ^ 12 * (-L210 * B * cd) = -L210 * B * (cd * B ^ 12) by ring, hcd_B12]
    linear_combination (L210 * S_K ^ 8 * A ^ 2 * (-A) ^ 15 * B) * hk1
  have hinner : 21 * S_K * (r35 * (6 * S_K * B) ^ 4 * P_eps) + L210 * B * (r35 * (6 * S_K * B) ^ 4 * P_val) =
      w0 ^ 3 * rinv * S_K ^ 3 * A ^ 4 * B * (r119 * S_K ^ 3 * A * (rDRU * RU_val)) := by
    rw [hPe, hPv, ← hU0_id]
    linear_combination -(w0 ^ 3 * S_K ^ 5 * A ^ 4 * B * A3 * q1_e * 21) * hk3.1 +
      (w0 ^ 3 * S_K ^ 4 * A ^ 4 * B * Qq * q1_v * 21) * hk3.2.1 -
      (w0 ^ 3 * S_K ^ 4 * A ^ 4 * B * L210 * A3 * q1_v) * hk3.2.2
  rw [div_eq_iff hden_ne]
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (mul_ne_zero h21_ne hS) (mul_ne_zero h35_ne (pow_ne_zero 4 hd_ab_ne))) hw0_ne)
  have hcomb : 21 * S_K * (r35 * (6 * S_K * B) ^ 4) * w0 * (-(P1_0 * d0 - P0_0 * d1) * w0 * (r50 * S_K * A) ^ 4) =
      -q2 ^ 3 * (r50 * S_K * A) ^ 4 * cd * w0 *
        (21 * S_K * (r35 * (6 * S_K * B) ^ 4 * P_eps) + L210 * B * (r35 * (6 * S_K * B) ^ 4 * P_val)) := by
    have h1 : w0 * (P1_0 * d0 - P0_0 * d1) = (P1_0 * w0) * cd - (P1_0 * (w0 * S_K / B) + P0_0) * (w0 * d1) := by
      rw [← hcd_eq]; ring
    rw [show 21 * S_K * (r35 * (6 * S_K * B) ^ 4) * w0 * (-(P1_0 * d0 - P0_0 * d1) * w0 * (r50 * S_K * A) ^ 4) =
          -(r35 * (6 * S_K * B) ^ 4) * (r50 * S_K * A) ^ 4 * w0 * (21 * S_K * (w0 * (P1_0 * d0 - P0_0 * d1))) by ring,
        h1, ← hP_eps, ← hP_val]
    linear_combination (r35 * (6 * S_K * B) ^ 4 * (r50 * S_K * A) ^ 4 * w0 * q2 ^ 3 * P_val) * hw0_d1
  rw [hcomb, hinner]
  apply mul_left_cancel₀ (mul_ne_zero hB12 hB12)
  have hq2_div : q2 ^ 3 * (cd ^ 2 / q2) = q2 ^ 2 * cd ^ 2 := by
    rw [show q2 ^ 3 * (cd ^ 2 / q2) = q2 ^ 2 * (cd ^ 2 / q2 * q2) by ring, div_mul_cancel₀ _ hq2_ne]
  have hL : B ^ 12 * B ^ 12 * (-q2 ^ 3 * (r50 * S_K * A) ^ 4 * cd * w0 *
      (w0 ^ 3 * rinv * S_K ^ 3 * A ^ 4 * B * (r119 * S_K ^ 3 * A * (rDRU * RU_val)))) =
      (-r15 ^ 3 * r50 ^ 4 * rinv * r119 * rDRU * r25 ^ 4) * (B ^ 12 * B * S_K ^ 17 * A ^ 29 * cd * RU_val) := by
    rw [show B ^ 12 * B ^ 12 * (-q2 ^ 3 * (r50 * S_K * A) ^ 4 * cd * w0 *
          (w0 ^ 3 * rinv * S_K ^ 3 * A ^ 4 * B * (r119 * S_K ^ 3 * A * (rDRU * RU_val)))) =
        -q2 ^ 3 * (r50 * S_K * A) ^ 4 * rinv * r119 * rDRU * B ^ 12 * B * S_K ^ 6 * A ^ 5 * cd * (w0 * B ^ 3) ^ 4 * RU_val by ring,
        hw0_B3]; dsimp only [q2]; ring
  have hR : B ^ 12 * B ^ 12 * (21 * S_K * (r35 * (6 * S_K * B) ^ 4) * w0 *
      (RU_val * (81 * (r4 * B ^ 3) * w0 * q2 ^ 3 * (cd ^ 2 / q2)))) =
      (21 * r35 * 81 * r4 * 6 ^ 4 * r15 ^ 2 * (-rcd) * r25 ^ 2) * (B ^ 12 * B * S_K ^ 17 * A ^ 29 * cd * RU_val) := by
    rw [mul_assoc _ (q2 ^ 3), hq2_div,
        show B ^ 12 * B ^ 12 * (21 * S_K * (r35 * (6 * S_K * B) ^ 4) * w0 *
          (RU_val * (81 * (r4 * B ^ 3) * w0 * (q2 ^ 2 * cd ^ 2)))) =
        21 * r35 * 81 * r4 * 6 ^ 4 * S_K ^ 5 * B ^ 13 * q2 ^ 2 * (w0 * B ^ 3) ^ 2 * cd * (cd * B ^ 12) * RU_val by ring,
        hw0_B3, hcd_B12]; dsimp only [q2]; ring
  rw [hL, hR, hk2]

lemma br2_0_eta_AC_coeff_neg_one : (br2_0 eta_AC).coeff (-1) = toK5_RU := by
  have hbr := branchHom_eta_AC ψ0 ψ0_C W2_0 W2_0_eq_ψ0
  simp only [ψ0_X] at hbr
  have hfP : ψ0.comp toRat = evalT := RingHom.ext ψ0_toRat
  simp only [hfP] at hbr
  change br2_0 eta_AC = _ at hbr
  rw [hbr]
  set U := HahnSeries.single (1 : ℤ) (1 : K5)
  set V := W2_0 / U
  set ca := evalT k5Params.ca_h
  set cb := evalT k5Params.cb_h
  set c0W := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.c0W)
  set d2_2 := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d2_2)
  set d2_1 := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d2_1)
  set d2_0 := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d2_0)
  set d1 := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d1_z)
  set d0 := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d0_z)
  set res := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.res_z)
  set g : LaurentSeries K5 → LaurentSeries K5 := fun z =>
    P18_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K)
      (z / W2_0) (-(ca * z + c0W) / (W2_0 * cb)) U V
  set p := interp4 g
  set P1 := remDeg4_P1 d2_2 d2_1 d2_0 p.1 p.2.1 p.2.2.1 p.2.2.2.1
  set P0 := remDeg4_P0 d2_2 d2_1 d2_0 p.1 p.2.1 p.2.2.1 p.2.2.2.2
  have hS := S_K_ne_zero; have hA := fiveS_sub_9Q_ne; have hB := T_K_sub_3_ne
  set A := 5 * S_K - 9 * Q_K
  set B := T_K - 3
  set w0 : K5 := -(k5Params.Bv0 * k5Params.Av0_inv)
  have hw0_eq : w0 = -(25 / 4 : K5) * S_K * A ^ 2 / B ^ 3 := by
    simp only [w0, CoverParams.Bv0, CoverParams.Av0_inv, CoverParams.inv4, CoverParams.inv243,
      k5Params_inv2, k5Params_inv3, k5Params_invT3, k5Params_S, k5Params_Q, A, B]
    field_simp [hB]; ring
  have hw0_ne : w0 ≠ 0 := by
    rw [hw0_eq]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (div_ne_zero
      (by exact_mod_cast (by decide : (25 : ℕ) ≠ 0))
      (by exact_mod_cast (by decide : (4 : ℕ) ≠ 0)))) hS) (pow_ne_zero 2 hA)) (pow_ne_zero 3 hB)
  have hw0_L : ValLead 0 W2_0 w0 := W2_0_valDual.toValLead
  have hU_L : ValLead 1 U 1 := ValLead.of_single 1 1
  have hV_L : ValLead (-1) V w0 := (hw0_L.div_of_ne hU_L one_ne_zero).eq_k (by omega) |>.eq_c (div_one w0)
  set ca0 : K5 := -(25 / 81 : K5) * A * (5 * S_K - 3 * Q_K)
  set cb0 : K5 := (50 / 27 : K5) * S_K * A
  set c0W0 : K5 := k5Params.c0_V2 * w0 ^ 2
  have hca_L : ValLead 0 ca ca0 := (ValLead.of_evalT _).eq_c (by
    simp only [CoverParams.ca_h, quadU_coeff_zero, CoverParams.inv81, CoverParams.inv27, k5Params_inv3, k5Params_S, k5Params_Q, ca0, A]; ring)
  have hcb_L : ValLead 0 cb cb0 := (ValLead.of_evalT _).eq_c (by
    simp only [CoverParams.cb_h, quadU_coeff_zero, CoverParams.inv27, CoverParams.inv9, k5Params_inv3, k5Params_S, k5Params_Q, cb0, A]; ring)
  have hcb0_ne : cb0 ≠ 0 := mul_ne_zero (mul_ne_zero (div_ne_zero
    (by exact_mod_cast (by decide : (50 : ℕ) ≠ 0))
    (by exact_mod_cast (by decide : (27 : ℕ) ≠ 0))) hS) hA
  have hc0W_L : ValLead 0 c0W c0W0 := (evalT_toUW_valDual_W2 _ _ _).toValLead.eq_c (by
    simp [Dual.C, Dual.pow_eq, c0W0, w0])
  set q2_0 : K5 := (15625 / 59049 : K5) * S_K * A ^ 4
  have hQ5_L : ValLead 0 (evalT k5Params.Q5_z) q2_0 := (ValLead.of_evalT _).eq_c (by
    simp only [Polynomial.coeff_zero_eq_eval_zero, CoverParams.Q5_z, CoverParams.q20, CoverParams.q11,
      CoverParams.q02, CoverParams.ca_h, CoverParams.cb_h, CoverParams.quadU,
      CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3, k5Params_S, k5Params_Q,
      eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X, q2_0, A]; ring)
  have hd2_2_L : ValLead 0 d2_2 q2_0 := by
    simpa only [d2_2, CoverParams.d2_2, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar] using hQ5_L
  set z2 : K5 := w0 * S_K / B
  have hd2_1_L : ValLead 0 d2_1 (-2 * q2_0 * z2) := by
    simp only [d2_1, CoverParams.d2_1, PairAlg.map_smul, PairAlg.evalAt_smul]
    have hsc : ValLead 0 (evalT (-k5Params.q11 * k5Params.cb_h + 2 * k5Params.q02 * k5Params.ca_h))
        (-(1250 / 729 : K5) * S_K * A ^ 2) := (ValLead.of_evalT _).eq_c (by
      simp only [Polynomial.coeff_zero_eq_eval_zero, CoverParams.q11, CoverParams.q02,
        CoverParams.ca_h, CoverParams.cb_h, CoverParams.quadU,
        CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3, k5Params_S, k5Params_Q,
        eval_add, eval_neg, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat, A]; ring)
    exact (hsc.mul hc0W_L).eq_k (by omega) |>.eq_c (by
      simp only [c0W0, hw0_eq, z2, q2_0, CoverParams.c0_V2, CoverParams.inv81, k5Params_inv3, k5Params_T, A, B]
      field_simp [hB]; ring)
  have hd2_0_L : ValLead 0 d2_0 (q2_0 * z2 ^ 2) := by
    simp only [d2_0, CoverParams.d2_0, CoverParams.pmul, PairAlg.map_add, PairAlg.map_smul,
      PairAlg.map_mul, PairAlg.map_W, PairAlg.evalAt_add, PairAlg.evalAt_smul,
      PairAlg.evalAt_mul _ _ W2_0 W2_0_eq, PairAlg.evalAt_W, map_pow]
    have hq02 : ValLead 0 (evalT k5Params.q02) (-(25 / 3 : K5) * S_K) := (ValLead.of_evalT _).eq_c (by
      simp only [CoverParams.q02, quadU_coeff_zero, k5Params_inv3, k5Params_S]; ring)
    have hk2W_L : ValLead 0 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.k2W)) (k5Params.k2_V2 * w0 ^ 2) :=
      (evalT_toUW_valDual_W2 _ _ _).toValLead.eq_c (by simp [Dual.C, Dual.pow_eq, w0])
    exact (((hq02.mul (hc0W_L.mul hc0W_L)).eq_k (by omega)).add
      (((hcb_L.pow 2).mul (hw0_L.mul hk2W_L)).eq_k (by omega))).eq_c (by
      simp only [c0W0, cb0, hw0_eq, z2, q2_0, CoverParams.c0_V2, CoverParams.k2_V2,
        CoverParams.inv81, k5Params_inv3, k5Params_T, A, B]
      field_simp [hB]; ring)
  obtain ⟨hd1_L, hd0_L, hcd_eq, hres_L, hcd_ne, hq2_ne⟩ := W2_0_d1_d0_res
  have h2W_L : ValLead 0 (2 * W2_0 + evalT k5Params.bW) w0 := by
    have hbW0 : ValLead 0 (evalT k5Params.bW) (-w0) := (ValLead.of_evalT _).eq_c (by
      simp only [CoverParams.bW, CoverParams.Bv, coeff_C_mul, quadU_coeff_zero, w0]; ring)
    exact ((((ValLead.of_nat 2).mul hw0_L).eq_k (by omega)).add hbW0).eq_c (by simp; ring)
  set cd : K5 := (-59604644775390625 / 4941387170271576 : K5) * S_K ^ 8 * (-A) ^ 17 / B ^ 12
  set d1_1 : K5 := (-2384185791015625 / 25942282643925774 : K5) *
    (225 * S_K - 45 * Q_K + 77 * T_K - 210) * S_K ^ 6 * (-A) ^ 15 / B ^ 8
  set d0_1 : K5 := (-59604644775390625 / 103769130575703096 : K5) *
    (225 * S_K - 45 * Q_K + 77 * T_K - 189) * S_K ^ 8 * (-A) ^ 17 / B ^ 12
  -- Denominator `ValLead 2`!
  have hden_L : ValLead 2
      (81 * HahnSeries.C k5Params.Av0 * (2 * W2_0 + evalT k5Params.bW) * evalT k5Params.Q5_z ^ 3 * res)
      (81 * k5Params.Av0 * w0 * q2_0 ^ 3 * (cd ^ 2 / q2_0)) :=
    (((((ValLead.of_nat 81).mul (ValLead.of_C k5Params.Av0)).mul h2W_L).mul (hQ5_L.pow 3)).mul hres_L).eq_k
      (by omega) |>.eq_c (by push_cast; rfl)
  have h81_ne : (81 : K5) ≠ 0 := by exact_mod_cast (by decide : (81 : ℕ) ≠ 0)
  have hden_ne : 81 * k5Params.Av0 * w0 * q2_0 ^ 3 * (cd ^ 2 / q2_0) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h81_ne k5Params_Av0_ne) hw0_ne)
      (pow_ne_zero 3 hq2_ne)) (div_ne_zero (pow_ne_zero 2 hcd_ne) hq2_ne)
  let q1_lead0 : K5 → K5 → K5 := fun a b =>
    let qY0 := 9 * ((QY_num S_K Q_K T_K x_K y_K 0 1 0 - QY_num S_K Q_K T_K x_K y_K 0 0 0) * a +
      (QY_num S_K Q_K T_K x_K y_K 0 1 1 - QY_num S_K Q_K T_K x_K y_K 0 0 1) * b +
      (QY_num S_K Q_K T_K x_K y_K 0 1 2 - QY_num S_K Q_K T_K x_K y_K 0 0 2))
    let cA0 := 9 * ((H0_of S_K Q_K T_K * dA1_fn 0 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 0 S_K Q_K T_K) * a +
      (H0_of S_K Q_K T_K * dA1_fn 1 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 1 S_K Q_K T_K) * b +
      (H0_of S_K Q_K T_K * dA1_fn 2 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 2 S_K Q_K T_K))
    w0 * (H0_of S_K Q_K T_K * A1_of S_K Q_K 0 1 * qY0 + cA0 * EB_of S_K Q_K T_K x_K y_K 0 1)
  let g0 : K5 → K5 := fun z =>
    let a := z / w0; let b := -(ca0 * z + c0W0) / (w0 * cb0)
    w0 ^ 2 * A0U_12_of (RingHom.id K5) a b * q1_lead0 a b
  have hg_L : ∀ z : K5, ValLead (-3) (g (HahnSeries.C z)) (g0 z) :=
    br2_0_g_lead hw0_eq hw0_ne hcb0_ne rfl rfl rfl hw0_L hU_L hV_L hca_L hcb_L hc0W_L
  -- Transport `ValLead (-3)` across `interp4` and `remDeg4_P1 / remDeg4_P0`!
  obtain ⟨hp4, hp3, hp2, hp1, hp0⟩ := ValLead.interp4_of hg_L
  set q := interp4 g0
  set P1_0 := remDeg4_P1 q2_0 (-2 * q2_0 * z2) (q2_0 * z2 ^ 2) q.1 q.2.1 q.2.2.1 q.2.2.2.1
  set P0_0 := remDeg4_P0 q2_0 (-2 * q2_0 * z2) (q2_0 * z2 ^ 2) q.1 q.2.1 q.2.2.1 q.2.2.2.2
  have hP1_L : ValLead (-3) P1 P1_0 := by
    simp only [P1, P1_0, remDeg4_P1]
    have hr3 := ((hd2_2_L.mul hp3).eq_k (k' := -3) (by omega)).sub ((hd2_1_L.mul hp4).eq_k (k' := -3) (by omega))
    have hr2 := ((hd2_2_L.mul hp2).eq_k (k' := -3) (by omega)).sub ((hd2_0_L.mul hp4).eq_k (k' := -3) (by omega))
    have hs2 := ((hd2_2_L.mul hr2).eq_k (k' := -3) (by omega)).sub ((hd2_1_L.mul hr3).eq_k (k' := -3) (by omega))
    have hs1 := (((hd2_2_L.pow 2).mul hp1).eq_k (k' := -3) (by omega)).sub ((hd2_0_L.mul hr3).eq_k (k' := -3) (by omega))
    exact ((hd2_2_L.mul hs1).eq_k (k' := -3) (by omega)).sub ((hd2_1_L.mul hs2).eq_k (k' := -3) (by omega))
  have hP0_L : ValLead (-3) P0 P0_0 := by
    simp only [P0, P0_0, remDeg4_P0]
    have hr3 := ((hd2_2_L.mul hp3).eq_k (k' := -3) (by omega)).sub ((hd2_1_L.mul hp4).eq_k (k' := -3) (by omega))
    have hr2 := ((hd2_2_L.mul hp2).eq_k (k' := -3) (by omega)).sub ((hd2_0_L.mul hp4).eq_k (k' := -3) (by omega))
    have hs2 := ((hd2_2_L.mul hr2).eq_k (k' := -3) (by omega)).sub ((hd2_1_L.mul hr3).eq_k (k' := -3) (by omega))
    exact (((hd2_2_L.pow 3).mul hp0).eq_k (k' := -3) (by omega)).sub ((hd2_0_L.mul hs2).eq_k (k' := -3) (by omega))
  have hnum_L : ValLead 1 (-(P1 * d0 - P0 * d1) * U ^ 3 * W2_0 * cb ^ 4)
      (-(P1_0 * d0_1 - P0_0 * d1_1) * w0 * cb0 ^ 4) := by
    have hcomb := (((hP1_L.mul hd0_L).eq_k (k' := -2) (by omega)).sub ((hP0_L.mul hd1_L).eq_k (k' := -2) (by omega))).neg
    exact (((hcomb.mul (hU_L.pow 3)).mul hw0_L).mul (hcb_L.pow 4)).eq_k (by omega) |>.eq_c (by ring)
  have hquot_L := (hnum_L.div_of_ne hden_L hden_ne).eq_k (k' := -1) (by omega)
  rw [hquot_L.c0]
  clear_value U V ca cb c0W d2_2 d2_1 d2_0 d1 d0 res g p P1 P0
  -- Evaluate `P1_0` and `P0_0` at double root `z2` via `remDeg4_eq` in `Dual K5` at `Z2 = ⟨z2, w0⟩`!
  -- First build explicit polynomials `P_A, P_Q : K5[X]` for `g0 z = w0^2 * A0U_12(a(z), b(z)) * q1_lead0(a(z), b(z))`!
  set aX : K5[X] := C (1 / w0) * X
  set bX : K5[X] := C (-ca0 / (w0 * cb0)) * X + C (-c0W0 / (w0 * cb0))
  have haX_eval (z : K5) : aX.eval z = z / w0 := by simp [aX]; ring
  have hbX_eval (z : K5) : bX.eval z = -(ca0 * z + c0W0) / (w0 * cb0) := by simp [bX]; ring
  set P_A : K5[X] := A0U_12_of Polynomial.C aX bX
  have hPA_eval (z : K5) : P_A.eval z = A0U_12_of (RingHom.id K5) (z / w0) (-(ca0 * z + c0W0) / (w0 * cb0)) := by
    have h := map_A0U_12_of (Polynomial.evalRingHom z) Polynomial.C aX bX
    have hcomp : (Polynomial.evalRingHom z).comp Polynomial.C = RingHom.id K5 :=
      RingHom.ext (fun r => Polynomial.eval_C)
    simpa only [P_A, hcomp, Polynomial.coe_evalRingHom, haX_eval, hbX_eval] using h
  have hPA_deg3 : P_A.natDegree ≤ 3 := by
    have hdeg : IsPolyDeg 3 (fun z => P_A.eval z) := by
      have hmi (mi : Fin 10) : IsPolyDeg 3 (fun z => numM_12_of (RingHom.id K5) mi (z / w0) (-(ca0 * z + c0W0) / (w0 * cb0))) := by
        have h1 (U : K5) : IsPolyDeg 3 (fun z => numM mi (z / w0) (-(ca0 * z + c0W0) / (w0 * cb0))
            (S_K - z / w0 * T_K) (Q_K - -(ca0 * z + c0W0) / (w0 * cb0) * T_K) U 1) :=
          (numM_isPolyDeg3 mi S_K Q_K T_K U 1 (1 / w0) 0 (-ca0 / (w0 * cb0)) (-c0W0 / (w0 * cb0))).congr
            (fun z => by congr 1 <;> ring)
        exact (((((h1 1).sub (h1 (-1))).smul_left 8).sub ((h1 2).sub (h1 (-2)))).div_const 12).congr
          (fun z => (numM_12_of_eq_interp mi _ _).symm)
      have hp (i j : Fin 10) : IsPolyDeg 3 (fun z =>
          5 * numM_12_of (RingHom.id K5) i (z / w0) (-(ca0 * z + c0W0) / (w0 * cb0)) -
          9 * numM_12_of (RingHom.id K5) j (z / w0) (-(ca0 * z + c0W0) / (w0 * cb0))) :=
        ((hmi i).smul_left 5).sub ((hmi j).smul_left 9)
      exact (((((hp 0 1).smul_left (-(19708 / 1257375 : K5))).add
        ((hp 1 2).smul_left (1472 / 1257375 : K5))).sub
        ((hp 3 5).smul_left (16 / 729 : K5))).add
        ((hp 4 6).smul_left (188 / 2025 : K5))).congr (fun z => by rw [hPA_eval]; simp [A0U_12_of])
    rcases hdeg with ⟨Q_poly, hQ_deg, hQ_eval⟩
    have : Infinite K5 := Infinite.of_injective (Nat.cast : ℕ → K5) Nat.cast_injective
    have hEq : P_A = Q_poly := Polynomial.funext (fun z => hQ_eval z)
    rwa [hEq]
  let q1_c0 : K5 := 9 * w0 * (H0_of S_K Q_K T_K * A1_of S_K Q_K 0 1 *
      (QY_num S_K Q_K T_K x_K y_K 0 1 0 - QY_num S_K Q_K T_K x_K y_K 0 0 0) +
    (H0_of S_K Q_K T_K * dA1_fn 0 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 0 S_K Q_K T_K) *
      EB_of S_K Q_K T_K x_K y_K 0 1)
  let q1_c1 : K5 := 9 * w0 * (H0_of S_K Q_K T_K * A1_of S_K Q_K 0 1 *
      (QY_num S_K Q_K T_K x_K y_K 0 1 1 - QY_num S_K Q_K T_K x_K y_K 0 0 1) +
    (H0_of S_K Q_K T_K * dA1_fn 1 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 1 S_K Q_K T_K) *
      EB_of S_K Q_K T_K x_K y_K 0 1)
  let q1_c2 : K5 := 9 * w0 * (H0_of S_K Q_K T_K * A1_of S_K Q_K 0 1 *
      (QY_num S_K Q_K T_K x_K y_K 0 1 2 - QY_num S_K Q_K T_K x_K y_K 0 0 2) +
    (H0_of S_K Q_K T_K * dA1_fn 2 S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn 2 S_K Q_K T_K) *
      EB_of S_K Q_K T_K x_K y_K 0 1)
  set P_Q : K5[X] := C q1_c0 * aX + C q1_c1 * bX + C q1_c2
  have hPQ_eval (z : K5) : P_Q.eval z = q1_lead0 (z / w0) (-(ca0 * z + c0W0) / (w0 * cb0)) := by
    simp only [P_Q, eval_add, eval_mul, eval_C, haX_eval, hbX_eval, q1_c0, q1_c1, q1_c2, q1_lead0]; ring
  have hPQ_deg1 : P_Q.natDegree ≤ 1 := by
    have haX_deg : aX.natDegree ≤ 1 := le_trans (natDegree_C_mul_le _ _) (by simp)
    have hbX_deg : bX.natDegree ≤ 1 :=
      (natDegree_add_le _ _).trans (max_le (le_trans (natDegree_C_mul_le _ _) (by simp)) (by simp))
    exact (natDegree_add_le _ _).trans (max_le
      ((natDegree_add_le _ _).trans (max_le (le_trans (natDegree_C_mul_le _ _) haX_deg)
        (le_trans (natDegree_C_mul_le _ _) hbX_deg))) (by simp))
  set P_g0 : K5[X] := C (w0 ^ 2) * P_A * P_Q
  have hPg0_deg4 : P_g0.natDegree ≤ 4 :=
    natDegree_mul_le.trans (Nat.add_le_add (le_trans (natDegree_C_mul_le _ _) hPA_deg3) hPQ_deg1)
  have hPg0_eval (z : K5) : g0 z = P_g0.eval z := by
    simp only [g0, P_g0, eval_mul, eval_C, hPA_eval, hPQ_eval]
  have hq_coeffs : q = (P_g0.coeff 4, P_g0.coeff 3, P_g0.coeff 2, P_g0.coeff 1, P_g0.coeff 0) := by
    apply interp4_eq
    intro z
    rw [hPg0_eval z, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hPg0_deg4)]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one]
    ring
  -- Evaluate `P_g0` in `Dual K5` at `Z2 = ⟨z2, w0⟩`!
  set Z2 : Dual K5 := ⟨z2, w0⟩
  have hPg0_Z2 : Dual.C q.1 * Z2 ^ 4 + Dual.C q.2.1 * Z2 ^ 3 + Dual.C q.2.2.1 * Z2 ^ 2 +
      Dual.C q.2.2.2.1 * Z2 + Dual.C q.2.2.2.2 = P_g0.eval₂ Dual.C Z2 := by
    rw [hq_coeffs, Polynomial.eval₂_eq_sum_range' Dual.C (Nat.lt_succ_of_le hPg0_deg4)]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one]
    simp only [pow_zero, mul_one, pow_one]
    ring
  have hrem_Z2 : Dual.C q2_0 ^ 3 * (P_g0.eval₂ Dual.C Z2) = Dual.C P1_0 * Z2 + Dual.C P0_0 := by
    have hrem := remDeg4_eq (Dual.C q2_0) (Dual.C (-2 * q2_0 * z2)) (Dual.C (q2_0 * z2 ^ 2))
      (Dual.C q.1) (Dual.C q.2.1) (Dual.C q.2.2.1) (Dual.C q.2.2.2.1) (Dual.C q.2.2.2.2) Z2
    have hquad0 : Dual.C q2_0 * Z2 ^ 2 + Dual.C (-2 * q2_0 * z2) * Z2 + Dual.C (q2_0 * z2 ^ 2) = 0 := by
      ext <;> simp [Z2, Dual.C_val, Dual.C_eps, Dual.pow_eq] <;> ring
    have hP1_map : remDeg4_P1 (Dual.C q2_0) (Dual.C (-2 * q2_0 * z2)) (Dual.C (q2_0 * z2 ^ 2))
        (Dual.C q.1) (Dual.C q.2.1) (Dual.C q.2.2.1) (Dual.C q.2.2.2.1) = Dual.C P1_0 := by
      simp only [remDeg4_P1, P1_0, map_sub, map_mul, map_pow]
    have hP0_map : remDeg4_P0 (Dual.C q2_0) (Dual.C (-2 * q2_0 * z2)) (Dual.C (q2_0 * z2 ^ 2))
        (Dual.C q.1) (Dual.C q.2.1) (Dual.C q.2.2.1) (Dual.C q.2.2.2.2) = Dual.C P0_0 := by
      simp only [remDeg4_P0, P0_0, map_sub, map_mul, map_pow]
    rw [hPg0_Z2, hquad0, mul_zero, zero_add, hP1_map, hP0_map] at hrem
    exact hrem
  have hP_val : q2_0 ^ 3 * (P_g0.eval₂ Dual.C Z2).val = P1_0 * z2 + P0_0 := by
    have h := congrArg Dual.val hrem_Z2
    simpa [Z2, Dual.C_val, Dual.C_eps, Dual.pow_eq] using h
  have hP_eps : q2_0 ^ 3 * (P_g0.eval₂ Dual.C Z2).eps = P1_0 * w0 := by
    have h := congrArg Dual.eps hrem_Z2
    simpa [Z2, Dual.C_val, Dual.C_eps, Dual.pow_eq] using h
  -- Compute `aX.eval₂ Dual.C Z2 = ⟨S_K / B, 1⟩` and `bX.eval₂ Dual.C Z2 = ⟨Q_K / B, (5*S_K - 3*Q_K)/(6*S_K)⟩`!
  set d_ab : K5 := 6 * S_K * B
  have h6_ne : (6 : K5) ≠ 0 := by exact_mod_cast (by decide : (6 : ℕ) ≠ 0)
  have hd_ab_ne : d_ab ≠ 0 := mul_ne_zero (mul_ne_zero h6_ne hS) hB
  set inv_d : K5 := d_ab⁻¹
  have hd_inv : d_ab * inv_d = 1 := mul_inv_cancel₀ hd_ab_ne
  set a_du : Dual K5 := Dual.C inv_d * ⟨6 * S_K ^ 2, 6 * S_K * B⟩
  set b_du : Dual K5 := Dual.C inv_d * ⟨6 * S_K * Q_K, (5 * S_K - 3 * Q_K) * B⟩
  have haX_Z2 : aX.eval₂ Dual.C Z2 = a_du := by
    ext
    · simp only [aX, Z2, a_du, eval₂_mul, eval₂_C, eval₂_X, Dual.C_val, Dual.mul_val, z2]
      apply mul_left_cancel₀ (mul_ne_zero hw0_ne hd_ab_ne)
      have h1 : w0 * d_ab * (1 / w0 * (w0 * S_K / B)) = 6 * S_K ^ 2 * w0 := by
        dsimp only [d_ab]; field_simp [hw0_ne, hB]
      have h2 : w0 * d_ab * (inv_d * (6 * S_K ^ 2)) = 6 * S_K ^ 2 * w0 := by
        linear_combination (w0 * (6 * S_K ^ 2)) * hd_inv
      rw [h1, h2]
    · simp only [aX, Z2, a_du, eval₂_mul, eval₂_C, eval₂_X, Dual.C_val, Dual.C_eps, Dual.mul_eps]
      rw [zero_mul, add_zero, one_div, inv_mul_cancel₀ hw0_ne, zero_mul, add_zero]
      have h : inv_d * (6 * S_K * B) = d_ab * inv_d := by dsimp only [d_ab]; ring
      rw [h, hd_inv]
  have hbX_Z2 : bX.eval₂ Dual.C Z2 = b_du := by
    have hca_cb : -ca0 / cb0 = (5 * S_K - 3 * Q_K) / (6 * S_K) := by
      apply mul_left_cancel₀ (mul_ne_zero hcb0_ne (mul_ne_zero h6_ne hS))
      have hl : cb0 * (6 * S_K) * (-ca0 / cb0) = -6 * S_K * ca0 := by field_simp [hcb0_ne]
      have hr : cb0 * (6 * S_K) * ((5 * S_K - 3 * Q_K) / (6 * S_K)) = cb0 * (5 * S_K - 3 * Q_K) := by
        field_simp [h6_ne, hS]
      rw [hl, hr]; dsimp only [ca0, cb0]; ring
    ext
    · simp only [bX, Z2, b_du, eval₂_add, eval₂_mul, eval₂_C, eval₂_X, Dual.C_val, Dual.add_val, Dual.mul_val]
      apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hw0_ne hcb0_ne) hd_ab_ne)
      have hl : w0 * cb0 * d_ab * (-ca0 / (w0 * cb0) * z2 + -c0W0 / (w0 * cb0)) =
          -d_ab * (ca0 * z2 + c0W0) := by field_simp [hw0_ne, hcb0_ne]; ring
      have hr : w0 * cb0 * d_ab * (inv_d * (6 * S_K * Q_K)) = 6 * S_K * Q_K * w0 * cb0 := by
        linear_combination (w0 * cb0 * (6 * S_K * Q_K)) * hd_inv
      rw [hl, hr]
      have hw0_mul : B ^ 3 * w0 = -(25 / 4 : K5) * S_K * A ^ 2 := by
        rw [hw0_eq, mul_div_cancel₀ _ (pow_ne_zero 3 hB)]
      apply mul_left_cancel₀ (pow_ne_zero 2 hB)
      have h1 : B ^ 2 * (-d_ab * (ca0 * z2 + c0W0)) =
          -6 * S_K * B ^ 2 * ca0 * S_K * w0 - 6 * S_K * (c0W0 * B ^ 3) := by
        dsimp only [d_ab, z2]; field_simp [hB]; ring
      rw [h1]
      have hc0W : c0W0 * B ^ 3 = -(4 / 81 : K5) * B ^ 2 * w0 * (B ^ 3 * w0) := by
        simp only [c0W0, CoverParams.c0_V2, CoverParams.inv81, k5Params_inv3, k5Params_T, B]; ring
      rw [hc0W, hw0_mul]
      dsimp only [ca0, cb0, A]; ring
    · simp only [bX, Z2, b_du, eval₂_add, eval₂_mul, eval₂_C, eval₂_X, Dual.C_val, Dual.C_eps, Dual.add_eps, Dual.mul_eps]
      rw [zero_mul, add_zero, add_zero, zero_mul, add_zero]
      have h1 : -ca0 / (w0 * cb0) * w0 = -ca0 / cb0 := by field_simp [hw0_ne, hcb0_ne]
      rw [h1, hca_cb]
      apply mul_left_cancel₀ hd_ab_ne
      have h2 : d_ab * ((5 * S_K - 3 * Q_K) / (6 * S_K)) = (5 * S_K - 3 * Q_K) * B := by
        dsimp only [d_ab]; field_simp [h6_ne, hS]
      rw [h2]; linear_combination -((5 * S_K - 3 * Q_K) * B) * hd_inv
  -- Evaluate `P_A.eval₂ Dual.C Z2 = A0U_12_of Dual.C a_du b_du` by clearing `d_ab ^ 6` (division-free `ring`!)
  set Q_quad : K5 := 11943020 * S_K ^ 2 - 876486 * S_K * Q_K + 8382500 * S_K * T_K +
    5029500 * Q_K * T_K - 14837025 * S_K - 33647355 * Q_K
  have hPA_Z2 : P_A.eval₂ Dual.C Z2 = A0U_12_of Dual.C a_du b_du := by
    have h := map_A0U_12_of (Polynomial.eval₂RingHom Dual.C Z2) Polynomial.C aX bX
    have hcomp : (Polynomial.eval₂RingHom Dual.C Z2).comp Polynomial.C = Dual.C :=
      RingHom.ext (fun r => by simp)
    simpa only [P_A, hcomp, Polynomial.coe_eval₂RingHom, haX_Z2, hbX_Z2] using h
  have hA0U_Z2_val_eps :
      Dual.C (d_ab ^ 3) * (P_A.eval₂ Dual.C Z2) =
        ⟨(8248380 / 51331077 : K5) * (5 * S_K - 3 * Q_K) * S_K ^ 3 * A ^ 2,
         -(2 / 51331077 : K5) * B * S_K ^ 2 * A ^ 2 * Q_quad⟩ := by
    rw [hPA_Z2]
    exact br2_0_A0U_Z2_eval
  -- Evaluate `P_Q.eval₂ Dual.C Z2` in terms of `evalBivK5 q1_v_35721_biv` and `evalBivK5 q1_e_35721_divB5_biv`!
  have hPQ_Z2 : Dual.C (35721 * d_ab) * (P_Q.eval₂ Dual.C Z2) =
      ⟨w0 * S_K * A ^ 2 * evalBivK5 q1_v_35721_biv,
       w0 * S_K * A ^ 2 * B * evalBivK5 q1_e_35721_divB5_biv⟩ := by
    obtain ⟨hq1v, hq1e⟩ := br2_0_q1_biv_eval w0
    rw [hq1v, hq1e]
    ext
    · simp only [P_Q, eval₂_add, eval₂_mul, eval₂_C, haX_Z2, hbX_Z2, a_du, b_du,
        Dual.C_val, Dual.add_val, Dual.mul_val]
      have h := hd_inv; dsimp only [d_ab] at h ⊢
      linear_combination (35721 * (q1_c0 * (6 * S_K ^ 2) + q1_c1 * (6 * S_K * Q_K))) * h
    · simp only [P_Q, eval₂_add, eval₂_mul, eval₂_C, haX_Z2, hbX_Z2, a_du, b_du,
        Dual.C_val, Dual.C_eps, Dual.add_eps, Dual.mul_eps, zero_mul, add_zero]
      linear_combination (35721 * (q1_c0 * (6 * S_K * B) + q1_c1 * ((5 * S_K - 3 * Q_K) * B))) * hd_inv
  -- Combine `hA0U_Z2_val_eps`, `hPQ_Z2`, `hP_val`, `hP_eps` and close via `br2_0_final_cancel`!
  have hPg0_Z2_prod : Dual.C (35721 * d_ab ^ 4) * (P_g0.eval₂ Dual.C Z2) =
      Dual.C (w0 ^ 2) *
        ⟨(8248380 / 51331077 : K5) * (5 * S_K - 3 * Q_K) * S_K ^ 3 * A ^ 2,
         -(2 / 51331077 : K5) * B * S_K ^ 2 * A ^ 2 * Q_quad⟩ *
        ⟨w0 * S_K * A ^ 2 * evalBivK5 q1_v_35721_biv,
         w0 * S_K * A ^ 2 * B * evalBivK5 q1_e_35721_divB5_biv⟩ := by
    rw [← hA0U_Z2_val_eps, ← hPQ_Z2]
    simp only [P_g0, eval₂_mul, eval₂_C]
    rw [show Dual.C (35721 * d_ab ^ 4) = Dual.C (d_ab ^ 3) * Dual.C (35721 * d_ab) by
      rw [← map_mul]; congr 1; ring]
    ring
  exact br2_0_final_cancel hw0_eq hw0_ne hden_ne hq2_ne hcd_eq hP_val hP_eps hPg0_Z2_prod

/-! ### Section 5: Master Theorem `residue_zero_eta` -/

theorem residue_zero_eta : CrossedRationalResidue.residue 0 CoverResidue.eta = toK5_RU := by
  change (ψ0 CoverResidue.eta).coeff (-1) = toK5_RU
  unfold CoverResidue.eta
  rw [map_trace_AC_eq_sum_branches ψ0 W1_0 W2_0 W1_0_eq_ψ0 W2_0_eq_ψ0 W1_W2_0_sum_ψ0,
    HahnSeries.coeff_add, br1_0_eta_AC_coeff_neg_one, zero_add, br2_0_eta_AC_coeff_neg_one]

end SymmetricSexticResidual.LocalResidueU0
