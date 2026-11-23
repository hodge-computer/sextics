import Proposal.LocalResidueQ5Trace
import Proposal.LocalResidueQ5CheckB

/-! Final assembly of `LocalResidueQ5`: `sum_RQ5_eta_L` and `global_residue_cancellation`. -/

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
  have hbQ_eq : ((masterLim ^ masterDegS : ℕ) : ℤ) = bQ2D := by
    have hpow : ∀ a b : ℕ, (((Nat.pow 2 a) ^ b : ℕ) : ℤ) = Int.ofNat (Nat.pow 2 (b * a)) := by
      intro a b; rw [show Nat.pow 2 a = 2 ^ a from rfl, ← pow_mul, Nat.mul_comm]; rfl
    unfold masterLim bQ2D
    exact hpow masterBits masterDegS
  have hrelV (t : ℤ) :
      BRel (fun p z => MvPolynomial.eval (v3Int (masterLim : ℤ) ((masterLim ^ masterDegS : ℕ) : ℤ) t) p = z)
        bP3 (evalTStep intOps bS2D c2D t) :=
    evalTStep_rel (poly3ToIntRel (masterLim : ℤ) ((masterLim ^ masterDegS : ℕ) : ℤ) t)
      (by rw [MvPolynomial.eval_X, v3Int]; rfl)
      (evalSQCache_rel (poly3ToIntRel (masterLim : ℤ) ((masterLim ^ masterDegS : ℕ) : ℤ) t)
        (by rw [MvPolynomial.eval_X, v3Int]; rfl) (by rw [MvPolynomial.eval_X, v3Int]; exact hbQ_eq))
      (by rw [MvPolynomial.eval_X, v3Int])
  have hrelK : BRel (fun p x => evalP3K5 p = x) bP3 (evalTStep k5Ops S_K cacheK T_K) :=
    evalTStep_rel poly3ToK5Rel (by simp [evalP3K5, v3K5])
      (evalSQCache_rel poly3ToK5Rel (by simp [evalP3K5, v3K5]) (by simp [evalP3K5, v3K5]))
      (by simp [evalP3K5, v3K5])
  have hallB : ∀ r ∈ bPB, ∀ b ∈ r, b.dS < masterDegS ∧ b.dT < 20 ∧ b.M < masterLim := by
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
        simp only [evalYListK5, evalYList, hk0, htail0, mul_zero, add_zero]
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
        simp only [evalBivLK5, evalBivL, hr0, htail0, mul_zero, add_zero]
  exact hzero_gen masterDegS masterLim bP3 bPB (evalTStep intOps bS2D c2D) (evalTStep k5Ops S_K cacheK T_K) hrelB hrelV hrelK hallB hallV

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
