import Proposal.LocalResidueU0
import Proposal.LocalResidueInfAlg

/-!
# Local Residue at Infinity (`U = ∞`)

Proves `CrossedRationalResidue.infinityCoefficient CoverResidue.eta = -toK5_RInf / L_K ^ 2`.

Architecture:
1. `ψinf := ψ0.comp CrossedRationalResidue.reciprocal.toRingHom`, `ψinf_toRat = evalInvT`,
   and `infinityCoefficient_eq_coeff_one : infinityCoefficient f = (ψinf f).coeff 1`.
2. Polymorphic `[Field R] [CharZero R]` algebraic identities: `minor_split_UV`, `numM_split_UV`,
   `AY_t3_U3_eq_zero`, `A0V_U3_lead3_eq`, `A0V_U2_lead3_eq`, `AX_U3_lead3_eq`, `QY_10_u1_zero`,
   `br_10_eq..om_11_eq`, and the log-derivative `W1_inf_weights_alg`.
3. `W1_inf` dual expansion, exact weights `A4[3], A4[4], A3[4], A2[4]`, and `res_z_W2_inf_val_ne`.
4. Branch 2 (`W2_inf`): `(br2_inf eta_AC).coeff 1 = 0`.
5. Branch 1 (`W1_inf`): `Uinf_biv_identity` via `biv_denote_eq_of_kronecker3` (`decide +kernel`),
   `br1_inf_g_valLead`, `br1_inf_p4_valDual`, `br1_inf_eta_AC_coeff_one`, and `infinityCoefficient_eta`.
-/

namespace SymmetricSexticResidual.LocalResidueInf

open Polynomial
open Lean.Grind.CommRing PolynomialEncoding.BivariateExpressions PolynomialEncoding.SignedExpressions
open SymmetricSexticResidual.K5Field
open SymmetricSexticResidual.VerticalData
open SymmetricSexticResidual.VerticalIdentity
open SymmetricSexticResidual.LocalResidueData
open SymmetricSexticResidual.SheetCalculus
open SymmetricSexticResidual.CoverAlgebra
open SymmetricSexticResidual.CoverResidue
open SymmetricSexticResidual.LocalResidueU0
open SymmetricSexticResidual.LocalResidueInfAlg
open PolynomialEncoding.KroneckerCheck QuadraticCovers

/-! ### Section 1: `ψinf`, `infinityCoefficient_eq_coeff_one`, `br1_inf`, `br2_inf` -/

lemma L_K_ne_zero : L_K ≠ 0 := by
  have hQ5 := LocK5.ne_zero_of_evLoc Q5_lc_evLoc_ne
  have hc5 : ((locParams.Q5_z.coeff 5 : LocK5) : K5) = k5Params.Q5_z.coeff 5 := by
    change LocK5.subtype (locParams.Q5_z.coeff 5) = k5Params.Q5_z.coeff 5
    rw [← Polynomial.coeff_map, CoverParams.map_Q5_z]; rfl
  rw [hc5, k5Params_Q5_c5_eq] at hQ5
  have hfac : Q5_c5 S_K Q_K = (16 / 413343 : K5) * L_K * (S_K - 3 * Q_K) ^ 4 := by
    simp only [Q5_c5, L_K]; ring
  rw [hfac] at hQ5
  intro h0; rw [h0, mul_zero, zero_mul] at hQ5; exact hQ5 rfl

noncomputable def ψinf : RatFunc K5 →+* LaurentSeries K5 :=
  ψ0.comp CrossedRationalResidue.reciprocal.toRingHom

lemma ψinf_C (c : K5) : ψinf (RatFunc.C c) = HahnSeries.C c := by
  change ψ0 (CrossedRationalResidue.reciprocal (RatFunc.C c)) = HahnSeries.C c
  rw [CrossedRationalResidue.reciprocal_C, ψ0_C]

lemma ψinf_X : ψinf (RatFunc.X : RatFunc K5) = HahnSeries.single (-1 : ℤ) (1 : K5) := by
  change ψ0 (CrossedRationalResidue.reciprocal (RatFunc.X : RatFunc K5)) = HahnSeries.single (-1 : ℤ) (1 : K5)
  rw [CrossedRationalResidue.reciprocal_X, map_inv₀, ψ0_X]
  have h : HahnSeries.single (1 : ℤ) (1 : K5) * HahnSeries.single (-1 : ℤ) (1 : K5) = 1 := by
    rw [HahnSeries.single_mul_single]; simp
  exact inv_eq_of_mul_eq_one_right h

lemma ψinf_toRat (P : K5[X]) : ψinf (toRat P) = evalInvT P := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | monomial n c =>
    rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, map_mul, map_pow]
    simp only [toRat, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
      ψinf_C, ψinf_X, map_mul, map_pow, evalInvT_C, evalInvT_X]

private lemma ValLead.of_ofNat (n : ℕ) [n.AtLeastTwo] :
    ValLead 0 (no_index (OfNat.ofNat n) : LaurentSeries K5) (no_index (OfNat.ofNat n) : K5) := by
  simpa only [map_ofNat] using ValLead.of_C (OfNat.ofNat n : K5)

private lemma HasValGe.of_ofNat (n : ℕ) [n.AtLeastTwo] :
    HasValGe 0 (no_index (OfNat.ofNat n) : LaurentSeries K5) := by
  simpa only [map_ofNat] using HasValGe.of_C (OfNat.ofNat n : K5)

private lemma ValDual.of_ofNat (n : ℕ) [n.AtLeastTwo] :
    ValDual 0 (no_index (OfNat.ofNat n) : LaurentSeries K5) (Dual.C (OfNat.ofNat n : K5)) := by
  simpa only [map_ofNat] using ValDual.of_C (OfNat.ofNat n : K5)

private lemma valLead_eq_fc {k : ℤ} {f g : LaurentSeries K5} {a b : K5}
    (hf : ValLead k f a) (hfg : f = g) (hab : a = b) : ValLead k g b := hfg ▸ hab ▸ hf

private lemma valDual_eq_fd {k : ℤ} {f g : LaurentSeries K5} {a b : Dual K5}
    (hf : ValDual k f a) (hfg : f = g) (hab : a = b) : ValDual k g b := hfg ▸ hab ▸ hf

private lemma hasValGe_eq_f {k : ℤ} {f g : LaurentSeries K5}
    (hf : HasValGe k f) (hfg : f = g) : HasValGe k g := hfg ▸ hf

private lemma ringEval_H0_7_inf : ringEval vK5 H0_int_e = 7 * H0_of S_K Q_K T_K := by
  simp only [H0_int_e, ringEval, eS, eQ, eT, vK5, H0_of]; ring

lemma infinityCoefficient_eq_coeff_one (f : RatFunc K5) :
    CrossedRationalResidue.infinityCoefficient f = (ψinf f).coeff 1 := by
  change CrossedRationalResidue.residue 0 ((RatFunc.X ^ 2)⁻¹ * CrossedRationalResidue.reciprocal f) =
    (ψ0 (CrossedRationalResidue.reciprocal f)).coeff 1
  change (ψ0 ((RatFunc.X ^ 2)⁻¹ * CrossedRationalResidue.reciprocal f)).coeff (-1) =
    (ψ0 (CrossedRationalResidue.reciprocal f)).coeff 1
  rw [map_mul, map_inv₀, map_pow, ψ0_X]
  have hinv : (HahnSeries.single (1 : ℤ) (1 : K5) ^ 2)⁻¹ = HahnSeries.single (-2 : ℤ) (1 : K5) := by
    apply inv_eq_of_mul_eq_one_right
    rw [HahnSeries.single_pow, HahnSeries.single_mul_single]; simp
  rw [hinv, HahnSeries.coeff_single_mul]
  simp

lemma W1_inf_eq_ψinf :
    W1_inf ^ 2 + ψinf (toRat k5Params.bW) * W1_inf + ψinf (toRat k5Params.cW) = 0 := by
  rw [ψinf_toRat, ψinf_toRat]; exact W1_inf_eq

lemma W2_inf_eq_ψinf :
    W2_inf ^ 2 + ψinf (toRat k5Params.bW) * W2_inf + ψinf (toRat k5Params.cW) = 0 := by
  rw [ψinf_toRat, ψinf_toRat]; exact W2_inf_eq

lemma W1_W2_inf_sum_ψinf : W1_inf + W2_inf = -ψinf (toRat k5Params.bW) := by
  rw [ψinf_toRat]; exact W1_W2_inf_sum

noncomputable def br1_inf : A_C →+* LaurentSeries K5 :=
  branchHom ψinf W1_inf W1_inf_eq_ψinf

noncomputable def br2_inf : A_C →+* LaurentSeries K5 :=
  branchHom ψinf W2_inf W2_inf_eq_ψinf

/-! ### Section 3: `W1_inf` Dual Expansion, Weights, and `res_z_W2_inf_val_ne` -/

lemma W1_inf_valDual :
    ValDual 0 W1_inf ⟨-(k5Params.Cv0 / k5Params.Bv2), k5Params.Cv0 * k5Params.Bv1 / k5Params.Bv2 ^ 2⟩ := by
  have hw := HasValGe_W1_inf
  have heq : HahnSeries.C k5Params.Av0 * W1_inf ^ 2 +
      evalInvT k5Params.Bv * W1_inf + HahnSeries.C k5Params.Cv0 * HahnSeries.single (-2) 1 = 0 := by
    have h0 := congrArg (HahnSeries.C k5Params.Av0 * ·) W1_inf_eq
    rw [mul_zero] at h0
    have hAv : HahnSeries.C k5Params.Av0 * evalInvT k5Params.bW = evalInvT k5Params.Bv := by
      rw [CoverParams.bW, map_mul, evalInvT_C, ← mul_assoc, ← map_mul, k5Params_Av0_mul_inv, map_one, one_mul]
    have hCv : HahnSeries.C k5Params.Av0 * evalInvT k5Params.cW =
        HahnSeries.C k5Params.Cv0 * HahnSeries.single (-2) 1 := by
      rw [CoverParams.cW, map_mul, map_pow, evalInvT_C, evalInvT_X, HahnSeries.single_pow,
        ← mul_assoc, ← map_mul]
      have : k5Params.Av0 * (k5Params.Cv0 * k5Params.Av0_inv) = k5Params.Cv0 := by
        rw [mul_left_comm, k5Params_Av0_mul_inv, mul_one]
      rw [this]; simp
    linear_combination h0 - hAv * W1_inf - hCv
  have hBv_D : ValDual (-2) (evalInvT k5Params.Bv) ⟨k5Params.Bv2, k5Params.Bv1⟩ := by
    have hdeg : k5Params.Bv.natDegree ≤ 2 := by
      simp only [CoverParams.Bv, CoverParams.quadU]
      exact (Polynomial.natDegree_add_le _ _).trans (max_le
        ((Polynomial.natDegree_add_le _ _).trans (max_le (by simp)
          ((Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_le.trans (by omega)))))
        ((Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_pow_le 2)))
    exact ((ValDual.of_evalInvT k5Params.Bv hdeg (by omega)).eq_k (by omega)).eq_d (by
      ext <;> simp only [CoverParams.Bv, coeff_quadU])
  have hsq : HasValGe 0 (HahnSeries.C k5Params.Av0 * W1_inf ^ 2) :=
    ((HasValGe.of_C _).mul (hw.pow 2)).mono (by omega)
  have hBvW_D : ValDual (-2) (evalInvT k5Params.Bv * W1_inf)
      (⟨k5Params.Bv2, k5Params.Bv1⟩ * ⟨W1_inf.coeff 0, W1_inf.coeff 1⟩) :=
    (hBv_D.mul ⟨hw, rfl, rfl⟩).eq_k (by omega)
  have hCs : HahnSeries.C k5Params.Cv0 * HahnSeries.single (-2 : ℤ) (1 : K5) =
      HahnSeries.single (-2 : ℤ) k5Params.Cv0 := by
    rw [HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]
  rw [hCs] at heq
  have hc_m2 := congrArg (fun f : LaurentSeries K5 => f.coeff (-2)) heq
  rw [HahnSeries.coeff_add, HahnSeries.coeff_add, hsq (-2) (by omega), zero_add, hBvW_D.c0,
    HahnSeries.coeff_single_same, HahnSeries.coeff_zero] at hc_m2
  have hc0 : W1_inf.coeff 0 = -(k5Params.Cv0 / k5Params.Bv2) := by
    apply mul_left_cancel₀ k5Params_Bv2_ne
    rw [mul_neg, mul_div_cancel₀ _ k5Params_Bv2_ne]
    simp only [Dual.mul_val] at hc_m2; linear_combination hc_m2
  have hc_m1 := congrArg (fun f : LaurentSeries K5 => f.coeff (-1)) heq
  have hBvW_c1 : (evalInvT k5Params.Bv * W1_inf).coeff (-1) =
      (⟨k5Params.Bv2, k5Params.Bv1⟩ * ⟨W1_inf.coeff 0, W1_inf.coeff 1⟩ : Dual K5).eps := hBvW_D.c1
  rw [HahnSeries.coeff_add, HahnSeries.coeff_add, hsq (-1) (by omega), zero_add, hBvW_c1,
    HahnSeries.coeff_single_of_ne (by decide : (-1 : ℤ) ≠ -2),
    add_zero, HahnSeries.coeff_zero] at hc_m1
  have hc1 : W1_inf.coeff 1 = k5Params.Cv0 * k5Params.Bv1 / k5Params.Bv2 ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 k5Params_Bv2_ne)
    rw [mul_div_cancel₀ _ (pow_ne_zero 2 k5Params_Bv2_ne)]
    simp only [Dual.mul_eps] at hc_m1
    have hmul := congrArg (k5Params.Bv2 * ·) hc_m1
    rw [mul_zero] at hmul
    rw [hc0] at hmul
    have hmul' : k5Params.Bv2 ^ 2 * W1_inf.coeff 1 + k5Params.Bv1 * (k5Params.Bv2 * -(k5Params.Cv0 / k5Params.Bv2)) = 0 := by
      linear_combination hmul
    rw [mul_neg, mul_div_cancel₀ _ k5Params_Bv2_ne] at hmul'
    linear_combination hmul'
  exact ⟨hw, hc0, hc1⟩

private lemma evalInvT_toUW_valLead_W1 (v0 v1 v2 : K5) :
    ValLead (-2) (PairAlg.evalAt W1_inf (PairAlg.map evalInvT (k5Params.toUW v0 v1 v2))) v0 := by
  have heq : PairAlg.evalAt W1_inf (PairAlg.map evalInvT (k5Params.toUW v0 v1 v2)) =
      HahnSeries.C v0 * HahnSeries.single (-2) 1 +
      (HahnSeries.C v1 * HahnSeries.single (-1) 1 * W1_inf + HahnSeries.C v2 * W1_inf ^ 2) := by
    simp only [PairAlg.evalAt, PairAlg.map, CoverParams.toUW, map_sub, map_mul, map_pow,
      evalInvT_C, evalInvT_X, HahnSeries.single_pow]
    have h2p : (2 : ℕ) • (-1 : ℤ) = -2 := by decide
    simp only [one_pow, h2p]
    linear_combination -HahnSeries.C v2 * W1_inf_eq
  rw [heq]
  have h0 : ValLead (-2) (HahnSeries.C v0 * HahnSeries.single (-2) 1) v0 :=
    ((ValLead.of_C v0).mul (ValLead.of_single (-2) 1)).eq_k (by omega) |>.eq_c (mul_one v0)
  have h1 : HasValGe (-1) (HahnSeries.C v1 * HahnSeries.single (-1) 1 * W1_inf + HahnSeries.C v2 * W1_inf ^ 2) :=
    ((((HasValGe.of_C v1).mul (HasValGe.single (-1) 1)).mul HasValGe_W1_inf).mono (by omega)).add
      (((HasValGe.of_C v2).mul (HasValGe_W1_inf.pow 2)).mono (by omega))
  exact h0.add_high h1

private lemma natDegree_quadU_le {R : Type*} [CommRing R] (a0 a1 a2 : R) :
    (CoverParams.quadU a0 a1 a2).natDegree ≤ 2 := by
  unfold CoverParams.quadU
  exact (Polynomial.natDegree_add_le _ _).trans (max_le
    ((Polynomial.natDegree_add_le _ _).trans (max_le (by simp)
      ((Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_le.trans (by omega)))))
    ((Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_pow_le 2)))

private lemma deg2_q11 : k5Params.q11.natDegree ≤ 2 := natDegree_quadU_le _ _ _
private lemma deg2_q02 : k5Params.q02.natDegree ≤ 2 := natDegree_quadU_le _ _ _
private lemma deg2_c21 : k5Params.c21.natDegree ≤ 2 := natDegree_quadU_le _ _ _
private lemma deg2_c12 : k5Params.c12.natDegree ≤ 2 := natDegree_quadU_le _ _ _
private lemma deg2_c03 : k5Params.c03.natDegree ≤ 2 := natDegree_quadU_le _ _ _
private lemma deg2_ca : k5Params.ca_h.natDegree ≤ 2 := natDegree_quadU_le _ _ _
private lemma deg2_cb : k5Params.cb_h.natDegree ≤ 2 := natDegree_quadU_le _ _ _

private lemma coeff_mul_top2 (a b : K5[X]) (ha : a.natDegree ≤ 2) (hb : b.natDegree ≤ 2) :
    (a * b).coeff 4 = a.coeff 2 * b.coeff 2 := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a.coeff i * b.coeff j),
    Finset.sum_eq_single 2]
  · intro i _ hi2; by_cases hgt : 2 < i
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : a.natDegree < i), zero_mul]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : b.natDegree < 4 - i), mul_zero]
  · intro h; simp at h

private lemma coeff_mul_top3 (a b c : K5[X]) (ha : a.natDegree ≤ 2) (hb : b.natDegree ≤ 2) (hc : c.natDegree ≤ 2) :
    (a * b * c).coeff 6 = a.coeff 2 * b.coeff 2 * c.coeff 2 := by
  have hbc : (b * c).natDegree ≤ 4 := (Polynomial.natDegree_mul_le).trans (by omega)
  rw [mul_assoc, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a.coeff i * (b * c).coeff j),
    Finset.sum_eq_single 2]
  · rw [show 6 - 2 = 4 by rfl, coeff_mul_top2 b c hb hc]; ring
  · intro i _ hi2; by_cases hgt : 2 < i
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : a.natDegree < i), zero_mul]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : (b * c).natDegree < 6 - i), mul_zero]
  · intro h; simp at h

private lemma natDegree_mul3_le (a b c : K5[X]) (ha : a.natDegree ≤ 2) (hb : b.natDegree ≤ 2) (hc : c.natDegree ≤ 2) :
    (a * b * c).natDegree ≤ 6 :=
  (Polynomial.natDegree_mul_le).trans (by have := Polynomial.natDegree_mul_le (p := a) (q := b); omega)

private lemma k5Params_p21_natDegree_le :
    (-k5Params.q11 * k5Params.cb_h + 2 * k5Params.q02 * k5Params.ca_h).natDegree ≤ 3 := by
  have hle4 : (-k5Params.q11 * k5Params.cb_h + 2 * k5Params.q02 * k5Params.ca_h).natDegree ≤ 4 := by
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact Polynomial.natDegree_mul_le.trans (by rw [Polynomial.natDegree_neg]; linarith [deg2_q11, deg2_cb])
    · rw [mul_assoc, show (2 : K5[X]) = C 2 from (map_ofNat C 2).symm]
      exact (Polynomial.natDegree_C_mul_le 2 _).trans (Polynomial.natDegree_mul_le.trans (by linarith [deg2_q02, deg2_ca]))
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  by_cases h4 : n = 4
  · subst h4
    rw [Polynomial.coeff_add, neg_mul, Polynomial.coeff_neg, mul_assoc,
      show (2 : K5[X]) * (k5Params.q02 * k5Params.ca_h) = C 2 * (k5Params.q02 * k5Params.ca_h) by rw [map_ofNat],
      Polynomial.coeff_C_mul, coeff_mul_top2 _ _ deg2_q11 deg2_cb, coeff_mul_top2 _ _ deg2_q02 deg2_ca]
    simp only [CoverParams.q11, CoverParams.q02, CoverParams.ca_h, CoverParams.cb_h, coeff_quadU,
      CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3]; ring
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

private lemma k5Params_p31_natDegree_le :
    (k5Params.c12 * k5Params.cb_h - 3 * k5Params.c03 * k5Params.ca_h).natDegree ≤ 3 := by
  have hle4 : (k5Params.c12 * k5Params.cb_h - 3 * k5Params.c03 * k5Params.ca_h).natDegree ≤ 4 := by
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact Polynomial.natDegree_mul_le.trans (by linarith [deg2_c12, deg2_cb])
    · rw [mul_assoc, show (3 : K5[X]) = C 3 from (map_ofNat C 3).symm]
      exact (Polynomial.natDegree_C_mul_le 3 _).trans (Polynomial.natDegree_mul_le.trans (by linarith [deg2_c03, deg2_ca]))
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  by_cases h4 : n = 4
  · subst h4
    rw [Polynomial.coeff_sub, mul_assoc,
      show (3 : K5[X]) * (k5Params.c03 * k5Params.ca_h) = C 3 * (k5Params.c03 * k5Params.ca_h) by rw [map_ofNat],
      Polynomial.coeff_C_mul, coeff_mul_top2 _ _ deg2_c12 deg2_cb, coeff_mul_top2 _ _ deg2_c03 deg2_ca]
    simp only [CoverParams.c12, CoverParams.c03, CoverParams.ca_h, CoverParams.cb_h, coeff_quadU,
      CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3]; ring
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

private lemma k5Params_p32_natDegree_le :
    (-k5Params.c21 * k5Params.cb_h ^ 2 + 2 * k5Params.c12 * k5Params.ca_h * k5Params.cb_h -
      3 * k5Params.c03 * k5Params.ca_h ^ 2).natDegree ≤ 5 := by
  have hle6 : (-k5Params.c21 * k5Params.cb_h ^ 2 + 2 * k5Params.c12 * k5Params.ca_h * k5Params.cb_h -
      3 * k5Params.c03 * k5Params.ca_h ^ 2).natDegree ≤ 6 := by
    have h1 : (-k5Params.c21 * k5Params.cb_h ^ 2).natDegree ≤ 6 := by
      rw [show -k5Params.c21 * k5Params.cb_h ^ 2 = -(k5Params.c21 * k5Params.cb_h * k5Params.cb_h) by ring,
        Polynomial.natDegree_neg]
      exact natDegree_mul3_le _ _ _ deg2_c21 deg2_cb deg2_cb
    have h2 : (2 * k5Params.c12 * k5Params.ca_h * k5Params.cb_h).natDegree ≤ 6 := by
      rw [show 2 * k5Params.c12 * k5Params.ca_h * k5Params.cb_h = C 2 * (k5Params.c12 * k5Params.ca_h * k5Params.cb_h) by rw [map_ofNat]; ring]
      exact (Polynomial.natDegree_C_mul_le 2 _).trans (natDegree_mul3_le _ _ _ deg2_c12 deg2_ca deg2_cb)
    have h3 : (3 * k5Params.c03 * k5Params.ca_h ^ 2).natDegree ≤ 6 := by
      rw [show 3 * k5Params.c03 * k5Params.ca_h ^ 2 = C 3 * (k5Params.c03 * k5Params.ca_h * k5Params.ca_h) by rw [map_ofNat]; ring]
      exact (Polynomial.natDegree_C_mul_le 3 _).trans (natDegree_mul3_le _ _ _ deg2_c03 deg2_ca deg2_ca)
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le ((Polynomial.natDegree_add_le _ _).trans (max_le h1 h2)) h3)
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  by_cases h6 : n = 6
  · subst h6
    rw [Polynomial.coeff_sub, Polynomial.coeff_add,
      show -k5Params.c21 * k5Params.cb_h ^ 2 = -(k5Params.c21 * k5Params.cb_h * k5Params.cb_h) by ring,
      show 2 * k5Params.c12 * k5Params.ca_h * k5Params.cb_h = C 2 * (k5Params.c12 * k5Params.ca_h * k5Params.cb_h) by rw [map_ofNat]; ring,
      show 3 * k5Params.c03 * k5Params.ca_h ^ 2 = C 3 * (k5Params.c03 * k5Params.ca_h * k5Params.ca_h) by rw [map_ofNat]; ring,
      Polynomial.coeff_neg, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
      coeff_mul_top3 _ _ _ deg2_c21 deg2_cb deg2_cb,
      coeff_mul_top3 _ _ _ deg2_c12 deg2_ca deg2_cb,
      coeff_mul_top3 _ _ _ deg2_c03 deg2_ca deg2_ca]
    simp only [CoverParams.c21, CoverParams.c12, CoverParams.c03, CoverParams.ca_h, CoverParams.cb_h,
      coeff_quadU, CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3]; ring
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

-- Exact decomposition of `remDeg4_P1 * d0 - remDeg4_P0 * d1` as a linear combination of `p4..p0`:
private lemma P1_d0_sub_P0_d1_split {R : Type*} [CommRing R] (q2 q1 q0 d1 d0 p4 p3 p2 p1 p0 : R) :
    remDeg4_P1 q2 q1 q0 p4 p3 p2 p1 * d0 - remDeg4_P0 q2 q1 q0 p4 p3 p2 p0 * d1 =
      ((-q1 ^ 3 + 2 * q2 * q1 * q0) * d0 - (-q1 ^ 2 * q0 + q2 * q0 ^ 2) * d1) * p4 +
      ((q2 * (q1 ^ 2 - q2 * q0)) * d0 - (q2 * q1 * q0) * d1) * p3 +
      ((-q2 ^ 2 * q1) * d0 - (-q2 ^ 2 * q0) * d1) * p2 +
      (q2 ^ 3 * d0) * p1 +
      (-q2 ^ 3 * d1) * p0 := by
  simp only [remDeg4_P1, remDeg4_P0]; ring

-- Bundle of `W1_inf` dual weights `A4[3], A4[4], A3[4], A2[4]`, `HasValGe 5 A1, A0`, and `res_z` valuation!
private lemma W1_inf_weights :
    let d2_2 := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d2_2)
    let d2_1 := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d2_1)
    let d2_0 := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d2_0)
    let d1 := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d1_z)
    let d0 := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d0_z)
    let res := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.res_z)
    let pref := -(HahnSeries.single (-1 : ℤ) (1 : K5) ^ 3 * W1_inf * evalInvT k5Params.cb_h ^ 4) /
      (81 * HahnSeries.C k5Params.Av0 * (2 * W1_inf + evalInvT k5Params.bW) * evalInvT k5Params.Q5_z ^ 3 * res)
    let A4 := pref * ((-d2_1 ^ 3 + 2 * d2_2 * d2_1 * d2_0) * d0 - (-d2_1 ^ 2 * d2_0 + d2_2 * d2_0 ^ 2) * d1)
    let A3 := pref * ((d2_2 * (d2_1 ^ 2 - d2_2 * d2_0)) * d0 - (d2_2 * d2_1 * d2_0) * d1)
    let A2 := pref * ((-d2_2 ^ 2 * d2_1) * d0 - (-d2_2 ^ 2 * d2_0) * d1)
    let A1 := pref * (d2_2 ^ 3 * d0)
    let A0 := pref * (-d2_2 ^ 3 * d1)
    let S3Q := S_K - 3 * Q_K; let T59 := 5 * T_K - 9
    ValDual 3 A4
      ⟨-(279006525 / 64 : K5) * T_K * T59 ^ 2 / (S3Q ^ 8 * L_K),
       (13286025 / 12544 : K5) * T_K * T59 ^ 2 * P44_fn S_K Q_K T_K / (S3Q ^ 11 * L_K ^ 2)⟩ ∧
    ValLead 4 A3 ((531441 / 448 : K5) * T_K * T59 * (35 * S_K * T_K + 133 * S_K - 420 * Q_K + 225 * T_K - 45) / S3Q ^ 8) ∧
    ValLead 4 A2 (-(177147 / 400 : K5) * T_K / S3Q ^ 5) ∧
    HasValGe 5 A1 ∧ HasValGe 5 A0 ∧
    HasValGe (-32) res ∧ res.coeff (-32) ≠ 0 := by
  intro d2_2 d2_1 d2_0 d1 d0 res pref A4 A3 A2 A1 A0 S3Q T59
  have hS3Q := S_K_sub_3Q_ne; have hL := L_K_ne_zero; have hT59 := fiveT_sub_9_ne
  set Bv2 : K5 := w1_Bv2 S_K Q_K
  set Bv1 : K5 := w1_Bv1 S_K Q_K T_K
  set Cv0 : K5 := w1_Cv0 T_K
  have hBv2_eq : k5Params.Bv2 = Bv2 := by
    simp only [CoverParams.Bv2, CoverParams.inv243, k5Params_inv3, k5Params_S, k5Params_Q, Bv2, w1_Bv2]; ring
  have hBv1_eq : k5Params.Bv1 = Bv1 := by
    simp only [CoverParams.Bv1, CoverParams.inv9, CoverParams.inv27, CoverParams.inv243, k5Params_inv3,
      k5Params_inv7, k5Params_S, k5Params_Q, k5Params_T, Bv1, w1_Bv1]; ring
  have hCv0_eq : k5Params.Cv0 = Cv0 := by
    simp only [CoverParams.Cv0, CoverParams.inv243, k5Params_inv3, k5Params_T, Cv0, w1_Cv0]; ring
  set w0 : K5 := w1_w0 S_K Q_K T_K
  set w1 : K5 := w1_w1 S_K Q_K T_K
  have hW_D : ValDual 0 W1_inf (w1_WD S_K Q_K T_K) := by
    simpa only [hCv0_eq, hBv2_eq, hBv1_eq, w1_WD, w1_w0, w1_w1, neg_div] using W1_inf_valDual
  set cbD : Dual K5 := w1_cbD S_K Q_K
  have hcb_D : ValDual (-2) (evalInvT k5Params.cb_h) cbD :=
    (ValDual.of_evalInvT k5Params.cb_h deg2_cb (by omega)).eq_d (by
      ext <;> (simp only [CoverParams.cb_h, coeff_quadU, CoverParams.inv9, CoverParams.inv27,
        k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q, cbD, w1_cbD]; ring))
  have hD22_D : ValDual (-5) d2_2 (w1_D22 S_K Q_K) := by
    simpa only [d2_2, CoverParams.d2_2, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar] using
      ((ValDual.of_evalInvT k5Params.Q5_z k5Params_Q5_z_natDegree_le (by omega)).eq_k (by omega)).eq_d
        (by ext; exact k5Params_Q5_c5_eq; exact k5Params_Q5_c4_eq)
  have hD33_D : ValDual (-7) (PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_3))
      (w1_D33 S_K Q_K) := by
    simpa only [CoverParams.d3_3, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar] using
      ((ValDual.of_evalInvT k5Params.Q7_z k5Params_Q7_z_natDegree_le (by omega)).eq_k (by omega)).eq_d
        (by ext; exact k5Params_Q7_c7_eq; exact k5Params_Q7_c6_eq)
  set c0_0 : K5 := w1_c0_0 T_K
  set k2_0 : K5 := w1_k2_0 T_K
  set k3_0 : K5 := w1_k3_0 K5
  have hc0W_L : ValLead (-2) (PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.c0W)) c0_0 :=
    (evalInvT_toUW_valLead_W1 _ _ _).eq_c (by simp only [CoverParams.c0_V0, CoverParams.inv81, k5Params_inv3, k5Params_T, c0_0, w1_c0_0]; ring)
  have hk2W_L : ValLead (-2) (PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.k2W)) k2_0 :=
    (evalInvT_toUW_valLead_W1 _ _ _).eq_c (by simp only [CoverParams.k2_V0, CoverParams.inv81, k5Params_inv3, k5Params_T, k2_0, w1_k2_0]; ring)
  have hk3W_L : ValLead (-2) (PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.k3W)) k3_0 :=
    (evalInvT_toUW_valLead_W1 _ _ _).eq_c (by simp only [CoverParams.k3_V0, CoverParams.inv243, k5Params_inv3, k3_0, w1_k3_0]; ring)
  have hD21_L : ValLead (-5) d2_1 (w1_D21_v S_K Q_K T_K) := by
    simp only [d2_1, CoverParams.d2_1, PairAlg.map_smul, PairAlg.evalAt_smul]
    have hp := (ValDual.of_evalInvT _ k5Params_p21_natDegree_le (by omega)).toValLead.eq_c k5Params_p21_c3_eq
    exact (hp.mul hc0W_L).eq_k (by omega)
  have hq02_L : ValLead (-2) (evalInvT k5Params.q02) (-(4 / 9 : K5) * S_K + (4 / 3) * Q_K) :=
    (ValDual.of_evalInvT k5Params.q02 deg2_q02 (by omega)).toValLead.eq_c (by
      simp only [CoverParams.q02, coeff_quadU, CoverParams.inv9, k5Params_inv3, k5Params_S, k5Params_Q]; ring)
  have hc03_L : ValLead (-2) (evalInvT k5Params.c03) (4 / 9 : K5) :=
    (ValDual.of_evalInvT k5Params.c03 deg2_c03 (by omega)).toValLead.eq_c (by
      simp only [CoverParams.c03, coeff_quadU, CoverParams.inv9, k5Params_inv3]; ring)
  set D20_v : K5 := w1_D20_v S_K Q_K T_K
  have hD20_L : ValLead (-6) d2_0 D20_v := by
    simp only [d2_0, CoverParams.d2_0, CoverParams.pmul, PairAlg.map_add, PairAlg.map_smul,
      PairAlg.map_mul, PairAlg.map_W, PairAlg.evalAt_add, PairAlg.evalAt_smul,
      PairAlg.evalAt_mul _ _ W1_inf W1_inf_eq, PairAlg.evalAt_W, map_pow]
    exact (((hq02_L.mul (hc0W_L.mul hc0W_L)).eq_k (by omega)).add
      (((hcb_D.toValLead.pow 2).mul (hW_D.toValLead.mul hk2W_L)).eq_k (by omega))).eq_c
        (by dsimp only [D20_v, w1_D20_v, w1_WD, c0_0, k2_0, cbD]; ring)
  have hD20_D : ValDual (-6) d2_0 (w1_D20 S_K Q_K T_K (d2_0.coeff (-5))) := ⟨hD20_L.val, hD20_L.c0, rfl⟩
  have hD32_L : ValLead (-7) (PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_2)) (w1_D32_v S_K Q_K T_K) := by
    simp only [CoverParams.d3_2, PairAlg.map_smul, PairAlg.evalAt_smul]
    have hp := (ValDual.of_evalInvT _ k5Params_p32_natDegree_le (by omega)).toValLead.eq_c k5Params_p32_c5_eq
    exact (hp.mul hc0W_L).eq_k (by omega)
  have hD31_L : ValLead (-7) (PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_1)) (w1_D31_v S_K Q_K T_K) := by
    simp only [CoverParams.d3_1, CoverParams.pmul, PairAlg.map_smul, PairAlg.map_mul,
      PairAlg.evalAt_smul, PairAlg.evalAt_mul _ _ W1_inf W1_inf_eq]
    have hp := (ValDual.of_evalInvT _ k5Params_p31_natDegree_le (by omega)).toValLead.eq_c k5Params_p31_c3_eq
    exact (hp.mul (hc0W_L.mul hc0W_L)).eq_k (by omega) |>.eq_c (by dsimp only [w1_D31_v, c0_0]; ring)
  set D30_v : K5 := w1_D30_v S_K Q_K T_K
  have hD30_L : ValLead (-8) (PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_0)) D30_v := by
    simp only [CoverParams.d3_0, CoverParams.pmul, PairAlg.map_add, PairAlg.map_smul, PairAlg.map_mul,
      PairAlg.map_W, PairAlg.evalAt_add, PairAlg.evalAt_smul, PairAlg.evalAt_mul _ _ W1_inf W1_inf_eq,
      PairAlg.evalAt_W, map_neg, map_pow]
    exact (((hc03_L.neg.mul (hc0W_L.mul (hc0W_L.mul hc0W_L))).eq_k (by omega)).add
      (((hcb_D.toValLead.pow 3).mul ((hW_D.toValLead.mul hW_D.toValLead).mul hk3W_L)).eq_k (by omega))).eq_c
        (by dsimp only [D30_v, w1_D30_v, w1_WD, c0_0, k3_0, cbD]; ring)
  -- `d1` (`ValDual (-18)`), `d0` (`ValLead (-18)`), `res` (`ValDual (-32)`):
  set D22 : Dual K5 := w1_D22 S_K Q_K
  set D33 : Dual K5 := w1_D33 S_K Q_K
  set D20 : Dual K5 := w1_D20 S_K Q_K T_K (d2_0.coeff (-5))
  set D21_v := w1_D21_v S_K Q_K T_K
  set D32_v := w1_D32_v S_K Q_K T_K
  set D31_v := w1_D31_v S_K Q_K T_K
  set diff12_v := w1_diff12_v S_K Q_K T_K
  have hdiff12_L : ValLead (-12)
      (d2_2 * PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_2) -
       d2_1 * PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_3)) diff12_v :=
    ((hD22_D.toValLead.mul hD32_L).eq_k (by omega)).sub ((hD21_L.mul hD33_D.toValLead).eq_k (by omega))
  set d1_main : Dual K5 := w1_d1_main S_K Q_K T_K (d2_0.coeff (-5))
  set d1_sub_v : K5 := w1_d1_sub_v S_K Q_K T_K
  have hd1_D : ValDual (-18) d1 (w1_d1_D S_K Q_K T_K (d2_0.coeff (-5))) := by
    have heq : d1 = -(d2_2 * d2_0 * PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_3)) +
        (d2_2 * (d2_2 * PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_1)) -
         d2_1 * (d2_2 * PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_2) -
                 d2_1 * PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_3))) := by
      simp only [d1, d2_2, d2_1, d2_0, CoverParams.d1_z, CoverParams.pmul, PairAlg.map_sub,
        PairAlg.map_mul, PairAlg.evalAt_sub, PairAlg.evalAt_mul _ _ W1_inf W1_inf_eq]; ring
    rw [heq]
    have hm : ValDual (-18) (-(d2_2 * d2_0 * PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_3))) d1_main :=
      (((hD22_D.mul hD20_D).mul hD33_D).neg).eq_k (by omega)
    have hs : ValLead (-17) (d2_2 * (d2_2 * PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_1)) -
        d2_1 * (d2_2 * PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_2) -
                d2_1 * PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_3))) d1_sub_v :=
      (((hD22_D.toValLead.mul (hD22_D.toValLead.mul hD31_L)).eq_k (by omega)).sub
        ((hD21_L.mul hdiff12_L).eq_k (by omega))).eq_c (by dsimp only [d1_sub_v, w1_d1_sub_v]; ring)
    exact (hm.add_shift1 hs).eq_d (by ext <;> simp only [w1_d1_D, d1_main, d1_sub_v, Dual.add_val, Dual.add_eps, add_zero])
  set d0_v : K5 := w1_d0_v S_K Q_K T_K
  have hd0_L : ValLead (-18) d0 d0_v := by
    have heq : d0 = d2_2 * (d2_2 * PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_0)) -
        d2_0 * (d2_2 * PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_2) -
                d2_1 * PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_3)) := by
      simp only [d0, d2_2, d2_1, d2_0, CoverParams.d0_z, CoverParams.pmul, PairAlg.map_sub,
        PairAlg.map_mul, PairAlg.evalAt_sub, PairAlg.evalAt_mul _ _ W1_inf W1_inf_eq]
    rw [heq]
    exact (((hD22_D.toValLead.mul (hD22_D.toValLead.mul hD30_L)).eq_k (by omega)).sub
      ((hD20_L.mul hdiff12_L).eq_k (by omega))).eq_c (by dsimp only [d0_v, w1_d0_v]; ring)
  set res_main : Dual K5 := w1_res_main S_K Q_K T_K (d2_0.coeff (-5))
  set res_sub_v : K5 := w1_res_sub_v S_K Q_K T_K
  have hres_D : ValDual (-32) res (w1_res_D S_K Q_K T_K (d2_0.coeff (-5))) := by
    set e3 := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_3)
    set e2 := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_2)
    set e1 := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_1)
    set e0 := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_0)
    have hsplit : res = (d2_0 ^ 3 * e3 ^ 2 +
        (-d2_1 * d2_0 ^ 2 * e3 * e2 + d2_2 * d2_0 ^ 2 * e2 ^ 2 -
         2 * d2_2 * d2_0 ^ 2 * e3 * e1 + 3 * d2_2 * d2_1 * d2_0 * e3 * e0 -
         2 * d2_2 ^ 2 * d2_0 * e2 * e0 + d2_2 ^ 3 * e0 ^ 2)) +
        (d2_1 ^ 2 * d2_0 * e3 * e1 - d2_2 * d2_1 * d2_0 * e2 * e1 +
         d2_2 ^ 2 * d2_0 * e1 ^ 2 - d2_1 ^ 3 * e3 * e0 +
         d2_2 * d2_1 ^ 2 * e2 * e0 - d2_2 ^ 2 * d2_1 * e1 * e0) := by
      dsimp only [res, d2_2, d2_1, d2_0, e3, e2, e1, e0]
      rw [CoverParams.res_z, map_syl5Pair, evalAt_syl5Pair _ _ _ _ _ _ _ _ _ W1_inf W1_inf_eq]
      simp only [syl5]; ring
    rw [hsplit]
    have hm : ValDual (-32) (d2_0 ^ 3 * e3 ^ 2) res_main :=
      ((hD20_D.pow 3).mul (hD33_D.pow 2)).eq_k (by omega)
    have hs : ValLead (-31)
        (-d2_1 * d2_0 ^ 2 * e3 * e2 + d2_2 * d2_0 ^ 2 * e2 ^ 2 -
         2 * d2_2 * d2_0 ^ 2 * e3 * e1 + 3 * d2_2 * d2_1 * d2_0 * e3 * e0 -
         2 * d2_2 ^ 2 * d2_0 * e2 * e0 + d2_2 ^ 3 * e0 ^ 2) res_sub_v := by
      have t1 : ValLead (-31) _ _ := ((((hD21_L.neg.mul (hD20_L.pow 2)).mul hD33_D.toValLead).mul hD32_L).eq_k (by omega))
      have t2 : ValLead (-31) _ _ := (((hD22_D.toValLead.mul (hD20_L.pow 2)).mul (hD32_L.pow 2)).eq_k (by omega))
      have t3 : ValLead (-31) _ _ := ((((((ValLead.of_ofNat 2).mul hD22_D.toValLead).mul (hD20_L.pow 2)).mul hD33_D.toValLead).mul hD31_L).eq_k (by omega))
      have t4 : ValLead (-31) _ _ := (((((((ValLead.of_ofNat 3).mul hD22_D.toValLead).mul hD21_L).mul hD20_L).mul hD33_D.toValLead).mul hD30_L).eq_k (by omega))
      have t5 : ValLead (-31) _ _ := ((((((ValLead.of_ofNat 2).mul (hD22_D.toValLead.pow 2)).mul hD20_L).mul hD32_L).mul hD30_L).eq_k (by omega))
      have t6 : ValLead (-31) _ _ := (((hD22_D.toValLead.pow 3).mul (hD30_L.pow 2)).eq_k (by omega))
      exact (((((t1.add t2).sub t3).add t4).sub t5).add t6).eq_c rfl
    have hhi : HasValGe (-30)
        (d2_1 ^ 2 * d2_0 * e3 * e1 - d2_2 * d2_1 * d2_0 * e2 * e1 +
         d2_2 ^ 2 * d2_0 * e1 ^ 2 - d2_1 ^ 3 * e3 * e0 +
         d2_2 * d2_1 ^ 2 * e2 * e0 - d2_2 ^ 2 * d2_1 * e1 * e0) := by
      have r1 : HasValGe (-30) _ := (((((hD21_L.val.pow 2).mul hD20_L.val).mul hD33_D.val).mul hD31_L.val).mono (by omega))
      have r2 : HasValGe (-30) _ := (((((hD22_D.val.mul hD21_L.val).mul hD20_L.val).mul hD32_L.val).mul hD31_L.val).mono (by omega))
      have r3 : HasValGe (-30) _ := ((((hD22_D.val.pow 2).mul hD20_L.val).mul (hD31_L.val.pow 2)).mono (by omega))
      have r4 : HasValGe (-30) _ := ((((hD21_L.val.pow 3).mul hD33_D.val).mul hD30_L.val).mono (by omega))
      have r5 : HasValGe (-30) _ := (((((hD22_D.val.mul (hD21_L.val.pow 2)).mul hD32_L.val).mul hD30_L.val)).mono (by omega))
      have r6 : HasValGe (-30) _ := (((((hD22_D.val.pow 2).mul hD21_L.val).mul hD31_L.val).mul hD30_L.val).mono (by omega))
      exact ((((r1.sub r2).add r3).sub r4).add r5).sub r6
    exact ((hm.add_shift1 hs).add_high hhi).eq_d (by ext <;> simp only [w1_res_D, res_main, res_sub_v, Dual.add_val, Dual.add_eps, add_zero])
  -- Combine `pref`, `A4`, `A3`, `A2`, `A1`, `A0` using `W1_inf_weights_alg`!
  obtain ⟨hres_val_eq, hden_ne, hA4_eq, hA3_eq, hA2_eq⟩ :=
    W1_inf_weights_alg S_K Q_K T_K (d2_0.coeff (-5)) hS3Q hL hT59
  have h81Av_D : ValDual (-2) (81 * HahnSeries.C k5Params.Av0 * (2 * W1_inf + evalInvT k5Params.bW))
      (Dual.C (81 : K5) * ⟨Bv2, Bv1⟩) := by
    have heq : 81 * HahnSeries.C k5Params.Av0 * (2 * W1_inf + evalInvT k5Params.bW) =
        HahnSeries.C (81 : K5) * evalInvT k5Params.Bv + 162 * HahnSeries.C k5Params.Av0 * W1_inf := by
      have hAv : HahnSeries.C k5Params.Av0 * evalInvT k5Params.bW = evalInvT k5Params.Bv := by
        rw [CoverParams.bW, map_mul, evalInvT_C, ← mul_assoc, ← map_mul, k5Params_Av0_mul_inv, map_one, one_mul]
      rw [show HahnSeries.C (81 : K5) = (81 : LaurentSeries K5) by rw [map_ofNat]]
      linear_combination 81 * hAv
    rw [heq]
    have hBv_D : ValDual (-2) (evalInvT k5Params.Bv) ⟨Bv2, Bv1⟩ :=
      ((ValDual.of_evalInvT k5Params.Bv (natDegree_quadU_le _ _ _) (by omega)).eq_k (by omega)).eq_d (by
        ext <;> simp only [CoverParams.Bv, coeff_quadU, hBv2_eq, hBv1_eq])
    have hhi : HasValGe 0 (162 * HahnSeries.C k5Params.Av0 * W1_inf) :=
      (((HasValGe.of_ofNat 162).mul (HasValGe.of_C _)).mul HasValGe_W1_inf).mono (by omega)
    exact (((ValDual.of_C (81 : K5)).mul hBv_D).eq_k (by omega)).add_high hhi
  set num_pref_D : Dual K5 := w1_num_pref S_K Q_K T_K
  set den_pref_D : Dual K5 := w1_den_pref S_K Q_K T_K (d2_0.coeff (-5))
  have hnum_pref_D : ValDual (-11) (-(HahnSeries.single (-1 : ℤ) (1 : K5) ^ 3 * W1_inf * evalInvT k5Params.cb_h ^ 4)) num_pref_D := by
    have hU3 : ValDual (-3) (HahnSeries.single (-1 : ℤ) (1 : K5) ^ 3) (Dual.C 1) :=
      ((ValDual.of_single (-1) 1).pow 3).eq_k (by omega) |>.eq_d (by rw [← map_pow, one_pow])
    exact (((hU3.mul hW_D).mul (hcb_D.pow 4)).neg).eq_k (by omega) |>.eq_d (by dsimp only [num_pref_D, w1_num_pref]; rw [map_one, one_mul])
  have hden_pref_D : ValDual (-49)
      (81 * HahnSeries.C k5Params.Av0 * (2 * W1_inf + evalInvT k5Params.bW) * evalInvT k5Params.Q5_z ^ 3 * res) den_pref_D := by
    have hQ5_D : ValDual (-5) (evalInvT k5Params.Q5_z) D22 := by
      simpa only [d2_2, CoverParams.d2_2, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar] using hD22_D
    exact (((h81Av_D.mul (hQ5_D.pow 3)).mul hres_D)).eq_k (by omega)
  have hpref_D : ValDual 38 pref (num_pref_D * ⟨den_pref_D.val⁻¹, -den_pref_D.eps / den_pref_D.val ^ 2⟩) :=
    (hnum_pref_D.div_of_ne hden_pref_D hden_ne).eq_k (by omega)
  -- `A4`: `ValDual 3`!
  have hP0_4_D : ValDual (-17) (-d2_1 ^ 2 * d2_0 + d2_2 * d2_0 ^ 2)
      (w1_P0_4_D S_K Q_K T_K (d2_0.coeff (-5))) := by
    rw [add_comm]
    have hm : ValDual (-17) _ _ := (hD22_D.mul (hD20_D.pow 2)).eq_k (by omega)
    have hs : ValLead (-16) _ _ := (((hD21_L.pow 2).neg.mul hD20_L).eq_k (by omega))
    exact (hm.add_shift1 hs).eq_d (by ext <;> simp only [w1_P0_4_D, Dual.add_val, Dual.add_eps, add_zero] <;> ring)
  have hP1_4_L : ValLead (-16) (-d2_1 ^ 3 + 2 * d2_2 * d2_1 * d2_0) (w1_P1_4_v S_K Q_K T_K) := by
    rw [add_comm]
    have hm : ValLead (-16) (2 * d2_2 * d2_1 * d2_0) (w1_P1_4_v S_K Q_K T_K) :=
      ((((ValLead.of_ofNat 2).mul hD22_D.toValLead).mul hD21_L).mul hD20_L).eq_k (by omega)
    have hhi : HasValGe (-15) (-d2_1 ^ 3) := (hD21_L.val.pow 3).neg.mono (by omega)
    exact hm.add_high hhi
  have hC4_D : ValDual (-35) ((-d2_1 ^ 3 + 2 * d2_2 * d2_1 * d2_0) * d0 - (-d2_1 ^ 2 * d2_0 + d2_2 * d2_0 ^ 2) * d1)
      (w1_C4_D S_K Q_K T_K (d2_0.coeff (-5))) := by
    rw [sub_eq_add_neg, add_comm]
    have hm : ValDual (-35) _ _ := (hP0_4_D.mul hd1_D).neg.eq_k (by omega)
    have hs : ValLead (-34) _ _ := (hP1_4_L.mul hd0_L).eq_k (by omega)
    exact (hm.add_shift1 hs).eq_d (by ext <;> simp only [w1_C4_D, d0_v, Dual.add_val, Dual.add_eps, Dual.neg_val, Dual.neg_eps, add_zero])
  have hA4_D : ValDual 3 A4 ⟨w1_A4_3 S_K Q_K T_K, w1_A4_4 S_K Q_K T_K⟩ := by
    refine ((hpref_D.mul hC4_D).eq_k (by omega)).eq_d ?_
    rw [mul_right_comm]
    exact (dual_div_eq_iff _ den_pref_D _ hden_ne).mpr hA4_eq
  -- `A3`: `ValLead 4`!
  have hA3_L : ValLead 4 A3 (w1_A3_4 S_K Q_K T_K) := by
    have hP1_3 : ValLead (-16) (d2_2 * (d2_1 ^ 2 - d2_2 * d2_0)) (-D22.val ^ 2 * D20_v) := by
      have hsub : d2_2 * (d2_1 ^ 2 - d2_2 * d2_0) = -(d2_2 ^ 2 * d2_0) + d2_2 * d2_1 ^ 2 := by ring
      rw [hsub]
      have hm : ValLead (-16) (-(d2_2 ^ 2 * d2_0)) (-D22.val ^ 2 * D20_v) :=
        (((hD22_D.toValLead.pow 2).mul hD20_L).neg.eq_k (by omega)).eq_c (by ring)
      exact hm.add_high ((hD22_D.val.mul (hD21_L.val.pow 2)).mono (by omega))
    have hP0_3 : ValLead (-16) (d2_2 * d2_1 * d2_0) (D22.val * D21_v * D20_v) :=
      ((hD22_D.toValLead.mul hD21_L).mul hD20_L).eq_k (by omega)
    have hC3 : ValLead (-34) ((d2_2 * (d2_1 ^ 2 - d2_2 * d2_0)) * d0 - (d2_2 * d2_1 * d2_0) * d1)
        (w1_C3_v S_K Q_K T_K (d2_0.coeff (-5))) :=
      ((hP1_3.mul hd0_L).eq_k (by omega)).sub ((hP0_3.mul hd1_D.toValLead).eq_k (by omega))
    refine ((hpref_D.toValLead.mul hC3).eq_k (by omega)).eq_c ?_
    apply mul_left_cancel₀ hden_ne
    simp only [Dual.mul_val]
    have : den_pref_D.val * (num_pref_D.val * den_pref_D.val⁻¹ * w1_C3_v S_K Q_K T_K (d2_0.coeff (-5))) =
        num_pref_D.val * w1_C3_v S_K Q_K T_K (d2_0.coeff (-5)) := by
      field_simp [hden_ne]
    rw [this]; exact hA3_eq
  -- `A2`: `ValLead 4`!
  have hA2_L : ValLead 4 A2 (w1_A2_4 S_K Q_K T_K) := by
    have hC2 : ValLead (-34) ((-d2_2 ^ 2 * d2_1) * d0 - (-d2_2 ^ 2 * d2_0) * d1)
        (w1_C2_v S_K Q_K T_K (d2_0.coeff (-5))) := by
      have hre : (-d2_2 ^ 2 * d2_1) * d0 - (-d2_2 ^ 2 * d2_0) * d1 =
          (d2_2 ^ 2 * d2_0) * d1 + (-d2_2 ^ 2 * d2_1) * d0 := by ring
      rw [hre]
      exact ((((hD22_D.toValLead.pow 2).mul hD20_L).mul hd1_D.toValLead).eq_k (by omega)).add_high
        ((((hD22_D.val.pow 2).neg.mul hD21_L.val).mul hd0_L.val).mono (by omega))
    refine ((hpref_D.toValLead.mul hC2).eq_k (by omega)).eq_c ?_
    apply mul_left_cancel₀ hden_ne
    simp only [Dual.mul_val]
    have : den_pref_D.val * (num_pref_D.val * den_pref_D.val⁻¹ * w1_C2_v S_K Q_K T_K (d2_0.coeff (-5))) =
        num_pref_D.val * w1_C2_v S_K Q_K T_K (d2_0.coeff (-5)) := by field_simp [hden_ne]
    rw [this]; exact hA2_eq
  have hA1 : HasValGe 5 A1 :=
    (hpref_D.val.mul ((hD22_D.val.pow 3).mul hd0_L.val)).mono (by omega)
  have hA0 : HasValGe 5 A0 :=
    (hpref_D.val.mul ((hD22_D.val.pow 3).neg.mul hd1_D.val)).mono (by omega)
  have hres_ne : res.coeff (-32) ≠ 0 := by
    rw [hres_D.c0, hres_val_eq]
    have hc : -(64000000000000 / 6461081889226673298932241 : K5) ≠ 0 :=
      neg_ne_zero.mpr (div_ne_zero (ofNat_ne_zero 64000000000000) (ofNat_ne_zero 6461081889226673298932241))
    exact mul_ne_zero (mul_ne_zero hc (pow_ne_zero 6 hT59)) (pow_ne_zero 15 hS3Q)
  exact ⟨hA4_D, hA3_L, hA2_L, hA1, hA0, hres_D.val, hres_ne⟩

private lemma res_z_W2_inf_val_ne :
    HasValGe (-41) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.res_z)) ∧
    (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.res_z)).coeff (-41) ≠ 0 := by
  have h2_val : HasValGe (-41) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.res_z)) := by
    -- Extract directly from `HasValGe_evalInvT_nm_z` components or prove cleanly in 20 lines:
    have hw := HasValGe_W2_inf; have hw_eq := W2_inf_eq
    rw [CoverParams.res_z, map_syl5Pair, evalAt_syl5Pair _ _ _ _ _ _ _ _ _ W2_inf hw_eq]
    have hw_c : W2_inf.coeff (-2) = -(k5Params.Bv2 * k5Params.Av0_inv) := by
      rw [W2_inf, HahnSeries.coeff_sub, HahnSeries.coeff_neg, HasValGe_W1_inf (-2) (by omega), sub_zero,
        evalInvT_bW_eq]
      have hmul := (HasValGe.single (-2 : ℤ) (1 : K5)).coeff_mul_min (HasValGe.of_powerSeries bInfPS)
      simp only [add_zero] at hmul
      rw [hmul, HahnSeries.coeff_single_same, one_mul]
      change -(HahnSeries.coeff ((bInfPS : PowerSeries K5) : LaurentSeries K5) (0 : ℕ)) = _
      rw [LaurentSeries.coeff_coe_powerSeries, bInfPS_coeff0]
    have htoUW (v0 v1 v2 : K5) :
        ValLead (-4) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT (k5Params.toUW v0 v1 v2)))
          (v2 * (-(k5Params.Bv2 * k5Params.Av0_inv)) ^ 2) := by
      have heq : PairAlg.evalAt W2_inf (PairAlg.map evalInvT (k5Params.toUW v0 v1 v2)) =
          HahnSeries.C v2 * W2_inf ^ 2 +
          (HahnSeries.C v1 * HahnSeries.single (-1) 1 * W2_inf + HahnSeries.C v0 * HahnSeries.single (-2) 1) := by
        simp only [PairAlg.evalAt, PairAlg.map, CoverParams.toUW, map_sub, map_mul, map_pow,
          evalInvT_C, evalInvT_X, HahnSeries.single_pow]
        have h2p : (2 : ℕ) • (-1 : ℤ) = -2 := by decide
        simp only [one_pow, h2p]; linear_combination -HahnSeries.C v2 * hw_eq
      rw [heq]
      have ht1 : ValLead (-4) (HahnSeries.C v2 * W2_inf ^ 2) (v2 * (-(k5Params.Bv2 * k5Params.Av0_inv)) ^ 2) :=
        ((ValLead.of_C v2).mul ((⟨hw, hw_c⟩ : ValLead (-2) W2_inf _).pow 2)).eq_k (by omega)
      have ht2 : HasValGe (-3) (HahnSeries.C v1 * HahnSeries.single (-1) 1 * W2_inf + HahnSeries.C v0 * HahnSeries.single (-2) 1) :=
        ((((HasValGe.of_C v1).mul (HasValGe.single (-1) 1)).mul hw).mono (by omega)).add
          (((HasValGe.of_C v0).mul (HasValGe.single (-2) 1)).mono (by omega))
      exact ht1.add_high ht2
    have hc0W := htoUW k5Params.c0_V0 k5Params.c0_V1 k5Params.c0_V2
    have hk2W := htoUW k5Params.k2_V0 k5Params.k2_V1 k5Params.k2_V2
    have hk3W := htoUW k5Params.k3_V0 k5Params.k3_V1 k5Params.k3_V2
    have hq2 : HasValGe (-5) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d2_2)) := by
      simpa [CoverParams.d2_2, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar] using
        HasValGe.evalInvT_of_natDegree_le _ k5Params_Q5_z_natDegree_le
    have hq1 : HasValGe (-7) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d2_1)) := by
      rw [CoverParams.d2_1, PairAlg.map_smul, PairAlg.evalAt_smul]
      exact ((HasValGe.evalInvT_of_natDegree_le _ k5Params_p21_natDegree_le).mul hc0W.val).mono (by omega)
    have hcb : ValLead (-2) (evalInvT k5Params.cb_h) (k5Params.cb_h.coeff 2) :=
      (ValDual.of_evalInvT _ deg2_cb (by omega)).toValLead
    have hq02 : ValLead (-2) (evalInvT k5Params.q02) (k5Params.q02.coeff 2) :=
      (ValDual.of_evalInvT _ deg2_q02 (by omega)).toValLead
    have hc03 : ValLead (-2) (evalInvT k5Params.c03) (k5Params.c03.coeff 2) :=
      (ValDual.of_evalInvT _ deg2_c03 (by omega)).toValLead
    have hq0 : HasValGe (-9) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d2_0)) := by
      rw [CoverParams.d2_0, PairAlg.map_add, PairAlg.evalAt_add, PairAlg.map_smul, PairAlg.map_smul,
        PairAlg.evalAt_smul, PairAlg.evalAt_smul, CoverParams.pmul, CoverParams.pmul,
        PairAlg.map_mul, PairAlg.map_mul, PairAlg.evalAt_mul _ _ W2_inf hw_eq,
        PairAlg.evalAt_mul _ _ W2_inf hw_eq, PairAlg.map_W, PairAlg.evalAt_W, map_pow]
      have hL : ValLead (-10) _ _ := ((hq02.mul (hc0W.mul hc0W)).eq_k (by omega)).add
        (((hcb.pow 2).mul ((⟨hw, hw_c⟩ : ValLead (-2) W2_inf _).mul hk2W)).eq_k (by omega))
      refine (hL.eq_c ?_).hasValGe_succ
      simp only [CoverParams.q02, CoverParams.cb_h, CoverParams.c0_V2, CoverParams.k2_V2,
        CoverParams.Bv2, CoverParams.Av0_inv, coeff_quadU, CoverParams.inv4, CoverParams.inv9,
        CoverParams.inv27, CoverParams.inv81, CoverParams.inv243, k5Params_inv2, k5Params_inv3,
        k5Params_invT3, k5Params_S, k5Params_Q, k5Params_T]
      have hT := T_K_sub_3_ne; field_simp [hT]; ring
    have he3 : HasValGe (-7) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d3_3)) := by
      simpa [CoverParams.d3_3, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar] using
        HasValGe.evalInvT_of_natDegree_le _ k5Params_Q7_z_natDegree_le
    have he2 : HasValGe (-9) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d3_2)) := by
      rw [CoverParams.d3_2, PairAlg.map_smul, PairAlg.evalAt_smul]
      exact ((HasValGe.evalInvT_of_natDegree_le _ k5Params_p32_natDegree_le).mul hc0W.val).mono (by omega)
    have he1 : HasValGe (-11) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d3_1)) := by
      rw [CoverParams.d3_1, PairAlg.map_smul, PairAlg.evalAt_smul, CoverParams.pmul,
        PairAlg.map_mul, PairAlg.evalAt_mul _ _ W2_inf hw_eq]
      exact ((HasValGe.evalInvT_of_natDegree_le _ k5Params_p31_natDegree_le).mul (hc0W.val.mul hc0W.val)).mono (by omega)
    have he0 : HasValGe (-13) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d3_0)) := by
      rw [CoverParams.d3_0, PairAlg.map_add, PairAlg.evalAt_add, PairAlg.map_smul, PairAlg.map_smul,
        PairAlg.evalAt_smul, PairAlg.evalAt_smul, CoverParams.pmul, CoverParams.pmul,
        CoverParams.pmul, CoverParams.pmul, PairAlg.map_mul, PairAlg.map_mul, PairAlg.map_mul,
        PairAlg.map_mul, PairAlg.evalAt_mul _ _ W2_inf hw_eq, PairAlg.evalAt_mul _ _ W2_inf hw_eq,
        PairAlg.evalAt_mul _ _ W2_inf hw_eq, PairAlg.evalAt_mul _ _ W2_inf hw_eq, PairAlg.map_W,
        PairAlg.evalAt_W, map_neg, map_pow]
      have hL : ValLead (-14) _ _ := ((hc03.neg.mul (hc0W.mul (hc0W.mul hc0W))).eq_k (by omega)).add
        (((hcb.pow 3).mul (((⟨hw, hw_c⟩ : ValLead (-2) W2_inf _).mul ⟨hw, hw_c⟩).mul hk3W)).eq_k (by omega))
      refine (hL.eq_c ?_).hasValGe_succ
      simp only [CoverParams.c03, CoverParams.cb_h, CoverParams.c0_V2, CoverParams.k3_V2,
        CoverParams.Bv2, CoverParams.Av0_inv, coeff_quadU, CoverParams.inv4, CoverParams.inv9,
        CoverParams.inv27, CoverParams.inv81, CoverParams.inv243, k5Params_inv2, k5Params_inv3,
        k5Params_invT3, k5Params_S, k5Params_Q, k5Params_T]
      have hT := T_K_sub_3_ne; field_simp [hT]; ring
    exact HasValGe.syl5 hq2 hq1 hq0 he3 he2 he1 he0
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  refine ⟨h2_val, ?_⟩
  have h1_val : HasValGe (-32) (PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.res_z)) :=
    W1_inf_weights.2.2.2.2.2.1
  have hnm : evalInvT k5Params.nm_z =
      PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.res_z) *
      PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.res_z) := by
    rw [CoverParams.nm_z, CoverParams.pnm, PairAlg.map_nm]
    exact PairAlg.evalAt_nm _ _ W1_inf W2_inf W1_W2_inf_sum W1_W2_inf_prod _
  have hc73 : k5Params.nm_z.coeff 73 = lc34_K5 := by
    rw [nm_z_K5_factor]
    have hcbm_monic : cb_h_m_K5.Monic := cb_h_m_loc_spec.1.map LocK5.subtype
    have hcbm_deg : cb_h_m_K5.natDegree = 2 := by
      rw [cb_h_m_K5, cb_h_m_loc_spec.1.natDegree_map, cb_h_m_loc_spec.2.1]
    have hM : (X ^ 15 * cb_h_m_K5 ^ 12 * P34_K5).Monic :=
      ((monic_X_pow 15).mul (hcbm_monic.pow 12)).mul P34_K5_monic
    have hdeg : (X ^ 15 * cb_h_m_K5 ^ 12 * P34_K5).natDegree = 73 := by
      have h1 : (X ^ 15 * cb_h_m_K5 ^ 12).Monic := (monic_X_pow 15).mul (hcbm_monic.pow 12)
      rw [h1.natDegree_mul' P34_K5_monic.ne_zero, P34_K5_natDegree,
        (monic_X_pow 15).natDegree_mul' (hcbm_monic.pow 12).ne_zero,
        Polynomial.natDegree_X_pow, hcbm_monic.natDegree_pow, hcbm_deg]
    rw [show C lc34_K5 * X ^ 15 * cb_h_m_K5 ^ 12 * P34_K5 =
        C lc34_K5 * (X ^ 15 * cb_h_m_K5 ^ 12 * P34_K5) by ring,
      Polynomial.coeff_C_mul, ← hdeg, hM.coeff_natDegree, mul_one]
  have hprod : (evalInvT k5Params.nm_z).coeff (-73) =
      (PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.res_z)).coeff (-32) *
      (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.res_z)).coeff (-41) := by
    rw [hnm, show (-73 : ℤ) = -32 + -41 by omega, h1_val.coeff_mul_min h2_val]
  rw [show (-73 : ℤ) = -((73 : ℕ) : ℤ) by omega, evalInvT_coeff_neg, hc73] at hprod
  intro h0; rw [h0, mul_zero] at hprod; exact lc34_K5_ne_zero hprod

/-! ### Section 4: Branch 2 (`W2_inf`) Vanishing `(br2_inf eta_AC).coeff 1 = 0` -/

private lemma numM_Uk_valLead (k : Fin 4) (mi : Fin 10)
    {a_s b_s ξS_s ξQ_s : LaurentSeries K5} {a0 b0 ξS0 ξQ0 : K5}
    (ha_L : ValLead 0 a_s a0) (hb_L : ValLead 0 b_s b0)
    (hξS_L : ValLead 0 ξS_s ξS0) (hξQ_L : ValLead 0 ξQ_s ξQ0) :
    ValLead 0 (numM_Uk k mi a_s b_s ξS_s ξQ_s) (numM_Uk k mi a0 b0 ξS0 ξQ0) := by
  have hC (r : K5) {f : LaurentSeries K5} {v : K5} (hf : ValLead 0 f v) :
      ValLead 0 (HahnSeries.C r * f) (r * v) := ((ValLead.of_C r).mul hf).eq_k (by omega)
  have hN (n : ℕ) [n.AtLeastTwo] {f : LaurentSeries K5} {v : K5} (hf : ValLead 0 f v) :
      ValLead 0 ((no_index (OfNat.ofNat n) : LaurentSeries K5) * f) ((no_index (OfNat.ofNat n) : K5) * v) :=
    ((ValLead.of_ofNat n).mul hf).eq_k (by omega)
  have h0_L : ValLead 0 (0 : LaurentSeries K5) (0 : K5) := by simpa only [map_zero] using ValLead.of_C (0 : K5)
  have h1_L : ValLead 0 (1 : LaurentSeries K5) (1 : K5) := by simpa only [map_one] using ValLead.of_C (1 : K5)
  have hS2 {s q : LaurentSeries K5} {s0 q0 : K5} (hs : ValLead 0 s s0) (hq : ValLead 0 q q0) :
      ValLead 0 (dHS_2 s q) (dHS_2 s0 q0) := by
    unfold dHS_2
    simpa only [map_div₀, map_neg, map_ofNat] using
      hC (-(4 / 81 : K5)) (((hs.sub (hN 3 hq)).pow 2).eq_k (by omega))
  have hS1 {s q : LaurentSeries K5} {s0 q0 : K5} (hs : ValLead 0 s s0) (hq : ValLead 0 q q0) :
      ValLead 0 (dHS_1 s q) (dHS_1 s0 q0) := by
    unfold dHS_1
    simpa only [map_div₀, map_neg, map_ofNat, mul_assoc] using
      ((hC (143 / 81 : K5) ((hs.pow 2).eq_k (by omega))).sub
        (hC (184 / 27 : K5) ((hs.mul hq).eq_k (by omega)))).add
        (hC (52 / 9 : K5) ((hq.pow 2).eq_k (by omega)))
  have hS0 {s q : LaurentSeries K5} {s0 q0 : K5} (hs : ValLead 0 s s0) (hq : ValLead 0 q q0) :
      ValLead 0 (dHS_0 s q) (dHS_0 s0 q0) := by
    unfold dHS_0
    simpa only [map_div₀, map_neg, map_ofNat, mul_assoc] using
      (hC (-(25 / 243 : K5)) ((hN 5 hs).sub (hN 9 hq))).mul ((hN 15 hs).sub (hN 9 hq)) |>.eq_k (by omega)
  have hQ1 {s q : LaurentSeries K5} {s0 q0 v0 : K5} (hs : ValLead 0 s s0) (hq : ValLead 0 q q0) :
      ValLead 0 (dHQ_1 s q (HahnSeries.C v0)) (dHQ_1 s0 q0 v0) := by
    unfold dHQ_1
    simpa only [map_div₀, map_neg, map_ofNat, mul_assoc] using
      ((((hC (-(92 / 27 : K5)) ((hs.pow 2).eq_k (by omega))).add
        (hC (104 / 9 : K5) ((hs.mul hq).eq_k (by omega)))).sub
        (hC (22 / 3 : K5) ((hq.pow 2).eq_k (by omega)))).add
        (hC (10 / 7 : K5) ((hq.mul (ValLead.of_C v0)).eq_k (by omega)))).add
        (hC (10 / 7 : K5) (((ValLead.of_C v0).pow 2).eq_k (by omega)))
  have hQ0 {s q : LaurentSeries K5} {s0 q0 : K5} (hs : ValLead 0 s s0) (hq : ValLead 0 q q0) :
      ValLead 0 (dHQ_0 s q) (dHQ_0 s0 q0) := by
    unfold dHQ_0
    simpa only [map_div₀, map_neg, map_ofNat, mul_assoc] using
      ((hC (50 / 27 : K5) hs).mul ((hN 5 hs).sub (hN 9 hq))).eq_k (by omega)
  have hm3 {s1 q1 s2 q2 : LaurentSeries K5} {s10 q10 v1 s20 q20 v2 : K5}
      (h1 : ValLead 0 s1 s10) (hq1 : ValLead 0 q1 q10) (h2 : ValLead 0 s2 s20) (hq2 : ValLead 0 q2 q20) :
      ValLead 0 (minor_U3 s1 q1 (HahnSeries.C v1) s2 q2 (HahnSeries.C v2)) (minor_U3 s10 q10 v1 s20 q20 v2) :=
    (((hS2 h1 hq1).mul ((hQ1 h2 hq2).add (hN 3 (hS1 h2 hq2)))).eq_k (by omega)).sub
      (((hS2 h2 hq2).mul ((hQ1 h1 hq1).add (hN 3 (hS1 h1 hq1)))).eq_k (by omega))
  have hm2 {s1 q1 s2 q2 : LaurentSeries K5} {s10 q10 v1 s20 q20 v2 : K5}
      (h1 : ValLead 0 s1 s10) (hq1 : ValLead 0 q1 q10) (h2 : ValLead 0 s2 s20) (hq2 : ValLead 0 q2 q20) :
      ValLead 0 (minor_U2 s1 q1 (HahnSeries.C v1) s2 q2 (HahnSeries.C v2)) (minor_U2 s10 q10 v1 s20 q20 v2) :=
    (((((hS2 h1 hq1).mul ((hQ0 h2 hq2).add (hN 3 (hS0 h2 hq2)))).eq_k (by omega)).sub
      (((hS2 h2 hq2).mul ((hQ0 h1 hq1).add (hN 3 (hS0 h1 hq1)))).eq_k (by omega))).add
      (((hS1 h1 hq1).mul (hQ1 h2 hq2)).eq_k (by omega))).sub
      (((hS1 h2 hq2).mul (hQ1 h1 hq1)).eq_k (by omega))
  have hm1 {s1 q1 s2 q2 : LaurentSeries K5} {s10 q10 v1 s20 q20 v2 : K5}
      (h1 : ValLead 0 s1 s10) (hq1 : ValLead 0 q1 q10) (h2 : ValLead 0 s2 s20) (hq2 : ValLead 0 q2 q20) :
      ValLead 0 (minor_U1 s1 q1 (HahnSeries.C v1) s2 q2 (HahnSeries.C v2)) (minor_U1 s10 q10 v1 s20 q20 v2) :=
    (((((hS1 h1 hq1).mul (hQ0 h2 hq2)).eq_k (by omega)).sub
      (((hS1 h2 hq2).mul (hQ0 h1 hq1)).eq_k (by omega))).add
      (((hS0 h1 hq1).mul (hQ1 h2 hq2)).eq_k (by omega))).sub
      (((hS0 h2 hq2).mul (hQ1 h1 hq1)).eq_k (by omega))
  have hm0 {s1 q1 s2 q2 : LaurentSeries K5} {s10 q10 s20 q20 : K5}
      (h1 : ValLead 0 s1 s10) (hq1 : ValLead 0 q1 q10) (h2 : ValLead 0 s2 s20) (hq2 : ValLead 0 q2 q20) :
      ValLead 0 (minor_U0 s1 q1 s2 q2) (minor_U0 s10 q10 s20 q20) :=
    (((hS0 h1 hq1).mul (hQ0 h2 hq2)).eq_k (by omega)).sub (((hS0 h2 hq2).mul (hQ0 h1 hq1)).eq_k (by omega))
  have htriples {d10s d20s d21s : LaurentSeries K5} {d100 d200 d210 : K5}
      (hd10 : ValLead 0 d10s d100) (hd20 : ValLead 0 d20s d200) (hd21 : ValLead 0 d21s d210) :
      ValLead 0
        (let (m2, m1, m0) : LaurentSeries K5 × LaurentSeries K5 × LaurentSeries K5 := match mi with
          | 0 => (a_s ^ 2, 2 * a_s * ξS_s, ξS_s ^ 2)
          | 1 => (a_s * b_s, a_s * ξQ_s + b_s * ξS_s, ξS_s * ξQ_s)
          | 2 => (b_s ^ 2, 2 * b_s * ξQ_s, ξQ_s ^ 2)
          | 3 => (a_s, ξS_s, 0) | 4 => (0, a_s, ξS_s)
          | 5 => (b_s, ξQ_s, 0) | 6 => (0, b_s, ξQ_s)
          | 7 => (1, 0, 0) | 8 => (0, 1, 0) | 9 => (0, 0, 1)
         (1 / 16 : LaurentSeries K5) * (m2 * d10s - m1 * d20s + m0 * d21s))
        (let (m2, m1, m0) : K5 × K5 × K5 := match mi with
          | 0 => (a0 ^ 2, 2 * a0 * ξS0, ξS0 ^ 2)
          | 1 => (a0 * b0, a0 * ξQ0 + b0 * ξS0, ξS0 * ξQ0)
          | 2 => (b0 ^ 2, 2 * b0 * ξQ0, ξQ0 ^ 2)
          | 3 => (a0, ξS0, 0) | 4 => (0, a0, ξS0)
          | 5 => (b0, ξQ0, 0) | 6 => (0, b0, ξQ0)
          | 7 => (1, 0, 0) | 8 => (0, 1, 0) | 9 => (0, 0, 1)
         (1 / 16 : K5) * (m2 * d100 - m1 * d200 + m0 * d210)) := by
    have hcomb {m2 m1 m0 : LaurentSeries K5} {m20 m10 m00 : K5}
        (h2 : ValLead 0 m2 m20) (h1 : ValLead 0 m1 m10) (h0 : ValLead 0 m0 m00) :
        ValLead 0 ((1 / 16 : LaurentSeries K5) * (m2 * d10s - m1 * d20s + m0 * d21s))
          ((1 / 16 : K5) * (m20 * d100 - m10 * d200 + m00 * d210)) := by
      simpa only [map_div₀, map_ofNat, map_one] using
        hC (1 / 16 : K5) ((((h2.mul hd10).eq_k (by omega)).sub ((h1.mul hd20).eq_k (by omega))).add ((h0.mul hd21).eq_k (by omega)))
    fin_cases mi
    · exact hcomb ((ha_L.pow 2).eq_k (by omega)) (((hN 2 ha_L).mul hξS_L).eq_k (by omega)) ((hξS_L.pow 2).eq_k (by omega))
    · exact hcomb ((ha_L.mul hb_L).eq_k (by omega))
        (((ha_L.mul hξQ_L).eq_k (by omega)).add ((hb_L.mul hξS_L).eq_k (by omega))) ((hξS_L.mul hξQ_L).eq_k (by omega))
    · exact hcomb ((hb_L.pow 2).eq_k (by omega)) (((hN 2 hb_L).mul hξQ_L).eq_k (by omega)) ((hξQ_L.pow 2).eq_k (by omega))
    · exact hcomb ha_L hξS_L h0_L
    · exact hcomb h0_L ha_L hξS_L
    · exact hcomb hb_L hξQ_L h0_L
    · exact hcomb h0_L hb_L hξQ_L
    · exact hcomb h1_L h0_L h0_L
    · exact hcomb h0_L h1_L h0_L
    · exact hcomb h0_L h0_L h1_L
  fin_cases k
  · exact htriples
      (((hm0 (ha_L.add hξS_L) (hb_L.add hξQ_L) hξS_L hξQ_L).sub (hm0 ha_L hb_L hξS_L hξQ_L)).sub (hm0 hξS_L hξQ_L hξS_L hξQ_L))
      (hm0 ha_L hb_L hξS_L hξQ_L)
      ((hm0 ha_L hb_L (ha_L.add hξS_L) (hb_L.add hξQ_L)).sub (hm0 ha_L hb_L hξS_L hξQ_L))
  · exact htriples
      (by simpa only [d10_U1, map_div₀, map_ofNat, map_zero, map_one, mul_assoc] using
            (((hm1 (v1 := 0) (v2 := 1) (ha_L.add hξS_L) (hb_L.add hξQ_L) hξS_L hξQ_L).sub
              (hm1 (v1 := 0) (v2 := 1) ha_L hb_L hξS_L hξQ_L)).sub (hm1 (v1 := 0) (v2 := 1) hξS_L hξQ_L hξS_L hξQ_L)).sub
              (hC (10 / 7 : K5) ((hb_L.mul (hS0 hξS_L hξQ_L)).eq_k (by omega))))
      (by simpa only [d20_U1, map_zero, map_one] using hm1 (v1 := 0) (v2 := 1) ha_L hb_L hξS_L hξQ_L)
      (by simpa only [d21_U1, map_div₀, map_ofNat, map_zero, mul_assoc] using
            ((hm1 (v1 := 0) (v2 := 0) ha_L hb_L (ha_L.add hξS_L) (hb_L.add hξQ_L)).sub
              (hm1 (v1 := 0) (v2 := 0) ha_L hb_L hξS_L hξQ_L)).add
              (hC (10 / 7 : K5) ((hb_L.mul (hS0 ha_L hb_L)).eq_k (by omega))))
  · exact htriples
      (by simpa only [d10_U2, map_div₀, map_ofNat, map_zero, map_one, mul_assoc] using
            (((hm2 (v1 := 0) (v2 := 1) (ha_L.add hξS_L) (hb_L.add hξQ_L) hξS_L hξQ_L).sub
              (hm2 (v1 := 0) (v2 := 1) ha_L hb_L hξS_L hξQ_L)).sub (hm2 (v1 := 0) (v2 := 1) hξS_L hξQ_L hξS_L hξQ_L)).sub
              (hC (10 / 7 : K5) ((hb_L.mul (hS1 hξS_L hξQ_L)).eq_k (by omega))))
      (by simpa only [d20_U2, map_zero, map_one] using hm2 (v1 := 0) (v2 := 1) ha_L hb_L hξS_L hξQ_L)
      (by simpa only [d21_U2, map_div₀, map_ofNat, map_zero, mul_assoc] using
            ((hm2 (v1 := 0) (v2 := 0) ha_L hb_L (ha_L.add hξS_L) (hb_L.add hξQ_L)).sub
              (hm2 (v1 := 0) (v2 := 0) ha_L hb_L hξS_L hξQ_L)).add
              (hC (10 / 7 : K5) ((hb_L.mul (hS1 ha_L hb_L)).eq_k (by omega))))
  · exact htriples
      (by simpa only [d10_U3, map_div₀, map_ofNat, map_zero, map_one, mul_assoc] using
            (((hm3 (v1 := 0) (v2 := 1) (ha_L.add hξS_L) (hb_L.add hξQ_L) hξS_L hξQ_L).sub
              (hm3 (v1 := 0) (v2 := 1) ha_L hb_L hξS_L hξQ_L)).sub (hm3 (v1 := 0) (v2 := 1) hξS_L hξQ_L hξS_L hξQ_L)).sub
              (hC (10 / 7 : K5) ((hb_L.mul (hS2 hξS_L hξQ_L)).eq_k (by omega))))
      (by simpa only [d20_U3, map_zero, map_one] using hm3 (v1 := 0) (v2 := 1) ha_L hb_L hξS_L hξQ_L)
      (by simpa only [d21_U3, map_div₀, map_ofNat, map_zero, mul_assoc] using
            ((hm3 (v1 := 0) (v2 := 0) ha_L hb_L (ha_L.add hξS_L) (hb_L.add hξQ_L)).sub
              (hm3 (v1 := 0) (v2 := 0) ha_L hb_L hξS_L hξQ_L)).add
              (hC (10 / 7 : K5) ((hb_L.mul (hS2 ha_L hb_L)).eq_k (by omega))))

private lemma numM_Uk_hasValGe (k : Fin 4) (mi : Fin 10)
    {a_s b_s ξS_s ξQ_s : LaurentSeries K5}
    (ha : HasValGe 0 a_s) (hb : HasValGe 0 b_s)
    (hξS : HasValGe 0 ξS_s) (hξQ : HasValGe 0 ξQ_s) :
    HasValGe 0 (numM_Uk k mi a_s b_s ξS_s ξQ_s) :=
  (numM_Uk_valLead k mi ⟨ha, rfl⟩ ⟨hb, rfl⟩ ⟨hξS, rfl⟩ ⟨hξQ, rfl⟩).val

private lemma br2_inf_g_scaled {W2s U V ca cb c0W : LaurentSeries K5} {w_m2 ca_m2 cb_m2 c0W_m4 : K5}
    (hw_ne : w_m2 ≠ 0) (hcb_ne : cb_m2 ≠ 0)
    (hW_L : ValLead (-2) W2s w_m2) (hU_L : ValLead (-1) U 1) (hV_L : ValLead (-1) V w_m2)
    (hca_L : ValLead (-2) ca ca_m2) (hcb_L : ValLead (-2) cb cb_m2) (hc0W_L : ValLead (-4) c0W c0W_m4) :
    let g : LaurentSeries K5 → LaurentSeries K5 := fun z =>
      P18_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) (z / W2s) (-(ca * z + c0W) / (W2s * cb)) U V
    ∀ c : K5, HasValGe (-7) (g (HahnSeries.single (-2) c)) := by
  intro g c
  set z : LaurentSeries K5 := HahnSeries.single (-2) c
  dsimp only [g]
  rw [P18_of_HahnC_eq]
  set a_s := z / W2s
  set b_s := -(ca * z + c0W) / (W2s * cb)
  set a0 : K5 := c / w_m2
  set b0 : K5 := -(ca_m2 * c + c0W_m4) / (w_m2 * cb_m2)
  have hz_L : ValLead (-2) z c := ValLead.of_single (-2) c
  have ha_L : ValLead 0 a_s a0 := (hz_L.div_of_ne hW_L hw_ne).eq_k (by omega)
  have hb_L : ValLead 0 b_s b0 := by
    have hnum : ValLead (-4) _ _ := (((hca_L.mul hz_L).eq_k (by omega)).add hc0W_L).neg
    have hden : ValLead (-4) _ _ := (hW_L.mul hcb_L).eq_k (by omega)
    exact (hnum.div_of_ne hden (mul_ne_zero hw_ne hcb_ne)).eq_k (by omega)
  set ξS_s := HahnSeries.C S_K - a_s * HahnSeries.C T_K
  set ξQ_s := HahnSeries.C Q_K - b_s * HahnSeries.C T_K
  set ξS0 : K5 := S_K - a0 * T_K
  set ξQ0 : K5 := Q_K - b0 * T_K
  have hξS_L : ValLead 0 ξS_s ξS0 := (ValLead.of_C S_K).sub ((ha_L.mul (ValLead.of_C T_K)).eq_k (by omega))
  have hξQ_L : ValLead 0 ξQ_s ξQ0 := (ValLead.of_C Q_K).sub ((hb_L.mul (ValLead.of_C T_K)).eq_k (by omega))
  -- By `numM_split_UV`, every `numM mi` has `ValLead (-5) (w_m2^2 * numM_Uk 3 mi a0 b0 ξS0 ξQ0)`!
  have hUk_L (k : Fin 4) (mi : Fin 10) :
      ValLead 0 (numM_Uk k mi a_s b_s ξS_s ξQ_s) (numM_Uk k mi a0 b0 ξS0 ξQ0) :=
    numM_Uk_valLead k mi ha_L hb_L hξS_L hξQ_L
  have hnumM_L (mi : Fin 10) : ValLead (-5) (numM mi a_s b_s ξS_s ξQ_s U V) (w_m2 ^ 2 * numM_Uk 3 mi a0 b0 ξS0 ξQ0) := by
    rw [numM_split_UV]
    have hmain : ValLead (-5) (V ^ 2 * (U ^ 3 * numM_Uk 3 mi a_s b_s ξS_s ξQ_s))
        (w_m2 ^ 2 * numM_Uk 3 mi a0 b0 ξS0 ξQ0) :=
      (((hV_L.pow 2).mul ((hU_L.pow 3).mul (hUk_L 3 mi))).eq_k (by omega)).eq_c (by ring)
    have hhi : HasValGe (-4) (V ^ 2 * (U ^ 2 * numM_Uk 2 mi a_s b_s ξS_s ξQ_s +
        U * numM_Uk 1 mi a_s b_s ξS_s ξQ_s + numM_Uk 0 mi a_s b_s ξS_s ξQ_s)) := by
      have h2 := ((hU_L.val.pow 2).mul (hUk_L 2 mi).val).mono (by omega : (-2 : ℤ) ≤ _)
      have h1 := (hU_L.val.mul (hUk_L 1 mi).val).mono (by omega : (-2 : ℤ) ≤ _)
      have h0 := (hUk_L 0 mi).val.mono (by omega : (-2 : ℤ) ≤ _)
      exact ((hV_L.val.pow 2).mul ((h2.add h1).add h0)).mono (by omega)
    have hre : V ^ 2 * (U ^ 3 * numM_Uk 3 mi a_s b_s ξS_s ξQ_s + U ^ 2 * numM_Uk 2 mi a_s b_s ξS_s ξQ_s +
        U * numM_Uk 1 mi a_s b_s ξS_s ξQ_s + numM_Uk 0 mi a_s b_s ξS_s ξQ_s) =
        V ^ 2 * (U ^ 3 * numM_Uk 3 mi a_s b_s ξS_s ξQ_s) +
        V ^ 2 * (U ^ 2 * numM_Uk 2 mi a_s b_s ξS_s ξQ_s + U * numM_Uk 1 mi a_s b_s ξS_s ξQ_s +
          numM_Uk 0 mi a_s b_s ξS_s ξQ_s) := by ring
    rw [hre]; exact hmain.add_high hhi
  have hm5 (i : Fin 10) : HasValGe (-5) (numM i a_s b_s ξS_s ξQ_s U V) := (hnumM_L i).val
  have hsc5 (r : K5) {f : LaurentSeries K5} (hf : HasValGe (-5) f) : HasValGe (-5) (HahnSeries.C r * f) :=
    ((HasValGe.of_C r).mul hf).mono (by omega)
  have hnat5 (n : ℕ) [n.AtLeastTwo] {f : LaurentSeries K5} (hf : HasValGe (-5) f) :
      HasValGe (-5) ((no_index (OfNat.ofNat n) : LaurentSeries K5) * f) :=
    ((HasValGe.of_ofNat n).mul hf).mono (by omega)
  have hp5 (i j : Fin 10) : HasValGe (-5) (5 * numM i a_s b_s ξS_s ξQ_s U V - 9 * numM j a_s b_s ξS_s ξQ_s U V) :=
    (hnat5 5 (hm5 i)).sub (hnat5 9 (hm5 j))
  have hA0U_5 : HasValGe (-5) (A_0U a_s b_s ξS_s ξQ_s U V) := by
    unfold A_0U
    simpa only [map_div₀, map_neg, map_ofNat] using
      (((hsc5 (-(19708 / 1257375 : K5)) (hp5 0 1)).add (hsc5 (1472 / 1257375 : K5) (hp5 1 2))).sub
        (hsc5 (16 / 729 : K5) (hp5 3 5))).add (hsc5 (188 / 2025 : K5) (hp5 4 6))
  have hA0V_5 : HasValGe (-5) (A_0V a_s b_s ξS_s ξQ_s U V) := by
    unfold A_0V
    simpa only [map_div₀, map_neg, map_ofNat] using
      (((hsc5 (-(892 / 3645 : K5)) (hp5 3 4)).add (hsc5 (40 / 81 : K5) (hp5 5 6))).sub
        (hsc5 (112 / 2395 : K5) (hp5 7 8))).add (hsc5 (392 / 11975 : K5) (hp5 8 9))
  have hM0_4 : HasValGe (-4) (A_0U a_s b_s ξS_s ξQ_s U V / U + A_0V a_s b_s ξS_s ξQ_s U V / V) :=
    ((hA0U_5.div_of_lead_ne hU_L.val (hU_L.c0.symm ▸ one_ne_zero)).1.mono (by omega)).add
      ((hA0V_5.div_of_lead_ne hV_L.val (hV_L.c0.symm ▸ hw_ne)).1.mono (by omega))
  have hAX_6 : HasValGe (-6) (A_X a_s b_s ξS_s ξQ_s U V) := by
    unfold A_X
    refine (hU_L.val.mul (?_ : HasValGe (-5) _)).mono (by omega)
    simpa only [map_div₀, map_neg, map_ofNat] using
      ((hsc5 (-(8 / 405 : K5)) (hp5 3 4)).sub (hsc5 (476 / 7185 : K5) (hp5 7 8))).add
        (hsc5 (6916 / 35925 : K5) (hp5 8 9))
  have hAY_6 : HasValGe (-6) (A_Y a_s b_s ξS_s ξQ_s U V) := by
    unfold A_Y
    refine (HasValGe.add (HasValGe.add ?_ ?_) ?_)
    · refine HasValGe.mono (by omega) (?_ : HasValGe (-5) _)
      simpa only [map_div₀, map_neg, map_ofNat] using
        hsc5 (-(100 / 243 : K5)) ((((hnat5 25 (hm5 3)).sub (hnat5 45 (hm5 4))).sub (hnat5 45 (hm5 5))).add (hnat5 81 (hm5 6)))
    · refine (hV_L.val.mul (?_ : HasValGe (-5) _)).mono (by omega)
      simpa only [map_div₀, map_neg, map_ofNat] using
        (((hsc5 (-(907876 / 33949125 : K5)) (hp5 0 1)).add (hsc5 (2258324 / 33949125 : K5) (hp5 1 2))).add
          (hsc5 (8 / 243 : K5) (hp5 3 5))).sub (hsc5 (64 / 675 : K5) (hp5 4 6))
    · have hL5 (r : K5) {f : LaurentSeries K5} {v : K5} (hf : ValLead (-5) f v) :
          ValLead (-5) (HahnSeries.C r * f) (r * v) := ((ValLead.of_C r).mul hf).eq_k (by omega)
      have hN5 (n : ℕ) [n.AtLeastTwo] {f : LaurentSeries K5} {v : K5} (hf : ValLead (-5) f v) :
          ValLead (-5) ((no_index (OfNat.ofNat n) : LaurentSeries K5) * f) ((no_index (OfNat.ofNat n) : K5) * v) :=
        ((ValLead.of_ofNat n).mul hf).eq_k (by omega)
      have hcomb : ValLead (-5)
          (-(123236 / 24249375 : LaurentSeries K5) * (numM 0 a_s b_s ξS_s ξQ_s U V +
            (2790 / 77) * numM 6 a_s b_s ξS_s ξQ_s U V + 28 * numM 8 a_s b_s ξS_s ξQ_s U V -
            (5904 / 77) * numM 9 a_s b_s ξS_s ξQ_s U V) +
           (492944 / 33949125) * (numM 1 a_s b_s ξS_s ξQ_s U V +
            (927 / 77) * numM 6 a_s b_s ξS_s ξQ_s U V + (49 / 5) * numM 8 a_s b_s ξS_s ξQ_s U V -
            (21159 / 770) * numM 9 a_s b_s ξS_s ξQ_s U V)) 0 := by
        have hraw := (hL5 (-(123236 / 24249375 : K5))
          (((((hnumM_L 0).add (hL5 (2790 / 77 : K5) (hnumM_L 6))).add (hN5 28 (hnumM_L 8))).sub
            (hL5 (5904 / 77 : K5) (hnumM_L 9))))).add
          (hL5 (492944 / 33949125 : K5)
          (((((hnumM_L 1).add (hL5 (927 / 77 : K5) (hnumM_L 6))).add (hL5 (49 / 5 : K5) (hnumM_L 8))).sub
            (hL5 (21159 / 770 : K5) (hnumM_L 9)))))
        simp only [map_div₀, map_neg, map_ofNat] at hraw
        refine hraw.eq_c ?_
        have hz := AY_t3_U3_eq_zero a0 b0 ξS0 ξQ0
        linear_combination w_m2 ^ 2 * hz
      exact ((hU_L.val.mul hV_L.val).mul hcomb.hasValGe_succ).mono (by omega)
  -- Now `qX, qY` (`HasValGe (-1)`), `A1, B1, cA1, EB` (`HasValGe (-2)`), `u_of U, v_of V` (`ValLead (-1)`) -> `q1` (`HasValGe (-3)`)!
  have h9_ne : (9 : K5) ≠ 0 := by exact_mod_cast (by decide : (9 : ℕ) ≠ 0)
  have hu_L : ValLead (-1) (u_of U) (1 / 9 : K5) := by
    unfold u_of
    exact ((hU_L.add_high (HasValGe.of_C (-1 : K5))).div_of_ne (ValLead.of_ofNat 9) h9_ne).eq_k (by omega)
      |> fun h => by simpa only [sub_eq_add_neg, map_neg, map_one] using h
  have hv_L : ValLead (-1) (v_of V) (w_m2 / 9) := by
    unfold v_of
    exact ((hV_L.add_high (HasValGe.of_C (-1 : K5))).div_of_ne (ValLead.of_ofNat 9) h9_ne).eq_k (by omega)
      |> fun h => by simpa only [sub_eq_add_neg, map_neg, map_one] using h
  have hbi2 (a00 a01 a10 a11 : K5) :
      HasValGe (-2) (HahnSeries.C a00 + HahnSeries.C a01 * V + HahnSeries.C a10 * U + HahnSeries.C a11 * U * V) :=
    ((((HasValGe.of_C a00).mono (by omega)).add (((HasValGe.of_C a01).mul hV_L.val).mono (by omega))).add
      (((HasValGe.of_C a10).mul hU_L.val).mono (by omega))).add
      ((((HasValGe.of_C a11).mul hU_L.val).mul hV_L.val).mono (by omega))
  have hEB_2 : HasValGe (-2) (EB_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V) := by
    have hbi := EB_bilinear_UV (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V
    have hmap (u0 v0 : K5) : (EB_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) (HahnSeries.C u0) (HahnSeries.C v0) : LaurentSeries K5) =
        HahnSeries.C (EB_of S_K Q_K T_K x_K y_K u0 v0) := by
      simp only [EB_of, W2_of, DX2_of, DY2_of, dF5_fn, br_fn, LX_of, LY_of,
        dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of,
        map_add, map_sub, map_mul, map_div₀, map_pow, map_ofNat, map_zero, map_one]
    have h00 := hmap 0 0; have h01 := hmap 0 1; have h10 := hmap 1 0; have h11 := hmap 1 1
    simp only [map_zero, map_one] at h00 h01 h10 h11
    rw [hbi, h00, h01, h10, h11, ← map_sub, ← map_sub, ← map_sub, ← map_sub, ← map_add]
    exact hbi2 _ _ _ _
  have hQY_2 (i : Fin 3) : HasValGe (-2) (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V i) := by
    have hbi := QY_bilinear_UV (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V i
    have hmap (u0 v0 : K5) : (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) (HahnSeries.C u0) (HahnSeries.C v0) i : LaurentSeries K5) =
        HahnSeries.C (QY_num S_K Q_K T_K x_K y_K u0 v0 i) := by
      fin_cases i <;> simp only [QY_num, Omega_F, dDX2_F, F_contract, dF5_fn, dH0_fn, dDX2_fn, DX2_of, DY2_of,
        om_fn, br_fn, LX_of, LY_of, dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of,
        map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat, map_zero, map_one]
    have h00 := hmap 0 0; have h01 := hmap 0 1; have h10 := hmap 1 0; have h11 := hmap 1 1
    simp only [map_zero, map_one] at h00 h01 h10 h11
    rw [hbi, h00, h01, h10, h11, ← map_sub, ← map_sub, ← map_sub, ← map_sub, ← map_add]
    exact hbi2 _ _ _ _
  have hQX_2 (i : Fin 3) : HasValGe (-2) (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V i) := by
    have hbi := QX_bilinear_UV (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V i
    have hmap (u0 v0 : K5) : (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) (HahnSeries.C u0) (HahnSeries.C v0) i : LaurentSeries K5) =
        HahnSeries.C (QX_num S_K Q_K T_K x_K y_K u0 v0 i) := by
      fin_cases i <;> simp only [QX_num, Omega_F, dDY2_F, F_contract, dF5_fn, dH0_fn, dDY2_fn, DX2_of, DY2_of,
        om_fn, br_fn, LX_of, LY_of, dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of,
        map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat, map_zero, map_one]
    have h00 := hmap 0 0; have h01 := hmap 0 1; have h10 := hmap 1 0; have h11 := hmap 1 1
    simp only [map_zero, map_one] at h00 h01 h10 h11
    rw [hbi, h00, h01, h10, h11, ← map_sub, ← map_sub, ← map_sub, ← map_sub, ← map_add]
    exact hbi2 _ _ _ _
  have hqY_1 : HasValGe (-1) (dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / v_of V) := by
    have hdot : HasValGe (-2) (dot_ab _ a_s b_s) :=
      ((((hQY_2 0).mul ha_L.val).mono (by omega)).add (((hQY_2 1).mul hb_L.val).mono (by omega))).add (hQY_2 2)
    exact (hdot.div_of_lead_ne hv_L.val (hv_L.c0.symm ▸ div_ne_zero hw_ne h9_ne)).1.mono (by omega)
  have hqX_1 : HasValGe (-1) (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / u_of U) := by
    have hdot : HasValGe (-2) (dot_ab _ a_s b_s) :=
      ((((hQX_2 0).mul ha_L.val).mono (by omega)).add (((hQX_2 1).mul hb_L.val).mono (by omega))).add (hQX_2 2)
    exact (hdot.div_of_lead_ne hu_L.val (hu_L.c0.symm ▸ div_ne_zero one_ne_zero h9_ne)).1.mono (by omega)
  have hA1_2 : HasValGe (-2) (A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V) := by
    have heq : A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V =
        HahnSeries.C 0 + HahnSeries.C (A1_of S_K Q_K 0 1) * V + HahnSeries.C 0 * U +
        HahnSeries.C (A1_of S_K Q_K 1 1 - A1_of S_K Q_K 0 1) * U * V := by
      simp only [A1_of, map_sub, map_mul, map_div₀, map_pow, map_ofNat, map_one, map_zero]; ring
    rw [heq]; exact hbi2 _ _ _ _
  have hB1_2 : HasValGe (-2) (B1_of (HahnSeries.C T_K) U V) := by
    have heq : B1_of (HahnSeries.C T_K) U V =
        HahnSeries.C 0 + HahnSeries.C 0 * V + HahnSeries.C (B1_of T_K 1 0) * U +
        HahnSeries.C (B1_of T_K 1 1 - B1_of T_K 1 0) * U * V := by
      simp only [B1_of, map_sub, map_mul, map_div₀, map_pow, map_ofNat, map_one, map_zero]; ring
    rw [heq]; exact hbi2 _ _ _ _
  have hH0_0 : HasValGe 0 (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)) := by
    rw [show H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) = HahnSeries.C (H0_of S_K Q_K T_K) by
      simp only [H0_of, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]]
    exact HasValGe.of_C _
  have hcA1_2 : HasValGe (-2) (cA1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) a_s b_s U V) := by
    have hdA1 (k : Fin 3) : HasValGe (-2) (dA1_fn k (HahnSeries.C S_K) (HahnSeries.C Q_K) U V) := by
      fin_cases k
      · change HasValGe (-2) (dA1_fn 0 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V)
        have heq : dA1_fn 0 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V =
            HahnSeries.C 0 + HahnSeries.C (dA1_fn 0 S_K Q_K 0 1) * V + HahnSeries.C 0 * U +
            HahnSeries.C (dA1_fn 0 S_K Q_K 1 1 - dA1_fn 0 S_K Q_K 0 1) * U * V := by
          simp only [dA1_fn, map_sub, map_mul, map_div₀, map_pow, map_ofNat, map_one, map_zero]; ring
        rw [heq]; exact hbi2 _ _ _ _
      · change HasValGe (-2) (dA1_fn 1 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V)
        have heq : dA1_fn 1 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V =
            HahnSeries.C 0 + HahnSeries.C (dA1_fn 1 S_K Q_K 0 1) * V + HahnSeries.C 0 * U +
            HahnSeries.C (dA1_fn 1 S_K Q_K 1 1 - dA1_fn 1 S_K Q_K 0 1) * U * V := by
          simp only [dA1_fn, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat, map_one, map_zero]; ring
        rw [heq]; exact hbi2 _ _ _ _
      · exact HasValGe.zero (-2)
    have hdH0 (k : Fin 3) : HasValGe 0 (dH0_fn k (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)) := by
      rw [show dH0_fn k (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) = HahnSeries.C (dH0_fn k S_K Q_K T_K) by
        fin_cases k <;> simp only [dH0_fn, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]]
      exact HasValGe.of_C _
    unfold cA1_of
    exact (((((hH0_0.mul (hdA1 0)).mono (k2 := -2) (by omega)).sub ((hA1_2.mul (hdH0 0)).mono (k2 := -2) (by omega))).mul ha_L.val |>.mono (k2 := -2) (by omega)).add
      (((((hH0_0.mul (hdA1 1)).mono (k2 := -2) (by omega)).sub ((hA1_2.mul (hdH0 1)).mono (k2 := -2) (by omega))).mul hb_L.val |>.mono (k2 := -2) (by omega)))).add
      ((((hH0_0.mul (hdA1 2)).mono (k2 := -2) (by omega)).sub ((hA1_2.mul (hdH0 2)).mono (k2 := -2) (by omega))))
  have hq1_3 : HasValGe (-3) _ :=
    (((hH0_0.mul hA1_2).mul hqY_1).mono (k2 := -3) (by omega)).add (((hH0_0.mul hB1_2).mul hqX_1).mono (k2 := -3) (by omega)) |>.add
      (((hcA1_2.div_of_lead_ne hv_L.val (hv_L.c0.symm ▸ div_ne_zero hw_ne h9_ne)).1.mul hEB_2).mono (k2 := -3) (by omega))
  exact ((hM0_4.mul hq1_3).mono (k2 := -7) (by omega)).add
    ((((hAY_6.mul hqY_1).mono (k2 := -7) (by omega)).add ((hAX_6.mul hqX_1).mono (k2 := -7) (by omega))).mul (hH0_0.pow 2) |>.mono (k2 := -7) (by omega))

lemma br2_inf_eta_AC_coeff_one : (br2_inf eta_AC).coeff 1 = 0 := by
  have hbr := branchHom_eta_AC ψinf ψinf_C W2_inf W2_inf_eq_ψinf
  simp only [ψinf_X] at hbr
  have hfP : ψinf.comp toRat = evalInvT := RingHom.ext ψinf_toRat
  simp only [hfP] at hbr
  change br2_inf eta_AC = _ at hbr
  rw [hbr]
  set U := HahnSeries.single (-1 : ℤ) (1 : K5)
  set V := W2_inf / U
  set ca := evalInvT k5Params.ca_h
  set cb := evalInvT k5Params.cb_h
  set c0W := PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.c0W)
  set d2_2 := PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d2_2)
  set d2_1 := PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d2_1)
  set d2_0 := PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d2_0)
  set d1 := PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d1_z)
  set d0 := PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d0_z)
  set res := PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.res_z)
  set g : LaurentSeries K5 → LaurentSeries K5 := fun z =>
    P18_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) (z / W2_inf) (-(ca * z + c0W) / (W2_inf * cb)) U V
  set p := interp4 g
  set P1 := remDeg4_P1 d2_2 d2_1 d2_0 p.1 p.2.1 p.2.2.1 p.2.2.2.1
  set P0 := remDeg4_P0 d2_2 d2_1 d2_0 p.1 p.2.1 p.2.2.1 p.2.2.2.2
  set w_m2 : K5 := -(k5Params.Bv2 * k5Params.Av0_inv)
  have hAi_ne : k5Params.Av0_inv ≠ 0 := fun h => by
    have := k5Params_Av0_mul_inv; rw [h, mul_zero] at this; exact zero_ne_one this
  have hw_ne : w_m2 ≠ 0 := neg_ne_zero.mpr (mul_ne_zero k5Params_Bv2_ne hAi_ne)
  have hw_c : W2_inf.coeff (-2) = w_m2 := by
    rw [W2_inf, HahnSeries.coeff_sub, HahnSeries.coeff_neg, HasValGe_W1_inf (-2) (by omega), sub_zero,
      evalInvT_bW_eq]
    have hmul := (HasValGe.single (-2 : ℤ) (1 : K5)).coeff_mul_min (HasValGe.of_powerSeries bInfPS)
    simp only [add_zero] at hmul
    rw [hmul, HahnSeries.coeff_single_same, one_mul]
    change -(HahnSeries.coeff ((bInfPS : PowerSeries K5) : LaurentSeries K5) (0 : ℕ)) = _
    rw [LaurentSeries.coeff_coe_powerSeries, bInfPS_coeff0]
  have hW_L : ValLead (-2) W2_inf w_m2 := ⟨HasValGe_W2_inf, hw_c⟩
  have hU_L : ValLead (-1) U 1 := ValLead.of_single (-1) 1
  have hV_L : ValLead (-1) V w_m2 := (hW_L.div_of_ne hU_L one_ne_zero).eq_k (by omega) |>.eq_c (div_one w_m2)
  have hca_L : ValLead (-2) ca (k5Params.ca_h.coeff 2) := (ValDual.of_evalInvT _ deg2_ca (by omega)).toValLead
  have hcb_L : ValLead (-2) cb (k5Params.cb_h.coeff 2) := (ValDual.of_evalInvT _ deg2_cb (by omega)).toValLead
  have hcb_ne : k5Params.cb_h.coeff 2 ≠ 0 := by
    have heq : k5Params.cb_h.coeff 2 = (4 / 27 : K5) * (S_K - 3 * Q_K) ^ 2 := by
      simp only [CoverParams.cb_h, coeff_quadU, CoverParams.inv27, CoverParams.inv9, k5Params_inv3, k5Params_S, k5Params_Q]; ring
    rw [heq]
    exact mul_ne_zero (div_ne_zero (by exact_mod_cast (by decide : (4 : ℕ) ≠ 0))
      (by exact_mod_cast (by decide : (27 : ℕ) ≠ 0))) (pow_ne_zero 2 S_K_sub_3Q_ne)
  have htoUW (v0 v1 v2 : K5) :
      ValLead (-4) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT (k5Params.toUW v0 v1 v2))) (v2 * w_m2 ^ 2) := by
    have heq : PairAlg.evalAt W2_inf (PairAlg.map evalInvT (k5Params.toUW v0 v1 v2)) =
        HahnSeries.C v2 * W2_inf ^ 2 +
        (HahnSeries.C v1 * HahnSeries.single (-1) 1 * W2_inf + HahnSeries.C v0 * HahnSeries.single (-2) 1) := by
      simp only [PairAlg.evalAt, PairAlg.map, CoverParams.toUW, map_sub, map_mul, map_pow,
        evalInvT_C, evalInvT_X, HahnSeries.single_pow]
      have h2p : (2 : ℕ) • (-1 : ℤ) = -2 := by decide
      simp only [one_pow, h2p]; linear_combination -HahnSeries.C v2 * W2_inf_eq
    rw [heq]
    exact (((ValLead.of_C v2).mul (hW_L.pow 2)).eq_k (by omega)).add_high
      (((((HasValGe.of_C v1).mul (HasValGe.single (-1) 1)).mul HasValGe_W2_inf).mono (by omega)).add
        (((HasValGe.of_C v0).mul (HasValGe.single (-2) 1)).mono (by omega)))
  have hc0W_L : ValLead (-4) c0W (k5Params.c0_V2 * w_m2 ^ 2) := htoUW _ _ _
  have hk2W_L := htoUW k5Params.k2_V0 k5Params.k2_V1 k5Params.k2_V2
  have hk3W_L := htoUW k5Params.k3_V0 k5Params.k3_V1 k5Params.k3_V2
  have hg_scaled : ∀ c : K5, HasValGe (-7) (g (HahnSeries.single (-2) c)) :=
    br2_inf_g_scaled hw_ne hcb_ne hW_L hU_L hV_L hca_L hcb_L hc0W_L
  have hg_deg4 : IsPolyDeg 4 g := by
    have h := P18_of_isPolyDeg4 (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V (1 / W2_inf) 0 (-ca / (W2_inf * cb)) (-c0W / (W2_inf * cb))
    refine h.congr (fun z => ?_)
    dsimp only [g]
    have hW_ne' : W2_inf ≠ 0 := fun h0 => hw_ne (by rw [← hw_c, h0]; rfl)
    have hcb_ne' : cb ≠ 0 := fun h0 => hcb_ne (by rw [← hcb_L.c0, h0]; rfl)
    have h1 : z / W2_inf = 1 / W2_inf * z + 0 := by ring
    have h2 : -(ca * z + c0W) / (W2_inf * cb) = -ca / (W2_inf * cb) * z + -c0W / (W2_inf * cb) := by
      field_simp [hW_ne', hcb_ne']; ring
    rw [h1, h2]
  obtain ⟨hp4, hp3, hp2, hp1, hp0⟩ := HasValGe.interp4_scaled (s := -2) (k := -7) hg_deg4 hg_scaled
  -- Valuations of `d2_2..0, d3_3..0, d1, d0` along `W2_inf`:
  have hQ5_L : ValLead (-5) (evalInvT k5Params.Q5_z) (Q5_c5 S_K Q_K) :=
    (ValDual.of_evalInvT _ k5Params_Q5_z_natDegree_le (by omega)).toValLead.eq_c k5Params_Q5_c5_eq
  have hq2 : HasValGe (-5) d2_2 := by
    simpa [d2_2, CoverParams.d2_2, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar] using hQ5_L.val
  have hq1 : HasValGe (-7) d2_1 := by
    rw [show d2_1 = evalInvT (-k5Params.q11 * k5Params.cb_h + 2 * k5Params.q02 * k5Params.ca_h) * c0W by
      simp only [d2_1, c0W, CoverParams.d2_1, PairAlg.map_smul, PairAlg.evalAt_smul]]
    exact ((HasValGe.evalInvT_of_natDegree_le _ k5Params_p21_natDegree_le).mul hc0W_L.val).mono (by omega)
  have hq02 : ValLead (-2) (evalInvT k5Params.q02) (k5Params.q02.coeff 2) := (ValDual.of_evalInvT _ deg2_q02 (by omega)).toValLead
  have hc03 : ValLead (-2) (evalInvT k5Params.c03) (k5Params.c03.coeff 2) := (ValDual.of_evalInvT _ deg2_c03 (by omega)).toValLead
  have hq0 : HasValGe (-9) d2_0 := by
    dsimp only [d2_0]
    rw [CoverParams.d2_0, PairAlg.map_add, PairAlg.evalAt_add, PairAlg.map_smul, PairAlg.map_smul,
      PairAlg.evalAt_smul, PairAlg.evalAt_smul, CoverParams.pmul, CoverParams.pmul,
      PairAlg.map_mul, PairAlg.map_mul, PairAlg.evalAt_mul _ _ W2_inf W2_inf_eq,
      PairAlg.evalAt_mul _ _ W2_inf W2_inf_eq, PairAlg.map_W, PairAlg.evalAt_W, map_pow]
    have hL : ValLead (-10) _ _ := ((hq02.mul (hc0W_L.mul hc0W_L)).eq_k (by omega)).add
      (((hcb_L.pow 2).mul (hW_L.mul hk2W_L)).eq_k (by omega))
    refine (hL.eq_c ?_).hasValGe_succ
    simp only [CoverParams.q02, CoverParams.cb_h, CoverParams.c0_V2, CoverParams.k2_V2,
      CoverParams.Bv2, CoverParams.Av0_inv, coeff_quadU, CoverParams.inv4, CoverParams.inv9,
      CoverParams.inv27, CoverParams.inv81, CoverParams.inv243, k5Params_inv2, k5Params_inv3,
      k5Params_invT3, k5Params_S, k5Params_Q, k5Params_T, w_m2]
    have hT := T_K_sub_3_ne; field_simp [hT]; ring
  have he3 : HasValGe (-7) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d3_3)) := by
    simpa [CoverParams.d3_3, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar] using
      HasValGe.evalInvT_of_natDegree_le _ k5Params_Q7_z_natDegree_le
  have he2 : HasValGe (-9) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d3_2)) := by
    rw [CoverParams.d3_2, PairAlg.map_smul, PairAlg.evalAt_smul]
    exact ((HasValGe.evalInvT_of_natDegree_le _ k5Params_p32_natDegree_le).mul hc0W_L.val).mono (by omega)
  have he1 : HasValGe (-11) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d3_1)) := by
    rw [CoverParams.d3_1, PairAlg.map_smul, PairAlg.evalAt_smul, CoverParams.pmul,
      PairAlg.map_mul, PairAlg.evalAt_mul _ _ W2_inf W2_inf_eq]
    exact ((HasValGe.evalInvT_of_natDegree_le _ k5Params_p31_natDegree_le).mul (hc0W_L.val.mul hc0W_L.val)).mono (by omega)
  have he0 : HasValGe (-13) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d3_0)) := by
    rw [CoverParams.d3_0, PairAlg.map_add, PairAlg.evalAt_add, PairAlg.map_smul, PairAlg.map_smul,
      PairAlg.evalAt_smul, PairAlg.evalAt_smul, CoverParams.pmul, CoverParams.pmul,
      CoverParams.pmul, CoverParams.pmul, PairAlg.map_mul, PairAlg.map_mul, PairAlg.map_mul,
      PairAlg.map_mul, PairAlg.evalAt_mul _ _ W2_inf W2_inf_eq, PairAlg.evalAt_mul _ _ W2_inf W2_inf_eq,
      PairAlg.evalAt_mul _ _ W2_inf W2_inf_eq, PairAlg.evalAt_mul _ _ W2_inf W2_inf_eq, PairAlg.map_W,
      PairAlg.evalAt_W, map_neg, map_pow]
    have hL : ValLead (-14) _ _ := ((hc03.neg.mul (hc0W_L.mul (hc0W_L.mul hc0W_L))).eq_k (by omega)).add
      (((hcb_L.pow 3).mul ((hW_L.mul hW_L).mul hk3W_L)).eq_k (by omega))
    refine (hL.eq_c ?_).hasValGe_succ
    simp only [CoverParams.c03, CoverParams.cb_h, CoverParams.c0_V2, CoverParams.k3_V2,
      CoverParams.Bv2, CoverParams.Av0_inv, coeff_quadU, CoverParams.inv4, CoverParams.inv9,
      CoverParams.inv27, CoverParams.inv81, CoverParams.inv243, k5Params_inv2, k5Params_inv3,
      k5Params_invT3, k5Params_S, k5Params_Q, k5Params_T, w_m2]
    have hT := T_K_sub_3_ne; field_simp [hT]; ring
  have hd1 : HasValGe (-21) d1 := by
    simp only [d1, CoverParams.d1_z, CoverParams.pmul, PairAlg.map_sub, PairAlg.map_mul,
      PairAlg.evalAt_sub, PairAlg.evalAt_mul _ _ W2_inf W2_inf_eq]
    have t1 : HasValGe (-16) _ := ((hq2.mul he1).mono (by omega)).sub ((hq0.mul he3).mono (by omega))
    have t2 : HasValGe (-14) _ := ((hq2.mul he2).mono (by omega)).sub ((hq1.mul he3).mono (by omega))
    exact ((hq2.mul t1).mono (by omega)).sub ((hq1.mul t2).mono (by omega))
  have hd0 : HasValGe (-23) d0 := by
    simp only [d0, CoverParams.d0_z, CoverParams.pmul, PairAlg.map_sub, PairAlg.map_mul,
      PairAlg.evalAt_sub, PairAlg.evalAt_mul _ _ W2_inf W2_inf_eq]
    have t1 : HasValGe (-18) _ := (hq2.mul he0).mono (by omega)
    have t2 : HasValGe (-14) _ := ((hq2.mul he2).mono (by omega)).sub ((hq1.mul he3).mono (by omega))
    exact ((hq2.mul t1).mono (by omega)).sub ((hq0.mul t2).mono (by omega))
  have hP1 : HasValGe (-20) P1 := by
    simp only [P1, remDeg4_P1]
    have hr3 : HasValGe (-6) (d2_2 * p.2.1 - d2_1 * p.1) :=
      ((hq2.mul hp3).mono (by omega)).sub ((hq1.mul hp4).mono (by omega))
    have hr2 : HasValGe (-8) (d2_2 * p.2.2.1 - d2_0 * p.1) :=
      ((hq2.mul hp2).mono (by omega)).sub ((hq0.mul hp4).mono (by omega))
    have hs2 : HasValGe (-13) (d2_2 * (d2_2 * p.2.2.1 - d2_0 * p.1) - d2_1 * (d2_2 * p.2.1 - d2_1 * p.1)) :=
      ((hq2.mul hr2).mono (by omega)).sub ((hq1.mul hr3).mono (by omega))
    have hs1 : HasValGe (-15) (d2_2 ^ 2 * p.2.2.2.1 - d2_0 * (d2_2 * p.2.1 - d2_1 * p.1)) :=
      (((hq2.pow 2).mul hp1).mono (by omega)).sub ((hq0.mul hr3).mono (by omega))
    exact ((hq2.mul hs1).mono (by omega)).sub ((hq1.mul hs2).mono (by omega))
  have hP0 : HasValGe (-22) P0 := by
    simp only [P0, remDeg4_P0]
    have hr3 : HasValGe (-6) (d2_2 * p.2.1 - d2_1 * p.1) :=
      ((hq2.mul hp3).mono (by omega)).sub ((hq1.mul hp4).mono (by omega))
    have hr2 : HasValGe (-8) (d2_2 * p.2.2.1 - d2_0 * p.1) :=
      ((hq2.mul hp2).mono (by omega)).sub ((hq0.mul hp4).mono (by omega))
    have hs2 : HasValGe (-13) (d2_2 * (d2_2 * p.2.2.1 - d2_0 * p.1) - d2_1 * (d2_2 * p.2.1 - d2_1 * p.1)) :=
      ((hq2.mul hr2).mono (by omega)).sub ((hq1.mul hr3).mono (by omega))
    exact (((hq2.pow 3).mul hp0).mono (by omega)).sub ((hq0.mul hs2).mono (by omega))
  have hnum : HasValGe (-56) (-(P1 * d0 - P0 * d1) * U ^ 3 * W2_inf * cb ^ 4) := by
    have hsub : HasValGe (-43) (P1 * d0 - P0 * d1) :=
      ((hP1.mul hd0).mono (by omega)).sub ((hP0.mul hd1).mono (by omega))
    exact (((hsub.neg.mul (hU_L.val.pow 3)).mul hW_L.val).mul (hcb_L.val.pow 4)).mono (by omega)
  obtain ⟨hres_val, hres_ne⟩ := res_z_W2_inf_val_ne
  have h2W_L : ValLead (-2) (2 * W2_inf + evalInvT k5Params.bW) w_m2 := by
    have hbW : ValLead (-2) (evalInvT k5Params.bW) (-w_m2) := by
      have hdeg : k5Params.bW.natDegree ≤ 2 := by
        rw [CoverParams.bW]; exact (Polynomial.natDegree_C_mul_le _ _).trans (natDegree_quadU_le _ _ _)
      exact (ValDual.of_evalInvT _ hdeg (by omega)).toValLead.eq_c (by
        simp only [CoverParams.bW, CoverParams.Bv, Polynomial.coeff_C_mul, coeff_quadU, w_m2]; ring)
    exact ((((ValLead.of_ofNat 2).mul hW_L).eq_k (by omega)).add hbW).eq_c (by ring)
  have hden_L : ValLead (-58)
      (81 * HahnSeries.C k5Params.Av0 * (2 * W2_inf + evalInvT k5Params.bW) * evalInvT k5Params.Q5_z ^ 3 * res)
      (81 * k5Params.Av0 * w_m2 * Q5_c5 S_K Q_K ^ 3 * res.coeff (-41)) :=
    (((((ValLead.of_ofNat 81).mul (ValLead.of_C k5Params.Av0)).mul h2W_L).mul (hQ5_L.pow 3)).mul ⟨hres_val, rfl⟩).eq_k
      (by omega)
  have hQ5_ne : Q5_c5 S_K Q_K ≠ 0 := by
    have hfac : Q5_c5 S_K Q_K = (16 / 413343 : K5) * L_K * (S_K - 3 * Q_K) ^ 4 := by
      simp only [Q5_c5, L_K]; ring
    rw [hfac]
    exact mul_ne_zero (mul_ne_zero (div_ne_zero (by exact_mod_cast (by decide : (16 : ℕ) ≠ 0))
      (by exact_mod_cast (by decide : (413343 : ℕ) ≠ 0))) L_K_ne_zero) (pow_ne_zero 4 S_K_sub_3Q_ne)
  have hden_ne : (81 * HahnSeries.C k5Params.Av0 * (2 * W2_inf + evalInvT k5Params.bW) *
      evalInvT k5Params.Q5_z ^ 3 * res).coeff (-58) ≠ 0 := by
    rw [hden_L.c0]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by exact_mod_cast (by decide : (81 : ℕ) ≠ 0))
      k5Params_Av0_ne) hw_ne) (pow_ne_zero 3 hQ5_ne)) hres_ne
  have hquot : HasValGe 2 (-(P1 * d0 - P0 * d1) * U ^ 3 * W2_inf * cb ^ 4 /
      (81 * HahnSeries.C k5Params.Av0 * (2 * W2_inf + evalInvT k5Params.bW) * evalInvT k5Params.Q5_z ^ 3 * res)) :=
    (hnum.div_of_lead_ne hden_L.val hden_ne).1.mono (by omega)
  exact hquot 1 (by omega)

/-! ### Section 5: `Uinf_biv_identity` (`decide +kernel`) & Branch 1 (`W1_inf`) Exact Value -/

private def P44_e : Expr :=
  .add (.add (.add (.add (.add (.num 20510415) (.mul (.num (-45278190)) eT)) (.add (.mul (.num (-135184545)) (.pow eT 2)) (.add (.mul (.num (-13243230)) (.pow eT 3)) (.mul (.num (-496300770)) eQ)))) (.add (.add (.mul (.mul (.num 1002263220) eQ) eT) (.add (.mul (.mul (.num 1619567460) eQ) (.pow eT 2)) (.mul (.mul (.num 61801740) eQ) (.pow eT 3)))) (.add (.mul (.num 1510998300) (.pow eQ 2)) (.add (.mul (.mul (.num (-9227925000)) (.pow eQ 2)) eT) (.mul (.mul (.num (-4613962500)) (.pow eQ 2)) (.pow eT 2)))))) (.add (.add (.add (.mul (.num 4883417910) (.pow eQ 3)) (.mul (.mul (.num 25838190000) (.pow eQ 3)) eT)) (.add (.mul (.num (-20513855880)) (.pow eQ 4)) (.add (.mul (.num 141076404) eS) (.mul (.mul (.num (-302433264)) eS) eT)))) (.add (.add (.mul (.mul (.num (-657628902)) eS) (.pow eT 2)) (.add (.mul (.mul (.num (-22660638)) eS) (.pow eT 3)) (.mul (.mul (.num (-1013761980)) eS) eQ))) (.add (.mul (.mul (.mul (.num 6278958000) eS) eQ) eT) (.add (.mul (.mul (.mul (.num 3978922500) eS) eQ) (.pow eT 2)) (.mul (.mul (.num (-4586695470)) eS) (.pow eQ 2))))))) (.add (.add (.add (.add (.mul (.mul (.mul (.num (-28116396000)) eS) (.pow eQ 2)) eT) (.mul (.mul (.mul (.num (-1389150000)) eS) (.pow eQ 2)) (.pow eT 2))) (.add (.mul (.mul (.num 28084223286) eS) (.pow eQ 3)) (.add (.mul (.mul (.mul (.num 2593080000) eS) (.pow eQ 3)) eT) (.mul (.num 161280315) (.pow eS 2))))) (.add (.add (.mul (.mul (.num (-1055687850)) (.pow eS 2)) eT) (.add (.mul (.mul (.num (-843577875)) (.pow eS 2)) (.pow eT 2)) (.mul (.mul (.num 1449439110) (.pow eS 2)) eQ))) (.add (.mul (.mul (.mul (.num 10141721100) (.pow eS 2)) eQ) eT) (.add (.mul (.mul (.mul (.num 1065015000) (.pow eS 2)) eQ) (.pow eT 2)) (.mul (.mul (.num (-14449808646)) (.pow eS 2)) (.pow eQ 2)))))) (.add (.add (.add (.mul (.mul (.mul (.num (-2722734000)) (.pow eS 2)) (.pow eQ 2)) eT) (.mul (.mul (.mul (.num (-108045000)) (.pow eS 2)) (.pow eQ 2)) (.pow eT 2))) (.add (.mul (.num (-155306970)) (.pow eS 3)) (.add (.mul (.mul (.num (-1212264900)) (.pow eS 3)) eT) (.mul (.mul (.num (-203742000)) (.pow eS 3)) (.pow eT 2))))) (.add (.add (.mul (.mul (.num 3313480842) (.pow eS 3)) eQ) (.add (.mul (.mul (.mul (.num 950796000) (.pow eS 3)) eQ) eT) (.mul (.mul (.mul (.num 79233000) (.pow eS 3)) eQ) (.pow eT 2)))) (.add (.mul (.num (-285894273)) (.pow eS 4)) (.add (.mul (.mul (.num (-110397980)) (.pow eS 4)) eT) (.mul (.mul (.num (-14526050)) (.pow eS 4)) (.pow eT 2)))))))

private def M01_q_e : Expr :=
  .add (.add (.add (.add (.mul (.num (-2238759810)) eQ) (.add (.mul (.mul (.num 5237503740) eQ) eT) (.mul (.mul (.num (-3040030980)) eQ) (.pow eT 2)))) (.add (.mul (.mul (.num 525029505) eQ) (.pow eT 3)) (.add (.mul (.num 7683624765) (.pow eQ 2)) (.mul (.mul (.num (-372008700)) (.pow eQ 2)) eT)))) (.add (.add (.mul (.num 10237067550) (.pow eQ 3)) (.add (.mul (.mul (.num 1928934000) (.pow eQ 3)) eT) (.mul (.num 4197469815) (.pow eQ 4)))) (.add (.add (.mul (.num 746253270) eS) (.mul (.mul (.num (-1745834580)) eS) eT)) (.add (.mul (.mul (.num 1013343660) eS) (.pow eT 2)) (.mul (.mul (.num (-175009835)) eS) (.pow eT 3)))))) (.add (.add (.add (.mul (.mul (.num (-4575240450)) eS) eQ) (.add (.mul (.mul (.mul (.num 275562000) eS) eQ) eT) (.mul (.mul (.num (-8309917980)) eS) (.pow eQ 2)))) (.add (.add (.mul (.mul (.mul (.num (-2057529600)) eS) (.pow eQ 2)) eT) (.mul (.mul (.num (-7561149120)) eS) (.pow eQ 3))) (.add (.mul (.num 671344065) (.pow eS 2)) (.mul (.mul (.num (-50519700)) (.pow eS 2)) eT)))) (.add (.add (.mul (.mul (.num 2244102813) (.pow eS 2)) eQ) (.add (.mul (.mul (.mul (.num 730851660) (.pow eS 2)) eQ) eT) (.mul (.mul (.num 4310935335) (.pow eS 2)) (.pow eQ 2)))) (.add (.add (.mul (.num (-203860701)) (.pow eS 3)) (.mul (.mul (.num (-86444820)) (.pow eS 3)) eT)) (.add (.mul (.mul (.num (-968078160)) (.pow eS 3)) eQ) (.mul (.num 71921850) (.pow eS 4))))))

private def A32_2_q_e : Expr :=
  .add (.add (.add (.mul (.num 3000564) eQ) (.mul (.mul (.num 78318540) eQ) eT)) (.add (.mul (.num (-197659350)) (.pow eQ 2)) (.mul (.num (-1000188)) eS))) (.add (.add (.mul (.mul (.num (-26106180)) eS) eT) (.mul (.mul (.num 124429830) eS) eQ)) (.add (.mul (.mul (.mul (.num 18357675) eS) eQ) eT) (.add (.mul (.num (-19514460)) (.pow eS 2)) (.mul (.mul (.num (-6119225)) (.pow eS 2)) eT))))

private def A32_1_q_e : Expr :=
  .add (.add (.add (.add (.mul (.num 482717070) eQ) (.mul (.mul (.num (-275562000)) eQ) eT)) (.add (.mul (.mul (.num (-1157172750)) eQ) (.pow eT 2)) (.add (.mul (.num 1567877310) (.pow eQ 2)) (.mul (.mul (.num (-1841555250)) (.pow eQ 2)) eT)))) (.add (.add (.mul (.num (-160905690)) eS) (.add (.mul (.mul (.num 91854000) eS) eT) (.mul (.mul (.num 385724250) eS) (.pow eT 2)))) (.add (.mul (.mul (.num (-1036249848)) eS) eQ) (.add (.mul (.mul (.mul (.num 1656892800) eS) eQ) eT) (.mul (.mul (.mul (.num (-783185400)) eS) eQ) (.pow eT 2)))))) (.add (.add (.add (.mul (.mul (.num (-1185956100)) eS) (.pow eQ 2)) (.mul (.mul (.mul (.num 1976593500) eS) (.pow eQ 2)) eT)) (.add (.mul (.num 171208026) (.pow eS 2)) (.add (.mul (.mul (.num (-347680350)) (.pow eS 2)) eT) (.mul (.mul (.num 261061800) (.pow eS 2)) (.pow eT 2))))) (.add (.add (.mul (.mul (.num 779622795) (.pow eS 2)) eQ) (.add (.mul (.mul (.mul (.num (-1244298300)) (.pow eS 2)) eQ) eT) (.mul (.mul (.mul (.num (-91788375)) (.pow eS 2)) eQ) (.pow eT 2)))) (.add (.mul (.num (-128101365)) (.pow eS 3)) (.add (.mul (.mul (.num 195144600) (.pow eS 3)) eT) (.mul (.mul (.num 30596125) (.pow eS 3)) (.pow eT 2))))))


private def L5_e : Expr := .add (.sub (.mul (.num 77) eS) (.mul (.num 210) eQ)) (.num 45)
private def S3Q_e : Expr := .sub eS (.mul (.num 3) eQ)
private def T59_e : Expr := .sub (.mul (.num 5) eT) (.num 9)
private def T53_e : Expr := .sub (.mul (.num 5) eT) (.num 3)
private def A5_e : Expr := .sub (.mul (.num 5) eS) (.mul (.num 9) eQ)
private def c0_num_e : Expr := .neg (.mul S3Q_e T53_e)
private def w0_sc4_e : Expr := .mul (.mul (.num (-25)) eT) (.pow T59_e 2)
private def Bv1_1701_e : Expr :=
  .add (.add (.mul (.num 7)
    (.add (.sub (.add (.sub (.add (.sub (.add (.mul (.num 143) (.pow eS 3)) (.mul (.num (-828)) (.mul (.pow eS 2) eQ)))
      (.mul (.num (-1404)) (.mul eS (.pow eQ 2)))) (.mul (.num 594) (.pow eQ 3)))
      (.mul (.num 143) (.pow eT 3))) (.mul (.num 828) (.pow eT 2)))
      (.mul (.num 1404) eT)) (.num (-594))))
    (.mul (.num 1215) (.pow eQ 2))) (.mul (.num 2430) eQ)

-- Clean Bv1_1701_e matching `verify_uinf_biv_exact.py` verbatim!
private def Bv1_1701_exact_e : Expr :=
  .add (.add (.mul (.num 7)
    (.sub (.add (.sub (.add (.sub (.add (.sub (.mul (.num 143) (.pow eS 3))
      (.mul (.num 828) (.mul (.pow eS 2) eQ))) (.mul (.num 1404) (.mul eS (.pow eQ 2))))
      (.mul (.num 594) (.pow eQ 3))) (.mul (.num 143) (.pow eT 3)))
      (.mul (.num 828) (.pow eT 2))) (.mul (.num 1404) eT)) (.num 594)))
    (.mul (.num 1215) (.pow eQ 2))) (.mul (.num 2430) eQ)

private def rb_num_28_e : Expr :=
  .mul (.num (-3)) (.add (.add (.add (.sub (.mul (.num 119) (.pow eS 2))
    (.mul (.num 560) (.mul eS eQ))) (.mul (.num 630) (.pow eQ 2))) (.mul (.num 90) eQ)) (.num 90))
private def rb_sc_28_e : Expr := .mul S3Q_e rb_num_28_e

private def dH0_7_inf_e : Fin 3 → Expr
  | 0 => .sub (.add (.mul (.num (-42)) (.pow eS 2)) (.mul (.num 84) (.mul eS eQ))) (.mul (.num 21) (.pow eQ 2))
  | 1 => .add (.add (.sub (.sub (.mul (.num 42) (.pow eS 2)) (.mul (.num 42) (.mul eS eQ)))
           (.mul (.num 42) (.pow eQ 2))) (.mul (.num 10) eQ)) (.num 10)
  | 2 => .sub (.add (.mul (.num (-42)) (.pow eT 2)) (.mul (.num 84) eT)) (.num 21)

private def dH0_301_21_e : Expr := .add (.mul (.num 3) (dH0_7_inf_e 0)) (dH0_7_inf_e 1)

private def bscE (e : Expr) (p : Biv) : Biv := scale e 0 0 p

private def dF5_7_inf_biv : Fin 5 → Biv
  | 0 => .cons (.num 21) 2 0 (.cons (dH0_7_inf_e 0) 0 0 .nil)
  | 1 => .cons (dH0_7_inf_e 1) 0 0 .nil
  | 2 => .cons (.num 21) 0 2 (.cons (dH0_7_inf_e 2) 0 0 .nil)
  | 3 => .cons (.mul (.num 42) eS) 1 0 .nil
  | 4 => .cons (.mul (.num 42) eT) 0 1 .nil

private def dDX2_inf_biv : Fin 5 → Biv
  | 0 => .cons (.num (-27)) 2 0 (.cons (.sub (.mul (.num 100) eS) (.mul (.num 90) eQ)) 1 0
          (.cons (.add (.sub (.mul (.num (-69)) (.pow eS 2)) (.mul (.num (-164)) (.mul eS eQ))) (.mul (.num (-71)) (.pow eQ 2))) 0 0 .nil))
  | 1 => .cons (.mul (.num (-90)) eS) 1 0
          (.cons (.add (.sub (.mul (.num 82) (.pow eS 2)) (.mul (.num 142) (.mul eS eQ))) (.mul (.num (-12)) (.pow eQ 2))) 0 0 .nil)
  | 3 => .cons (.mul (.num (-54)) eS) 1 0 (.cons (.sub (.mul (.num 50) (.pow eS 2)) (.mul (.num 90) (.mul eS eQ))) 0 0 .nil)
  | _ => .nil

private def dDY2_inf_biv : Fin 5 → Biv
  | 2 => .cons (.num (-27)) 0 2 (.cons (.sub (.mul (.num 100) eT) (.num 90)) 0 1
          (.cons (.add (.sub (.mul (.num (-69)) (.pow eT 2)) (.mul (.num (-164)) eT)) (.num (-71))) 0 0 .nil))
  | 4 => .cons (.mul (.num (-54)) eT) 0 1 (.cons (.sub (.mul (.num 50) (.pow eT 2)) (.mul (.num 90) eT)) 0 0 .nil)
  | _ => .nil

private def LX1_9_biv : Biv := .cons (.num 9) 1 0 (.cons (.add (.mul (.num (-25)) eS) (.mul (.num 15) eQ)) 0 0 .nil)
private def LX1_27_biv : Biv := .cons (.num 27) 1 0 (.cons (.add (.mul (.num (-25)) eS) (.mul (.num 45) eQ)) 0 0 .nil)
private def LY1_9_biv : Biv := .cons (.num 9) 0 1 (.cons (.add (.mul (.num (-25)) eT) (.num 15)) 0 0 .nil)
private def LY1_27_biv : Biv := .cons (.num 27) 0 1 (.cons (.add (.mul (.num (-25)) eT) (.num 45)) 0 0 .nil)

private def br_10_243_biv : Fin 5 → Biv
  | 0 => bscE (.mul (.mul (.num (-5)) eT) T59_e) LX1_9_biv
  | 1 => .cons (.mul (.mul (.mul (.num (-150)) eT) T59_e) eS) 0 0 .nil
  | 2 => bscE (.mul (.mul (.num 5) T53_e) eS) LX1_27_biv
  | 3 => .cons (.mul (.mul (.mul (.num (-90)) eT) T59_e) eS) 0 0 .nil
  | 4 => .nil

private def br_00_243_biv : Fin 5 → Biv
  | 0 => .cons (.mul (.mul (.mul (.num 25) eT) T59_e) (.add (.mul (.num (-5)) eS) (.mul (.num 3) eQ))) 0 0 .nil
  | 1 => .cons (.mul (.mul (.mul (.num 150) eT) T59_e) eS) 0 0 .nil
  | 2 => .cons (.mul (.mul (.mul (.num (-25)) T53_e) (.add (.mul (.num (-5)) eS) (.mul (.num 9) eQ))) eS) 0 0 .nil
  | _ => .nil

private def br_11_243_biv : Fin 5 → Biv
  | 0 => bscE (.neg eT) (bivMul LY1_27_biv LX1_9_biv)
  | 1 => bscE (.mul (.mul (.num (-30)) eT) eS) LY1_27_biv
  | 2 => bscE eS (bivMul LY1_9_biv LX1_27_biv)
  | 3 => bscE (.mul (.mul (.num (-18)) eT) eS) LY1_27_biv
  | 4 => bscE (.mul (.mul (.num 18) eT) eS) LX1_27_biv

private def om_10_raw (p q : Fin 5) : Biv := match p, q with
  | 0, 2 => bscE (.mul (.num 5) T53_e) LX1_9_biv
  | 1, 2 => .cons (.mul (.mul (.num 150) T53_e) eS) 0 0 .nil
  | 2, 3 => .cons (.mul (.mul (.num (-90)) T53_e) eS) 0 0 .nil
  | _, _ => .nil

private def om_10_81_biv (p q : Fin 5) : Biv := bivSub (om_10_raw p q) (om_10_raw q p)

private def om_00_raw (p q : Fin 5) : Biv := match p, q with
  | 0, 2 => .cons (.mul (.mul (.num (-25)) T53_e) (.add (.mul (.num (-5)) eS) (.mul (.num 3) eQ))) 0 0 .nil
  | 1, 2 => .cons (.mul (.mul (.num (-150)) T53_e) eS) 0 0 .nil
  | _, _ => .nil

private def om_00_81_biv (p q : Fin 5) : Biv := bivSub (om_00_raw p q) (om_00_raw q p)

private def om_11_raw (p q : Fin 5) : Biv := match p, q with
  | 0, 2 => bivMul LY1_9_biv LX1_9_biv
  | 0, 4 => bscE (.mul (.num 18) eT) LX1_9_biv
  | 1, 2 => bscE (.mul (.num 30) eS) LY1_9_biv
  | 1, 4 => .cons (.mul (.mul (.num 540) eT) eS) 0 0 .nil
  | 2, 3 => bscE (.mul (.num (-18)) eS) LY1_9_biv
  | 3, 4 => .cons (.mul (.mul (.num 324) eT) eS) 0 0 .nil
  | _, _ => .nil

private def om_11_81_biv (p q : Fin 5) : Biv := bivSub (om_11_raw p q) (om_11_raw q p)

private def F_c_inf_biv (f2 : Fin 5 → Fin 5 → Biv) (i : Fin 3) : Biv :=
  let idx : Fin 5 := match i with | 0 => 0 | 1 => 1 | 2 => 2
  bivAdd (bivAdd (bivMul (dF5_7_inf_biv 4) (f2 idx 3))
    (bivMul (dF5_7_inf_biv 3) (f2 4 idx))) (bivMul (dF5_7_inf_biv idx) (f2 3 4))

private def make_QY_biv (br243 : Fin 5 → Biv) (om81 : Fin 5 → Fin 5 → Biv) (i : Fin 3) : Biv :=
  let Om := F_c_inf_biv (fun a b => bscE (.mul eS eT) (om81 a b)) i
  let dX := F_c_inf_biv (fun a b => bscE (.mul eS eT)
    (bivSub (bivMul (dDX2_inf_biv a) (br243 b)) (bivMul (dDX2_inf_biv b) (br243 a)))) i
  bivMul DY2_biv (bivSub (bivScale 3 (bivMul DX2_biv Om)) dX)

private def make_QX_biv (br243 : Fin 5 → Biv) (om81 : Fin 5 → Fin 5 → Biv) (i : Fin 3) : Biv :=
  let Om := F_c_inf_biv (fun a b => bscE (.mul eS eT) (om81 a b)) i
  let dY := F_c_inf_biv (fun a b => bscE (.mul eS eT)
    (bivSub (bivMul (dDY2_inf_biv a) (br243 b)) (bivMul (dDY2_inf_biv b) (br243 a)))) i
  bivMul DX2_biv (bivAdd (bivScale (-3) (bivMul DY2_biv Om)) dY)

private def QX10_biv (i : Fin 3) : Biv := make_QX_biv br_10_243_biv om_10_81_biv i
private def QY10_biv (i : Fin 3) : Biv := make_QY_biv br_10_243_biv om_10_81_biv i
private def QX00_biv (i : Fin 3) : Biv := make_QX_biv br_00_243_biv om_00_81_biv i
private def QY00_biv (i : Fin 3) : Biv := make_QY_biv br_00_243_biv om_00_81_biv i
private def QX11_biv (i : Fin 3) : Biv := make_QX_biv br_11_243_biv om_11_81_biv i
private def QY11_biv (i : Fin 3) : Biv := make_QY_biv br_11_243_biv om_11_81_biv i

private def EB10_biv : Biv :=
  bivScale 12 (bivMul W2_biv (bivSub (scale eT 0 1 (br_10_243_biv 3))
    (scale eS 1 0 (br_10_243_biv 4))))

private def EB11_biv : Biv :=
  bivScale 12 (bivMul W2_biv (bivSub (scale eT 0 1 (br_11_243_biv 3))
    (scale eS 1 0 (br_11_243_biv 4))))

private def cQX_0_biv : Biv := bivAdd (bivScale 3 (QX10_biv 0)) (QX10_biv 1)
private def cQX_00_biv : Biv := bivAdd (bivScale 3 (QX00_biv 0)) (QX00_biv 1)
private def cQX_11_biv : Biv := bivAdd (bivScale 3 (QX11_biv 0)) (QX11_biv 1)
private def cQY_00_biv : Biv := bivAdd (bivScale 3 (QY00_biv 0)) (QY00_biv 1)
private def cQY_11_biv : Biv := bivAdd (bivScale 3 (QY11_biv 0)) (QY11_biv 1)

private def q1_m1_u1_biv : Biv :=
  bscE (.mul (.mul (.num 25) eT) (.pow T59_e 2))
    (bivAdd (bscE H0_int_e cQX_0_biv) (bscE (.mul (.num 7) dH0_301_21_e) EB10_biv))

private def q1_m1_u0_biv : Biv :=
  let t1 := bscE (.mul (.mul (.mul (.num (-75)) eT) (.pow T59_e 2)) H0_int_e)
    (bivAdd (bscE c0_num_e (QY10_biv 1)) (bscE (.mul (.mul (.num 3) eT) T59_e) (QY10_biv 2)))
  let t2 := bscE (.mul (.mul (.mul (.num 75) eT) (.pow T59_e 2)) H0_int_e)
    (bivAdd (bscE c0_num_e (QX10_biv 1)) (bscE (.mul (.mul (.num 3) eT) T59_e) (QX10_biv 2)))
  let t3 := bscE (.mul (.num (-525))
    (.sub (.mul (.mul (.mul (.mul (.num 9) eT) (.pow T59_e 2)) T53_e) H0_int_e)
      (.mul (.mul eT (.pow T59_e 2)) (.add (.mul (dH0_7_inf_e 1) c0_num_e)
        (.mul (.mul (.mul (.num 3) eT) T59_e) (dH0_7_inf_e 2)))))) EB10_biv
  bivAdd (bivAdd t1 t2) t3

private def cQX_1_biv : Biv :=
  bivAdd (bivAdd (bscE (.neg Bv1_1701_exact_e) cQX_0_biv) (bscE rb_sc_28_e (QX10_biv 1)))
    (bivAdd (bscE (.mul (.num 28) (.pow S3Q_e 3)) cQX_00_biv) (bscE (.mul (.num 7) w0_sc4_e) cQX_11_biv))

private def q1_0_u1_biv : Biv :=
  let qa := bscE (.mul (.mul (.mul (.num (-25)) eT) (.pow T59_e 2)) H0_int_e)
    (bivAdd (bscE rb_sc_28_e (QY10_biv 1))
      (bivAdd (bscE (.mul (.num 28) (.pow S3Q_e 3)) cQY_00_biv) (bscE (.mul (.num 7) w0_sc4_e) cQY_11_biv)))
  let qb := bivSub
    (bscE (.mul (.mul (.mul (.num 25) eT) (.pow T59_e 2)) H0_int_e)
      (bivAdd cQX_1_biv (bscE (.mul (.num 28) (.pow S3Q_e 3)) cQX_0_biv)))
    (bscE (.mul (.mul (.mul (.num 28) (.pow (.sub eT (.num 3)) 3)) w0_sc4_e) H0_int_e) cQX_0_biv)
  let qc1_fac : Expr :=
    .sub (.sub (.mul (.mul H0_int_e w0_sc4_e)
      (.add (.mul (.num 63) rb_num_28_e) (.mul (.mul (.num 33075) A5_e) (.sub eS eQ))))
      (.mul (.mul (.mul (.mul (.num 1225) eS) (.pow A5_e 2)) w0_sc4_e) dH0_301_21_e))
      (.mul (.mul (.mul (.mul (.num 175) eT) (.pow T59_e 2)) rb_sc_28_e) (dH0_7_inf_e 1))
  let qc := bivAdd (bscE (.neg qc1_fac) EB10_biv)
    (bscE (.mul (.mul (.mul (.mul (.num 1225) w0_sc4_e) eT) (.pow T59_e 2)) dH0_301_21_e)
      (bivAdd EB11_biv EB10_biv))
  bivAdd (bivAdd qa qb) qc

private def lin_A3_e : Expr :=
  .sub (.add (.sub (.add (.mul (.num 35) (.mul eS eT)) (.mul (.num 133) eS)) (.mul (.num 420) eQ))
    (.mul (.num 225) eT)) (.num 45)

private def LHS_Uinf_raw_biv : Biv :=
  let s1 := bscE (.mul (.mul (.num 539715645) L5_e) S3Q_e) q1_0_u1_biv
  let s2 := bscE (.mul (.mul (.num 6174) L5_e) M01_q_e) q1_m1_u1_biv
  let s3 := bscE (.mul (.mul (.mul (.mul (.num 3593175390) L5_e) w0_sc4_e) S3Q_e) (.pow H0_int_e 2)) cQX_0_biv
  let s4 := bscE (.mul (.mul (.num (-3671535)) P44_e) S3Q_e) q1_m1_u1_biv
  let s5 := bscE (.mul (.mul (.mul (.num 8566915) (.pow L5_e 2)) lin_A3_e) S3Q_e) q1_m1_u0_biv
  let s6 := bscE (.mul (.mul (.mul (.num 63) (.pow L5_e 2)) lin_A3_e) A32_2_q_e) q1_m1_u1_biv
  let s7 := bscE (.mul (.mul (.num 49) (.pow L5_e 2)) A32_2_q_e) q1_m1_u0_biv
  let s8 := bscE (.mul (.mul (.num 147) (.pow L5_e 2)) A32_1_q_e) q1_m1_u1_biv
  bivAdd (bivAdd (bivAdd s1 s2) (bivAdd s3 s4)) (bivAdd (bivAdd s5 s6) (bivAdd s7 s8))

private def LHS_Uinf_biv : Biv := bivReduceX2 (bivReduceX2 LHS_Uinf_raw_biv)

private def RHS_Uinf_biv : Biv :=
  bscE (.mul (.pow (.mul (.num 21) eS) 2)
    (.mul (.mul (.mul (.num (-40500)) S3Q_e) (.pow eT 2)) (.pow T59_e 3))) RInf_biv

private lemma evalBivK5_bscE (e : Expr) (p : Biv) :
    evalBivK5 (bscE e p) = ringEval vK5 e * evalBivK5 p := by
  simpa only [bscE, pow_zero, mul_one] using evalBivK5_scale e 0 0 p

private lemma Uinf_biv_identity : evalBivK5 LHS_Uinf_biv = evalBivK5 RHS_Uinf_biv := by
  exact biv_denote_eq_of_kronecker3 vK5 x_K y_K 19 16 22 (2 ^ 136) LHS_Uinf_biv RHS_Uinf_biv
    (by decide +kernel)

private lemma evalBivK5_DX2_inf : evalBivK5 DX2_biv = DX2_of S_K Q_K x_K := by
  simp only [evalBivK5, denote, DX2_biv, ringEval, eS, eQ, vK5, DX2_of, u3_of]; ring

private lemma evalBivK5_DY2_inf : evalBivK5 DY2_biv = DY2_of T_K y_K := by
  simp only [evalBivK5, denote, DY2_biv, ringEval, eT, vK5, DY2_of, v3_of]; ring

private lemma evalBivK5_W2_inf : evalBivK5 W2_biv = W2_of S_K Q_K T_K x_K y_K := by
  simp only [W2_biv, evalBivK5_bivMul, evalBivK5_scale, evalBivK5_DX2_inf, evalBivK5_DY2_inf, W2_of]
  simp only [ringEval, eS, eT, vK5, pow_zero, mul_one]

private lemma ringEval_dH0_7_inf (k : Fin 3) :
    ringEval vK5 (dH0_7_inf_e k) = 7 * dH0_fn k S_K Q_K T_K := by
  fin_cases k <;> (simp only [dH0_7_inf_e, ringEval, eS, eQ, eT, vK5, dH0_fn]; ring)

private lemma evalBivK5_dF5_7_inf (k : Fin 5) :
    evalBivK5 (dF5_7_inf_biv k) = 7 * dF5_fn k S_K Q_K T_K x_K y_K := by
  fin_cases k <;> (simp only [dF5_7_inf_biv, evalBivK5, denote, ringEval_dH0_7_inf, ringEval,
    eS, eT, vK5, dF5_fn, dH0_fn]; ring)

private lemma evalBivK5_dDX2_inf (k : Fin 5) :
    evalBivK5 (dDX2_inf_biv k) = dDX2_fn k S_K Q_K x_K := by
  fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, dDX2_inf_biv, evalBivK5, denote, ringEval, eS, eQ, vK5, dDX2_fn, u3_of]
  all_goals ring

private lemma evalBivK5_dDY2_inf (k : Fin 5) :
    evalBivK5 (dDY2_inf_biv k) = dDY2_fn k T_K y_K := by
  fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, dDY2_inf_biv, evalBivK5, denote, ringEval, eT, vK5, dDY2_fn, v3_of]
  all_goals ring

private lemma evalBivK5_br_10 (k : Fin 5) :
    evalBivK5 (br_10_243_biv k) = 243 * (br_fn k S_K Q_K T_K x_K y_K 1 0 - br_fn k S_K Q_K T_K x_K y_K 0 0) := by
  rw [br_10_eq]
  fin_cases k <;> (
    simp only [br_10_243_biv, evalBivK5_bscE]
    simp only [LX1_9_biv, LX1_27_biv, T59_e, T53_e, evalBivK5, denote, ringEval, eS, eQ, eT, vK5])
  all_goals ring

private lemma evalBivK5_br_00 (k : Fin 5) :
    evalBivK5 (br_00_243_biv k) = 243 * br_fn k S_K Q_K T_K x_K y_K 0 0 := by
  rw [br_00_eq]
  fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, br_00_243_biv, T59_e, T53_e, evalBivK5, denote, ringEval, eS, eQ, eT, vK5]
  all_goals ring

private lemma evalBivK5_br_11 (k : Fin 5) :
    evalBivK5 (br_11_243_biv k) = 243 * (br_fn k S_K Q_K T_K x_K y_K 1 1 - br_fn k S_K Q_K T_K x_K y_K 1 0 -
      br_fn k S_K Q_K T_K x_K y_K 0 1 + br_fn k S_K Q_K T_K x_K y_K 0 0) := by
  rw [br_11_eq]
  fin_cases k <;> (
    simp only [br_11_243_biv, evalBivK5_bscE, evalBivK5_bivMul]
    simp only [LX1_9_biv, LX1_27_biv, LY1_9_biv, LY1_27_biv, evalBivK5, denote, ringEval, eS, eQ, eT, vK5]; ring)

private lemma evalBivK5_om_10 (p q : Fin 5) :
    evalBivK5 (om_10_81_biv p q) = 81 * (om_fn p q S_K Q_K T_K x_K y_K 1 0 - om_fn p q S_K Q_K T_K x_K y_K 0 0) := by
  have h := om_10_eq p q S_K Q_K T_K x_K y_K
  simp only [Nat.cast_ofNat] at h
  rw [h]
  fin_cases p <;> fin_cases q <;> (
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, om_10_81_biv, om_10_raw, evalBivK5_bivSub, evalBivK5_bscE]
    simp only [LX1_9_biv, T53_e, evalBivK5, denote, ringEval, eS, eQ, eT, vK5])
  all_goals ring

private lemma evalBivK5_om_00 (p q : Fin 5) :
    evalBivK5 (om_00_81_biv p q) = 81 * om_fn p q S_K Q_K T_K x_K y_K 0 0 := by
  have h := om_00_eq p q S_K Q_K T_K x_K y_K
  simp only [Nat.cast_ofNat] at h
  rw [h]
  fin_cases p <;> fin_cases q <;> (
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, om_00_81_biv, om_00_raw, evalBivK5_bivSub]
    simp only [T53_e, evalBivK5, denote, ringEval, eS, eQ, eT, vK5])
  all_goals ring

private lemma evalBivK5_om_11 (p q : Fin 5) :
    evalBivK5 (om_11_81_biv p q) = 81 * (om_fn p q S_K Q_K T_K x_K y_K 1 1 - om_fn p q S_K Q_K T_K x_K y_K 1 0 -
      om_fn p q S_K Q_K T_K x_K y_K 0 1 + om_fn p q S_K Q_K T_K x_K y_K 0 0) := by
  have h := om_11_eq p q S_K Q_K T_K x_K y_K
  simp only [Nat.cast_ofNat] at h
  rw [h]
  fin_cases p <;> fin_cases q <;> (
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, om_11_81_biv, om_11_raw, evalBivK5_bivSub, evalBivK5_bscE, evalBivK5_bivMul]
    simp only [LX1_9_biv, LY1_9_biv, evalBivK5, denote, ringEval, eS, eQ, eT, vK5])
  all_goals ring

private lemma evalBivK5_F_c_inf (f2 : Fin 5 → Fin 5 → Biv) (g2 : Fin 5 → Fin 5 → K5)
    (hf : ∀ a b, evalBivK5 (f2 a b) = g2 a b) (i : Fin 3) :
    evalBivK5 (F_c_inf_biv f2 i) = 7 * F_contract S_K Q_K T_K x_K y_K g2 i := by
  fin_cases i <;> (simp only [F_c_inf_biv, F_contract,
    evalBivK5_bivAdd, evalBivK5_bivMul, evalBivK5_dF5_7_inf, hf]; ring)

private lemma evalBivK5_QY10 (i : Fin 3) :
    evalBivK5 (QY10_biv i) = 1701 * (QY_num S_K Q_K T_K x_K y_K 1 0 i - QY_num S_K Q_K T_K x_K y_K 0 0 i) := by
  simp only [QY10_biv, make_QY_biv, evalBivK5_bivMul, evalBivK5_bivSub, evalBivK5_bivScale,
    evalBivK5_DX2_inf, evalBivK5_DY2_inf]
  rw [evalBivK5_F_c_inf _ (fun a b => S_K * T_K * (81 * (om_fn a b S_K Q_K T_K x_K y_K 1 0 - om_fn a b S_K Q_K T_K x_K y_K 0 0)))
    (fun a b => by rw [evalBivK5_bscE, evalBivK5_om_10]; simp only [ringEval, eS, eT, vK5]) i,
    evalBivK5_F_c_inf _ (fun a b => S_K * T_K * (dDX2_fn a S_K Q_K x_K * (243 * (br_fn b S_K Q_K T_K x_K y_K 1 0 - br_fn b S_K Q_K T_K x_K y_K 0 0)) -
      dDX2_fn b S_K Q_K x_K * (243 * (br_fn a S_K Q_K T_K x_K y_K 1 0 - br_fn a S_K Q_K T_K x_K y_K 0 0))))
    (fun a b => by rw [evalBivK5_bscE, evalBivK5_bivSub, evalBivK5_bivMul, evalBivK5_bivMul,
      evalBivK5_dDX2_inf, evalBivK5_dDX2_inf, evalBivK5_br_10, evalBivK5_br_10]; simp only [ringEval, eS, eT, vK5]) i]
  simp only [QY_num, Omega_F, dDX2_F, F_contract]; push_cast; ring

private lemma evalBivK5_QX10 (i : Fin 3) :
    evalBivK5 (QX10_biv i) = 1701 * (QX_num S_K Q_K T_K x_K y_K 1 0 i - QX_num S_K Q_K T_K x_K y_K 0 0 i) := by
  simp only [QX10_biv, make_QX_biv, evalBivK5_bivMul, evalBivK5_bivAdd, evalBivK5_bivScale,
    evalBivK5_DX2_inf, evalBivK5_DY2_inf]
  rw [evalBivK5_F_c_inf _ (fun a b => S_K * T_K * (81 * (om_fn a b S_K Q_K T_K x_K y_K 1 0 - om_fn a b S_K Q_K T_K x_K y_K 0 0)))
    (fun a b => by rw [evalBivK5_bscE, evalBivK5_om_10]; simp only [ringEval, eS, eT, vK5]) i,
    evalBivK5_F_c_inf _ (fun a b => S_K * T_K * (dDY2_fn a T_K y_K * (243 * (br_fn b S_K Q_K T_K x_K y_K 1 0 - br_fn b S_K Q_K T_K x_K y_K 0 0)) -
      dDY2_fn b T_K y_K * (243 * (br_fn a S_K Q_K T_K x_K y_K 1 0 - br_fn a S_K Q_K T_K x_K y_K 0 0))))
    (fun a b => by rw [evalBivK5_bscE, evalBivK5_bivSub, evalBivK5_bivMul, evalBivK5_bivMul,
      evalBivK5_dDY2_inf, evalBivK5_dDY2_inf, evalBivK5_br_10, evalBivK5_br_10]; simp only [ringEval, eS, eT, vK5]) i]
  simp only [QX_num, Omega_F, dDY2_F, F_contract]; push_cast; ring

private lemma evalBivK5_QY00 (i : Fin 3) :
    evalBivK5 (QY00_biv i) = 1701 * QY_num S_K Q_K T_K x_K y_K 0 0 i := by
  simp only [QY00_biv, make_QY_biv, evalBivK5_bivMul, evalBivK5_bivSub, evalBivK5_bivScale,
    evalBivK5_DX2_inf, evalBivK5_DY2_inf]
  rw [evalBivK5_F_c_inf _ (fun a b => S_K * T_K * (81 * om_fn a b S_K Q_K T_K x_K y_K 0 0))
    (fun a b => by rw [evalBivK5_bscE, evalBivK5_om_00]; simp only [ringEval, eS, eT, vK5]) i,
    evalBivK5_F_c_inf _ (fun a b => S_K * T_K * (dDX2_fn a S_K Q_K x_K * (243 * br_fn b S_K Q_K T_K x_K y_K 0 0) -
      dDX2_fn b S_K Q_K x_K * (243 * br_fn a S_K Q_K T_K x_K y_K 0 0)))
    (fun a b => by rw [evalBivK5_bscE, evalBivK5_bivSub, evalBivK5_bivMul, evalBivK5_bivMul,
      evalBivK5_dDX2_inf, evalBivK5_dDX2_inf, evalBivK5_br_00, evalBivK5_br_00]; simp only [ringEval, eS, eT, vK5]) i]
  simp only [QY_num, Omega_F, dDX2_F, F_contract]; push_cast; ring

private lemma evalBivK5_QX00 (i : Fin 3) :
    evalBivK5 (QX00_biv i) = 1701 * QX_num S_K Q_K T_K x_K y_K 0 0 i := by
  simp only [QX00_biv, make_QX_biv, evalBivK5_bivMul, evalBivK5_bivAdd, evalBivK5_bivScale,
    evalBivK5_DX2_inf, evalBivK5_DY2_inf]
  rw [evalBivK5_F_c_inf _ (fun a b => S_K * T_K * (81 * om_fn a b S_K Q_K T_K x_K y_K 0 0))
    (fun a b => by rw [evalBivK5_bscE, evalBivK5_om_00]; simp only [ringEval, eS, eT, vK5]) i,
    evalBivK5_F_c_inf _ (fun a b => S_K * T_K * (dDY2_fn a T_K y_K * (243 * br_fn b S_K Q_K T_K x_K y_K 0 0) -
      dDY2_fn b T_K y_K * (243 * br_fn a S_K Q_K T_K x_K y_K 0 0)))
    (fun a b => by rw [evalBivK5_bscE, evalBivK5_bivSub, evalBivK5_bivMul, evalBivK5_bivMul,
      evalBivK5_dDY2_inf, evalBivK5_dDY2_inf, evalBivK5_br_00, evalBivK5_br_00]; simp only [ringEval, eS, eT, vK5]) i]
  simp only [QX_num, Omega_F, dDY2_F, F_contract]; push_cast; ring

private lemma evalBivK5_QY11 (i : Fin 3) :
    evalBivK5 (QY11_biv i) = 1701 * (QY_num S_K Q_K T_K x_K y_K 1 1 i - QY_num S_K Q_K T_K x_K y_K 1 0 i -
      QY_num S_K Q_K T_K x_K y_K 0 1 i + QY_num S_K Q_K T_K x_K y_K 0 0 i) := by
  simp only [QY11_biv, make_QY_biv, evalBivK5_bivMul, evalBivK5_bivSub, evalBivK5_bivScale,
    evalBivK5_DX2_inf, evalBivK5_DY2_inf]
  rw [evalBivK5_F_c_inf _ (fun a b => S_K * T_K * (81 * (om_fn a b S_K Q_K T_K x_K y_K 1 1 - om_fn a b S_K Q_K T_K x_K y_K 1 0 -
      om_fn a b S_K Q_K T_K x_K y_K 0 1 + om_fn a b S_K Q_K T_K x_K y_K 0 0)))
    (fun a b => by rw [evalBivK5_bscE, evalBivK5_om_11]; simp only [ringEval, eS, eT, vK5]) i,
    evalBivK5_F_c_inf _ (fun a b => S_K * T_K * (dDX2_fn a S_K Q_K x_K * (243 * (br_fn b S_K Q_K T_K x_K y_K 1 1 - br_fn b S_K Q_K T_K x_K y_K 1 0 -
        br_fn b S_K Q_K T_K x_K y_K 0 1 + br_fn b S_K Q_K T_K x_K y_K 0 0)) -
      dDX2_fn b S_K Q_K x_K * (243 * (br_fn a S_K Q_K T_K x_K y_K 1 1 - br_fn a S_K Q_K T_K x_K y_K 1 0 -
        br_fn a S_K Q_K T_K x_K y_K 0 1 + br_fn a S_K Q_K T_K x_K y_K 0 0))))
    (fun a b => by rw [evalBivK5_bscE, evalBivK5_bivSub, evalBivK5_bivMul, evalBivK5_bivMul,
      evalBivK5_dDX2_inf, evalBivK5_dDX2_inf, evalBivK5_br_11, evalBivK5_br_11]; simp only [ringEval, eS, eT, vK5]) i]
  simp only [QY_num, Omega_F, dDX2_F, F_contract]; push_cast; ring

private lemma evalBivK5_QX11 (i : Fin 3) :
    evalBivK5 (QX11_biv i) = 1701 * (QX_num S_K Q_K T_K x_K y_K 1 1 i - QX_num S_K Q_K T_K x_K y_K 1 0 i -
      QX_num S_K Q_K T_K x_K y_K 0 1 i + QX_num S_K Q_K T_K x_K y_K 0 0 i) := by
  simp only [QX11_biv, make_QX_biv, evalBivK5_bivMul, evalBivK5_bivAdd, evalBivK5_bivScale,
    evalBivK5_DX2_inf, evalBivK5_DY2_inf]
  rw [evalBivK5_F_c_inf _ (fun a b => S_K * T_K * (81 * (om_fn a b S_K Q_K T_K x_K y_K 1 1 - om_fn a b S_K Q_K T_K x_K y_K 1 0 -
      om_fn a b S_K Q_K T_K x_K y_K 0 1 + om_fn a b S_K Q_K T_K x_K y_K 0 0)))
    (fun a b => by rw [evalBivK5_bscE, evalBivK5_om_11]; simp only [ringEval, eS, eT, vK5]) i,
    evalBivK5_F_c_inf _ (fun a b => S_K * T_K * (dDY2_fn a T_K y_K * (243 * (br_fn b S_K Q_K T_K x_K y_K 1 1 - br_fn b S_K Q_K T_K x_K y_K 1 0 -
        br_fn b S_K Q_K T_K x_K y_K 0 1 + br_fn b S_K Q_K T_K x_K y_K 0 0)) -
      dDY2_fn b T_K y_K * (243 * (br_fn a S_K Q_K T_K x_K y_K 1 1 - br_fn a S_K Q_K T_K x_K y_K 1 0 -
        br_fn a S_K Q_K T_K x_K y_K 0 1 + br_fn a S_K Q_K T_K x_K y_K 0 0))))
    (fun a b => by rw [evalBivK5_bscE, evalBivK5_bivSub, evalBivK5_bivMul, evalBivK5_bivMul,
      evalBivK5_dDY2_inf, evalBivK5_dDY2_inf, evalBivK5_br_11, evalBivK5_br_11]; simp only [ringEval, eS, eT, vK5]) i]
  simp only [QX_num, Omega_F, dDY2_F, F_contract]; push_cast; ring

private lemma evalBivK5_EB10 :
    evalBivK5 EB10_biv = 243 * (EB_of S_K Q_K T_K x_K y_K 1 0 - EB_of S_K Q_K T_K x_K y_K 0 0) := by
  have h1 : evalBivK5 (scale eT 0 1 (br_10_243_biv 3)) =
      T_K * y_K * evalBivK5 (br_10_243_biv 3) := by
    simpa only [pow_zero, pow_one, mul_one, ringEval, eT, vK5] using evalBivK5_scale eT 0 1 (br_10_243_biv 3)
  have h2 : evalBivK5 (scale eS 1 0 (br_10_243_biv 4)) =
      S_K * x_K * evalBivK5 (br_10_243_biv 4) := by
    simpa only [pow_zero, pow_one, mul_one, ringEval, eS, vK5] using evalBivK5_scale eS 1 0 (br_10_243_biv 4)
  simp only [EB10_biv, evalBivK5_bivScale, evalBivK5_bivMul, evalBivK5_bivSub, evalBivK5_W2_inf, h1, h2,
    evalBivK5_br_10, EB_of, dF5_fn]; push_cast; ring

private lemma evalBivK5_EB11 :
    evalBivK5 EB11_biv = 243 * (EB_of S_K Q_K T_K x_K y_K 1 1 - EB_of S_K Q_K T_K x_K y_K 1 0 -
      EB_of S_K Q_K T_K x_K y_K 0 1 + EB_of S_K Q_K T_K x_K y_K 0 0) := by
  have h1 : evalBivK5 (scale eT 0 1 (br_11_243_biv 3)) =
      T_K * y_K * evalBivK5 (br_11_243_biv 3) := by
    simpa only [pow_zero, pow_one, mul_one, ringEval, eT, vK5] using evalBivK5_scale eT 0 1 (br_11_243_biv 3)
  have h2 : evalBivK5 (scale eS 1 0 (br_11_243_biv 4)) =
      S_K * x_K * evalBivK5 (br_11_243_biv 4) := by
    simpa only [pow_zero, pow_one, mul_one, ringEval, eS, vK5] using evalBivK5_scale eS 1 0 (br_11_243_biv 4)
  simp only [EB11_biv, evalBivK5_bivScale, evalBivK5_bivMul, evalBivK5_bivSub, evalBivK5_W2_inf, h1, h2,
    evalBivK5_br_11, EB_of, dF5_fn]; push_cast; ring

private lemma ringEval_P44_e : ringEval vK5 P44_e = P44_fn S_K Q_K T_K := by
  simp only [P44_e, P44_fn, ringEval, eS, eQ, eT, vK5]; ring

private lemma ringEval_M01_q_e : ringEval vK5 M01_q_e = M01_q_fn S_K Q_K T_K := by
  simp only [M01_q_e, M01_q_fn, ringEval, eS, eQ, eT, vK5]; ring

private lemma ringEval_A32_2_q_e : ringEval vK5 A32_2_q_e = A32_2_q_fn S_K Q_K T_K := by
  simp only [A32_2_q_e, A32_2_q_fn, ringEval, eS, eQ, eT, vK5]; ring

private lemma ringEval_A32_1_q_e : ringEval vK5 A32_1_q_e = A32_1_q_fn S_K Q_K T_K := by
  simp only [A32_1_q_e, A32_1_q_fn, ringEval, eS, eQ, eT, vK5]; ring

-- `interp4_p4_mul` & `interp4_add_p4`:
private lemma interp4_add_p4 {R : Type*} [Field R] [CharZero R] (f g : R → R) :
    (interp4 (fun z => f z + g z)).1 = (interp4 f).1 + (interp4 g).1 := by
  unfold interp4; ring

private lemma interp4_p4_mul {R : Type*} [Field R] [CharZero R] {f h : R → R}
    (hf : IsPolyDeg 3 f) (hh : IsPolyDeg 1 h) :
    (interp4 (fun z => f z * h z)).1 = ((f 2 - 3 * f 1 + 3 * f 0 - f (-1)) / 6) * (h 1 - h 0) := by
  rcases hf with ⟨P, hP, heP⟩
  rcases hh with ⟨Q, hQ, heQ⟩
  have hfeq (z : R) : f z = P.coeff 0 + P.coeff 1 * z + P.coeff 2 * z ^ 2 + P.coeff 3 * z ^ 3 := by
    rw [heP z, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hP)]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]; ring
  have hheq (z : R) : h z = Q.coeff 0 + Q.coeff 1 * z := by
    rw [heQ z, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hQ)]
    rw [Finset.sum_range_succ, Finset.sum_range_one]; ring
  unfold interp4
  simp only [hfeq, hheq]; ring

private lemma IsPolyDeg_numM {R : Type*} [Field R] [CharZero R]
    (S Q T U V aa ab b0 : R) (mi : Fin 10) :
    IsPolyDeg 3 (fun z : R => numM mi (aa * z) (ab * z + b0) (S - aa * z * T) (Q - (ab * z + b0) * T) U V) :=
  IsPolyDeg.congr (numM_isPolyDeg3 mi S Q T U V aa 0 ab b0) (fun z => by simp only [add_zero])

private lemma br1_inf_EB_valLead {U V : LaurentSeries K5} {w0 : K5}
    (hU_L : ValLead (-1) U 1) (hV_L : ValLead 1 V w0) :
    ValLead (-1) (EB_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V) (evalBivK5 EB10_biv / 243) := by
  have hlinU {a00 a01 a10 a11 : K5} :
      ValLead (-1) (HahnSeries.C a00 + HahnSeries.C a01 * V + HahnSeries.C a10 * U + HahnSeries.C a11 * U * V) a10 := by
    have hre : HahnSeries.C a00 + HahnSeries.C a01 * V + HahnSeries.C a10 * U + HahnSeries.C a11 * U * V =
        HahnSeries.C a10 * U + (HahnSeries.C a00 + HahnSeries.C a01 * V + HahnSeries.C a11 * U * V) := by ring
    rw [hre]
    exact (((ValLead.of_C a10).mul hU_L).eq_k (by omega) |>.eq_c (mul_one _)).add_high
      ((((HasValGe.of_C a00).add (((HasValGe.of_C a01).mul hV_L.val).mono (by omega))).add
        ((((HasValGe.of_C a11).mul hU_L.val).mul hV_L.val).mono (by omega))))
  have hbi := EB_bilinear_UV (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
    (HahnSeries.C x_K) (HahnSeries.C y_K) U V
  have hmap (u0 v0 : K5) : (EB_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) (HahnSeries.C u0) (HahnSeries.C v0) : LaurentSeries K5) =
      HahnSeries.C (EB_of S_K Q_K T_K x_K y_K u0 v0) := by
    simp only [EB_of, W2_of, DX2_of, DY2_of, dF5_fn, br_fn, LX_of, LY_of,
      dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of,
      map_add, map_sub, map_mul, map_div₀, map_pow, map_ofNat, map_zero, map_one]
  have h00 := hmap 0 0; have h01 := hmap 0 1; have h10 := hmap 1 0; have h11 := hmap 1 1
  simp only [map_zero, map_one] at h00 h01 h10 h11
  rw [hbi, h00, h01, h10, h11, ← map_sub, ← map_sub, ← map_sub, ← map_sub, ← map_add]
  exact hlinU.eq_c (by rw [evalBivK5_EB10]; ring)

private lemma br1_inf_QY_valLead {U V : LaurentSeries K5} {w0 : K5}
    (hU_L : ValLead (-1) U 1) (hV_L : ValLead 1 V w0) (i : Fin 3) :
    ValLead (-1)
      (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V i)
      (evalBivK5 (QY10_biv i) / 1701) := by
  have hlinU {a00 a01 a10 a11 : K5} :
      ValLead (-1) (HahnSeries.C a00 + HahnSeries.C a01 * V + HahnSeries.C a10 * U + HahnSeries.C a11 * U * V) a10 := by
    have hre : HahnSeries.C a00 + HahnSeries.C a01 * V + HahnSeries.C a10 * U + HahnSeries.C a11 * U * V =
        HahnSeries.C a10 * U + (HahnSeries.C a00 + HahnSeries.C a01 * V + HahnSeries.C a11 * U * V) := by ring
    rw [hre]
    exact (((ValLead.of_C a10).mul hU_L).eq_k (by omega) |>.eq_c (mul_one _)).add_high
      ((((HasValGe.of_C a00).add (((HasValGe.of_C a01).mul hV_L.val).mono (by omega))).add
        ((((HasValGe.of_C a11).mul hU_L.val).mul hV_L.val).mono (by omega))))
  have hbi := QY_bilinear_UV (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
    (HahnSeries.C x_K) (HahnSeries.C y_K) U V i
  have hmap (u0 v0 : K5) : (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) (HahnSeries.C u0) (HahnSeries.C v0) i : LaurentSeries K5) =
      HahnSeries.C (QY_num S_K Q_K T_K x_K y_K u0 v0 i) := by
    fin_cases i <;> simp only [QY_num, Omega_F, dDX2_F, F_contract, dF5_fn, dH0_fn, dDX2_fn, DX2_of, DY2_of,
      om_fn, br_fn, LX_of, LY_of, dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of,
      map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat, map_zero, map_one]
  have h00 := hmap 0 0; have h01 := hmap 0 1; have h10 := hmap 1 0; have h11 := hmap 1 1
  simp only [map_zero, map_one] at h00 h01 h10 h11
  rw [hbi, h00, h01, h10, h11, ← map_sub, ← map_sub, ← map_sub, ← map_sub, ← map_add]
  exact hlinU.eq_c (by rw [evalBivK5_QY10]; ring)

private lemma br1_inf_QX_valLead {U V : LaurentSeries K5} {w0 : K5}
    (hU_L : ValLead (-1) U 1) (hV_L : ValLead 1 V w0) (i : Fin 3) :
    ValLead (-1)
      (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V i)
      (evalBivK5 (QX10_biv i) / 1701) := by
  have hlinU {a00 a01 a10 a11 : K5} :
      ValLead (-1) (HahnSeries.C a00 + HahnSeries.C a01 * V + HahnSeries.C a10 * U + HahnSeries.C a11 * U * V) a10 := by
    have hre : HahnSeries.C a00 + HahnSeries.C a01 * V + HahnSeries.C a10 * U + HahnSeries.C a11 * U * V =
        HahnSeries.C a10 * U + (HahnSeries.C a00 + HahnSeries.C a01 * V + HahnSeries.C a11 * U * V) := by ring
    rw [hre]
    exact (((ValLead.of_C a10).mul hU_L).eq_k (by omega) |>.eq_c (mul_one _)).add_high
      ((((HasValGe.of_C a00).add (((HasValGe.of_C a01).mul hV_L.val).mono (by omega))).add
        ((((HasValGe.of_C a11).mul hU_L.val).mul hV_L.val).mono (by omega))))
  have hbi := QX_bilinear_UV (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
    (HahnSeries.C x_K) (HahnSeries.C y_K) U V i
  have hmap (u0 v0 : K5) : (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) (HahnSeries.C u0) (HahnSeries.C v0) i : LaurentSeries K5) =
      HahnSeries.C (QX_num S_K Q_K T_K x_K y_K u0 v0 i) := by
    fin_cases i <;> simp only [QX_num, Omega_F, dDY2_F, F_contract, dF5_fn, dH0_fn, dDY2_fn, DX2_of, DY2_of,
      om_fn, br_fn, LX_of, LY_of, dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of,
      map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat, map_zero, map_one]
  have h00 := hmap 0 0; have h01 := hmap 0 1; have h10 := hmap 1 0; have h11 := hmap 1 1
  simp only [map_zero, map_one] at h00 h01 h10 h11
  rw [hbi, h00, h01, h10, h11, ← map_sub, ← map_sub, ← map_sub, ← map_sub, ← map_add]
  exact hlinU.eq_c (by rw [evalBivK5_QX10]; ring)

-- Standalone Branch 1 (`W1_inf`) `ValLead (-3)` for `g (C z)` (gives `p4[-3], p3[-3], p2[-3]` and `HasValGe (-3)` for `p0..p4`)!
private lemma br1_inf_g_valLead {W1s U V ca cb c0W : LaurentSeries K5} {w0 : K5}
    (hw0_eq : w0 = -(25 / 4 : K5) * T_K * (5 * T_K - 9) ^ 2 / (S_K - 3 * Q_K) ^ 3)
    (hw0_ne : w0 ≠ 0)
    (hW_L : ValLead 0 W1s w0) (hU_L : ValLead (-1) U 1) (hV_L : ValLead 1 V w0)
    (hca_L : ValLead (-2) ca (-(4 / 81 : K5) * (S_K - 3 * Q_K) ^ 2))
    (hcb_L : ValLead (-2) cb ((4 / 27 : K5) * (S_K - 3 * Q_K) ^ 2))
    (hc0W_L : ValLead (-2) c0W (-(25 / 81 : K5) * (5 * T_K - 9) * (5 * T_K - 3))) :
    ∀ z : K5, ValLead (-3)
      (P18_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) (HahnSeries.C z / W1s) (-(ca * HahnSeries.C z + c0W) / (W1s * cb)) U V)
      ((w0 * A0V_Uk 3 (z / w0) (z / w0 / 3 + -(S_K - 3 * Q_K) * (5 * T_K - 3) / (3 * T_K * (5 * T_K - 9)))
        (S_K - z / w0 * T_K) (Q_K - (z / w0 / 3 + -(S_K - 3 * Q_K) * (5 * T_K - 3) / (3 * T_K * (5 * T_K - 9))) * T_K)) *
       ((evalBivK5 q1_m1_u1_biv / 107163) * (z / w0) + (evalBivK5 q1_m1_u0_biv / (3 * T_K * (5 * T_K - 9) * 107163)))) := by
  intro z
  set S3Q := S_K - 3 * Q_K; set T59 := 5 * T_K - 9
  set c0_num := -S3Q * (5 * T_K - 3)
  have hS3Q : S3Q ≠ 0 := S_K_sub_3Q_ne; have hT : T_K ≠ 0 := T_K_ne_zero; have hT59 : T59 ≠ 0 := fiveT_sub_9_ne
  have hS3Q_def : S_K - 3 * Q_K = S3Q := rfl
  have hT59_def : 5 * T_K - 9 = T59 := rfl
  have hw0_eq' : w0 = -(25 / 4 : K5) * T_K * T59 ^ 2 / S3Q ^ 3 := hw0_eq
  have h9_ne : (9 : K5) ≠ 0 := ofNat_ne_zero 9
  have hcb_ne : (4 / 27 : K5) * S3Q ^ 2 ≠ 0 :=
    mul_ne_zero (div_ne_zero (ofNat_ne_zero 4) (ofNat_ne_zero 27)) (pow_ne_zero 2 hS3Q)
  set zL : LaurentSeries K5 := HahnSeries.C z
  rw [P18_of_HahnC_eq]
  set a_s := zL / W1s
  set b_s := -(ca * zL + c0W) / (W1s * cb)
  set u : K5 := z / w0
  set β : K5 := c0_num / (3 * T_K * T59)
  set b0 : K5 := u / 3 + β
  have hz_L : ValLead 0 zL z := ValLead.of_C z
  have ha_L : ValLead 0 a_s u := (hz_L.div_of_ne hW_L hw0_ne).eq_k (by omega)
  have hb_L : ValLead 0 b_s b0 := by
    have hnum : ValLead (-2) _ _ := (((hca_L.mul hz_L).eq_k (by omega)).add hc0W_L).neg
    have hden : ValLead (-2) _ _ := (hW_L.mul hcb_L).eq_k (by omega)
    refine ((hnum.div_of_ne hden (mul_ne_zero hw0_ne hcb_ne)).eq_k (by omega)).eq_c ?_
    dsimp only [b0, u, β, c0_num]; rw [hw0_eq']
    field_simp [hS3Q, hT, hT59]; ring
  set ξS_s := HahnSeries.C S_K - a_s * HahnSeries.C T_K
  set ξQ_s := HahnSeries.C Q_K - b_s * HahnSeries.C T_K
  set ξS0 : K5 := S_K - u * T_K
  set ξQ0 : K5 := Q_K - b0 * T_K
  have hξS_L : ValLead 0 ξS_s ξS0 := (ValLead.of_C S_K).sub ((ha_L.mul (ValLead.of_C T_K)).eq_k (by omega))
  have hξQ_L : ValLead 0 ξQ_s ξQ0 := (ValLead.of_C Q_K).sub ((hb_L.mul (ValLead.of_C T_K)).eq_k (by omega))
  have hUk_L (k : Fin 4) (mi : Fin 10) :
      ValLead 0 (numM_Uk k mi a_s b_s ξS_s ξQ_s) (numM_Uk k mi u b0 ξS0 ξQ0) :=
    numM_Uk_valLead k mi ha_L hb_L hξS_L hξQ_L
  have hnumM_L (mi : Fin 10) : ValLead (-1) (numM mi a_s b_s ξS_s ξQ_s U V) (w0 ^ 2 * numM_Uk 3 mi u b0 ξS0 ξQ0) := by
    rw [numM_split_UV]
    have hmain : ValLead (-1) (V ^ 2 * (U ^ 3 * numM_Uk 3 mi a_s b_s ξS_s ξQ_s))
        (w0 ^ 2 * numM_Uk 3 mi u b0 ξS0 ξQ0) :=
      (((hV_L.pow 2).mul ((hU_L.pow 3).mul (hUk_L 3 mi))).eq_k (by omega)).eq_c (by ring)
    have hhi : HasValGe 0 (V ^ 2 * (U ^ 2 * numM_Uk 2 mi a_s b_s ξS_s ξQ_s +
        U * numM_Uk 1 mi a_s b_s ξS_s ξQ_s + numM_Uk 0 mi a_s b_s ξS_s ξQ_s)) := by
      have h2 := ((hU_L.val.pow 2).mul (hUk_L 2 mi).val).mono (k2 := -2) (by omega)
      have h1 := (hU_L.val.mul (hUk_L 1 mi).val).mono (k2 := -2) (by omega)
      have h0 := (hUk_L 0 mi).val.mono (k2 := -2) (by omega)
      exact ((hV_L.val.pow 2).mul ((h2.add h1).add h0)).mono (by omega)
    have hre : V ^ 2 * (U ^ 3 * numM_Uk 3 mi a_s b_s ξS_s ξQ_s + U ^ 2 * numM_Uk 2 mi a_s b_s ξS_s ξQ_s +
        U * numM_Uk 1 mi a_s b_s ξS_s ξQ_s + numM_Uk 0 mi a_s b_s ξS_s ξQ_s) =
        V ^ 2 * (U ^ 3 * numM_Uk 3 mi a_s b_s ξS_s ξQ_s) +
        V ^ 2 * (U ^ 2 * numM_Uk 2 mi a_s b_s ξS_s ξQ_s + U * numM_Uk 1 mi a_s b_s ξS_s ξQ_s +
          numM_Uk 0 mi a_s b_s ξS_s ξQ_s) := by ring
    rw [hre]; exact hmain.add_high hhi
  have hm1 (i : Fin 10) : HasValGe (-1) (numM i a_s b_s ξS_s ξQ_s U V) := (hnumM_L i).val
  have hsc1 (r : K5) {f : LaurentSeries K5} (hf : HasValGe (-1) f) : HasValGe (-1) (HahnSeries.C r * f) :=
    ((HasValGe.of_C r).mul hf).mono (by omega)
  have hnat1 (n : ℕ) [n.AtLeastTwo] {f : LaurentSeries K5} (hf : HasValGe (-1) f) :
      HasValGe (-1) ((no_index (OfNat.ofNat n) : LaurentSeries K5) * f) :=
    ((HasValGe.of_ofNat n).mul hf).mono (by omega)
  have hp1 (i j : Fin 10) : HasValGe (-1) (5 * numM i a_s b_s ξS_s ξQ_s U V - 9 * numM j a_s b_s ξS_s ξQ_s U V) :=
    (hnat1 5 (hm1 i)).sub (hnat1 9 (hm1 j))
  have hA0U_0 : HasValGe 0 (A_0U a_s b_s ξS_s ξQ_s U V / U) := by
    have hA0U_1 : HasValGe (-1) (A_0U a_s b_s ξS_s ξQ_s U V) := by
      unfold A_0U; simpa only [map_div₀, map_neg, map_ofNat] using
        (((hsc1 (-(19708 / 1257375 : K5)) (hp1 0 1)).add (hsc1 (1472 / 1257375 : K5) (hp1 1 2))).sub
          (hsc1 (16 / 729 : K5) (hp1 3 5))).add (hsc1 (188 / 2025 : K5) (hp1 4 6))
    exact (hA0U_1.div_of_lead_ne hU_L.val (hU_L.c0.symm ▸ one_ne_zero)).1.mono (by omega)
  have hA0V_L : ValLead (-2) (A_0V a_s b_s ξS_s ξQ_s U V / V) (w0 * A0V_Uk 3 u b0 ξS0 ξQ0) := by
    have hV_m1 : ValLead (-1) (A_0V a_s b_s ξS_s ξQ_s U V) (w0 ^ 2 * A0V_Uk 3 u b0 ξS0 ξQ0) := by
      refine (A0V_ValLead_of hnumM_L).eq_c ?_
      simp only [A0V_Uk]; ring
    exact (hV_m1.div_of_ne hV_L hw0_ne).eq_k (by omega) |>.eq_c (by field_simp [hw0_ne])
  have hM0_L : ValLead (-2) (A_0U a_s b_s ξS_s ξQ_s U V / U + A_0V a_s b_s ξS_s ξQ_s U V / V)
      (w0 * A0V_Uk 3 u b0 ξS0 ξQ0) := by
    rw [add_comm]; exact hA0V_L.add_high (hA0U_0.mono (by omega))
  have hAX_2 : HasValGe (-2) (A_X a_s b_s ξS_s ξQ_s U V) := by
    unfold A_X
    refine (hU_L.val.mul (?_ : HasValGe (-1) _)).mono (by omega)
    simpa only [map_div₀, map_neg, map_ofNat] using
      ((hsc1 (-(8 / 405 : K5)) (hp1 3 4)).sub (hsc1 (476 / 7185 : K5) (hp1 7 8))).add
        (hsc1 (6916 / 35925 : K5) (hp1 8 9))
  have hAY_1 : HasValGe (-1) (A_Y a_s b_s ξS_s ξQ_s U V) := by
    unfold A_Y
    refine (HasValGe.add (HasValGe.add ?_ ?_) ?_)
    · simpa only [map_div₀, map_neg, map_ofNat] using
        hsc1 (-(100 / 243 : K5)) ((((hnat1 25 (hm1 3)).sub (hnat1 45 (hm1 4))).sub (hnat1 45 (hm1 5))).add (hnat1 81 (hm1 6)))
    · refine (hV_L.val.mul (?_ : HasValGe (-1) _)).mono (by omega)
      simpa only [map_div₀, map_neg, map_ofNat] using
        (((hsc1 (-(907876 / 33949125 : K5)) (hp1 0 1)).add (hsc1 (2258324 / 33949125 : K5) (hp1 1 2))).add
          (hsc1 (8 / 243 : K5) (hp1 3 5))).sub (hsc1 (64 / 675 : K5) (hp1 4 6))
    · refine ((hU_L.val.mul hV_L.val).mul (?_ : HasValGe (-1) _)).mono (by omega)
      simpa only [map_div₀, map_neg, map_ofNat] using
        (hsc1 (-(123236 / 24249375 : K5)) ((((hm1 0).add (hsc1 (2790 / 77 : K5) (hm1 6))).add (hnat1 28 (hm1 8))).sub
          (hsc1 (5904 / 77 : K5) (hm1 9)))).add
        (hsc1 (492944 / 33949125 : K5) ((((hm1 1).add (hsc1 (927 / 77 : K5) (hm1 6))).add (hsc1 (49 / 5 : K5) (hm1 8))).sub
          (hsc1 (21159 / 770 : K5) (hm1 9))))
  have hu_L : ValLead (-1) (u_of U) (1 / 9 : K5) := by
    unfold u_of
    simpa only [sub_eq_add_neg, map_neg, map_one] using
      ((hU_L.add_high (HasValGe.of_C (-1 : K5))).div_of_ne (ValLead.of_ofNat 9) h9_ne).eq_k (by omega)
  have hv_L : ValLead 0 (v_of V) (-(1 / 9 : K5)) := by
    unfold v_of
    have hV0 : ValLead 0 V 0 := ValLead.of_hasValGe_succ (k := 0) (hV_L.val.mono (by omega))
    exact ((hV0.sub (ValLead.of_C 1)).div_of_ne (ValLead.of_ofNat 9) h9_ne).eq_k (by omega) |>.eq_c (by ring)
  have hneg19_ne : (-(1 / 9 : K5)) ≠ 0 := neg_ne_zero.mpr (div_ne_zero one_ne_zero h9_ne)
  have hEB_L := br1_inf_EB_valLead hU_L hV_L
  have hQY_L := br1_inf_QY_valLead hU_L hV_L
  have hQX_L := br1_inf_QX_valLead hU_L hV_L
  have hqY_L : ValLead (-1)
      (dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / v_of V)
      (-9 * ((evalBivK5 (QY10_biv 1) * c0_num + 3 * T_K * T59 * evalBivK5 (QY10_biv 2)) / (3 * T_K * T59 * 1701))) := by
    have hdot := ((((hQY_L 0).mul ha_L).eq_k (k' := -1) (by omega)).add (((hQY_L 1).mul hb_L).eq_k (k' := -1) (by omega))).add (hQY_L 2)
    refine valLead_eq_fc ((hdot.div_of_ne hv_L hneg19_ne).eq_k (k' := -1) (by omega)) (by simp only [dot_ab]) ?_
    have hqy0 : 3 * evalBivK5 (QY10_biv 0) + evalBivK5 (QY10_biv 1) = 0 := by
      rw [evalBivK5_QY10, evalBivK5_QY10]; linear_combination 1701 * QY_10_u1_zero S_K Q_K T_K x_K y_K
    generalize evalBivK5 (QY10_biv 0) = y0 at hqy0 ⊢
    generalize evalBivK5 (QY10_biv 1) = y1 at hqy0 ⊢
    generalize evalBivK5 (QY10_biv 2) = y2
    have hy1 : y1 = -(3 * y0) := by linear_combination hqy0
    rw [hy1]; dsimp only [b0, β]; field_simp [hT, hT59]; ring
  have hqX_L : ValLead 0
      (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / u_of U)
      (9 * (evalBivK5 cQX_0_biv / 5103 * u +
        (evalBivK5 (QX10_biv 1) * c0_num + 3 * T_K * T59 * evalBivK5 (QX10_biv 2)) / (3 * T_K * T59 * 1701))) := by
    have hdot := ((((hQX_L 0).mul ha_L).eq_k (k' := -1) (by omega)).add (((hQX_L 1).mul hb_L).eq_k (k' := -1) (by omega))).add (hQX_L 2)
    refine valLead_eq_fc ((hdot.div_of_ne hu_L (div_ne_zero one_ne_zero h9_ne)).eq_k (k' := 0) (by omega)) (by simp only [dot_ab]) ?_
    simp only [cQX_0_biv, evalBivK5_bivAdd, evalBivK5_bivScale, b0, β]
    generalize evalBivK5 (QX10_biv 0) = x0
    generalize evalBivK5 (QX10_biv 1) = x1
    generalize evalBivK5 (QX10_biv 2) = x2
    push_cast; field_simp [hT, hT59]; ring
  have hA1_L : ValLead 0 (A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V) ((25 / 27 : K5) * T_K * T59 ^ 2) := by
    have hre : A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V =
        -(4 / 27 : LaurentSeries K5) * HahnSeries.C S3Q ^ 3 * (U * V) +
        (25 / 27 : LaurentSeries K5) * HahnSeries.C (S_K * (5 * S_K - 9 * Q_K) ^ 2) * V := by
      simp only [A1_of, S3Q, map_sub, map_mul, map_pow, map_ofNat]; ring
    rw [hre]
    have hmain : ValLead 0 (-(4 / 27 : LaurentSeries K5) * HahnSeries.C S3Q ^ 3 * (U * V)) ((25 / 27 : K5) * T_K * T59 ^ 2) := by
      rw [show -(4 / 27 : LaurentSeries K5) = HahnSeries.C (-(4 / 27 : K5)) by simp only [map_div₀, map_neg, map_ofNat]]
      exact (((ValLead.of_C _).mul ((ValLead.of_C S3Q).pow 3)).mul (hU_L.mul hV_L)).eq_k (by omega) |>.eq_c (by
        rw [hw0_eq']; field_simp [hS3Q])
    have hhi : HasValGe 1 ((25 / 27 : LaurentSeries K5) * HahnSeries.C (S_K * (5 * S_K - 9 * Q_K) ^ 2) * V) := by
      rw [show (25 / 27 : LaurentSeries K5) = HahnSeries.C (25 / 27 : K5) by simp only [map_div₀, map_ofNat]]
      exact (((HasValGe.of_C _).mul (HasValGe.of_C _)).mul hV_L.val).mono (by omega)
    exact hmain.add_high hhi
  have hB1_L : ValLead (-1) (B1_of (HahnSeries.C T_K) U V) ((25 / 27 : K5) * T_K * T59 ^ 2) := by
    have hre : B1_of (HahnSeries.C T_K) U V =
        HahnSeries.C ((25 / 27 : K5) * T_K * T59 ^ 2) * U +
        HahnSeries.C (-(4 / 27 : K5) * (T_K - 3) ^ 3) * (U * V) := by
      simp only [B1_of, T59, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]; ring
    rw [hre]
    exact (((ValLead.of_C _).mul hU_L).eq_k (by omega) |>.eq_c (mul_one _)).add_high
      (((HasValGe.of_C _).mul (hU_L.val.mul hV_L.val)).mono (by omega))
  have hH0_L : ValLead 0 (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)) (ringEval vK5 H0_int_e / 7) := by
    rw [show H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) = HahnSeries.C (H0_of S_K Q_K T_K) by
      simp only [H0_of, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]]
    exact (ValLead.of_C _).eq_c (by rw [ringEval_H0_7_inf]; ring)
  have hcA1_L : ValLead 0 (cA1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) a_s b_s U V)
      ((ringEval vK5 H0_int_e / 7) * ((25 / 9 : K5) * T59 * (5 * T_K - 3)) -
       ((25 / 27 : K5) * T_K * T59 ^ 2) * (ringEval vK5 dH0_301_21_e / 21 * u +
         (ringEval vK5 (dH0_7_inf_e 1) * c0_num + 3 * T_K * T59 * ringEval vK5 (dH0_7_inf_e 2)) / (21 * T_K * T59))) := by
    have hdA1_0 : ValLead 0 (dA1_fn 0 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V) ((25 / 9 : K5) * T_K * T59 ^ 2 / S3Q) := by
      have hre : dA1_fn 0 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V =
          HahnSeries.C (-(4 / 9 : K5) * S3Q ^ 2) * (U * V) +
          HahnSeries.C ((25 / 27 : K5) * (5 * S_K - 9 * Q_K) * (15 * S_K - 9 * Q_K)) * V := by
        simp only [dA1_fn, S3Q, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]; ring
      rw [hre]
      exact (((ValLead.of_C _).mul (hU_L.mul hV_L)).eq_k (by omega) |>.eq_c (by rw [hw0_eq']; field_simp [hS3Q])).add_high
        (((HasValGe.of_C _).mul hV_L.val).mono (by omega))
    have hdA1_1 : ValLead 0 (dA1_fn 1 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V) (-(25 / 3 : K5) * T_K * T59 ^ 2 / S3Q) := by
      have hre : dA1_fn 1 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V =
          HahnSeries.C ((4 / 3 : K5) * S3Q ^ 2) * (U * V) +
          HahnSeries.C (-(450 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)) * V := by
        simp only [dA1_fn, S3Q, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]; ring
      rw [hre]
      exact (((ValLead.of_C _).mul (hU_L.mul hV_L)).eq_k (by omega) |>.eq_c (by rw [hw0_eq']; field_simp [hS3Q])).add_high
        (((HasValGe.of_C _).mul hV_L.val).mono (by omega))
    have hdH0_L (k : Fin 3) : ValLead 0 (dH0_fn k (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K))
        (ringEval vK5 (dH0_7_inf_e k) / 7) := by
      rw [show dH0_fn k (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) = HahnSeries.C (dH0_fn k S_K Q_K T_K) by
        fin_cases k <;> simp only [dH0_fn, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]]
      exact (ValLead.of_C _).eq_c (by rw [ringEval_dH0_7_inf]; ring)
    have ht0 : ValLead 0 _ _ := (((hH0_L.mul hdA1_0).sub (hA1_L.mul (hdH0_L 0))).mul ha_L).eq_k (by omega)
    have ht1 : ValLead 0 _ _ := (((hH0_L.mul hdA1_1).sub (hA1_L.mul (hdH0_L 1))).mul hb_L).eq_k (by omega)
    have ht2 : ValLead 0 _ _ := (((hH0_L.mul (ValLead.of_C 0)).sub (hA1_L.mul (hdH0_L 2)))).eq_k (by omega)
    have hre0 : dA1_fn 2 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V = HahnSeries.C 0 := by simp [dA1_fn]
    refine valLead_eq_fc ((ht0.add ht1).add ht2) (by unfold cA1_of; rw [hre0]) ?_
    simp only [dH0_301_21_e, ringEval, b0, β, c0_num]
    field_simp [hS3Q, hT, hT59]; ring
  have hq1_L : ValLead (-1)
      (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) * A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V *
        (dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / v_of V) +
       H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) * B1_of (HahnSeries.C T_K) U V *
        (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / u_of U) +
       (cA1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) a_s b_s U V / v_of V) *
        EB_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V)
      ((evalBivK5 q1_m1_u1_biv / 107163) * u + (evalBivK5 q1_m1_u0_biv / (3 * T_K * T59 * 107163))) := by
    have ht1 : ValLead (-1) _ _ := ((hH0_L.mul hA1_L).mul hqY_L).eq_k (by omega)
    have ht2 : ValLead (-1) _ _ := ((hH0_L.mul hB1_L).mul hqX_L).eq_k (by omega)
    have ht3 : ValLead (-1) _ _ := ((hcA1_L.div_of_ne hv_L hneg19_ne).mul hEB_L).eq_k (by omega)
    refine valLead_eq_fc ((ht1.add ht2).add ht3) (by ring) ?_
    have hS3Q_e : ringEval vK5 S3Q_e = S3Q := rfl
    have hT59_e : ringEval vK5 T59_e = T59 := rfl
    simp only [q1_m1_u1_biv, q1_m1_u0_biv, evalBivK5_bscE, evalBivK5_bivAdd, ringEval,
      hT59_e, hS3Q_e, T53_e, c0_num_e, eT, vK5, c0_num]
    field_simp [hT, hT59]; ring
  have hrest : HasValGe (-2)
      ((A_Y a_s b_s ξS_s ξQ_s U V *
        (dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / v_of V) +
        A_X a_s b_s ξS_s ξQ_s U V *
        (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / u_of U)) *
       H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) ^ 2) :=
    hasValGe_eq_f (((((hAY_1.mul hqY_L.val).mono (k2 := -2) (by omega)).add
      ((hAX_2.mul hqX_L.val).mono (k2 := -2) (by omega))).mul (hH0_L.val.pow 2)).mono (k2 := -2) (by omega))
      rfl
  exact valLead_eq_fc (((hM0_L.mul hq1_L).eq_k (k' := -3) (by omega)).add_high hrest) rfl
    (by dsimp only [u, b0, β, c0_num, S3Q, T59, ξS0, ξQ0])

private lemma br1_inf_hbi_D {U V : LaurentSeries K5} {w0 w1 : K5}
    (hU_D : ValDual (-1) U (Dual.C 1)) (hV_D : ValDual 1 V ⟨w0, w1⟩)
    (a00 a01 a10 a11 : K5) :
    ValDual (-1) (HahnSeries.C a00 + HahnSeries.C a01 * V + HahnSeries.C a10 * U + HahnSeries.C a11 * U * V)
      ⟨a10, a00 + a11 * w0⟩ := by
  have hre : HahnSeries.C a00 + HahnSeries.C a01 * V + HahnSeries.C a10 * U + HahnSeries.C a11 * U * V =
      (HahnSeries.C a10 * U + (HahnSeries.C a00 + HahnSeries.C a11 * (U * V))) + HahnSeries.C a01 * V := by ring
  rw [hre]
  have hm : ValDual (-1) (HahnSeries.C a10 * U) (Dual.C a10) :=
    ((ValDual.of_C a10).mul hU_D).eq_k (by omega) |>.eq_d (by rw [← map_mul, mul_one])
  have hs : ValLead 0 (HahnSeries.C a00 + HahnSeries.C a11 * (U * V)) (a00 + a11 * w0) :=
    ((ValLead.of_C a00).add (((ValLead.of_C a11).mul ((hU_D.toValLead.mul hV_D.toValLead).eq_k (k' := 0) (by omega))).eq_k (k' := 0) (by omega))).eq_c (by simp only [Dual.C_val]; ring)
  have hhi : HasValGe 1 (HahnSeries.C a01 * V) := ((HasValGe.of_C a01).mul hV_D.val).mono (by omega)
  exact ((hm.add_shift1 hs).add_high hhi).eq_d (by ext <;> simp)

private lemma br1_inf_EB_valDual {U V : LaurentSeries K5} {w0 w1 : K5}
    (hU_D : ValDual (-1) U (Dual.C 1)) (hV_D : ValDual 1 V ⟨w0, w1⟩) :
    ValDual (-1) (EB_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V) ⟨evalBivK5 EB10_biv / 243, evalBivK5 EB11_biv / 243 * w0⟩ := by
  have hbi := EB_bilinear_UV (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
    (HahnSeries.C x_K) (HahnSeries.C y_K) U V
  have hmap (u0 v0 : K5) : (EB_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) (HahnSeries.C u0) (HahnSeries.C v0) : LaurentSeries K5) =
      HahnSeries.C (EB_of S_K Q_K T_K x_K y_K u0 v0) := by
    simp only [EB_of, W2_of, DX2_of, DY2_of, dF5_fn, br_fn, LX_of, LY_of,
      dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of,
      map_add, map_sub, map_mul, map_div₀, map_pow, map_ofNat, map_zero, map_one]
  have h00 := hmap 0 0; have h01 := hmap 0 1; have h10 := hmap 1 0; have h11 := hmap 1 1
  simp only [map_zero, map_one] at h00 h01 h10 h11
  rw [hbi, h00, h01, h10, h11, ← map_sub, ← map_sub, ← map_sub, ← map_sub, ← map_add]
  exact (br1_inf_hbi_D hU_D hV_D _ _ _ _).eq_d (by
    have hEB00 : EB_of S_K Q_K T_K x_K y_K 0 0 = 0 := by simp only [EB_of, br_fn, dLX_fn, dLY_fn]; ring
    ext
    · rw [evalBivK5_EB10]; ring
    · rw [evalBivK5_EB11, hEB00]; ring)

private lemma br1_inf_QY_valDual {U V : LaurentSeries K5} {w0 w1 : K5}
    (hU_D : ValDual (-1) U (Dual.C 1)) (hV_D : ValDual 1 V ⟨w0, w1⟩) (i : Fin 3) :
    ValDual (-1)
      (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V i)
      ⟨evalBivK5 (QY10_biv i) / 1701, evalBivK5 (QY00_biv i) / 1701 + evalBivK5 (QY11_biv i) / 1701 * w0⟩ := by
  have hbi := QY_bilinear_UV (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
    (HahnSeries.C x_K) (HahnSeries.C y_K) U V i
  have hmap (u0 v0 : K5) : (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) (HahnSeries.C u0) (HahnSeries.C v0) i : LaurentSeries K5) =
      HahnSeries.C (QY_num S_K Q_K T_K x_K y_K u0 v0 i) := by
    fin_cases i <;> simp only [QY_num, Omega_F, dDX2_F, F_contract, dF5_fn, dH0_fn, dDX2_fn, DX2_of, DY2_of,
      om_fn, br_fn, LX_of, LY_of, dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of,
      map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat, map_zero, map_one]
  have h00 := hmap 0 0; have h01 := hmap 0 1; have h10 := hmap 1 0; have h11 := hmap 1 1
  simp only [map_zero, map_one] at h00 h01 h10 h11
  rw [hbi, h00, h01, h10, h11, ← map_sub, ← map_sub, ← map_sub, ← map_sub, ← map_add]
  exact (br1_inf_hbi_D hU_D hV_D _ _ _ _).eq_d (by ext <;> rw [evalBivK5_QY10, evalBivK5_QY00, evalBivK5_QY11] <;> ring)

private lemma br1_inf_QX_valDual {U V : LaurentSeries K5} {w0 w1 : K5}
    (hU_D : ValDual (-1) U (Dual.C 1)) (hV_D : ValDual 1 V ⟨w0, w1⟩) (i : Fin 3) :
    ValDual (-1)
      (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V i)
      ⟨evalBivK5 (QX10_biv i) / 1701, evalBivK5 (QX00_biv i) / 1701 + evalBivK5 (QX11_biv i) / 1701 * w0⟩ := by
  have hbi := QX_bilinear_UV (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
    (HahnSeries.C x_K) (HahnSeries.C y_K) U V i
  have hmap (u0 v0 : K5) : (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) (HahnSeries.C u0) (HahnSeries.C v0) i : LaurentSeries K5) =
      HahnSeries.C (QX_num S_K Q_K T_K x_K y_K u0 v0 i) := by
    fin_cases i <;> simp only [QX_num, Omega_F, dDY2_F, F_contract, dF5_fn, dH0_fn, dDY2_fn, DX2_of, DY2_of,
      om_fn, br_fn, LX_of, LY_of, dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of,
      map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat, map_zero, map_one]
  have h00 := hmap 0 0; have h01 := hmap 0 1; have h10 := hmap 1 0; have h11 := hmap 1 1
  simp only [map_zero, map_one] at h00 h01 h10 h11
  rw [hbi, h00, h01, h10, h11, ← map_sub, ← map_sub, ← map_sub, ← map_sub, ← map_add]
  exact (br1_inf_hbi_D hU_D hV_D _ _ _ _).eq_d (by ext <;> rw [evalBivK5_QX10, evalBivK5_QX00, evalBivK5_QX11] <;> ring)

private lemma br1_inf_fV_lead3_valDual {U V aa rca ab b0s : LaurentSeries K5} {w0 w1 : K5}
    (hw1_eq : w1 = w0 * ((243 / 4 : K5) * k5Params.Bv1 / (S_K - 3 * Q_K) ^ 3))
    (hw0_ne : w0 ≠ 0) (hab_eq : ab = rca * aa)
    (hU_D : ValDual (-1) U (Dual.C 1)) (hV_D : ValDual 1 V ⟨w0, w1⟩)
    (hrca_D : ValDual 0 rca ⟨1 / 3, (-(3 / 28 : K5) * (S_K - 3 * Q_K) *
      (119 * S_K ^ 2 - 560 * S_K * Q_K + 630 * Q_K ^ 2 + 90 * Q_K + 90)) / (3 * (S_K - 3 * Q_K) ^ 3)⟩)
    (haa_D : ValDual 0 aa ⟨w0⁻¹, -w1 / w0 ^ 2⟩)
    (hab_D : ValDual 0 ab (⟨1 / 3, (-(3 / 28 : K5) * (S_K - 3 * Q_K) *
      (119 * S_K ^ 2 - 560 * S_K * Q_K + 630 * Q_K ^ 2 + 90 * Q_K + 90)) / (3 * (S_K - 3 * Q_K) ^ 3)⟩ * ⟨w0⁻¹, -w1 / w0 ^ 2⟩))
    (hb0_L : ValLead 0 b0s (-((S_K - 3 * Q_K) * (5 * T_K - 3)) / (3 * T_K * (5 * T_K - 9)))) :
    let fV : LaurentSeries K5 → LaurentSeries K5 := fun z =>
      A_0V (aa * z) (ab * z + b0s) (HahnSeries.C S_K - aa * z * HahnSeries.C T_K)
        (HahnSeries.C Q_K - (ab * z + b0s) * HahnSeries.C T_K) U V / V
    let S3Q := S_K - 3 * Q_K; let T59 := 5 * T_K - 9
    ValDual (-2) ((fV 2 - 3 * fV 1 + 3 * fV 0 - fV (-1)) / 6)
      ⟨w0⁻¹ ^ 2 * ((73 / 7971615 : K5) * T59 * S3Q ^ 2),
       w0⁻¹ ^ 2 * (M01_q_fn S_K Q_K T_K * T59 * S3Q / (267288250950 * S3Q ^ 3))⟩ := by
  intro fV S3Q T59
  have hS3Q := S_K_sub_3Q_ne
  set rb_sc : K5 := -(3 / 28 : K5) * S3Q * (119 * S_K ^ 2 - 560 * S_K * Q_K + 630 * Q_K ^ 2 + 90 * Q_K + 90)
  set r1 : K5 := rb_sc / (3 * S3Q ^ 3)
  have hV_ne : V ≠ 0 := fun h0 => hw0_ne (by have h := hV_D.c0; rw [h0, HahnSeries.coeff_zero] at h; exact h.symm)
  let leadA0V (k : Fin 4) : LaurentSeries K5 :=
    let f := fun z : LaurentSeries K5 => A0V_Uk k (aa * z) (ab * z + b0s)
      (HahnSeries.C S_K - aa * z * HahnSeries.C T_K) (HahnSeries.C Q_K - (ab * z + b0s) * HahnSeries.C T_K)
    (f 2 - 3 * f 1 + 3 * f 0 - f (-1)) / 6
  have hfV_eq : (fV 2 - 3 * fV 1 + 3 * fV 0 - fV (-1)) / 6 =
      V * U ^ 3 * A0V_U3_lead3_fn (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) aa ab +
      V * U ^ 2 * leadA0V 2 + V * (U * leadA0V 1 + leadA0V 0) := by
    have hsp (z : LaurentSeries K5) : fV z =
        V * (U ^ 3 * A0V_Uk 3 (aa * z) (ab * z + b0s) (HahnSeries.C S_K - aa * z * HahnSeries.C T_K)
          (HahnSeries.C Q_K - (ab * z + b0s) * HahnSeries.C T_K) +
        U ^ 2 * A0V_Uk 2 (aa * z) (ab * z + b0s) (HahnSeries.C S_K - aa * z * HahnSeries.C T_K)
          (HahnSeries.C Q_K - (ab * z + b0s) * HahnSeries.C T_K) +
        U * A0V_Uk 1 (aa * z) (ab * z + b0s) (HahnSeries.C S_K - aa * z * HahnSeries.C T_K)
          (HahnSeries.C Q_K - (ab * z + b0s) * HahnSeries.C T_K) +
        A0V_Uk 0 (aa * z) (ab * z + b0s) (HahnSeries.C S_K - aa * z * HahnSeries.C T_K)
          (HahnSeries.C Q_K - (ab * z + b0s) * HahnSeries.C T_K)) := by
      dsimp only [fV]; rw [A_0V_split_UV]; field_simp [hV_ne]
    dsimp only [leadA0V]
    rw [hsp 2, hsp 1, hsp 0, hsp (-1),
      ← A0V_U3_lead3_eq (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) aa ab b0s]
    ring
  rw [hfV_eq]
  have hhom3 : A0V_U3_lead3_fn (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) aa ab =
      aa ^ 3 * A0V_U3_lead3_fn (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) 1 rca := by
    rw [hab_eq]; simp only [A0V_U3_lead3_fn]; ring
  have hD1 : ValDual (-2) (V * U ^ 3 * A0V_U3_lead3_fn (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) aa ab)
      (⟨w0, w1⟩ * ⟨w0⁻¹, -w1 / w0 ^ 2⟩ ^ 3 *
       ⟨(73 / 7971615 : K5) * T59 * S3Q ^ 2,
        -(2 / 2121335325 : K5) * T59 * (-464630 * S_K + 1568725 * Q_K + 34020 * T_K - 23814) * (-S_K + 3 * Q_K) * r1⟩) := by
    rw [hhom3]
    have hpoly : ValDual 0 (A0V_U3_lead3_fn (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) 1 rca)
        ⟨(73 / 7971615 : K5) * T59 * S3Q ^ 2,
         -(2 / 2121335325 : K5) * T59 * (-464630 * S_K + 1568725 * Q_K + 34020 * T_K - 23814) * (-S_K + 3 * Q_K) * r1⟩ := by
      set c0_p : K5 := -7728665 * Q_K ^ 2 - 1746360 * Q_K * T_K + 6563302 * Q_K + 5340850
      set c1_p : K5 := 15457330 * S_K * Q_K + 21962150 * Q_K ^ 2 + 1746360 * S_K * T_K + 10001880 * Q_K * T_K -
        6563302 * S_K - 39046416 * Q_K - 1020600 * T_K - 42108180
      set c2_p : K5 := -7728665 * S_K ^ 2 - 43924300 * S_K * Q_K - 10001880 * S_K * T_K - 14288400 * Q_K * T_K +
        39046416 * S_K + 58069530 * Q_K + 6123600 * T_K + 108446130
      set c3_p : K5 := 21962150 * S_K ^ 2 + 14288400 * S_K * T_K - 58069530 * S_K - 9185400 * T_K - 90567720
      have hre : A0V_U3_lead3_fn (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) 1 rca =
          HahnSeries.C (-(1 / 4949782425 : K5) * T59) *
            (HahnSeries.C c0_p + HahnSeries.C c1_p * rca + HahnSeries.C c2_p * rca ^ 2 + HahnSeries.C c3_p * rca ^ 3) := by
        simp only [A0V_U3_lead3_fn, c0_p, c1_p, c2_p, c3_p, T59,
          map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat, map_one]; ring
      rw [hre]
      have hsum := (((ValDual.of_C c0_p).add (((ValDual.of_C c1_p).mul hrca_D).eq_k (k' := 0) (by omega))).add
        (((ValDual.of_C c2_p).mul (hrca_D.pow 2)).eq_k (k' := 0) (by omega))).add
        (((ValDual.of_C c3_p).mul (hrca_D.pow 3)).eq_k (k' := 0) (by omega))
      refine (((ValDual.of_C (-(1 / 4949782425 : K5) * T59)).mul hsum).eq_k (k' := 0) (by omega)).eq_d ?_
      obtain ⟨hv, he⟩ := A0V_U3_lead3_dual S_K Q_K T_K r1
      ext
      · simp only [Dual.mul_val, Dual.add_val, Dual.C_val, Dual.pow_eq, c0_p, c1_p, c2_p, c3_p]; linear_combination hv
      · simp only [Dual.mul_val, Dual.mul_eps, Dual.add_val, Dual.add_eps, Dual.C_val, Dual.C_eps,
          Dual.pow_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, c0_p, c1_p, c2_p, c3_p]; linear_combination he
    have hU3 : ValDual (-3) (U ^ 3) (Dual.C 1) := (hU_D.pow 3).eq_k (by omega) |>.eq_d (by rw [← map_pow, one_pow])
    have hre2 : V * U ^ 3 * (aa ^ 3 * A0V_U3_lead3_fn (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) 1 rca) =
        (V * aa ^ 3 * A0V_U3_lead3_fn (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) 1 rca) * U ^ 3 := by ring
    rw [hre2]
    exact ((((hV_D.mul (haa_D.pow 3)).mul hpoly).eq_k (k' := 1) (by omega)).mul hU3).eq_k (k' := -2) (by omega) |>.eq_d
      (by rw [map_one, mul_one])
  have hUk0 (k : Fin 4) (z0 : K5) : ValLead 0
      (A0V_Uk k (aa * HahnSeries.C z0) (ab * HahnSeries.C z0 + b0s)
        (HahnSeries.C S_K - aa * HahnSeries.C z0 * HahnSeries.C T_K)
        (HahnSeries.C Q_K - (ab * HahnSeries.C z0 + b0s) * HahnSeries.C T_K))
      (A0V_Uk k (w0⁻¹ * z0) ((w0⁻¹ / 3) * z0 + (-(S3Q * (5 * T_K - 3)) / (3 * T_K * T59)))
        (S_K - w0⁻¹ * z0 * T_K) (Q_K - ((w0⁻¹ / 3) * z0 + (-(S3Q * (5 * T_K - 3)) / (3 * T_K * T59))) * T_K)) := by
    have haL : ValLead 0 (aa * HahnSeries.C z0) (w0⁻¹ * z0) := (haa_D.toValLead.mul (ValLead.of_C z0)).eq_k (by omega)
    have hbL : ValLead 0 (ab * HahnSeries.C z0 + b0s) ((w0⁻¹ / 3) * z0 + (-(S3Q * (5 * T_K - 3)) / (3 * T_K * T59))) :=
      (((hab_D.toValLead.mul (ValLead.of_C z0)).eq_k (by omega)).add hb0_L).eq_c (by simp only [Dual.mul_val]; ring)
    have hξSL : ValLead 0 (HahnSeries.C S_K - aa * HahnSeries.C z0 * HahnSeries.C T_K) (S_K - w0⁻¹ * z0 * T_K) :=
      (ValLead.of_C S_K).sub ((haL.mul (ValLead.of_C T_K)).eq_k (by omega))
    have hξQL : ValLead 0 (HahnSeries.C Q_K - (ab * HahnSeries.C z0 + b0s) * HahnSeries.C T_K)
        (Q_K - ((w0⁻¹ / 3) * z0 + (-(S3Q * (5 * T_K - 3)) / (3 * T_K * T59))) * T_K) :=
      (ValLead.of_C Q_K).sub ((hbL.mul (ValLead.of_C T_K)).eq_k (by omega))
    have hC (r : K5) {f : LaurentSeries K5} {v : K5} (hf : ValLead 0 f v) :
        ValLead 0 (HahnSeries.C r * f) (r * v) := ((ValLead.of_C r).mul hf).eq_k (by omega)
    have hN (n : ℕ) [n.AtLeastTwo] {f : LaurentSeries K5} {v : K5} (hf : ValLead 0 f v) :
        ValLead 0 ((no_index (OfNat.ofNat n) : LaurentSeries K5) * f) ((no_index (OfNat.ofNat n) : K5) * v) :=
      ((ValLead.of_ofNat n).mul hf).eq_k (by omega)
    have hnum (mi : Fin 10) : ValLead 0 (numM_Uk k mi (aa * HahnSeries.C z0) (ab * HahnSeries.C z0 + b0s)
          (HahnSeries.C S_K - aa * HahnSeries.C z0 * HahnSeries.C T_K)
          (HahnSeries.C Q_K - (ab * HahnSeries.C z0 + b0s) * HahnSeries.C T_K))
        (numM_Uk k mi (w0⁻¹ * z0) ((w0⁻¹ / 3) * z0 + (-(S3Q * (5 * T_K - 3)) / (3 * T_K * T59)))
          (S_K - w0⁻¹ * z0 * T_K) (Q_K - ((w0⁻¹ / 3) * z0 + (-(S3Q * (5 * T_K - 3)) / (3 * T_K * T59))) * T_K)) :=
      numM_Uk_valLead k mi haL hbL hξSL hξQL
    have hp (i j : Fin 10) := (hN 5 (hnum i)).sub (hN 9 (hnum j))
    unfold A0V_Uk
    simpa only [map_div₀, map_neg, map_ofNat] using
      (((hC (-(892 / 3645 : K5)) (hp 3 4)).add (hC (40 / 81 : K5) (hp 5 6))).sub
        (hC (112 / 2395 : K5) (hp 7 8))).add (hC (392 / 11975 : K5) (hp 8 9))
  have h6_ne : (6 : K5) ≠ 0 := ofNat_ne_zero 6
  have hL2 : ValLead (-1) (V * U ^ 2 * leadA0V 2)
      (w0⁻¹ ^ 2 * ((1 / 53457650190 : K5) * T59 *
        (-50137409 * S_K ^ 2 + 300824454 * S_K * Q_K - 451236681 * Q_K ^ 2 - 10001880 * S_K * T_K +
         30005640 * Q_K * T_K - 45873099 * S_K + 137619297 * Q_K - 10103940 * T_K + 58998753))) := by
    have hf2 := hUk0 2 2; have hf1 := hUk0 2 1; have hf0 := hUk0 2 0; have hfm1 := hUk0 2 (-1)
    have hcomb := ((((hf2.sub (((ValLead.of_ofNat 3).mul hf1).eq_k (k' := 0) (by omega))).add
      (((ValLead.of_ofNat 3).mul hf0).eq_k (k' := 0) (by omega))).sub hfm1).div_of_ne
      (ValLead.of_ofNat 6) h6_ne).eq_k (k' := 0) (by omega)
    have hU2 : ValLead (-2) (U ^ 2) 1 := (hU_D.toValLead.pow 2).eq_k (by omega) |>.eq_c (by simp)
    refine valLead_eq_fc (((hV_D.toValLead.mul hU2).mul hcomb).eq_k (k' := -1) (by omega))
      (by dsimp only [leadA0V]; simp only [map_ofNat, map_one, map_zero, map_neg]) ?_
    have h3 := A0V_U2_lead3_at_third S_K Q_K T_K w0⁻¹ (-(S3Q * (5 * T_K - 3)) / (3 * T_K * T59))
    dsimp only at h3
    have h4 : ((A0V_Uk 2 (w0⁻¹ * 2) (w0⁻¹ / 3 * 2 + -(S3Q * (5 * T_K - 3)) / (3 * T_K * T59))
          (S_K - w0⁻¹ * 2 * T_K) (Q_K - (w0⁻¹ / 3 * 2 + -(S3Q * (5 * T_K - 3)) / (3 * T_K * T59)) * T_K) -
        (3 : K5) * A0V_Uk 2 (w0⁻¹ * 1) (w0⁻¹ / 3 * 1 + -(S3Q * (5 * T_K - 3)) / (3 * T_K * T59))
          (S_K - w0⁻¹ * 1 * T_K) (Q_K - (w0⁻¹ / 3 * 1 + -(S3Q * (5 * T_K - 3)) / (3 * T_K * T59)) * T_K) +
        (3 : K5) * A0V_Uk 2 (w0⁻¹ * 0) (w0⁻¹ / 3 * 0 + -(S3Q * (5 * T_K - 3)) / (3 * T_K * T59))
          (S_K - w0⁻¹ * 0 * T_K) (Q_K - (w0⁻¹ / 3 * 0 + -(S3Q * (5 * T_K - 3)) / (3 * T_K * T59)) * T_K) -
        A0V_Uk 2 (w0⁻¹ * -1) (w0⁻¹ / 3 * -1 + -(S3Q * (5 * T_K - 3)) / (3 * T_K * T59))
          (S_K - w0⁻¹ * -1 * T_K) (Q_K - (w0⁻¹ / 3 * -1 + -(S3Q * (5 * T_K - 3)) / (3 * T_K * T59)) * T_K)) / (6 : K5)) =
        w0⁻¹ ^ 3 * ((1 / 53457650190 : K5) * T59 *
          (-50137409 * S_K ^ 2 + 300824454 * S_K * Q_K - 451236681 * Q_K ^ 2 - 10001880 * S_K * T_K +
           30005640 * Q_K * T_K - 45873099 * S_K + 137619297 * Q_K - 10103940 * T_K + 58998753)) := by
      simpa only [T59] using h3
    push_cast; rw [mul_one, h4]; field_simp [hw0_ne]
  have hhi0 : HasValGe 0 (V * (U * leadA0V 1 + leadA0V 0)) := by
    have h0 (k : Fin 4) : HasValGe 0 (leadA0V k) := by
      have hf2 := (hUk0 k 2).val; have hf1 := (hUk0 k 1).val; have hf0 := (hUk0 k 0).val; have hfm1 := (hUk0 k (-1)).val
      exact hasValGe_eq_f (((((hf2.sub (((HasValGe.of_ofNat 3).mul hf1).mono (k2 := 0) (by omega))).add
        (((HasValGe.of_ofNat 3).mul hf0).mono (k2 := 0) (by omega))).sub hfm1).div_of_lead_ne
        (HasValGe.of_ofNat 6) (by rw [(ValLead.of_ofNat 6).c0]; exact h6_ne)).1.mono (k2 := 0) (by omega))
        (by dsimp only [leadA0V]; simp only [map_ofNat, map_one, map_zero, map_neg])
    exact (hV_D.val.mul (((hU_D.val.mul (h0 1)).mono (k2 := -1) (by omega)).add ((h0 0).mono (k2 := -1) (by omega)))).mono (by omega)
  refine ((hD1.add_shift1 hL2).add_high hhi0).eq_d ?_
  have hcomb := M01_dual_combine S_K Q_K T_K
  have hBv1_eq : k5Params.Bv1 = (143 / 243 : K5) * S_K ^ 3 - (92 / 27) * S_K ^ 2 * Q_K + (52 / 9) * S_K * Q_K ^ 2 -
      (22 / 9) * Q_K ^ 3 + (143 / 243) * T_K ^ 3 - (92 / 27) * T_K ^ 2 + (52 / 9) * T_K - (22 / 9) +
      (5 / 7) * Q_K ^ 2 + (10 / 7) * Q_K := by
    simp only [CoverParams.Bv1, CoverParams.inv9, CoverParams.inv27, CoverParams.inv243, k5Params_inv3,
      k5Params_inv7, k5Params_S, k5Params_Q, k5Params_T]; ring
  ext
  · simp only [Dual.add_val, Dual.mul_val, Dual.pow_eq]; field_simp [hw0_ne]; ring
  · simp only [Dual.add_eps, Dual.mul_val, Dual.mul_eps, Dual.pow_eq, Nat.cast_ofNat, Nat.reduceSub]
    rw [hw1_eq, hBv1_eq]; dsimp only [r1, rb_sc, S3Q, T59] at hcomb ⊢
    set c0_loc : K5 := (73 / 7971615 : K5) * (5 * T_K - 9) * (S_K - 3 * Q_K) ^ 2
    set dc0_loc : K5 := -(2 / 2121335325 : K5) * (5 * T_K - 9) * (-464630 * S_K + 1568725 * Q_K + 34020 * T_K - 23814) * (-S_K + 3 * Q_K)
    set c2_loc : K5 := (1 / 53457650190 : K5) * (5 * T_K - 9) *
      (-50137409 * S_K ^ 2 + 300824454 * S_K * Q_K - 451236681 * Q_K ^ 2 - 10001880 * S_K * T_K +
       30005640 * Q_K * T_K - 45873099 * S_K + 137619297 * Q_K - 10103940 * T_K + 58998753)
    set m01_loc : K5 := M01_q_fn S_K Q_K T_K * (5 * T_K - 9) * (S_K - 3 * Q_K) / 267288250950
    set Bv1_loc : K5 := (143 / 243 : K5) * S_K ^ 3 - (92 / 27) * S_K ^ 2 * Q_K + (52 / 9) * S_K * Q_K ^ 2 -
      (22 / 9) * Q_K ^ 3 + (143 / 243) * T_K ^ 3 - (92 / 27) * T_K ^ 2 + (52 / 9) * T_K - (22 / 9) +
      (5 / 7) * Q_K ^ 2 + (10 / 7) * Q_K
    set rb_loc : K5 := -(3 / 28 : K5) * (S_K - 3 * Q_K) * (119 * S_K ^ 2 - 560 * S_K * Q_K + 630 * Q_K ^ 2 + 90 * Q_K + 90)
    rw [show M01_q_fn S_K Q_K T_K * (5 * T_K - 9) * (S_K - 3 * Q_K) / (267288250950 * (S_K - 3 * Q_K) ^ 3) =
      m01_loc / (S_K - 3 * Q_K) ^ 3 by dsimp only [m01_loc]; rw [div_div]]
    have hcomb' : -2 * ((243 / 4 : K5) * Bv1_loc) * c0_loc + (rb_loc / 3) * dc0_loc + (S_K - 3 * Q_K) ^ 3 * c2_loc = m01_loc := hcomb
    rw [← hcomb']
    generalize c0_loc = v0; generalize dc0_loc = v1; generalize c2_loc = v2
    generalize Bv1_loc = vB; generalize rb_loc = vr
    generalize (S_K - 3 * Q_K) = s3q at hS3Q ⊢
    field_simp [hw0_ne, hS3Q]; ring

private lemma br1_inf_q1_lead1_valDual {U V aa ab b0s : LaurentSeries K5} {w0 w1 : K5}
    (hw0_eq : w0 = -(25 / 4 : K5) * T_K * (5 * T_K - 9) ^ 2 / (S_K - 3 * Q_K) ^ 3)
    (hw1_eq : w1 = w0 * ((243 / 4 : K5) * k5Params.Bv1 / (S_K - 3 * Q_K) ^ 3))
    (hw0_ne : w0 ≠ 0)
    (hU_D : ValDual (-1) U (Dual.C 1)) (hV_D : ValDual 1 V ⟨w0, w1⟩)
    (haa_D : ValDual 0 aa ⟨w0⁻¹, -w1 / w0 ^ 2⟩)
    (hab_D : ValDual 0 ab (⟨1 / 3, (-(3 / 28 : K5) * (S_K - 3 * Q_K) *
      (119 * S_K ^ 2 - 560 * S_K * Q_K + 630 * Q_K ^ 2 + 90 * Q_K + 90)) / (3 * (S_K - 3 * Q_K) ^ 3)⟩ * ⟨w0⁻¹, -w1 / w0 ^ 2⟩)) :
    let hqY : LaurentSeries K5 → LaurentSeries K5 := fun z =>
      dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) U V) (aa * z) (ab * z + b0s) / v_of V
    let hqX : LaurentSeries K5 → LaurentSeries K5 := fun z =>
      dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) U V) (aa * z) (ab * z + b0s) / u_of U
    let hq1 : LaurentSeries K5 → LaurentSeries K5 := fun z =>
      H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) * A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V * hqY z +
      H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) * B1_of (HahnSeries.C T_K) U V * hqX z +
      (cA1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (aa * z) (ab * z + b0s) U V / v_of V) *
        EB_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V
    let S3Q := S_K - 3 * Q_K
    let r1 : K5 := (-(3 / 28 : K5) * S3Q * (119 * S_K ^ 2 - 560 * S_K * Q_K + 630 * Q_K ^ 2 + 90 * Q_K + 90)) / (3 * S3Q ^ 3)
    ValDual (-1) (hqY 1 - hqY 0)
      ⟨0, -9 * w0⁻¹ * (r1 * evalBivK5 (QY10_biv 1) / 1701 +
        evalBivK5 cQY_00_biv / 5103 + w0 * evalBivK5 cQY_11_biv / 5103)⟩ ∧
    ValDual 0 (hqX 1 - hqX 0)
      ⟨w0⁻¹ * (evalBivK5 cQX_0_biv / 567),
       w0⁻¹ * ((evalBivK5 cQX_1_biv + 28 * S3Q ^ 3 * evalBivK5 cQX_0_biv) / (28 * 567 * S3Q ^ 3))⟩ ∧
    ValDual (-1) (hq1 1 - hq1 0)
      ⟨w0⁻¹ * (evalBivK5 q1_m1_u1_biv / 107163), w0⁻¹ * (evalBivK5 q1_0_u1_biv / (28 * 107163 * S3Q ^ 3))⟩ := by
  intro hqY hqX hq1 S3Q r1
  set T59 := 5 * T_K - 9
  set rb_sc : K5 := -(3 / 28 : K5) * S3Q * (119 * S_K ^ 2 - 560 * S_K * Q_K + 630 * Q_K ^ 2 + 90 * Q_K + 90)
  have hS3Q := S_K_sub_3Q_ne; have hT := T_K_ne_zero; have hT59 := fiveT_sub_9_ne
  have h9_ne : (9 : K5) ≠ 0 := ofNat_ne_zero 9
  have hneg19_ne : (-(1 / 9 : K5)) ≠ 0 := neg_ne_zero.mpr (div_ne_zero one_ne_zero h9_ne)
  have h19_ne : (1 / 9 : K5) ≠ 0 := div_ne_zero one_ne_zero h9_ne
  have hu_D : ValDual (-1) (u_of U) ⟨1 / 9, -(1 / 9)⟩ := by
    unfold u_of
    have h1 : ValDual (-1) (U - 1) ⟨1, -1⟩ := by
      have : U - 1 = U + HahnSeries.C (-1 : K5) := by simp [sub_eq_add_neg]
      rw [this]; exact hU_D.add_shift1 (ValLead.of_C (-1)) |>.eq_d (by ext <;> simp)
    refine ((h1.div_of_ne (ValDual.of_ofNat 9) (by simpa only [Dual.C_val] using h9_ne)).eq_k (by omega)).eq_d ?_
    exact (dual_div_eq_iff _ _ _ (by simpa only [Dual.C_val] using h9_ne)).mpr (by
      ext <;> simp only [Dual.mul_val, Dual.mul_eps, Dual.C_val, Dual.C_eps] <;> ring)
  have hv_D : ValDual 0 (v_of V) ⟨-(1 / 9), w0 / 9⟩ := by
    unfold v_of
    have h1 : ValDual 0 (V - 1) ⟨-1, w0⟩ := by
      have : V - 1 = HahnSeries.C (-1 : K5) + V := by simp [sub_eq_add_neg, add_comm]
      rw [this]; exact (ValDual.of_C (-1 : K5)).add_shift1 hV_D.toValLead |>.eq_d (by ext <;> simp)
    refine ((h1.div_of_ne (ValDual.of_ofNat 9) (by simpa only [Dual.C_val] using h9_ne)).eq_k (by omega)).eq_d ?_
    exact (dual_div_eq_iff _ _ _ (by simpa only [Dual.C_val] using h9_ne)).mpr (by
      ext <;> simp only [Dual.mul_val, Dual.mul_eps, Dual.C_val, Dual.C_eps] <;> ring)
  have hEB_D := br1_inf_EB_valDual hU_D hV_D
  have hQY_D := br1_inf_QY_valDual hU_D hV_D
  have hQX_D := br1_inf_QX_valDual hU_D hV_D
  have hl1_qY_D : ValDual (-1) (hqY 1 - hqY 0)
      ⟨0, -9 * w0⁻¹ * (r1 * evalBivK5 (QY10_biv 1) / 1701 +
        evalBivK5 cQY_00_biv / 5103 + w0 * evalBivK5 cQY_11_biv / 5103)⟩ := by
    have heq : hqY 1 - hqY 0 = (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) U V 0 * aa +
        QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V 1 * ab) / v_of V := by
      dsimp only [hqY, dot_ab]; ring
    rw [heq]
    have hnum : ValDual (-1) _ _ := (((hQY_D 0).mul haa_D).eq_k (k' := -1) (by omega)).add (((hQY_D 1).mul hab_D).eq_k (k' := -1) (by omega))
    refine valDual_eq_fd ((hnum.div_of_ne hv_D hneg19_ne).eq_k (k' := -1) (by omega)) (by ring) ?_
    exact (dual_div_eq_iff _ _ _ hneg19_ne).mpr (by
      have hqy0 : 3 * evalBivK5 (QY10_biv 0) + evalBivK5 (QY10_biv 1) = 0 := by
        rw [evalBivK5_QY10, evalBivK5_QY10]; linear_combination 1701 * QY_10_u1_zero S_K Q_K T_K x_K y_K
      ext
      · simp only [Dual.add_val, Dual.mul_val]; linear_combination (w0⁻¹ / 5103) * hqy0
      · simp only [Dual.add_eps, Dual.mul_val, Dual.mul_eps,
          cQY_00_biv, cQY_11_biv, evalBivK5_bivAdd, evalBivK5_bivScale]
        push_cast; linear_combination -(w1 / (5103 * w0 ^ 2)) * hqy0)
  have hl1_qX_D : ValDual 0 (hqX 1 - hqX 0)
      ⟨w0⁻¹ * (evalBivK5 cQX_0_biv / 567),
       w0⁻¹ * ((evalBivK5 cQX_1_biv + 28 * S3Q ^ 3 * evalBivK5 cQX_0_biv) / (28 * 567 * S3Q ^ 3))⟩ := by
    have heq : hqX 1 - hqX 0 = (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) U V 0 * aa +
        QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V 1 * ab) / u_of U := by
      dsimp only [hqX, dot_ab]; ring
    rw [heq]
    have hnum : ValDual (-1) _ _ := (((hQX_D 0).mul haa_D).eq_k (k' := -1) (by omega)).add (((hQX_D 1).mul hab_D).eq_k (k' := -1) (by omega))
    refine valDual_eq_fd ((hnum.div_of_ne hu_D h19_ne).eq_k (k' := 0) (by omega)) (by ring) ?_
    exact (dual_div_eq_iff _ _ _ h19_ne).mpr (by
      have hBv1_1701 : ringEval vK5 Bv1_1701_exact_e = 1701 * k5Params.Bv1 := by
        simp only [Bv1_1701_exact_e, ringEval, eS, eQ, eT, vK5, CoverParams.Bv1, CoverParams.inv9,
          CoverParams.inv27, CoverParams.inv243, k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q, k5Params_T]; ring
      ext
      · simp only [Dual.add_val, Dual.mul_val, cQX_0_biv, evalBivK5_bivAdd, evalBivK5_bivScale]; push_cast; ring
      · simp only [Dual.add_eps, Dual.mul_val, Dual.mul_eps,
          cQX_1_biv, cQX_0_biv, cQX_00_biv, cQX_11_biv, evalBivK5_bivAdd, evalBivK5_bivScale,
          evalBivK5_bscE, ringEval, hBv1_1701, rb_sc_28_e, rb_num_28_e, S3Q_e, w0_sc4_e, T59_e, eS, eQ, eT, vK5]
        push_cast; rw [hw1_eq, hw0_eq]; dsimp only [r1, rb_sc, S3Q, T59]
        field_simp [hS3Q, hT, hT59]; ring)
  have hA1_D : ValDual 0 (A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V)
      ⟨(25 / 27 : K5) * T_K * T59 ^ 2,
       -(4 / 27 : K5) * S3Q ^ 3 * w1 + (25 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 2 * w0⟩ := by
    have hre : A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V =
        HahnSeries.C (-(4 / 27 : K5) * S3Q ^ 3) * (U * V) +
        HahnSeries.C ((25 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 2) * V := by
      simp only [A1_of, S3Q, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]; ring
    rw [hre]
    have hm : ValDual 0 (HahnSeries.C (-(4 / 27 : K5) * S3Q ^ 3) * (U * V))
        ⟨(25 / 27 : K5) * T_K * T59 ^ 2, -(4 / 27 : K5) * S3Q ^ 3 * w1⟩ :=
      ((ValDual.of_C _).mul ((hU_D.mul hV_D).eq_k (k' := 0) (by omega))).eq_k (k' := 0) (by omega) |>.eq_d (by
        ext
        · simp only [Dual.mul_val, Dual.C_val]; rw [hw0_eq]; field_simp [hS3Q]; ring
        · simp only [Dual.mul_val, Dual.mul_eps, Dual.C_val, Dual.C_eps]; ring)
    have hs : ValLead 1 (HahnSeries.C ((25 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 2) * V)
        ((25 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 2 * w0) :=
      ((ValLead.of_C _).mul hV_D.toValLead).eq_k (k' := 1) (by omega)
    exact (hm.add_shift1 hs).eq_d (by ext <;> simp)
  have hB1_D : ValDual (-1) (B1_of (HahnSeries.C T_K) U V)
      ⟨(25 / 27 : K5) * T_K * T59 ^ 2, -(4 / 27 : K5) * (T_K - 3) ^ 3 * w0⟩ := by
    have hre : B1_of (HahnSeries.C T_K) U V =
        HahnSeries.C ((25 / 27 : K5) * T_K * T59 ^ 2) * U +
        HahnSeries.C (-(4 / 27 : K5) * (T_K - 3) ^ 3) * (U * V) := by
      simp only [B1_of, T59, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]; ring
    rw [hre]
    have hm : ValDual (-1) (HahnSeries.C ((25 / 27 : K5) * T_K * T59 ^ 2) * U)
        (Dual.C ((25 / 27 : K5) * T_K * T59 ^ 2)) :=
      ((ValDual.of_C _).mul hU_D).eq_k (k' := -1) (by omega) |>.eq_d (by rw [← map_mul, mul_one])
    have hs : ValLead 0 (HahnSeries.C (-(4 / 27 : K5) * (T_K - 3) ^ 3) * (U * V))
        (-(4 / 27 : K5) * (T_K - 3) ^ 3 * w0) :=
      ((ValLead.of_C _).mul ((hU_D.toValLead.mul hV_D.toValLead).eq_k (k' := 0) (by omega))).eq_k (k' := 0) (by omega) |>.eq_c (by simp only [Dual.C_val]; ring)
    exact hm.add_shift1 hs |>.eq_d (by ext <;> simp [Dual.C_val, Dual.C_eps, Dual.pow_eq])
  have hH0_D : ValDual 0 (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K))
      (Dual.C (ringEval vK5 H0_int_e / 7)) := by
    rw [show H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) = HahnSeries.C (H0_of S_K Q_K T_K) by
      simp only [H0_of, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]]
    exact (ValDual.of_C _).eq_d (by congr 1; rw [ringEval_H0_7_inf]; ring)
  have hdA1_0_D : ValDual 0 (dA1_fn 0 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V)
      ⟨-(4 / 9 : K5) * S3Q ^ 2 * w0, -(4 / 9 : K5) * S3Q ^ 2 * w1 + (25 / 27 : K5) * (5 * S_K - 9 * Q_K) * (15 * S_K - 9 * Q_K) * w0⟩ := by
    have hre : dA1_fn 0 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V =
        HahnSeries.C (-(4 / 9 : K5) * S3Q ^ 2) * (U * V) +
        HahnSeries.C ((25 / 27 : K5) * (5 * S_K - 9 * Q_K) * (15 * S_K - 9 * Q_K)) * V := by
      simp only [dA1_fn, S3Q, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]; ring
    rw [hre]
    exact (((ValDual.of_C _).mul ((hU_D.mul hV_D).eq_k (k' := 0) (by omega))).eq_k (k' := 0) (by omega)).add_shift1
      (((ValLead.of_C _).mul hV_D.toValLead).eq_k (k' := 1) (by omega)) |>.eq_d (by ext <;> simp [Dual.C_val, Dual.C_eps, Dual.pow_eq])
  have hdA1_1_D : ValDual 0 (dA1_fn 1 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V)
      ⟨(4 / 3 : K5) * S3Q ^ 2 * w0, (4 / 3 : K5) * S3Q ^ 2 * w1 - (50 / 3 : K5) * S_K * (5 * S_K - 9 * Q_K) * w0⟩ := by
    have hre : dA1_fn 1 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V =
        HahnSeries.C ((4 / 3 : K5) * S3Q ^ 2) * (U * V) +
        HahnSeries.C (-(50 / 3 : K5) * S_K * (5 * S_K - 9 * Q_K)) * V := by
      simp only [dA1_fn, S3Q, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]; ring
    rw [hre]
    exact (((ValDual.of_C _).mul ((hU_D.mul hV_D).eq_k (k' := 0) (by omega))).eq_k (k' := 0) (by omega)).add_shift1
      (((ValLead.of_C _).mul hV_D.toValLead).eq_k (k' := 1) (by omega)) |>.eq_d (by ext <;> simp [Dual.C_val, Dual.C_eps, Dual.pow_eq]; ring)
  have hdH0_D (k : Fin 3) : ValDual 0 (dH0_fn k (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K))
      (Dual.C (ringEval vK5 (dH0_7_inf_e k) / 7)) := by
    rw [show dH0_fn k (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) = HahnSeries.C (dH0_fn k S_K Q_K T_K) by
      fin_cases k <;> simp only [dH0_fn, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]]
    exact (ValDual.of_C _).eq_d (by congr 1; rw [ringEval_dH0_7_inf]; ring)
  have hl1_q1_D : ValDual (-1) (hq1 1 - hq1 0)
      ⟨w0⁻¹ * (evalBivK5 q1_m1_u1_biv / 107163), w0⁻¹ * (evalBivK5 q1_0_u1_biv / (28 * 107163 * S3Q ^ 3))⟩ := by
    have heq : hq1 1 - hq1 0 =
        H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) * A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V * (hqY 1 - hqY 0) +
        H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) * B1_of (HahnSeries.C T_K) U V * (hqX 1 - hqX 0) +
        (((H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) * dA1_fn 0 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V -
           A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V * dH0_fn 0 (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)) * aa +
          (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) * dA1_fn 1 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V -
           A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V * dH0_fn 1 (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)) * ab) / v_of V) *
          EB_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V := by
      dsimp only [hq1, cA1_of]; ring
    rw [heq]
    have ht1 : ValDual (-1) _ _ := ((hH0_D.mul hA1_D).mul hl1_qY_D).eq_k (by omega)
    have ht2 : ValDual (-1) _ _ := ((hH0_D.mul hB1_D).mul hl1_qX_D).eq_k (by omega)
    have hcA1_l1 : ValDual 0 _ _ := ((((hH0_D.mul hdA1_0_D).sub (hA1_D.mul (hdH0_D 0))).mul haa_D).eq_k (by omega)).add
      ((((hH0_D.mul hdA1_1_D).sub (hA1_D.mul (hdH0_D 1))).mul hab_D).eq_k (by omega))
    have ht3 : ValDual (-1) _ _ := ((hcA1_l1.div_of_ne hv_D hneg19_ne).mul hEB_D).eq_k (by omega)
    refine valDual_eq_fd ((ht1.add ht2).add ht3) (by ring) ?_
    ext
    · simp only [Dual.add_val, Dual.mul_val, Dual.sub_val, Dual.C_val, Dual.invOfNe,
        q1_m1_u1_biv, evalBivK5_bscE, evalBivK5_bivAdd, ringEval, T59_e, eT, vK5, dH0_301_21_e, T59]
      field_simp [hw0_ne]; ring
    · have hS3Q_e : ringEval vK5 S3Q_e = S_K - 3 * Q_K := rfl
      have hT59_e : ringEval vK5 T59_e = 5 * T_K - 9 := rfl
      have hA5_e : ringEval vK5 A5_e = 5 * S_K - 9 * Q_K := rfl
      have hrb_num : -(3 / 28 : K5) * (S_K - 3 * Q_K) * (119 * S_K ^ 2 - 560 * S_K * Q_K + 630 * Q_K ^ 2 + 90 * Q_K + 90) =
          (S_K - 3 * Q_K) * ringEval vK5 rb_num_28_e / 28 := by
        simp only [rb_num_28_e, ringEval, eS, eQ, vK5]; ring
      simp only [Dual.add_val, Dual.add_eps, Dual.mul_val, Dual.mul_eps, Dual.sub_val, Dual.sub_eps,
        Dual.C_val, Dual.C_eps, Dual.invOfNe,
        q1_0_u1_biv, evalBivK5_bscE, evalBivK5_bivAdd, evalBivK5_bivSub, ringEval,
        hT59_e, hS3Q_e, hA5_e, w0_sc4_e, rb_sc_28_e, dH0_301_21_e, eS, eQ, eT, vK5]
      rw [hw0_eq]; dsimp only [r1, rb_sc, S3Q, T59]; rw [hrb_num]
      generalize ringEval vK5 rb_num_28_e = vrb
      generalize evalBivK5 (QY10_biv 1) = vQY1; generalize evalBivK5 cQY_00_biv = vQY00; generalize evalBivK5 cQY_11_biv = vQY11
      generalize evalBivK5 cQX_0_biv = vQX0; generalize evalBivK5 cQX_1_biv = vQX1
      generalize evalBivK5 EB10_biv = vEB10; generalize evalBivK5 EB11_biv = vEB11
      generalize ringEval vK5 H0_int_e = vH0; generalize ringEval vK5 (dH0_7_inf_e 0) = vdH0; generalize ringEval vK5 (dH0_7_inf_e 1) = vdH1
      generalize (S_K - 3 * Q_K) = s3q at hS3Q ⊢
      generalize (5 * T_K - 9) = t59 at hT59 ⊢
      field_simp [hS3Q, hT, hT59]; ring
  exact ⟨hl1_qY_D, hl1_qX_D, hl1_q1_D⟩

private lemma br1_inf_fX_lead3_valLead {U V aa ab b0s : LaurentSeries K5} {w0 w1 : K5}
    (hw0_ne : w0 ≠ 0)
    (hU_D : ValDual (-1) U (Dual.C 1)) (hV_D : ValDual 1 V ⟨w0, w1⟩)
    (haa_D : ValDual 0 aa ⟨w0⁻¹, -w1 / w0 ^ 2⟩)
    (hab_D : ValDual 0 ab (⟨1 / 3, (-(3 / 28 : K5) * (S_K - 3 * Q_K) *
      (119 * S_K ^ 2 - 560 * S_K * Q_K + 630 * Q_K ^ 2 + 90 * Q_K + 90)) / (3 * (S_K - 3 * Q_K) ^ 3)⟩ * ⟨w0⁻¹, -w1 / w0 ^ 2⟩))
    (hb0_L : ValLead 0 b0s (-((S_K - 3 * Q_K) * (5 * T_K - 3)) / (3 * T_K * (5 * T_K - 9)))) :
    let fX : LaurentSeries K5 → LaurentSeries K5 := fun z =>
      A_X (aa * z) (ab * z + b0s) (HahnSeries.C S_K - aa * z * HahnSeries.C T_K)
        (HahnSeries.C Q_K - (ab * z + b0s) * HahnSeries.C T_K) U V *
      H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) ^ 2
    ValLead (-2) ((fX 2 - 3 * fX 1 + 3 * fX 0 - fX (-1)) / 6)
      (w0⁻¹ * ((2 / 885735 : K5) * (5 * T_K - 9) * (S_K - 3 * Q_K) ^ 2) * (ringEval vK5 H0_int_e / 7) ^ 2) := by
  intro fX
  set S3Q := S_K - 3 * Q_K; set T59 := 5 * T_K - 9
  have h6_ne : (6 : K5) ≠ 0 := ofNat_ne_zero 6
  have hH0_L : ValLead 0 (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)) (ringEval vK5 H0_int_e / 7) := by
    rw [show H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) = HahnSeries.C (H0_of S_K Q_K T_K) by
      simp only [H0_of, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]]
    exact (ValLead.of_C _).eq_c (by rw [ringEval_H0_7_inf]; ring)
  let leadAX (k : Fin 4) : LaurentSeries K5 :=
    let f := fun z : LaurentSeries K5 => AX_Uk k (aa * z) (ab * z + b0s)
      (HahnSeries.C S_K - aa * z * HahnSeries.C T_K) (HahnSeries.C Q_K - (ab * z + b0s) * HahnSeries.C T_K)
    (f 2 - 3 * f 1 + 3 * f 0 - f (-1)) / 6
  have hX_split : (fX 2 - 3 * fX 1 + 3 * fX 0 - fX (-1)) / 6 =
      (U * V ^ 2 * (U ^ 3 * leadAX 3) + U * V ^ 2 * (U ^ 2 * leadAX 2 + U * leadAX 1 + leadAX 0)) *
      H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) ^ 2 := by
    dsimp only [fX, leadAX]; simp only [A_X_split_UV]; ring
  rw [hX_split]
  have hAXk0 (k : Fin 4) (z0 : K5) : ValLead 0
      (AX_Uk k (aa * HahnSeries.C z0) (ab * HahnSeries.C z0 + b0s)
        (HahnSeries.C S_K - aa * HahnSeries.C z0 * HahnSeries.C T_K)
        (HahnSeries.C Q_K - (ab * HahnSeries.C z0 + b0s) * HahnSeries.C T_K))
      (AX_Uk k (w0⁻¹ * z0) ((w0⁻¹ / 3) * z0 + (-(S3Q * (5 * T_K - 3)) / (3 * T_K * T59)))
        (S_K - w0⁻¹ * z0 * T_K) (Q_K - ((w0⁻¹ / 3) * z0 + (-(S3Q * (5 * T_K - 3)) / (3 * T_K * T59))) * T_K)) := by
    have haL : ValLead 0 (aa * HahnSeries.C z0) (w0⁻¹ * z0) := (haa_D.toValLead.mul (ValLead.of_C z0)).eq_k (by omega)
    have hbL : ValLead 0 (ab * HahnSeries.C z0 + b0s) ((w0⁻¹ / 3) * z0 + (-(S3Q * (5 * T_K - 3)) / (3 * T_K * T59))) :=
      (((hab_D.toValLead.mul (ValLead.of_C z0)).eq_k (by omega)).add hb0_L).eq_c (by simp only [Dual.mul_val]; ring)
    have hξSL : ValLead 0 (HahnSeries.C S_K - aa * HahnSeries.C z0 * HahnSeries.C T_K) (S_K - w0⁻¹ * z0 * T_K) :=
      (ValLead.of_C S_K).sub ((haL.mul (ValLead.of_C T_K)).eq_k (by omega))
    have hξQL : ValLead 0 (HahnSeries.C Q_K - (ab * HahnSeries.C z0 + b0s) * HahnSeries.C T_K)
        (Q_K - ((w0⁻¹ / 3) * z0 + (-(S3Q * (5 * T_K - 3)) / (3 * T_K * T59))) * T_K) :=
      (ValLead.of_C Q_K).sub ((hbL.mul (ValLead.of_C T_K)).eq_k (by omega))
    have hC (r : K5) {f : LaurentSeries K5} {v : K5} (hf : ValLead 0 f v) :
        ValLead 0 (HahnSeries.C r * f) (r * v) := ((ValLead.of_C r).mul hf).eq_k (by omega)
    have hN (n : ℕ) [n.AtLeastTwo] {f : LaurentSeries K5} {v : K5} (hf : ValLead 0 f v) :
        ValLead 0 ((no_index (OfNat.ofNat n) : LaurentSeries K5) * f) ((no_index (OfNat.ofNat n) : K5) * v) :=
      ((ValLead.of_ofNat n).mul hf).eq_k (by omega)
    have hnum (mi : Fin 10) : ValLead 0 (numM_Uk k mi (aa * HahnSeries.C z0) (ab * HahnSeries.C z0 + b0s)
          (HahnSeries.C S_K - aa * HahnSeries.C z0 * HahnSeries.C T_K)
          (HahnSeries.C Q_K - (ab * HahnSeries.C z0 + b0s) * HahnSeries.C T_K))
        (numM_Uk k mi (w0⁻¹ * z0) ((w0⁻¹ / 3) * z0 + (-(S3Q * (5 * T_K - 3)) / (3 * T_K * T59)))
          (S_K - w0⁻¹ * z0 * T_K) (Q_K - ((w0⁻¹ / 3) * z0 + (-(S3Q * (5 * T_K - 3)) / (3 * T_K * T59))) * T_K)) :=
      numM_Uk_valLead k mi haL hbL hξSL hξQL
    have hp (i j : Fin 10) := (hN 5 (hnum i)).sub (hN 9 (hnum j))
    unfold AX_Uk
    simpa only [map_div₀, map_neg, map_ofNat] using
      ((hC (-(8 / 405 : K5)) (hp 3 4)).sub (hC (476 / 7185 : K5) (hp 7 8))).add (hC (6916 / 35925 : K5) (hp 8 9))
  have hL3 : ValLead (-2) (U * V ^ 2 * (U ^ 3 * leadAX 3)) (w0⁻¹ * ((2 / 885735 : K5) * T59 * S3Q ^ 2)) := by
    have hf2 := hAXk0 3 2; have hf1 := hAXk0 3 1; have hf0 := hAXk0 3 0; have hfm1 := hAXk0 3 (-1)
    have hcomb := ((((hf2.sub (((ValLead.of_ofNat 3).mul hf1).eq_k (k' := 0) (by omega))).add
      (((ValLead.of_ofNat 3).mul hf0).eq_k (k' := 0) (by omega))).sub hfm1).div_of_ne
      (ValLead.of_ofNat 6) h6_ne).eq_k (k' := 0) (by omega)
    have hU3 : ValLead (-3) (U ^ 3) 1 := (hU_D.toValLead.pow 3).eq_k (by omega) |>.eq_c (by simp)
    refine valLead_eq_fc (((hU_D.toValLead.mul (hV_D.toValLead.pow 2)).mul (hU3.mul hcomb)).eq_k (k' := -2) (by omega))
      (by dsimp only [leadAX]; simp only [map_ofNat, map_one, map_zero, map_neg]) ?_
    have h3 := AX_U3_lead3_at_third S_K Q_K T_K w0⁻¹ (-(S3Q * (5 * T_K - 3)) / (3 * T_K * T59))
    dsimp only at h3
    have h4 : ((AX_Uk 3 (w0⁻¹ * 2) (w0⁻¹ / 3 * 2 + -(S3Q * (5 * T_K - 3)) / (3 * T_K * T59))
          (S_K - w0⁻¹ * 2 * T_K) (Q_K - (w0⁻¹ / 3 * 2 + -(S3Q * (5 * T_K - 3)) / (3 * T_K * T59)) * T_K) -
        (3 : K5) * AX_Uk 3 (w0⁻¹ * 1) (w0⁻¹ / 3 * 1 + -(S3Q * (5 * T_K - 3)) / (3 * T_K * T59))
          (S_K - w0⁻¹ * 1 * T_K) (Q_K - (w0⁻¹ / 3 * 1 + -(S3Q * (5 * T_K - 3)) / (3 * T_K * T59)) * T_K) +
        (3 : K5) * AX_Uk 3 (w0⁻¹ * 0) (w0⁻¹ / 3 * 0 + -(S3Q * (5 * T_K - 3)) / (3 * T_K * T59))
          (S_K - w0⁻¹ * 0 * T_K) (Q_K - (w0⁻¹ / 3 * 0 + -(S3Q * (5 * T_K - 3)) / (3 * T_K * T59)) * T_K) -
        AX_Uk 3 (w0⁻¹ * -1) (w0⁻¹ / 3 * -1 + -(S3Q * (5 * T_K - 3)) / (3 * T_K * T59))
          (S_K - w0⁻¹ * -1 * T_K) (Q_K - (w0⁻¹ / 3 * -1 + -(S3Q * (5 * T_K - 3)) / (3 * T_K * T59)) * T_K)) / (6 : K5)) =
        w0⁻¹ ^ 3 * ((2 / 885735 : K5) * T59 * S3Q ^ 2) := by
      simpa only [S3Q, T59] using h3
    push_cast; simp only [Dual.C_val, one_mul, h4]; field_simp [hw0_ne]
  have hhiX : HasValGe (-1) (U * V ^ 2 * (U ^ 2 * leadAX 2 + U * leadAX 1 + leadAX 0)) := by
    have h0 (k : Fin 4) : HasValGe 0 (leadAX k) := by
      have hf2 := (hAXk0 k 2).val; have hf1 := (hAXk0 k 1).val; have hf0 := (hAXk0 k 0).val; have hfm1 := (hAXk0 k (-1)).val
      exact hasValGe_eq_f (((((hf2.sub (((HasValGe.of_ofNat 3).mul hf1).mono (k2 := 0) (by omega))).add
        (((HasValGe.of_ofNat 3).mul hf0).mono (k2 := 0) (by omega))).sub hfm1).div_of_lead_ne
        (HasValGe.of_ofNat 6) (by rw [(ValLead.of_ofNat 6).c0]; exact h6_ne)).1.mono (k2 := 0) (by omega))
        (by dsimp only [leadAX]; simp only [map_ofNat, map_one, map_zero, map_neg])
    exact ((hU_D.val.mul (hV_D.val.pow 2)).mul
      (((((hU_D.val.pow 2).mul (h0 2)).mono (k2 := -2) (by omega)).add
        ((hU_D.val.mul (h0 1)).mono (k2 := -2) (by omega))).add ((h0 0).mono (k2 := -2) (by omega)))).mono (by omega)
  exact valLead_eq_fc (((hL3.add_high hhiX).mul (hH0_L.pow 2)).eq_k (k' := -2) (by omega)) rfl
    (by dsimp only [S3Q, T59])

private lemma br1_inf_fUfY_lead3_ge {U V aa ab b0s : LaurentSeries K5} {w0 w1 : K5}
    (hU_D : ValDual (-1) U (Dual.C 1)) (hV_D : ValDual 1 V ⟨w0, w1⟩)
    (haa_val : HasValGe 0 aa) (hab_val : HasValGe 0 ab) (hb0_val : HasValGe 0 b0s) :
    let fU : LaurentSeries K5 → LaurentSeries K5 := fun z =>
      A_0U (aa * z) (ab * z + b0s) (HahnSeries.C S_K - aa * z * HahnSeries.C T_K)
        (HahnSeries.C Q_K - (ab * z + b0s) * HahnSeries.C T_K) U V / U
    let fY : LaurentSeries K5 → LaurentSeries K5 := fun z =>
      A_Y (aa * z) (ab * z + b0s) (HahnSeries.C S_K - aa * z * HahnSeries.C T_K)
        (HahnSeries.C Q_K - (ab * z + b0s) * HahnSeries.C T_K) U V *
      H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) ^ 2
    HasValGe 0 ((fU 2 - 3 * fU 1 + 3 * fU 0 - fU (-1)) / 6) ∧
    HasValGe (-1) ((fY 2 - 3 * fY 1 + 3 * fY 0 - fY (-1)) / 6) := by
  intro fU fY
  have hH0_0 : HasValGe 0 (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)) := by
    rw [show H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) = HahnSeries.C (H0_of S_K Q_K T_K) by
      simp only [H0_of, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]]
    exact HasValGe.of_C _
  have hnum_at (z0 : K5) (mi : Fin 10) :
      HasValGe (-1) (numM mi (aa * HahnSeries.C z0) (ab * HahnSeries.C z0 + b0s)
        (HahnSeries.C S_K - aa * HahnSeries.C z0 * HahnSeries.C T_K)
        (HahnSeries.C Q_K - (ab * HahnSeries.C z0 + b0s) * HahnSeries.C T_K) U V) := by
    rw [numM_split_UV]
    have ha0 : HasValGe 0 (aa * HahnSeries.C z0) := (haa_val.mul (HasValGe.of_C z0)).mono (by omega)
    have hb0' : HasValGe 0 (ab * HahnSeries.C z0 + b0s) :=
      ((hab_val.mul (HasValGe.of_C z0)).mono (by omega)).add hb0_val
    have hξS0 : HasValGe 0 (HahnSeries.C S_K - aa * HahnSeries.C z0 * HahnSeries.C T_K) :=
      (HasValGe.of_C S_K).sub ((ha0.mul (HasValGe.of_C T_K)).mono (by omega))
    have hξQ0 : HasValGe 0 (HahnSeries.C Q_K - (ab * HahnSeries.C z0 + b0s) * HahnSeries.C T_K) :=
      (HasValGe.of_C Q_K).sub ((hb0'.mul (HasValGe.of_C T_K)).mono (by omega))
    have hUk (k : Fin 4) : HasValGe 0 (numM_Uk k mi (aa * HahnSeries.C z0) (ab * HahnSeries.C z0 + b0s)
        (HahnSeries.C S_K - aa * HahnSeries.C z0 * HahnSeries.C T_K)
        (HahnSeries.C Q_K - (ab * HahnSeries.C z0 + b0s) * HahnSeries.C T_K)) :=
      numM_Uk_hasValGe k mi ha0 hb0' hξS0 hξQ0
    exact ((hV_D.val.pow 2).mul (((((hU_D.val.pow 3).mul (hUk 3)).mono (k2 := -3) (by omega)).add
      (((hU_D.val.pow 2).mul (hUk 2)).mono (k2 := -3) (by omega))).add
      ((hU_D.val.mul (hUk 1)).mono (k2 := -3) (by omega)) |>.add ((hUk 0).mono (k2 := -3) (by omega)))).mono (by omega)
  have h6_ne : (6 : K5) ≠ 0 := ofNat_ne_zero 6
  have hlead3_ge {f : LaurentSeries K5 → LaurentSeries K5} {k : ℤ}
      (hf : ∀ z0 : K5, HasValGe k (f (HahnSeries.C z0))) :
      HasValGe k ((f 2 - 3 * f 1 + 3 * f 0 - f (-1)) / 6) := by
    have h2 := hf 2; have h1 := hf 1; have h0 := hf 0; have hm1 := hf (-1)
    exact hasValGe_eq_f (((((h2.sub (((HasValGe.of_ofNat 3).mul h1).mono (k2 := k) (by omega))).add
      (((HasValGe.of_ofNat 3).mul h0).mono (k2 := k) (by omega))).sub hm1).div_of_lead_ne
      (HasValGe.of_ofNat 6) (by rw [(ValLead.of_ofNat 6).c0]; exact h6_ne)).1.mono (k2 := k) (by omega))
      (by simp only [map_ofNat, map_one, map_zero, map_neg])
  constructor
  · apply hlead3_ge; intro z0
    have hm1 := hnum_at z0
    have hsc1 (r : K5) {f : LaurentSeries K5} (hf : HasValGe (-1) f) := ((HasValGe.of_C r).mul hf).mono (k2 := -1) (by omega)
    have hnat1 (n : ℕ) [n.AtLeastTwo] {f : LaurentSeries K5} (hf : HasValGe (-1) f) :
        HasValGe (-1) ((no_index (OfNat.ofNat n) : LaurentSeries K5) * f) := ((HasValGe.of_ofNat n).mul hf).mono (k2 := -1) (by omega)
    have hp1 (i j : Fin 10) := (hnat1 5 (hm1 i)).sub (hnat1 9 (hm1 j))
    have hA0U : HasValGe (-1) (A_0U (aa * HahnSeries.C z0) (ab * HahnSeries.C z0 + b0s)
        (HahnSeries.C S_K - aa * HahnSeries.C z0 * HahnSeries.C T_K)
        (HahnSeries.C Q_K - (ab * HahnSeries.C z0 + b0s) * HahnSeries.C T_K) U V) := by
      unfold A_0U; simpa only [map_div₀, map_neg, map_ofNat] using
        (((hsc1 (-(19708 / 1257375 : K5)) (hp1 0 1)).add (hsc1 (1472 / 1257375 : K5) (hp1 1 2))).sub
          (hsc1 (16 / 729 : K5) (hp1 3 5))).add (hsc1 (188 / 2025 : K5) (hp1 4 6))
    exact hasValGe_eq_f ((hA0U.div_of_lead_ne hU_D.val (by rw [hU_D.c0]; exact one_ne_zero)).1.mono (k2 := 0) (by omega))
      (by simp only [fU])
  · apply hlead3_ge; intro z0
    have hm1 := hnum_at z0
    have hsc1 (r : K5) {f : LaurentSeries K5} (hf : HasValGe (-1) f) := ((HasValGe.of_C r).mul hf).mono (k2 := -1) (by omega)
    have hnat1 (n : ℕ) [n.AtLeastTwo] {f : LaurentSeries K5} (hf : HasValGe (-1) f) :
        HasValGe (-1) ((no_index (OfNat.ofNat n) : LaurentSeries K5) * f) := ((HasValGe.of_ofNat n).mul hf).mono (k2 := -1) (by omega)
    have hp1 (i j : Fin 10) := (hnat1 5 (hm1 i)).sub (hnat1 9 (hm1 j))
    have hAY : HasValGe (-1) (A_Y (aa * HahnSeries.C z0) (ab * HahnSeries.C z0 + b0s)
        (HahnSeries.C S_K - aa * HahnSeries.C z0 * HahnSeries.C T_K)
        (HahnSeries.C Q_K - (ab * HahnSeries.C z0 + b0s) * HahnSeries.C T_K) U V) := by
      unfold A_Y
      refine HasValGe.add (HasValGe.add ?_ ?_) ?_
      · simpa only [map_div₀, map_neg, map_ofNat] using
          hsc1 (-(100 / 243 : K5)) ((((hnat1 25 (hm1 3)).sub (hnat1 45 (hm1 4))).sub (hnat1 45 (hm1 5))).add (hnat1 81 (hm1 6)))
      · refine (hV_D.val.mul (?_ : HasValGe (-1) _)).mono (by omega)
        simpa only [map_div₀, map_neg, map_ofNat] using
          (((hsc1 (-(907876 / 33949125 : K5)) (hp1 0 1)).add (hsc1 (2258324 / 33949125 : K5) (hp1 1 2))).add
            (hsc1 (8 / 243 : K5) (hp1 3 5))).sub (hsc1 (64 / 675 : K5) (hp1 4 6))
      · refine ((hU_D.val.mul hV_D.val).mul (?_ : HasValGe (-1) _)).mono (by omega)
        simpa only [map_div₀, map_neg, map_ofNat] using
          (hsc1 (-(123236 / 24249375 : K5)) ((((hm1 0).add (hsc1 (2790 / 77 : K5) (hm1 6))).add (hnat1 28 (hm1 8))).sub
            (hsc1 (5904 / 77 : K5) (hm1 9)))).add
          (hsc1 (492944 / 33949125 : K5) ((((hm1 1).add (hsc1 (927 / 77 : K5) (hm1 6))).add (hsc1 (49 / 5 : K5) (hm1 8))).sub
            (hsc1 (21159 / 770 : K5) (hm1 9))))
    exact hasValGe_eq_f ((hAY.mul (hH0_0.pow 2)).mono (k2 := -1) (by omega)) (by simp only [fY])

-- Standalone Branch 1 (`W1_inf`) `ValDual (-3)` for `p4 = (interp4 g).1` using `interp4_p4_mul`!
private lemma br1_inf_p4_valDual {W1s U V ca cb c0W : LaurentSeries K5} {w0 w1 : K5}
    (hw0_eq : w0 = -(25 / 4 : K5) * T_K * (5 * T_K - 9) ^ 2 / (S_K - 3 * Q_K) ^ 3)
    (hw1_eq : w1 = w0 * ((243 / 4 : K5) * k5Params.Bv1 / (S_K - 3 * Q_K) ^ 3))
    (hw0_ne : w0 ≠ 0)
    (hW_D : ValDual 0 W1s ⟨w0, w1⟩) (hU_D : ValDual (-1) U (Dual.C 1)) (hV_D : ValDual 1 V ⟨w0, w1⟩)
    (hca_D : ValDual (-2) ca ⟨-(4 / 81 : K5) * (S_K - 3 * Q_K) ^ 2,
      (143 / 81 : K5) * S_K ^ 2 - (184 / 27) * S_K * Q_K + (52 / 9) * Q_K ^ 2⟩)
    (hcb_D : ValDual (-2) cb ⟨(4 / 27 : K5) * (S_K - 3 * Q_K) ^ 2,
      -(92 / 27 : K5) * S_K ^ 2 + (104 / 9) * S_K * Q_K - (22 / 3) * Q_K ^ 2 + (10 / 7) * Q_K + (10 / 7)⟩)
    (hc0W_L : ValLead (-2) c0W (-(25 / 81 : K5) * (5 * T_K - 9) * (5 * T_K - 3))) :
    let g : LaurentSeries K5 → LaurentSeries K5 := fun z =>
      P18_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) (z / W1s) (-(ca * z + c0W) / (W1s * cb)) U V
    let S3Q := S_K - 3 * Q_K; let T59 := 5 * T_K - 9
    let p4_m3 : K5 := w0⁻¹ ^ 3 * ((73 / 7971615 : K5) * T59 * S3Q ^ 2) * (evalBivK5 q1_m1_u1_biv / 107163)
    let p4_m2 : K5 :=
      w0⁻¹ ^ 3 * ((73 / 7971615 : K5) * T59 * S3Q ^ 2) * (evalBivK5 q1_0_u1_biv / (28 * 107163 * S3Q ^ 3)) +
      w0⁻¹ ^ 3 * (M01_q_fn S_K Q_K T_K * T59 * S3Q / (267288250950 * S3Q ^ 3)) * (evalBivK5 q1_m1_u1_biv / 107163) +
      w0⁻¹ ^ 2 * ((2 / 885735 : K5) * T59 * S3Q ^ 2) * (evalBivK5 cQX_0_biv / 567) * (ringEval vK5 H0_int_e / 7) ^ 2
    ValDual (-3) (interp4 g).1 ⟨p4_m3, p4_m2⟩ := by
  intro g S3Q T59 p4_m3 p4_m2
  have hS3Q := S_K_sub_3Q_ne; have hT := T_K_ne_zero; have hT59 := fiveT_sub_9_ne
  have hcb_ne : (4 / 27 : K5) * S3Q ^ 2 ≠ 0 :=
    mul_ne_zero (div_ne_zero (ofNat_ne_zero 4) (ofNat_ne_zero 27)) (pow_ne_zero 2 hS3Q)
  have hW_ne : W1s ≠ 0 := fun h0 => hw0_ne (by have h := hW_D.c0; rw [h0, HahnSeries.coeff_zero] at h; exact h.symm)
  have hcb_s_ne : cb ≠ 0 := fun h0 => hcb_ne (by have h := hcb_D.c0; rw [h0, HahnSeries.coeff_zero] at h; exact h.symm)
  set aa : LaurentSeries K5 := 1 / W1s
  set rca : LaurentSeries K5 := -ca / cb
  set ab : LaurentSeries K5 := rca / W1s
  set b0s : LaurentSeries K5 := -c0W / (W1s * cb)
  have ha_eq (z : LaurentSeries K5) : z / W1s = aa * z := by dsimp only [aa]; ring
  have hb_eq (z : LaurentSeries K5) : -(ca * z + c0W) / (W1s * cb) = ab * z + b0s := by
    dsimp only [ab, rca, b0s]; field_simp [hW_ne, hcb_s_ne]; ring
  set fV : LaurentSeries K5 → LaurentSeries K5 := fun z =>
    A_0V (aa * z) (ab * z + b0s) (HahnSeries.C S_K - aa * z * HahnSeries.C T_K)
      (HahnSeries.C Q_K - (ab * z + b0s) * HahnSeries.C T_K) U V / V
  set fU : LaurentSeries K5 → LaurentSeries K5 := fun z =>
    A_0U (aa * z) (ab * z + b0s) (HahnSeries.C S_K - aa * z * HahnSeries.C T_K)
      (HahnSeries.C Q_K - (ab * z + b0s) * HahnSeries.C T_K) U V / U
  set fX : LaurentSeries K5 → LaurentSeries K5 := fun z =>
    A_X (aa * z) (ab * z + b0s) (HahnSeries.C S_K - aa * z * HahnSeries.C T_K)
      (HahnSeries.C Q_K - (ab * z + b0s) * HahnSeries.C T_K) U V *
    H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) ^ 2
  set fY : LaurentSeries K5 → LaurentSeries K5 := fun z =>
    A_Y (aa * z) (ab * z + b0s) (HahnSeries.C S_K - aa * z * HahnSeries.C T_K)
      (HahnSeries.C Q_K - (ab * z + b0s) * HahnSeries.C T_K) U V *
    H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) ^ 2
  set hqY : LaurentSeries K5 → LaurentSeries K5 := fun z =>
    dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V) (aa * z) (ab * z + b0s) / v_of V
  set hqX : LaurentSeries K5 → LaurentSeries K5 := fun z =>
    dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V) (aa * z) (ab * z + b0s) / u_of U
  set hq1 : LaurentSeries K5 → LaurentSeries K5 := fun z =>
    H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) * A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V * hqY z +
    H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) * B1_of (HahnSeries.C T_K) U V * hqX z +
    (cA1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (aa * z) (ab * z + b0s) U V / v_of V) *
      EB_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V
  have hg_eq : g = fun z => (fV z * hq1 z + fU z * hq1 z) + (fX z * hqX z + fY z * hqY z) := by
    funext z; dsimp only [g, fV, fU, fX, fY, hq1, hqX, hqY]
    rw [P18_of_HahnC_eq, ha_eq z, hb_eq z]; ring
  have hdeg3_m := IsPolyDeg_numM (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) U V aa ab b0s
  have hpair3 (i j : Fin 10) : IsPolyDeg 3 (fun z =>
      5 * numM i (aa * z) (ab * z + b0s) (HahnSeries.C S_K - aa * z * HahnSeries.C T_K)
            (HahnSeries.C Q_K - (ab * z + b0s) * HahnSeries.C T_K) U V -
      9 * numM j (aa * z) (ab * z + b0s) (HahnSeries.C S_K - aa * z * HahnSeries.C T_K)
            (HahnSeries.C Q_K - (ab * z + b0s) * HahnSeries.C T_K) U V) :=
    IsPolyDeg.sub (IsPolyDeg.smul_left 5 (hdeg3_m i)) (IsPolyDeg.smul_left 9 (hdeg3_m j))
  have hdeg3_fV : IsPolyDeg 3 fV :=
    IsPolyDeg.div_const (IsPolyDeg.add (IsPolyDeg.sub (IsPolyDeg.add
      (IsPolyDeg.smul_left _ (hpair3 3 4)) (IsPolyDeg.smul_left _ (hpair3 5 6)))
      (IsPolyDeg.smul_left _ (hpair3 7 8))) (IsPolyDeg.smul_left _ (hpair3 8 9))) V
  have hdeg3_fU : IsPolyDeg 3 fU :=
    IsPolyDeg.div_const (IsPolyDeg.add (IsPolyDeg.sub (IsPolyDeg.add
      (IsPolyDeg.smul_left _ (hpair3 0 1)) (IsPolyDeg.smul_left _ (hpair3 1 2)))
      (IsPolyDeg.smul_left _ (hpair3 3 5))) (IsPolyDeg.smul_left _ (hpair3 4 6))) U
  have hdeg3_fX : IsPolyDeg 3 fX :=
    IsPolyDeg.smul_right (IsPolyDeg.smul_left U (IsPolyDeg.add (IsPolyDeg.sub
      (IsPolyDeg.smul_left _ (hpair3 3 4)) (IsPolyDeg.smul_left _ (hpair3 7 8)))
      (IsPolyDeg.smul_left _ (hpair3 8 9)))) _
  have hdeg3_fY : IsPolyDeg 3 fY := by
    unfold fY A_Y
    refine IsPolyDeg.smul_right (IsPolyDeg.add (IsPolyDeg.add ?_ ?_) ?_) _
    · exact IsPolyDeg.smul_left _
        (IsPolyDeg.add (IsPolyDeg.sub (IsPolyDeg.sub
          (IsPolyDeg.smul_left _ (hdeg3_m 3)) (IsPolyDeg.smul_left _ (hdeg3_m 4)))
          (IsPolyDeg.smul_left _ (hdeg3_m 5))) (IsPolyDeg.smul_left _ (hdeg3_m 6)))
    · exact IsPolyDeg.smul_left V (IsPolyDeg.sub (IsPolyDeg.add (IsPolyDeg.add
        (IsPolyDeg.smul_left _ (hpair3 0 1)) (IsPolyDeg.smul_left _ (hpair3 1 2)))
        (IsPolyDeg.smul_left _ (hpair3 3 5))) (IsPolyDeg.smul_left _ (hpair3 4 6)))
    · exact IsPolyDeg.smul_left (U * V) (IsPolyDeg.add
        (IsPolyDeg.smul_left _ (IsPolyDeg.sub (IsPolyDeg.add (IsPolyDeg.add (hdeg3_m 0)
          (IsPolyDeg.smul_left _ (hdeg3_m 6))) (IsPolyDeg.smul_left _ (hdeg3_m 8)))
          (IsPolyDeg.smul_left _ (hdeg3_m 9))))
        (IsPolyDeg.smul_left _ (IsPolyDeg.sub (IsPolyDeg.add (IsPolyDeg.add (hdeg3_m 1)
          (IsPolyDeg.smul_left _ (hdeg3_m 6))) (IsPolyDeg.smul_left _ (hdeg3_m 8)))
          (IsPolyDeg.smul_left _ (hdeg3_m 9)))))
  have hdot1 (f3 : Fin 3 → LaurentSeries K5) : IsPolyDeg 1 (fun z => dot_ab f3 (aa * z) (ab * z + b0s)) :=
    IsPolyDeg.congr (IsPolyDeg.linear (f3 0 * aa + f3 1 * ab) (f3 1 * b0s + f3 2))
      (fun z => by dsimp only [dot_ab]; ring)
  have hdeg1_hqY : IsPolyDeg 1 hqY := IsPolyDeg.div_const (hdot1 _) (v_of V)
  have hdeg1_hqX : IsPolyDeg 1 hqX := IsPolyDeg.div_const (hdot1 _) (u_of U)
  have hdeg1_hq1 : IsPolyDeg 1 hq1 := by
    have hcA1 : IsPolyDeg 1 (fun z => cA1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (aa * z) (ab * z + b0s) U V) :=
      IsPolyDeg.congr (IsPolyDeg.linear
        ((H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) * dA1_fn 0 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V -
          A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V * dH0_fn 0 (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)) * aa +
         (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) * dA1_fn 1 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V -
          A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V * dH0_fn 1 (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)) * ab)
        ((H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) * dA1_fn 1 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V -
          A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V * dH0_fn 1 (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)) * b0s +
         (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) * dA1_fn 2 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V -
          A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V * dH0_fn 2 (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K))))
        (fun z => by dsimp only [cA1_of]; ring)
    exact IsPolyDeg.add (IsPolyDeg.add (IsPolyDeg.smul_left _ hdeg1_hqY) (IsPolyDeg.smul_left _ hdeg1_hqX))
      (IsPolyDeg.smul_right (IsPolyDeg.div_const hcA1 _) _)
  have hp4_split : (interp4 g).1 =
      ((fV 2 - 3 * fV 1 + 3 * fV 0 - fV (-1)) / 6) * (hq1 1 - hq1 0) +
      ((fU 2 - 3 * fU 1 + 3 * fU 0 - fU (-1)) / 6) * (hq1 1 - hq1 0) +
      ((fX 2 - 3 * fX 1 + 3 * fX 0 - fX (-1)) / 6) * (hqX 1 - hqX 0) +
      ((fY 2 - 3 * fY 1 + 3 * fY 0 - fY (-1)) / 6) * (hqY 1 - hqY 0) := by
    rw [hg_eq, interp4_add_p4, interp4_add_p4, interp4_add_p4,
      interp4_p4_mul hdeg3_fV hdeg1_hq1, interp4_p4_mul hdeg3_fU hdeg1_hq1,
      interp4_p4_mul hdeg3_fX hdeg1_hqX, interp4_p4_mul hdeg3_fY hdeg1_hqY]
    ring
  rw [hp4_split]
  set rb_sc : K5 := -(3 / 28 : K5) * S3Q * (119 * S_K ^ 2 - 560 * S_K * Q_K + 630 * Q_K ^ 2 + 90 * Q_K + 90)
  set r1 : K5 := rb_sc / (3 * S3Q ^ 3)
  have hrca_D : ValDual 0 rca ⟨1 / 3, r1⟩ := by
    refine ((hca_D.neg.div_of_ne hcb_D hcb_ne).eq_k (by omega)).eq_d ?_
    have hr1_cb : r1 * ((4 / 27 : K5) * (S_K - 3 * Q_K) ^ 2) =
        -(1 / 189 : K5) * (119 * S_K ^ 2 - 560 * S_K * Q_K + 630 * Q_K ^ 2 + 90 * Q_K + 90) := by
      dsimp only [r1, rb_sc, S3Q]; field_simp [hS3Q]; ring
    exact (dual_div_eq_iff _ _ _ hcb_ne).mpr (by
      ext
      · simp only [Dual.neg_val, Dual.mul_val]; ring
      · simp only [Dual.neg_eps, Dual.mul_eps]; rw [_root_.mul_comm _ r1, hr1_cb]; ring)
  have haa_D : ValDual 0 aa ⟨w0⁻¹, -w1 / w0 ^ 2⟩ := by
    have hinv := (hW_D.inv_of_ne hw0_ne).eq_k (k' := 0) (by omega)
    simpa only [aa, one_div] using hinv.eq_d (by ext <;> simp [Dual.invOfNe])
  have hab_eq : ab = rca * aa := by dsimp only [ab, aa]; ring
  have hab_D : ValDual 0 ab (⟨1 / 3, r1⟩ * ⟨w0⁻¹, -w1 / w0 ^ 2⟩) := by
    rw [hab_eq]; exact (hrca_D.mul haa_D).eq_k (by omega)
  have hb0_L : ValLead 0 b0s (-(S3Q * (5 * T_K - 3)) / (3 * T_K * T59)) := by
    refine ((hc0W_L.neg.div_of_ne ((hW_D.toValLead.mul hcb_D.toValLead).eq_k (k' := -2) (by omega))
      (mul_ne_zero hw0_ne hcb_ne)).eq_k (by omega)).eq_c ?_
    rw [hw0_eq]; dsimp only [S3Q, T59]; field_simp [hS3Q, hT, hT59]; ring
  have hfV_L3_D := br1_inf_fV_lead3_valDual hw1_eq hw0_ne hab_eq hU_D hV_D hrca_D haa_D hab_D hb0_L
  obtain ⟨hl1_qY_D, hl1_qX_D, hl1_q1_D⟩ := br1_inf_q1_lead1_valDual (b0s := b0s) hw0_eq hw1_eq hw0_ne hU_D hV_D haa_D hab_D
  have hfX_L3_L := br1_inf_fX_lead3_valLead hw0_ne hU_D hV_D haa_D hab_D hb0_L
  obtain ⟨hfU_L3, hfY_L3⟩ := br1_inf_fUfY_lead3_ge hU_D hV_D haa_D.val hab_D.val hb0_L.val
  have hT_V : ValDual (-3) _ _ := (hfV_L3_D.mul hl1_q1_D).eq_k (by omega)
  have hT_U : HasValGe (-1) (((fU 2 - 3 * fU 1 + 3 * fU 0 - fU (-1)) / 6) * (hq1 1 - hq1 0)) :=
    (hfU_L3.mul hl1_q1_D.val).mono (by omega)
  have hT_X : ValLead (-2) _ _ := (hfX_L3_L.mul hl1_qX_D.toValLead).eq_k (by omega)
  have hT_Y : HasValGe (-1) (((fY 2 - 3 * fY 1 + 3 * fY 0 - fY (-1)) / 6) * (hqY 1 - hqY 0)) :=
    (hfY_L3.mul (hl1_qY_D.val.inc hl1_qY_D.c0)).mono (by omega)
  have hre :
      ((fV 2 - 3 * fV 1 + 3 * fV 0 - fV (-1)) / 6) * (hq1 1 - hq1 0) +
      ((fU 2 - 3 * fU 1 + 3 * fU 0 - fU (-1)) / 6) * (hq1 1 - hq1 0) +
      ((fX 2 - 3 * fX 1 + 3 * fX 0 - fX (-1)) / 6) * (hqX 1 - hqX 0) +
      ((fY 2 - 3 * fY 1 + 3 * fY 0 - fY (-1)) / 6) * (hqY 1 - hqY 0) =
      (((fV 2 - 3 * fV 1 + 3 * fV 0 - fV (-1)) / 6) * (hq1 1 - hq1 0) +
       ((fX 2 - 3 * fX 1 + 3 * fX 0 - fX (-1)) / 6) * (hqX 1 - hqX 0)) +
      (((fU 2 - 3 * fU 1 + 3 * fU 0 - fU (-1)) / 6) * (hq1 1 - hq1 0) +
       ((fY 2 - 3 * fY 1 + 3 * fY 0 - fY (-1)) / 6) * (hqY 1 - hqY 0)) := by ring
  rw [hre]
  exact ((hT_V.add_shift1 hT_X).add_high (hT_U.add hT_Y)).eq_d (by
    ext <;> (simp only [Dual.add_val, Dual.add_eps, Dual.mul_val, Dual.mul_eps, p4_m3, p4_m2, S3Q, T59]; ring))

private lemma br1_inf_combine_K5 {w0 : K5}
    (hw0_eq : w0 = -(25 / 4 : K5) * T_K * (5 * T_K - 9) ^ 2 / (S_K - 3 * Q_K) ^ 3) :
    let S3Q := S_K - 3 * Q_K
    let T59 := 5 * T_K - 9
    let q1_1 : K5 := evalBivK5 q1_m1_u1_biv / 107163
    let q1_0 : K5 := evalBivK5 q1_m1_u0_biv / (3 * T_K * T59 * 107163)
    let c3_A : K5 := (73 / 7971615 : K5) * T59 * S3Q ^ 2
    let c2_A : K5 := A32_2_q_fn S_K Q_K T_K * T59 * S3Q / (14849347275 * (3 * T_K * T59))
    let c1_A : K5 := A32_1_q_fn S_K Q_K T_K * T59 * S3Q / (4949782425 * (3 * T_K * T59) ^ 2)
    ({ val := -(279006525 / 64 : K5) * T_K * T59 ^ 2 / (S3Q ^ 8 * L_K),
        eps := (13286025 / 12544 : K5) * T_K * T59 ^ 2 * P44_fn S_K Q_K T_K / (S3Q ^ 11 * L_K ^ 2) } *
      { val := w0⁻¹ ^ 3 * (73 / 7971615 * T59 * S3Q ^ 2) * (evalBivK5 q1_m1_u1_biv / 107163),
        eps :=
          w0⁻¹ ^ 3 * (73 / 7971615 * T59 * S3Q ^ 2) * (evalBivK5 q1_0_u1_biv / (28 * 107163 * S3Q ^ 3)) +
          w0⁻¹ ^ 3 * (M01_q_fn S_K Q_K T_K * T59 * S3Q / (267288250950 * S3Q ^ 3)) * (evalBivK5 q1_m1_u1_biv / 107163) +
          w0⁻¹ ^ 2 * (2 / 885735 * T59 * S3Q ^ 2) * (evalBivK5 cQX_0_biv / 567) * (ringEval vK5 H0_int_e / 7) ^ 2 } +
      { val := 0,
        eps :=
          (531441 / 448 : K5) * T_K * T59 * (35 * S_K * T_K + 133 * S_K - 420 * Q_K + 225 * T_K - 45) / S3Q ^ 8 *
            (w0⁻¹ ^ 2 * (c3_A * q1_0 + c2_A * q1_1)) +
          -(177147 / 400 : K5) * T_K / S3Q ^ 5 * (w0⁻¹ * (c2_A * q1_0 + c1_A * q1_1)) } : Dual K5).eps =
      -toK5_RInf / L_K ^ 2 := by
  intro S3Q T59 q1_1 q1_0 c3_A c2_A c1_A
  have hS3Q : S3Q ≠ 0 := S_K_sub_3Q_ne; have hT : T_K ≠ 0 := T_K_ne_zero
  have hT59 : T59 ≠ 0 := fiveT_sub_9_ne; have hL : L_K ≠ 0 := L_K_ne_zero
  have hw0_eq' : w0 = -(25 / 4 : K5) * T_K * T59 ^ 2 / S3Q ^ 3 := hw0_eq
  have hid := Uinf_biv_identity
  rw [LHS_Uinf_biv, evalBivK5_bivReduceX2, evalBivK5_bivReduceX2, RHS_Uinf_biv, evalBivK5_bscE] at hid
  have h21S : (21 * S_K) ^ 2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero (by exact_mod_cast (by decide : (21 : ℕ) ≠ 0)) S_K_ne_zero)
  have hraw_eq : evalBivK5 LHS_Uinf_raw_biv = -40500 * S3Q * T_K ^ 2 * T59 ^ 3 * evalBivK5 RInf_biv := by
    apply mul_left_cancel₀ h21S
    have h1 : (21 * S_K) ^ 2 * evalBivK5 LHS_Uinf_raw_biv = (21 * S_K) * ((21 * S_K) * evalBivK5 LHS_Uinf_raw_biv) := by ring
    rw [h1, hid]
    simp only [ringEval, S3Q_e, T59_e, eS, eQ, eT, vK5, S3Q, T59, Int.cast_neg, Int.cast_ofNat]; ring
  simp only [LHS_Uinf_raw_biv, evalBivK5_bivAdd, evalBivK5_bscE, ringEval_P44_e, ringEval_M01_q_e,
    ringEval_A32_2_q_e, ringEval_A32_1_q_e, ringEval, L5_e, S3Q_e, w0_sc4_e, T59_e, lin_A3_e,
    eS, eQ, eT, vK5, Int.cast_neg, Int.cast_ofNat] at hraw_eq
  simp only [Dual.add_eps, Dual.mul_eps, toK5_RInf, D_RInf, Int.cast_ofNat, c3_A, c2_A, c1_A, q1_1, q1_0]
  have hw0_inv : w0⁻¹ = -(4 / 25 : K5) * S3Q ^ 3 / (T_K * T59 ^ 2) := by
    rw [hw0_eq']; field_simp [hS3Q, hT, hT59]
  rw [hw0_inv]
  have hL_def : (77 * S_K - 210 * Q_K + 45 : K5) = L_K := rfl
  have hS3Q_def : (S_K - 3 * Q_K : K5) = S3Q := rfl
  have hT59_def : (5 * T_K - 9 : K5) = T59 := rfl
  have hlin_def : (35 * (S_K * T_K) + 133 * S_K - 420 * Q_K + 225 * T_K - 45 : K5) =
      35 * S_K * T_K + 133 * S_K - 420 * Q_K + 225 * T_K - 45 := by ring
  rw [hL_def, hS3Q_def, hT59_def, hlin_def] at hraw_eq
  have hM_ne : ((244535547375 : K5) * 40500) ≠ 0 :=
    mul_ne_zero (ofNat_ne_zero 244535547375) (ofNat_ne_zero 40500)
  have hK_ne : ((244535547375 : K5) * 40500) * S3Q * T_K ^ 2 * T59 ^ 3 * L_K ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hM_ne hS3Q) (pow_ne_zero 2 hT))
      (pow_ne_zero 3 hT59)) (pow_ne_zero 2 hL)
  apply mul_left_cancel₀ hK_ne
  have hs1 : ((244535547375 : K5) * 40500) *
      (-(279006525 / 64 : K5)) * (-(4 / 25 : K5)) ^ 3 * (73 / 7971615 : K5) / (28 * 107163 : K5) = 539715645 := by
    have hq : (244535547375 : ℚ) * 40500 * (-(279006525 / 64)) * (-(4 / 25)) ^ 3 * (73 / 7971615) / (28 * 107163) = 539715645 := by norm_num
    have hc := congrArg (Rat.castHom K5) hq; simpa only [map_mul, map_div₀, map_neg, map_pow, map_ofNat] using hc
  have hs2 : ((244535547375 : K5) * 40500) *
      (-(279006525 / 64 : K5)) * (-(4 / 25 : K5)) ^ 3 / (267288250950 * 107163 : K5) = 6174 := by
    have hq : (244535547375 : ℚ) * 40500 * (-(279006525 / 64)) * (-(4 / 25)) ^ 3 / (267288250950 * 107163) = 6174 := by norm_num
    have hc := congrArg (Rat.castHom K5) hq; simpa only [map_mul, map_div₀, map_neg, map_pow, map_ofNat] using hc
  have hs3 : ((244535547375 : K5) * 40500) *
      (-(279006525 / 64 : K5)) * (-(4 / 25 : K5)) ^ 2 * (2 / 885735 : K5) / (567 * 49 : K5) = 3593175390 * (-25) := by
    have hq : (244535547375 : ℚ) * 40500 * (-(279006525 / 64)) * (-(4 / 25)) ^ 2 * (2 / 885735) / (567 * 49) = 3593175390 * (-25) := by norm_num
    have hc := congrArg (Rat.castHom K5) hq; simpa only [map_mul, map_div₀, map_neg, map_pow, map_ofNat] using hc
  have hs4 : ((244535547375 : K5) * 40500) *
      (13286025 / 12544 : K5) * (-(4 / 25 : K5)) ^ 3 * (73 / 7971615 : K5) / 107163 = -3671535 := by
    have hq : (244535547375 : ℚ) * 40500 * (13286025 / 12544) * (-(4 / 25)) ^ 3 * (73 / 7971615) / 107163 = -3671535 := by norm_num
    have hc := congrArg (Rat.castHom K5) hq; simpa only [map_mul, map_div₀, map_neg, map_pow, map_ofNat] using hc
  have hs5 : ((244535547375 : K5) * 40500) *
      (531441 / 448 : K5) * (-(4 / 25 : K5)) ^ 2 * (73 / 7971615 : K5) / (3 * 107163 : K5) = 8566915 := by
    have hq : (244535547375 : ℚ) * 40500 * (531441 / 448) * (-(4 / 25)) ^ 2 * (73 / 7971615) / (3 * 107163) = 8566915 := by norm_num
    have hc := congrArg (Rat.castHom K5) hq; simpa only [map_mul, map_div₀, map_neg, map_pow, map_ofNat] using hc
  have hs6 : ((244535547375 : K5) * 40500) *
      (531441 / 448 : K5) * (-(4 / 25 : K5)) ^ 2 / (14849347275 * 3 * 107163 : K5) = 63 := by
    have hq : (244535547375 : ℚ) * 40500 * (531441 / 448) * (-(4 / 25)) ^ 2 / (14849347275 * 3 * 107163) = 63 := by norm_num
    have hc := congrArg (Rat.castHom K5) hq; simpa only [map_mul, map_div₀, map_neg, map_pow, map_ofNat] using hc
  have hs7 : ((244535547375 : K5) * 40500) *
      (-(177147 / 400 : K5)) * (-(4 / 25 : K5)) / (14849347275 * 3 * 3 * 107163 : K5) = 49 := by
    have hq : (244535547375 : ℚ) * 40500 * (-(177147 / 400)) * (-(4 / 25)) / (14849347275 * 3 * 3 * 107163) = 49 := by norm_num
    have hc := congrArg (Rat.castHom K5) hq; simpa only [map_mul, map_div₀, map_neg, map_pow, map_ofNat] using hc
  have hs8 : ((244535547375 : K5) * 40500) *
      (-(177147 / 400 : K5)) * (-(4 / 25 : K5)) / (4949782425 * 9 * 107163 : K5) = 147 := by
    have hq : (244535547375 : ℚ) * 40500 * (-(177147 / 400)) * (-(4 / 25)) / (4949782425 * 9 * 107163) = 147 := by norm_num
    have hc := congrArg (Rat.castHom K5) hq; simpa only [map_mul, map_div₀, map_neg, map_pow, map_ofNat] using hc
  have hrhs : ((244535547375 : K5) * 40500) / (244535547375 : K5) = 40500 := by
    have hq : ((244535547375 : ℚ) * 40500) / 244535547375 = 40500 := by norm_num
    have hc := congrArg (Rat.castHom K5) hq; simpa only [map_mul, map_div₀, map_ofNat] using hc
  set M_c : K5 := ((244535547375 : K5) * 40500)
  have h28 : (28 : K5) ≠ 0 := ofNat_ne_zero 28
  have h107 : (107163 : K5) ≠ 0 := ofNat_ne_zero 107163
  have h267 : (267288250950 : K5) ≠ 0 := ofNat_ne_zero 267288250950
  have h567 : (567 : K5) ≠ 0 := ofNat_ne_zero 567
  have h7 : (7 : K5) ≠ 0 := ofNat_ne_zero 7
  have h3 : (3 : K5) ≠ 0 := ofNat_ne_zero 3
  have h148 : (14849347275 : K5) ≠ 0 := ofNat_ne_zero 14849347275
  have h494 : (4949782425 : K5) ≠ 0 := ofNat_ne_zero 4949782425
  have h244 : (244535547375 : K5) ≠ 0 := ofNat_ne_zero 244535547375
  have h49 : (49 : K5) = 7 ^ 2 := by norm_num
  have h9 : (9 : K5) = 3 ^ 2 := by norm_num
  rw [h49] at hs3; rw [h9] at hs8
  set cA4v : K5 := -(279006525 / 64 : K5)
  set cA4e : K5 := (13286025 / 12544 : K5)
  set cA3 : K5 := (531441 / 448 : K5)
  set cA2 : K5 := -(177147 / 400 : K5)
  set cwi : K5 := -(4 / 25 : K5)
  set c73 : K5 := (73 / 7971615 : K5)
  set c2_88 : K5 := (2 / 885735 : K5)
  set eP44 := P44_fn S_K Q_K T_K
  set eM01 := M01_q_fn S_K Q_K T_K
  set eA32_2 := A32_2_q_fn S_K Q_K T_K
  set eA32_1 := A32_1_q_fn S_K Q_K T_K
  set eLin := 35 * S_K * T_K + 133 * S_K - 420 * Q_K + 225 * T_K - 45
  set eQ1_0 := evalBivK5 q1_0_u1_biv
  set eQ1_1 := evalBivK5 q1_m1_u1_biv
  set eQ1_u0 := evalBivK5 q1_m1_u0_biv
  set eQX0 := evalBivK5 cQX_0_biv
  set eH0 := ringEval vK5 H0_int_e
  set eRInf := evalBivK5 RInf_biv
  clear_value eP44 eM01 eA32_2 eA32_1 eLin eQ1_0 eQ1_1 eQ1_u0 eQX0 eH0 eRInf
  change M_c * S3Q * T_K ^ 2 * T59 ^ 3 * L_K ^ 2 *
      ((cA4v * T_K * T59 ^ 2 / (S3Q ^ 8 * L_K) *
          ((cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) ^ 3 * (c73 * T59 * S3Q ^ 2) * (eQ1_0 / (28 * 107163 * S3Q ^ 3)) +
           (cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) ^ 3 * (eM01 * T59 * S3Q / (267288250950 * S3Q ^ 3)) * (eQ1_1 / 107163) +
           (cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) ^ 2 * (c2_88 * T59 * S3Q ^ 2) * (eQX0 / 567) * (eH0 / 7) ^ 2) +
        cA4e * T_K * T59 ^ 2 * eP44 / (S3Q ^ 11 * L_K ^ 2) *
          ((cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) ^ 3 * (c73 * T59 * S3Q ^ 2) * (eQ1_1 / 107163))) +
       (cA3 * T_K * T59 * eLin / S3Q ^ 8 *
          ((cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) ^ 2 *
            (c73 * T59 * S3Q ^ 2 * (eQ1_u0 / (3 * T_K * T59 * 107163)) +
             eA32_2 * T59 * S3Q / (14849347275 * (3 * T_K * T59)) * (eQ1_1 / 107163))) +
        cA2 * T_K / S3Q ^ 5 *
          ((cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) *
            (eA32_2 * T59 * S3Q / (14849347275 * (3 * T_K * T59)) * (eQ1_u0 / (3 * T_K * T59 * 107163)) +
             eA32_1 * T59 * S3Q / (4949782425 * (3 * T_K * T59) ^ 2) * (eQ1_1 / 107163))))) =
      M_c * S3Q * T_K ^ 2 * T59 ^ 3 * L_K ^ 2 * (-(eRInf / 244535547375) / L_K ^ 2)
  have ht1 : M_c * S3Q * T_K ^ 2 * T59 ^ 3 * L_K ^ 2 *
      (cA4v * T_K * T59 ^ 2 / (S3Q ^ 8 * L_K) *
        ((cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) ^ 3 * (c73 * T59 * S3Q ^ 2) * (eQ1_0 / (28 * 107163 * S3Q ^ 3)))) =
      539715645 * L_K * S3Q * eQ1_0 := by
    rw [← hs1]; generalize M_c = vM; generalize cA4v = vA; generalize cwi = vw; generalize c73 = v7
    generalize (28 : K5) = d28 at h28 ⊢; generalize (107163 : K5) = d107 at h107 ⊢
    field_simp [hS3Q, hT, hT59, hL, h28, h107]
  have ht2 : M_c * S3Q * T_K ^ 2 * T59 ^ 3 * L_K ^ 2 *
      (cA4v * T_K * T59 ^ 2 / (S3Q ^ 8 * L_K) *
        ((cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) ^ 3 * (eM01 * T59 * S3Q / (267288250950 * S3Q ^ 3)) * (eQ1_1 / 107163))) =
      6174 * L_K * eM01 * eQ1_1 := by
    rw [← hs2]; generalize M_c = vM; generalize cA4v = vA; generalize cwi = vw
    generalize (267288250950 : K5) = d267 at h267 ⊢; generalize (107163 : K5) = d107 at h107 ⊢
    field_simp [hS3Q, hT, hT59, hL, h267, h107]
  have ht3 : M_c * S3Q * T_K ^ 2 * T59 ^ 3 * L_K ^ 2 *
      (cA4v * T_K * T59 ^ 2 / (S3Q ^ 8 * L_K) *
        ((cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) ^ 2 * (c2_88 * T59 * S3Q ^ 2) * (eQX0 / 567) * (eH0 / 7) ^ 2)) =
      3593175390 * L_K * (-25 * T_K * T59 ^ 2) * S3Q * eH0 ^ 2 * eQX0 := by
    have h3' : 3593175390 * L_K * (-25 * T_K * T59 ^ 2) * S3Q * eH0 ^ 2 * eQX0 =
        (3593175390 * (-25)) * L_K * T_K * T59 ^ 2 * S3Q * eH0 ^ 2 * eQX0 := by ring
    rw [h3', ← hs3]; generalize M_c = vM; generalize cA4v = vA; generalize cwi = vw; generalize c2_88 = v2
    generalize (567 : K5) = d567 at h567 ⊢; generalize (7 : K5) = d7 at h7 ⊢
    field_simp [hS3Q, hT, hT59, hL, h567, h7]
  have ht4 : M_c * S3Q * T_K ^ 2 * T59 ^ 3 * L_K ^ 2 *
      (cA4e * T_K * T59 ^ 2 * eP44 / (S3Q ^ 11 * L_K ^ 2) *
        ((cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) ^ 3 * (c73 * T59 * S3Q ^ 2) * (eQ1_1 / 107163))) =
      (-3671535) * eP44 * S3Q * eQ1_1 := by
    rw [← hs4]; generalize M_c = vM; generalize cA4e = vA; generalize cwi = vw; generalize c73 = v7
    generalize (107163 : K5) = d107 at h107 ⊢
    field_simp [hS3Q, hT, hT59, hL, h107]
  have ht5 : M_c * S3Q * T_K ^ 2 * T59 ^ 3 * L_K ^ 2 *
      (cA3 * T_K * T59 * eLin / S3Q ^ 8 *
        ((cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) ^ 2 * (c73 * T59 * S3Q ^ 2 * (eQ1_u0 / (3 * T_K * T59 * 107163))))) =
      8566915 * L_K ^ 2 * eLin * S3Q * eQ1_u0 := by
    rw [← hs5]; generalize M_c = vM; generalize cA3 = vA; generalize cwi = vw; generalize c73 = v7
    generalize (3 : K5) = d3 at h3 ⊢; generalize (107163 : K5) = d107 at h107 ⊢
    field_simp [hS3Q, hT, hT59, hL, h3, h107]
  have ht6 : M_c * S3Q * T_K ^ 2 * T59 ^ 3 * L_K ^ 2 *
      (cA3 * T_K * T59 * eLin / S3Q ^ 8 *
        ((cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) ^ 2 * (eA32_2 * T59 * S3Q / (14849347275 * (3 * T_K * T59)) * (eQ1_1 / 107163)))) =
      63 * L_K ^ 2 * eLin * eA32_2 * eQ1_1 := by
    rw [← hs6]; generalize M_c = vM; generalize cA3 = vA; generalize cwi = vw
    generalize (14849347275 : K5) = d148 at h148 ⊢; generalize (3 : K5) = d3 at h3 ⊢
    generalize (107163 : K5) = d107 at h107 ⊢
    field_simp [hS3Q, hT, hT59, hL, h148, h3, h107]
  have ht7 : M_c * S3Q * T_K ^ 2 * T59 ^ 3 * L_K ^ 2 *
      (cA2 * T_K / S3Q ^ 5 *
        ((cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) *
          (eA32_2 * T59 * S3Q / (14849347275 * (3 * T_K * T59)) * (eQ1_u0 / (3 * T_K * T59 * 107163))))) =
      49 * L_K ^ 2 * eA32_2 * eQ1_u0 := by
    rw [← hs7]; generalize M_c = vM; generalize cA2 = vA; generalize cwi = vw
    generalize (14849347275 : K5) = d148 at h148 ⊢; generalize (3 : K5) = d3 at h3 ⊢
    generalize (107163 : K5) = d107 at h107 ⊢
    field_simp [hS3Q, hT, hT59, hL, h148, h3, h107]
  have ht8 : M_c * S3Q * T_K ^ 2 * T59 ^ 3 * L_K ^ 2 *
      (cA2 * T_K / S3Q ^ 5 *
        ((cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) *
          (eA32_1 * T59 * S3Q / (4949782425 * (3 * T_K * T59) ^ 2) * (eQ1_1 / 107163)))) =
      147 * L_K ^ 2 * eA32_1 * eQ1_1 := by
    rw [← hs8]; generalize M_c = vM; generalize cA2 = vA; generalize cwi = vw
    generalize (4949782425 : K5) = d494 at h494 ⊢; generalize (3 : K5) = d3 at h3 ⊢
    generalize (107163 : K5) = d107 at h107 ⊢
    field_simp [hS3Q, hT, hT59, hL, h494, h3, h107]
  have htr : M_c * S3Q * T_K ^ 2 * T59 ^ 3 * L_K ^ 2 * (-(eRInf / 244535547375) / L_K ^ 2) =
      -40500 * S3Q * T_K ^ 2 * T59 ^ 3 * eRInf := by
    have hr' : -40500 * S3Q * T_K ^ 2 * T59 ^ 3 * eRInf = -(40500 * S3Q * T_K ^ 2 * T59 ^ 3 * eRInf) := by ring
    rw [hr', ← hrhs]; generalize M_c = vM; generalize (244535547375 : K5) = d244 at h244 ⊢
    field_simp [hL, h244]
  rw [htr]
  have hexp : M_c * S3Q * T_K ^ 2 * T59 ^ 3 * L_K ^ 2 *
      ((cA4v * T_K * T59 ^ 2 / (S3Q ^ 8 * L_K) *
          ((cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) ^ 3 * (c73 * T59 * S3Q ^ 2) * (eQ1_0 / (28 * 107163 * S3Q ^ 3)) +
           (cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) ^ 3 * (eM01 * T59 * S3Q / (267288250950 * S3Q ^ 3)) * (eQ1_1 / 107163) +
           (cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) ^ 2 * (c2_88 * T59 * S3Q ^ 2) * (eQX0 / 567) * (eH0 / 7) ^ 2) +
        cA4e * T_K * T59 ^ 2 * eP44 / (S3Q ^ 11 * L_K ^ 2) *
          ((cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) ^ 3 * (c73 * T59 * S3Q ^ 2) * (eQ1_1 / 107163))) +
       (cA3 * T_K * T59 * eLin / S3Q ^ 8 *
          ((cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) ^ 2 *
            (c73 * T59 * S3Q ^ 2 * (eQ1_u0 / (3 * T_K * T59 * 107163)) +
             eA32_2 * T59 * S3Q / (14849347275 * (3 * T_K * T59)) * (eQ1_1 / 107163))) +
        cA2 * T_K / S3Q ^ 5 *
          ((cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) *
            (eA32_2 * T59 * S3Q / (14849347275 * (3 * T_K * T59)) * (eQ1_u0 / (3 * T_K * T59 * 107163)) +
             eA32_1 * T59 * S3Q / (4949782425 * (3 * T_K * T59) ^ 2) * (eQ1_1 / 107163))))) =
      ((539715645 * L_K * S3Q * eQ1_0 + 6174 * L_K * eM01 * eQ1_1) +
       (3593175390 * L_K * (-25 * T_K * T59 ^ 2) * S3Q * eH0 ^ 2 * eQX0 + (-3671535) * eP44 * S3Q * eQ1_1)) +
      ((8566915 * L_K ^ 2 * eLin * S3Q * eQ1_u0 + 63 * L_K ^ 2 * eLin * eA32_2 * eQ1_1) +
       (49 * L_K ^ 2 * eA32_2 * eQ1_u0 + 147 * L_K ^ 2 * eA32_1 * eQ1_1)) := by
    rw [← ht1, ← ht2, ← ht3, ← ht4, ← ht5, ← ht6, ← ht7, ← ht8]
    generalize M_c = vM; generalize cA4v = vA4v; generalize cA4e = vA4e; generalize cA3 = vA3; generalize cA2 = vA2
    generalize cwi = vw; generalize c73 = v73; generalize c2_88 = v288
    generalize eP44 = vP44; generalize eM01 = vM01; generalize eA32_2 = vA32_2; generalize eA32_1 = vA32_1
    generalize eLin = vLin; generalize eQ1_0 = vQ1_0; generalize eQ1_1 = vQ1_1; generalize eQ1_u0 = vQ1_u0
    generalize eQX0 = vQX0; generalize eH0 = vH0; generalize S3Q = vS3Q; generalize T59 = vT59
    generalize (28 : K5) = d28; generalize (107163 : K5) = d107; generalize (267288250950 : K5) = d267
    generalize (567 : K5) = d567; generalize (7 : K5) = d7; generalize (3 : K5) = d3
    generalize (14849347275 : K5) = d148; generalize (4949782425 : K5) = d494
    ring
  rw [hexp]
  simpa only [Int.cast_neg, Int.cast_ofNat] using hraw_eq

lemma br1_inf_eta_AC_coeff_one : (br1_inf eta_AC).coeff 1 = -toK5_RInf / L_K ^ 2 := by
  have hbr := branchHom_eta_AC ψinf ψinf_C W1_inf W1_inf_eq_ψinf
  simp only [ψinf_X] at hbr
  have hfP : ψinf.comp toRat = evalInvT := RingHom.ext ψinf_toRat
  simp only [hfP] at hbr
  change br1_inf eta_AC = _ at hbr
  rw [hbr]
  set U := HahnSeries.single (-1 : ℤ) (1 : K5)
  set V := W1_inf / U
  set ca := evalInvT k5Params.ca_h
  set cb := evalInvT k5Params.cb_h
  set c0W := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.c0W)
  set d2_2 := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d2_2)
  set d2_1 := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d2_1)
  set d2_0 := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d2_0)
  set d1 := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d1_z)
  set d0 := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d0_z)
  set res := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.res_z)
  set g : LaurentSeries K5 → LaurentSeries K5 := fun z =>
    P18_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) (z / W1_inf) (-(ca * z + c0W) / (W1_inf * cb)) U V
  set p := interp4 g
  set P1 := remDeg4_P1 d2_2 d2_1 d2_0 p.1 p.2.1 p.2.2.1 p.2.2.2.1
  set P0 := remDeg4_P0 d2_2 d2_1 d2_0 p.1 p.2.1 p.2.2.1 p.2.2.2.2
  set pref := -(U ^ 3 * W1_inf * cb ^ 4) /
    (81 * HahnSeries.C k5Params.Av0 * (2 * W1_inf + evalInvT k5Params.bW) * evalInvT k5Params.Q5_z ^ 3 * res)
  set A4 := pref * ((-d2_1 ^ 3 + 2 * d2_2 * d2_1 * d2_0) * d0 - (-d2_1 ^ 2 * d2_0 + d2_2 * d2_0 ^ 2) * d1)
  set A3 := pref * ((d2_2 * (d2_1 ^ 2 - d2_2 * d2_0)) * d0 - (d2_2 * d2_1 * d2_0) * d1)
  set A2 := pref * ((-d2_2 ^ 2 * d2_1) * d0 - (-d2_2 ^ 2 * d2_0) * d1)
  set A1 := pref * (d2_2 ^ 3 * d0)
  set A0 := pref * (-d2_2 ^ 3 * d1)
  have hsplit : -(P1 * d0 - P0 * d1) * U ^ 3 * W1_inf * cb ^ 4 /
      (81 * HahnSeries.C k5Params.Av0 * (2 * W1_inf + evalInvT k5Params.bW) * evalInvT k5Params.Q5_z ^ 3 * res) =
      A4 * p.1 + A3 * p.2.1 + A2 * p.2.2.1 + A1 * p.2.2.2.1 + A0 * p.2.2.2.2 := by
    have hP := P1_d0_sub_P0_d1_split d2_2 d2_1 d2_0 d1 d0 p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2
    dsimp only [A4, A3, A2, A1, A0, pref, P1, P0]
    rw [hP]; ring
  rw [hsplit]
  obtain ⟨hA4_D, hA3_L, hA2_L, hA1_5, hA0_5, _, _⟩ := W1_inf_weights
  set S3Q := S_K - 3 * Q_K; set T59 := 5 * T_K - 9
  have hS3Q' := S_K_sub_3Q_ne
  have hS3Q : S3Q ≠ 0 := S_K_sub_3Q_ne; have hT := T_K_ne_zero; have hT59 : T59 ≠ 0 := fiveT_sub_9_ne; have hL : L_K ≠ 0 := L_K_ne_zero
  set w0 : K5 := -(k5Params.Cv0 / k5Params.Bv2)
  set w1 : K5 := k5Params.Cv0 * k5Params.Bv1 / k5Params.Bv2 ^ 2
  have hw0_eq : w0 = -(25 / 4 : K5) * T_K * T59 ^ 2 / S3Q ^ 3 := by
    dsimp only [w0]; simp only [CoverParams.Cv0, CoverParams.Bv2, CoverParams.inv243, k5Params_inv3,
      k5Params_S, k5Params_Q, k5Params_T, S3Q, T59]; field_simp [hS3Q']
  have hw1_eq : w1 = w0 * ((243 / 4 : K5) * k5Params.Bv1 / S3Q ^ 3) := by
    dsimp only [w1, w0]; simp only [CoverParams.Bv2, CoverParams.inv243, k5Params_inv3,
      k5Params_S, k5Params_Q, S3Q]; field_simp [hS3Q']; ring
  have hw0_ne : w0 ≠ 0 := neg_ne_zero.mpr (div_ne_zero k5Params_Cv0_ne k5Params_Bv2_ne)
  have hW_D : ValDual 0 W1_inf ⟨w0, w1⟩ := W1_inf_valDual
  have hU_D : ValDual (-1) U (Dual.C 1) := ValDual.of_single (-1) 1
  have hV_D : ValDual 1 V ⟨w0, w1⟩ := (hW_D.div_of_ne hU_D one_ne_zero).eq_k (by omega) |>.eq_d (by
    ext <;> simp only [Dual.mul_val, Dual.mul_eps, Dual.invOfNe, Dual.C_val, Dual.C_eps] <;> ring)
  have hca_D : ValDual (-2) ca ⟨-(4 / 81 : K5) * S3Q ^ 2,
      (143 / 81 : K5) * S_K ^ 2 - (184 / 27) * S_K * Q_K + (52 / 9) * Q_K ^ 2⟩ :=
    (ValDual.of_evalInvT _ deg2_ca (by omega)).eq_d (by
      ext <;> (simp only [CoverParams.ca_h, coeff_quadU, CoverParams.inv9, CoverParams.inv27,
        CoverParams.inv81, k5Params_inv3, k5Params_S, k5Params_Q, S3Q]; ring))
  have hcb_D : ValDual (-2) cb ⟨(4 / 27 : K5) * S3Q ^ 2,
      -(92 / 27 : K5) * S_K ^ 2 + (104 / 9) * S_K * Q_K - (22 / 3) * Q_K ^ 2 + (10 / 7) * Q_K + (10 / 7)⟩ :=
    (ValDual.of_evalInvT _ deg2_cb (by omega)).eq_d (by
      ext <;> (simp only [CoverParams.cb_h, coeff_quadU, CoverParams.inv9, CoverParams.inv27,
        k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q, S3Q]; ring))
  have hc0W_L : ValLead (-2) c0W (-(25 / 81 : K5) * T59 * (5 * T_K - 3)) :=
    (evalInvT_toUW_valLead_W1 _ _ _).eq_c (by
      simp only [CoverParams.c0_V0, CoverParams.inv81, k5Params_inv3, k5Params_T, T59]; ring)
  -- `ValLead (-3)` for `g (C z)` -> `p3[-3], p2[-3]` and `HasValGe (-3)` for `p1, p0`!
  set q1_1 : K5 := evalBivK5 q1_m1_u1_biv / 107163
  set q1_0 : K5 := evalBivK5 q1_m1_u0_biv / (3 * T_K * T59 * 107163)
  set g0 : K5 → K5 := fun z =>
    (w0 * A0V_Uk 3 (z / w0) (z / w0 / 3 + -S3Q * (5 * T_K - 3) / (3 * T_K * T59))
      (S_K - z / w0 * T_K) (Q_K - (z / w0 / 3 + -S3Q * (5 * T_K - 3) / (3 * T_K * T59)) * T_K)) *
    (q1_1 * (z / w0) + q1_0)
  have hg_L := br1_inf_g_valLead hw0_eq hw0_ne hW_D.toValLead hU_D.toValLead hV_D.toValLead
    hca_D.toValLead hcb_D.toValLead hc0W_L
  obtain ⟨_, hp3_L, hp2_L, hp1_L, hp0_L⟩ := ValLead.interp4_of (g := g) (g0 := g0) hg_L
  -- `ValDual (-3)` for `p4`:
  have hp4_D := br1_inf_p4_valDual hw0_eq hw1_eq hw0_ne hW_D hU_D hV_D hca_D hcb_D hc0W_L
  -- Compute `(interp4 g0).2.1` (`p3[-3]`) and `(interp4 g0).2.2.1` (`p2[-3]`) via `A0V_U3_poly`!
  set c3_A : K5 := (73 / 7971615 : K5) * T59 * S3Q ^ 2
  set c2_A : K5 := A32_2_q_fn S_K Q_K T_K * T59 * S3Q / (14849347275 * (3 * T_K * T59))
  set c1_A : K5 := A32_1_q_fn S_K Q_K T_K * T59 * S3Q / (4949782425 * (3 * T_K * T59) ^ 2)
  have hp32_eq :
      (interp4 g0).2.1 = w0⁻¹ ^ 2 * (c3_A * q1_0 + c2_A * q1_1) ∧
      (interp4 g0).2.2.1 = w0⁻¹ * (c2_A * q1_0 + c1_A * q1_1) := by
    have hpoly (z : K5) :
        A0V_Uk 3 (z / w0) (z / w0 / 3 + -S3Q * (5 * T_K - 3) / (3 * T_K * T59))
          (S_K - z / w0 * T_K) (Q_K - (z / w0 / 3 + -S3Q * (5 * T_K - 3) / (3 * T_K * T59)) * T_K) =
        c3_A * (z / w0) ^ 3 + c2_A * (z / w0) ^ 2 + c1_A * (z / w0) +
        A0V_Uk 3 0 (-S3Q * (5 * T_K - 3) / (3 * T_K * T59)) S_K (Q_K - (-S3Q * (5 * T_K - 3) / (3 * T_K * T59)) * T_K) := by
      simpa only [c3_A, c2_A, c1_A, S3Q, T59] using A0V_U3_poly S_K Q_K T_K (z / w0) hT hT59
    dsimp only [g0]; unfold interp4
    simp only [hpoly]
    constructor <;> (field_simp [hw0_ne]; ring)
  -- Read `coeff 1` of `A4 * p4 + A3 * p3 + A2 * p2 + A1 * p1 + A0 * p0`!
  have hT4 : ValDual 0 (A4 * p.1) _ := (hA4_D.mul hp4_D).eq_k (by omega)
  have hT3 : ValLead 1 (A3 * p.2.1) _ := (hA3_L.mul (hp3_L.eq_c hp32_eq.1)).eq_k (by omega)
  have hT2 : ValLead 1 (A2 * p.2.2.1) _ := (hA2_L.mul (hp2_L.eq_c hp32_eq.2)).eq_k (by omega)
  have hT1 : HasValGe 2 (A1 * p.2.2.2.1) := (hA1_5.mul hp1_L.val).mono (by omega)
  have hT0 : HasValGe 2 (A0 * p.2.2.2.2) := (hA0_5.mul hp0_L.val).mono (by omega)
  have htot := ((hT4.add_shift1 (hT3.add hT2)).add_high (hT1.add hT0))
  have hre : A4 * p.1 + A3 * p.2.1 + A2 * p.2.2.1 + A1 * p.2.2.2.1 + A0 * p.2.2.2.2 =
      (A4 * p.1 + (A3 * p.2.1 + A2 * p.2.2.1)) + (A1 * p.2.2.2.1 + A0 * p.2.2.2.2) := by ring
  rw [hre, show (1 : ℤ) = 0 + 1 by norm_num, htot.c1]
  exact br1_inf_combine_K5 hw0_eq

/-! ### Section 6: Main Theorem `infinityCoefficient_eta` -/

theorem infinityCoefficient_eta :
    CrossedRationalResidue.infinityCoefficient CoverResidue.eta = -toK5_RInf / L_K ^ 2 := by
  rw [infinityCoefficient_eq_coeff_one]
  unfold CoverResidue.eta
  rw [map_trace_AC_eq_sum_branches ψinf W1_inf W2_inf W1_inf_eq_ψinf W2_inf_eq_ψinf W1_W2_inf_sum_ψinf,
    HahnSeries.coeff_add]
  change (br1_inf eta_AC).coeff 1 + (br2_inf eta_AC).coeff 1 = _
  rw [br1_inf_eta_AC_coeff_one, br2_inf_eta_AC_coeff_one, add_zero]

end SymmetricSexticResidual.LocalResidueInf
