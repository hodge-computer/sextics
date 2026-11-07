import WeightedMatrixBindings
import ModularRank
import PackedCheckSound
import PackedRowChecks
import Mathlib.Tactic.FinCases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace WeightedSupport.CheckedRank
open Matrix


theorem Q_modular_binding : ∀ i j : Fin 82,
    (QMinor i j : ZMod 101) = (PackedCheck.digit PackedCheck.Qrows[i.val]! j.val : ZMod 101) := by
  intro i
  fin_cases i
  · exact Q_binding_row_0
  · exact Q_binding_row_1
  · exact Q_binding_row_2
  · exact Q_binding_row_3
  · exact Q_binding_row_4
  · exact Q_binding_row_5
  · exact Q_binding_row_6
  · exact Q_binding_row_7
  · exact Q_binding_row_8
  · exact Q_binding_row_9
  · exact Q_binding_row_10
  · exact Q_binding_row_11
  · exact Q_binding_row_12
  · exact Q_binding_row_13
  · exact Q_binding_row_14
  · exact Q_binding_row_15
  · exact Q_binding_row_16
  · exact Q_binding_row_17
  · exact Q_binding_row_18
  · exact Q_binding_row_19
  · exact Q_binding_row_20
  · exact Q_binding_row_21
  · exact Q_binding_row_22
  · exact Q_binding_row_23
  · exact Q_binding_row_24
  · exact Q_binding_row_25
  · exact Q_binding_row_26
  · exact Q_binding_row_27
  · exact Q_binding_row_28
  · exact Q_binding_row_29
  · exact Q_binding_row_30
  · exact Q_binding_row_31
  · exact Q_binding_row_32
  · exact Q_binding_row_33
  · exact Q_binding_row_34
  · exact Q_binding_row_35
  · exact Q_binding_row_36
  · exact Q_binding_row_37
  · exact Q_binding_row_38
  · exact Q_binding_row_39
  · exact Q_binding_row_40
  · exact Q_binding_row_41
  · exact Q_binding_row_42
  · exact Q_binding_row_43
  · exact Q_binding_row_44
  · exact Q_binding_row_45
  · exact Q_binding_row_46
  · exact Q_binding_row_47
  · exact Q_binding_row_48
  · exact Q_binding_row_49
  · exact Q_binding_row_50
  · exact Q_binding_row_51
  · exact Q_binding_row_52
  · exact Q_binding_row_53
  · exact Q_binding_row_54
  · exact Q_binding_row_55
  · exact Q_binding_row_56
  · exact Q_binding_row_57
  · exact Q_binding_row_58
  · exact Q_binding_row_59
  · exact Q_binding_row_60
  · exact Q_binding_row_61
  · exact Q_binding_row_62
  · exact Q_binding_row_63
  · exact Q_binding_row_64
  · exact Q_binding_row_65
  · exact Q_binding_row_66
  · exact Q_binding_row_67
  · exact Q_binding_row_68
  · exact Q_binding_row_69
  · exact Q_binding_row_70
  · exact Q_binding_row_71
  · exact Q_binding_row_72
  · exact Q_binding_row_73
  · exact Q_binding_row_74
  · exact Q_binding_row_75
  · exact Q_binding_row_76
  · exact Q_binding_row_77
  · exact Q_binding_row_78
  · exact Q_binding_row_79
  · exact Q_binding_row_80
  · exact Q_binding_row_81

#print axioms Q_modular_binding

theorem Q_inverse_checked :
    QMinor.map (Int.castRingHom (ZMod 101)) * QInverse = 1 := by
  ext i j
  have hr : PackedCheck.checkRow 82 PackedCheck.Qrows[i.val]! PackedCheck.Qcols i.val = true := by
    fin_cases i
    · exact PackedCheck.Q_row_0_checked
    · exact PackedCheck.Q_row_1_checked
    · exact PackedCheck.Q_row_2_checked
    · exact PackedCheck.Q_row_3_checked
    · exact PackedCheck.Q_row_4_checked
    · exact PackedCheck.Q_row_5_checked
    · exact PackedCheck.Q_row_6_checked
    · exact PackedCheck.Q_row_7_checked
    · exact PackedCheck.Q_row_8_checked
    · exact PackedCheck.Q_row_9_checked
    · exact PackedCheck.Q_row_10_checked
    · exact PackedCheck.Q_row_11_checked
    · exact PackedCheck.Q_row_12_checked
    · exact PackedCheck.Q_row_13_checked
    · exact PackedCheck.Q_row_14_checked
    · exact PackedCheck.Q_row_15_checked
    · exact PackedCheck.Q_row_16_checked
    · exact PackedCheck.Q_row_17_checked
    · exact PackedCheck.Q_row_18_checked
    · exact PackedCheck.Q_row_19_checked
    · exact PackedCheck.Q_row_20_checked
    · exact PackedCheck.Q_row_21_checked
    · exact PackedCheck.Q_row_22_checked
    · exact PackedCheck.Q_row_23_checked
    · exact PackedCheck.Q_row_24_checked
    · exact PackedCheck.Q_row_25_checked
    · exact PackedCheck.Q_row_26_checked
    · exact PackedCheck.Q_row_27_checked
    · exact PackedCheck.Q_row_28_checked
    · exact PackedCheck.Q_row_29_checked
    · exact PackedCheck.Q_row_30_checked
    · exact PackedCheck.Q_row_31_checked
    · exact PackedCheck.Q_row_32_checked
    · exact PackedCheck.Q_row_33_checked
    · exact PackedCheck.Q_row_34_checked
    · exact PackedCheck.Q_row_35_checked
    · exact PackedCheck.Q_row_36_checked
    · exact PackedCheck.Q_row_37_checked
    · exact PackedCheck.Q_row_38_checked
    · exact PackedCheck.Q_row_39_checked
    · exact PackedCheck.Q_row_40_checked
    · exact PackedCheck.Q_row_41_checked
    · exact PackedCheck.Q_row_42_checked
    · exact PackedCheck.Q_row_43_checked
    · exact PackedCheck.Q_row_44_checked
    · exact PackedCheck.Q_row_45_checked
    · exact PackedCheck.Q_row_46_checked
    · exact PackedCheck.Q_row_47_checked
    · exact PackedCheck.Q_row_48_checked
    · exact PackedCheck.Q_row_49_checked
    · exact PackedCheck.Q_row_50_checked
    · exact PackedCheck.Q_row_51_checked
    · exact PackedCheck.Q_row_52_checked
    · exact PackedCheck.Q_row_53_checked
    · exact PackedCheck.Q_row_54_checked
    · exact PackedCheck.Q_row_55_checked
    · exact PackedCheck.Q_row_56_checked
    · exact PackedCheck.Q_row_57_checked
    · exact PackedCheck.Q_row_58_checked
    · exact PackedCheck.Q_row_59_checked
    · exact PackedCheck.Q_row_60_checked
    · exact PackedCheck.Q_row_61_checked
    · exact PackedCheck.Q_row_62_checked
    · exact PackedCheck.Q_row_63_checked
    · exact PackedCheck.Q_row_64_checked
    · exact PackedCheck.Q_row_65_checked
    · exact PackedCheck.Q_row_66_checked
    · exact PackedCheck.Q_row_67_checked
    · exact PackedCheck.Q_row_68_checked
    · exact PackedCheck.Q_row_69_checked
    · exact PackedCheck.Q_row_70_checked
    · exact PackedCheck.Q_row_71_checked
    · exact PackedCheck.Q_row_72_checked
    · exact PackedCheck.Q_row_73_checked
    · exact PackedCheck.Q_row_74_checked
    · exact PackedCheck.Q_row_75_checked
    · exact PackedCheck.Q_row_76_checked
    · exact PackedCheck.Q_row_77_checked
    · exact PackedCheck.Q_row_78_checked
    · exact PackedCheck.Q_row_79_checked
    · exact PackedCheck.Q_row_80_checked
    · exact PackedCheck.Q_row_81_checked
  calc
    _ = ∑ t : Fin 82, (PackedCheck.digit PackedCheck.Qrows[i.val]! t.val : ZMod 101) *
        (PackedCheck.digit PackedCheck.Qcols[j.val]! t.val : ZMod 101) := by
      change (∑ t : Fin 82, (QMinor i t : ZMod 101) * QInverse t j) = _
      apply Finset.sum_congr rfl
      intro t ht
      exact congrArg (fun v : ZMod 101 => v * (PackedCheck.digit PackedCheck.Qcols[j.val]! t.val : ZMod 101)) (Q_modular_binding i t)
    _ = if i.val = j.val then 1 else 0 := PackedCheck.checkRow_sound 82 _ _ _ hr j
    _ = (1 : Matrix (Fin 82) (Fin 82) (ZMod 101)) i j := by simp only [Matrix.one_apply, Fin.ext_iff]

theorem Q_rational_minor_nonsingular :
    (QMinor.map (Int.castRingHom ℚ)).det ≠ 0 :=
  rational_det_ne_zero_of_modular_inverse _ _ Q_inverse_checked

theorem Q_minor_binding : QMatrix.submatrix QSelectRows id = QMinor := by rfl
theorem Q_rational_rank : (QMatrix.map (Int.castRingHom ℚ)).rank = 82 := by
  apply full_column_rank_of_nonsingular_minor _ QSelectRows
  change ((QMatrix.submatrix QSelectRows id).map (Int.castRingHom ℚ)).det ≠ 0
  rw [Q_minor_binding]
  exact Q_rational_minor_nonsingular


theorem HQ_modular_binding : ∀ i j : Fin 74,
    (HQMinor i j : ZMod 101) = (PackedCheck.digit PackedCheck.HQrows[i.val]! j.val : ZMod 101) := by
  intro i
  fin_cases i
  · exact HQ_binding_row_0
  · exact HQ_binding_row_1
  · exact HQ_binding_row_2
  · exact HQ_binding_row_3
  · exact HQ_binding_row_4
  · exact HQ_binding_row_5
  · exact HQ_binding_row_6
  · exact HQ_binding_row_7
  · exact HQ_binding_row_8
  · exact HQ_binding_row_9
  · exact HQ_binding_row_10
  · exact HQ_binding_row_11
  · exact HQ_binding_row_12
  · exact HQ_binding_row_13
  · exact HQ_binding_row_14
  · exact HQ_binding_row_15
  · exact HQ_binding_row_16
  · exact HQ_binding_row_17
  · exact HQ_binding_row_18
  · exact HQ_binding_row_19
  · exact HQ_binding_row_20
  · exact HQ_binding_row_21
  · exact HQ_binding_row_22
  · exact HQ_binding_row_23
  · exact HQ_binding_row_24
  · exact HQ_binding_row_25
  · exact HQ_binding_row_26
  · exact HQ_binding_row_27
  · exact HQ_binding_row_28
  · exact HQ_binding_row_29
  · exact HQ_binding_row_30
  · exact HQ_binding_row_31
  · exact HQ_binding_row_32
  · exact HQ_binding_row_33
  · exact HQ_binding_row_34
  · exact HQ_binding_row_35
  · exact HQ_binding_row_36
  · exact HQ_binding_row_37
  · exact HQ_binding_row_38
  · exact HQ_binding_row_39
  · exact HQ_binding_row_40
  · exact HQ_binding_row_41
  · exact HQ_binding_row_42
  · exact HQ_binding_row_43
  · exact HQ_binding_row_44
  · exact HQ_binding_row_45
  · exact HQ_binding_row_46
  · exact HQ_binding_row_47
  · exact HQ_binding_row_48
  · exact HQ_binding_row_49
  · exact HQ_binding_row_50
  · exact HQ_binding_row_51
  · exact HQ_binding_row_52
  · exact HQ_binding_row_53
  · exact HQ_binding_row_54
  · exact HQ_binding_row_55
  · exact HQ_binding_row_56
  · exact HQ_binding_row_57
  · exact HQ_binding_row_58
  · exact HQ_binding_row_59
  · exact HQ_binding_row_60
  · exact HQ_binding_row_61
  · exact HQ_binding_row_62
  · exact HQ_binding_row_63
  · exact HQ_binding_row_64
  · exact HQ_binding_row_65
  · exact HQ_binding_row_66
  · exact HQ_binding_row_67
  · exact HQ_binding_row_68
  · exact HQ_binding_row_69
  · exact HQ_binding_row_70
  · exact HQ_binding_row_71
  · exact HQ_binding_row_72
  · exact HQ_binding_row_73

#print axioms HQ_modular_binding

theorem HQ_inverse_checked :
    HQMinor.map (Int.castRingHom (ZMod 101)) * HQInverse = 1 := by
  ext i j
  have hr : PackedCheck.checkRow 74 PackedCheck.HQrows[i.val]! PackedCheck.HQcols i.val = true := by
    fin_cases i
    · exact PackedCheck.HQ_row_0_checked
    · exact PackedCheck.HQ_row_1_checked
    · exact PackedCheck.HQ_row_2_checked
    · exact PackedCheck.HQ_row_3_checked
    · exact PackedCheck.HQ_row_4_checked
    · exact PackedCheck.HQ_row_5_checked
    · exact PackedCheck.HQ_row_6_checked
    · exact PackedCheck.HQ_row_7_checked
    · exact PackedCheck.HQ_row_8_checked
    · exact PackedCheck.HQ_row_9_checked
    · exact PackedCheck.HQ_row_10_checked
    · exact PackedCheck.HQ_row_11_checked
    · exact PackedCheck.HQ_row_12_checked
    · exact PackedCheck.HQ_row_13_checked
    · exact PackedCheck.HQ_row_14_checked
    · exact PackedCheck.HQ_row_15_checked
    · exact PackedCheck.HQ_row_16_checked
    · exact PackedCheck.HQ_row_17_checked
    · exact PackedCheck.HQ_row_18_checked
    · exact PackedCheck.HQ_row_19_checked
    · exact PackedCheck.HQ_row_20_checked
    · exact PackedCheck.HQ_row_21_checked
    · exact PackedCheck.HQ_row_22_checked
    · exact PackedCheck.HQ_row_23_checked
    · exact PackedCheck.HQ_row_24_checked
    · exact PackedCheck.HQ_row_25_checked
    · exact PackedCheck.HQ_row_26_checked
    · exact PackedCheck.HQ_row_27_checked
    · exact PackedCheck.HQ_row_28_checked
    · exact PackedCheck.HQ_row_29_checked
    · exact PackedCheck.HQ_row_30_checked
    · exact PackedCheck.HQ_row_31_checked
    · exact PackedCheck.HQ_row_32_checked
    · exact PackedCheck.HQ_row_33_checked
    · exact PackedCheck.HQ_row_34_checked
    · exact PackedCheck.HQ_row_35_checked
    · exact PackedCheck.HQ_row_36_checked
    · exact PackedCheck.HQ_row_37_checked
    · exact PackedCheck.HQ_row_38_checked
    · exact PackedCheck.HQ_row_39_checked
    · exact PackedCheck.HQ_row_40_checked
    · exact PackedCheck.HQ_row_41_checked
    · exact PackedCheck.HQ_row_42_checked
    · exact PackedCheck.HQ_row_43_checked
    · exact PackedCheck.HQ_row_44_checked
    · exact PackedCheck.HQ_row_45_checked
    · exact PackedCheck.HQ_row_46_checked
    · exact PackedCheck.HQ_row_47_checked
    · exact PackedCheck.HQ_row_48_checked
    · exact PackedCheck.HQ_row_49_checked
    · exact PackedCheck.HQ_row_50_checked
    · exact PackedCheck.HQ_row_51_checked
    · exact PackedCheck.HQ_row_52_checked
    · exact PackedCheck.HQ_row_53_checked
    · exact PackedCheck.HQ_row_54_checked
    · exact PackedCheck.HQ_row_55_checked
    · exact PackedCheck.HQ_row_56_checked
    · exact PackedCheck.HQ_row_57_checked
    · exact PackedCheck.HQ_row_58_checked
    · exact PackedCheck.HQ_row_59_checked
    · exact PackedCheck.HQ_row_60_checked
    · exact PackedCheck.HQ_row_61_checked
    · exact PackedCheck.HQ_row_62_checked
    · exact PackedCheck.HQ_row_63_checked
    · exact PackedCheck.HQ_row_64_checked
    · exact PackedCheck.HQ_row_65_checked
    · exact PackedCheck.HQ_row_66_checked
    · exact PackedCheck.HQ_row_67_checked
    · exact PackedCheck.HQ_row_68_checked
    · exact PackedCheck.HQ_row_69_checked
    · exact PackedCheck.HQ_row_70_checked
    · exact PackedCheck.HQ_row_71_checked
    · exact PackedCheck.HQ_row_72_checked
    · exact PackedCheck.HQ_row_73_checked
  calc
    _ = ∑ t : Fin 74, (PackedCheck.digit PackedCheck.HQrows[i.val]! t.val : ZMod 101) *
        (PackedCheck.digit PackedCheck.HQcols[j.val]! t.val : ZMod 101) := by
      change (∑ t : Fin 74, (HQMinor i t : ZMod 101) * HQInverse t j) = _
      apply Finset.sum_congr rfl
      intro t ht
      exact congrArg (fun v : ZMod 101 => v * (PackedCheck.digit PackedCheck.HQcols[j.val]! t.val : ZMod 101)) (HQ_modular_binding i t)
    _ = if i.val = j.val then 1 else 0 := PackedCheck.checkRow_sound 74 _ _ _ hr j
    _ = (1 : Matrix (Fin 74) (Fin 74) (ZMod 101)) i j := by simp only [Matrix.one_apply, Fin.ext_iff]

theorem HQ_rational_minor_nonsingular :
    (HQMinor.map (Int.castRingHom ℚ)).det ≠ 0 :=
  rational_det_ne_zero_of_modular_inverse _ _ HQ_inverse_checked

theorem HQ_minor_binding : HQMatrix.submatrix id HQSelectColumns = HQMinor := by rfl
theorem HQ_rational_rank : (HQMatrix.map (Int.castRingHom ℚ)).rank = 74 := by
  apply full_row_rank_of_nonsingular_minor _ HQSelectColumns
  change ((HQMatrix.submatrix id HQSelectColumns).map (Int.castRingHom ℚ)).det ≠ 0
  rw [HQ_minor_binding]
  exact HQ_rational_minor_nonsingular

theorem HQ_kernel_finrank :
    Module.finrank ℚ (LinearMap.ker (HQMatrix.map (Int.castRingHom ℚ)).mulVecLin) = 8 := by
  have h := LinearMap.finrank_range_add_finrank_ker (HQMatrix.map (Int.castRingHom ℚ)).mulVecLin
  have hr := HQ_rational_rank
  change Module.finrank ℚ (LinearMap.range (HQMatrix.map (Int.castRingHom ℚ)).mulVecLin) = 74 at hr
  simp only [Module.finrank_pi, Fintype.card_fin] at h
  omega
end WeightedSupport.CheckedRank
#print axioms WeightedSupport.CheckedRank.Q_rational_rank
#print axioms WeightedSupport.CheckedRank.HQ_rational_rank
#print axioms WeightedSupport.CheckedRank.HQ_kernel_finrank
