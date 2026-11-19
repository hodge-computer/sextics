import Proposal.GenericCubicLines

namespace GenericCubicLines
open Polynomial ParameterEliminant GenericLineChart

noncomputable section

theorem toSpecial_M : toSpecial lineM = AdjoinRoot.mk GenericSpecialization.P GenericSpecialization.MActual := by
  simp only [lineM, a, b, c, d, e, g, GenericSpecialization.MActual,
    GenericSpecialization.aActual, GenericSpecialization.bActual, GenericSpecialization.cActual,
    GenericSpecialization.dActual, GenericSpecialization.eActual, GenericSpecialization.gActual,
    GenericSpecialization.kCoeff, QuadricContact.Subresultant.constant,
    qa, qb, qc, cd, ce, cg, aa, bb, hNum,
    map_mul, map_add, map_sub, map_pow, map_ofNat,
    toSpecial_root, pe, qe, se, ke, ue, ve, toSpecial_algebraMap,
    ParameterSpecialization.specialize_p, ParameterSpecialization.specialize_q,
    ParameterSpecialization.specialize_s, ParameterSpecialization.specialize_k,
    ParameterSpecialization.specialize_u, ParameterSpecialization.specialize_v,
    AdjoinRoot.mk_X, AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq]

theorem x_mul_L : x * lineL = -lineM := by
  unfold x
  rw [mul_assoc, Ring.inverse_mul_cancel _ isUnit_L, mul_one]

theorem toSpecial_x : toSpecial x = AdjoinRoot.mk GenericSpecialization.P GenericSpecialization.line_x := by
  apply (isUnit_L.map toSpecial).mul_left_inj.mp
  have h := congrArg (AdjoinRoot.mk GenericSpecialization.P)
    GenericSpecialization.coordinate_relation_x
  simp only [map_add, map_mul, AdjoinRoot.mk_self, zero_mul] at h
  rw [← GenericSpecialization.L_factor_actual] at h
  rw [← toSpecial_L, ← toSpecial_M] at h
  rw [← map_mul, x_mul_L, map_neg]
  exact (eq_neg_of_add_eq_zero_left h).symm

theorem toSpecial_y : toSpecial y = AdjoinRoot.mk GenericSpecialization.P GenericSpecialization.line_y := by
  have h := congrArg (AdjoinRoot.mk GenericSpecialization.P)
    GenericSpecialization.coordinate_relation_y
  simp only [map_sub, map_mul, AdjoinRoot.mk_self, zero_mul, AdjoinRoot.mk_X] at h
  simp only [y, map_mul, toSpecial_root, toSpecial_x]
  exact (sub_eq_zero.mp h).symm

theorem z_mul_scale : z * (ke^3*root^3) = aa root pe qe se ke ue ve*x+ke^2*root*bb root ue ve := by
  unfold z lineZ
  rw [mul_assoc, Ring.inverse_mul_cancel _ ((isUnit_ke.pow 3).mul (isUnit_root.pow 3)), mul_one]

theorem toSpecial_z : toSpecial z = AdjoinRoot.mk GenericSpecialization.P GenericSpecialization.line_z := by
  apply (((isUnit_ke.pow 3).mul (isUnit_root.pow 3)).map toSpecial).mul_left_inj.mp
  rw [← map_mul, z_mul_scale]
  have h := congrArg (AdjoinRoot.mk GenericSpecialization.P)
    GenericSpecialization.coordinate_relation_z
  simp only [map_sub, map_mul, map_add, map_pow, map_ofNat, AdjoinRoot.mk_self, zero_mul,
    AdjoinRoot.mk_X, AdjoinRoot.mk_C, GenericSpecialization.kCoeff,
    GenericLineChart.aa, GenericLineChart.bb, GenericLineChart.hNum] at h
  simp only [map_add, map_mul, map_sub, map_pow, map_ofNat, toSpecial_x, toSpecial_root,
    aa, bb, hNum, pe, qe, se, ke, ue, ve, toSpecial_algebraMap,
    ParameterSpecialization.specialize_p, ParameterSpecialization.specialize_q,
    ParameterSpecialization.specialize_s, ParameterSpecialization.specialize_k,
    ParameterSpecialization.specialize_u, ParameterSpecialization.specialize_v]
  norm_num [map_ofNat, ← AdjoinRoot.algebraMap_eq] at h ⊢
  linear_combination -h

theorem w_sub_mul_scale : (w-root*z)*(ke*root) = hNum root ue ve := by
  unfold w lineW
  change (root*z+hNum root ue ve*Ring.inverse (ke*root)-root*z)*(ke*root) = _
  rw [add_sub_cancel_left, mul_assoc, Ring.inverse_mul_cancel _ (isUnit_ke.mul isUnit_root), mul_one]

theorem toSpecial_w : toSpecial w = AdjoinRoot.mk GenericSpecialization.P GenericSpecialization.line_w := by
  apply ((isUnit_ke.mul isUnit_root).map toSpecial).mul_left_inj.mp
  have hw := congrArg toSpecial w_sub_mul_scale
  have h := congrArg (AdjoinRoot.mk GenericSpecialization.P)
    GenericSpecialization.coordinate_relation_w
  simp only [map_sub, map_mul, map_add, map_pow, map_ofNat, AdjoinRoot.mk_self, zero_mul,
    AdjoinRoot.mk_X, AdjoinRoot.mk_C, GenericSpecialization.kCoeff,
    GenericLineChart.hNum] at h
  simp only [map_add, map_mul, map_sub, map_pow, map_ofNat, toSpecial_z, toSpecial_root,
    hNum, ke, ue, ve, toSpecial_algebraMap,
    ParameterSpecialization.specialize_k,
    ParameterSpecialization.specialize_u, ParameterSpecialization.specialize_v] at hw ⊢
  norm_num [map_ofNat, ← AdjoinRoot.algebraMap_eq] at h hw ⊢
  linear_combination hw - h

end
end GenericCubicLines
