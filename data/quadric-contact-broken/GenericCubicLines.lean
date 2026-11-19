import Proposal.ParameterEliminant
import Proposal.GenericCoordinateData
import Proposal.GenericEliminantEvaluation
import Proposal.GenericLineUnscale
import Proposal.ConcreteLine
import Mathlib.Tactic.LinearCombination

namespace GenericCubicLines
open Polynomial ParameterEliminant
open GenericLineChart

noncomputable section

def pe : E := algebraMap ParameterSpecialization.Coefficients E ParameterSpecialization.p
def qe : E := algebraMap ParameterSpecialization.Coefficients E ParameterSpecialization.q
def se : E := algebraMap ParameterSpecialization.Coefficients E ParameterSpecialization.s
def ke : E := algebraMap ParameterSpecialization.Coefficients E ParameterSpecialization.k
def ue : E := algebraMap ParameterSpecialization.Coefficients E ParameterSpecialization.u
def ve : E := algebraMap ParameterSpecialization.Coefficients E ParameterSpecialization.v

def a : E := qa root pe qe se ke ue ve
def b : E := qb root pe se ke ue ve
def c : E := qc root ke ue ve
def d : E := cd root pe qe se ke ue ve
def e : E := ce root pe qe se ke ue ve
def f : E := cf root pe ke ue ve
def g : E := cg root ke ue

def lineL : E := QuadricContact.Subresultant.linear a b c d e f
def lineM : E := QuadricContact.Subresultant.constant a b c d e g

def x : E := -lineM * Ring.inverse lineL
def y : E := root*x
def z : E := lineZ root pe qe se ke ue ve x
def w : E := lineW root pe qe se ke ue ve x

theorem isUnit_ke : IsUnit ke := ParameterSpecialization.isUnit_k.map (algebraMap _ E)

theorem isUnit_root : IsUnit root := by
  apply isUnit_of_special_isUnit
  rw [toSpecial_root]
  have h := AdjoinRootSpecialization.isUnit_mk_of_bezout GenericSpecialization.P
    GenericSpecialization.r_factor GenericSpecialization.r_inverse GenericSpecialization.r_quotient
    GenericSpecialization.r_bezout
  simpa [GenericSpecialization.r_factor] using h

theorem toSpecial_a : toSpecial a = AdjoinRoot.mk GenericSpecialization.P GenericSpecialization.a_factor := by
  rw [GenericSpecialization.a_factor_actual]
  simp only [a, GenericSpecialization.aActual, GenericSpecialization.kCoeff,
    qa, aa, hNum, map_mul, map_add, map_sub, map_pow, map_ofNat,
    toSpecial_root, pe, qe, se, ke, ue, ve, toSpecial_algebraMap,
    ParameterSpecialization.specialize_p, ParameterSpecialization.specialize_q,
    ParameterSpecialization.specialize_s, ParameterSpecialization.specialize_k,
    ParameterSpecialization.specialize_u, ParameterSpecialization.specialize_v,
    AdjoinRoot.mk_X, AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq]

theorem toSpecial_L : toSpecial lineL = AdjoinRoot.mk GenericSpecialization.P GenericSpecialization.L_factor := by
  rw [GenericSpecialization.L_factor_actual]
  simp only [lineL, a, b, c, d, e, f, GenericSpecialization.LActual,
    GenericSpecialization.aActual, GenericSpecialization.bActual, GenericSpecialization.cActual,
    GenericSpecialization.dActual, GenericSpecialization.eActual, GenericSpecialization.fActual,
    GenericSpecialization.kCoeff, QuadricContact.Subresultant.linear,
    qa, qb, qc, cd, ce, cf, aa, bb, hNum,
    map_mul, map_add, map_sub, map_pow, map_ofNat,
    toSpecial_root, pe, qe, se, ke, ue, ve, toSpecial_algebraMap,
    ParameterSpecialization.specialize_p, ParameterSpecialization.specialize_q,
    ParameterSpecialization.specialize_s, ParameterSpecialization.specialize_k,
    ParameterSpecialization.specialize_u, ParameterSpecialization.specialize_v,
    AdjoinRoot.mk_X, AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq]

theorem isUnit_a : IsUnit a := by
  apply isUnit_of_special_isUnit
  rw [toSpecial_a]
  exact AdjoinRootSpecialization.isUnit_mk_of_bezout _ _ _ _ GenericSpecialization.a_bezout

theorem isUnit_L : IsUnit lineL := by
  apply isUnit_of_special_isUnit
  rw [toSpecial_L]
  exact AdjoinRootSpecialization.isUnit_mk_of_bezout _ _ _ _ GenericSpecialization.L_bezout

theorem eliminant_root : eliminant root pe qe se ke ue ve = 0 := by
  have hraw : AdjoinRoot.mk P
      (GenericMonicPolynomial.rawPolynomial ParameterSpecialization.p ParameterSpecialization.q
        ParameterSpecialization.s ParameterSpecialization.k ParameterSpecialization.u
        ParameterSpecialization.v) = 0 := by
    rw [← GenericMonicPolynomial.leading_mul_monicPolynomial _ _ _ _ _ _
      ParameterSpecialization.isUnit_leadingCoefficient]
    change AdjoinRoot.mk P (C _ * P) = 0
    simp
  have he := GenericMonicPolynomial.rawPolynomial_eval₂
    (algebraMap ParameterSpecialization.Coefficients E) root ParameterSpecialization.p
    ParameterSpecialization.q ParameterSpecialization.s ParameterSpecialization.k
    ParameterSpecialization.u ParameterSpecialization.v
  rw [← aeval_def] at he
  change aeval (AdjoinRoot.root P) _ = _ at he
  rw [AdjoinRoot.aeval_eq, hraw] at he
  exact he.symm

theorem resultant_root : QuadricContact.Subresultant.resultant a b c d e f g = 0 := by
  change QuadricContact.Subresultant.resultant
    (qa root pe qe se ke ue ve) (qb root pe se ke ue ve) (qc root ke ue ve)
    (cd root pe qe se ke ue ve) (ce root pe qe se ke ue ve)
    (cf root pe ke ue ve) (cg root ke ue) = 0
  rw [eliminant_identity, eliminant_root, mul_zero]

theorem common_root : quadratic root pe qe se ke ue ve x = 0 ∧
    cubicEq root pe qe se ke ue ve x = 0 := by
  exact QuadricContact.Subresultant.common_root a b c d e f g
    (Ring.inverse a) (Ring.inverse lineL)
    (Ring.mul_inverse_cancel _ isUnit_a) (Ring.mul_inverse_cancel _ isUnit_L) resultant_root

/-- The actual generic line, before specializing alpha and beta. -/
theorem line_identity (B C : E) :
    cubic pe qe se ke ue ve (x*B+y*C) (z*B+w*C) B C = 0 := by
  exact unscaled_line root pe qe se ke ue ve x B C isUnit_ke isUnit_root
    common_root.1 common_root.2


theorem rel0_zero : QuadricContact.ConcreteLine.rel0 pe ue x z = 0 := by
  simpa [GenericLineChart.cubic, QuadricContact.ConcreteLine.rel0, mul_comm] using line_identity 1 0

theorem rel3_zero : QuadricContact.ConcreteLine.rel3 se ve y w = 0 := by
  simpa [GenericLineChart.cubic, QuadricContact.ConcreteLine.rel3, mul_comm] using line_identity 0 1

theorem isUnit_two : IsUnit (2 : E) := by
  have h : IsUnit (2 : ℚ) := isUnit_iff_ne_zero.mpr (by norm_num)
  simpa only [map_ofNat] using h.map (algebraMap ℚ E)

theorem rel1_zero : QuadricContact.ConcreteLine.rel1 pe qe ke x y z w = 0 := by
  apply isUnit_two.mul_right_eq_zero.mp
  have hp := line_identity 1 1
  have hm := line_identity 1 (-1)
  have h3 := rel3_zero
  unfold GenericLineChart.cubic at hp hm
  unfold QuadricContact.ConcreteLine.rel3 at h3
  unfold QuadricContact.ConcreteLine.rel1
  linear_combination hp - hm - 2*h3

theorem rel2_zero : QuadricContact.ConcreteLine.rel2 qe se ke x y z w = 0 := by
  apply isUnit_two.mul_right_eq_zero.mp
  have hp := line_identity 1 1
  have hm := line_identity 1 (-1)
  have h0 := rel0_zero
  unfold GenericLineChart.cubic at hp hm
  unfold QuadricContact.ConcreteLine.rel0 at h0
  unfold QuadricContact.ConcreteLine.rel2
  linear_combination hp + hm - 2*h0

end
end GenericCubicLines
