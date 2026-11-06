import Proposal.PEllipticAmbientTransfer
import HodgeComputer.Constructions.BinaryCubic.Derivatives

/-! # Actual frozen coefficient blocks and the supplied factored scalar tuple -/
set_option autoImplicit false
noncomputable section
namespace HodgeTestbed.EllipticAmbient
open HodgeTestbed.FrozenChart HodgeTestbed.Conic
open scoped BigOperators

/-- Coefficients in U of the first frozen cubic after removing chart denominators. -/
def pCoefficients {R : Type*} [CommRing R] (x y : R) : Cubic.Data R :=
  ⟨14, 7*x^2+21*y^2, 23*x^4+12*x^2*y^2+23*y^4,
    4*x^6+39*x^4*y^2+73*x^2*y^4+8*y^6⟩
/-- Coefficients in U of Q(r²,U,z²), with leading coefficient 59. -/
def qCoefficients {R : Type*} [CommRing R] (r z : R) : Cubic.Data R :=
  ⟨59, 43*r^2+61*z^2, 37*r^4+47*r^2*z^2+67*z^4,
    31*r^6+41*r^4*z^2+53*r^2*z^4+71*z^6⟩
def pc : Cubic.Data K4 := pCoefficients (coord (0 : Fin 4)) (coord (1 : Fin 4))
def qc : Cubic.Data K4 := qCoefficients (coord (2 : Fin 4)) (coord (3 : Fin 4))
def EP : Derivation ℚ K4 K4 := coord (0 : Fin 4) • rationalPartial 0 + coord (1 : Fin 4) • rationalPartial 1
def EQ : Derivation ℚ K4 K4 := coord (2 : Fin 4) • rationalPartial 2 + coord (3 : Fin 4) • rationalPartial 3

theorem fourP_cubic : fourP = Cubic.f pc := by
  simp only [fourP, pc, pCoefficients, Cubic.f, Incidence.P]
  ring
theorem fourQ_cubic : fourQ = Cubic.f qc := by
  simp only [fourQ, qc, qCoefficients, Cubic.f, Incidence.Q]
  ring

@[simp] theorem EP_coord (i : Fin 4) : EP (coord i) = if i.val < 2 then coord i else 0 := by
  fin_cases i <;> norm_num [EP, Derivation.add_apply, Derivation.smul_apply, smul_eq_mul, partial_coord, Fin.ext_iff]
@[simp] theorem EQ_coord (i : Fin 4) : EQ (coord i) = if 2 ≤ i.val then coord i else 0 := by
  fin_cases i <;> norm_num [EQ, Derivation.add_apply, Derivation.smul_apply, smul_eq_mul, partial_coord, Fin.ext_iff]
  all_goals rfl

theorem pc_weights : Cubic.Weights EP pc := by
  constructor <;>
    norm_num [pc, pCoefficients, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
      Cubic.deriv_ofNat EP 14, Cubic.deriv_ofNat EP 7, Cubic.deriv_ofNat EP 21,
      Cubic.deriv_ofNat EP 23, Cubic.deriv_ofNat EP 12, Cubic.deriv_ofNat EP 4,
      Cubic.deriv_ofNat EP 39, Cubic.deriv_ofNat EP 73, Cubic.deriv_ofNat EP 8]
  all_goals ring

theorem qc_weights : Cubic.Weights EQ qc := by
  constructor <;>
    norm_num [qc, qCoefficients, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
      Cubic.deriv_ofNat EQ 59, Cubic.deriv_ofNat EQ 43, Cubic.deriv_ofNat EQ 61,
      Cubic.deriv_ofNat EQ 37, Cubic.deriv_ofNat EQ 47, Cubic.deriv_ofNat EQ 67,
      Cubic.deriv_ofNat EQ 31, Cubic.deriv_ofNat EQ 41, Cubic.deriv_ofNat EQ 53, Cubic.deriv_ofNat EQ 71]
  all_goals ring

theorem pc_constant : EQ pc.a = 0 ∧ EQ pc.b = 0 ∧ EQ pc.c = 0 ∧ EQ pc.d = 0 := by
  norm_num [pc, pCoefficients, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
    Cubic.deriv_ofNat EQ 14, Cubic.deriv_ofNat EQ 7, Cubic.deriv_ofNat EQ 21,
    Cubic.deriv_ofNat EQ 23, Cubic.deriv_ofNat EQ 12, Cubic.deriv_ofNat EQ 4,
    Cubic.deriv_ofNat EQ 39, Cubic.deriv_ofNat EQ 73, Cubic.deriv_ofNat EQ 8]
theorem qc_constant : EP qc.a = 0 ∧ EP qc.b = 0 ∧ EP qc.c = 0 ∧ EP qc.d = 0 := by
  norm_num [qc, qCoefficients, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
    Cubic.deriv_ofNat EP 59, Cubic.deriv_ofNat EP 43, Cubic.deriv_ofNat EP 61,
    Cubic.deriv_ofNat EP 37, Cubic.deriv_ofNat EP 47, Cubic.deriv_ofNat EP 67,
    Cubic.deriv_ofNat EP 31, Cubic.deriv_ofNat EP 41, Cubic.deriv_ofNat EP 53, Cubic.deriv_ofNat EP 71]

/-- The actual root-free common denominator, S=2G. -/
def actualS : K4 := 2*Cubic.G pc qc
def actualNP : K4 := Cubic.f pc*Cubic.V pc qc
def actualNQ : K4 := -Cubic.f pc*Cubic.U pc qc
/-- Exactly p*(xV,yV,-rU,-zU), in the supplied scalar packet order. -/
def actualT : Fin 4 → K4 :=
  ![coord (0 : Fin 4)*actualNP, coord (1 : Fin 4)*actualNP, coord (2 : Fin 4)*actualNQ, coord (3 : Fin 4)*actualNQ]

theorem actualT_action (g : K4) : fieldAction rationalPartial actualT g = actualNP*EP g + actualNQ*EQ g := by
  simp only [fieldAction_apply, Fin.sum_univ_succ]
  norm_num [actualT, EP, EQ, Derivation.add_apply, Derivation.smul_apply,
    smul_eq_mul, Matrix.cons_val_succ, Matrix.cons_val_two]
  simp only [show Fin.succ (2 : Fin 3) = (3 : Fin 4) from rfl]
  ring

theorem actualT_divergence : fieldDivergence rationalPartial actualT =
    EP actualNP + EQ actualNQ + 2*actualNP + 2*actualNQ := by
  simp only [fieldDivergence, Fin.sum_univ_succ]
  norm_num [actualT, EP, EQ, Derivation.add_apply, Derivation.smul_apply,
    Derivation.leibniz, smul_eq_mul, Matrix.cons_val_succ, Matrix.cons_val_two, partial_coord, Fin.ext_iff]
  simp only [show Fin.succ (2 : Fin 3) = (3 : Fin 4) from rfl, if_pos rfl]
  ring

theorem actual_radial_derivatives :
    EP actualS = 2*Cubic.dPG pc qc ∧ EQ actualS = 2*Cubic.dQG pc qc ∧
    EP actualNP = Cubic.rf pc*Cubic.V pc qc+Cubic.f pc*Cubic.dPV pc qc ∧
    EQ actualNQ = -Cubic.f pc*Cubic.dQU pc qc ∧
    EP (Cubic.f pc) = Cubic.rf pc ∧ EQ (Cubic.f pc) = 0 ∧
    EP (Cubic.f qc) = 0 ∧ EQ (Cubic.f qc) = Cubic.rf qc := by
  obtain ⟨pa, pb, pd, ph, pt, pk, pl⟩ := Cubic.weighted_derivatives EP pc pc_weights
  obtain ⟨qa, qb, qd, qh, qt, qk, ql⟩ := Cubic.weighted_derivatives EQ qc qc_weights
  obtain ⟨pza, pzb, pzd, pzh, pzt, pzk, pzl⟩ :=
    Cubic.constant_derivatives EQ pc pc_constant.1 pc_constant.2.1 pc_constant.2.2.1 pc_constant.2.2.2
  obtain ⟨qza, qzb, qzd, qzh, qzt, qzk, qzl⟩ :=
    Cubic.constant_derivatives EP qc qc_constant.1 qc_constant.2.1 qc_constant.2.2.1 qc_constant.2.2.2
  simp only [actualS, actualNP, actualNQ, Cubic.G, Cubic.U, Cubic.V, Cubic.dPG, Cubic.dQG,
    Cubic.dPV, Cubic.dQU, map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow,
    smul_eq_mul, pa, pb, pd, ph, pt, pk, pl, qa, qb, qd, qh, qt, qk, ql,
    pza, pzb, pzd, pzh, pzt, pzk, pzl, qza, qzb, qzd, qzh, qzt, qzk, qzl,
    Cubic.deriv_ofNat EP 2, Cubic.deriv_ofNat EQ 2, Cubic.deriv_ofNat EP 3, Cubic.deriv_ofNat EQ 3]
  norm_num
  repeat' constructor <;> ring
  all_goals simp

/-- The supplied explicit frozen scalar tuple satisfies its full cleared equation.
The scalar equation is proved here, and is no longer an input. -/
theorem actual_scalar_identity : scalarNumerator actualT actualS = 0 := by
  obtain ⟨hsP, hsQ, hnP, hnQ, hfP, hfQ, hgP, hgQ⟩ := actual_radial_derivatives
  rw [scalarNumerator, actualT_divergence, actualT_action, actualT_action, actualT_action,
    fourP_cubic, fourQ_cubic, hsP, hsQ, hnP, hnQ, hfP, hfQ, hgP, hgQ]
  convert Cubic.radial_scalar_identity pc qc using 1
  simp only [actualS, actualNP, actualNQ, Cubic.radialScalar]
  ring

end HodgeTestbed.EllipticAmbient
