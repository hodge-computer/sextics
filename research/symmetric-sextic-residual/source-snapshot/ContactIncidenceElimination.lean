import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
Exact elimination used in `contact_alpha_elimination.json`.

The protected contact chart has q=q0+q2*alpha^2 and
h=a0+a2*alpha^2+alpha*(b0+b2*alpha^2).  These lemmas prove the
elimination and its Jacobian factor over an arbitrary field.  The actual
coefficient binding is checked by the accompanying independent Python audit.
The bN=0 summand is not discarded by any theorem in this module.
-/

namespace ContactIncidenceElimination

section Ring
variable {R : Type*} [CommRing R]

def q (q0 q2 α : R) := q0 + q2 * α^2
def h (a0 a2 b0 b2 α : R) := a0 + a2 * α^2 + α * (b0 + b2 * α^2)
def aN (q0 q2 a0 a2 : R) := q2*a0-q0*a2
def bN (q0 q2 b0 b2 : R) := q2*b0-q0*b2
def resultant (q0 q2 a0 a2 b0 b2 : R) :=
  q2 * aN q0 q2 a0 a2 ^ 2 + q0 * bN q0 q2 b0 b2 ^ 2

theorem linear_identity (q0 q2 a0 a2 b0 b2 α : R) :
    q2*h a0 a2 b0 b2 α - (a2+α*b2)*q q0 q2 α =
      aN q0 q2 a0 a2 + α*bN q0 q2 b0 b2 := by
  unfold q h aN bN
  ring

theorem resultant_identity (q0 q2 a0 a2 b0 b2 α : R) :
    resultant q0 q2 a0 a2 b0 b2 =
      bN q0 q2 b0 b2 ^ 2 * q q0 q2 α +
      q2 * (aN q0 q2 a0 a2 - α*bN q0 q2 b0 b2) *
        (aN q0 q2 a0 a2 + α*bN q0 q2 b0 b2) := by
  unfold resultant q aN bN
  ring

theorem cleared_h_substitution (q0 q2 a0 a2 b0 b2 : R) :
    a0 * bN q0 q2 b0 b2 ^ 3 +
      a2 * aN q0 q2 a0 a2 ^ 2 * bN q0 q2 b0 b2 -
      aN q0 q2 a0 a2 * b0 * bN q0 q2 b0 b2 ^ 2 -
      b2 * aN q0 q2 a0 a2 ^ 3 =
        (a2*b0-a0*b2) * resultant q0 q2 a0 a2 b0 b2 := by
  unfold resultant aN bN
  ring

/-- Exact chain-rule calculation for the cofactor tangent of the 44 unchanged
contact equations. The six dotted coefficients are arbitrary tangent values. -/
theorem eliminated_jacobian_factor
    (q0 q2 a0 a2 b0 b2 α dq0 dq2 da0 da2 db0 db2 : R)
    (hq : q q0 q2 α = 0) (hh : h a0 a2 b0 b2 α = 0) :
    dq2 * aN q0 q2 a0 a2 ^ 2 +
      2*q2*aN q0 q2 a0 a2*(dq2*a0+q2*da0-dq0*a2-q0*da2) +
      dq0 * bN q0 q2 b0 b2 ^ 2 +
      2*q0*bN q0 q2 b0 b2*(dq2*b0+q2*db0-dq0*b2-q0*db2) =
      q2*bN q0 q2 b0 b2 *
        ((dq0+dq2*α^2)*(2*a2*α+b0+3*b2*α^2) -
          (2*q2*α)*(da0+da2*α^2+α*(db0+db2*α^2))) := by
  have hq0 : q0 = -q2*α^2 := by
    unfold q at hq
    linear_combination hq
  have ha0 : a0 = -a2*α^2-α*(b0+b2*α^2) := by
    unfold h at hh
    linear_combination hh
  unfold aN bN
  rw [hq0, ha0]
  ring

end Ring

section Field
variable {R : Type*} [Field R]

theorem q_substitution (q0 q2 a0 a2 b0 b2 : R)
    (hb : bN q0 q2 b0 b2 ≠ 0) :
    q q0 q2 (-aN q0 q2 a0 a2 / bN q0 q2 b0 b2) =
      resultant q0 q2 a0 a2 b0 b2 / bN q0 q2 b0 b2 ^ 2 := by
  unfold q resultant
  field_simp
  ring

theorem h_substitution (q0 q2 a0 a2 b0 b2 : R)
    (hb : bN q0 q2 b0 b2 ≠ 0) :
    h a0 a2 b0 b2 (-aN q0 q2 a0 a2 / bN q0 q2 b0 b2) =
      (a2*b0-a0*b2)*resultant q0 q2 a0 a2 b0 b2 /
        bN q0 q2 b0 b2 ^ 3 := by
  unfold h
  field_simp
  linear_combination cleared_h_substitution q0 q2 a0 a2 b0 b2

theorem alpha_elimination (q0 q2 a0 a2 b0 b2 α : R)
    (hb : bN q0 q2 b0 b2 ≠ 0) :
    (q q0 q2 α = 0 ∧ h a0 a2 b0 b2 α = 0) ↔
      (resultant q0 q2 a0 a2 b0 b2 = 0 ∧
        α = -aN q0 q2 a0 a2 / bN q0 q2 b0 b2) := by
  constructor
  · rintro ⟨hq, hh⟩
    have hlin : aN q0 q2 a0 a2 + α*bN q0 q2 b0 b2 = 0 := by
      rw [← linear_identity q0 q2 a0 a2 b0 b2 α, hq, hh]
      ring
    constructor
    · rw [resultant_identity q0 q2 a0 a2 b0 b2 α, hq, hlin]
      ring
    · apply (eq_div_iff hb).2
      linear_combination hlin
  · rintro ⟨hp, rfl⟩
    constructor
    · rw [q_substitution q0 q2 a0 a2 b0 b2 hb, hp]
      simp
    · rw [h_substitution q0 q2 a0 a2 b0 b2 hb, hp]
      simp

/-- The omitted bN=0 summand also has aN=0; it is not proved empty. -/
theorem residual_aN_zero (q0 q2 a0 a2 b0 b2 α : R)
    (hq : q q0 q2 α = 0) (hh : h a0 a2 b0 b2 α = 0)
    (hb : bN q0 q2 b0 b2 = 0) : aN q0 q2 a0 a2 = 0 := by
  have hx := linear_identity q0 q2 a0 a2 b0 b2 α
  rw [hq, hh, hb] at hx
  simpa using hx.symm

end Field

#print axioms eliminated_jacobian_factor
#print axioms alpha_elimination
#print axioms residual_aN_zero

end ContactIncidenceElimination
