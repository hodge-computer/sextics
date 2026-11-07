import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
Exact incidence-minor algebra for two equations q=h=0 in (K,alpha,r,s).
Here qK,qa,qr,qs and hK,ha,hr,hs denote their first derivatives.
No contact solution, source identity, or nonzero Jacobian is asserted to exist.
-/

namespace ContactIncidenceAlgebra

section Ring
variable {R : Type*} [CommRing R]

def jacobian (qK qa hK ha : R) := qK*ha-qa*hK
def uNumerator (qa qr ha hr : R) := qa*hr-ha*qr
def vNumerator (qa qs ha hs : R) := qa*hs-ha*qs
def zNumerator (qr qs hr hs : R) := qr*hs-qs*hr
def alphaNumerator (qK qi hK hi : R) := hK*qi-qK*hi

/-- The determinant of the two Cramer solutions is J times the remaining minor. -/
theorem incidence_minor_identity (qK qa qr qs hK ha hr hs : R) :
    uNumerator qa qr ha hr * alphaNumerator qK qs hK hs
      - vNumerator qa qs ha hs * alphaNumerator qK qr hK hr =
      jacobian qK qa hK ha * zNumerator qr qs hr hs := by
  unfold uNumerator vNumerator alphaNumerator jacobian zNumerator
  ring

theorem q_annihilator (qa qr qs ha hr hs : R) :
    uNumerator qa qr ha hr * qs - vNumerator qa qs ha hs * qr
      + zNumerator qr qs hr hs * qa = 0 := by
  unfold uNumerator vNumerator zNumerator
  ring

theorem h_annihilator (qa qr qs ha hr hs : R) :
    uNumerator qa qr ha hr * hs - vNumerator qa qs ha hs * hr
      + zNumerator qr qs hr hs * ha = 0 := by
  unfold uNumerator vNumerator zNumerator
  ring

theorem q_cramer_numerator (qK qa qi hK ha hi : R) :
    qK*uNumerator qa qi ha hi + qa*alphaNumerator qK qi hK hi
      + jacobian qK qa hK ha*qi = 0 := by
  unfold uNumerator alphaNumerator jacobian
  ring

theorem h_cramer_numerator (qK qa qi hK ha hi : R) :
    hK*uNumerator qa qi ha hi + ha*alphaNumerator qK qi hK hi
      + jacobian qK qa hK ha*hi = 0 := by
  unfold uNumerator alphaNumerator jacobian
  ring
end Ring

section Field
variable {R : Type*} [Field R]

/-- The actual rational tangent coordinates solve both differentiated incidence equations. -/
theorem cramer_tangent (qK qa qi hK ha hi : R) (hJ : jacobian qK qa hK ha ≠ 0) :
    qK*(uNumerator qa qi ha hi / jacobian qK qa hK ha)
      + qa*(alphaNumerator qK qi hK hi / jacobian qK qa hK ha) + qi = 0 ∧
    hK*(uNumerator qa qi ha hi / jacobian qK qa hK ha)
      + ha*(alphaNumerator qK qi hK hi / jacobian qK qa hK ha) + hi = 0 := by
  constructor
  · field_simp [hJ]
    simpa only [mul_zero] using q_cramer_numerator qK qa qi hK ha hi
  · field_simp [hJ]
    simpa only [mul_zero] using h_cramer_numerator qK qa qi hK ha hi

/-- Wedge coefficient obtained from the two rational Cramer solutions. -/
theorem cramer_wedge (qK qa qr qs hK ha hr hs : R)
    (hJ : jacobian qK qa hK ha ≠ 0) :
    (uNumerator qa qr ha hr / jacobian qK qa hK ha) *
        (alphaNumerator qK qs hK hs / jacobian qK qa hK ha)
      - (vNumerator qa qs ha hs / jacobian qK qa hK ha) *
        (alphaNumerator qK qr hK hr / jacobian qK qa hK ha) =
      zNumerator qr qs hr hs / jacobian qK qa hK ha := by
  field_simp [hJ]
  exact incidence_minor_identity qK qa qr qs hK ha hr hs
end Field

#print axioms incidence_minor_identity
#print axioms cramer_tangent
#print axioms cramer_wedge
end ContactIncidenceAlgebra
