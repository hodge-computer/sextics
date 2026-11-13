import Proposal.GeometricAffineCurveCharts
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Literal adjunction transition on the x1/x2 overlap

In chart x1=1 use (a,b,c)=(x0/x1,x2/x1,x3/x1). In chart x2=1 use
(A,B,C)=(a/b,1/b,c/b). The coordinate Jacobian has determinant -b^(-4).
The quadratic and cubic equations transform by b^(-2) and b^(-3).
Their derivatives include the off-curve terms -2*b^(-3)*f*db and
-3*b^(-4)*h*db; these are retained before imposing f=h=0.

Thus the conormal determinant scales by b^(-5), whereas the ambient
volume scales by -b^(-4). With the projective signs (-1)^j, the adjunction
frame on the second chart is b times the first frame, exactly x2/x1.
All identities are over commutative rings with a specified unit, not just
at sample points or in a field of meromorphic functions.

This implements the local formulas needed for a canonical-sheaf comparison.
It does not itself construct that sheaf comparison or a Serre trace.
Validation: this module compiles under Lean 4.33.1 and the pinned Mathlib
revision, and passes independent leanchecker replay. The global
canonical-sheaf and Serre-trace comparisons remain separate obligations.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2GeometricAdjunctionOverlap

open MvPolynomial CycleQ2GeometricAffineCurveCharts

section Algebra
variable {R : Type*} [CommRing R]

/-- Differentials of the first-chart quadratic. -/
def gradQuadricOne (r a : R) : Fin 3 → R := ![2 * a, 0, -r]

/-- Differentials of the first-chart cubic, with both parameters retained. -/
def gradCubicOne (i θ a b c : R) : Fin 3 → R :=
  ![b * c + 1 + 3 * θ * a ^ 2,
    3 * b ^ 2 + c + a * c,
    3 * (1 - i) * c ^ 2 + b + a * b]

def gradQuadricTwo (r a b c : R) : Fin 3 → R := ![2 * a, -r * c, -r * b]

def gradCubicTwo (i θ a b c : R) : Fin 3 → R :=
  ![c + b ^ 2 + 3 * θ * a ^ 2,
    c + 2 * a * b - 3 * i * b ^ 2,
    3 * (1 - i) * c ^ 2 + b + a]

/-- Entries are derivatives of the new coordinates with respect to (a,b,c).
The inverse coordinate t will subsequently be the value of b^(-1). -/
def coordinateJacobian (a c t : R) : Matrix (Fin 3) (Fin 3) R :=
  !![t, -a * t ^ 2, 0;
     0, -t ^ 2, 0;
     0, -c * t ^ 2, t]

def pullRow (a c t : R) (v : Fin 3 → R) : Fin 3 → R :=
  fun j => ∑ k : Fin 3, v k * coordinateJacobian a c t k j

theorem quadratic_scaling (r a c t : R) :
    quadricTwo r (a * t) t (c * t) = t ^ 2 * quadricOne r a 0 c := by
  dsimp [quadricOne, quadricTwo]
  ring

/-- The inverse-unit equation is the only extra relation used. -/
theorem cubic_scaling (i θ a b c t : R) (ht : b * t = 1) :
    cubicTwo i θ (a * t) t (c * t) = t ^ 3 * cubicOne i θ a b c := by
  dsimp [cubicOne, cubicTwo]
  linear_combination -(a * c * t ^ 2 + b ^ 2 * t ^ 2 + b * t + c * t ^ 2 + 1) * ht

/-- These identities retain the derivative of the scaling factor even off
of the curve. A later quotient, not a frozen coefficient, removes it. -/
theorem quadratic_differential_change (r a c t : R) :
    pullRow a c t (gradQuadricTwo r (a * t) t (c * t)) =
      fun j => t ^ 2 * gradQuadricOne r a j -
        (if j = 1 then 2 * t ^ 3 * quadricOne r a 0 c else 0) := by
  funext j
  fin_cases j <;>
    simp [pullRow, coordinateJacobian, gradQuadricOne, gradQuadricTwo,
      quadricOne, Fin.sum_univ_succ] <;> ring

theorem cubic_differential_change (i θ a b c t : R) (ht : b * t = 1) :
    pullRow a c t (gradCubicTwo i θ (a * t) t (c * t)) =
      fun j => t ^ 3 * gradCubicOne i θ a b c j -
        (if j = 1 then 3 * t ^ 4 * cubicOne i θ a b c else 0) := by
  funext j
  fin_cases j
  · simp [pullRow, coordinateJacobian, gradCubicOne, gradCubicTwo,
      cubicOne, Fin.sum_univ_succ] <;>
      linear_combination -(c * t ^ 2) * ht
  · simp [pullRow, coordinateJacobian, gradCubicOne, gradCubicTwo,
      cubicOne, Fin.sum_univ_succ] <;>
      linear_combination (3 * t ^ 3 * (a * c + b ^ 2 + c)) * ht
  · simp [pullRow, coordinateJacobian, gradCubicOne, gradCubicTwo,
      cubicOne, Fin.sum_univ_succ] <;>
      linear_combination -(t ^ 2 * (a + 1)) * ht

/-- The derivative rows transform diagonally in the actual conormal
quotient, because the defining equations, not their derivatives, vanish. -/
theorem conormal_change_on_curve (r i θ a b c t : R) (ht : b * t = 1)
    (hf : quadricOne r a b c = 0) (hh : cubicOne i θ a b c = 0) :
    pullRow a c t (gradQuadricTwo r (a * t) t (c * t)) =
      (fun j => t ^ 2 * gradQuadricOne r a j) ∧
    pullRow a c t (gradCubicTwo i θ (a * t) t (c * t)) =
      (fun j => t ^ 3 * gradCubicOne i θ a b c j) := by
  constructor
  · rw [quadratic_differential_change]
    have hf' : quadricOne r a 0 c = 0 := hf
    simp [hf']
  · rw [cubic_differential_change i θ a b c t ht]
    simp [hh]

theorem coordinateJacobian_det (a c t : R) :
    (coordinateJacobian a c t).det = -t ^ 4 := by
  simp [coordinateJacobian, Matrix.det_fin_three]
  ring

/-- The determinant of the two-equation conormal change. -/
def conormalJacobian (t : R) : Matrix (Fin 2) (Fin 2) R :=
  !![t ^ 2, 0; 0, t ^ 3]

theorem conormalJacobian_det (t : R) : (conormalJacobian t).det = t ^ 5 := by
  simp [conormalJacobian, Matrix.det_fin_two]
  ring

/-- Coordinate signs from deleting projective coordinates 1 and 2 differ.
After including them, the adjunction transition is +b, not -b or b^(-1). -/
theorem oriented_adjunction_transition (a c : R) (b : Rˣ) :
    -(coordinateJacobian a c (↑(b⁻¹) : R)).det =
      (b : R) * (conormalJacobian (↑(b⁻¹) : R)).det := by
  rw [coordinateJacobian_det, conormalJacobian_det, neg_neg]
  have hb : (b : R) * (↑(b⁻¹) : R) = 1 := b.mul_inv
  linear_combination -((↑(b⁻¹) : R) ^ 4) * hb

end Algebra

/-! The gradient rows are the actual partial derivatives of the two
polynomials used to construct the quotient rings. -/

theorem firstQuadric_gradient (r : ℂ) :
    (fun j : Fin 3 => pderiv j (firstQuadric r)) =
      gradQuadricOne (C r) (X 0) := by
  funext j
  fin_cases j <;>
    simp [firstQuadric, quadricOne, gradQuadricOne, pderiv_mul, pderiv_pow] <;> ring

theorem firstCubic_gradient (θ : ℂ) :
    (fun j : Fin 3 => pderiv j (firstCubic θ)) =
      gradCubicOne (C Complex.I) (C θ) (X 0) (X 1) (X 2) := by
  funext j
  fin_cases j <;>
    simp [firstCubic, cubicOne, gradCubicOne, pderiv_mul, pderiv_pow] <;> ring

theorem secondQuadric_gradient (r : ℂ) :
    (fun j : Fin 3 => pderiv j (secondQuadric r)) =
      gradQuadricTwo (C r) (X 0) (X 1) (X 2) := by
  funext j
  fin_cases j <;>
    simp [secondQuadric, quadricTwo, gradQuadricTwo, pderiv_mul, pderiv_pow] <;> ring

theorem secondCubic_gradient (θ : ℂ) :
    (fun j : Fin 3 => pderiv j (secondCubic θ)) =
      gradCubicTwo (C Complex.I) (C θ) (X 0) (X 1) (X 2) := by
  funext j
  fin_cases j <;>
    simp [secondCubic, cubicTwo, gradCubicTwo, pderiv_mul, pderiv_pow] <;> ring

end CycleQ2GeometricAdjunctionOverlap

end
