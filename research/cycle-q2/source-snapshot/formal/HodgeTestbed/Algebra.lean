import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic.Ring

/-!
# Polynomial identities for rational vector-field certificates

All identities hold over an arbitrary commutative coefficient ring and finite variable type.
They concern polynomial numerators: no fraction field or denominator hypothesis is hidden here.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeTestbed

open MvPolynomial
open scoped BigOperators

variable {σ R : Type*} [Fintype σ] [CommRing R]

/-- `dP(N)`, the polynomial directional derivative of `P` along `N`. -/
def directional (P : MvPolynomial σ R) (N : σ → MvPolynomial σ R) :
    MvPolynomial σ R := ∑ i, pderiv i P * N i

/-- The divergence of a polynomial vector field. -/
def divergence (N : σ → MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ i, pderiv i (N i)

/-- The numerator of `div(N / D)` when cleared by `D²`. -/
def divergenceNumerator (D : MvPolynomial σ R) (N : σ → MvPolynomial σ R) :
    MvPolynomial σ R := D * divergence N - directional D N

/-- The numerator of `A - dF(N/D) + F div(N/D)` after clearing by `D²`. -/
def clearedDefect (F A D : MvPolynomial σ R) (N : σ → MvPolynomial σ R) :
    MvPolynomial σ R := A * D ^ 2 - D * directional F N + F * divergenceNumerator D N

/-- The two polynomial equations of a certificate, before degree/parity/legality checks. -/
structure Equations (F A D : MvPolynomial σ R) (N : σ → MvPolynomial σ R)
    (C : MvPolynomial σ R) : Prop where
  e1 : directional F N = A * D
  e2 : divergenceNumerator D N = F * C

/-- The precise cleared game identity supplied by E1 and E2. -/
theorem Equations.clearedDefect_eq {F A D C : MvPolynomial σ R}
    {N : σ → MvPolynomial σ R} (h : Equations F A D N C) :
    clearedDefect F A D N = F ^ 2 * C := by
  unfold clearedDefect
  rw [h.e1, h.e2]
  ring

/-- Thus the cleared defect has the required factor `F²`. -/
theorem Equations.square_dvd_clearedDefect {F A D C : MvPolynomial σ R}
    {N : σ → MvPolynomial σ R} (h : Equations F A D N C) :
    F ^ 2 ∣ clearedDefect F A D N := ⟨C, h.clearedDefect_eq⟩

theorem directional_mul (P H : MvPolynomial σ R) (N : σ → MvPolynomial σ R) :
    directional P (fun i => H * N i) = H * directional P N := by
  unfold directional
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem directional_product (P H : MvPolynomial σ R) (N : σ → MvPolynomial σ R) :
    directional (H * P) N = P * directional H N + H * directional P N := by
  unfold directional
  simp only [pderiv_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

theorem divergence_mul (H : MvPolynomial σ R) (N : σ → MvPolynomial σ R) :
    divergence (fun i => H * N i) = directional H N + H * divergence N := by
  unfold divergence directional
  simp only [pderiv_mul, Finset.sum_add_distrib, Finset.mul_sum]

/-- Multiplying both `D` and `N` by `H` multiplies the divergence numerator by `H²`.
The derivatives of `H` cancel exactly. No regularity or nonzero assumption is needed. -/
theorem divergenceNumerator_mul (H D : MvPolynomial σ R)
    (N : σ → MvPolynomial σ R) :
    divergenceNumerator (H * D) (fun i => H * N i) =
      H ^ 2 * divergenceNumerator D N := by
  unfold divergenceNumerator
  rw [divergence_mul, directional_mul, directional_product]
  ring

/-- Denominator scaling preserves the equations, with residual multiplier `H² C`.
Legality of the new denominator is a separate condition in `Certificate.scale`. -/
theorem Equations.scale {F A D C : MvPolynomial σ R}
    {N : σ → MvPolynomial σ R} (h : Equations F A D N C) (H : MvPolynomial σ R) :
    Equations F A (H * D) (fun i => H * N i) (H ^ 2 * C) where
  e1 := by rw [directional_mul, h.e1]; ring
  e2 := by rw [divergenceNumerator_mul, h.e2]; ring

/-- A strict certificate is the special case with residual polynomial zero. -/
theorem strict_to_equations {F A D : MvPolynomial σ R} {N : σ → MvPolynomial σ R}
    (h1 : directional F N = A * D) (h2 : divergenceNumerator D N = 0) :
    Equations F A D N 0 := ⟨h1, by simpa using h2⟩

/-- A vector field with one polynomial component. -/
def coordinateField (j : σ) (P : MvPolynomial σ R) : σ → MvPolynomial σ R :=
by
  classical
  exact fun i => if i = j then P else 0

theorem directional_coordinateField (F P : MvPolynomial σ R) (j : σ) :
    directional F (coordinateField j P) = pderiv j F * P := by
  classical
  simp [directional, coordinateField]

theorem divergence_coordinateField (P : MvPolynomial σ R) (j : σ) :
    divergence (coordinateField j P) = pderiv j P := by
  classical
  unfold divergence coordinateField
  simp only [apply_ite, map_zero]
  simp

/-- The elementary Jacobian direction has zero divergence when its component is a
variable different from the direction. This is a control construction, not an arbitrary target. -/
theorem jacobianDirection_equations (F : MvPolynomial σ R) (j k : σ) (hjk : k ≠ j) :
    Equations F (X k * pderiv j F) 1 (coordinateField j (X k)) 0 := by
  apply strict_to_equations
  · rw [directional_coordinateField]
    ring
  · simp [divergenceNumerator, divergence_coordinateField, pderiv_X_of_ne hjk,
      directional]

end HodgeTestbed
