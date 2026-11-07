import Proposal.ContactCubicData
import Proposal.WeightedFiberSmoothness
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Exact target binding for the certified 44-variable contact system

The polynomial data in `ContactCubicData` are tied here to the unchanged
`WeightedFiberSmoothness.weightedG`, not to a new surrogate equation.
The sole input to the contact identity is that those actual 44 polynomials
vanish. The separate Banach proof supplies such a zero.
-/

noncomputable section

namespace ContactCubicTargetBinding

open MvPolynomial
open scoped BigOperators

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false

abbrev Poly := MvPolynomial (Fin 5) ℂ

def Q1 (x : Fin 44 → ℂ) : Poly :=
  C (1/4 : ℂ) * X 0 ^ 2 +
  C (x 0) * (X 1 ^ 2) +
  C (x 1) * (X 2 ^ 2) +
  C (x 2) * (X 2 * X 3) +
  C (x 3) * (X 3 ^ 2)

def Q2 (x : Fin 44 → ℂ) : Poly :=
  X 0 * X 1 +
  C (x 4) * (X 0 ^ 2) +
  C (x 5) * (X 1 ^ 2) +
  C (x 6) * (X 2 ^ 2) +
  C (x 7) * (X 2 * X 3) +
  C (x 8) * (X 3 ^ 2)

def evenCubic (x : Fin 44 → ℂ) : Poly :=
  C (x 9) * (X 0 ^ 3) +
  C (x 10) * (X 1 ^ 3) +
  C (x 11) * (X 0 * X 2 ^ 2) +
  C (x 12) * (X 0 * X 2 * X 3) +
  C (x 13) * (X 0 * X 3 ^ 2) +
  C (x 14) * (X 1 * X 2 ^ 2) +
  C (x 15) * (X 1 * X 2 * X 3) +
  C (x 16) * (X 1 * X 3 ^ 2)

def oddCubic (x : Fin 44 → ℂ) : Poly :=
  C (x 17) * (X 0 ^ 2 * X 2) +
  C (x 18) * (X 0 ^ 2 * X 3) +
  C (x 19) * (X 1 ^ 2 * X 2) +
  C (x 20) * (X 1 ^ 2 * X 3) +
  C (x 21) * (X 2 ^ 3) +
  C (x 22) * (X 2 ^ 2 * X 3) +
  C (x 23) * (X 2 * X 3 ^ 2) +
  C (x 24) * (X 3 ^ 3)

def quartic (x : Fin 44 → ℂ) : Poly :=
  C (x 25) * (X 3 ^ 4) +
  C (x 26) * (X 2 * X 3 ^ 3) +
  C (x 27) * (X 2 ^ 2 * X 3 ^ 2) +
  C (x 28) * (X 2 ^ 3 * X 3) +
  C (x 29) * (X 2 ^ 4) +
  C (x 30) * (X 1 ^ 2 * X 3 ^ 2) +
  C (x 31) * (X 1 ^ 2 * X 2 * X 3) +
  C (x 32) * (X 1 ^ 2 * X 2 ^ 2) +
  C (x 33) * (X 1 ^ 4) +
  C (x 34) * (X 0 * X 1 * X 3 ^ 2) +
  C (x 35) * (X 0 * X 1 * X 2 * X 3) +
  C (x 36) * (X 0 * X 1 * X 2 ^ 2) +
  C (x 37) * (X 0 * X 1 ^ 3) +
  C (x 38) * (X 0 ^ 2 * X 3 ^ 2) +
  C (x 39) * (X 0 ^ 2 * X 2 * X 3) +
  C (x 40) * (X 0 ^ 2 * X 2 ^ 2) +
  C (x 41) * (X 0 ^ 2 * X 1 ^ 2) +
  C (x 42) * (X 0 ^ 3 * X 1) +
  C (x 43) * (X 0 ^ 4)

def leftCore : Poly := X 0 ^ 2 + C 2 * X 0 * X 1
def rightCore : Poly := X 2 ^ 2 + C 2 * X 2 * X 3

def h2 : Poly := C (1/13 : ℂ) *
  (C 210 * (X 0 ^ 2 + X 2 ^ 2) + C 20 * leftCore + C 25 * rightCore)

def h4 : Poly := C (1/13 : ℂ) *
  (C 210 * (X 0 ^ 4 + X 2 ^ 4) - C 5 * leftCore ^ 2 -
    C 30 * leftCore * rightCore - C 10 * rightCore ^ 2)

def h6 : Poly := C (1/13 : ℂ) *
  (C 14 * X 0 ^ 6 + C 7 * X 1 ^ 6 + C 14 * X 2 ^ 6 + C 7 * X 3 ^ 6 +
    C 5 * leftCore ^ 2 * rightCore + C 10 * leftCore * rightCore ^ 2)

def firstFactor (x : Fin 44 → ℂ) : Poly := X 4 + Q1 x
def secondFactor (x : Fin 44 → ℂ) : Poly :=
  X 4 ^ 2 + (h2 - Q1 x) * X 4 + h4 - h2 * Q1 x + Q1 x ^ 2

def residual (x : Fin 44 → ℂ) : Poly :=
  Q1 x ^ 3 - h2 * Q1 x ^ 2 + h4 * Q1 x + evenCubic x ^ 2 - oddCubic x ^ 2 +
    Q2 x * quartic x - h6

def sexticMonomial : Fin 44 → Poly :=
  ![X 3 ^ 6,
    X 2 * X 3 ^ 5,
    X 2 ^ 2 * X 3 ^ 4,
    X 2 ^ 3 * X 3 ^ 3,
    X 2 ^ 4 * X 3 ^ 2,
    X 2 ^ 5 * X 3,
    X 2 ^ 6,
    X 1 ^ 2 * X 3 ^ 4,
    X 1 ^ 2 * X 2 * X 3 ^ 3,
    X 1 ^ 2 * X 2 ^ 2 * X 3 ^ 2,
    X 1 ^ 2 * X 2 ^ 3 * X 3,
    X 1 ^ 2 * X 2 ^ 4,
    X 1 ^ 4 * X 3 ^ 2,
    X 1 ^ 4 * X 2 * X 3,
    X 1 ^ 4 * X 2 ^ 2,
    X 1 ^ 6,
    X 0 * X 1 * X 3 ^ 4,
    X 0 * X 1 * X 2 * X 3 ^ 3,
    X 0 * X 1 * X 2 ^ 2 * X 3 ^ 2,
    X 0 * X 1 * X 2 ^ 3 * X 3,
    X 0 * X 1 * X 2 ^ 4,
    X 0 * X 1 ^ 3 * X 3 ^ 2,
    X 0 * X 1 ^ 3 * X 2 * X 3,
    X 0 * X 1 ^ 3 * X 2 ^ 2,
    X 0 * X 1 ^ 5,
    X 0 ^ 2 * X 3 ^ 4,
    X 0 ^ 2 * X 2 * X 3 ^ 3,
    X 0 ^ 2 * X 2 ^ 2 * X 3 ^ 2,
    X 0 ^ 2 * X 2 ^ 3 * X 3,
    X 0 ^ 2 * X 2 ^ 4,
    X 0 ^ 2 * X 1 ^ 2 * X 3 ^ 2,
    X 0 ^ 2 * X 1 ^ 2 * X 2 * X 3,
    X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 2,
    X 0 ^ 2 * X 1 ^ 4,
    X 0 ^ 3 * X 1 * X 3 ^ 2,
    X 0 ^ 3 * X 1 * X 2 * X 3,
    X 0 ^ 3 * X 1 * X 2 ^ 2,
    X 0 ^ 3 * X 1 ^ 3,
    X 0 ^ 4 * X 3 ^ 2,
    X 0 ^ 4 * X 2 * X 3,
    X 0 ^ 4 * X 2 ^ 2,
    X 0 ^ 4 * X 1 ^ 2,
    X 0 ^ 5 * X 1,
    X 0 ^ 6]

theorem weightedG_eq_cubic :
    WeightedFiberSmoothness.weightedG = X 4 ^ 3 + h2 * X 4 ^ 2 + h4 * X 4 + h6 := by
  apply MvPolynomial.funext
  intro y
  simp [WeightedFiberSmoothness.weightedG, WeightedFiberSmoothness.integerWeighted,
    WeightedFiberSmoothness.leftQuadric, WeightedFiberSmoothness.rightQuadric,
    h2, h4, h6, leftCore, rightCore]
  ring

/-- The exact 832-cleared coefficient identity for all 44 saved equations. -/
theorem residual_expansion (x : Fin 44 → ℂ) :
    (∑ i : Fin 44, C (ContactPolynomialBounds.poly (ContactCubicData.polynomials i) x) *
      sexticMonomial i) = C (832 : ℂ) * residual x := by
  apply MvPolynomial.funext
  intro y
  norm_num [Fin.sum_univ_succ, ContactCubicData.polynomials, ContactCubicData.integerPolys,
    ContactPolynomialBounds.poly, ContactPolynomialBounds.monomial, sexticMonomial,
    residual, Q1, Q2, evenCubic, oddCubic, quartic, h2, h4, h6, leftCore, rightCore]
  ring

theorem residual_eq_zero (x : Fin 44 → ℂ)
    (hx : ∀ i, ContactPolynomialBounds.poly (ContactCubicData.polynomials i) x = 0) :
    residual x = 0 := by
  have h := residual_expansion x
  simp only [hx, map_zero, zero_mul, Finset.sum_const_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (by simp)

/-- A zero of the actual integer system gives an exact norm contact on the
protected weighted lambda-one fiber. -/
theorem weightedG_contact_identity (x : Fin 44 → ℂ)
    (hx : ∀ i, ContactPolynomialBounds.poly (ContactCubicData.polynomials i) x = 0) :
    WeightedFiberSmoothness.weightedG =
      firstFactor x * secondFactor x + Q2 x * quartic x +
        (evenCubic x + oddCubic x) * (evenCubic x - oddCubic x) := by
  have hz := residual_eq_zero x hx
  rw [weightedG_eq_cubic]
  dsimp [residual] at hz
  dsimp [firstFactor, secondFactor]
  linear_combination -hz

theorem weightedG_contact_evaluation (x : Fin 44 → ℂ)
    (hx : ∀ i, ContactPolynomialBounds.poly (ContactCubicData.polynomials i) x = 0)
    (y : Fin 5 → ℂ) :
    eval y WeightedFiberSmoothness.weightedG =
      eval y (firstFactor x) * eval y (secondFactor x) +
      eval y (Q2 x) * eval y (quartic x) +
      (eval y (evenCubic x) + eval y (oddCubic x)) *
        (eval y (evenCubic x) - eval y (oddCubic x)) := by
  rw [weightedG_contact_identity x hx]
  simp

#print axioms residual_expansion
#print axioms weightedG_contact_identity
#print axioms weightedG_contact_evaluation

end ContactCubicTargetBinding
