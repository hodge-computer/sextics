import Proposal.ContactRationalPolynomial
import Proposal.NonsingularAlgebraicRoot

/-!
# The actual contact point is defined over a number field

The contact point supplied by the closed analytic certificate satisfies the
actual square polynomial system over the rationals and has invertible
Jacobian.  Therefore its coordinates generate a finite extension of the
rationals.  The exact weighted norm identity is retained in the conclusion.

This proves algebraicity of the contact point at lambda = 1.  It does not
construct a relative rational primitive, a global family, or a certificate
for the original sextic.
-/

noncomputable section

namespace ContactCubicAlgebraic

open ContactCubicData ContactPolynomialBounds ContactRationalPolynomial
open NonsingularAlgebraicRoot Metric

set_option backward.isDefEq.respectTransparency false

theorem finite_contact_coordinate_field (x : Space 44)
    (hroot : ∀ i, poly (polynomials i) x = 0)
    (hregular : Function.Bijective (systemDeriv polynomials x)) :
    FiniteDimensional ℚ (coordinateField (K := ℚ) x) :=
  finite_coordinateField rationalSystem x (rationalSystem_zero x hroot)
    (rationalSystem_det_ne_zero x hregular)

theorem contact_coordinates_algebraic (x : Space 44)
    (hroot : ∀ i, poly (polynomials i) x = 0)
    (hregular : Function.Bijective (systemDeriv polynomials x)) :
    ∀ i, IsAlgebraic ℚ (x i) :=
  coordinate_isAlgebraic rationalSystem x (rationalSystem_zero x hroot)
    (rationalSystem_det_ne_zero x hregular)

/-- A closed existence theorem for the actual regular contact, including
algebraicity of all coordinates and finite degree of their generated field. -/
theorem regular_algebraic_contact_point_exists :
    ∃ x ∈ closedBall center radius,
      (∀ i, poly (polynomials i) x = 0) ∧
      Function.Bijective (systemDeriv polynomials x) ∧
      WeightedFiberSmoothness.weightedG =
        ContactCubicTargetBinding.firstFactor x * ContactCubicTargetBinding.secondFactor x +
        ContactCubicTargetBinding.Q2 x * ContactCubicTargetBinding.quartic x +
        (ContactCubicTargetBinding.evenCubic x + ContactCubicTargetBinding.oddCubic x) *
          (ContactCubicTargetBinding.evenCubic x - ContactCubicTargetBinding.oddCubic x) ∧
      FiniteDimensional ℚ (coordinateField (K := ℚ) x) ∧
      (∀ i, IsAlgebraic ℚ (x i)) := by
  obtain ⟨x, hx, hroot, hregular, hnorm⟩ :=
    ContactCubicExistence.regular_contact_point_exists
  exact ⟨x, hx, hroot, hregular, hnorm,
    finite_contact_coordinate_field x hroot hregular,
    contact_coordinates_algebraic x hroot hregular⟩

#print axioms regular_algebraic_contact_point_exists

end ContactCubicAlgebraic
