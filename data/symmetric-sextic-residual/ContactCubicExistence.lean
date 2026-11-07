import Proposal.ContactCubicChecks
import Proposal.ContactCubicBounds

/-!
# A certified regular contact point for the actual symmetric sextic

The finite Gaussian integer computations are discharged by the Lean kernel.
The analytic theorem supplies a genuine root, rather than treating the dyadic
approximation as a root. The final identity uses the existing weightedG.

This theorem establishes a contact point and an invertible contact Jacobian.
It does not assert the rational-primitive endpoint or the Gysin comparison.
-/

noncomputable section

namespace ContactCubicExistence

open ContactCubicData ContactPolynomialBounds Metric

/-- An actual regular contact point, in the prescribed numerical neighborhood,
for the unchanged weighted fiber at lambda=1. There are no certificate or root
hypotheses: the preceding finite-check modules discharge all of them. -/
theorem regular_contact_point_exists :
    ∃ x ∈ closedBall center radius,
      (∀ i, poly (polynomials i) x = 0) ∧
      Function.Bijective (systemDeriv polynomials x) ∧
      WeightedFiberSmoothness.weightedG =
        ContactCubicTargetBinding.firstFactor x * ContactCubicTargetBinding.secondFactor x +
        ContactCubicTargetBinding.Q2 x * ContactCubicTargetBinding.quartic x +
        (ContactCubicTargetBinding.evenCubic x + ContactCubicTargetBinding.oddCubic x) *
          (ContactCubicTargetBinding.evenCubic x - ContactCubicTargetBinding.oddCubic x) :=
  ContactCubicBounds.exists_regular_target_contact rowCertificate

#print axioms regular_contact_point_exists

end ContactCubicExistence
