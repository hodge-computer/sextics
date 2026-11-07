import SymmetricPrime
import SymmetricSmoothness
import CanonicalFractionCoordinates
import RegularEulerClearing
import CertificateRegularCurrent

/-!
# The exact symmetric-sextic endpoint with automatic legal clearing

All field, coordinate, commutativity, primality, homogeneity, and normal-chart
inputs are supplied by proved theorems. The remaining hypothesis is written
in full: existence of a regular homogeneous rational current satisfying the
ordinary game identity. This file does not assert that remaining existence
claim, and does not declare an unconditional solution of the protected target.
-/

noncomputable section

namespace SymmetricRegularCurrent

open HodgeComputer HodgeTestbed HodgeTestbed.Conic
open AutomaticLegalClearing RegularEulerClearing CanonicalFractionCoordinates

abbrev K := RationalFunctionField 5
abbrev Regular := RegularRing HodgeSubmission.F

/-- The exact surviving rational-current existence statement. The localization
allows only nonzero denominators relatively prime to the protected equation. -/
def RegularGameExists : Prop :=
  ∃ (v : Fin 6 → Regular) (r : Regular),
    (∀ i, fieldAction (coordinates 5).derivative (coordinateEuler (coordinates 5))
      (regularMap (coordinates 5) HodgeSubmission.F (v i)) =
        regularMap (coordinates 5) HodgeSubmission.F (v i)) ∧
    (coordinates 5).embed HodgeSubmission.A -
        fieldAction (coordinates 5).derivative
          (fun i => regularMap (coordinates 5) HodgeSubmission.F (v i))
          ((coordinates 5).embed HodgeSubmission.F) +
        (coordinates 5).embed HodgeSubmission.F *
          fieldDivergence (coordinates 5).derivative
            (fun i => regularMap (coordinates 5) HodgeSubmission.F (v i)) =
      (coordinates 5).embed HodgeSubmission.F ^ 2 *
        regularMap (coordinates 5) HodgeSubmission.F r

/-- An existence proof suffices for the literal original target; the caller
does not supply or compute any polynomial certificate witnesses. -/
theorem certificate_of_regular_game_exists (h : RegularGameExists) :
    HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A := by
  exact hasCertificate_of_exists_regular_homogeneous_game (coordinates 5)
    HodgeSubmission.F HodgeSubmission.A SymmetricSmoothness.target_homogeneous
    SymmetricSmoothness.source_homogeneous SymmetricPrime.target_prime
    (fun i j x => coordinates_commute 5 i j x) h

/-- Conversely, every accepted certificate produces a current with exactly
these regularity, homogeneity, and ordinary-remainder properties. -/
theorem regular_game_exists_of_certificate
    (h : HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A) :
    RegularGameExists :=
  CertificateRegularCurrent.exists_regular_homogeneous_game_of_hasCertificate
    (coordinates 5) HodgeSubmission.F HodgeSubmission.A
    SymmetricSmoothness.target_homogeneous h

/-- This reduction is an equivalence for the literal protected target. It
does not impose a stronger current-existence problem than the verifier asks. -/
theorem certificate_iff_regular_game_exists :
    HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A ↔
      RegularGameExists :=
  ⟨regular_game_exists_of_certificate, certificate_of_regular_game_exists⟩

#print axioms certificate_of_regular_game_exists
#print axioms regular_game_exists_of_certificate
#print axioms certificate_iff_regular_game_exists

end SymmetricRegularCurrent
