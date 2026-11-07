import HodgeTarget
import Proposal.SymmetricPrimitiveEndpoint
import Proposal.SymmetricRegularCurrent

/-!
# Incomplete symmetric-sextic certificate

This draft uses the ordinary protected target and proposal helper layout.
Exactly two substantive proof obligations remain below. The final theorem
depends on their `sorry` placeholders and is not an accepted certificate.
-/

noncomputable section
namespace Submission

/-- Missing geometric step: identify the actual contact correspondence with
the required residue class and prove exactness in the chart function field.
The finite contact-rank calculation alone does not establish this theorem. -/
theorem relative_primitive_exists :
    Nonempty SymmetricPrimitiveEndpoint.RelativePrimitive := by
  sorry

/-- Missing transport step: assemble the legal affine clearing data into a
regular homogeneous current for the original protected sextic. -/
theorem regular_game_of_relative_primitive
    (beta : SymmetricPrimitiveEndpoint.RelativePrimitive) :
    SymmetricRegularCurrent.RegularGameExists := by
  have affine_data := SymmetricPrimitiveEndpoint.clear_relative_primitive beta
  -- The affine identities are proved; their projective transport and
  -- homogeneous assembly into RegularGameExists remain to be formalized.
  sorry

/-- Standard submission entry point, conditional on the two unfinished
lemmas above. Its transitive axioms include sorryAx until those are proved. -/
theorem certificate :
    HodgeComputer.HasCertificate
      HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A := by
  obtain ⟨beta⟩ := relative_primitive_exists
  exact SymmetricRegularCurrent.certificate_of_regular_game_exists
    (regular_game_of_relative_primitive beta)

end Submission

#print axioms Submission.certificate
