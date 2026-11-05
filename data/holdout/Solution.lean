import HodgeTarget
import Proposal.ConicResidue
import Proposal.CoverCertificate

/- Source component: Solution -/
section
/-!
The exact protected holdout statement. The moving-conic construction solves
the quotient residue equation for the positive source selected by the
Fermat cover. The concrete cover transport, deck trace, legal clearing, and
finite homogeneous extraction then supply the required certificate.
-/

noncomputable section

open HoldoutConstruction HoldoutConicIncidence

theorem Submission.certificate :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A := by
  change HodgeComputer.HasCertificate holdoutSextic 1 holdoutSource
  obtain ⟨p⟩ := HoldoutConic.exists_seed
  obtain ⟨w, hw⟩ := conic_target_residue_solution p coverQuotientSource
  exact holdout_hasCertificate_of_quotient_divergence w hw

#print axioms Submission.certificate
end
end
