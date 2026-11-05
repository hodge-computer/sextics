/- Adapted for the instance `one-reflection-y2-sector` from the accepted holdout proof by `fqlx` (hodge-computer/sextics PR #128, prepared with OpenAI ChatGPT assistance); the target-specific source, companion and trace data are replaced, all other modules are unchanged. Adaptation prepared with Claude Code assistance for `DiamondJM`. -/
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
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q := by
  change HodgeComputer.HasCertificate holdoutSextic holdoutSource 1
  obtain ⟨p⟩ := HoldoutConic.exists_seed
  obtain ⟨w, hw⟩ := conic_target_residue_solution p coverQuotientSource
  exact holdout_hasCertificate_of_quotient_divergence w hw

#print axioms Submission.certificate
end
end
