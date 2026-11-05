import HodgeTarget
import Proposal.BundleAssembly

/-! Exact binding to the generated protected holdout-bundle target. -/

noncomputable section
namespace HoldoutBundle
open HoldoutConstruction

theorem protected_polynomial : HodgeSubmission.F = holdoutSextic := by
  unfold HodgeSubmission.F holdoutSextic
  ring

theorem protected_source : HodgeSubmission.A = Abundle := by
  unfold HodgeSubmission.A Abundle Astar holdoutSource
  ring

theorem protected_pole : HodgeSubmission.q = 1 := rfl

theorem protected_certificate_of_bundle
    (h : HodgeComputer.HasCertificate holdoutSextic Abundle 1) :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q := by
  rw [protected_polynomial, protected_source, protected_pole]
  exact h

end HoldoutBundle

#print axioms HoldoutBundle.protected_certificate_of_bundle
