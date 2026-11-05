import HodgeTarget
import Proposal.DeformedCoverCompatibility
import Proposal.DeformedSourceBinding
import Proposal.DeformedDeck
import Proposal.DeformedCertificateClosure
import HodgeComputer.Constructions.HoldoutCover.ResiduePiolaPullback

/-!
The exact holdout-ternary-deformation certificate. A nonsingular conic
incidence supplies a polynomial-family primitive on the weighted quotient;
Piola transport, the deck trace and legal homogeneous denominator clearing
then give the protected existential certificate. The reusable transport,
trace and clearing machinery is due to fqlx and the credited mathlib
contributors. The new incidence and all deformed target bindings are
proved in the local helpers. Prepared with OpenAI Codex assistance for
hodgepodgeconjecture. See solution.md for the full mathematical argument.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
namespace DeformedCover
open HoldoutConstruction
open DeformedConic (BaseField TargetField targetResidueMap targetTangent quotientEquation)
local instance solution_local_1 : Algebra ℤ TargetField := Ring.toIntAlgebra _
local instance solution_local_2 : Algebra ℤ PhysicalField := Ring.toIntAlgebra _
local instance solution_local_3 : Algebra ℤ CoverField := Ring.toIntAlgebra _
local instance solution_local_4 : Module.Finite PhysicalField CoverField := coverField_physicalFinite
local instance solution_local_5 : Algebra.IsIntegral PhysicalField CoverField := Algebra.IsIntegral.of_finite PhysicalField CoverField

theorem deformed_hasCertificate :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.A 1 := by
  obtain ⟨wq,hq⟩ := DeformedConic.quotient_residue_solution coverQuotientSource
  let g : TargetField := targetResidueMap (integerPartial 0 quotientEquation)
  let r : TargetField :=
    (targetResidueMap (integerPartial 0 coverQuotientSource)*g-
      targetResidueMap coverQuotientSource*
        targetResidueMap (integerPartial 0 (integerPartial 0 quotientEquation)))/g^2
  have hqr : r+residueDivergence targetTangent g wq=0 := by
    rw [hq]
    dsimp [r,g]
    field_simp [DeformedConic.target_normal_ne_zero]
    ring
  let w : Fin 5 → CoverField := Fin.lastCases 0 (fun i => quotientFieldMap (wq i))
  let v : Fin 5 → CoverField := fun i => actualCoverJacobian.det*(inverseCoverJacobian.mulVec w) i
  have hmap : quotientFieldMap r+
      residueDivergence coverQuotientTangent (quotientFieldMap g) w=0 := by
    rw [residueDivergence_append_zero,
      residueDivergence_map quotientFieldMap targetTangent (fun i => coverQuotientTangent i.castSucc)
        coverQuotientTangent_compatible g wq,← map_add,hqr,map_zero]
  have hp := residue_solution_piola_pullback coverPhysicalTangent coverQuotientTangent
    actualCoverJacobian inverseCoverJacobian actualCoverJacobian_mul_inverse
    inverseCoverJacobian_mul_actual actualCoverJacobian_det_ne_zero
    coverQuotientTangent_apply actualCoverJacobian_mixed (quotientFieldMap g) (quotientFieldMap r) w hmap
  have hs : actualCoverJacobian.det*quotientFieldMap r=
      physicalFieldMap physicalNormalSource*
        (1-physicalFieldMap (physicalResidueMap (MvPolynomial.X 4)^4)*(coverT^4)⁻¹) := by
    rw [actualCoverJacobian_det]
    simpa only [r,g,physicalNormalSource,physicalNormal,map_pow] using cover_normal_source_binding
  have hg : quotientFieldMap g=physicalFieldMap physicalNormal := cover_normal_binding
  apply hasCertificate_of_cover_residue coverT cover_trace_inverse_fourth v
  change physicalFieldMap physicalNormalSource*
      (1-physicalFieldMap (physicalResidueMap (MvPolynomial.X 4)^4)*(coverT^4)⁻¹)+
    residueDivergence coverPhysicalTangent (physicalFieldMap physicalNormal) v=0
  rw [← hs,← hg]
  exact hp
end DeformedCover

theorem Submission.certificate :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q :=
  DeformedCover.deformed_hasCertificate

#print axioms Submission.certificate
