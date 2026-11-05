import HodgeTarget
import HodgeComputer.Constructions.HoldoutCover.GeneralizedCover

/- Target specialization of fqlx's accepted PR #128, with Codex assistance
for benediamond. The shared construction and its attribution are retained. -/
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Submission
open HoldoutConstruction HoldoutGeneralization MvPolynomial

attribute [local instance] fermatCurve_adjoinRoot_isDomain fermat_base_charZero
attribute [local instance] holdoutCoordinateRing_isDomain genericCommonCoverRing_isDomain
attribute [local instance] quotient_adjoinRoot_isDomain quotient_charZero
attribute [local instance] commonCoverFunctionField_finite
local instance : CharZero CommonCoverFunctionField :=
  charZero_of_injective_ringHom (f := algebraMap ℂ CommonCoverFunctionField)
    (algebraMap ℂ CommonCoverFunctionField).injective

def target : HodgeComputer.Poly := (X 1)^3*(X 4)^3
def reflected : HodgeComputer.Poly := (X 1)^3*(X 4)
def quotientSource : MvPolynomial (Fin 5) (FermatCoefficientField ℂ) :=
  C (-(genericBaseBeta ℂ)^0/(2*(genericBaseAlpha ℂ)^5))*(X 1)^3*(X 4)

theorem target_partial : integerPartial 0 target = 0 := by
  norm_num [integerPartial_apply, target, MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_mul, Pi.single_apply, Fin.ext_iff] <;> ring
theorem reflected_partial : integerPartial 0 reflected = 0 := by
  norm_num [integerPartial_apply, reflected, MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_mul, Pi.single_apply, Fin.ext_iff] <;> ring
theorem quotient_partial : integerPartial 0 quotientSource = 0 := by
  norm_num [integerPartial_apply, quotientSource, MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_mul, Pi.single_apply, Fin.ext_iff] <;> ring

local notation "ρq" => quotientResidueMap (genericBaseAlpha ℂ) (genericBaseBeta ℂ)

theorem source_binding : actualCoverJacobian.det*quotientCoverFieldMap (ρq quotientSource) =
    physicalCoverFieldMap (physicalResidueMap target)-
      physicalCoverFieldMap (physicalResidueMap reflected)*(coverT^2) := by
  rw [actualCoverJacobian_det]
  simp only [target, reflected, quotientSource, map_mul, map_pow, map_neg, map_one, map_ofNat,
    quotientCoverFieldMap_residue_X, quotientCoverFieldMap_residue_C,
    physicalCoverFieldMap_residue_X, map_div₀]
  change (2*coverAlpha^5*(coverT^2-coverY^2)/coverT)*((-coverBeta^0/(2*coverAlpha^5))*coverX1^3*(coverY*coverT)) =
    coverX1^3*coverY^3-(coverX1^3*coverY)*(coverT^2)
  field_simp [coverAlpha_ne_zero,coverT_ne_zero] <;> ring

theorem partial_binding : actualCoverJacobian.det*quotientCoverFieldMap (ρq (integerPartial 0 quotientSource)) =
    physicalCoverFieldMap (physicalResidueMap (integerPartial 0 target))-
      physicalCoverFieldMap (physicalResidueMap (integerPartial 0 reflected))*(coverT^2) := by
  rw [quotient_partial,target_partial,reflected_partial]
  simp only [map_zero,mul_zero,zero_mul,sub_zero]

theorem certificate :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q := by
  change HodgeComputer.HasCertificate holdoutSextic target 1
  apply certificate_of_source_pair target reflected quotientSource (coverT^2)
  · simpa only [target, pow_one] using ((isHomogeneous_X_pow (R := ℂ) (1 : Fin 6) 3).mul (isHomogeneous_X_pow (R := ℂ) (4 : Fin 6) 3))
  · exact trace_square
  · exact source_binding
  · exact partial_binding

end Submission
#print axioms Submission.certificate
