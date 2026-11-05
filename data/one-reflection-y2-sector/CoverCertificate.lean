/- Adapted for the instance `one-reflection-y2-sector` from the accepted holdout proof by `fqlx` (hodge-computer/sextics PR #128, prepared with OpenAI ChatGPT assistance); the target-specific source, companion and trace data are replaced, all other modules are unchanged. Adaptation prepared with Claude Code assistance for `DiamondJM`. -/
import Proposal.CoverDeckField
import Proposal.CoverQuotientCompatibility
import Proposal.CoverSourceBinding
import Proposal.HoldoutCertificateClosure
import Proposal.ResiduePiolaPullback

/- Source component: CoverCertificate -/
section
/-!
Complete algebraic transport from a residue primitive for the positive
weighted-quotient numerator to the exact holdout certificate. The common
field, coordinate maps, inverse Jacobian, deck transformation, trace
identity, denominator clearing, and homogeneity normalization used here
have all been constructed in the imported proof modules. Prepared with
OpenAI ChatGPT assistance for a contribution through GitHub account fqlx.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace HoldoutConstruction

private theorem residue_source_map_append_zero
    {R K : Type*} [Field R] [Field K] {n : ℕ}
    (φ : R →+* K)
    (D : Fin n → Derivation ℤ R R) (E : Fin (n+1) → Derivation ℤ K K)
    (compatible : ∀ i x, E i.castSucc (φ x) = φ (D i x))
    (g r : R) (w : Fin n → R)
    (equation : r + residueDivergence D g w = 0) :
    φ r + residueDivergence E (φ g) (Fin.lastCases 0 (fun i => φ (w i))) = 0 := by
  rw [residueDivergence_append_zero,
    residueDivergence_map φ D (fun i => E i.castSucc) compatible g w,
    ← map_add, equation, map_zero]

attribute [local instance] fermatCurve_adjoinRoot_isDomain fermat_base_charZero
attribute [local instance] holdoutCoordinateRing_isDomain genericCommonCoverRing_isDomain
attribute [local instance] quotient_adjoinRoot_isDomain commonCoverFunctionField_finite

attribute [local irreducible] quotientCoverFieldMap quotientTangent coverQuotientTangent

local instance coverCertificate_intHoldoutFunctionFieldAlgebra : Algebra ℤ HoldoutFunctionField := Ring.toIntAlgebra _
local instance coverCertificate_intCommonCoverFunctionFieldAlgebra : Algebra ℤ CommonCoverFunctionField := Ring.toIntAlgebra _
local instance coverCertificate_intGenericQuotientFieldAlgebra : Algebra ℤ GenericQuotientField := Ring.toIntAlgebra _

local instance coverCertificate_holdoutFunctionFieldCharZero : CharZero HoldoutFunctionField :=
  charZero_of_injective_ringHom (f := algebraMap ℂ HoldoutFunctionField)
    (algebraMap ℂ HoldoutFunctionField).injective

local instance coverCertificate_commonCoverFunctionFieldCharZero : CharZero CommonCoverFunctionField :=
  charZero_of_injective_ringHom (f := algebraMap ℂ CommonCoverFunctionField)
    (algebraMap ℂ CommonCoverFunctionField).injective

local notation "ρq" => quotientResidueMap (genericBaseAlpha ℂ) (genericBaseAlpha ℂ)
local notation "G" => weightedHypersurface (genericBaseAlpha ℂ) (genericBaseAlpha ℂ)

def coverQuotientNormal : GenericQuotientField := ρq (integerPartial 0 G)

def coverQuotientNormalSource : GenericQuotientField :=
  (ρq (integerPartial 0 coverQuotientSource)*coverQuotientNormal -
    ρq coverQuotientSource*ρq (integerPartial 0 (integerPartial 0 G))) /
      coverQuotientNormal^2

/-- An actual quotient residue primitive gives the exact certificate for
the unchanged physical sextic, numerator, and pole index. -/
theorem holdout_hasCertificate_of_quotient_residue
    (wq : Fin 4 → GenericQuotientField)
    (hq : coverQuotientNormalSource +
      residueDivergence (quotientTangent (genericBaseAlpha ℂ) (genericBaseAlpha ℂ))
        coverQuotientNormal wq = 0) :
    HodgeComputer.HasCertificate holdoutSextic holdoutSource 1 := by
  let w : Fin 5 → CommonCoverFunctionField :=
    Fin.lastCases 0 (fun i => quotientCoverFieldMap (wq i))
  let v : Fin 5 → CommonCoverFunctionField :=
    fun i => actualCoverJacobian.det*(inverseCoverJacobian.mulVec w) i
  have hmap : quotientCoverFieldMap coverQuotientNormalSource +
      residueDivergence coverQuotientTangent
        (quotientCoverFieldMap coverQuotientNormal) w = 0 := by
    exact residue_source_map_append_zero
      (R := GenericQuotientField) (K := CommonCoverFunctionField) (n := 4)
      quotientCoverFieldMap
      (quotientTangent (genericBaseAlpha ℂ) (genericBaseAlpha ℂ)) coverQuotientTangent
      coverQuotientTangent_compatible
      coverQuotientNormal coverQuotientNormalSource wq hq
  have hp := residue_solution_piola_pullback coverPhysicalTangent coverQuotientTangent
    actualCoverJacobian inverseCoverJacobian actualCoverJacobian_mul_inverse
    inverseCoverJacobian_mul_actual actualCoverJacobian_det_ne_zero
    coverQuotientTangent_apply actualCoverJacobian_mixed
    (quotientCoverFieldMap coverQuotientNormal)
    (quotientCoverFieldMap coverQuotientNormalSource) w hmap
  have hs : actualCoverJacobian.det*quotientCoverFieldMap coverQuotientNormalSource =
      physicalCoverFieldMap physicalNormalSource -
        physicalCoverFieldMap physicalCompanionNormalSource * (coverT^2)⁻¹ := by
    rw [actualCoverJacobian_det]
    simpa only [coverQuotientNormalSource, coverQuotientNormal,
      physicalNormalSource, physicalCompanionNormalSource, physicalNormal] using
        cover_normal_source_binding
  have hg : quotientCoverFieldMap coverQuotientNormal =
      physicalCoverFieldMap physicalNormal := cover_normal_binding
  apply holdout_hasCertificate_of_cover_residue ((coverT^2)⁻¹) commonCover_trace_inverse_square v
  change physicalCoverFieldMap physicalNormalSource -
      physicalCoverFieldMap physicalCompanionNormalSource * (coverT^2)⁻¹ +
    residueDivergence coverPhysicalTangent (physicalCoverFieldMap physicalNormal) v = 0
  rw [← hs, ← hg]
  exact hp

/-- This equivalent source convention matches the polynomial conic's
residue-divergence theorem directly. -/
theorem holdout_hasCertificate_of_quotient_divergence
    (wq : Fin 4 → GenericQuotientField)
    (hq : residueDivergence
      (quotientTangent (genericBaseAlpha ℂ) (genericBaseAlpha ℂ))
      (ρq (integerPartial 0 G)) wq =
        -(ρq (integerPartial 0 coverQuotientSource)/ρq (integerPartial 0 G) -
          ρq coverQuotientSource*ρq (integerPartial 0 (integerPartial 0 G)) /
            (ρq (integerPartial 0 G))^2)) :
    HodgeComputer.HasCertificate holdoutSextic holdoutSource 1 := by
  apply holdout_hasCertificate_of_quotient_residue wq
  change coverQuotientNormalSource +
    residueDivergence (quotientTangent (genericBaseAlpha ℂ) (genericBaseAlpha ℂ))
      (ρq (integerPartial 0 G)) wq = 0
  rw [hq]
  unfold coverQuotientNormalSource coverQuotientNormal
  field_simp [quotient_normal_ne_zero (genericBaseAlpha ℂ) (genericBaseAlpha ℂ)]
  ring

end HoldoutConstruction

#print axioms HoldoutConstruction.holdout_hasCertificate_of_quotient_residue
#print axioms HoldoutConstruction.holdout_hasCertificate_of_quotient_divergence
end
end
