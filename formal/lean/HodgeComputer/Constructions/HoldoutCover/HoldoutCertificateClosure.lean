import HodgeComputer.Constructions.HoldoutCover.FiniteResidueClearing
import HodgeComputer.Constructions.HoldoutCover.HomogeneousCertificate
import HodgeComputer.Constructions.HoldoutCover.PhysicalDerivations
import HodgeComputer.Constructions.HoldoutCover.Piola

/- Source component: HoldoutCertificateClosure -/
section
/-!
The exact physical closure of the holdout construction. A residue primitive
on the actual finite common cover, together with the proved zero trace of
the fourth inverse-power deck term, supplies legal polynomial data. The
homogeneous normalization theorem then gives the unchanged certificate
predicate for the protected sextic, protected numerator, and q = 1.
-/

noncomputable section

namespace HoldoutConstruction

open scoped BigOperators

attribute [local instance] holdoutCoordinateRing_isDomain genericCommonCoverRing_isDomain
attribute [local instance] commonCoverFunctionField_finite

local instance holdoutCertificateClosure_intHoldoutFunctionFieldAlgebra : Algebra ℤ HoldoutFunctionField := Ring.toIntAlgebra _
local instance holdoutCertificateClosure_intCommonCoverFunctionFieldAlgebra : Algebra ℤ CommonCoverFunctionField := Ring.toIntAlgebra _

local instance holdoutCertificateClosure_holdoutFunctionFieldCharZero : CharZero HoldoutFunctionField :=
  charZero_of_injective_ringHom (f := algebraMap ℂ HoldoutFunctionField)
    (algebraMap ℂ HoldoutFunctionField).injective

local instance holdoutCertificateClosure_commonCoverFunctionFieldCharZero : CharZero CommonCoverFunctionField :=
  charZero_of_injective_ringHom (f := algebraMap ℂ CommonCoverFunctionField)
    (algebraMap ℂ CommonCoverFunctionField).injective

def physicalNormal : HoldoutFunctionField :=
  physicalResidueMap (integerPartial 0 holdoutSextic)

def physicalNormalSource : HoldoutFunctionField :=
  (physicalResidueMap (integerPartial 0 holdoutSource) * physicalNormal -
    physicalResidueMap holdoutSource *
      physicalResidueMap (integerPartial 0 (integerPartial 0 holdoutSextic))) /
        physicalNormal^2

private theorem physical_normal_source_trace
    (T : CommonCoverFunctionField)
    (hT : Algebra.normalizedTrace HoldoutFunctionField CommonCoverFunctionField
      ((T^4)⁻¹) = 0) (r c : HoldoutFunctionField) :
    Algebra.normalizedTrace HoldoutFunctionField CommonCoverFunctionField
      (algebraMap HoldoutFunctionField CommonCoverFunctionField r *
        (1 - algebraMap HoldoutFunctionField CommonCoverFunctionField c * (T^4)⁻¹)) = r := by
  have hlin : Algebra.normalizedTrace HoldoutFunctionField CommonCoverFunctionField
      (algebraMap HoldoutFunctionField CommonCoverFunctionField r *
        algebraMap HoldoutFunctionField CommonCoverFunctionField c * (T^4)⁻¹) = 0 := by
    have heq : algebraMap HoldoutFunctionField CommonCoverFunctionField r *
        algebraMap HoldoutFunctionField CommonCoverFunctionField c * (T^4)⁻¹ =
          (r*c) • (T^4)⁻¹ := by
      simp only [Algebra.smul_def, map_mul]
    rw [heq, map_smul, hT, smul_zero]
  rw [mul_sub, mul_one, ← mul_assoc, map_sub,
    Algebra.normalizedTrace_algebraMap_apply_eq_self, hlin, sub_zero]

/-- All physical denominator, homogeneity, and exact certificate obligations
follow from the concrete finite-cover residue equation and its deck trace.
The two hypotheses here are supplied by the cover transport construction. -/
theorem holdout_hasCertificate_of_cover_residue
    (T : CommonCoverFunctionField)
    (hT : Algebra.normalizedTrace HoldoutFunctionField CommonCoverFunctionField
      ((T^4)⁻¹) = 0)
    (w : Fin 5 → CommonCoverFunctionField)
    (equation :
      algebraMap HoldoutFunctionField CommonCoverFunctionField physicalNormalSource *
        (1 - algebraMap HoldoutFunctionField CommonCoverFunctionField
          (physicalResidueMap (MvPolynomial.X 4)^4) * (T^4)⁻¹) +
      residueDivergence
        (fun i => extendFiniteDerivation (L := CommonCoverFunctionField) (physicalTangent i))
        (algebraMap HoldoutFunctionField CommonCoverFunctionField physicalNormal) w = 0) :
    HodgeComputer.HasCertificate holdoutSextic holdoutSource 1 := by
  have hi : (Complex.I : ℂ)^6 = -1 := by
    rw [show (6 : ℕ) = 2*3 by decide, pow_mul, Complex.I_sq]
    norm_num
  have heq :
      algebraMap HoldoutFunctionField CommonCoverFunctionField physicalNormalSource *
        (1 - algebraMap HoldoutFunctionField CommonCoverFunctionField
          (physicalResidueMap (MvPolynomial.X 4)^4) * (T^4)⁻¹) +
      ∑ i, (extendFiniteDerivation (L := CommonCoverFunctionField) (physicalTangent i) (w i) -
        w i * extendFiniteDerivation (L := CommonCoverFunctionField) (physicalTangent i)
          (algebraMap HoldoutFunctionField CommonCoverFunctionField physicalNormal) /
            algebraMap HoldoutFunctionField CommonCoverFunctionField physicalNormal) = 0 := by
    simpa only [residueDivergence, fieldDivergence, Finset.sum_sub_distrib,
      div_eq_mul_inv, Finset.sum_mul] using equation
  obtain ⟨D, N₀, N, Q, _hD, hlegal, hnormal, hdiv, _hdefect⟩ :=
    finite_residue_solution_clearing_value (K := HoldoutFunctionField)
      (L := CommonCoverFunctionField)
      physicalProjection physicalProjection_surjective
      (integerPartial 0) (fun i : Fin 5 => integerPartial i.succ)
      physicalTangent
      (fun i => extendFiniteDerivation (L := CommonCoverFunctionField) (physicalTangent i))
      holdoutSextic holdoutSource
      (algebraMap HoldoutFunctionField CommonCoverFunctionField physicalNormalSource *
        (1 - algebraMap HoldoutFunctionField CommonCoverFunctionField
          (physicalResidueMap (MvPolynomial.X 4)^4) * (T^4)⁻¹)) w
      (holdoutSextic_irreducible Complex.I hi) physicalProjection_kernel
      physical_normal_ne_zero (fun i => integerPartial_commute i.succ 0 _)
      physicalTangent_apply (fun i x => extendFiniteDerivation_apply (physicalTangent i) x)
      (physical_normal_source_trace T hT physicalNormalSource
        (physicalResidueMap (MvPolynomial.X 4)^4)) heq
  apply holdout_hasCertificate_of_normalized D (Fin.cases N₀ N) Q hlegal
  · set_option backward.isDefEq.respectTransparency false in
    simpa only [HodgeTestbed.directional, Fin.sum_univ_succ,
      Fin.cases_zero, Fin.cases_succ, integerPartial, Derivation.restrictScalars_apply,
      Derivation.coeFn_coe, mul_comm] using hnormal
  · set_option backward.isDefEq.respectTransparency false in
    simpa only [HodgeTestbed.divergenceNumerator, HodgeTestbed.divergence,
      HodgeTestbed.directional, residueDivNum, Fin.sum_univ_succ,
      Fin.cases_zero, Fin.cases_succ, integerPartial, Derivation.restrictScalars_apply,
      Derivation.coeFn_coe, mul_comm] using hdiv

end HoldoutConstruction

#print axioms HoldoutConstruction.holdout_hasCertificate_of_cover_residue
end
end
