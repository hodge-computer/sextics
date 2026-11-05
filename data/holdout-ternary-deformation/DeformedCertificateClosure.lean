import Proposal.PhysicalModel
import HodgeComputer.Constructions.HoldoutCover.FiniteResidueClearing
import HodgeComputer.Constructions.HoldoutCover.HomogeneousCertificate
import HodgeComputer.Constructions.HoldoutCover.Piola

/-!
Legal denominator clearing and homogeneous extraction for the protected
sextic and numerator. Applies fqlx's shared finite-residue clearing and
homogeneous certificate theorems to the new physical model. Prepared
with OpenAI Codex assistance for hodgepodgeconjecture.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
namespace DeformedCover
open HoldoutConstruction MvPolynomial
open scoped BigOperators
local instance deformedCertificateClosure_local_1 : Algebra ℤ PhysicalField := Ring.toIntAlgebra _
local instance deformedCertificateClosure_local_2 : Algebra ℤ CoverField := Ring.toIntAlgebra _
local instance deformedCertificateClosure_local_3 : Module.Finite PhysicalField CoverField := coverField_physicalFinite
local instance deformedCertificateClosure_local_4 : Algebra.IsIntegral PhysicalField CoverField := Algebra.IsIntegral.of_finite PhysicalField CoverField

lemma protected_isHomogeneous : HodgeSubmission.F.IsHomogeneous 6 := by
  have hp (i : Fin 6) : (X (R := ℂ) i^6).IsHomogeneous 6 := isHomogeneous_X_pow i 6
  have hc (i j k l : Fin 6) :
      (X (R := ℂ) i^3*X j*X k*X l).IsHomogeneous 6 :=
    (((isHomogeneous_X_pow i 3).mul (isHomogeneous_X ℂ j)).mul
      (isHomogeneous_X ℂ k)).mul (isHomogeneous_X ℂ l)
  have hd (i j : Fin 6) (c : ℂ) : (X (R := ℂ) i^5*X j*C c).IsHomogeneous 6 :=
    ((isHomogeneous_X_pow i 5).mul (isHomogeneous_X ℂ j)).mul (isHomogeneous_C (Fin 6) c)
  have hd' (i j : Fin 6) (c : ℂ) : (X (R := ℂ) i*X j^5*C c).IsHomogeneous 6 :=
    ((isHomogeneous_X ℂ i).mul (isHomogeneous_X_pow j 5)).mul (isHomogeneous_C (Fin 6) c)
  exact ((((((((((hp 0).add (hd 0 1 (1/14))).add (hc 0 1 3 4)).add
    (hd' 0 2 (1/14))).add (hp 1)).add (hd 1 2 (1/7))).add (hc 1 2 4 5)).add
    (hp 2)).add (hp 3)).add (hp 4)).add (hp 5)
lemma protected_source_isHomogeneous : HodgeSubmission.A.IsHomogeneous 6 :=
  (isHomogeneous_X_pow (0 : Fin 6) 3).mul (isHomogeneous_X_pow (3 : Fin 6) 3)

def physicalNormal : PhysicalField :=
  physicalResidueMap (integerPartial 0 HodgeSubmission.F)

def physicalNormalSource : PhysicalField :=
  (physicalResidueMap (integerPartial 0 HodgeSubmission.A) * physicalNormal -
    physicalResidueMap HodgeSubmission.A *
      physicalResidueMap (integerPartial 0 (integerPartial 0 HodgeSubmission.F))) /
        physicalNormal^2

private theorem physical_normal_source_trace
    (T : CoverField)
    (hT : Algebra.normalizedTrace PhysicalField CoverField
      ((T^4)⁻¹) = 0) (r c : PhysicalField) :
    Algebra.normalizedTrace PhysicalField CoverField
      (algebraMap PhysicalField CoverField r *
        (1 - algebraMap PhysicalField CoverField c * (T^4)⁻¹)) = r := by
  have hlin : Algebra.normalizedTrace PhysicalField CoverField
      (algebraMap PhysicalField CoverField r *
        algebraMap PhysicalField CoverField c * (T^4)⁻¹) = 0 := by
    have heq : algebraMap PhysicalField CoverField r *
        algebraMap PhysicalField CoverField c * (T^4)⁻¹ =
          (r*c) • (T^4)⁻¹ := by
      simp only [Algebra.smul_def, map_mul]
    rw [heq, map_smul, hT, smul_zero]
  rw [mul_sub, mul_one, ← mul_assoc, map_sub,
    Algebra.normalizedTrace_algebraMap_apply_eq_self, hlin, sub_zero]

/-- All physical denominator, homogeneity, and exact certificate obligations
follow from the concrete finite-cover residue equation and its deck trace.
The two hypotheses here are supplied by the cover transport construction. -/
theorem hasCertificate_of_cover_residue
    (T : CoverField)
    (hT : Algebra.normalizedTrace PhysicalField CoverField
      ((T^4)⁻¹) = 0)
    (w : Fin 5 → CoverField)
    (equation :
      algebraMap PhysicalField CoverField physicalNormalSource *
        (1 - algebraMap PhysicalField CoverField
          (physicalResidueMap (MvPolynomial.X 4)^4) * (T^4)⁻¹) +
      residueDivergence
        (fun i => extendFiniteDerivation (L := CoverField) (physicalTangent i))
        (algebraMap PhysicalField CoverField physicalNormal) w = 0) :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.A 1 := by
  have heq :
      algebraMap PhysicalField CoverField physicalNormalSource *
        (1 - algebraMap PhysicalField CoverField
          (physicalResidueMap (MvPolynomial.X 4)^4) * (T^4)⁻¹) +
      ∑ i, (extendFiniteDerivation (L := CoverField) (physicalTangent i) (w i) -
        w i * extendFiniteDerivation (L := CoverField) (physicalTangent i)
          (algebraMap PhysicalField CoverField physicalNormal) /
            algebraMap PhysicalField CoverField physicalNormal) = 0 := by
    simpa only [residueDivergence, fieldDivergence, Finset.sum_sub_distrib,
      div_eq_mul_inv, Finset.sum_mul] using equation
  obtain ⟨D, N₀, N, Q, _hD, hlegal, hnormal, hdiv, _hdefect⟩ :=
    finite_residue_solution_clearing_value (K := PhysicalField)
      (L := CoverField)
      physicalProjection physicalProjection_surjective
      (integerPartial 0) (fun i : Fin 5 => integerPartial i.succ)
      physicalTangent
      (fun i => extendFiniteDerivation (L := CoverField) (physicalTangent i))
      HodgeSubmission.F HodgeSubmission.A
      (algebraMap PhysicalField CoverField physicalNormalSource *
        (1 - algebraMap PhysicalField CoverField
          (physicalResidueMap (MvPolynomial.X 4)^4) * (T^4)⁻¹)) w
      protected_irreducible physicalProjection_kernel
      physical_normal_ne_zero (fun i => integerPartial_commute i.succ 0 _)
      physicalTangent_apply (fun i x => extendFiniteDerivation_apply (physicalTangent i) x)
      (physical_normal_source_trace T hT physicalNormalSource
        (physicalResidueMap (MvPolynomial.X 4)^4)) heq
  apply hasCertificate_of_normalized HodgeSubmission.F HodgeSubmission.A D (Fin.cases N₀ N) Q
    protected_isHomogeneous protected_source_isHomogeneous protected_irreducible.prime hlegal
    ?_ ?_ 0 protected_not_dvd_normal
  · set_option backward.isDefEq.respectTransparency false in
    simpa only [HodgeTestbed.directional, Fin.sum_univ_succ,
      Fin.cases_zero, Fin.cases_succ, integerPartial, Derivation.restrictScalars_apply,
      Derivation.coeFn_coe, mul_comm] using hnormal
  · set_option backward.isDefEq.respectTransparency false in
    simpa only [HodgeTestbed.divergenceNumerator, HodgeTestbed.divergence,
      HodgeTestbed.directional, residueDivNum, Fin.sum_univ_succ,
      Fin.cases_zero, Fin.cases_succ, integerPartial, Derivation.restrictScalars_apply,
      Derivation.coeFn_coe, mul_comm] using hdiv

end DeformedCover
#print axioms DeformedCover.hasCertificate_of_cover_residue
