import HodgeComputer.Constructions.HoldoutCover.ConicResidue
import HodgeComputer.Constructions.HoldoutCover.CoverCertificate

/-!
Target-linear extension of fqlx's accepted Fermat-cover construction (PR #128).
The geometric family, finite traces, and legal homogeneous clearing are unchanged.
This module separates the two target identities from that shared construction.
Prepared with OpenAI Codex assistance for benediamond, crediting fqlx and the
prior mathematical and formal sources acknowledged in the accepted proof.
-/

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 10000

namespace HoldoutGeneralization
open HoldoutConstruction HoldoutConicIncidence MvPolynomial
open scoped BigOperators

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
attribute [local instance] quotient_adjoinRoot_isDomain quotient_charZero
attribute [local instance] commonCoverFunctionField_finite

attribute [local irreducible] quotientCoverFieldMap quotientTangent coverQuotientTangent

local instance : CharZero HoldoutFunctionField :=
  charZero_of_injective_ringHom (f := algebraMap ℂ HoldoutFunctionField)
    (algebraMap ℂ HoldoutFunctionField).injective
local instance : CharZero CommonCoverFunctionField :=
  charZero_of_injective_ringHom (f := algebraMap ℂ CommonCoverFunctionField)
    (algebraMap ℂ CommonCoverFunctionField).injective

local notation "ρq" => quotientResidueMap (genericBaseAlpha ℂ) (genericBaseBeta ℂ)
local notation "G" => weightedHypersurface (genericBaseAlpha ℂ) (genericBaseBeta ℂ)
local notation "ρp" => physicalResidueMap

private theorem normalizedTrace_square_zero
    {K L : Type*} [Field K] [Field L] [CharZero K]
    [Algebra K L] [FiniteDimensional K L]
    (σ : L →ₐ[K] L) (zeta : K) (hzeta : zeta^2 ≠ 1)
    (T : L) (scale : σ T = algebraMap K L zeta * T) :
    Algebra.normalizedTrace K L (T^2) = 0 := by
  apply normalizedTrace_eigen_zero σ (zeta^2) hzeta (T^2)
  simp only [map_pow, scale, mul_pow]

private theorem normalizedTrace_inv_square_zero
    {K L : Type*} [Field K] [Field L] [CharZero K]
    [Algebra K L] [FiniteDimensional K L]
    (σ : L →ₐ[K] L) (zeta : K) (hzeta : zeta^2 ≠ 1)
    (T : L) (scale : σ T = algebraMap K L zeta * T) :
    Algebra.normalizedTrace K L ((T^2)⁻¹) = 0 := by
  apply normalizedTrace_eigen_zero σ ((zeta^2)⁻¹)
  · intro h
    apply hzeta
    have hi := congrArg (fun x : K => x⁻¹) h
    simpa only [inv_inv, inv_one] using hi
  · simp only [map_inv₀, map_pow, scale, mul_pow, mul_inv_rev]
    ring

private theorem nontrivial_square (z : ℂ) (hz4 : z^4 ≠ 1) :
    (algebraMap ℂ HoldoutFunctionField z)^2 ≠ 1 := by
  intro h
  have hz2 : z^2=1 := (algebraMap ℂ HoldoutFunctionField).injective
    (by simpa only [map_pow,map_one] using h)
  apply hz4
  calc
    z^4 = (z^2)^2 := by ring
    _ = 1 := by rw [hz2,one_pow]

theorem trace_square :
    Algebra.normalizedTrace HoldoutFunctionField CommonCoverFunctionField (coverT^2) = 0 := by
  obtain ⟨z,hz,hz0,hz4⟩ := exists_nontrivial_sixth_root
  exact normalizedTrace_square_zero (K := HoldoutFunctionField) (L := CommonCoverFunctionField)
    (physicalDeckAlgHom z hz hz0)
    (algebraMap ℂ HoldoutFunctionField z) (nontrivial_square z hz4)
    coverT (physicalDeckAlgHom_T z hz hz0)

theorem trace_inverse_square :
    Algebra.normalizedTrace HoldoutFunctionField CommonCoverFunctionField ((coverT^2)⁻¹) = 0 := by
  obtain ⟨z,hz,hz0,hz4⟩ := exists_nontrivial_sixth_root
  exact normalizedTrace_inv_square_zero (K := HoldoutFunctionField) (L := CommonCoverFunctionField)
    (physicalDeckAlgHom z hz hz0)
    (algebraMap ℂ HoldoutFunctionField z) (nontrivial_square z hz4)
    coverT (physicalDeckAlgHom_T z hz hz0)

def normalSource (A : HodgeComputer.Poly) : HoldoutFunctionField :=
  (ρp (integerPartial 0 A)*physicalNormal -
    ρp A*ρp (integerPartial 0 (integerPartial 0 holdoutSextic)))/physicalNormal^2

private theorem trace_difference (r s : HoldoutFunctionField) (t : CommonCoverFunctionField)
    (ht : Algebra.normalizedTrace HoldoutFunctionField CommonCoverFunctionField t = 0) :
    Algebra.normalizedTrace HoldoutFunctionField CommonCoverFunctionField
      (algebraMap HoldoutFunctionField CommonCoverFunctionField r -
       algebraMap HoldoutFunctionField CommonCoverFunctionField s*t) = r := by
  have he : algebraMap HoldoutFunctionField CommonCoverFunctionField s*t = s • t := by
    rw [Algebra.smul_def]
  rw [map_sub, Algebra.normalizedTrace_algebraMap_apply_eq_self, he,
      map_smul, ht, smul_zero, sub_zero]

local instance : Algebra ℤ HoldoutFunctionField := Ring.toIntAlgebra _
local instance : Algebra ℤ CommonCoverFunctionField := Ring.toIntAlgebra _
local instance : Algebra ℤ GenericQuotientField := Ring.toIntAlgebra _

theorem certificate_of_source_pair
    (A C : HodgeComputer.Poly)
    (B : MvPolynomial (Fin 5) (FermatCoefficientField ℂ))
    (t : CommonCoverFunctionField)
    (hA : A.IsHomogeneous 6)
    (ht : Algebra.normalizedTrace HoldoutFunctionField CommonCoverFunctionField t = 0)
    (hsource : actualCoverJacobian.det*quotientCoverFieldMap (ρq B) =
      physicalCoverFieldMap (ρp A)-physicalCoverFieldMap (ρp C)*t)
    (hpartial : actualCoverJacobian.det*quotientCoverFieldMap (ρq (integerPartial 0 B)) =
      physicalCoverFieldMap (ρp (integerPartial 0 A))-
        physicalCoverFieldMap (ρp (integerPartial 0 C))*t) :
    HodgeComputer.HasCertificate holdoutSextic A 1 := by
  obtain ⟨p⟩ := HoldoutConic.exists_seed
  obtain ⟨wq,hq⟩ : ∃ wq : Fin 4 → GenericQuotientField,
      residueDivergence (quotientTangent (genericBaseAlpha ℂ) (genericBaseBeta ℂ))
        (ρq (integerPartial 0 G)) wq =
      -(ρq (integerPartial 0 B)/ρq (integerPartial 0 G) -
        ρq B*ρq (integerPartial 0 (integerPartial 0 G))/(ρq (integerPartial 0 G))^2) := by
    exact conic_target_residue_solution p B
  let gq := ρq (integerPartial 0 G)
  let rq := (ρq (integerPartial 0 B)*gq-ρq B*ρq (integerPartial 0 (integerPartial 0 G)))/gq^2
  have hq' : rq + residueDivergence
      (quotientTangent (genericBaseAlpha ℂ) (genericBaseBeta ℂ)) gq wq = 0 := by
    rw [hq]
    dsimp [rq,gq]
    field_simp [quotient_normal_ne_zero (genericBaseAlpha ℂ) (genericBaseBeta ℂ)]
    ring
  let w : Fin 5 → CommonCoverFunctionField :=
    Fin.lastCases 0 (fun i => quotientCoverFieldMap (wq i))
  let v : Fin 5 → CommonCoverFunctionField :=
    fun i => actualCoverJacobian.det*(inverseCoverJacobian.mulVec w) i
  have hmap : quotientCoverFieldMap rq +
      residueDivergence coverQuotientTangent (quotientCoverFieldMap gq) w = 0 := by
    exact residue_source_map_append_zero
      (R := GenericQuotientField) (K := CommonCoverFunctionField) (n := 4)
      quotientCoverFieldMap
      (quotientTangent (genericBaseAlpha ℂ) (genericBaseBeta ℂ)) coverQuotientTangent
      coverQuotientTangent_compatible gq rq wq hq'
  have hp := residue_solution_piola_pullback coverPhysicalTangent coverQuotientTangent
    actualCoverJacobian inverseCoverJacobian actualCoverJacobian_mul_inverse
    inverseCoverJacobian_mul_actual actualCoverJacobian_det_ne_zero
    coverQuotientTangent_apply actualCoverJacobian_mixed
    (quotientCoverFieldMap gq) (quotientCoverFieldMap rq) w hmap
  have hs : actualCoverJacobian.det*quotientCoverFieldMap rq =
      physicalCoverFieldMap (normalSource A)-physicalCoverFieldMap (normalSource C)*t := by
    dsimp only [rq,gq,normalSource,physicalNormal]
    simp only [map_div₀, map_sub, map_mul, map_pow]
    rw [cover_normal_binding, cover_second_normal_binding]
    calc
      _ = ((actualCoverJacobian.det*quotientCoverFieldMap (ρq (integerPartial 0 B))) *
          physicalCoverFieldMap (ρp (integerPartial 0 holdoutSextic)) -
          (actualCoverJacobian.det*quotientCoverFieldMap (ρq B)) *
          physicalCoverFieldMap (ρp (integerPartial 0 (integerPartial 0 holdoutSextic)))) /
          physicalCoverFieldMap (ρp (integerPartial 0 holdoutSextic))^2 := by ring
      _ = _ := by rw [hpartial,hsource]; ring
  have hg : quotientCoverFieldMap gq =
      physicalCoverFieldMap physicalNormal := cover_normal_binding
  rw [hs,hg] at hp
  have hi : (Complex.I : ℂ)^6 = -1 := by
    rw [show (6 : ℕ)=2*3 by decide,pow_mul,Complex.I_sq]
    norm_num
  have heq :
      algebraMap HoldoutFunctionField CommonCoverFunctionField (normalSource A) -
      algebraMap HoldoutFunctionField CommonCoverFunctionField (normalSource C)*t +
      ∑ i, (extendFiniteDerivation (L := CommonCoverFunctionField) (physicalTangent i) (v i) -
        v i * extendFiniteDerivation (L := CommonCoverFunctionField) (physicalTangent i)
          (algebraMap HoldoutFunctionField CommonCoverFunctionField physicalNormal) /
            algebraMap HoldoutFunctionField CommonCoverFunctionField physicalNormal) = 0 := by
    change physicalCoverFieldMap (normalSource A)-physicalCoverFieldMap (normalSource C)*t +
      ∑ i, (coverPhysicalTangent i (v i) - v i * coverPhysicalTangent i
        (physicalCoverFieldMap physicalNormal) / physicalCoverFieldMap physicalNormal) = 0
    simpa only [residueDivergence, fieldDivergence, Finset.sum_sub_distrib,
      div_eq_mul_inv, Finset.sum_mul] using hp
  obtain ⟨D,N₀,N,Q,_hD,hlegal,hnormal,hdiv,_hdefect⟩ :=
    finite_residue_solution_clearing_value (K := HoldoutFunctionField) (L := CommonCoverFunctionField)
      physicalProjection physicalProjection_surjective
      (integerPartial 0) (fun i : Fin 5 => integerPartial i.succ)
      physicalTangent
      (fun i => extendFiniteDerivation (L := CommonCoverFunctionField) (physicalTangent i))
      holdoutSextic A
      (algebraMap HoldoutFunctionField CommonCoverFunctionField (normalSource A)-
       algebraMap HoldoutFunctionField CommonCoverFunctionField (normalSource C)*t) v
      (holdoutSextic_irreducible Complex.I hi) physicalProjection_kernel
      physical_normal_ne_zero (fun i => integerPartial_commute i.succ 0 _)
      physicalTangent_apply (fun i x => extendFiniteDerivation_apply (physicalTangent i) x)
      (trace_difference (normalSource A) (normalSource C) t ht) heq
  apply hasCertificate_of_normalized holdoutSextic A D (Fin.cases N₀ N) Q
    holdoutSextic_isHomogeneous hA (holdoutSextic_irreducible Complex.I hi).prime hlegal
    ?_ ?_ 0 holdoutSextic_not_dvd_pderiv_zero
  · set_option backward.isDefEq.respectTransparency false in
    simpa only [HodgeTestbed.directional, Fin.sum_univ_succ,
      Fin.cases_zero, Fin.cases_succ, integerPartial, Derivation.restrictScalars_apply,
      Derivation.coeFn_coe, mul_comm] using hnormal
  · set_option backward.isDefEq.respectTransparency false in
    simpa only [HodgeTestbed.divergenceNumerator, HodgeTestbed.divergence,
      HodgeTestbed.directional, residueDivNum, Fin.sum_univ_succ,
      Fin.cases_zero, Fin.cases_succ, integerPartial, Derivation.restrictScalars_apply,
      Derivation.coeFn_coe, mul_comm] using hdiv

end HoldoutGeneralization

#print axioms HoldoutGeneralization.certificate_of_source_pair
