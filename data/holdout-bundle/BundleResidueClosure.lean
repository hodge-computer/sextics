import Proposal.BundleAssembly
import HodgeComputer.Constructions.HoldoutCover.ResiduePiolaPullback
import HodgeComputer.Constructions.HoldoutCover.ResidueClearing

/-!
Close the protected physical certificate from its actual rational residue
equation.  The diagonal transport theorem keeps all five tangent components,
including the parameter coordinate, and uses the existing full Piola identity.
The parameter component may be zero while other components depend on it.
-/

noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace HoldoutBundle

open HoldoutConstruction MvPolynomial
open scoped BigOperators

attribute [local instance] holdoutCoordinateRing_isDomain

local instance : Algebra ℤ HoldoutFunctionField := Ring.toIntAlgebra _

local instance : CharZero HoldoutFunctionField :=
  charZero_of_injective_ringHom (f := algebraMap ℂ HoldoutFunctionField)
    (algebraMap ℂ HoldoutFunctionField).injective

def physicalSourceFor (A : HodgeComputer.Poly) : HoldoutFunctionField :=
  (physicalResidueMap (integerPartial 0 A) * physicalNormal -
    physicalResidueMap A *
      physicalResidueMap (integerPartial 0 (integerPartial 0 holdoutSextic))) /
        physicalNormal^2

theorem physical_certificate_of_residue
    (A : HodgeComputer.Poly) (hA : A.IsHomogeneous 6)
    (w : Fin 5 → HoldoutFunctionField)
    (equation : physicalSourceFor A +
      residueDivergence physicalTangent physicalNormal w = 0) :
    HodgeComputer.HasCertificate holdoutSextic A 1 := by
  have hi : (Complex.I : ℂ)^6 = -1 := by
    rw [show (6 : ℕ) = 2*3 by decide, pow_mul, Complex.I_sq]
    norm_num
  have heq :
      (physicalResidueMap (integerPartial 0 A) *
          physicalResidueMap (integerPartial 0 holdoutSextic) -
        physicalResidueMap A *
          physicalResidueMap (integerPartial 0 (integerPartial 0 holdoutSextic))) /
          (physicalResidueMap (integerPartial 0 holdoutSextic))^2 +
        ∑ i, (physicalTangent i (w i) - w i *
          physicalTangent i (physicalResidueMap (integerPartial 0 holdoutSextic)) /
            physicalResidueMap (integerPartial 0 holdoutSextic)) = 0 := by
    simpa only [physicalSourceFor, physicalNormal, residueDivergence,
      fieldDivergence, Finset.sum_sub_distrib, div_eq_mul_inv, Finset.sum_mul]
      using equation
  have hreps : ∃ d : HodgeComputer.Poly, ∃ n : Fin 5 → HodgeComputer.Poly,
      physicalResidueMap d ≠ 0 ∧
      ∀ i, physicalResidueMap (n i) = physicalResidueMap d * w i := by
    exact residue_common_representatives physicalProjection
      physicalProjection_surjective w
  obtain ⟨D, N₀, N, Q, _hD, hlegal, hnormal, hdiv, _hdefect⟩ :=
    residue_solution_clearing physicalResidueMap
      (integerPartial 0) (fun i : Fin 5 => integerPartial i.succ)
      physicalTangent holdoutSextic A w
      (holdoutSextic_irreducible Complex.I hi) physicalResidueMap_kernel
      physical_normal_ne_zero (fun i => integerPartial_commute i.succ 0 _)
      physicalTangent_apply hreps heq
  apply hasCertificate_of_normalized holdoutSextic A D (Fin.cases N₀ N) Q
    holdoutSextic_isHomogeneous hA (holdoutSextic_irreducible Complex.I hi).prime
    hlegal ?_ ?_ 0 holdoutSextic_not_dvd_pderiv_zero
  · simpa only [HodgeTestbed.directional, Fin.sum_univ_succ,
      Fin.cases_zero, Fin.cases_succ, integerPartial, Derivation.restrictScalars_apply,
      Derivation.coeFn_coe, mul_comm] using hnormal
  · simpa only [HodgeTestbed.divergenceNumerator, HodgeTestbed.divergence,
      HodgeTestbed.directional, residueDivNum, Fin.sum_univ_succ,
      Fin.cases_zero, Fin.cases_succ, integerPartial, Derivation.restrictScalars_apply,
      Derivation.coeFn_coe, mul_comm] using hdiv

theorem residue_source_map_append_zero
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

/-- Compatibility of a derivation with a field map only needs to be checked
on the coefficient ring and polynomial variables. -/
theorem derivation_map_polynomial_compatible
    {C R L σ : Type*} [CommRing C] [Field R] [Field L]
    (ρ : MvPolynomial σ C →+* R) (φ : R →+* L)
    (D : Derivation ℤ R R) (E : Derivation ℤ L L)
    (hC : ∀ c, E (φ (ρ (MvPolynomial.C c))) =
      φ (D (ρ (MvPolynomial.C c))))
    (hX : ∀ i, E (φ (ρ (MvPolynomial.X i))) =
      φ (D (ρ (MvPolynomial.X i)))) :
    ∀ p, E (φ (ρ p)) = φ (D (ρ p)) := by
  intro p
  induction p using MvPolynomial.induction_on with
  | C c => exact hC c
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hp, hX]

/-- Quotient-rule compatibility extends from a domain to its actual fraction
field. No formal or chosen normal extension is used. -/
theorem derivation_map_fraction_compatible
    {B R L : Type*} [CommRing B] [Field R] [Field L]
    [Algebra B R] [IsFractionRing B R]
    (φ : R →+* L) (D : Derivation ℤ R R) (E : Derivation ℤ L L)
    (h : ∀ b, E (φ (algebraMap B R b)) = φ (D (algebraMap B R b))) :
    ∀ x, E (φ x) = φ (D x) := by
  intro x
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective B x
  simp only [map_div₀, Derivation.leibniz_div, h, smul_eq_mul,
    map_sub, map_mul, map_pow, map_inv₀]

theorem normal_source_binding_of_pair
    {R : Type*} [Field R] (J B B0 A A0 g g0 : R)
    (hB : J*B=A) (hB0 : J*B0=A0) :
    J*((B0*g-B*g0)/g^2) = (A0*g-A*g0)/g^2 := by
  rw [← mul_div_assoc]
  congr 1
  linear_combination g*hB0-g0*hB

/-- The diagonal coordinate construction supplies these concrete matrix and
source identities.  This theorem performs their complete residue transport
and the legal homogeneous certificate extraction. -/
theorem physical_certificate_of_diagonal_residue
    {R : Type*} [Field R]
    (A : HodgeComputer.Poly) (hA : A.IsHomogeneous 6)
    (φ : R →+* HoldoutFunctionField)
    (Dq : Fin 4 → Derivation ℤ R R)
    (E : Fin 5 → Derivation ℤ HoldoutFunctionField HoldoutFunctionField)
    (M N : Matrix (Fin 5) (Fin 5) HoldoutFunctionField)
    (hMN : M*N = 1) (hNM : N*M = 1) (hdet : M.det ≠ 0)
    (chain : ∀ j x, E j x = ∑ k, N k j * physicalTangent k x)
    (mixed : ∀ i j k, physicalTangent k (M j i) = physicalTangent i (M j k))
    (compatible : ∀ i x, E i.castSucc (φ x) = φ (Dq i x))
    (gq rq : R) (wq : Fin 4 → R)
    (equation : rq + residueDivergence Dq gq wq = 0)
    (normal : φ gq = physicalNormal)
    (source : M.det * φ rq = physicalSourceFor A) :
    HodgeComputer.HasCertificate holdoutSextic A 1 := by
  let w : Fin 5 → HoldoutFunctionField := Fin.lastCases 0 (fun i => φ (wq i))
  have hw : φ rq + residueDivergence E (φ gq) w = 0 :=
    residue_source_map_append_zero φ Dq E compatible gq rq wq equation
  have hp := residue_solution_piola_pullback physicalTangent E M N
    hMN hNM hdet chain mixed (φ gq) (φ rq) w hw
  rw [normal, source] at hp
  exact physical_certificate_of_residue A hA
    (fun i => M.det * (N.mulVec w) i) hp

end HoldoutBundle

#print axioms HoldoutBundle.physical_certificate_of_residue
#print axioms HoldoutBundle.physical_certificate_of_diagonal_residue
