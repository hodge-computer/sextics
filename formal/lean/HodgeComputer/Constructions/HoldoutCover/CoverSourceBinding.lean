import HodgeComputer.Constructions.HoldoutCover.CoverCoordinates
import HodgeComputer.Constructions.HoldoutCover.CoverScalars
import HodgeComputer.Constructions.HoldoutCover.HomogeneousCertificate
import HodgeComputer.Constructions.HoldoutCover.QuotientDerivatives

/- Source component: CoverSourceBinding -/
section
/-!
Bind the finite-cover source calculation to the exact holdout polynomials.
The physical numerator is the unchanged holdoutSource = X0^3*Y0^3.
The quotient coordinate order is X0,X1,X2,S,P, and its numerator is
X0^3*S/(2*alpha^2). The maps in the identities below are the actual
injective maps of residue function fields.
-/

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace HoldoutConstruction

open MvPolynomial

section PolynomialIdentities

variable {R : Type*} [CommRing R]

theorem cover_holdout_normal_polynomial :
    integerPartial 0 (holdoutSextic (R := R)) =
      6*X 0^5+3*X 0^2*X 1*X 3*X 4 := by
  norm_num [integerPartial_apply, holdoutSextic, MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_mul, Pi.single_apply, Fin.ext_iff]
  ring

theorem cover_holdout_second_normal_polynomial :
    integerPartial 0 (integerPartial 0 (holdoutSextic (R := R))) =
      30*X 0^4+6*X 0*X 1*X 3*X 4 := by
  rw [cover_holdout_normal_polynomial]
  have hthree : MvPolynomial.pderiv (0 : Fin 6) (3 : MvPolynomial (Fin 6) R) = 0 :=
    Derivation.map_natCast _ 3
  have hsix : MvPolynomial.pderiv (0 : Fin 6) (6 : MvPolynomial (Fin 6) R) = 0 :=
    Derivation.map_natCast _ 6
  norm_num [integerPartial_apply, MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_mul, Pi.single_apply, Fin.ext_iff, hthree, hsix]
  ring

theorem cover_quotient_normal_polynomial (alpha beta : R) :
    integerPartial 0 (weightedHypersurface alpha beta) =
      6*X 0^5+3*C alpha*X 0^2*X 1*X 4 := by
  have hthree : MvPolynomial.pderiv (0 : Fin 5) (3 : MvPolynomial (Fin 5) R) = 0 :=
    Derivation.map_natCast _ 3
  norm_num [integerPartial_apply, weightedHypersurface, MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_mul, Pi.single_apply, Fin.ext_iff, hthree]
  ring

theorem cover_quotient_second_normal_polynomial (alpha beta : R) :
    integerPartial 0 (integerPartial 0 (weightedHypersurface alpha beta)) =
      30*X 0^4+6*C alpha*X 0*X 1*X 4 := by
  rw [cover_quotient_normal_polynomial]
  have hthree : MvPolynomial.pderiv (0 : Fin 5) (3 : MvPolynomial (Fin 5) R) = 0 :=
    Derivation.map_natCast _ 3
  have hsix : MvPolynomial.pderiv (0 : Fin 5) (6 : MvPolynomial (Fin 5) R) = 0 :=
    Derivation.map_natCast _ 6
  norm_num [integerPartial_apply, MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_mul, Pi.single_apply, Fin.ext_iff, hthree, hsix]
  ring

def scaledCoverQuotientSource (c : R) : MvPolynomial (Fin 5) R :=
  C c*X 0^3*X 3

theorem scaledCoverQuotientSource_partial (c : R) :
    integerPartial 0 (scaledCoverQuotientSource c) = 3*C c*X 0^2*X 3 := by
  norm_num [integerPartial_apply, scaledCoverQuotientSource,
    MvPolynomial.pderiv_pow, MvPolynomial.pderiv_mul, Pi.single_apply, Fin.ext_iff]
  ring

end PolynomialIdentities

theorem cover_holdoutSource_partial :
    integerPartial 0 holdoutSource = 3*X 0^2*X 3^3 := by
  norm_num [integerPartial_apply, holdoutSource, MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_mul, Pi.single_apply, Fin.ext_iff]
  ring

attribute [local instance] fermatCurve_adjoinRoot_isDomain fermat_base_charZero
attribute [local instance] holdoutCoordinateRing_isDomain genericCommonCoverRing_isDomain
attribute [local instance] quotient_adjoinRoot_isDomain quotient_charZero

local instance coverSourceBinding_commonCoverFunctionFieldCharZero : CharZero CommonCoverFunctionField :=
  charZero_of_injective_ringHom (f := algebraMap ℂ CommonCoverFunctionField)
    (algebraMap ℂ CommonCoverFunctionField).injective

local notation "ρq" => quotientResidueMap (genericBaseAlpha ℂ) (genericBaseBeta ℂ)
local notation "G" => weightedHypersurface (genericBaseAlpha ℂ) (genericBaseBeta ℂ)
local notation "ρp" => physicalResidueMap
local notation "F" => (holdoutSextic (R := ℂ))

/-- The exact positive source on the weighted quotient. -/
def coverQuotientSource : MvPolynomial (Fin 5) (FermatCoefficientField ℂ) :=
  scaledCoverQuotientSource (1/(2*(genericBaseAlpha ℂ)^2))

@[simp] theorem physicalCoverFieldMap_residue_X (i : Fin 6) :
    physicalCoverFieldMap (ρp (X i)) =
      ![coverX0, coverX1, coverX2, coverAlpha*coverT, coverY, coverBeta*coverT] i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [physicalResidueMap_X_zero, physicalCoverFieldMap_root]
    rfl
  · rw [physicalResidueMap_X_succ, physicalCoverFieldMap_parameter]
    rfl

@[simp] theorem quotientCoverFieldMap_residue_X (i : Fin 5) :
    quotientCoverFieldMap (ρq (X i)) =
      ![coverX0, coverX1, coverX2, coverY^2+coverT^2, coverY*coverT] i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [quotientResidueMap_X_zero]
    exact quotientCoverFieldMap_root
  · rw [quotientResidueMap_X_succ]
    exact quotientCoverFieldMap_parameter j

@[simp] theorem quotientCoverFieldMap_residue_C (c : FermatCoefficientField ℂ) :
    quotientCoverFieldMap (ρq (C c)) =
      algebraMap (FermatCoefficientField ℂ) CommonCoverFunctionField c := by
  rw [quotientResidueMap_C, quotientCoverFieldMap_coefficient]

theorem cover_physical_normal_value :
    physicalCoverFieldMap (ρp (integerPartial 0 F)) =
      6*coverX0^5+3*coverX0^2*coverX1*(coverAlpha*coverT)*coverY := by
  rw [cover_holdout_normal_polynomial]
  simp only [map_add, map_mul, map_pow, map_ofNat, physicalCoverFieldMap_residue_X]
  rfl

theorem cover_physical_second_normal_value :
    physicalCoverFieldMap (ρp (integerPartial 0 (integerPartial 0 F))) =
      30*coverX0^4+6*coverX0*coverX1*(coverAlpha*coverT)*coverY := by
  rw [cover_holdout_second_normal_polynomial]
  simp only [map_add, map_mul, map_pow, map_ofNat, physicalCoverFieldMap_residue_X]
  rfl

theorem cover_quotient_normal_value :
    quotientCoverFieldMap (ρq (integerPartial 0 G)) =
      6*coverX0^5+3*coverAlpha*coverX0^2*coverX1*(coverY*coverT) := by
  rw [cover_quotient_normal_polynomial]
  simp only [map_add, map_mul, map_pow, map_ofNat,
    quotientCoverFieldMap_residue_X, quotientCoverFieldMap_residue_C]
  rfl

theorem cover_quotient_second_normal_value :
    quotientCoverFieldMap (ρq (integerPartial 0 (integerPartial 0 G))) =
      30*coverX0^4+6*coverAlpha*coverX0*coverX1*(coverY*coverT) := by
  rw [cover_quotient_second_normal_polynomial]
  simp only [map_add, map_mul, map_pow, map_ofNat,
    quotientCoverFieldMap_residue_X, quotientCoverFieldMap_residue_C]
  rfl

/-- Both coordinate maps fix the distinguished normal coordinate X0. -/
theorem cover_normal_binding :
    quotientCoverFieldMap (ρq (integerPartial 0 G)) =
      physicalCoverFieldMap (ρp (integerPartial 0 F)) := by
  rw [cover_quotient_normal_value, cover_physical_normal_value]
  ring

theorem cover_second_normal_binding :
    quotientCoverFieldMap (ρq (integerPartial 0 (integerPartial 0 G))) =
      physicalCoverFieldMap (ρp (integerPartial 0 (integerPartial 0 F))) := by
  rw [cover_quotient_second_normal_value, cover_physical_second_normal_value]
  ring

theorem cover_physical_normal_ne_zero :
    physicalCoverFieldMap (ρp (integerPartial 0 F)) ≠ 0 := by
  exact (map_ne_zero physicalCoverFieldMap).2 physical_normal_ne_zero

theorem cover_physical_source_value :
    physicalCoverFieldMap (ρp holdoutSource) = coverX0^3*(coverAlpha*coverT)^3 := by
  simp only [holdoutSource, map_mul, map_pow, physicalCoverFieldMap_residue_X]
  rfl

theorem cover_physical_source_partial_value :
    physicalCoverFieldMap (ρp (integerPartial 0 holdoutSource)) =
      3*coverX0^2*(coverAlpha*coverT)^3 := by
  rw [cover_holdoutSource_partial]
  simp only [map_mul, map_pow, map_ofNat, physicalCoverFieldMap_residue_X]
  rfl

theorem cover_quotient_source_value :
    quotientCoverFieldMap (ρq coverQuotientSource) =
      coverX0^3*(coverY^2+coverT^2)/(2*coverAlpha^2) := by
  simp only [coverQuotientSource, scaledCoverQuotientSource, map_mul, map_pow,
    quotientCoverFieldMap_residue_X, quotientCoverFieldMap_residue_C,
    map_div₀, map_one, map_ofNat]
  change (1/(2*coverAlpha^2))*coverX0^3*(coverY^2+coverT^2) = _
  ring

theorem cover_quotient_source_partial_value :
    quotientCoverFieldMap (ρq (integerPartial 0 coverQuotientSource)) =
      3*coverX0^2*(coverY^2+coverT^2)/(2*coverAlpha^2) := by
  unfold coverQuotientSource
  rw [scaledCoverQuotientSource_partial]
  simp only [map_mul, map_pow, map_ofNat, quotientCoverFieldMap_residue_X,
    quotientCoverFieldMap_residue_C, map_div₀, map_one]
  change 3*(1/(2*coverAlpha^2))*coverX0^2*(coverY^2+coverT^2) = _
  ring

/-- The source multiplier is exactly the nontrivial deck-character correction
whose normalized trace vanishes. The denominator T is proved nonzero in the
actual common residue field. -/
theorem cover_source_binding :
    (2*coverAlpha^5*(coverT^2-coverY^2)/coverT) *
      quotientCoverFieldMap (ρq coverQuotientSource) =
      physicalCoverFieldMap (ρp holdoutSource) *
        (1-physicalCoverFieldMap (ρp (X 4))^4*(coverT^4)⁻¹) := by
  rw [cover_quotient_source_value, cover_physical_source_value]
  have hy : physicalCoverFieldMap (ρp (X 4)) = coverY := physicalCoverFieldMap_residue_X 4
  rw [hy]
  simpa only [div_eq_mul_inv] using
    cover_source_identity coverAlpha coverX0 coverY coverT coverAlpha_ne_zero coverT_ne_zero

/-- The exact normal-divergence source required by finite residue clearing,
with the same physical numerator and the same physical normal derivative. -/
theorem cover_normal_source_binding :
    (2*coverAlpha^5*(coverT^2-coverY^2)/coverT) *
      quotientCoverFieldMap
        ((ρq (integerPartial 0 coverQuotientSource)*ρq (integerPartial 0 G)-
          ρq coverQuotientSource*ρq (integerPartial 0 (integerPartial 0 G))) /
            (ρq (integerPartial 0 G))^2) =
      physicalCoverFieldMap
        ((ρp (integerPartial 0 holdoutSource)*ρp (integerPartial 0 F)-
          ρp holdoutSource*ρp (integerPartial 0 (integerPartial 0 F))) /
            (ρp (integerPartial 0 F))^2) *
        (1-physicalCoverFieldMap (ρp (X 4))^4*(coverT^4)⁻¹) := by
  simp only [map_div₀, map_sub, map_mul, map_pow]
  rw [cover_normal_binding, cover_second_normal_binding,
    cover_quotient_source_partial_value, cover_quotient_source_value,
    cover_physical_source_partial_value, cover_physical_source_value]
  have hy : physicalCoverFieldMap (ρp (X 4)) = coverY := physicalCoverFieldMap_residue_X 4
  rw [hy]
  simpa only [div_eq_mul_inv] using
    cover_normal_source_identity coverAlpha coverX0 coverY coverT
      (physicalCoverFieldMap (ρp (integerPartial 0 F)))
      (physicalCoverFieldMap (ρp (integerPartial 0 (integerPartial 0 F))))
      coverAlpha_ne_zero coverT_ne_zero

end HoldoutConstruction

#print axioms HoldoutConstruction.cover_normal_binding
#print axioms HoldoutConstruction.cover_second_normal_binding
#print axioms HoldoutConstruction.cover_source_binding
#print axioms HoldoutConstruction.cover_normal_source_binding
end
end
