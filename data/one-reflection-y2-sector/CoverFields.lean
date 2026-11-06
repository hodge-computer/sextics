import Mathlib.Analysis.Complex.Polynomial.Basic
import HodgeComputer.Constructions.HoldoutCover.AlgebraicFields
import Proposal.CommonCoverBaseChange

/- Source component: CoverFields -/
section
/-!
The actual common-cover function field is a finite extension of the exact
physical holdout function field. Finiteness follows from proved coordinate
injections, equal transcendence degree, and essential finite generation;
no assertion of an unproved exact degree is used. Prepared with OpenAI
ChatGPT assistance for a contribution through GitHub account fqlx.
-/

noncomputable section

namespace HoldoutConstruction

open Polynomial Algebra Cardinal

attribute [local instance] fermatCurve_adjoinRoot_isDomain fermat_base_charZero

abbrev HoldoutCoordinateRing := AdjoinRoot (holdoutPolynomial (R := ℂ))
abbrev HoldoutFunctionField := FractionRing HoldoutCoordinateRing
abbrev CommonCoverFunctionField := FractionRing (GenericCommonCoverRing ℂ)

private theorem complex_I_six : (Complex.I : ℂ)^6 = -1 := by
  rw [show 6 = 2*3 by decide, pow_mul, Complex.I_sq]
  norm_num

theorem holdoutCoordinateRing_isDomain : IsDomain HoldoutCoordinateRing :=
  AdjoinRoot.isDomain_of_prime
    (holdoutPolynomial_irreducible Complex.I complex_I_six).prime

theorem genericCommonCoverRing_isDomain : IsDomain (GenericCommonCoverRing ℂ) := by
  apply commonCover_adjoinRoot_isDomain
    (genericBaseAlpha ℂ) (genericBaseAlpha ℂ)
    (algebraMap ℂ (FermatCoefficientField ℂ) Complex.I)
  rw [← map_pow, complex_I_six, map_neg, map_one]

attribute [local instance] holdoutCoordinateRing_isDomain genericCommonCoverRing_isDomain

def physicalCoordinateFieldMap : HoldoutCoordinateRing →+* CommonCoverFunctionField :=
  (algebraMap (GenericCommonCoverRing ℂ) CommonCoverFunctionField).comp
    (physicalGenericCoverMap ℂ)

theorem physicalCoordinateFieldMap_injective :
    Function.Injective physicalCoordinateFieldMap := by
  intro a b h
  apply physicalGenericCoverMap_injective (K := ℂ)
  exact IsFractionRing.injective (GenericCommonCoverRing ℂ) CommonCoverFunctionField h

/-- The physical embedding extended to the actual residue function fields. -/
def physicalCoverFieldMap : HoldoutFunctionField →+* CommonCoverFunctionField :=
  IsFractionRing.lift (K := HoldoutFunctionField) (g := physicalCoordinateFieldMap)
    physicalCoordinateFieldMap_injective

@[simp] theorem physicalCoverFieldMap_coordinateRing (r : HoldoutCoordinateRing) :
    physicalCoverFieldMap (algebraMap HoldoutCoordinateRing HoldoutFunctionField r) =
      algebraMap (GenericCommonCoverRing ℂ) CommonCoverFunctionField
        (physicalGenericCoverMap ℂ r) := by
  simp [physicalCoverFieldMap, physicalCoordinateFieldMap, RingHom.comp_apply]

@[simp] theorem physicalCoverFieldMap_coefficient (c : ℂ) :
    physicalCoverFieldMap (algebraMap ℂ HoldoutFunctionField c) =
      algebraMap ℂ CommonCoverFunctionField c := by
  rw [IsScalarTower.algebraMap_apply ℂ HoldoutCoordinateRing HoldoutFunctionField,
    physicalCoverFieldMap_coordinateRing, physicalGenericCoverMap_coefficient,
    ← IsScalarTower.algebraMap_apply]

/-- This is the intended physical-base algebra structure on the common field. -/
noncomputable instance physicalCoverFieldAlgebra :
    Algebra HoldoutFunctionField CommonCoverFunctionField :=
  physicalCoverFieldMap.toAlgebra

instance physicalCoverField_scalarTower :
    IsScalarTower ℂ HoldoutFunctionField CommonCoverFunctionField :=
  IsScalarTower.of_algebraMap_eq (fun c => (physicalCoverFieldMap_coefficient c).symm)

theorem fermatBaseRing_trdeg :
    trdeg ℂ (FermatBaseRing ℂ) = 1 := by
  let : Module.Finite (Polynomial ℂ) (FermatBaseRing ℂ) :=
    Polynomial.Monic.finite_adjoinRoot fermatCurvePolynomial_monic
  let : FaithfulSMul (Polynomial ℂ) (FermatBaseRing ℂ) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr fermat_base_of_injective
  have h := trdeg_add_eq ℂ (Polynomial ℂ) (A := FermatBaseRing ℂ)
  simpa only [trdeg_eq_zero, add_zero, Polynomial.trdeg_of_isDomain] using h.symm

theorem fermatCoefficientField_trdeg :
    trdeg ℂ (FermatCoefficientField ℂ) = 1 := by
  rw [fractionRing_trdeg, fermatBaseRing_trdeg]

theorem holdoutFunctionField_trdeg : trdeg ℂ HoldoutFunctionField = 5 := by
  apply monic_hypersurface_field_trdeg
    (holdoutPolynomial (R := ℂ)) holdoutPolynomial_monic
  exact ne_of_gt (holdoutPolynomial_monic.degree_pos_of_not_isUnit
    (holdoutPolynomial_irreducible Complex.I complex_I_six).not_isUnit)

theorem commonCoverFunctionField_trdeg : trdeg ℂ CommonCoverFunctionField = 5 := by
  have hdeg :
      (commonCoverPolynomial (genericBaseAlpha ℂ) (genericBaseAlpha ℂ)).degree ≠ 0 := by
    apply ne_of_gt
    apply (commonCoverPolynomial_monic _ _).degree_pos_of_not_isUnit
    apply (commonCoverPolynomial_irreducible _ _
      (algebraMap ℂ (FermatCoefficientField ℂ) Complex.I) ?_).not_isUnit
    rw [← map_pow, complex_I_six, map_neg, map_one]
  rw [monic_hypersurface_relative_trdeg _ (commonCoverPolynomial_monic _ _) hdeg,
    fermatCoefficientField_trdeg]
  norm_num

theorem commonCoverFunctionField_essFiniteType :
    Algebra.EssFiniteType ℂ CommonCoverFunctionField := by
  let : Algebra.EssFiniteType ℂ (FermatCoefficientField ℂ) :=
    fractionRing_essFiniteType ℂ (FermatBaseRing ℂ)
  exact monic_hypersurface_relative_essFiniteType
    (commonCoverPolynomial (genericBaseAlpha ℂ) (genericBaseAlpha ℂ))

/-- The exact common residue field is finite over the physical residue field. -/
theorem commonCoverFunctionField_finite :
    Module.Finite HoldoutFunctionField CommonCoverFunctionField := by
  let : Algebra.EssFiniteType ℂ CommonCoverFunctionField :=
    commonCoverFunctionField_essFiniteType
  apply finite_of_same_finite_trdeg (K := ℂ)
  · rw [holdoutFunctionField_trdeg]
    exact Cardinal.natCast_lt_aleph0
  · rw [holdoutFunctionField_trdeg, commonCoverFunctionField_trdeg]

end HoldoutConstruction

#print axioms HoldoutConstruction.physicalCoverFieldMap
#print axioms HoldoutConstruction.commonCoverFunctionField_trdeg
#print axioms HoldoutConstruction.commonCoverFunctionField_finite
end
end
