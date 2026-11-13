import HodgeComputer.Constructions.HoldoutCover.PhysicalDerivations
import HodgeComputer.Constructions.HoldoutCover.QuotientCoverField

/- Source component: CoverCoordinates -/
section
/-!
Exact coordinate formulas and nonzero chart functions on the common
residue field. All coordinate maps are the previously proved injections.
Prepared with OpenAI ChatGPT assistance for a contribution through GitHub
account fqlx.
-/

noncomputable section

namespace HoldoutConstruction

attribute [local instance] fermatCurve_adjoinRoot_isDomain fermat_base_charZero
attribute [local instance] holdoutCoordinateRing_isDomain genericCommonCoverRing_isDomain

@[simp] theorem cover_of_C (c : FermatCoefficientField ℂ) :
    algebraMap (GenericCommonCoverRing ℂ) CommonCoverFunctionField
      (AdjoinRoot.of _ (MvPolynomial.C c)) =
        algebraMap (FermatCoefficientField ℂ) CommonCoverFunctionField c := by
  change algebraMap (GenericCommonCoverRing ℂ) CommonCoverFunctionField
    (algebraMap (FermatCoefficientField ℂ) (GenericCommonCoverRing ℂ) c) = _
  exact (IsScalarTower.algebraMap_apply (FermatCoefficientField ℂ)
    (GenericCommonCoverRing ℂ) CommonCoverFunctionField c).symm

private theorem commonCoverBaseChange_of_C
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (a b c : R) :
    commonCoverBaseChange φ a b (AdjoinRoot.of _ (MvPolynomial.C c)) =
      AdjoinRoot.of _ (MvPolynomial.C (φ c)) :=
  commonCoverBaseChange_coefficient φ a b c

@[simp] theorem physicalCoverFieldMap_root :
    physicalCoverFieldMap (algebraMap HoldoutCoordinateRing HoldoutFunctionField physicalRoot) =
      coverX0 := by
  rw [physicalCoverFieldMap_coordinateRing]
  simp [physicalRoot, coverX0]

@[simp] theorem physicalCoverFieldMap_parameter (i : Fin 5) :
    physicalCoverFieldMap
      (algebraMap HoldoutCoordinateRing HoldoutFunctionField (physicalParameter i)) =
      ![coverX1, coverX2, coverAlpha*coverT, coverY, coverBeta*coverT] i := by
  rw [physicalCoverFieldMap_coordinateRing]
  change algebraMap (GenericCommonCoverRing ℂ) CommonCoverFunctionField
    (commonCoverBaseChange (algebraMap (FermatBaseRing ℂ) (FermatCoefficientField ℂ))
      baseAlpha baseBeta
      (physicalCommonCoverMap (AdjoinRoot.of _ (MvPolynomial.X i)))) = _
  rw [physicalCommonCoverMap, AdjoinRoot.map_of]
  fin_cases i <;>
    norm_num [physicalCoverCoefficientMap, Fin.ext_iff,
      commonCoverBaseChange_of_C, coverCoefficient, coverAlpha, coverBeta,
      -MvPolynomial.eval₂Hom_C_eq_bind₁] <;>
    rfl

@[simp] theorem quotientCoverFieldMap_root :
    quotientCoverFieldMap (algebraMap GenericQuotientRing GenericQuotientField
      (AdjoinRoot.root (quotientPolynomial (genericBaseAlpha ℂ) (genericBaseBeta ℂ)))) =
      coverX0 := by
  rw [quotientCoverFieldMap_coordinateRing]
  simp [quotientCommonCoverMap, coverX0]

@[simp] theorem quotientCoverFieldMap_parameter (i : Fin 4) :
    quotientCoverFieldMap (algebraMap GenericQuotientRing GenericQuotientField
      (AdjoinRoot.of _ (MvPolynomial.X i))) =
      ![coverX1, coverX2, coverY^2+coverT^2, coverY*coverT] i := by
  rw [quotientCoverFieldMap_coordinateRing, quotientCommonCoverMap, AdjoinRoot.map_of]
  fin_cases i <;> simp [quotientCoverCoefficientMap, coverCoefficient]

theorem coverAlpha_ne_zero : coverAlpha ≠ 0 := by
  have ha : genericBaseAlpha ℂ ≠ 0 := by
    have h := (IsFractionRing.injective (FermatBaseRing ℂ) (FermatCoefficientField ℂ)).ne
      (baseAlpha_ne_zero (R := ℂ))
    simpa only [genericBaseAlpha, map_zero] using h
  simpa only [coverAlpha] using
    ((map_ne_zero (algebraMap (FermatCoefficientField ℂ) CommonCoverFunctionField)).2 ha)

private theorem commonCover_degree_ne_zero :
    (commonCoverPolynomial (genericBaseAlpha ℂ) (genericBaseBeta ℂ)).degree ≠ 0 := by
  apply ne_of_gt
  apply (commonCoverPolynomial_monic _ _).degree_pos_of_not_isUnit
  apply (commonCoverPolynomial_irreducible _ _
    (algebraMap ℂ (FermatCoefficientField ℂ) Complex.I) ?_).not_isUnit
  rw [← map_pow, show (Complex.I : ℂ)^6 = -1 by
    rw [show 6=2*3 by decide, pow_mul, Complex.I_sq]; norm_num,
    map_neg, map_one]

private theorem commonCoefficientMap_injective :
    Function.Injective
      ((algebraMap (GenericCommonCoverRing ℂ) CommonCoverFunctionField).comp
        (AdjoinRoot.of (commonCoverPolynomial (genericBaseAlpha ℂ) (genericBaseBeta ℂ)))) :=
  (IsFractionRing.injective (GenericCommonCoverRing ℂ) CommonCoverFunctionField).comp
    (AdjoinRoot.of.injective_of_degree_ne_zero commonCover_degree_ne_zero)

theorem coverT_ne_zero : coverT ≠ 0 := by
  have hX : (MvPolynomial.X (3 : Fin 4) : MvPolynomial (Fin 4) (FermatCoefficientField ℂ)) ≠ 0 := by
    intro h
    have he := congrArg (MvPolynomial.eval (fun _ => (1 : FermatCoefficientField ℂ))) h
    simp at he
  have h := commonCoefficientMap_injective.ne hX
  simpa only [RingHom.comp_apply, map_zero, coverCoefficient] using h

theorem cover_square_difference_ne_zero : coverT^2-coverY^2 ≠ 0 := by
  have hp : ((MvPolynomial.X (3 : Fin 4))^2-(MvPolynomial.X 2)^2 :
      MvPolynomial (Fin 4) (FermatCoefficientField ℂ)) ≠ 0 := by
    intro h
    have he := congrArg (MvPolynomial.eval ![0,0,0,(1 : FermatCoefficientField ℂ)]) h
    simp at he
  have h := commonCoefficientMap_injective.ne hp
  simpa [coverCoefficient, RingHom.comp_apply] using h

end HoldoutConstruction

#print axioms HoldoutConstruction.physicalCoverFieldMap_parameter
#print axioms HoldoutConstruction.quotientCoverFieldMap_parameter
#print axioms HoldoutConstruction.cover_square_difference_ne_zero
end
end
