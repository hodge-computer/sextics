import Proposal.CoverDifferentials
import Proposal.FermatCoefficientDerivations
import HodgeComputer.Constructions.HoldoutCover.FiniteDifferentials
import Proposal.QuotientDerivatives

/- Source component: CoverQuotientCompatibility -/
section
/-!
Compatibility of the inverse-Jacobian derivations with the actual weighted
quotient residue field. The fifth quotient coordinate is the Fermat base
parameter beta, and its vector component will be zero in the pullback.
Prepared with OpenAI ChatGPT assistance for a contribution through GitHub
account fqlx.
-/

noncomputable section

namespace HoldoutConstruction

open scoped BigOperators

attribute [local instance] fermatCurve_adjoinRoot_isDomain fermat_base_charZero
attribute [local instance] genericCommonCoverRing_isDomain quotient_adjoinRoot_isDomain

local instance coverQuotientCompatibility_intCommonCoverFunctionFieldAlgebra : Algebra ℤ CommonCoverFunctionField := Ring.toIntAlgebra _
local instance coverQuotientCompatibility_intGenericQuotientFieldAlgebra : Algebra ℤ GenericQuotientField := Ring.toIntAlgebra _

local instance coverQuotientCompatibility_commonCoverFunctionFieldCharZero : CharZero CommonCoverFunctionField :=
  charZero_of_injective_ringHom (f := algebraMap ℂ CommonCoverFunctionField)
    (algebraMap ℂ CommonCoverFunctionField).injective

theorem coverQuotientTangent_beta (j : Fin 4) :
    coverQuotientTangent j.castSucc coverBeta = 0 := by
  have h := coverQuotientTangent_coordinate j.castSucc (Fin.last 4)
  have hj : (Fin.last 4 : Fin 5) ≠ j.castSucc := (Fin.castSucc_ne_last j).symm
  rw [show coverQuotientCoordinate (Fin.last 4) = coverBeta by rfl, if_neg hj] at h
  exact h

theorem coverQuotientTangent_alpha (j : Fin 4) :
    coverQuotientTangent j.castSucc coverAlpha = 0 := by
  rw [fermat_cover_passive_derivative (coverQuotientTangent j.castSucc)
    coverAlpha coverBeta cover_fermat_relation coverAlpha_ne_zero,
    coverQuotientTangent_beta]
  simp

/-- The four fiber derivations kill every rational function of the entire
Fermat coefficient field, rather than just its displayed generators. -/
theorem coverQuotientTangent_base (j : Fin 4) (c : FermatCoefficientField ℂ) :
    coverQuotientTangent j.castSucc
      (algebraMap (FermatCoefficientField ℂ) CommonCoverFunctionField c) = 0 := by
  apply fermatCoefficient_derivation_zero
    (coverQuotientTangent j.castSucc)
    (algebraMap (FermatCoefficientField ℂ) CommonCoverFunctionField)
  · intro a
    rw [← IsScalarTower.algebraMap_apply]
    exact coverQuotientTangent_constant j.castSucc a
  · exact coverQuotientTangent_alpha j
  · exact coverQuotientTangent_beta j

def coverQuotientResidueMap :
    MvPolynomial (Fin 5) (FermatCoefficientField ℂ) →+* CommonCoverFunctionField :=
  quotientCoverFieldMap.comp (quotientResidueMap (genericBaseAlpha ℂ) (genericBaseAlpha ℂ))

@[simp] theorem coverQuotientResidueMap_C (c : FermatCoefficientField ℂ) :
    coverQuotientResidueMap (MvPolynomial.C c) =
      algebraMap (FermatCoefficientField ℂ) CommonCoverFunctionField c := by
  simp only [coverQuotientResidueMap, RingHom.comp_apply, quotientResidueMap_C,
    quotientCoverFieldMap_coefficient]

@[simp] theorem coverQuotientResidueMap_X_zero :
    coverQuotientResidueMap (MvPolynomial.X 0) = coverX0 := by
  simp only [coverQuotientResidueMap, RingHom.comp_apply, quotientResidueMap_X_zero,
    quotientRoot, quotientCoverFieldMap_root]

@[simp] theorem coverQuotientResidueMap_X_succ (i : Fin 4) :
    coverQuotientResidueMap (MvPolynomial.X i.succ) =
      coverQuotientCoordinate i.castSucc := by
  simp only [coverQuotientResidueMap, RingHom.comp_apply,
    quotientResidueMap_X_succ, quotientParameter, quotientCoverFieldMap_parameter]
  fin_cases i <;> rfl

theorem coverQuotientResidueMap_equation :
    coverQuotientResidueMap
      (weightedHypersurface (genericBaseAlpha ℂ) (genericBaseAlpha ℂ)) = 0 := by
  have h := (quotientResidueMap_kernel (genericBaseAlpha ℂ) (genericBaseAlpha ℂ)
    (weightedHypersurface (genericBaseAlpha ℂ) (genericBaseAlpha ℂ))).mpr (dvd_refl _)
  simp only [coverQuotientResidueMap, RingHom.comp_apply, h, map_zero]

theorem coverQuotientResidueMap_normal_ne_zero :
    coverQuotientResidueMap
      (integerPartial 0 (weightedHypersurface (genericBaseAlpha ℂ) (genericBaseAlpha ℂ))) ≠ 0 :=
  (_root_.map_ne_zero (G₀ := GenericQuotientField) (M₀' := CommonCoverFunctionField)
    quotientCoverFieldMap).2
    (quotient_normal_ne_zero (genericBaseAlpha ℂ) (genericBaseAlpha ℂ))

theorem coverQuotientTangent_root (j : Fin 4) :
    coverQuotientTangent j.castSucc coverX0 =
      -coverQuotientResidueMap
        (integerPartial j.succ (weightedHypersurface (genericBaseAlpha ℂ) (genericBaseAlpha ℂ))) /
        coverQuotientResidueMap
          (integerPartial 0 (weightedHypersurface (genericBaseAlpha ℂ) (genericBaseAlpha ℂ))) := by
  have h := derivation_polynomial_ringHom_chain (coverQuotientTangent j.castSucc)
    coverQuotientResidueMap (by
      intro c
      rw [coverQuotientResidueMap_C]
      exact coverQuotientTangent_base j c)
    (weightedHypersurface (genericBaseAlpha ℂ) (genericBaseAlpha ℂ))
  rw [coverQuotientResidueMap_equation, map_zero, Fin.sum_univ_succ] at h
  simp only [coverQuotientResidueMap_X_zero, coverQuotientResidueMap_X_succ,
    coverQuotientTangent_coordinate, Fin.castSucc_inj] at h
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at h
  apply (eq_div_iff coverQuotientResidueMap_normal_ne_zero).mpr
  simp only [integerPartial_apply]
  linear_combination -h

/-- Full field compatibility follows from the coefficient and coordinate
identities; the common field need not be finite over this quotient field. -/
theorem coverQuotientTangent_compatible (j : Fin 4) (r : GenericQuotientField) :
    coverQuotientTangent j.castSucc (quotientCoverFieldMap r) =
      quotientCoverFieldMap
        (quotientTangent (genericBaseAlpha ℂ) (genericBaseAlpha ℂ) j r) := by
  apply derivation_intertwines_quotient_fraction
    (quotientProjection (genericBaseAlpha ℂ) (genericBaseAlpha ℂ))
    (quotientProjection_surjective (genericBaseAlpha ℂ) (genericBaseAlpha ℂ))
    quotientCoverFieldMap
    (quotientTangent (genericBaseAlpha ℂ) (genericBaseAlpha ℂ) j)
    (coverQuotientTangent j.castSucc)
  · intro c
    change coverQuotientTangent j.castSucc
      (quotientCoverFieldMap (quotientResidueMap _ _ (MvPolynomial.C c))) =
      quotientCoverFieldMap (quotientTangent _ _ j
        (quotientResidueMap _ _ (MvPolynomial.C c)))
    simp only [quotientResidueMap_C, quotientCoverFieldMap_coefficient,
      quotientTangent_algebraMap, map_zero, coverQuotientTangent_base]
  · intro i
    change coverQuotientTangent j.castSucc (coverQuotientResidueMap (MvPolynomial.X i)) =
      quotientCoverFieldMap (quotientTangent _ _ j
        (quotientResidueMap _ _ (MvPolynomial.X i)))
    refine Fin.cases ?_ (fun k => ?_) i
    · rw [coverQuotientResidueMap_X_zero, quotientResidueMap_X_zero,
        quotientTangent_root,
        map_div₀ (G₀ := GenericQuotientField) (G₀' := CommonCoverFunctionField)
          quotientCoverFieldMap,
        RingHom.map_neg, coverQuotientTangent_root]
      rfl
    · rw [coverQuotientResidueMap_X_succ, quotientResidueMap_X_succ,
        quotientTangent_parameter, coverQuotientTangent_coordinate]
      simp only [Fin.castSucc_inj]
      split_ifs <;> simp

end HoldoutConstruction

#print axioms HoldoutConstruction.coverQuotientTangent_base
#print axioms HoldoutConstruction.coverQuotientTangent_root
#print axioms HoldoutConstruction.coverQuotientTangent_compatible
end
end
