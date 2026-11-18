import Proposal.DeformedCoverDifferentials
import HodgeComputer.Constructions.HoldoutCover.FermatCoefficientDerivations

/-!
Compatibility of inverse-Jacobian derivations with the exact deformed
quotient field. Follows fqlx's CoverQuotientCompatibility proof, using
our deformed equation and its actual residue derivations throughout.
Prepared with OpenAI Codex assistance for hodgepodgeconjecture.
-/
noncomputable section
namespace DeformedCover
open HoldoutConstruction
open DeformedConic (BaseField TargetField targetProjection targetResidueMap targetTangent quotientEquation)
local instance deformedCoverCompatibility_local_1 : Algebra ℤ CoverField := Ring.toIntAlgebra _
local instance deformedCoverCompatibility_local_2 : Algebra ℤ TargetField := Ring.toIntAlgebra _
theorem coverQuotientTangent_beta (j : Fin 4) :
    coverQuotientTangent j.castSucc coverBeta = 0 := by
  have h := coverQuotientTangent_coordinate j.castSucc (Fin.last 4)
  have hj : (Fin.last 4 : Fin 5) ≠ j.castSucc := (Fin.castSucc_ne_last j).symm
  rw [show coverQuotientCoordinate (Fin.last 4) = coverBeta by rfl, ite_eq_right hj] at h
  exact h

theorem coverQuotientTangent_alpha (j : Fin 4) :
    coverQuotientTangent j.castSucc coverAlpha = 0 := by
  rw [fermat_cover_passive_derivative (coverQuotientTangent j.castSucc)
    coverAlpha coverBeta cover_fermat_relation coverAlpha_ne_zero,
    coverQuotientTangent_beta]
  simp

/-- The four fiber derivations kill every rational function of the entire
Fermat coefficient field, rather than just its displayed generators. -/
theorem coverQuotientTangent_base (j : Fin 4) (c : BaseField) :
    coverQuotientTangent j.castSucc
      (algebraMap (BaseField) CoverField c) = 0 := by
  apply fermatCoefficient_derivation_zero
    (coverQuotientTangent j.castSucc)
    (algebraMap (BaseField) CoverField)
  · intro a
    rw [← IsScalarTower.algebraMap_apply]
    exact coverQuotientTangent_constant j.castSucc a
  · exact coverQuotientTangent_alpha j
  · exact coverQuotientTangent_beta j


def coverQuotientResidueMap : MvPolynomial (Fin 5) BaseField →+* CoverField :=
  quotientFieldMap.comp targetResidueMap
@[simp] lemma coverQuotientResidueMap_C (c : BaseField) :
    coverQuotientResidueMap (MvPolynomial.C c)=algebraMap BaseField CoverField c :=
  quotientFieldMap_residue_C c
@[simp] lemma coverQuotientResidueMap_X_zero :
    coverQuotientResidueMap (MvPolynomial.X 0)=coverX0 :=
  quotientFieldMap_residue_X 0
@[simp] lemma coverQuotientResidueMap_X_succ (i : Fin 4) :
    coverQuotientResidueMap (MvPolynomial.X i.succ)=coverQuotientCoordinate i.castSucc := by
  change quotientFieldMap (targetResidueMap (MvPolynomial.X i.succ))=_
  rw [quotientFieldMap_residue_X]
  fin_cases i <;> rfl
lemma coverQuotientResidueMap_equation : coverQuotientResidueMap quotientEquation=0 := by
  have h := (DeformedGeometry.quotientResidueMap_kernel (14⁻¹)
    DeformedConic.baseFieldAlpha DeformedConic.baseFieldBeta quotientEquation).mpr (dvd_refl _)
  change quotientFieldMap (targetResidueMap quotientEquation)=0
  rw [show targetResidueMap quotientEquation=0 from h,map_zero]
lemma coverQuotientResidueMap_normal_ne_zero :
    coverQuotientResidueMap (integerPartial 0 quotientEquation) ≠ 0 :=
  (map_ne_zero quotientFieldMap).mpr DeformedConic.target_normal_ne_zero
lemma coverQuotientTangent_root (j : Fin 4) :
    coverQuotientTangent j.castSucc coverX0 =
      -coverQuotientResidueMap (integerPartial j.succ quotientEquation)/
        coverQuotientResidueMap (integerPartial 0 quotientEquation) := by
  have h := derivation_polynomial_ringHom_chain (coverQuotientTangent j.castSucc)
    coverQuotientResidueMap (by
      intro c
      rw [coverQuotientResidueMap_C]
      exact coverQuotientTangent_base j c) quotientEquation
  rw [coverQuotientResidueMap_equation,map_zero,Fin.sum_univ_succ] at h
  simp only [coverQuotientResidueMap_X_zero,coverQuotientResidueMap_X_succ,
    coverQuotientTangent_coordinate,Fin.castSucc_inj] at h
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at h
  apply (eq_div_iff coverQuotientResidueMap_normal_ne_zero).mpr
  simp only [integerPartial_apply]
  linear_combination -h

lemma coverQuotientTangent_compatible (j : Fin 4) (r : TargetField) :
    coverQuotientTangent j.castSucc (quotientFieldMap r)=quotientFieldMap (targetTangent j r) := by
  apply derivation_intertwines_quotient_fraction targetProjection
    (DeformedGeometry.quotientProjection_surjective _ _ _) quotientFieldMap
    (targetTangent j) (coverQuotientTangent j.castSucc)
  · intro c
    change coverQuotientTangent j.castSucc (quotientFieldMap (targetResidueMap (MvPolynomial.C c)))=
      quotientFieldMap (targetTangent j (targetResidueMap (MvPolynomial.C c)))
    rw [DeformedConic.targetTangent_apply]
    simp only [integerPartial_C,map_zero,mul_zero,sub_zero,
      quotientFieldMap_residue_C,coverQuotientTangent_base]
  · intro i
    change coverQuotientTangent j.castSucc (coverQuotientResidueMap (MvPolynomial.X i))=
      quotientFieldMap (targetTangent j (targetResidueMap (MvPolynomial.X i)))
    rw [DeformedConic.targetTangent_apply]
    refine Fin.cases ?_ (fun k => ?_) i
    · rw [coverQuotientResidueMap_X_zero,coverQuotientTangent_root]
      simp only [integerPartial_X_self,integerPartial_X_of_ne j.succ 0 (Fin.succ_ne_zero j).symm,
        map_zero,map_one,mul_one,zero_sub,map_neg,map_div₀,neg_div,coverQuotientResidueMap,RingHom.comp_apply]
    · rw [coverQuotientResidueMap_X_succ,coverQuotientTangent_coordinate,
        integerPartial_X_of_ne 0 k.succ (Fin.succ_ne_zero k)]
      simp only [map_zero,mul_zero,sub_zero,integerPartial_apply,MvPolynomial.pderiv_X,
        Pi.single_apply,Fin.castSucc_inj,Fin.succ_inj,apply_ite,map_one,map_zero]
      split_ifs <;> rfl
end DeformedCover
#print axioms DeformedCover.coverQuotientTangent_base
#print axioms DeformedCover.coverQuotientTangent_compatible
