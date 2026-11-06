import HodgeComputer.Constructions.HoldoutCover.CoverCoordinateDerivatives
import Proposal.CoverCoordinates
import Proposal.CoverScalars
import HodgeComputer.Constructions.HoldoutCover.FiniteDifferentials
import HodgeComputer.Constructions.HoldoutCover.PolynomialFamilyBridge

/- Source component: CoverDifferentials -/
section
/-!
The actual physical residue derivations extended to the common field,
and the inverse-Jacobian coordinate derivations for the weighted quotient.
Every Jacobian entry is computed from the defining coordinate relations.
Prepared with OpenAI ChatGPT assistance for a contribution through GitHub
account fqlx.
-/

noncomputable section

namespace HoldoutConstruction

open scoped BigOperators

attribute [local instance] fermatCurve_adjoinRoot_isDomain fermat_base_charZero
attribute [local instance] holdoutCoordinateRing_isDomain genericCommonCoverRing_isDomain
attribute [local instance] commonCoverFunctionField_finite

local instance coverDifferentials_intHoldoutFunctionFieldAlgebra : Algebra ℤ HoldoutFunctionField := Ring.toIntAlgebra _
local instance coverDifferentials_intCommonCoverFunctionFieldAlgebra : Algebra ℤ CommonCoverFunctionField := Ring.toIntAlgebra _

local instance coverDifferentials_holdoutFunctionFieldCharZero : CharZero HoldoutFunctionField :=
  charZero_of_injective_ringHom (f := algebraMap ℂ HoldoutFunctionField)
    (algebraMap ℂ HoldoutFunctionField).injective

local instance coverDifferentials_commonCoverFunctionFieldCharZero : CharZero CommonCoverFunctionField :=
  charZero_of_injective_ringHom (f := algebraMap ℂ CommonCoverFunctionField)
    (algebraMap ℂ CommonCoverFunctionField).injective

def coverPhysicalTangent (i : Fin 5) :
    Derivation ℤ CommonCoverFunctionField CommonCoverFunctionField :=
  extendFiniteDerivation (L := CommonCoverFunctionField) (physicalTangent i)

theorem coverPhysicalTangent_compatible (i : Fin 5) (r : HoldoutFunctionField) :
    coverPhysicalTangent i (physicalCoverFieldMap r) =
      physicalCoverFieldMap (physicalTangent i r) :=
  extendFiniteDerivation_apply (physicalTangent i) r

theorem coverPhysicalTangents_commute (i j : Fin 5) :
    Function.Commute (coverPhysicalTangent i) (coverPhysicalTangent j) :=
  extendFiniteDerivation_commute (physicalTangent i) (physicalTangent j)
    (physicalTangents_commute i j)

@[simp] theorem coverPhysicalTangent_constant (i : Fin 5) (c : ℂ) :
    coverPhysicalTangent i (algebraMap ℂ CommonCoverFunctionField c) = 0 := by
  rw [← physicalCoverFieldMap_coefficient, coverPhysicalTangent_compatible,
    physicalTangent_algebraMap, map_zero]

theorem coverPhysicalTangent_parameter (i j : Fin 5) :
    coverPhysicalTangent i
      (![coverX1,coverX2,coverAlpha*coverT,coverY,coverBeta*coverT] j) =
        if j=i then 1 else 0 := by
  rw [← physicalCoverFieldMap_parameter, coverPhysicalTangent_compatible,
    physicalTangent_parameter]
  split_ifs <;> simp

@[simp] theorem coverPhysicalTangent_x1 (i : Fin 5) :
    coverPhysicalTangent i coverX1 = if (0:Fin 5)=i then 1 else 0 := by
  simpa only [Matrix.cons_val_zero] using coverPhysicalTangent_parameter i 0

@[simp] theorem coverPhysicalTangent_x2 (i : Fin 5) :
    coverPhysicalTangent i coverX2 = if (1:Fin 5)=i then 1 else 0 := by
  simpa only [Matrix.cons_val_one, Matrix.cons_val_zero] using coverPhysicalTangent_parameter i 1

@[simp] theorem coverPhysicalTangent_Y0 (i : Fin 5) :
    coverPhysicalTangent i (coverAlpha*coverT) = if (2:Fin 5)=i then 1 else 0 := by
  simpa only [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using
    coverPhysicalTangent_parameter i 2

@[simp] theorem coverPhysicalTangent_y (i : Fin 5) :
    coverPhysicalTangent i coverY = if (3:Fin 5)=i then 1 else 0 := by
  simpa using coverPhysicalTangent_parameter i 3

@[simp] theorem coverPhysicalTangent_Y2 (i : Fin 5) :
    coverPhysicalTangent i (coverBeta*coverT) = if (4:Fin 5)=i then 1 else 0 := by
  simpa using coverPhysicalTangent_parameter i 4

theorem coverPhysicalTangent_T (i : Fin 5) :
    coverPhysicalTangent i coverT =
      coverAlpha^5*(if (2:Fin 5)=i then 1 else 0) +
        coverBeta^5*(if (4:Fin 5)=i then 1 else 0) :=
  fermat_cover_time_derivative (coverPhysicalTangent i) _ _ _ _ _
    cover_fermat_relation (coverPhysicalTangent_Y0 i) (coverPhysicalTangent_Y2 i)

theorem coverPhysicalTangent_beta (i : Fin 5) :
    coverPhysicalTangent i coverBeta =
      (-coverBeta*coverAlpha^5*(if (2:Fin 5)=i then 1 else 0) +
        coverAlpha^6*(if (4:Fin 5)=i then 1 else 0))/coverT :=
  fermat_cover_beta_derivative (coverPhysicalTangent i) _ _ _ _ _
    cover_fermat_relation coverT_ne_zero
    (coverPhysicalTangent_Y0 i) (coverPhysicalTangent_Y2 i)

theorem coverPhysicalTangent_sum (i : Fin 5) :
    coverPhysicalTangent i (coverY^2+coverT^2) =
      2*coverY*(if (3:Fin 5)=i then 1 else 0)+
        2*coverT*(coverAlpha^5*(if (2:Fin 5)=i then 1 else 0)+
          coverBeta^5*(if (4:Fin 5)=i then 1 else 0)) :=
  fermat_cover_sum_derivative (coverPhysicalTangent i) _ _ _ _ _ _ _
    cover_fermat_relation (coverPhysicalTangent_Y0 i)
    (coverPhysicalTangent_y i) (coverPhysicalTangent_Y2 i)

theorem coverPhysicalTangent_product (i : Fin 5) :
    coverPhysicalTangent i (coverY*coverT) =
      coverT*(if (3:Fin 5)=i then 1 else 0)+
        coverY*(coverAlpha^5*(if (2:Fin 5)=i then 1 else 0)+
          coverBeta^5*(if (4:Fin 5)=i then 1 else 0)) :=
  fermat_cover_product_derivative (coverPhysicalTangent i) _ _ _ _ _ _ _
    cover_fermat_relation (coverPhysicalTangent_Y0 i)
    (coverPhysicalTangent_y i) (coverPhysicalTangent_Y2 i)

def coverQuotientCoordinate : Fin 5 → CommonCoverFunctionField :=
  ![coverX1,coverX2,coverY^2+coverT^2,coverY*coverT,coverBeta]

/-- Defining the matrix by the actual derivatives makes its mixed-partial
identity immediate from the proved commutation of the physical lifts. -/
def actualCoverJacobian : Matrix (Fin 5) (Fin 5) CommonCoverFunctionField :=
  fun j i => coverPhysicalTangent i (coverQuotientCoordinate j)

theorem actualCoverJacobian_eq :
    actualCoverJacobian = coverResidueJacobian coverAlpha coverBeta coverY coverT := by
  rw [coverResidueJacobian_eq_matrix]
  ext j i
  fin_cases j <;> fin_cases i <;>
    norm_num [actualCoverJacobian, coverQuotientCoordinate, coverPhysicalTangent_sum,
      coverPhysicalTangent_product, coverPhysicalTangent_beta, coverPhysicalTangent_T,
      Fin.ext_iff]

theorem actualCoverJacobian_det :
    actualCoverJacobian.det = 2*coverAlpha^5*(coverT^2-coverY^2)/coverT := by
  rw [actualCoverJacobian_eq,
    coverResidueJacobian_det _ _ _ _ coverT_ne_zero cover_fermat_relation]

theorem actualCoverJacobian_det_ne_zero : actualCoverJacobian.det ≠ 0 := by
  rw [actualCoverJacobian_eq]
  exact coverResidueJacobian_det_ne_zero _ _ _ _ coverAlpha_ne_zero
    coverT_ne_zero cover_square_difference_ne_zero cover_fermat_relation

theorem actualCoverJacobian_mixed (i j k : Fin 5) :
    coverPhysicalTangent k (actualCoverJacobian j i) =
      coverPhysicalTangent i (actualCoverJacobian j k) :=
  coverPhysicalTangents_commute k i (coverQuotientCoordinate j)

def inverseCoverJacobian := actualCoverJacobian⁻¹

theorem actualCoverJacobian_mul_inverse : actualCoverJacobian*inverseCoverJacobian=1 := by
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr actualCoverJacobian_det_ne_zero)

theorem inverseCoverJacobian_mul_actual : inverseCoverJacobian*actualCoverJacobian=1 := by
  exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr actualCoverJacobian_det_ne_zero)

def coverQuotientTangent (j : Fin 5) :
    Derivation ℤ CommonCoverFunctionField CommonCoverFunctionField :=
  derivationLinearCombination coverPhysicalTangent (fun i => inverseCoverJacobian i j)

theorem coverQuotientTangent_apply (j : Fin 5) (r : CommonCoverFunctionField) :
    coverQuotientTangent j r = ∑ i, inverseCoverJacobian i j*coverPhysicalTangent i r :=
  derivationLinearCombination_apply _ _ _

theorem coverQuotientTangent_coordinate (j k : Fin 5) :
    coverQuotientTangent j (coverQuotientCoordinate k) = if k=j then 1 else 0 := by
  rw [coverQuotientTangent_apply]
  change (∑ i, inverseCoverJacobian i j*actualCoverJacobian k i) = _
  have h := congrFun (congrFun actualCoverJacobian_mul_inverse k) j
  simpa only [Matrix.mul_apply, Matrix.one_apply, mul_comm] using h

@[simp] theorem coverQuotientTangent_constant (j : Fin 5) (c : ℂ) :
    coverQuotientTangent j (algebraMap ℂ CommonCoverFunctionField c) = 0 := by
  rw [coverQuotientTangent_apply]
  simp

end HoldoutConstruction

#print axioms HoldoutConstruction.actualCoverJacobian_eq
#print axioms HoldoutConstruction.actualCoverJacobian_det_ne_zero
#print axioms HoldoutConstruction.coverQuotientTangent_coordinate
end
end
