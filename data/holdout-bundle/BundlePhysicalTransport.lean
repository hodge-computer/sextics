import Proposal.BundlePhysicalCoordinates
import Proposal.BundleResidueClosure
import HodgeComputer.Constructions.HoldoutCover.PolynomialFamilyBridge
import HodgeComputer.Constructions.HoldoutCover.CoverSourceBinding
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
The complementary diagonal map on the actual protected function field.
The matrix is defined by actual residue derivations.  Its determinant and
inverse therefore retain the volume character and every tangent component.
Prepared with OpenAI ChatGPT collaborating-agent assistance.
-/

noncomputable section

namespace HoldoutBundle

open HoldoutConstruction MvPolynomial
open scoped BigOperators Matrix

attribute [local instance] holdoutCoordinateRing_isDomain

local instance : Algebra ℤ HoldoutFunctionField := Ring.toIntAlgebra _
local instance : CharZero HoldoutFunctionField :=
  charZero_of_injective_ringHom (f := algebraMap ℂ HoldoutFunctionField)
    (algebraMap ℂ HoldoutFunctionField).injective

section Block

variable {R : Type*} [Field R]

def diagonalTangentBlock (A : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 5) (Fin 5) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) R) 0 0 A)

theorem diagonalTangentBlock_det (A : Matrix (Fin 3) (Fin 3) R) :
    (diagonalTangentBlock A).det = A.det := by
  rw [diagonalTangentBlock, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, one_mul]

theorem diagonalTangentBlock_explicit (A : Matrix (Fin 3) (Fin 3) R) :
    diagonalTangentBlock A =
      !![1,0,0,0,0;
         0,1,0,0,0;
         0,0,A 0 0,A 0 1,A 0 2;
         0,0,A 1 0,A 1 1,A 1 2;
         0,0,A 2 0,A 2 1,A 2 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end Block

def physicalDiagonalJacobian : Matrix (Fin 5) (Fin 5) HoldoutFunctionField :=
  fun j i => physicalTangent i (physicalQuotientTail j)

theorem physicalDiagonalJacobian_eq :
    physicalDiagonalJacobian = diagonalTangentBlock
      (diagonalJacobian physicalI (physicalY 3) (physicalY 4) (physicalY 5)) := by
  rw [diagonalTangentBlock_explicit]
  ext j i
  fin_cases j <;> fin_cases i <;>
    norm_num [physicalDiagonalJacobian, physicalQuotientTail, physicalP, physicalQ,
      physicalLambda, diagonalJacobian, lambdaValue, Derivation.leibniz_div,
      Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, Fin.ext_iff,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, Matrix.cons_val] <;>
    try field_simp [physicalY4_ne_zero, physicalBranch_ne_zero] <;> ring

theorem physicalDiagonalJacobian_det :
    physicalDiagonalJacobian.det = -6*physicalLambda*physicalY 4 := by
  rw [physicalDiagonalJacobian_eq, diagonalTangentBlock_det,
    diagonalJacobian_det _ _ _ _ physicalY4_ne_zero physicalBranch_ne_zero]
  rfl

theorem physicalDiagonalJacobian_det_ne_zero : physicalDiagonalJacobian.det ≠ 0 := by
  rw [physicalDiagonalJacobian_eq, diagonalTangentBlock_det]
  exact diagonalJacobian_det_ne_zero _ _ _ _ physicalY4_ne_zero physicalBranch_ne_zero

theorem physicalDiagonalJacobian_mixed (i j k : Fin 5) :
    physicalTangent k (physicalDiagonalJacobian j i) =
      physicalTangent i (physicalDiagonalJacobian j k) :=
  physicalTangents_commute k i (physicalQuotientTail j)

def inversePhysicalDiagonalJacobian := physicalDiagonalJacobian⁻¹

theorem physicalDiagonalJacobian_mul_inverse :
    physicalDiagonalJacobian*inversePhysicalDiagonalJacobian = 1 := by
  exact Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr physicalDiagonalJacobian_det_ne_zero)

theorem inversePhysicalDiagonalJacobian_mul_actual :
    inversePhysicalDiagonalJacobian*physicalDiagonalJacobian = 1 := by
  exact Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr physicalDiagonalJacobian_det_ne_zero)

def physicalDiagonalTangent (j : Fin 5) :
    Derivation ℤ HoldoutFunctionField HoldoutFunctionField :=
  derivationLinearCombination physicalTangent
    (fun i => inversePhysicalDiagonalJacobian i j)

theorem physicalDiagonalTangent_apply (j : Fin 5) (x : HoldoutFunctionField) :
    physicalDiagonalTangent j x =
      ∑ i, inversePhysicalDiagonalJacobian i j*physicalTangent i x :=
  derivationLinearCombination_apply _ _ _

theorem physicalDiagonalTangent_coordinate (j k : Fin 5) :
    physicalDiagonalTangent j (physicalQuotientTail k) = if k=j then 1 else 0 := by
  rw [physicalDiagonalTangent_apply]
  change (∑ i, inversePhysicalDiagonalJacobian i j*physicalDiagonalJacobian k i) = _
  have h := congrFun (congrFun physicalDiagonalJacobian_mul_inverse k) j
  simpa only [Matrix.mul_apply, Matrix.one_apply, mul_comm] using h

@[simp] theorem physicalDiagonalTangent_constant (j : Fin 5) (c : ℂ) :
    physicalDiagonalTangent j (algebraMap ℂ HoldoutFunctionField c) = 0 := by
  rw [physicalDiagonalTangent_apply]
  simp

theorem physicalDiagonalTangent_lambda (j : Fin 4) :
    physicalDiagonalTangent j.castSucc physicalLambda = 0 := by
  have h := physicalDiagonalTangent_coordinate j.castSucc (Fin.last 4)
  have hj : (Fin.last 4 : Fin 5) ≠ j.castSucc := (Fin.castSucc_ne_last j).symm
  rw [show physicalQuotientTail (Fin.last 4) = physicalLambda by rfl, ite_eq_right hj] at h
  exact h

def physicalDiagonalDensity : HoldoutFunctionField :=
  densityValue physicalLambda (physicalY 0) physicalP

def physicalDiagonalDensityNormal : HoldoutFunctionField :=
  -(3*physicalY 0^2*physicalP)/(6*physicalLambda)

theorem Astar_partial : integerPartial 0 Astar = 3*X 0^2*X 3*X 4^2 := by
  norm_num [integerPartial_apply, Astar, MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_mul, Pi.single_apply, Fin.ext_iff]
  ring

theorem physical_Astar_value :
    physicalResidueMap Astar = physicalY 0^3*physicalY 3*physicalY 4^2 := by
  simp only [Astar, map_mul, map_pow, physicalY]

theorem physical_Astar_partial_value :
    physicalResidueMap (integerPartial 0 Astar) =
      3*physicalY 0^2*physicalY 3*physicalY 4^2 := by
  rw [Astar_partial]
  simp only [map_mul, map_pow, map_ofNat, physicalY]

theorem physical_diagonal_density_binding :
    physicalDiagonalJacobian.det * physicalDiagonalDensity = physicalResidueMap Astar := by
  rw [physicalDiagonalJacobian_det, physical_Astar_value]
  exact density_binding physicalI (physicalY 0) (physicalY 3) (physicalY 4) (physicalY 5)
    physicalY4_ne_zero physicalBranch_ne_zero

theorem physical_diagonal_density_normal_binding :
    physicalDiagonalJacobian.det * physicalDiagonalDensityNormal =
      physicalResidueMap (integerPartial 0 Astar) := by
  rw [physicalDiagonalJacobian_det, physical_Astar_partial_value]
  unfold physicalDiagonalDensityNormal physicalP
  field_simp [physicalLambda_ne_zero] <;> ring

theorem physical_normal_value :
    physicalNormal = 6*physicalY 0^5+3*physicalY 0^2*physicalY 1*physicalP := by
  rw [physicalNormal, cover_holdout_normal_polynomial]
  simp only [map_add, map_mul, map_pow, map_ofNat, physicalY, physicalP]
  ring

theorem physical_second_normal_value :
    physicalResidueMap (integerPartial 0 (integerPartial 0 holdoutSextic)) =
      30*physicalY 0^4+6*physicalY 0*physicalY 1*physicalP := by
  rw [cover_holdout_second_normal_polynomial]
  simp only [map_add, map_mul, map_pow, map_ofNat, physicalY, physicalP]
  ring

theorem physical_diagonal_normal_source_binding :
    physicalDiagonalJacobian.det *
      ((physicalDiagonalDensityNormal*physicalNormal-physicalDiagonalDensity*
        physicalResidueMap (integerPartial 0 (integerPartial 0 holdoutSextic)))) /
        physicalNormal^2 = physicalSourceFor Astar := by
  rw [mul_div_assoc]
  exact normal_source_binding_of_pair _ _ _ _ _ _ _
    physical_diagonal_density_binding physical_diagonal_density_normal_binding

end HoldoutBundle

#print axioms HoldoutBundle.physicalDiagonalJacobian_det
#print axioms HoldoutBundle.physical_diagonal_normal_source_binding
