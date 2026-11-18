import Proposal.BundleCoordinates
import Proposal.BundleResidueClosure

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

def physicalY (j : Fin 6) : HoldoutFunctionField := physicalResidueMap (X j)
def physicalI : HoldoutFunctionField := algebraMap ℂ HoldoutFunctionField Complex.I
def physicalBranch : HoldoutFunctionField := physicalY 3^3+physicalI*physicalY 5^3
def physicalLambda : HoldoutFunctionField :=
  lambdaValue physicalI (physicalY 3) (physicalY 4) (physicalY 5)
def physicalP : HoldoutFunctionField := physicalY 3*physicalY 4
def physicalQ : HoldoutFunctionField := physicalY 4*physicalY 5

theorem physicalI_sq : physicalI^2 = -1 := by
  rw [physicalI, ← map_pow, Complex.I_sq, map_neg, map_one]

theorem physicalY_equation :
    physicalY 0^6+physicalY 1^6+physicalY 2^6+
      physicalY 3^6+physicalY 4^6+physicalY 5^6+
      physicalY 0^3*physicalY 1*physicalY 3*physicalY 4+
      physicalY 1^3*physicalY 2*physicalY 4*physicalY 5 = 0 := by
  have h := (physicalResidueMap_kernel holdoutSextic).mpr (dvd_refl _)
  simp only [holdoutSextic, map_add, map_pow, map_mul] at h
  change physicalY 0^6+physicalY 0^3*physicalY 1*physicalY 3*physicalY 4+
    physicalY 1^6+physicalY 1^3*physicalY 2*physicalY 4*physicalY 5+
    physicalY 2^6+physicalY 3^6+physicalY 4^6+physicalY 5^6=0 at h
  linear_combination h

@[simp] theorem physicalTangent_Y_succ (i j : Fin 5) :
    physicalTangent i (physicalY j.succ) = if j=i then 1 else 0 := by
  rw [physicalY, physicalResidueMap_X_succ, physicalTangent_parameter]

@[simp] theorem physicalTangent_X1 (i : Fin 5) :
    physicalTangent i (physicalY 1) = if (0 : Fin 5)=i then 1 else 0 :=
  physicalTangent_Y_succ i 0

@[simp] theorem physicalTangent_X2 (i : Fin 5) :
    physicalTangent i (physicalY 2) = if (1 : Fin 5)=i then 1 else 0 :=
  physicalTangent_Y_succ i 1

@[simp] theorem physicalTangent_Y0 (i : Fin 5) :
    physicalTangent i (physicalY 3) = if (2 : Fin 5)=i then 1 else 0 :=
  physicalTangent_Y_succ i 2

@[simp] theorem physicalTangent_Y1 (i : Fin 5) :
    physicalTangent i (physicalY 4) = if (3 : Fin 5)=i then 1 else 0 :=
  physicalTangent_Y_succ i 3

@[simp] theorem physicalTangent_Y2 (i : Fin 5) :
    physicalTangent i (physicalY 5) = if (4 : Fin 5)=i then 1 else 0 :=
  physicalTangent_Y_succ i 4

@[simp] theorem physicalTangent_I (i : Fin 5) : physicalTangent i physicalI = 0 :=
  physicalTangent_algebraMap i Complex.I

theorem physicalY_succ_ne_zero (j : Fin 5) : physicalY j.succ ≠ 0 := by
  intro h
  have hd := physicalTangent_Y_succ j j
  rw [h, map_zero] at hd
  norm_num at hd

theorem physicalY4_ne_zero : physicalY 4 ≠ 0 := physicalY_succ_ne_zero 3

theorem physicalBranch_ne_zero : physicalBranch ≠ 0 := by
  intro h
  have hd := congrArg (physicalTangent 2) h
  have hdv : physicalTangent 2 physicalBranch = 3*physicalY 3^2 := by
    norm_num [physicalBranch, Derivation.leibniz, Derivation.leibniz_pow,
      smul_eq_mul, Fin.ext_iff]
  rw [hdv, map_zero] at hd
  exact (mul_ne_zero (by norm_num : (3 : HoldoutFunctionField) ≠ 0)
    (pow_ne_zero 2 (physicalY_succ_ne_zero 2))) hd

theorem physicalLambda_ne_zero : physicalLambda ≠ 0 :=
  lambdaValue_ne_zero physicalI (physicalY 3) (physicalY 4) (physicalY 5)
    physicalY4_ne_zero physicalBranch_ne_zero

theorem physical_quotient_equation :
    K (coeffA physicalLambda) (coeffB physicalI physicalLambda)
      ![physicalY 0,physicalY 1,physicalY 2,physicalP,physicalQ] = 0 := by
  exact (quotient_equation_binding physicalI physicalY physicalI_sq
    physicalY4_ne_zero physicalBranch_ne_zero).trans physicalY_equation

def physicalQuotientTail : Fin 5 → HoldoutFunctionField :=
  ![physicalY 1,physicalY 2,physicalP,physicalQ,physicalLambda]

end HoldoutBundle

#print axioms HoldoutBundle.physicalY_equation
#print axioms HoldoutBundle.physicalBranch_ne_zero
