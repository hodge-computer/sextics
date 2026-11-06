import Proposal.PhysicalCubicVolume
import Proposal.CubicFieldDifferential
import HodgeComputer.Constructions.ResidueTransport.CoordinateIndependence
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! The direct Jacobian of the physical-to-Weierstrass coordinates.
Original cycle-three construction prepared with OpenAI Codex assistance.
Adapted to mixed-biweight for fqlx with OpenAI Codex assistance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace CyclePhysicalJacobianCoordinates
open scoped BigOperators

section Determinant
variable {K : Type*} [Field K]
def rawMatrix (p f : Fin 6 → K) (z : Fin 5 → K) (u : K) : Matrix (Fin 5) (Fin 5) K :=
  !![6*p 2^2*p 3^6*f 1/(p 0^7*f 0),
     2*p 2*p 3^6/p 0^6+6*p 2^2*p 3^6*f 2/(p 0^7*f 0),
     6*p 2^2*p 3^5/p 0^6+6*p 2^2*p 3^6*f 3/(p 0^7*f 0),
     6*p 2^2*p 3^6*f 4/(p 0^7*f 0),6*p 2^2*p 3^6*f 5/(p 0^7*f 0);
     -p 0*p 4/(p 1^2*p 3)-f 1/f 0*p 4/(p 1*p 3),
     -f 2/f 0*p 4/(p 1*p 3),
     -p 0*p 4/(p 1*p 3^2)-f 3/f 0*p 4/(p 1*p 3),
     p 0/(p 1*p 3)-f 4/f 0*p 4/(p 1*p 3),-f 5/f 0*p 4/(p 1*p 3);
     -f 1/f 0*p 5/(p 2*p 3),
     -p 0*p 5/(p 2^2*p 3)-f 2/f 0*p 5/(p 2*p 3),
     -p 0*p 5/(p 2*p 3^2)-f 3/f 0*p 5/(p 2*p 3),
     -f 4/f 0*p 5/(p 2*p 3),p 0/(p 2*p 3)-f 5/f 0*p 5/(p 2*p 3);
     0,2*p 2,0,0,0;
     p 2^4*z 0,p 2^4*z 1+4*p 2^3*u,p 2^4*z 2,p 2^4*z 3,p 2^4*z 4]

theorem raw_determinant (p f : Fin 6 → K) (z : Fin 5 → K) (u : K)
    (h0 : p 0≠0) (h1 : p 1≠0) (h2 : p 2≠0) (h3 : p 3≠0) (hf : f 0≠0) :
    (rawMatrix p f z u).det=
      -12*p 2^6*p 3^3/(p 0^5*p 1^2*f 0)*
        ((p 0*f 0+p 3*f 3)*p 1*z 0-p 3*(p 1*f 1+p 4*f 4)*z 2+
          (p 0*f 0+p 3*f 3)*p 4*z 3) := by
  rw [Matrix.det_succ_row _ (3:Fin 5)]
  have hrow (j : Fin 5) : rawMatrix p f z u 3 j=if j=1 then 2*p 2 else 0 := by
    fin_cases j <;> norm_num [rawMatrix,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons]
  simp_rw [hrow]
  simp only [mul_ite,ite_mul,mul_zero,zero_mul,Finset.sum_ite_eq',
    Finset.mem_univ,if_true]
  have hminor (A : Matrix (Fin 4) (Fin 4) K) :
      A.det=A 0 0*(A 1 1*A 2 2*A 3 3-A 1 1*A 2 3*A 3 2-A 1 2*A 2 1*A 3 3+
        A 1 2*A 2 3*A 3 1+A 1 3*A 2 1*A 3 2-A 1 3*A 2 2*A 3 1)-
      A 0 1*(A 1 0*A 2 2*A 3 3-A 1 0*A 2 3*A 3 2-A 1 2*A 2 0*A 3 3+
        A 1 2*A 2 3*A 3 0+A 1 3*A 2 0*A 3 2-A 1 3*A 2 2*A 3 0)+
      A 0 2*(A 1 0*A 2 1*A 3 3-A 1 0*A 2 3*A 3 1-A 1 1*A 2 0*A 3 3+
        A 1 1*A 2 3*A 3 0+A 1 3*A 2 0*A 3 1-A 1 3*A 2 1*A 3 0)-
      A 0 3*(A 1 0*A 2 1*A 3 2-A 1 0*A 2 2*A 3 1-A 1 1*A 2 0*A 3 2+
        A 1 1*A 2 2*A 3 0+A 1 2*A 2 0*A 3 1-A 1 2*A 2 1*A 3 0) := by
    rw [Matrix.det_succ_row_zero]
    simp only [Fin.sum_univ_succ,Matrix.det_fin_three,Matrix.submatrix_apply,
      Finset.univ_eq_empty,Finset.sum_empty,add_zero]
    norm_num only [Fin.val_zero,Fin.val_succ,Fin.val_one]
    simp only [Fin.succ_zero_eq_one,Fin.succ_one_eq_two,
      show (Fin.succAbove (0:Fin 4) (0:Fin 3))=(1:Fin 4) by decide,
      show (Fin.succAbove (0:Fin 4) (1:Fin 3))=(2:Fin 4) by decide,
      show (Fin.succAbove (0:Fin 4) (2:Fin 3))=(3:Fin 4) by decide,
      show (Fin.succAbove (1:Fin 4) (0:Fin 3))=(0:Fin 4) by decide,
      show (Fin.succAbove (1:Fin 4) (1:Fin 3))=(2:Fin 4) by decide,
      show (Fin.succAbove (1:Fin 4) (2:Fin 3))=(3:Fin 4) by decide,
      show (Fin.succAbove (2:Fin 4) (0:Fin 3))=(0:Fin 4) by decide,
      show (Fin.succAbove (2:Fin 4) (1:Fin 3))=(1:Fin 4) by decide,
      show (Fin.succAbove (2:Fin 4) (2:Fin 3))=(3:Fin 4) by decide,
      show (Fin.succAbove (3:Fin 4) (0:Fin 3))=(0:Fin 4) by decide,
      show (Fin.succAbove (3:Fin 4) (1:Fin 3))=(1:Fin 4) by decide,
      show (Fin.succAbove (3:Fin 4) (2:Fin 3))=(2:Fin 4) by decide,
      show (Fin.succ (0:Fin 3))=(1:Fin 4) by decide,
      show (Fin.succ (1:Fin 3))=(2:Fin 4) by decide,
      show (Fin.succ (2:Fin 3))=(3:Fin 4) by decide]
    ring
  rw [hminor]
  have hc : (-1:K)^((3:Fin 5).val+(1:Fin 5).val)=1 := by norm_num
  rw [hc,one_mul]
  change (2*p 2)*((rawMatrix p f z u 0 0)*((rawMatrix p f z u 1 2)*(rawMatrix p f z u 2 3)*(rawMatrix p f z u 4 4)-(rawMatrix p f z u 1 2)*(rawMatrix p f z u 2 4)*(rawMatrix p f z u 4 3)-(rawMatrix p f z u 1 3)*(rawMatrix p f z u 2 2)*(rawMatrix p f z u 4 4)+(rawMatrix p f z u 1 3)*(rawMatrix p f z u 2 4)*(rawMatrix p f z u 4 2)+(rawMatrix p f z u 1 4)*(rawMatrix p f z u 2 2)*(rawMatrix p f z u 4 3)-(rawMatrix p f z u 1 4)*(rawMatrix p f z u 2 3)*(rawMatrix p f z u 4 2))-(rawMatrix p f z u 0 2)*((rawMatrix p f z u 1 0)*(rawMatrix p f z u 2 3)*(rawMatrix p f z u 4 4)-(rawMatrix p f z u 1 0)*(rawMatrix p f z u 2 4)*(rawMatrix p f z u 4 3)-(rawMatrix p f z u 1 3)*(rawMatrix p f z u 2 0)*(rawMatrix p f z u 4 4)+(rawMatrix p f z u 1 3)*(rawMatrix p f z u 2 4)*(rawMatrix p f z u 4 0)+(rawMatrix p f z u 1 4)*(rawMatrix p f z u 2 0)*(rawMatrix p f z u 4 3)-(rawMatrix p f z u 1 4)*(rawMatrix p f z u 2 3)*(rawMatrix p f z u 4 0))+(rawMatrix p f z u 0 3)*((rawMatrix p f z u 1 0)*(rawMatrix p f z u 2 2)*(rawMatrix p f z u 4 4)-(rawMatrix p f z u 1 0)*(rawMatrix p f z u 2 4)*(rawMatrix p f z u 4 2)-(rawMatrix p f z u 1 2)*(rawMatrix p f z u 2 0)*(rawMatrix p f z u 4 4)+(rawMatrix p f z u 1 2)*(rawMatrix p f z u 2 4)*(rawMatrix p f z u 4 0)+(rawMatrix p f z u 1 4)*(rawMatrix p f z u 2 0)*(rawMatrix p f z u 4 2)-(rawMatrix p f z u 1 4)*(rawMatrix p f z u 2 2)*(rawMatrix p f z u 4 0))-(rawMatrix p f z u 0 4)*((rawMatrix p f z u 1 0)*(rawMatrix p f z u 2 2)*(rawMatrix p f z u 4 3)-(rawMatrix p f z u 1 0)*(rawMatrix p f z u 2 3)*(rawMatrix p f z u 4 2)-(rawMatrix p f z u 1 2)*(rawMatrix p f z u 2 0)*(rawMatrix p f z u 4 3)+(rawMatrix p f z u 1 2)*(rawMatrix p f z u 2 3)*(rawMatrix p f z u 4 0)+(rawMatrix p f z u 1 3)*(rawMatrix p f z u 2 0)*(rawMatrix p f z u 4 2)-(rawMatrix p f z u 1 3)*(rawMatrix p f z u 2 2)*(rawMatrix p f z u 4 0)))=_
  norm_num only [rawMatrix,Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
    Matrix.head_cons,Matrix.tail_cons,Matrix.cons_val_succ',Matrix.cons_val_zero',Function.comp_apply]
  field_simp
  ring
end Determinant

open HoldoutConstruction CyclePhysical CyclePhysicalCoordinates CyclePhysicalNormalTransport
open CyclePhysicalCubicTangent CyclePhysicalCubicVolume CycleCubicFieldDifferential.Physical
local instance : Algebra ℤ FunctionField := Ring.toIntAlgebra _
local notation "p" => coordinate
def targetTime : FunctionField := radial*t
def targetX : FunctionField := radial^2*xi
def targetY : FunctionField := radial^3*eta
def passive : Fin 5 → FunctionField := ![targetTime,cOne,cTwo,radial,targetX]
def matrix : Matrix (Fin 5) (Fin 5) FunctionField := fun j i => tangent i (passive j)

theorem matrix_formula : matrix=rawMatrix coordinate gradient (fun i=>tangent i xi) xi := by
  have h0 := coordinate_ne_zero 0
  have h1 := coordinate_ne_zero 1
  have h2 := coordinate_ne_zero 2
  have h3 := coordinate_ne_zero 3
  have hn : gradient 0≠0 := normal_ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [matrix,passive,targetTime,targetX,rawMatrix,t,radial,cOne,cTwo,ratio,
      Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.reduceSucc,Matrix.cons_val_one,Matrix.cons_val,
      Derivation.leibniz_div,Derivation.leibniz_pow,Derivation.leibniz,
      smul_eq_mul,nsmul_eq_mul,derivation_numeral,tangent_coordinate] <;>
    norm_num [Fin.ext_iff,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.head_cons,Matrix.tail_cons,Derivation.leibniz,Derivation.leibniz_pow,
      Derivation.leibniz_div,Derivation.leibniz_inv,
      smul_eq_mul,nsmul_eq_mul,tangent_coordinate] <;> try field_simp <;> ring
  all_goals first | rfl | simp

theorem determinant_volume : gradient 0*matrix.det=
    -48*radial^4*(∑ i,volumeVector i*tangent i xi) := by
  rw [matrix_formula,raw_determinant coordinate gradient (fun i=>tangent i xi) xi
    (coordinate_ne_zero 0) (coordinate_ne_zero 1) (coordinate_ne_zero 2)
    (coordinate_ne_zero 3) normal_ne_zero]
  have h0 := coordinate_ne_zero 0
  have h1 := coordinate_ne_zero 1
  have h2 := coordinate_ne_zero 2
  have hn : gradient 0≠0 := normal_ne_zero
  simp only [volumeVector,weight,pairedGradient,secondPairedGradient,radial,
    Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.reduceSucc,
    Finset.univ_eq_empty,Finset.sum_empty,zero_mul,add_zero]
  field_simp
  ring

theorem matrix_det_nonzero : matrix.det≠0 := by
  have he := determinant_volume
  rw [volume_direction] at he
  have hr : ratio≠0 := div_ne_zero (coordinate_ne_zero 3) (coordinate_ne_zero 0)
  have hright : -48*radial^4*(ratio^3*cubicNormal*derivative xi)≠0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ radial_ne_zero))
      (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr) cubic_normal_ne_zero) xi_derivative_ne_zero)
  intro hz
  rw [hz,mul_zero] at he
  exact hright he.symm

lemma eta_nonzero : eta≠0 :=
  div_ne_zero (neg_ne_zero.mpr CyclePhysicalChart.physical_jacobian_ne_zero)
    (mul_ne_zero (by norm_num) (pow_ne_zero _ CyclePhysicalChart.physical_hessian_ne_zero))
lemma targetY_nonzero : targetY≠0 :=
  mul_ne_zero (pow_ne_zero _ radial_ne_zero) eta_nonzero

theorem density_multiplier : gradient 0*matrix.det/(2*targetY)= -144*radial*ratio^3 := by
  have hd : cubicNormal*derivative xi=6*eta := by
    have h := invariant_differential
    have hg := cubic_normal_ne_zero
    have he := eta_nonzero
    field_simp at h
    linear_combination h
  rw [determinant_volume,volume_direction]
  have he : ratio^3*cubicNormal*derivative xi=ratio^3*(6*eta) := by
    rw [mul_assoc,hd]
  rw [he]
  unfold targetY
  have hr := radial_ne_zero
  have hη := eta_nonzero
  field_simp
  ring

def inverse : Matrix (Fin 5) (Fin 5) FunctionField := matrix⁻¹
lemma matrix_inverse : matrix*inverse=1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr matrix_det_nonzero)
lemma inverse_matrix : inverse*matrix=1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr matrix_det_nonzero)
def coordinateDerivation (j : Fin 5) : Derivation ℤ FunctionField FunctionField :=
  ∑ k,inverse k j • tangent k
lemma coordinateDerivation_apply (j : Fin 5) (z : FunctionField) :
    coordinateDerivation j z=∑ k,inverse k j*tangent k z := by
  simp only [coordinateDerivation,Fin.sum_univ_succ,Finset.univ_eq_empty,Finset.sum_empty,
    Derivation.add_apply,Derivation.smul_apply,smul_eq_mul,Derivation.coe_zero,Pi.zero_apply,add_zero]
lemma coordinateDerivation_passive (j i : Fin 5) :
    coordinateDerivation j (passive i)=if i=j then 1 else 0 := by
  rw [coordinateDerivation_apply]
  have h := congrArg (fun A : Matrix (Fin 5) (Fin 5) FunctionField => A i j) matrix_inverse
  simpa only [Matrix.mul_apply,Matrix.one_apply,matrix,mul_comm] using h
lemma coordinateDerivation_constant (j : Fin 5) (c : ℂ) :
    coordinateDerivation j (residueMap (MvPolynomial.C c))=0 := by
  simp only [coordinateDerivation_apply,tangent_apply,MvPolynomial.pderiv_C,map_zero,
    mul_zero,sub_zero,Finset.sum_const_zero]
theorem coefficient_evaluation_injective :
    Function.Injective (MvPolynomial.eval₂Hom (residueMap.comp MvPolynomial.C) passive) := by
  apply ResidueCoordinateIndependence.injective_of_coordinate_derivations
    (residueMap.comp MvPolynomial.C) passive coordinateDerivation
  · exact coordinateDerivation_constant
  · exact coordinateDerivation_passive

lemma tangents_commute (i j : Fin 5) : Function.Commute (tangent i) (tangent j) :=
  residueTangent_commute (K:=FunctionField) projection projection_surjective
    (integerPartial 0) (integerPartial i.succ) (integerPartial j.succ) sextic
    projection_kernel normal_ne_zero (integerPartial_commute i.succ 0)
    (integerPartial_commute j.succ 0) (integerPartial_commute i.succ j.succ)
lemma matrix_mixed (i j k : Fin 5) : tangent k (matrix j i)=tangent i (matrix j k) :=
  tangents_commute k i (passive j)

end CyclePhysicalJacobianCoordinates
#print axioms CyclePhysicalJacobianCoordinates.matrix_det_nonzero
#print axioms CyclePhysicalJacobianCoordinates.coefficient_evaluation_injective
