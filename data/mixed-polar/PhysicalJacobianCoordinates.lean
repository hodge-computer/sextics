import Proposal.PhysicalCubicVolume
import Proposal.PhysicalCubicJets
import Proposal.PhysicalJacobianGeometry
import Proposal.PhysicalJacobianCalculus
import Proposal.PhysicalJacobianVolumeIdentity
import HodgeComputer.Constructions.ResidueTransport.CoordinateIndependence

/-! The direct physical-to-Jacobian coordinates on the actual quadratic
extension. The arbitrary last row of the proved determinant formula retains
every passive derivative of the algebraic shear. Adapted from the accepted
calculation of fqlx and hodgepodgeconjecture with Codex assistance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace MixedPolarPhysicalJacobianCoordinates
open HoldoutConstruction MixedPolarPhysical MixedPolarPhysicalCoordinates
open MixedPolarPhysicalShear MixedPolarPhysicalTangent MixedPolarPhysicalCubicJets
open MixedPolarExtendedVolume MixedPolarJacobianGeometry
open scoped BigOperators
local instance : Algebra ℤ Extension := Ring.toIntAlgebra _
def liftedCoordinate (i : Fin 6) : Extension := ι (coordinate i)
def liftedGradient (i : Fin 6) : Extension := ι (gradient i)
local notation "p" => liftedCoordinate
def targetTime : Extension := ι parameterT
def targetX : Extension := (ι radial)^2*xi
def targetY : Extension := (ι radial)^3*eta
def passive : Fin 5 → Extension := ![targetTime,ι cOne,ι cTwo,ι radial,targetX]
def matrix : Matrix (Fin 5) (Fin 5) Extension := fun j i => liftedTangent i (passive j)

lemma lifted_coordinate_ne_zero (i : Fin 6) : p i≠0 := by
  change ι (coordinate i)≠0
  simpa only [map_zero] using ι.injective.ne (coordinate_ne_zero i)
lemma lifted_gradient_ne_zero : liftedGradient 0≠0 := by
  change ι (gradient 0)≠0
  have hn : gradient 0≠0 := MixedPolarPhysical.normal_ne_zero
  simpa only [map_zero] using ι.injective.ne hn
lemma lifted_radial_ne_zero : ι radial≠0 := by
  simpa only [map_zero] using ι.injective.ne radial_ne_zero
lemma lifted_ratio_ne_zero : ι ratio≠0 := by
  simpa only [map_zero] using ι.injective.ne ratio_ne_zero

lemma lifted_tangent_coordinate (i : Fin 5) (j : Fin 6) :
    liftedTangent i (p j)=(if j=i.succ then 1 else 0)-
      liftedGradient i.succ/liftedGradient 0*(if j=0 then 1 else 0) := by
  change liftedTangent i (ι (coordinate j))=_
  rw [lifted_on_base,MixedPolarPhysicalTangent.tangent_coordinate]
  by_cases hij : j=i.succ <;> by_cases hj : j=0 <;>
    simp [hij,hj,liftedGradient,map_sub,map_mul,map_div₀]

theorem matrix_formula :
    matrix=rawMatrix liftedCoordinate liftedGradient (fun i=>liftedTangent i xi) xi := by
  have h := MixedPolarJacobianCalculus.jacobian_formula liftedTangent liftedCoordinate
    liftedGradient xi (lifted_coordinate_ne_zero 0) (lifted_coordinate_ne_zero 1)
    (lifted_coordinate_ne_zero 2) (lifted_coordinate_ne_zero 3) lifted_gradient_ne_zero
    lifted_tangent_coordinate
  have hp : passive=MixedPolarJacobianCalculus.coordinates liftedCoordinate xi := by
    funext i
    fin_cases i <;>
      simp only [passive,targetTime,targetX,parameterT,t,radial,cOne,cTwo,ratio,
        MixedPolarJacobianCalculus.coordinates,liftedCoordinate,
        Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.reduceSucc,Matrix.cons_val,
        map_mul,map_pow,map_div₀] <;> ring
  rw [← hp] at h
  exact h

theorem determinant_volume : ι (gradient 0)*matrix.det=
    -48*(ι radial)^4*(∑ i,volumeVector i*liftedTangent i xi) := by
  rw [matrix_formula]
  have h := MixedPolarJacobianVolumeIdentity.determinant_volume liftedCoordinate liftedGradient
    (fun i=>liftedTangent i xi) xi (lifted_coordinate_ne_zero 0)
    (lifted_coordinate_ne_zero 1) (lifted_coordinate_ne_zero 2)
    (lifted_coordinate_ne_zero 3) lifted_gradient_ne_zero
  have hR : (liftedCoordinate 2)^2=ι radial := by simp only [liftedCoordinate,radial,map_pow]
  have hV : MixedPolarJacobianVolumeIdentity.volumeVector liftedCoordinate liftedGradient=
      volumeVector := by
    change MixedPolarJacobianVolumeIdentity.volumeVector (fun i=>ι (coordinate i))
      (fun i=>ι (gradient i))=(fun i=>ι (MixedPolarJacobianVolumeIdentity.volumeVector coordinate gradient i))
    exact MixedPolarJacobianVolumeIdentity.volumeVector_map ι coordinate gradient
  rw [hR,hV] at h
  exact h

theorem matrix_det_nonzero : matrix.det≠0 := by
  have he := determinant_volume
  rw [volume_direction] at he
  have hright : -48*(ι radial)^4*((ι ratio)^3*normal*extendedDerivative xi)≠0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ lifted_radial_ne_zero))
      (mul_ne_zero (mul_ne_zero (pow_ne_zero _ lifted_ratio_ne_zero)
        MixedPolarPhysicalShear.normal_ne_zero) xi_derivative_ne_zero)
  intro hz
  rw [hz,mul_zero] at he
  exact hright he.symm

lemma targetY_nonzero : targetY≠0 :=
  mul_ne_zero (pow_ne_zero _ lifted_radial_ne_zero) eta_nonzero

theorem density_multiplier : ι (gradient 0)*matrix.det/(2*targetY)=
    -144*(ι radial)*(ι ratio)^3 := by
  rw [determinant_volume,volume_direction]
  have he : (ι ratio)^3*normal*extendedDerivative xi=(ι ratio)^3*(6*eta) := by
    rw [mul_assoc,differential_value]
  rw [he]
  unfold targetY
  have hr := lifted_radial_ne_zero
  have hη := eta_nonzero
  field_simp
  ring

def inverse : Matrix (Fin 5) (Fin 5) Extension := matrix⁻¹
lemma matrix_inverse : matrix*inverse=1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr matrix_det_nonzero)
lemma inverse_matrix : inverse*matrix=1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr matrix_det_nonzero)
def coordinateDerivation (j : Fin 5) : Derivation ℤ Extension Extension :=
  ∑ k,inverse k j • liftedTangent k
lemma coordinateDerivation_apply (j : Fin 5) (z : Extension) :
    coordinateDerivation j z=∑ k,inverse k j*liftedTangent k z := by
  simp only [coordinateDerivation,Fin.sum_univ_succ,Finset.univ_eq_empty,Finset.sum_empty,
    Derivation.add_apply,Derivation.smul_apply,smul_eq_mul,Derivation.coe_zero,Pi.zero_apply,add_zero]
lemma coordinateDerivation_passive (j i : Fin 5) :
    coordinateDerivation j (passive i)=if i=j then 1 else 0 := by
  rw [coordinateDerivation_apply]
  have h := congrArg (fun A : Matrix (Fin 5) (Fin 5) Extension => A i j) matrix_inverse
  simpa only [Matrix.mul_apply,Matrix.one_apply,matrix,mul_comm] using h
lemma coordinateDerivation_constant (j : Fin 5) (c : ℂ) :
    coordinateDerivation j (ι (residueMap (MvPolynomial.C c)))=0 := by
  simp only [coordinateDerivation_apply,lifted_on_base,tangent_apply,
    MvPolynomial.pderiv_C,map_zero,mul_zero,sub_zero,Finset.sum_const_zero]
theorem coefficient_evaluation_injective :
    Function.Injective (MvPolynomial.eval₂Hom (ι.comp (residueMap.comp MvPolynomial.C)) passive) := by
  apply ResidueCoordinateIndependence.injective_of_coordinate_derivations
    (ι.comp (residueMap.comp MvPolynomial.C)) passive coordinateDerivation
  · exact coordinateDerivation_constant
  · exact coordinateDerivation_passive

lemma base_tangents_commute (i j : Fin 5) : Function.Commute (tangent i) (tangent j) :=
  residueTangent_commute (K:=FunctionField) projection projection_surjective
    (integerPartial 0) (integerPartial i.succ) (integerPartial j.succ) sextic
    projection_kernel MixedPolarPhysical.normal_ne_zero (integerPartial_commute i.succ 0)
    (integerPartial_commute j.succ 0) (integerPartial_commute i.succ j.succ)
lemma tangents_commute (i j : Fin 5) : Function.Commute (liftedTangent i) (liftedTangent j) :=
  extendFiniteDerivation_commute _ _ (base_tangents_commute i j)
lemma matrix_mixed (i j k : Fin 5) : liftedTangent k (matrix j i)=liftedTangent i (matrix j k) :=
  tangents_commute k i (passive j)
end MixedPolarPhysicalJacobianCoordinates
#print axioms MixedPolarPhysicalJacobianCoordinates.matrix_det_nonzero
#print axioms MixedPolarPhysicalJacobianCoordinates.density_multiplier
#print axioms MixedPolarPhysicalJacobianCoordinates.coefficient_evaluation_injective
