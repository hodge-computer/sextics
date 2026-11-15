import Proposal.PhysicalTangent
import Proposal.PhysicalNormalTransport

/-! The divergence-free relative cubic direction on the mixed-polar
physical field. Adapted from fqlx's accepted mixed-biweight volume argument,
which credits hodgepodgeconjecture and the shared HoldoutCover machinery.
Prepared with OpenAI Codex assistance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace MixedPolarPhysicalCubicVolume
open HoldoutConstruction MixedPolarPhysical MixedPolarPhysicalCoordinates
open MixedPolarPhysicalNormalTransport MixedPolarPhysicalTangent
open scoped BigOperators
local instance : Algebra ℤ FunctionField := Ring.toIntAlgebra _
local notation "p" => coordinate

@[simp] lemma derivation_numeral {K : Type*} [CommRing K]
    (D : Derivation ℤ K K) (n : ℕ) [n.AtLeastTwo] :
    D (ofNat(n) : K)=0 := D.map_natCast n

lemma tangent_gradient_all (i : Fin 5) (j : Fin 6) :
    tangent i (gradient j)=hessian i.succ j-gradient i.succ/gradient 0*hessian 0 j :=
  tangent_apply i _

def weight : FunctionField := p 3^3/(4*p 0^5*p 1^2*p 2^2)
def volumeVector : Fin 5 → FunctionField :=
  ![weight*pairedGradient*p 1,0,-weight*secondPairedGradient*p 3,
    weight*pairedGradient*p 4,0]

theorem volume_divergence : residueDivergence tangent (gradient 0) volumeVector=0 := by
  have h0 := coordinate_ne_zero 0
  have h1 := coordinate_ne_zero 1
  have h2 := coordinate_ne_zero 2
  have hn : gradient 0≠0 := normal_ne_zero
  simp only [residueDivergence,fieldDivergence,volumeVector,
    Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.reduceSucc,
    Finset.univ_eq_empty,Finset.sum_empty,map_zero,zero_mul,zero_div,add_zero,
    weight,pairedGradient,secondPairedGradient,Derivation.leibniz_div,
    Derivation.leibniz_pow,Derivation.leibniz,map_add,map_neg,
    smul_eq_mul,nsmul_eq_mul,derivation_numeral,MixedPolarPhysicalTangent.tangent_coordinate,tangent_gradient_all]
  norm_num [Fin.ext_iff]
  simp only [hessian_commute 1 0,hessian_commute 3 0,hessian_commute 4 0,
    hessian_commute 3 1,hessian_commute 4 1,hessian_commute 4 3]
  field_simp
  ring

theorem volume_vector_identity (i : Fin 5) :
    volumeVector i=ratio^3*cubicNormal*velocity i.succ := by
  have h0 := coordinate_ne_zero 0
  have h1 := coordinate_ne_zero 1
  have h2 := coordinate_ne_zero 2
  have hr := radial_ne_zero
  have hx : x≠0 := div_ne_zero (pow_ne_zero _ h0) hr
  have hy := y_ne_zero
  have hh := paired_gradient_ne_zero
  have hg : cubicNormal=pairedGradient/(2*radial^3*x) := by
    apply (eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hr)) hx)).2
    linear_combination -paired_gradient_identity
  rw [hg]
  fin_cases i <;>
    norm_num [volumeVector,velocity,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,weight,ratio,radial,x,y] <;>
    field_simp <;> ring

lemma volume_direction (z : FunctionField) :
    (∑ i, volumeVector i*tangent i z)=ratio^3*cubicNormal*derivative z := by
  simp only [volume_vector_identity,Fin.sum_univ_succ,velocity,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.reduceSucc,
    Finset.univ_eq_empty,Finset.sum_empty,zero_mul,mul_zero,add_zero,
    derivative,Derivation.add_apply,Derivation.smul_apply,smul_eq_mul]
  norm_num [velocity,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
    Matrix.head_cons,Matrix.tail_cons]
  ring

section ProductRule
variable {K ι : Type*} [Field K] [Fintype ι]
lemma divergence_product (Ds : ι → Derivation ℤ K K) (g s : K) (w : ι → K) :
    residueDivergence Ds g (fun i => s*w i)=
      s*residueDivergence Ds g w+∑ i,w i*Ds i s := by
  simp only [residueDivergence,fieldDivergence,Derivation.leibniz,smul_eq_mul,
    Finset.sum_add_distrib,mul_assoc,← Finset.mul_sum]
  ring
end ProductRule

theorem correction_divergence (z : FunctionField) :
    residueDivergence tangent (gradient 0) (fun i => (z/3)*volumeVector i)=
      ratio^3*cubicNormal/3*derivative z := by
  rw [divergence_product,volume_divergence,mul_zero,zero_add]
  have hd (i : Fin 5) : tangent i (z/3)=tangent i z/3 := by
    rw [Derivation.leibniz_div]
    simp [smul_eq_mul]
    ring
  simp only [hd,← mul_div_assoc,← Finset.sum_div]
  rw [volume_direction]
  ring
end MixedPolarPhysicalCubicVolume
#print axioms MixedPolarPhysicalCubicVolume.volume_divergence
#print axioms MixedPolarPhysicalCubicVolume.correction_divergence

namespace MixedPolarExtendedVolume
open HoldoutConstruction MixedPolarPhysical MixedPolarPhysicalCoordinates
open MixedPolarPhysicalShear MixedPolarPhysicalTangent
open scoped BigOperators
local instance : Algebra ℤ FunctionField := Ring.toIntAlgebra _

def liftedTangent (i : Fin 5) : Derivation ℤ Extension Extension :=
  extendFiniteDerivation (MixedPolarPhysical.tangent i)
lemma lifted_on_base (i : Fin 5) (z : FunctionField) :
    liftedTangent i (ι z)=ι (MixedPolarPhysical.tangent i z) :=
  extendFiniteDerivation_apply _ z

def weightedDerivative : Derivation ℤ Extension Extension :=
  ι (velocity 1) • liftedTangent 0+ι (velocity 3) • liftedTangent 2+
    ι (velocity 4) • liftedTangent 3

lemma extended_derivative_eq : extendedDerivative=weightedDerivative := by
  apply finite_derivation_unique derivative
  · exact extended_on_base
  · intro z
    change weightedDerivative (ι z)=ι (derivative z)
    simp only [weightedDerivative,Derivation.add_apply,Derivation.smul_apply,
      smul_eq_mul,lifted_on_base,derivative,map_add,map_mul]

lemma extended_derivative_formula (z : Extension) :
    extendedDerivative z=∑ i : Fin 5,ι (velocity i.succ)*liftedTangent i z := by
  rw [extended_derivative_eq]
  simp only [weightedDerivative,Derivation.add_apply,Derivation.smul_apply,smul_eq_mul,
    Fin.sum_univ_succ,Fin.reduceSucc,Finset.univ_eq_empty,Finset.sum_empty,
    show velocity (2:Fin 6)=0 from rfl,show velocity (5:Fin 6)=0 from rfl,
    map_zero,zero_mul,add_zero]
  ring

def volumeVector (i : Fin 5) : Extension :=
  ι (MixedPolarPhysicalCubicVolume.volumeVector i)

lemma volume_divergence : residueDivergence liftedTangent (ι (gradient 0)) volumeVector=0 := by
  have h := residueDivergence_map ι MixedPolarPhysical.tangent liftedTangent
    lifted_on_base (gradient 0) MixedPolarPhysicalCubicVolume.volumeVector
  rw [MixedPolarPhysicalCubicVolume.volume_divergence,map_zero] at h
  exact h

lemma volume_direction (z : Extension) :
    (∑ i,volumeVector i*liftedTangent i z)=ι ratio^3*normal*extendedDerivative z := by
  simp only [volumeVector,MixedPolarPhysicalCubicVolume.volume_vector_identity,map_mul,map_pow]
  calc
    (∑ i,ι ratio^3*ι cubicNormal*ι (velocity i.succ)*liftedTangent i z)=
        (ι ratio^3*ι cubicNormal)*(∑ i,ι (velocity i.succ)*liftedTangent i z) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _=ι ratio^3*normal*extendedDerivative z := by
      rw [← extended_derivative_formula,normal_identity]

def balancedVector (i : Fin 5) : Extension := ι (cOne*cTwo)*volumeVector i

lemma passive_factor : extendedDerivative (ι (cOne*cTwo))=0 := by
  rw [extended_on_base]
  obtain ⟨hR,hv,hc1,hc2,hy,hx⟩ := passive_parameters
  simp [Derivation.leibniz,smul_eq_mul,hc1,hc2]

lemma balanced_divergence :
    residueDivergence liftedTangent (ι (gradient 0)) balancedVector=0 := by
  apply (MixedPolarBalanced.balanced_volume_direction liftedTangent extendedDerivative
    (ι (gradient 0)) normal (ι ratio^3) (ι (cOne*cTwo)) volumeVector
    volume_divergence volume_direction passive_factor).1

lemma balanced_direction (z : Extension) :
    (∑ i,balancedVector i*liftedTangent i z)=
      ι MixedPolarPhysicalNormalTransport.sourceFactor*normal*extendedDerivative z := by
  have h := (MixedPolarBalanced.balanced_volume_direction liftedTangent extendedDerivative
    (ι (gradient 0)) normal (ι ratio^3) (ι (cOne*cTwo)) volumeVector
    volume_divergence volume_direction passive_factor).2 z
  simpa only [balancedVector,MixedPolarPhysicalNormalTransport.sourceFactor,
    map_mul,map_pow] using h

theorem correction_divergence (z : Extension) :
    residueDivergence liftedTangent (ι (gradient 0)) (fun i => (z/3)*balancedVector i)=
      ι MixedPolarPhysicalNormalTransport.sourceFactor*normal/3*extendedDerivative z := by
  rw [MixedPolarPhysicalCubicVolume.divergence_product,balanced_divergence,mul_zero,zero_add]
  have hd (i : Fin 5) : liftedTangent i (z/3)=liftedTangent i z/3 := by
    rw [Derivation.leibniz_div]
    simp [smul_eq_mul]
    ring
  simp only [hd,← mul_div_assoc,← Finset.sum_div]
  rw [balanced_direction]
  ring

end MixedPolarExtendedVolume
#print axioms MixedPolarExtendedVolume.correction_divergence
