import Proposal.PhysicalShear

/-! The actual relative cubic derivation on the mixed-polar residue field.
Adapted from the accepted tangent construction of hodgepodgeconjecture and
fqlx. Its finite extension fixes the actual algebraic shear coefficient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace MixedPolarPhysicalTangent
open HoldoutConstruction MixedPolarPhysical MixedPolarPhysicalCoordinates
open scoped BigOperators
local notation "p" => coordinate
local instance : Algebra ℤ FunctionField := Ring.toIntAlgebra _

def secondPairedGradient : FunctionField := p 1*gradient 1+p 4*gradient 4
def cubicYNormal : FunctionField := 3*coeffB*y^2+coeffD*x^2+2*coeffE*y+2*coeffF*x*y
def velocity : Fin 6 → FunctionField :=
  ![-p 0*secondPairedGradient/(2*y*pairedGradient),p 1/(2*y),0,
    -p 3*secondPairedGradient/(2*y*pairedGradient),p 4/(2*y),0]
def derivative : Derivation ℤ FunctionField FunctionField :=
  velocity 1 • tangent 0+velocity 3 • tangent 2+velocity 4 • tangent 3

lemma y_ne_zero : y≠0 :=
  div_ne_zero (pow_ne_zero _ (coordinate_ne_zero 1)) radial_ne_zero

lemma tangent_coordinate (i : Fin 5) (j : Fin 6) :
    tangent i (p j)=(if j=i.succ then 1 else 0)-
      gradient i.succ/gradient 0*(if j=0 then 1 else 0) := by
  rw [coordinate,tangent_apply]
  simp only [MvPolynomial.pderiv_X,Pi.single_apply,apply_ite,map_one,map_zero,gradient]
  split_ifs <;> rfl

lemma derivative_coordinate (j : Fin 6) : derivative (p j)=velocity j := by
  have hy := y_ne_zero
  have hh := paired_gradient_ne_zero
  have hf : gradient 0≠0 := normal_ne_zero
  have he : pairedGradient=p 0*gradient 0+p 3*gradient 3 := rfl
  have hb : secondPairedGradient=p 1*gradient 1+p 4*gradient 4 := rfl
  fin_cases j <;>
    simp only [derivative,Derivation.add_apply,Derivation.smul_apply,smul_eq_mul,
      tangent_coordinate,velocity,Matrix.cons_val_zero,
      Matrix.cons_val_succ,Fin.reduceSucc,Matrix.cons_val_one,Matrix.cons_val,
      Finset.sum_const_zero,Finset.univ_eq_empty,Finset.sum_empty] <;>
    norm_num [Fin.ext_iff] <;>
    field_simp <;> simp only [pairedGradient,secondPairedGradient] <;> ring

lemma derivative_constant (c : ℂ) : derivative (residueMap (MvPolynomial.C c))=0 := by
  simp only [derivative,Derivation.add_apply,Derivation.smul_apply,smul_eq_mul,
    tangent_apply,MvPolynomial.pderiv_C,map_zero,mul_zero,div_zero,sub_zero,
    Finset.sum_const_zero,add_zero]

lemma passive_parameters :
    derivative radial=0 ∧ derivative ratio=0 ∧ derivative cOne=0 ∧ derivative cTwo=0 ∧
      derivative y=1 ∧ derivative x= -x*secondPairedGradient/(y*pairedGradient) := by
  have h0 := coordinate_ne_zero 0
  have h1 := coordinate_ne_zero 1
  have h2 := coordinate_ne_zero 2
  have h3 := coordinate_ne_zero 3
  have hy := y_ne_zero
  have hh := paired_gradient_ne_zero
  have hr := radial_ne_zero
  simp only [radial,ratio,cOne,cTwo,x,y,Derivation.leibniz_div,
    Derivation.leibniz_pow,smul_eq_mul,nsmul_eq_mul,derivative_coordinate,
    velocity,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.reduceSucc,
    Matrix.cons_val_one,Matrix.cons_val]
  repeat' apply And.intro
  all_goals norm_num <;> field_simp <;> ring
  all_goals simp

lemma coefficient_constants :
    derivative coeffA=0 ∧ derivative coeffB=0 ∧ derivative coeffC=0 ∧
      derivative coeffD=0 ∧ derivative coeffE=0 ∧ derivative coeffF=0 := by
  obtain ⟨hR,hv,hc1,hc2,hy,hx⟩ := passive_parameters
  have h2 : derivative (2:FunctionField)=0 := derivative.map_natCast 2
  have h3 : derivative (3:FunctionField)=0 := derivative.map_natCast 3
  simp [coeffA,coeffB,coeffC,coeffD,coeffE,coeffF,t,map_add,
    Derivation.leibniz_div,Derivation.leibniz_pow,Derivation.leibniz,
    smul_eq_mul,nsmul_eq_mul,hv,hc1,hc2,h2,h3]

lemma second_paired_gradient_identity :
    secondPairedGradient=2*radial^3*y*cubicYNormal := by
  have h0 := coordinate_ne_zero 0
  have h1 := coordinate_ne_zero 1
  have h2 := coordinate_ne_zero 2
  have h3 := coordinate_ne_zero 3
  simp only [secondPairedGradient,gradient,sextic,MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_pow,map_add,map_mul,map_pow,MvPolynomial.pderiv_C,
    MvPolynomial.pderiv_X,Pi.single_apply]
  norm_num [Fin.ext_iff,coordinate_X,map_ofNat,field_half,field_third]
  simp only [cubicYNormal,coeffB,coeffD,coeffE,coeffF,radial,x,y,t,cOne,cTwo,ratio]
  field_simp
  ring

lemma derivative_x : derivative x= -cubicYNormal/cubicNormal := by
  rw [passive_parameters.2.2.2.2.2,second_paired_gradient_identity,paired_gradient_identity]
  have hx : x≠0 := div_ne_zero (pow_ne_zero _ (coordinate_ne_zero 0)) radial_ne_zero
  have hy := y_ne_zero
  have hr := radial_ne_zero
  have hg := cubic_normal_ne_zero
  field_simp

open MixedPolarPhysicalShear

def extendedDerivative : Derivation ℤ Extension Extension :=
  extendFiniteDerivation derivative
lemma extended_on_base (value : FunctionField) :
    extendedDerivative (ι value)=ι (derivative value) :=
  extendFiniteDerivation_apply derivative value

lemma sheared_coefficient_constants :
    extendedDerivative a=0 ∧ extendedDerivative b=0 ∧ extendedDerivative c=0 ∧
      extendedDerivative d=0 ∧ extendedDerivative e=0 ∧ extendedDerivative k=0 := by
  obtain ⟨ha,hb,hc,hd,he,hf⟩ := coefficient_constants
  have hk : extendedDerivative k=0 :=
    MixedPolarShear.shear_constant FunctionField coeffA coeffD coeffF derivative ha hd hf
  have h3 : extendedDerivative (3:Extension)=0 := extendedDerivative.map_natCast 3
  repeat' apply And.intro
  all_goals simp [a,b,c,d,e,Derivation.leibniz,Derivation.leibniz_pow,map_add,
    extended_on_base,ha,hb,hc,hd,he,hf,hk,h3,smul_eq_mul,nsmul_eq_mul]

lemma extended_y : extendedDerivative MixedPolarPhysicalShear.y=1 := by
  rw [MixedPolarPhysicalShear.y,extended_on_base,passive_parameters.2.2.2.2.1,map_one]

lemma extended_X : extendedDerivative X= -yNormal/normal := by
  obtain ⟨ha,hb,hc,hd,he,hk⟩ := sheared_coefficient_constants
  have h := congrArg extendedDerivative MixedPolarPhysicalShear.cubic_equation
  have hone : extendedDerivative (1:Extension)=0 := extendedDerivative.map_one_eq_zero
  simp only [TransitiveCubic.cubic,map_add,Derivation.leibniz,Derivation.leibniz_pow,
    smul_eq_mul,nsmul_eq_mul,ha,hb,hc,hd,he,extended_y,map_zero,hone,
    zero_mul,mul_zero,zero_add,add_zero,pow_one,one_pow,mul_one] at h
  norm_num at h
  apply (eq_div_iff MixedPolarPhysicalShear.normal_ne_zero).mpr
  unfold normal yNormal
  linear_combination h

end MixedPolarPhysicalTangent
#print axioms MixedPolarPhysicalTangent.derivative_coordinate
#print axioms MixedPolarPhysicalTangent.passive_parameters
#print axioms MixedPolarPhysicalTangent.derivative_x

#print axioms MixedPolarPhysicalTangent.sheared_coefficient_constants
#print axioms MixedPolarPhysicalTangent.extended_X
