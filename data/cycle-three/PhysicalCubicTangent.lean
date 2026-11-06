import Proposal.CyclicCubic
import Proposal.PhysicalNormalTransport
import HodgeComputer.Constructions.CyclicCubic.Map
import HodgeComputer.Constructions.CyclicCubic.Functorial

/-! The relative cubic derivation on the actual sextic function field.
All four passive parameters are fixed and y has derivative one. This supplies
the derivation required by the cubic covariant differential identity; it does
not posit an auxiliary parameter derivation on a specialized field.
Prepared with OpenAI Codex assistance for hodgepodgeconjecture. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace CyclePhysicalCubicTangent
open HoldoutConstruction CyclePhysical CyclePhysicalCoordinates CyclePhysicalNormalTransport
open scoped BigOperators
local notation "p" => coordinate
local instance : Algebra ℤ FunctionField := Ring.toIntAlgebra _

def secondPairedGradient : FunctionField := p 1*gradient 1+p 4*gradient 4
def cubicYNormal : FunctionField := 3*coeffB*y^2+coeffD*x^2+2*coeffE*y
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
  simp [coeffA,coeffB,coeffC,coeffD,coeffE,coeffF,t,map_add,
    Derivation.leibniz_div,Derivation.leibniz_pow,Derivation.leibniz,
    smul_eq_mul,nsmul_eq_mul,hv,hc1,hc2,h2]

lemma second_paired_gradient_identity :
    secondPairedGradient=2*radial^3*y*cubicYNormal := by
  have h0 := coordinate_ne_zero 0
  have h1 := coordinate_ne_zero 1
  have h2 := coordinate_ne_zero 2
  have h3 := coordinate_ne_zero 3
  simp only [secondPairedGradient,gradient,sextic,MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_pow,map_add,map_mul,map_pow,MvPolynomial.pderiv_C,
    MvPolynomial.pderiv_X,Pi.single_apply]
  norm_num [Fin.ext_iff,coordinate_X,map_ofNat,field_half]
  simp only [cubicYNormal,coeffB,coeffD,coeffE,radial,x,y,t,cOne,cTwo,ratio]
  field_simp
  ring

lemma derivative_x : derivative x= -cubicYNormal/cubicNormal := by
  rw [passive_parameters.2.2.2.2.2,second_paired_gradient_identity,paired_gradient_identity]
  have hx : x≠0 := div_ne_zero (pow_ne_zero _ (coordinate_ne_zero 0)) radial_ne_zero
  have hy := y_ne_zero
  have hr := radial_ne_zero
  have hg := cubic_normal_ne_zero
  field_simp

end CyclePhysicalCubicTangent
#print axioms CyclePhysicalCubicTangent.derivative_coordinate
#print axioms CyclePhysicalCubicTangent.passive_parameters
#print axioms CyclePhysicalCubicTangent.derivative_x
