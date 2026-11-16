import Proposal.PhysicalNonzero
import Proposal.QuadraticShear
import HodgeComputer.Constructions.TransitiveCubic.Cubic

/-! The actual finite quadratic shear of the fixed physical residue field.
This applies the generic algebraic extension to proved nonzero physical
coefficients; no extension or coefficient hypothesis is postulated. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace MixedPolarPhysicalShear
open MixedPolarPhysical MixedPolarPhysicalCoordinates
abbrev Extension := MixedPolarShear.Extension FunctionField coeffA coeffD coeffF
def ι : FunctionField →+* Extension := algebraMap FunctionField Extension
def k : Extension := MixedPolarShear.shear FunctionField coeffA coeffD coeffF
def a : Extension := ι coeffA
def b : Extension := ι coeffB+a*k^3+ι coeffD*k^2+ι coeffF*k
def c : Extension := ι coeffC
def d : Extension := ι coeffD+3*a*k
def e : Extension := ι coeffE
def X : Extension := ι MixedPolarPhysicalCoordinates.x-k*ι MixedPolarPhysicalCoordinates.y
def y : Extension := ι MixedPolarPhysicalCoordinates.y
def normal : Extension := 3*a*X^2+2*d*X*y
def yNormal : Extension := 3*b*y^2+d*X^2+2*e*y
def secondNormal : Extension := 6*a*X+2*d*y

lemma k_relation : 3*a*k^2+2*ι coeffD*k+ι coeffF=0 :=
  MixedPolarShear.shear_relation FunctionField coeffA coeffD coeffF coeffA_ne_zero
lemma d_ne_zero : d≠0 := by
  have he := MixedPolarShear.transformed_d FunctionField coeffA coeffD coeffF coeffA_ne_zero
  change d=MixedPolarShear.delta FunctionField coeffA coeffD coeffF at he
  rw [he]
  exact MixedPolarShear.delta_ne_zero FunctionField coeffA coeffD coeffF discriminant_ne_zero

lemma cubic_equation : TransitiveCubic.cubic a b c d e 0 X y 1=0 := by
  have he := congrArg ι MixedPolarPhysicalCoordinates.cubic_equation
  simp only [MixedPolarPhysicalCoordinates.cubic,map_add,map_mul,map_pow,map_one,map_zero] at he
  have hk := k_relation
  simp only [TransitiveCubic.cubic,a,b,c,d,e,X,y,zero_mul,add_zero,one_pow,mul_one]
  simp only [a] at hk
  linear_combination he-(ι MixedPolarPhysicalCoordinates.x-k*ι MixedPolarPhysicalCoordinates.y)*
    (ι MixedPolarPhysicalCoordinates.y)^2*hk

lemma normal_identity : normal=ι cubicNormal := by
  have hk := k_relation
  simp only [normal,a,d,X,y,cubicNormal,map_add,map_mul,map_pow,map_ofNat]
  simp only [a] at hk
  linear_combination -(ι MixedPolarPhysicalCoordinates.y)^2*hk

lemma normal_ne_zero : normal≠0 := by
  rw [normal_identity]
  simpa only [map_zero] using ι.injective.ne cubic_normal_ne_zero

lemma second_normal_identity : secondNormal=ι cubicSecondNormal := by
  simp only [secondNormal,a,d,X,y,cubicSecondNormal,map_add,map_mul,map_ofNat]
  ring

end MixedPolarPhysicalShear
#print axioms MixedPolarPhysicalShear.d_ne_zero
#print axioms MixedPolarPhysicalShear.cubic_equation
#print axioms MixedPolarPhysicalShear.normal_ne_zero
