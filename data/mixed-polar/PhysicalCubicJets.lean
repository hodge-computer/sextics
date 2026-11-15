import Proposal.CubicSourceJets
import Proposal.PhysicalTangent
import Proposal.PhysicalCovariantChart
import Proposal.PhysicalNormalTransport
import Proposal.JacobianScaling

/-! Instantiation of the balanced cubic first jet on the actual finite
quadratic extension of the fixed mixed-polar residue field. Every source,
normal, coefficient and derivative below is tied to that field. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace MixedPolarPhysicalCubicJets
open TransitiveCovariants MixedPolarPhysicalShear MixedPolarPhysicalTangent
local instance : Algebra ℤ Extension := Ring.toIntAlgebra _

abbrev Jets := MixedPolarCubicSourceJets.Data Extension
def data : Jets := ⟨a,b,c,d,e,k,X,y⟩
def xi : Extension := MixedPolarCubicSourceJets.xi data
def eta : Extension := MixedPolarCubicSourceJets.eta data
def aWeierstrass : Extension := MixedPolarCubicSourceJets.aWeierstrass data
def bWeierstrass : Extension := MixedPolarCubicSourceJets.bWeierstrass data
def xiDot : Extension := MixedPolarCubicSourceJets.xiDot data
def etaDot : Extension := MixedPolarCubicSourceJets.etaDot data
def aDot : Extension := MixedPolarCubicSourceJets.aDot data
def bDot : Extension := MixedPolarCubicSourceJets.bDot data

lemma hessian_nonzero : H a b c d e 0 X y 1 ≠ 0 := by
  have hk := k_relation
  simpa only [a,b,c,d,e,X,y,ι] using
    MixedPolarPhysicalCovariantChart.physical_H_nonzero k hk
lemma jacobian_nonzero : J a b c d e 0 X y 1 ≠ 0 := by
  have hk := k_relation
  simpa only [a,b,c,d,e,X,y,ι] using
    MixedPolarPhysicalCovariantChart.physical_J_nonzero k hk

lemma normal_data : MixedPolarCubicSourceJets.normal data=normal := rfl
lemma normal_dot_data : MixedPolarCubicSourceJets.normalDot data=
    ι MixedPolarPhysicalNormalTransport.cubicNormalJet := by
  change y-(X+k*y)*y*secondNormal/normal=_
  rw [normal_identity,second_normal_identity]
  simp only [MixedPolarPhysicalNormalTransport.cubicNormalJet,map_sub,map_mul,map_div₀]
  dsimp only [X,y]
  ring

lemma curve : eta^2=xi^3+aWeierstrass*xi+bWeierstrass :=
  MixedPolarCubicSourceJets.curve data cubic_equation normal_ne_zero hessian_nonzero
lemma eta_nonzero : eta ≠ 0 :=
  MixedPolarCubicSourceJets.eta_nonzero data hessian_nonzero jacobian_nonzero

lemma differential_value : normal*extendedDerivative xi=6*eta := by
  obtain ⟨ha,hb,hc,hd,he,hk⟩ := sheared_coefficient_constants
  exact MixedPolarCubicSourceJets.differential_value data extendedDerivative
    ha hb hc hd he hk extended_y cubic_equation normal_ne_zero hessian_nonzero
lemma invariant_differential : extendedDerivative xi/(2*eta)=3/normal := by
  have hh := differential_value
  have hg := normal_ne_zero
  have hη := eta_nonzero
  field_simp
  linear_combination hh
lemma xi_derivative_ne_zero : extendedDerivative xi ≠ 0 := by
  intro hz
  have hh := differential_value
  rw [hz,mul_zero] at hh
  exact (mul_ne_zero (by norm_num : (6:Extension)≠0) eta_nonzero) hh.symm

lemma aWeierstrass_formula : aWeierstrass=
    ι (MixedPolarScaling.reverseS4 MixedPolarPhysicalCoordinates.coeffA
      MixedPolarPhysicalCoordinates.coeffB MixedPolarPhysicalCoordinates.coeffC
      MixedPolarPhysicalCoordinates.coeffD MixedPolarPhysicalCoordinates.coeffE
      MixedPolarPhysicalCoordinates.coeffF) := by
  have hh := MixedPolarBalancedShear.s4_shear_numerator
    (ι MixedPolarPhysicalCoordinates.coeffA) (ι MixedPolarPhysicalCoordinates.coeffB)
    (ι MixedPolarPhysicalCoordinates.coeffC) (ι MixedPolarPhysicalCoordinates.coeffD)
    (ι MixedPolarPhysicalCoordinates.coeffE) (ι MixedPolarPhysicalCoordinates.coeffF) k k_relation
  change TransitiveCubic.s4 a b c d e 0=_
  unfold TransitiveCubic.s4
  have hn : TransitiveCubic.s4Numerator a b c d e 0=
      3*ι (MixedPolarScaling.reverseS4 MixedPolarPhysicalCoordinates.coeffA
        MixedPolarPhysicalCoordinates.coeffB MixedPolarPhysicalCoordinates.coeffC
        MixedPolarPhysicalCoordinates.coeffD MixedPolarPhysicalCoordinates.coeffE
        MixedPolarPhysicalCoordinates.coeffF) := by
    simpa only [a,b,c,d,e,MixedPolarBalancedShear.bPrime,MixedPolarBalancedShear.dPrime,
      MixedPolarBalancedShear.reverseS4,MixedPolarScaling.reverseS4,map_mul,map_sub,map_pow,map_ofNat] using hh
  rw [hn]
  ring

lemma bWeierstrass_formula : bWeierstrass=
    ι (-MixedPolarScaling.reverseS6 MixedPolarPhysicalCoordinates.coeffA
      MixedPolarPhysicalCoordinates.coeffB MixedPolarPhysicalCoordinates.coeffC
      MixedPolarPhysicalCoordinates.coeffD MixedPolarPhysicalCoordinates.coeffE
      MixedPolarPhysicalCoordinates.coeffF/4) := by
  have hh := MixedPolarBalancedShear.s6_shear_numerator
    (ι MixedPolarPhysicalCoordinates.coeffA) (ι MixedPolarPhysicalCoordinates.coeffB)
    (ι MixedPolarPhysicalCoordinates.coeffC) (ι MixedPolarPhysicalCoordinates.coeffD)
    (ι MixedPolarPhysicalCoordinates.coeffE) (ι MixedPolarPhysicalCoordinates.coeffF) k k_relation
  change -TransitiveCubic.s6 a b c d e 0/4=_
  unfold TransitiveCubic.s6
  have hn : TransitiveCubic.s6Numerator a b c d e 0=
      27*ι (MixedPolarScaling.reverseS6 MixedPolarPhysicalCoordinates.coeffA
        MixedPolarPhysicalCoordinates.coeffB MixedPolarPhysicalCoordinates.coeffC
        MixedPolarPhysicalCoordinates.coeffD MixedPolarPhysicalCoordinates.coeffE
        MixedPolarPhysicalCoordinates.coeffF) := by
    simpa only [a,b,c,d,e,MixedPolarBalancedShear.bPrime,MixedPolarBalancedShear.dPrime,
      MixedPolarBalancedShear.reverseS6,MixedPolarScaling.reverseS6,
      map_mul,map_sub,map_add,map_pow,map_ofNat] using hh
  rw [hn]
  simp only [map_neg,map_div₀,map_ofNat]
  ring

lemma aDot_formula : aDot=ι (MixedPolarScaling.dot4 MixedPolarPhysicalCoordinates.coeffA
    MixedPolarPhysicalCoordinates.coeffB MixedPolarPhysicalCoordinates.coeffC
    MixedPolarPhysicalCoordinates.coeffD MixedPolarPhysicalCoordinates.coeffE
    MixedPolarPhysicalCoordinates.coeffF) := by
  rw [aDot,MixedPolarCubicSourceJets.aDot_formula data d_ne_zero]
  have hh := MixedPolarBalancedShear.s4_first_variation
    (ι MixedPolarPhysicalCoordinates.coeffA) (ι MixedPolarPhysicalCoordinates.coeffB)
    (ι MixedPolarPhysicalCoordinates.coeffC) (ι MixedPolarPhysicalCoordinates.coeffD)
    (ι MixedPolarPhysicalCoordinates.coeffF) k k_relation
  simpa only [data,a,b,c,d,MixedPolarBalancedShear.bPrime,MixedPolarBalancedShear.dPrime,
    MixedPolarScaling.dot4,map_sub,map_mul,map_div₀,map_ofNat] using hh

lemma bDot_formula : bDot=ι (MixedPolarScaling.dotB MixedPolarPhysicalCoordinates.coeffA
    MixedPolarPhysicalCoordinates.coeffB MixedPolarPhysicalCoordinates.coeffC
    MixedPolarPhysicalCoordinates.coeffD MixedPolarPhysicalCoordinates.coeffE
    MixedPolarPhysicalCoordinates.coeffF) := by
  rw [bDot,MixedPolarCubicSourceJets.bDot_formula data d_ne_zero]
  simp only [data,a,c,d,e,MixedPolarScaling.dotB,map_mul,map_pow]
  ring

lemma weierstrass_constants : extendedDerivative aWeierstrass=0 ∧
    extendedDerivative bWeierstrass=0 := by
  obtain ⟨ha,hb,hc,hd,he,hk⟩ := sheared_coefficient_constants
  exact MixedPolarCubicSourceJets.weierstrass_constants data extendedDerivative ha hb hc hd he

/-- The exact physical balanced source after the auxiliary quadratic shear.
The right side contains the actual moving-map correction. -/
theorem source_transport :
    ι MixedPolarPhysicalNormalTransport.cubicNormalJet/ι MixedPolarPhysicalCoordinates.cubicNormal=
      (aDot*xi+bDot)/(2*eta^2)-(normal/3)*extendedDerivative (xiDot/(2*eta)) := by
  obtain ⟨ha,hb,hc,hd,he,hk⟩ := sheared_coefficient_constants
  have hh := MixedPolarCubicSourceJets.source_transport data extendedDerivative
    ha hb hc hd he hk extended_y cubic_equation d_ne_zero normal_ne_zero
    hessian_nonzero jacobian_nonzero
  rw [normal_dot_data,normal_data,normal_identity] at hh
  simpa only [normal_identity,aDot,bDot,xi,eta,xiDot] using hh

end MixedPolarPhysicalCubicJets
#print axioms MixedPolarPhysicalCubicJets.differential_value
#print axioms MixedPolarPhysicalCubicJets.source_transport
#print axioms MixedPolarPhysicalCubicJets.aDot_formula
#print axioms MixedPolarPhysicalCubicJets.bDot_formula
