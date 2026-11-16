import Proposal.PhysicalCubicJets
import Proposal.JacobianScaling

/-! Exact bindings of the physical covariant Jacobian and balanced source
to the polynomial family model. All algebraic shear coefficients disappear
from these identities before the polynomial-family primitive is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace MixedPolarPhysicalJacobianCoefficients
open MixedPolarPhysicalCoordinates MixedPolarPhysicalShear MixedPolarPhysicalCubicJets

lemma parameterT_scaling : ι parameterT=ι radial*(ι ratio)^6 := by
  simp only [parameterT,t,map_mul,map_pow]

lemma a432_div_scaling :
    MixedPolarJacobian.a432 (ι cOne) (ι cTwo) (ι radial) (ι parameterT)/432=
      (ι radial)^4*aWeierstrass := by
  rw [parameterT_scaling,MixedPolarScaling.model_a432,MixedPolarScaling.a4_scaling,
    aWeierstrass_formula]
  simp only [MixedPolarScaling.reverseS4,coeffA,coeffB,coeffC,coeffD,coeffE,coeffF,t,
    map_add,map_sub,map_mul,map_pow,map_div₀,map_ofNat,map_one]
  ring

lemma b432_div_scaling :
    MixedPolarJacobian.b432 (ι cOne) (ι cTwo) (ι radial) (ι parameterT)/432=
      (ι radial)^6*bWeierstrass := by
  rw [parameterT_scaling,MixedPolarScaling.model_b432,MixedPolarScaling.b6_scaling,
    bWeierstrass_formula]
  simp only [MixedPolarScaling.reverseS6,coeffA,coeffB,coeffC,coeffD,coeffE,coeffF,t,
    map_add,map_sub,map_mul,map_pow,map_div₀,map_ofNat,map_one,map_neg]
  ring

lemma a8_scaling :
    MixedPolarJacobian.a8 (ι cOne) (ι cTwo) 1 (ι radial) (ι parameterT)=
      432*(ι radial)^4*aWeierstrass := by
  have hh := a432_div_scaling
  field_simp at hh
  change MixedPolarJacobian.a432 (ι cOne) (ι cTwo) (ι radial) (ι parameterT)=_
  linear_combination hh

lemma b256_scaling :
    MixedPolarJacobian.b256 (ι cOne) (ι cTwo) 1 (ι radial) (ι parameterT)=
      432*(ι radial)^6*bWeierstrass := by
  have hh := b432_div_scaling
  field_simp at hh
  change MixedPolarJacobian.b432 (ι cOne) (ι cTwo) (ι radial) (ι parameterT)=_
  linear_combination hh

lemma jacobian_source_scaling :
    MixedPolarScaling.jacobianSource (ι cOne) (ι cTwo) (ι radial)
      (ι parameterT) ((ι radial)^2*xi)=
      ι (cOne*cTwo)*(ι radial)^5/144*(aDot*xi+bDot) := by
  rw [parameterT_scaling,MixedPolarScaling.source_scaling,aDot_formula,bDot_formula]
  simp only [MixedPolarScaling.dot4,MixedPolarScaling.dotB,coeffA,coeffB,coeffC,
    coeffD,coeffE,coeffF,t,map_add,map_sub,map_mul,map_pow,map_div₀,map_ofNat,map_one]
  ring

lemma source_scaling :
    MixedPolarScaling.jacobianSource (ι cOne) (ι cTwo) (ι radial)
      (ι parameterT) ((ι radial)^2*xi)=
      ι (cOne*cTwo)*(ι radial)^5/144*(aDot*xi+bDot) := jacobian_source_scaling

end MixedPolarPhysicalJacobianCoefficients
#print axioms MixedPolarPhysicalJacobianCoefficients.a8_scaling
#print axioms MixedPolarPhysicalJacobianCoefficients.b256_scaling
#print axioms MixedPolarPhysicalJacobianCoefficients.jacobian_source_scaling
