import Proposal.BundleIncidence

/-! Scalar towers and endpoint coordinates in the selected finite conic field. -/

noncomputable section

namespace HoldoutBundle
open Polynomial HoldoutConstruction

instance coefficientField_baseAlgebra : Algebra BaseField CoefficientField := inferInstance
instance coefficientField_baseTower : IsScalarTower BaseField EndpointField CoefficientField :=
  inferInstance

theorem sourceMap_base (r : BaseRing) :
    sourceMap (algebraMap BaseRing IntegralEndpoint r)=
      algebraMap BaseField CoefficientField (baseFieldMap r) := by
  rw [sourceMap_generic,endpointGenericMap_base]
  exact (IsScalarTower.algebraMap_apply BaseField EndpointField CoefficientField _).symm

theorem conicA_base : conicA=algebraMap BaseField CoefficientField genericA :=
  sourceMap_base baseA

theorem conicB_base : conicB=algebraMap BaseField CoefficientField genericB :=
  sourceMap_base baseB

def baseFamily : ConicFamily (algebraMap BaseField CoefficientField genericA)
    (algebraMap BaseField CoefficientField genericB) conicEndpoint where
  coefficients := bundleCoefficients
  endpoint_relation := by rw [← conicA_base,← conicB_base]; exact conic_endpoint_relation
  endpoint_nonzero := conic_endpoint_nonzero
  equations := by rw [← conicA_base,← conicB_base]; exact bundleCoefficients_equations
  jacobian := by rw [← conicA_base,← conicB_base]; exact bundleCoefficients_jacobian

theorem conicEndpoint_root :
    conicEndpoint 0=algebraMap EndpointField CoefficientField
      (algebraMap GenericEndpoint EndpointField (endpointRoot genericA genericB)) := by
  change sourceMap (endpointRoot baseA baseB)=_
  rw [sourceMap_generic,endpointGenericMap_root]

theorem conicEndpoint_parameter (j : Fin 3) :
    conicEndpoint j.succ=algebraMap EndpointField CoefficientField
      (algebraMap GenericEndpoint EndpointField (endpointParameter genericA genericB j)) := by
  have hj : integralPoint j.succ=endpointParameter baseA baseB j := by
    fin_cases j <;> rfl
  unfold conicEndpoint
  rw [hj,sourceMap_generic,endpointGenericMap_parameter]

theorem coefficientField_trdeg : Algebra.trdeg BaseField CoefficientField=3 := by
  rw [finite_extension_trdeg BaseField EndpointField CoefficientField,endpointField_trdeg]

abbrev ConicFunctionField := FractionRing (Polynomial CoefficientField)

theorem conicFunctionField_trdeg : Algebra.trdeg BaseField ConicFunctionField=4 := by
  rw [polynomial_fractionRing_trdeg BaseField EndpointField,endpointField_trdeg]
  norm_num

instance conicFunctionField_essFiniteType : Algebra.EssFiniteType BaseField ConicFunctionField :=
  polynomial_fractionRing_essFiniteType BaseField EndpointField CoefficientField

end HoldoutBundle
