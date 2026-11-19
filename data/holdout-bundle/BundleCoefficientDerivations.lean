import Proposal.BundleCoefficientBase
import Proposal.BundleEndpointDerivations
import Proposal.BundleFlow

/-! Actual commuting coefficient derivations after the finite separable
incidence lift. This supplies the remaining endpoint and constant-field
obligations of the polynomial integration theorem. -/

noncomputable section

namespace HoldoutBundle
open Polynomial HoldoutConstruction

local instance : Algebra ℤ EndpointField := Ring.toIntAlgebra _
local instance : Algebra ℤ CoefficientField := Ring.toIntAlgebra _
local instance : Algebra ℤ ConicFunctionField := Ring.toIntAlgebra _

def coefficientDerivation (j : Fin 3) : Derivation ℤ CoefficientField CoefficientField :=
  extendFiniteDerivation (L := CoefficientField) (endpointTangent j)

theorem coefficientDerivation_endpoint (j : Fin 3) (r : EndpointField) :
    coefficientDerivation j (algebraMap EndpointField CoefficientField r) =
      algebraMap EndpointField CoefficientField (endpointTangent j r) :=
  extendFiniteDerivation_apply _ _

theorem coefficientDerivations_commute (i j : Fin 3) :
    Function.Commute (coefficientDerivation i) (coefficientDerivation j) :=
  extendFiniteDerivation_commute _ _ (endpointTangents_commute i j)

theorem coefficientDerivation_base (j : Fin 3) (r : BaseField) :
    coefficientDerivation j (algebraMap BaseField CoefficientField r) = 0 := by
  rw [IsScalarTower.algebraMap_apply BaseField EndpointField CoefficientField,
    coefficientDerivation_endpoint, endpointTangent_algebraMap, map_zero]

theorem coefficientDerivation_parameter (i j : Fin 3) :
    coefficientDerivation i (conicEndpoint j.succ) = if j = i then 1 else 0 := by
  rw [conicEndpoint_parameter, coefficientDerivation_endpoint, endpointTangent_parameter]
  split_ifs <;> simp

/-- The same concrete family with its coefficient-base embedding made
explicit in the type. Its polynomial coordinates are unchanged. -/
def genericConic :
    ConicFamily (algebraMap BaseField CoefficientField genericA)
      (algebraMap BaseField CoefficientField genericB) conicEndpoint where
  coefficients := bundleCoefficients
  endpoint_relation := by
    rw [← conicA_base, ← conicB_base]
    exact conic_endpoint_relation
  endpoint_nonzero := conic_endpoint_nonzero
  equations := by
    rw [← conicA_base, ← conicB_base]
    exact bundleCoefficients_equations
  jacobian := by
    rw [← conicA_base, ← conicB_base]
    exact bundleCoefficients_jacobian

theorem genericConic_curve : genericConic.curve = arithmeticFamily.curve := rfl

def conicSourceDerivation : Fin 4 → Derivation ℤ ConicFunctionField ConicFunctionField :=
  ConicFamily.sourceDerivation coefficientDerivation

theorem conicSourceDerivations_commute (i j : Fin 4) :
    Function.Commute (conicSourceDerivation i) (conicSourceDerivation j) :=
  ConicFamily.sourceDerivations_commute coefficientDerivation coefficientDerivations_commute i j

theorem conicEvaluationMatrix_det_ne_zero :
    (genericConic.evaluationMatrix coefficientDerivation).det ≠ 0 :=
  genericConic.evaluationMatrix_det_ne_zero coefficientDerivation coefficientDerivation_parameter

end HoldoutBundle

#print axioms HoldoutBundle.coefficientDerivations_commute
#print axioms HoldoutBundle.conicEvaluationMatrix_det_ne_zero
