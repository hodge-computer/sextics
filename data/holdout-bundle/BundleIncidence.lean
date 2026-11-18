import Proposal.BundleBase
import Proposal.BundleConicLift
import Proposal.BundleFamily

/-!
The exact nonsingular conic incidence over the generic endpoint.  This file
selects a finite separable field factor, and identifies its coordinates with
the conic over the unchanged complementary diagonal quotient.
The finite incidence machinery is due to fqlx and hodgepodgeconjecture.
Prepared with OpenAI ChatGPT assistance.
-/

noncomputable section

namespace HoldoutBundle
open Polynomial HoldoutConstruction

def integralA : IntegralEndpoint := algebraMap BaseRing IntegralEndpoint baseA
def integralB : IntegralEndpoint := algebraMap BaseRing IntegralEndpoint baseB
def integralPoint : Fin 4 → IntegralEndpoint :=
  ![endpointRoot baseA baseB,endpointParameter baseA baseB 0,
    endpointParameter baseA baseB 1,endpointParameter baseA baseB 2]
def bundleEquations : Fin 12 → MvPolynomial (Fin 12) IntegralEndpoint :=
  equations integralA integralB integralPoint

@[simp] theorem integralSeed_A : integralEndpointSeedMap integralA=0 := by
  simp [integralA]

@[simp] theorem integralSeed_B : integralEndpointSeedMap integralB = -2 := by
  simp [integralB]

@[simp] theorem integralSeed_point (i : Fin 4) :
    integralEndpointSeedMap (integralPoint i)=complexEndpoint i := by
  fin_cases i <;> simp [integralPoint,complexEndpoint]

instance bundle_incidence_nontrivial : Nontrivial (SquareEtaleRing bundleEquations) :=
  conic_incidence_nontrivial integralA integralB integralPoint integralEndpointSeedMap
    integralSeed_A integralSeed_B integralSeed_point

abbrev BundleGenericIncidence := SquareGenericAlgebra EndpointField bundleEquations

theorem coefficientFactor_exists : ∃ I : Ideal BundleGenericIncidence, I.IsMaximal ∧
    Module.Finite EndpointField (BundleGenericIncidence ⧸ I) ∧
    Algebra.IsSeparable EndpointField (BundleGenericIncidence ⧸ I) := by
  obtain ⟨I,hi,hf,hs,_,_⟩ :=
    squareGeneric_exists_fieldFactor (K := EndpointField) bundleEquations
      (show Function.Injective (algebraMap IntegralEndpoint EndpointField) from
        endpointGenericMap_injective)
  exact ⟨I,hi,hf,hs⟩

def coefficientFactor : Ideal BundleGenericIncidence := Classical.choose coefficientFactor_exists

instance coefficientFactor_maximal : coefficientFactor.IsMaximal :=
  (Classical.choose_spec coefficientFactor_exists).1

abbrev CoefficientField := BundleGenericIncidence ⧸ coefficientFactor

instance coefficientField_field : Field CoefficientField := Ideal.Quotient.field _

instance coefficientField_finite : Module.Finite EndpointField CoefficientField :=
  (Classical.choose_spec coefficientFactor_exists).2.1

instance coefficientField_separable : Algebra.IsSeparable EndpointField CoefficientField :=
  (Classical.choose_spec coefficientFactor_exists).2.2

instance coefficientField_charZero : CharZero CoefficientField :=
  charZero_of_injective_ringHom (f := algebraMap EndpointField CoefficientField)
    (algebraMap EndpointField CoefficientField).injective

def sourceMap : IntegralEndpoint →+* CoefficientField :=
  algebraMap IntegralEndpoint CoefficientField

theorem sourceMap_generic (z : IntegralEndpoint) :
    sourceMap z=algebraMap EndpointField CoefficientField (endpointGenericMap z) :=
  IsScalarTower.algebraMap_apply IntegralEndpoint EndpointField CoefficientField z

theorem sourceMap_injective : Function.Injective sourceMap := by
  intro x y h
  apply endpointGenericMap_injective
  apply (algebraMap EndpointField CoefficientField).injective
  exact (sourceMap_generic x).symm.trans (h.trans (sourceMap_generic y))

def bundleCoefficients : Fin 12 → CoefficientField :=
  squareGenericCoordinates bundleEquations coefficientFactor

def conicA : CoefficientField := sourceMap integralA
def conicB : CoefficientField := sourceMap integralB
def conicEndpoint : Fin 4 → CoefficientField := fun i => sourceMap (integralPoint i)

theorem conicA_generic :
    conicA=algebraMap EndpointField CoefficientField
      (algebraMap BaseField EndpointField genericA) := by
  rw [conicA,integralA,sourceMap_generic,endpointGenericMap_base]

theorem conicB_generic :
    conicB=algebraMap EndpointField CoefficientField
      (algebraMap BaseField EndpointField genericB) := by
  rw [conicB,integralB,sourceMap_generic,endpointGenericMap_base]

theorem conic_endpoint_relation : endpoint conicA conicB conicEndpoint=0 := by
  change sourceMap (endpointRoot baseA baseB)^6+
    sourceMap (endpointParameter baseA baseB 0)^6+
    sourceMap (algebraMap BaseRing IntegralEndpoint baseA)*
      sourceMap (endpointParameter baseA baseB 1)^3+
    sourceMap (algebraMap BaseRing IntegralEndpoint baseB)*
      sourceMap (endpointParameter baseA baseB 2)^3=0
  have h := congrArg sourceMap (endpoint_relation baseA baseB)
  simpa only [map_add,map_pow,map_mul,map_zero] using h

theorem conic_endpoint_nonzero : conicEndpoint 0 ≠ 0 := by
  change sourceMap (endpointRoot baseA baseB) ≠ 0
  exact fun h => endpointRoot_ne_zero baseA baseB
    (sourceMap_injective (h.trans (map_zero sourceMap).symm))

theorem equations_map_to_field (i : Fin 12) :
    MvPolynomial.map sourceMap (bundleEquations i)=
      equations conicA conicB conicEndpoint i := by
  exact equations_map sourceMap integralA integralB integralPoint i

theorem bundleCoefficients_equations (i : Fin 12) :
    MvPolynomial.eval₂Hom (RingHom.id CoefficientField) bundleCoefficients
      (equations conicA conicB conicEndpoint i)=0 := by
  rw [← equations_map_to_field,MvPolynomial.eval₂Hom_map_hom,RingHom.id_comp]
  exact squareGeneric_solution bundleEquations coefficientFactor i

theorem bundleCoefficients_derivative (i j : Fin 12) :
    MvPolynomial.eval₂Hom (RingHom.id CoefficientField) bundleCoefficients
      (MvPolynomial.pderiv j (equations conicA conicB conicEndpoint i)) =
      MvPolynomial.aeval bundleCoefficients (MvPolynomial.pderiv j (bundleEquations i)) := by
  rw [← equations_map_to_field,MvPolynomial.pderiv_map,
    MvPolynomial.eval₂Hom_map_hom,RingHom.id_comp]
  rfl

theorem bundleCoefficients_jacobian :
    IsUnit (Matrix.det (fun i j : Fin 12 =>
      MvPolynomial.eval₂Hom (RingHom.id CoefficientField) bundleCoefficients
        (MvPolynomial.pderiv j (equations conicA conicB conicEndpoint i)))) := by
  let J : Matrix (Fin 12) (Fin 12) CoefficientField := fun i j =>
    MvPolynomial.aeval bundleCoefficients (MvPolynomial.pderiv i (bundleEquations j))
  have hM : (fun i j : Fin 12 =>
      MvPolynomial.eval₂Hom (RingHom.id CoefficientField) bundleCoefficients
        (MvPolynomial.pderiv j (equations conicA conicB conicEndpoint i)))=J.transpose := by
    funext i j
    exact bundleCoefficients_derivative i j
  rw [hM,Matrix.det_transpose]
  exact squareGeneric_jacobian bundleEquations coefficientFactor

def arithmeticFamily : ConicFamily conicA conicB conicEndpoint where
  coefficients := bundleCoefficients
  endpoint_relation := conic_endpoint_relation
  endpoint_nonzero := conic_endpoint_nonzero
  equations := bundleCoefficients_equations
  jacobian := bundleCoefficients_jacobian

end HoldoutBundle

#print axioms HoldoutBundle.arithmeticFamily
