import Proposal.ArithmeticEndpoint
import HodgeComputer.Constructions.PolynomialCurves.OpenIncidence
import Proposal.QuarticSeedIncidence

/-!
Arithmetic lifting of the exact free quartic to the generic complex endpoint.
The special fiber makes the doubly localized incidence nontrivial; etaleness,
flatness, and the injective endpoint map then give a finite separable generic
field factor. All 24 equations, the normal Jacobian, and the transverse
coefficient survive in that field factor.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace ReflectionCoupledFano.Arithmetic
open HoldoutConstruction

instance genericAlgebra : Algebra EndpointBase GenericEndpoint := genericMap.toAlgebra

def integralEquations : Index → MvPolynomial Index EndpointBase :=
  equations (algebraMap Base EndpointBase coupling) (Endpoint.point coupling)

abbrev GenericIncidence := OpenSquareGeneric GenericEndpoint integralEquations (1,0)

section SpecialFiber
variable {T : Type*} [Field T] [CharP T 5]

theorem integralEquations_specialize (j : T) (hj : j^2 = 2) (i : Index) :
    MvPolynomial.map (specialEndpointMap j hj) (integralEquations i) =
      equations 0 (modEndpoint j) i := by
  rw [integralEquations, equations_map]
  simp only [specialEndpointMap_coefficient, specialMap_coupling,
    specialEndpointMap_point, modEndpoint]

theorem integralDerivatives_specialize (j : T) (hj : j^2 = 2) (i k : Index) :
    MvPolynomial.map (specialEndpointMap j hj)
      (MvPolynomial.pderiv k (integralEquations i)) =
      MvPolynomial.pderiv k (equations 0 (modEndpoint j) i) := by
  rw [← MvPolynomial.pderiv_map, integralEquations_specialize]

theorem integralSeed_solution (j : T) (hj : j^2 = 2) (i : Index) :
    MvPolynomial.eval₂Hom (specialEndpointMap j hj) (modCoefficients j)
      (integralEquations i) = 0 := by
  have h := modEquations_zero hj i
  rw [← integralEquations_specialize j hj i, MvPolynomial.eval₂Hom_map_hom] at h
  simpa only [RingHom.id_comp] using h

theorem integralSeed_jacobian (j : T) (hj : j^2 = 2)
    (hunit : IsUnit (Matrix.det (fun i k : Index =>
      MvPolynomial.eval₂Hom (RingHom.id T) (modCoefficients j)
        (MvPolynomial.pderiv k (equations 0 (modEndpoint j) i))))) :
    IsUnit (Matrix.det (fun i k : Index =>
      MvPolynomial.eval₂Hom (specialEndpointMap j hj) (modCoefficients j)
        (MvPolynomial.pderiv i (integralEquations k)))) := by
  have he (i k : Index) :
      MvPolynomial.eval₂Hom (specialEndpointMap j hj) (modCoefficients j)
        (MvPolynomial.pderiv k (integralEquations i)) =
      MvPolynomial.eval₂Hom (RingHom.id T) (modCoefficients j)
        (MvPolynomial.pderiv k (equations 0 (modEndpoint j) i)) := by
    rw [← integralDerivatives_specialize j hj i k,
      MvPolynomial.eval₂Hom_map_hom, RingHom.id_comp]
  have hM : (fun i k : Index =>
      MvPolynomial.eval₂Hom (specialEndpointMap j hj) (modCoefficients j)
        (MvPolynomial.pderiv i (integralEquations k))) =
      Matrix.transpose (fun i k : Index =>
        MvPolynomial.eval₂Hom (RingHom.id T) (modCoefficients j)
          (MvPolynomial.pderiv k (equations 0 (modEndpoint j) i))) := by
    funext i k
    exact he k i
  rw [hM, Matrix.det_transpose]
  exact hunit

theorem exists_generic_field_of_seed (j : T) (hj : j^2 = 2)
    (hunit : IsUnit (Matrix.det (fun i k : Index =>
      MvPolynomial.eval₂Hom (RingHom.id T) (modCoefficients j)
        (MvPolynomial.pderiv k (equations 0 (modEndpoint j) i))))) :
    ∃ I : Ideal GenericIncidence, I.IsMaximal ∧
      Module.Finite GenericEndpoint (GenericIncidence ⧸ I) ∧
      Algebra.IsSeparable GenericEndpoint (GenericIncidence ⧸ I) ∧
      (∀ i, MvPolynomial.aeval
        (openGenericCoordinates integralEquations (1,0) I) (integralEquations i) = 0) ∧
      IsUnit (Matrix.det (fun i k => MvPolynomial.aeval
        (openGenericCoordinates integralEquations (1,0) I)
          (MvPolynomial.pderiv i (integralEquations k)))) ∧
      IsUnit (openGenericCoordinates integralEquations (1,0) I (1,0)) := by
  letI : Algebra EndpointBase T := (specialEndpointMap j hj).toAlgebra
  apply openSquare_exists_fieldFactor integralEquations (modCoefficients j)
    (integralSeed_solution j hj) (integralSeed_jacobian j hj hunit) (1,0)
    (isUnit_iff_ne_zero.mpr (modCoefficient_linear_ne_zero hj))
  exact genericMap_injective

end SpecialFiber
end ReflectionCoupledFano.Arithmetic

#print axioms ReflectionCoupledFano.Arithmetic.exists_generic_field_of_seed
