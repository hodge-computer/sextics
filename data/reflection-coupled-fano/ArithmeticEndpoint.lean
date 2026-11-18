import Proposal.ArithmeticBase
import Proposal.EndpointDomain
import Proposal.QuarticSeed

/-!
The same endpoint section over Z[1/7], over C, and at the finite-field
quartic. The ring maps keep the coupling fixed throughout specialization
and passage to the generic complex endpoint.
-/

noncomputable section
namespace ReflectionCoupledFano.Arithmetic
open Polynomial

abbrev EndpointBase := Endpoint.Ring coupling
abbrev ComplexEndpoint := Endpoint.Ring (complexMap coupling)
abbrev GenericEndpoint := Endpoint.Field (complexMap coupling)

def endpointMap : EndpointBase →+* ComplexEndpoint := Endpoint.map complexMap coupling

def genericMap : EndpointBase →+* GenericEndpoint :=
  (algebraMap ComplexEndpoint GenericEndpoint).comp endpointMap

theorem endpointMap_injective : Function.Injective endpointMap := by
  exact Endpoint.map_injective complexMap complexMap_injective coupling

theorem genericMap_injective : Function.Injective genericMap := by
  intro a b h
  apply endpointMap_injective
  apply IsFractionRing.injective ComplexEndpoint GenericEndpoint
  exact h

@[simp] theorem genericMap_point (i : Fin 6) :
    genericMap (Endpoint.point coupling i) =
      algebraMap ComplexEndpoint GenericEndpoint (Endpoint.point (complexMap coupling) i) := by
  fin_cases i <;> simp [genericMap, endpointMap, Endpoint.point]

@[simp] theorem genericMap_coefficient (r : Base) :
    genericMap (algebraMap Base EndpointBase r) =
      algebraMap ℂ GenericEndpoint (complexMap r) := by
  simp only [genericMap, RingHom.comp_apply, endpointMap, Endpoint.map_coefficient]
  exact (IsScalarTower.algebraMap_apply ℂ ComplexEndpoint GenericEndpoint (complexMap r)).symm

section SpecialFiber
variable {T : Type*} [Field T] [CharP T 5]

def specialCoefficientMap : MvPolynomial (Fin 4) Base →+* T :=
  MvPolynomial.eval₂Hom (specialMap T) ![0,0,1,1]

theorem specialEndpoint_relation {j : T} (hj : j^2 = 2) :
    (Endpoint.polynomial coupling).eval₂ (specialCoefficientMap (T := T)) j = 0 := by
  have h5 : (5 : T) = 0 := CharP.cast_eq_zero T 5
  have hj6 : j^6 = 8 := by calc
    j^6 = (j^2)^3 := by ring
    _ = 8 := by rw [hj]; norm_num
  simp only [Endpoint.polynomial, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
  norm_num [specialCoefficientMap, hj6, Matrix.cons_val]
  linear_combination 2*h5

def specialEndpointMap (j : T) (hj : j^2 = 2) : EndpointBase →+* T :=
  AdjoinRoot.lift (specialCoefficientMap (T := T)) j (specialEndpoint_relation hj)

@[simp] theorem specialEndpointMap_coefficient (j : T) (hj : j^2 = 2) (r : Base) :
    specialEndpointMap j hj (algebraMap Base EndpointBase r) = specialMap T r := by
  change specialEndpointMap j hj (AdjoinRoot.of _ (MvPolynomial.C r)) = _
  simp [specialEndpointMap, specialCoefficientMap]

@[simp] theorem specialEndpointMap_point (j : T) (hj : j^2 = 2) :
    (fun i => specialEndpointMap j hj (Endpoint.point coupling i)) = ![j,0,0,0,1,1] := by
  funext i
  fin_cases i <;>
    simp [specialEndpointMap, specialCoefficientMap, Endpoint.point,
      Endpoint.root, Endpoint.parameter]

end SpecialFiber
end ReflectionCoupledFano.Arithmetic

#print axioms ReflectionCoupledFano.Arithmetic.genericMap_injective
#print axioms ReflectionCoupledFano.Arithmetic.specialEndpointMap_point
