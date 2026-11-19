import Proposal.ArithmeticLifting
import Proposal.QuarticFamily

/-!
The generic field factor of the arithmetic incidence gives an actual
quartic family for the fixed complex coupling. The scalar-map identities
below identify its endpoint and every coefficient equation with the
characteristic-zero family, rather than replacing the target equation by
an unrelated deformation.
-/

noncomputable section
namespace ReflectionCoupledFano.Arithmetic
open Polynomial HoldoutConstruction

attribute [local irreducible] Endpoint.polynomial integralEquations coupling complexMap

abbrev CoefficientField (I : Ideal GenericIncidence) := GenericIncidence ⧸ I

instance coefficientField_commRing (I : Ideal GenericIncidence) :
    CommRing (CoefficientField I) := inferInstance

noncomputable instance coefficientField_field (I : Ideal GenericIncidence) [I.IsMaximal] :
    Field (CoefficientField I) := Ideal.Quotient.field I

instance coefficientField_charZero (I : Ideal GenericIncidence) [I.IsMaximal] :
    CharZero (CoefficientField I) :=
  charZero_of_injective_ringHom (f := algebraMap GenericEndpoint (CoefficientField I))
    (algebraMap GenericEndpoint (CoefficientField I)).injective

noncomputable instance coefficientField_complexAlgebra (I : Ideal GenericIncidence) :
    Algebra ℂ (CoefficientField I) := inferInstance

instance coefficientField_complexTower (I : Ideal GenericIncidence) :
    IsScalarTower ℂ GenericEndpoint (CoefficientField I) := inferInstance

def sourceMap (I : Ideal GenericIncidence) : EndpointBase →+* CoefficientField I :=
  algebraMap EndpointBase (CoefficientField I)

theorem sourceMap_generic (I : Ideal GenericIncidence) (a : EndpointBase) :
    sourceMap I a = algebraMap GenericEndpoint (CoefficientField I) (genericMap a) :=
  IsScalarTower.algebraMap_apply EndpointBase GenericEndpoint (CoefficientField I) a

@[simp] theorem sourceMap_coefficient (I : Ideal GenericIncidence) (r : Base) :
    sourceMap I (algebraMap Base EndpointBase r) =
      algebraMap ℂ (CoefficientField I) (complexMap r) := by
  rw [sourceMap_generic, genericMap_coefficient]
  exact (IsScalarTower.algebraMap_apply ℂ GenericEndpoint (CoefficientField I)
    (complexMap r)).symm

@[simp] theorem sourceMap_point (I : Ideal GenericIncidence) [I.IsMaximal] (i : Fin 6) :
    sourceMap I (Endpoint.point coupling i) =
      familyEndpoint (complexMap coupling) (CoefficientField I) i := by
  rw [sourceMap_generic, genericMap_point]
  rfl

def coefficients (I : Ideal GenericIncidence) : Index → CoefficientField I :=
  openGenericCoordinates integralEquations (1,0) I

theorem equations_map_to_field (I : Ideal GenericIncidence) [I.IsMaximal] (i : Index) :
    MvPolynomial.map (sourceMap I) (integralEquations i) =
      equations (algebraMap ℂ (CoefficientField I) (complexMap coupling))
        (familyEndpoint (complexMap coupling) (CoefficientField I)) i := by
  have he : integralEquations i =
      equations (algebraMap Base EndpointBase coupling) (Endpoint.point coupling) i := by
    unfold integralEquations
    rfl
  rw [he, equations_map, sourceMap_coefficient]
  congr 1
  funext i
  exact sourceMap_point I i

theorem coefficients_equations (I : Ideal GenericIncidence) [I.IsMaximal] (i : Index) :
    MvPolynomial.eval₂Hom (RingHom.id (CoefficientField I)) (coefficients I)
      (equations (algebraMap ℂ (CoefficientField I) (complexMap coupling))
        (familyEndpoint (complexMap coupling) (CoefficientField I)) i) = 0 := by
  rw [← equations_map_to_field, MvPolynomial.eval₂Hom_map_hom, RingHom.id_comp]
  exact openGeneric_solution integralEquations (1,0) I i

theorem coefficients_derivative (I : Ideal GenericIncidence) [I.IsMaximal] (i j : Index) :
    MvPolynomial.eval₂Hom (RingHom.id (CoefficientField I)) (coefficients I)
      (MvPolynomial.pderiv j
        (equations (algebraMap ℂ (CoefficientField I) (complexMap coupling))
          (familyEndpoint (complexMap coupling) (CoefficientField I)) i)) =
    MvPolynomial.aeval (coefficients I) (MvPolynomial.pderiv j (integralEquations i)) := by
  rw [← equations_map_to_field, MvPolynomial.pderiv_map,
    MvPolynomial.eval₂Hom_map_hom, RingHom.id_comp]
  rfl

theorem coefficients_jacobian (I : Ideal GenericIncidence) [I.IsMaximal] :
    IsUnit (Matrix.det (fun i j : Index =>
      MvPolynomial.eval₂Hom (RingHom.id (CoefficientField I)) (coefficients I)
        (MvPolynomial.pderiv j
          (equations (algebraMap ℂ (CoefficientField I) (complexMap coupling))
            (familyEndpoint (complexMap coupling) (CoefficientField I)) i)))) := by
  let J : Matrix Index Index (CoefficientField I) := fun i j =>
    MvPolynomial.aeval (coefficients I) (MvPolynomial.pderiv i (integralEquations j))
  have hM : (fun i j : Index =>
      MvPolynomial.eval₂Hom (RingHom.id (CoefficientField I)) (coefficients I)
        (MvPolynomial.pderiv j
          (equations (algebraMap ℂ (CoefficientField I) (complexMap coupling))
            (familyEndpoint (complexMap coupling) (CoefficientField I)) i))) =
      J.transpose := by
    funext i j
    exact coefficients_derivative I i j
  rw [hM, Matrix.det_transpose]
  exact openGeneric_jacobian integralEquations (1,0) I

theorem coefficients_transverse (I : Ideal GenericIncidence) [I.IsMaximal] :
    coefficients I (1,0) ≠ 0 :=
  isUnit_iff_ne_zero.mp (openGeneric_coordinate_unit integralEquations (1,0) I)

def arithmeticFamily (I : Ideal GenericIncidence) [I.IsMaximal] :
    QuarticFamily (complexMap coupling) (CoefficientField I) where
  coefficients := coefficients I
  equations := coefficients_equations I
  jacobian := coefficients_jacobian I
  transverse := coefficients_transverse I

end ReflectionCoupledFano.Arithmetic

#print axioms ReflectionCoupledFano.Arithmetic.arithmeticFamily
