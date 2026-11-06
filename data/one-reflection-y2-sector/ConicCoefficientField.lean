import HodgeComputer.Constructions.HoldoutCover.AlgebraicFields
import HodgeComputer.Constructions.HoldoutCover.EndpointFields
import Proposal.FermatIncidenceSeed
import HodgeComputer.Constructions.HoldoutCover.GenericIncidence

/- Source component: ConicCoefficientField -/
section
/-!
The finite algebraic coefficient field of the holdout conic family.
The seed lives over the endpoint coordinate ring. Only after nontriviality
is proved do we pass to a generic coefficient field and choose a maximal
ideal in the finite etale algebra.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace HoldoutConicIncidence

open HoldoutConstruction

attribute [local instance] fermatCurve_adjoinRoot_isDomain fermat_base_charZero
attribute [local instance] endpoint_adjoinRoot_isDomain endpoint_charZero

abbrev FermatBaseField := FractionRing FermatCurveBase
abbrev FermatEndpointField := FractionRing (EndpointRing FermatBaseField)

noncomputable instance fermatBaseField_field : Field FermatBaseField := inferInstance
instance fermatBaseField_charZero : CharZero FermatBaseField := inferInstance
noncomputable instance fermatEndpointField_field : Field FermatEndpointField := inferInstance
instance fermatEndpointField_charZero : CharZero FermatEndpointField := inferInstance

def endpointGenericMap : FermatEndpointRing →+* FermatEndpointField :=
  endpointFieldMap (algebraMap FermatCurveBase FermatBaseField)

theorem endpointGenericMap_injective : Function.Injective endpointGenericMap :=
  endpointFieldMap_injective _ (IsFractionRing.injective FermatCurveBase FermatBaseField)

noncomputable instance endpointGenericAlgebra :
    Algebra FermatEndpointRing FermatEndpointField := endpointGenericMap.toAlgebra

abbrev ConicGenericAlgebra (p : HoldoutConic.Seed) :=
  SquareGenericAlgebra FermatEndpointField (fermatEquations p)

theorem conicCoefficientFactor_exists (p : HoldoutConic.Seed) :
    ∃ I : Ideal (ConicGenericAlgebra p), I.IsMaximal ∧
      Module.Finite FermatEndpointField ((ConicGenericAlgebra p) ⧸ I) := by
  let : Nontrivial (SquareEtaleRing (fermatEquations p)) := fermat_incidence_nontrivial p
  let : Algebra.Etale FermatEndpointRing (SquareEtaleRing (fermatEquations p)) :=
    square_system_jacobian_etale (fermatEquations p)
  have hinj : Function.Injective (algebraMap FermatEndpointRing FermatEndpointField) :=
    endpointGenericMap_injective
  obtain ⟨I,hI,hfin,_⟩ := genericEtale_exists_fieldFactor
    FermatEndpointRing FermatEndpointField (SquareEtaleRing (fermatEquations p)) hinj
  exact ⟨I,hI,hfin⟩

def conicCoefficientFactor (p : HoldoutConic.Seed) : Ideal (ConicGenericAlgebra p) :=
  Classical.choose (α := Ideal (ConicGenericAlgebra p)) (conicCoefficientFactor_exists p)

instance conicCoefficientFactor_maximal (p : HoldoutConic.Seed) :
    (conicCoefficientFactor p).IsMaximal :=
  (Classical.choose_spec (conicCoefficientFactor_exists p)).1

abbrev ConicCoefficientField (p : HoldoutConic.Seed) :=
  (ConicGenericAlgebra p) ⧸ conicCoefficientFactor p

noncomputable instance conicCoefficientField_field (p : HoldoutConic.Seed) :
    Field (ConicCoefficientField p) := Ideal.Quotient.field _

instance conicCoefficientField_finite (p : HoldoutConic.Seed) :
    Module.Finite FermatEndpointField (ConicCoefficientField p) :=
  (Classical.choose_spec (conicCoefficientFactor_exists p)).2

instance conicCoefficientField_charZero (p : HoldoutConic.Seed) :
    CharZero (ConicCoefficientField p) :=
  charZero_of_injective_ringHom (f := algebraMap FermatEndpointField (ConicCoefficientField p))
    (algebraMap FermatEndpointField (ConicCoefficientField p)).injective

noncomputable instance conicCoefficientField_baseAlgebra (p : HoldoutConic.Seed) :
    Algebra FermatBaseField (ConicCoefficientField p) := inferInstance

instance conicCoefficientField_baseTower (p : HoldoutConic.Seed) :
    IsScalarTower FermatBaseField FermatEndpointField (ConicCoefficientField p) := inferInstance

def conicCoefficients (p : HoldoutConic.Seed) : Index → ConicCoefficientField p :=
  squareGenericCoordinates (fermatEquations p) (conicCoefficientFactor p)

theorem conicCoefficients_equations (p : HoldoutConic.Seed) (i : Index) :
    MvPolynomial.aeval (conicCoefficients p) (fermatEquations p i) = 0 :=
  squareGeneric_solution (fermatEquations p) (conicCoefficientFactor p) i

theorem conicCoefficients_jacobian (p : HoldoutConic.Seed) :
    IsUnit (Matrix.det (fun i j => MvPolynomial.aeval (conicCoefficients p)
      (MvPolynomial.pderiv i (fermatEquations p j)))) :=
  squareGeneric_jacobian (fermatEquations p) (conicCoefficientFactor p)

theorem fermatEndpointField_trdeg :
    Algebra.trdeg FermatBaseField FermatEndpointField = 3 := by
  apply monic_hypersurface_field_trdeg (endpointPolynomial (R := FermatBaseField))
    endpointPolynomial_monic
  change (Polynomial.X^6+Polynomial.C
    (MvPolynomial.X 0^6+MvPolynomial.X 1^3-
      3*MvPolynomial.X 1*MvPolynomial.X 2^2 : MvPolynomial (Fin 3) FermatBaseField)).degree ≠ 0
  rw [Polynomial.degree_X_pow_add_C (by decide)]
  norm_num

instance fermatEndpointField_essFiniteType :
    Algebra.EssFiniteType FermatBaseField FermatEndpointField :=
  monic_hypersurface_field_essFiniteType (endpointPolynomial (R := FermatBaseField))

theorem conic_function_field_trdeg (p : HoldoutConic.Seed) :
    Algebra.trdeg FermatBaseField (FractionRing (Polynomial (ConicCoefficientField p))) = 4 := by
  rw [polynomial_fractionRing_trdeg FermatBaseField FermatEndpointField,
    fermatEndpointField_trdeg]
  norm_num

instance conic_function_field_essFiniteType (p : HoldoutConic.Seed) :
    Algebra.EssFiniteType FermatBaseField (FractionRing (Polynomial (ConicCoefficientField p))) :=
  polynomial_fractionRing_essFiniteType FermatBaseField FermatEndpointField
    (ConicCoefficientField p)

end HoldoutConicIncidence

#print axioms HoldoutConicIncidence.conicCoefficients_equations
#print axioms HoldoutConicIncidence.conicCoefficients_jacobian
#print axioms HoldoutConicIncidence.conic_function_field_trdeg
end
end
