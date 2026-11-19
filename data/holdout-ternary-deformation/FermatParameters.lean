import Proposal.GenericConic
import HodgeComputer.Constructions.HoldoutCover.AlgebraicFields

/-!
The fraction field of the Fermat base embeds in the conic coefficient
field. Only this generic embedding is used: no rational function is
specialized at the finite-field seed. Prepared with OpenAI Codex assistance
for hodgepodgeconjecture, using fqlx's generic-incidence construction.
-/
noncomputable section
set_option profiler true
set_option profiler.threshold 100
namespace DeformedConic
open HoldoutConstruction Polynomial
attribute [local instance] fermatCurve_adjoinRoot_isDomain fermat_base_charZero

abbrev BaseField := FractionRing FermatRing
noncomputable instance baseField_field : Field BaseField := inferInstance
instance baseField_charZero : CharZero BaseField := inferInstance
instance parameterField_faithful_base : FaithfulSMul FermatRing ParameterField :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr
    ((IsFractionRing.injective ParameterRing ParameterField).comp (MvPolynomial.C_injective (Fin 3) FermatRing))
noncomputable instance parameterField_baseAlgebra : Algebra BaseField ParameterField :=
  FractionRing.liftAlgebra FermatRing ParameterField
instance parameterField_baseTower : IsScalarTower FermatRing BaseField ParameterField :=
  FractionRing.isScalarTower_liftAlgebra FermatRing ParameterField
noncomputable instance coefficientField_baseAlgebra : Algebra BaseField CoefficientField :=
  ((algebraMap ParameterField CoefficientField).comp (algebraMap BaseField ParameterField)).toAlgebra
noncomputable instance (priority := 2000) coefficientField_baseModule : Module BaseField CoefficientField :=
  Algebra.toModule
noncomputable instance (priority := 2000) coefficientField_baseSMul : SMul BaseField CoefficientField :=
  coefficientField_baseModule.toSMul
instance coefficientField_baseTower : IsScalarTower BaseField ParameterField CoefficientField :=
  IsScalarTower.of_algebraMap_eq (R := BaseField) (S := ParameterField)
    (A := CoefficientField) (fun _ => rfl)
instance coefficientField_ringTower : IsScalarTower FermatRing BaseField CoefficientField :=
  IsScalarTower.to₁₂₄ FermatRing BaseField ParameterField CoefficientField

def baseFieldAlpha : BaseField := algebraMap FermatRing BaseField baseAlpha
def baseFieldBeta : BaseField := algebraMap FermatRing BaseField baseBeta
lemma conicAlpha_base : algebraMap BaseField CoefficientField baseFieldAlpha=conicAlpha := by
  rw [baseFieldAlpha,← IsScalarTower.algebraMap_apply]
  rfl
lemma conicBeta_base : algebraMap BaseField CoefficientField baseFieldBeta=conicBeta := by
  rw [baseFieldBeta,← IsScalarTower.algebraMap_apply]
  rfl

lemma parameterField_algebraMap_injective :
    Function.Injective (algebraMap ParameterRing CoefficientField) := by
  rw [IsScalarTower.algebraMap_eq ParameterRing ParameterField CoefficientField]
  exact (algebraMap ParameterField CoefficientField).injective.comp
    (IsFractionRing.injective ParameterRing ParameterField)

end DeformedConic
#print axioms DeformedConic.conicAlpha_base
#print axioms DeformedConic.parameterField_algebraMap_injective
