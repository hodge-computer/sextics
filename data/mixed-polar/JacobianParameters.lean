import Proposal.JacobianFamily
import HodgeComputer.Constructions.HoldoutCover.FiniteDifferentials
import HodgeComputer.Constructions.HoldoutCover.PolynomialCalculus

/-! Independent complex parameters and their extended derivations.
Uses the shared localization and finite-extension derivation constructions.
Adapted from the accepted constructions of fqlx and hodgepodgeconjecture.
Prepared for benediamond with OpenAI Codex assistance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
namespace MixedPolarJacobianParameters
open HoldoutConstruction MixedPolarJacobianIncidence MixedPolarJacobianLifting MixedPolarJacobianFamily Polynomial
local instance : Algebra ℤ ComplexParameterField := Ring.toIntAlgebra _
local instance : Algebra ℤ CoefficientField := Ring.toIntAlgebra _

def parameterMap : ComplexParameterRing →+* CoefficientField :=
  (algebraMap ComplexParameterField CoefficientField).comp
    (algebraMap ComplexParameterRing ComplexParameterField)
lemma parameterMap_injective : Function.Injective parameterMap :=
  (algebraMap ComplexParameterField CoefficientField).injective.comp
    (IsFractionRing.injective ComplexParameterRing ComplexParameterField)
def constantMap : ℂ →+* CoefficientField := parameterMap.comp MvPolynomial.C
lemma parameterMap_X (i : Fin 4) : parameterMap (MvPolynomial.X i)=scalarParameter i := by
  change algebraMap ComplexParameterField CoefficientField
      (algebraMap ComplexParameterRing ComplexParameterField (MvPolynomial.X i)) =
    algebraMap ComplexParameterField CoefficientField
      (algebraMap ComplexParameterRing ComplexParameterField
        (MvPolynomial.map (Int.castRingHom ℂ) (MvPolynomial.X i)))
  rw [MvPolynomial.map_X]

lemma conicCurve_endpoint_r : (conicCurve 0).coeff 0=scalarParameter 2 := by
  rw [conicCurve,curveEval_eq_valueCurve]
  simp [valueCurve,endpoints,scalarParameter]
lemma conicCurve_endpoint_x : (conicCurve 1).coeff 0=scalarParameter 3 := by
  rw [conicCurve,curveEval_eq_valueCurve]
  simp [valueCurve,endpoints,scalarParameter]

/-- Complex constants remain fixed; all four endpoint/base parameters vary. -/
def parameterDerivation (i : Fin 4) : Derivation ℤ ComplexParameterField ComplexParameterField :=
  extendRingDerivation (P := ComplexParameterRing) (L := ComplexParameterField)
    (integerPartial (R := ℂ) i)
def coefficientDerivation (i : Fin 4) : Derivation ℤ CoefficientField CoefficientField :=
  extendFiniteDerivation (parameterDerivation i)
lemma coefficientDerivation_parameterMap (i : Fin 4) (p : ComplexParameterRing) :
    coefficientDerivation i (parameterMap p)=parameterMap (integerPartial i p) := by
  simp only [parameterMap,RingHom.comp_apply,coefficientDerivation,extendFiniteDerivation_apply,
    parameterDerivation,extendRingDerivation_apply]
lemma coefficientDerivation_parameter (i j : Fin 4) :
    coefficientDerivation i (scalarParameter j)=if j=i then 1 else 0 := by
  rw [← parameterMap_X,coefficientDerivation_parameterMap]
  simp [integerPartial_apply,MvPolynomial.pderiv_X,Pi.single_apply,apply_ite]
lemma coefficientDerivation_constant (i : Fin 4) (c : ℂ) :
    coefficientDerivation i (constantMap c)=0 := by
  change coefficientDerivation i (parameterMap (MvPolynomial.C c))=0
  rw [coefficientDerivation_parameterMap]
  simp
lemma coefficientDerivations_commute (i j : Fin 4) :
    Function.Commute (coefficientDerivation i) (coefficientDerivation j) :=
  extendFiniteDerivation_commute _ _
    (extendRingDerivation_commute (L := ComplexParameterField)
      (integerPartial (R := ℂ) i) (integerPartial (R := ℂ) j)
      (integerPartials_commute i j))

/-- Six ambient coordinates Y,T,c1,c2,R,X. -/
def fullCurve : Fin 6 → Polynomial CoefficientField :=
  ![conicCurve 2,X,C (scalarParameter 0),C (scalarParameter 1),conicCurve 0,conicCurve 1]
lemma fullCurve_time : fullCurve 1=X := rfl
lemma fullCurve_endpoint (i : Fin 4) : (fullCurve i.succ.succ).coeff 0=scalarParameter i := by
  fin_cases i <;> simp [fullCurve,conicCurve_endpoint_r,conicCurve_endpoint_x]
def fullNormal : Fin 6 → Polynomial CoefficientField :=
  ![conicNormal 2,0,0,0,conicNormal 0,conicNormal 1]
lemma fullNormal_constant (i : Fin 6) :
    (fullNormal i).coeff 0=if i=0 then (conicNormal 2).coeff 0 else 0 := by
  fin_cases i <;> simp [fullNormal,conicNormal_constant_zero]

def polynomialDerivation : Fin 5 → Derivation ℤ (Polynomial CoefficientField) (Polynomial CoefficientField) :=
  Fin.cases timePolynomialDerivation (fun j => coefficientPolynomialDerivation (coefficientDerivation j))
lemma polynomialDerivations_commute (i j : Fin 5) :
    Function.Commute (polynomialDerivation i) (polynomialDerivation j) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · intro f; rfl
    · exact time_coefficientPolynomialDerivation_commute _
  · refine Fin.cases ?_ (fun j => ?_) j
    · exact (time_coefficientPolynomialDerivation_commute _).symm
    · exact coefficientPolynomialDerivation_commute _ _ (coefficientDerivations_commute i j)

#print axioms parameterMap_injective
#print axioms coefficientDerivations_commute
end MixedPolarJacobianParameters
