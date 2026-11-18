import Proposal.ConicNormal
import HodgeComputer.Constructions.HoldoutCover.FiniteDifferentials
import HodgeComputer.Constructions.HoldoutCover.EvaluationMatrix
import HodgeComputer.Constructions.HoldoutCover.PolynomialCalculus

/-!
The source derivatives and the nonzero evaluation determinant of the new
conic. The three constant terms x2,S,P are independent parameters, so the
endpoint derivative block is the identity. Uses fqlx's shared extension
and determinant lemmas. Prepared with OpenAI Codex assistance for
hodgepodgeconjecture.
-/
noncomputable section
set_option profiler true
set_option profiler.threshold 100
namespace DeformedConic
open HoldoutConstruction Polynomial
attribute [local instance] fermatCurve_adjoinRoot_isDomain fermat_base_charZero
local instance conicFlow_local_1 : Algebra ℤ ParameterField := Ring.toIntAlgebra _
local instance conicFlow_local_2 : Algebra ℤ CoefficientField := Ring.toIntAlgebra _
abbrev FunctionField := FractionRing (Polynomial CoefficientField)
local instance conicFlow_local_3 : Algebra ℤ FunctionField := Ring.toIntAlgebra _

def parameterDerivation (j : Fin 3) : Derivation ℤ ParameterField ParameterField :=
  extendRingDerivation (P := ParameterRing) (L := ParameterField) (integerPartial (R := FermatRing) j)
def coefficientDerivation (j : Fin 3) : Derivation ℤ CoefficientField CoefficientField :=
  extendFiniteDerivation (parameterDerivation j)
lemma coefficientDerivation_parameterRing (j : Fin 3) (r : ParameterRing) :
    coefficientDerivation j (algebraMap ParameterRing CoefficientField r)=
      algebraMap ParameterRing CoefficientField (integerPartial j r) := by
  rw [IsScalarTower.algebraMap_apply ParameterRing ParameterField CoefficientField,
    coefficientDerivation,extendFiniteDerivation_apply,parameterDerivation]
  exact congrArg (algebraMap ParameterField CoefficientField)
    (extendRingDerivation_apply (L:=ParameterField) (integerPartial (R:=FermatRing) j) r)
lemma coefficientDerivations_commute (i j : Fin 3) :
    Function.Commute (coefficientDerivation i) (coefficientDerivation j) :=
  extendFiniteDerivation_commute _ _
    (extendRingDerivation_commute (L := ParameterField)
      (integerPartial (R := FermatRing) i) (integerPartial (R := FermatRing) j)
      (integerPartials_commute i j))

def scalarParameter (i : Fin 3) : CoefficientField :=
  algebraMap ParameterRing CoefficientField (parameter i)
@[simp] lemma coefficientDerivation_parameter (i j : Fin 3) :
    coefficientDerivation i (scalarParameter j)=if j=i then 1 else 0 := by
  rw [scalarParameter,coefficientDerivation_parameterRing]
  simp [parameter,integerPartial_apply,MvPolynomial.pderiv_X,Pi.single_apply,apply_ite]
@[simp] lemma coefficientDerivation_base (i : Fin 3) (r : FermatRing) :
    coefficientDerivation i (algebraMap ParameterRing CoefficientField (MvPolynomial.C r))=0 := by
  rw [coefficientDerivation_parameterRing]
  simp

lemma conicCurve_time : conicCurve 1=X := by
  rw [conicCurve,curveEval_eq_valueCurve]
  rfl
lemma conicCurve_endpoint (i : Fin 3) :
    (conicCurve i.succ.succ).coeff 0=scalarParameter i := by
  rw [conicCurve,curveEval_eq_valueCurve]
  fin_cases i <;> simp [valueCurve,scalarParameter]

def polynomialDerivation : Fin 4 → Derivation ℤ (Polynomial CoefficientField) (Polynomial CoefficientField) :=
  Fin.cases timePolynomialDerivation (fun j => coefficientPolynomialDerivation (coefficientDerivation j))
lemma polynomialDerivations_commute (i j : Fin 4) :
    Function.Commute (polynomialDerivation i) (polynomialDerivation j) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · intro f; rfl
    · exact time_coefficientPolynomialDerivation_commute _
  · refine Fin.cases ?_ (fun j => ?_) j
    · exact (time_coefficientPolynomialDerivation_commute _).symm
    · exact coefficientPolynomialDerivation_commute _ _ (coefficientDerivations_commute i j)
def sourceDerivation (j : Fin 4) : Derivation ℤ FunctionField FunctionField :=
  extendRingDerivation (polynomialDerivation j)
lemma sourceDerivations_commute (i j : Fin 4) :
    Function.Commute (sourceDerivation i) (sourceDerivation j) :=
  extendRingDerivation_commute _ _ (polynomialDerivations_commute i j)
@[simp] lemma sourceDerivation_polynomial (j : Fin 4) (f : Polynomial CoefficientField) :
    sourceDerivation j (algebraMap (Polynomial CoefficientField) FunctionField f)=
      algebraMap (Polynomial CoefficientField) FunctionField (polynomialDerivation j f) :=
  extendRingDerivation_apply _ f
@[simp] lemma sourceDerivation_time_constant (a : CoefficientField) :
    sourceDerivation 0 (algebraMap CoefficientField FunctionField a)=0 :=
  curveTimeDerivation_coefficient a
@[simp] lemma sourceDerivation_time : sourceDerivation 0 (curveTime (E := CoefficientField))=1 :=
  curveTimeDerivation_time

def evaluationPolynomialMatrix : Matrix (Fin 5) (Fin 5) (Polynomial CoefficientField) :=
  fun i => Fin.cases (conicNormal i) (fun j => polynomialDerivation j (conicCurve i))
lemma evaluationPolynomialMatrix_det_constant :
    evaluationPolynomialMatrix.det.coeff 0=(conicNormal 0).coeff 0 := by
  have h := polynomial_evaluation_det_constant evaluationPolynomialMatrix
    ((conicNormal 0).coeff 0) 1
  rw [mul_one] at h
  apply h
  · intro i
    change (conicNormal i).coeff 0=if i=0 then _ else _
    by_cases hi : i=0
    · simp [hi]
    · simp [hi,conicNormal_constant_zero i hi]
  · change (timePolynomialDerivation (conicCurve 1)).coeff 0=1
    rw [conicCurve_time,timePolynomialDerivation_apply]
    simp
  · intro j
    change (coefficientPolynomialDerivation (coefficientDerivation j) (conicCurve 1)).coeff 0=0
    rw [conicCurve_time,coefficientPolynomialDerivation_coeff]
    simp
  · intro i j
    change (coefficientPolynomialDerivation (coefficientDerivation j)
      (conicCurve i.succ.succ)).coeff 0=if i=j then 1 else 0
    rw [coefficientPolynomialDerivation_coeff,conicCurve_endpoint,coefficientDerivation_parameter]
lemma evaluationPolynomialMatrix_det_ne_zero : evaluationPolynomialMatrix.det ≠ 0 := by
  intro h
  have hc := evaluationPolynomialMatrix_det_constant
  rw [h,Polynomial.coeff_zero] at hc
  exact conicNormal_constant_nonzero hc.symm
def evaluationMatrix : Matrix (Fin 5) (Fin 5) FunctionField :=
  (algebraMap (Polynomial CoefficientField) FunctionField).mapMatrix evaluationPolynomialMatrix
lemma evaluationMatrix_det_ne_zero : evaluationMatrix.det ≠ 0 := by
  rw [evaluationMatrix,← RingHom.map_det]
  exact fun h => evaluationPolynomialMatrix_det_ne_zero
    (IsFractionRing.injective (Polynomial CoefficientField) FunctionField (h.trans (map_zero _).symm))

end DeformedConic
#print axioms DeformedConic.evaluationMatrix_det_ne_zero
#print axioms DeformedConic.sourceDerivations_commute
