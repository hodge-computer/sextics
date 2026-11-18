import Proposal.ComplexConic
import HodgeComputer.Constructions.HoldoutCover.FermatFields

/-!
The replacement conic over the generic Fermat base and three independent
endpoint parameters. The specialized complex point proves nontriviality
before passage to a fraction field; flatness then constructs the generic
family. This follows the incidence method of fqlx's accepted construction.
Prepared with OpenAI Codex assistance for hodgepodgeconjecture.
-/
noncomputable section
set_option profiler true
set_option profiler.threshold 100
namespace DeformedConic
open HoldoutConstruction Polynomial
open scoped TensorProduct
attribute [local instance] fermatCurve_adjoinRoot_isDomain fermat_base_charZero

abbrev FermatRing := FermatBaseRing ℂ
noncomputable instance fermatRing_commRing : CommRing FermatRing := inferInstance
instance fermatRing_domain : IsDomain FermatRing := fermatCurve_adjoinRoot_isDomain
instance fermatRing_charZero : CharZero FermatRing := fermat_base_charZero
abbrev ParameterRing := MvPolynomial (Fin 3) FermatRing
noncomputable instance parameterRing_commRing : CommRing ParameterRing := inferInstance
instance parameterRing_domain : IsDomain ParameterRing := inferInstance
instance parameterRing_charZero : CharZero ParameterRing := inferInstance
abbrev ParameterField := FractionRing ParameterRing
noncomputable instance parameterField_field : Field ParameterField := inferInstance
instance parameterField_charZero : CharZero ParameterField := inferInstance
noncomputable instance (priority := 2000) parameterField_module : Module ParameterRing ParameterField :=
  Algebra.toModule
noncomputable instance (priority := 2000) parameterField_smul : SMul ParameterRing ParameterField :=
  parameterField_module.toSMul
instance (priority := 2000) parameterField_comm : SMulCommClass ParameterRing ParameterRing ParameterField where
  smul_comm a b x := by
    simp only [Algebra.smul_def]
    ring
def parameter : Fin 3 → ParameterRing := MvPolynomial.X
def alpha : ParameterRing := MvPolynomial.C baseAlpha
def beta : ParameterRing := MvPolynomial.C baseBeta
def genericEquations : Fin 13 → MvPolynomial (Fin 13) ParameterRing :=
  equations alpha beta parameter

def seedMap : ParameterRing →+* ℂ :=
  MvPolynomial.eval₂Hom (baseEval (1 : ℂ) 0 (by norm_num)) ![4,4,4]
section Specialization
local instance seedAlgebra : Algebra ParameterRing ℂ := seedMap.toAlgebra

@[simp] lemma seedMap_alpha : seedMap alpha=1 := by simp [seedMap,alpha]
@[simp] lemma seedMap_beta : seedMap beta=0 := by simp [seedMap,beta]
@[simp] lemma seedMap_parameter (i : Fin 3) : seedMap (parameter i)=4 := by
  fin_cases i <;> simp [seedMap,parameter]

lemma seedCurve_binding (v : Fin 13 → ℂ) :
    curveEval parameter seedMap v=complexCurve v := by
  rw [curveEval_eq_valueCurve,complexCurve,curveEval_eq_valueCurve]
  congr 1
  funext i
  fin_cases i <;> simp [integerParameters]

instance generic_incidence_nontrivial : Nontrivial (SquareEtaleRing genericEquations) := by
  obtain ⟨v,hc,hj⟩ := exists_complex_conic
  have he (i : Fin 13) : MvPolynomial.aeval v (genericEquations i)=0 := by
    change MvPolynomial.eval₂Hom seedMap v (equations alpha beta parameter i)=0
    rw [equations_eval,seedMap_alpha,seedMap_beta,seedCurve_binding]
    simpa only [map_one,map_zero,hc,Polynomial.coeff_zero]
  have hm : (fun i j : Fin 13 => MvPolynomial.aeval v
      (MvPolynomial.pderiv i (genericEquations j)))=(complexJacobian v).transpose := by
    funext i j
    change MvPolynomial.eval₂Hom seedMap v
      (MvPolynomial.pderiv i (equations alpha beta parameter j)) = _
    rw [equations_pderiv_eval,seedMap_alpha,seedMap_beta,seedCurve_binding]
    simp only [map_one,map_zero,complexJacobian,Matrix.transpose_apply]
  apply square_system_jacobian_nontrivial genericEquations v he
  rw [hm,Matrix.det_transpose]
  exact hj

end Specialization

abbrev GenericIncidence := SquareGenericAlgebra ParameterField genericEquations
noncomputable instance (priority := 2000) genericIncidence_module : Module ParameterField GenericIncidence :=
  Algebra.toModule
noncomputable instance (priority := 2000) genericIncidence_smul : SMul ParameterField GenericIncidence :=
  genericIncidence_module.toSMul
theorem coefficientFactor_exists : ∃ I : Ideal GenericIncidence, I.IsMaximal ∧
    Module.Finite ParameterField (@HasQuotient.Quotient _ _ Ideal.instHasQuotient I) := by
  letI : Algebra.Etale ParameterRing (SquareEtaleRing genericEquations) :=
    square_system_jacobian_etale genericEquations
  obtain ⟨I,hi,hf,_⟩ := genericEtale_exists_fieldFactor
    ParameterRing ParameterField (SquareEtaleRing genericEquations)
      (IsFractionRing.injective ParameterRing ParameterField)
  exact ⟨I,hi,hf⟩
def coefficientFactor : Ideal GenericIncidence := Classical.choose coefficientFactor_exists
instance coefficientFactor_maximal : coefficientFactor.IsMaximal :=
  (Classical.choose_spec coefficientFactor_exists).1
abbrev CoefficientField := @HasQuotient.Quotient _ _ Ideal.instHasQuotient coefficientFactor
noncomputable instance coefficientField_field : Field CoefficientField := Ideal.Quotient.field _
noncomputable instance (priority := 2000) coefficientField_module : Module ParameterField CoefficientField :=
  Algebra.toModule
noncomputable instance (priority := 2000) coefficientField_smul : SMul ParameterField CoefficientField :=
  coefficientField_module.toSMul
instance coefficientField_finite : Module.Finite ParameterField CoefficientField :=
  (Classical.choose_spec coefficientFactor_exists).2
instance coefficientField_charZero : CharZero CoefficientField :=
  charZero_of_injective_ringHom (f := algebraMap ParameterField CoefficientField)
    (algebraMap ParameterField CoefficientField).injective

noncomputable instance coefficientField_parameterAlgebra : Algebra ParameterRing CoefficientField :=
  ((algebraMap ParameterField CoefficientField).comp (algebraMap ParameterRing ParameterField)).toAlgebra
noncomputable instance (priority := 2000) coefficientField_parameterModule : Module ParameterRing CoefficientField :=
  Algebra.toModule
noncomputable instance (priority := 2000) coefficientField_parameterSMul : SMul ParameterRing CoefficientField :=
  coefficientField_parameterModule.toSMul
instance coefficientField_parameterTower : IsScalarTower ParameterRing ParameterField CoefficientField :=
  IsScalarTower.of_algebraMap_eq (R := ParameterRing) (S := ParameterField)
    (A := CoefficientField) (fun _ => rfl)

def coefficients : Fin 13 → CoefficientField := squareGenericCoordinates genericEquations coefficientFactor
lemma coefficients_equations (i : Fin 13) :
    MvPolynomial.aeval coefficients (genericEquations i)=0 :=
  squareGeneric_solution genericEquations coefficientFactor i
lemma coefficients_jacobian : IsUnit (Matrix.det (fun i j => MvPolynomial.aeval coefficients
    (MvPolynomial.pderiv i (genericEquations j)))) :=
  squareGeneric_jacobian genericEquations coefficientFactor

def conicCurve : Fin 5 → Polynomial CoefficientField :=
  curveEval parameter (algebraMap ParameterRing CoefficientField) coefficients
def conicAlpha : CoefficientField := algebraMap ParameterRing CoefficientField alpha
def conicBeta : CoefficientField := algebraMap ParameterRing CoefficientField beta

lemma conic_base_relation : conicAlpha^6+conicBeta^6=1 := by
  have h := congrArg (algebraMap ParameterRing CoefficientField)
    (congrArg (MvPolynomial.C : FermatRing →+* ParameterRing) (fermat_base_relation (R := ℂ)))
  simpa only [map_add,map_pow,map_one,conicAlpha,conicBeta,alpha,beta] using h

lemma conic_equation : H (C conicAlpha) (C conicBeta) conicCurve=0 := by
  ext n
  rw [Polynomial.coeff_zero]
  by_cases hn : n<13
  · have h := coefficients_equations ⟨n,hn⟩
    change MvPolynomial.eval₂Hom (algebraMap ParameterRing CoefficientField) coefficients
      (equations alpha beta parameter ⟨n,hn⟩)=0 at h
    rw [equations_eval] at h
    exact h
  · have hb : (H (C conicAlpha) (C conicBeta) conicCurve).natDegree ≤ 12 :=
      H_eval_natDegree_le (algebraMap ParameterRing CoefficientField) alpha beta parameter coefficients
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hb (by omega))

def conicJacobian : Matrix (Fin 13) (Fin 13) CoefficientField := fun i j =>
  (gradient (C conicAlpha) (C conicBeta) conicCurve (slotCoordinate j)*X^slotDegree j).coeff i.val

lemma conic_jacobian_unit : IsUnit conicJacobian.det := by
  have hm : (fun i j : Fin 13 => MvPolynomial.aeval coefficients
      (MvPolynomial.pderiv i (genericEquations j)))=conicJacobian.transpose := by
    funext i j
    change MvPolynomial.eval₂Hom (algebraMap ParameterRing CoefficientField) coefficients
      (MvPolynomial.pderiv i (equations alpha beta parameter j)) = _
    rw [equations_pderiv_eval]
    rfl
  have h := coefficients_jacobian
  rw [hm,Matrix.det_transpose] at h
  exact h

#print axioms generic_incidence_nontrivial
#print axioms conic_equation
#print axioms conic_jacobian_unit
end DeformedConic
