import Proposal.ConicDimension
import HodgeComputer.Constructions.HoldoutCover.PolynomialFamilyBridge

/-!
Bind the polynomial family and its scaled normal vector to the deformed
quotient's actual residue map. All evaluations use the fixed coefficient
1/14. Prepared with OpenAI Codex assistance for hodgepodgeconjecture,
building on fqlx's shared polynomial-family residue bridge.
-/
noncomputable section
namespace DeformedConic
open HoldoutConstruction Polynomial
open scoped BigOperators
local instance conicTransport_local_1 : Algebra ℤ FunctionField := Ring.toIntAlgebra _

def quotientEquation : MvPolynomial (Fin 5) BaseField :=
  DeformedGeometry.weightedEquation (14⁻¹) baseFieldAlpha baseFieldBeta
def targetProjection : MvPolynomial (Fin 5) BaseField →+* TargetRing :=
  DeformedGeometry.quotientProjection (14⁻¹) baseFieldAlpha baseFieldBeta
def targetResidueMap : MvPolynomial (Fin 5) BaseField →+* TargetField :=
  DeformedGeometry.quotientResidueMap (14⁻¹) baseFieldAlpha baseFieldBeta
def fieldEval : MvPolynomial (Fin 5) BaseField →+* FunctionField :=
  MvPolynomial.eval₂Hom (algebraMap BaseField FunctionField) fieldCoordinate
@[simp] lemma targetResidueMap_C (r : BaseField) :
    targetResidueMap (MvPolynomial.C r)=algebraMap BaseField TargetField r := by
  change algebraMap TargetRing TargetField (AdjoinRoot.mk targetPolynomial
    (MvPolynomial.finSuccEquiv BaseField 4 (MvPolynomial.C r)))=_
  rw [show MvPolynomial.finSuccEquiv BaseField 4 (MvPolynomial.C r)=
    C (MvPolynomial.C r) from (MvPolynomial.finSuccEquiv BaseField 4).commutes r]
  rfl
lemma targetFieldMap_coordinate (i : Fin 5) :
    targetFieldMap (targetResidueMap (MvPolynomial.X i))=fieldCoordinate i := by
  change targetFieldMap (algebraMap TargetRing TargetField (AdjoinRoot.mk targetPolynomial
    (MvPolynomial.finSuccEquiv BaseField 4 (MvPolynomial.X i))))=_
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [MvPolynomial.finSuccEquiv_X_zero,targetFieldMap_ring]
    exact AdjoinRoot.lift_root conicField_root
  · rw [MvPolynomial.finSuccEquiv_X_succ,targetFieldMap_ring]
    change AdjoinRoot.lift _ _ _ (AdjoinRoot.of targetPolynomial (MvPolynomial.X j))=_
    rw [AdjoinRoot.lift_of,fieldCoefficientMap_X]
lemma targetFieldMap_residue (p : MvPolynomial (Fin 5) BaseField) :
    targetFieldMap (targetResidueMap p)=fieldEval p := by
  have h : targetFieldMap.comp targetResidueMap=fieldEval := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [fieldEval]
    · intro i
      simp [targetFieldMap_coordinate,fieldEval]
  exact congrArg (fun f : MvPolynomial (Fin 5) BaseField →+* FunctionField => f p) h
lemma finiteQuotientEvaluation_eq (p : MvPolynomial (Fin 5) BaseField) :
    finiteQuotientEvaluation (K := TargetField) (L := FunctionField) targetProjection p=fieldEval p :=
  targetFieldMap_residue p

lemma fieldEval_polynomial (p : MvPolynomial (Fin 5) BaseField) :
    fieldEval p=algebraMap (Polynomial CoefficientField) FunctionField
      (MvPolynomial.eval₂Hom (C.comp (algebraMap BaseField CoefficientField)) conicCurve p) := by
  have h : (algebraMap (Polynomial CoefficientField) FunctionField).comp
      (MvPolynomial.eval₂Hom (C.comp (algebraMap BaseField CoefficientField)) conicCurve)=fieldEval := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply,MvPolynomial.eval₂Hom_C,fieldEval]
      rfl
    · intro i
      simp [fieldEval,fieldCoordinate]
  exact (congrArg (fun f : MvPolynomial (Fin 5) BaseField →+* FunctionField => f p) h).symm

lemma gradient_evaluation (i : Fin 5) :
    14*fieldEval (integerPartial i quotientEquation)=
      algebraMap (Polynomial CoefficientField) FunctionField (conicGradient i) := by
  rw [fieldEval_polynomial]
  have h := DeformedGeometry.weightedEquation_partial_eval_fourteen
    (C.comp (algebraMap BaseField CoefficientField)) baseFieldAlpha baseFieldBeta conicCurve i
  simp only [RingHom.comp_apply,conicAlpha_base,conicBeta_base] at h
  have hm := congrArg (algebraMap (Polynomial CoefficientField) FunctionField) h
  simpa only [map_mul,map_ofNat,quotientEquation,conicGradient] using hm

def quotientNormal (i : Fin 5) : FunctionField :=
  14*algebraMap (Polynomial CoefficientField) FunctionField (conicNormal i)
lemma quotientNormal_pairing :
    (∑ i, fieldEval (integerPartial i quotientEquation)*quotientNormal i)=1 := by
  have h := congrArg (algebraMap (Polynomial CoefficientField) FunctionField) conicNormal_pairing
  simp only [polynomialPairing,map_sum,map_mul,map_one,← gradient_evaluation] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [quotientNormal]
  ring

def quotientEvaluationMatrix : Matrix (Fin 5) (Fin 5) FunctionField :=
  fun i => Fin.cases (quotientNormal i) (fun j => evaluationMatrix i j.succ)
lemma quotientEvaluationMatrix_factor : quotientEvaluationMatrix=
    evaluationMatrix * Matrix.diagonal (Fin.cases 14 (fun _ : Fin 4 => 1)) := by
  ext i j
  refine Fin.cases ?_ (fun j => ?_) j
  · rw [Matrix.mul_diagonal]
    change 14*algebraMap (Polynomial CoefficientField) FunctionField (conicNormal i)=
      algebraMap (Polynomial CoefficientField) FunctionField (conicNormal i)*14
    exact mul_comm _ _
  · rw [Matrix.mul_diagonal]
    change evaluationMatrix i j.succ=evaluationMatrix i j.succ*1
    exact (mul_one _).symm
lemma quotientEvaluationMatrix_det_ne_zero : quotientEvaluationMatrix.det ≠ 0 := by
  rw [quotientEvaluationMatrix_factor,Matrix.det_mul,Matrix.det_diagonal]
  simp only [Fin.prod_univ_succ,Fin.cases_zero,Fin.cases_succ,Finset.prod_const_one,mul_one]
  exact mul_ne_zero evaluationMatrix_det_ne_zero (by norm_num)

lemma coefficientDerivation_baseField (j : Fin 3) (r : BaseField) :
    coefficientDerivation j (algebraMap BaseField CoefficientField r)=0 := by
  obtain ⟨a,b,hb,rfl⟩ := IsFractionRing.div_surjective FermatRing r
  rw [map_div₀,← IsScalarTower.algebraMap_apply,← IsScalarTower.algebraMap_apply]
  change coefficientDerivation j (algebraMap ParameterRing CoefficientField (MvPolynomial.C a)/
    algebraMap ParameterRing CoefficientField (MvPolynomial.C b))=0
  simp [Derivation.leibniz_div,coefficientDerivation_base]
lemma sourceDerivation_baseField (j : Fin 4) (r : BaseField) :
    sourceDerivation j (algebraMap BaseField FunctionField r)=0 := by
  change sourceDerivation j (algebraMap CoefficientField FunctionField
    (algebraMap BaseField CoefficientField r))=0
  refine Fin.cases ?_ (fun j => ?_) j
  · exact sourceDerivation_time_constant _
  · change curveCoefficientDerivation (coefficientDerivation j)
      (algebraMap CoefficientField FunctionField (algebraMap BaseField CoefficientField r))=0
    rw [curveCoefficientDerivation_coefficient,coefficientDerivation_baseField,map_zero]

end DeformedConic
#print axioms DeformedConic.quotientNormal_pairing
#print axioms DeformedConic.quotientEvaluationMatrix_det_ne_zero
